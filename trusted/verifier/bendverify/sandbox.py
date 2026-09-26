"""Sandboxed execution. TRUSTED.

Untrusted code — the competitor's optimizer — only ever runs inside
`run_optimizer`: a fresh Docker container (image pinned by id in
competition.json) with

  * no network                    (--network none)
  * no secrets / host env          (only the variables set here)
  * read-only root file system     (--read-only), all capabilities dropped,
    no-new-privileges, unprivileged user 65534
  * the candidate repository and the reference IR mounted READ-ONLY; nothing
    of the trusted base is mounted at all
  * CPU / memory / pids / wall-clock limits
  * writable space only in size-capped tmpfs mounts (/out, /tmp) that vanish
    with the container; results leave as a size-capped tar stream on stdout.

Compiled workload binaries (built by the trusted pipeline from untrusted IR)
and trusted tools that parse hostile data (the Lean replay checker, Node
running the reference Bend front end) run under macOS `sandbox-exec` with
network access denied and writes confined to a scratch directory, plus
rlimits. This is defence in depth: those programs are not competitor code.
"""

from __future__ import annotations

import io
import os
import resource
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time

from .competition import canon_hash


class SandboxError(Exception):
    pass


MAX_OUTPUT = 64 * 1024 * 1024


def docker_available() -> bool:
    try:
        r = subprocess.run(["docker", "info", "--format", "{{.ServerVersion}}"], capture_output=True,
                           timeout=30)
        return r.returncode == 0
    except (OSError, subprocess.TimeoutExpired):
        return False


def image_id(image: str) -> str | None:
    r = subprocess.run(["docker", "image", "inspect", image, "--format", "{{.Id}}"],
                       capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 else None


def _safe_extract_tar_bytes(data: bytes, dest: str) -> None:
    with tarfile.open(fileobj=io.BytesIO(data), mode="r:") as tar:
        for m in tar:
            name = m.name
            while name.startswith("./"):
                name = name[2:]
            if name in ("", "."):
                continue
            parts = name.rstrip("/").split("/")
            for c in parts:
                canon_hash._check_component(c)
            target = os.path.join(dest, *parts)
            if m.type == tarfile.DIRTYPE:
                os.makedirs(target, exist_ok=True)
            elif m.type in (tarfile.REGTYPE, tarfile.AREGTYPE):
                os.makedirs(os.path.dirname(target), exist_ok=True)
                f = tar.extractfile(m)
                assert f is not None
                fd = os.open(target, os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0), 0o644)
                with os.fdopen(fd, "wb") as out:
                    out.write(f.read())
            else:
                raise SandboxError(f"optimizer produced a non-regular file: {m.name!r}")


def run_optimizer(cand_dir: str, in_dir: str, out_dir: str, spec: dict) -> dict:
    """Run `node <entry> /in /out` from the candidate repo in a locked-down
    container. Returns {"exit": code, "log": text, "seconds": t}."""
    image = spec["image_id"]
    lim = spec["limits"]
    if image_id(image) != image:
        raise SandboxError(f"pinned optimizer image {image} is not available locally")
    entry = spec["entry"]
    inner = (f"timeout -s KILL {int(lim['seconds'])} node /cand/{entry} /in /out > /tmp/log 2>&1; "
             "ec=$?; head -c 65536 /tmp/log > /out/.sandbox-log 2>/dev/null; "
             "echo $ec > /out/.sandbox-exit; tar -C /out -cf - .")
    name = "bendverify-opt-" + os.urandom(8).hex()
    cmd = ["docker", "run", "--rm", "--name", name,
           "--network", "none", "--read-only", "--cap-drop", "ALL",
           "--security-opt", "no-new-privileges", "--user", "65534:65534",
           "--pids-limit", str(int(lim["pids"])),
           "--memory", f"{int(lim['memory_mb'])}m", "--memory-swap", f"{int(lim['memory_mb'])}m",
           "--cpus", str(lim["cpus"]),
           "--tmpfs", f"/out:rw,nosuid,nodev,size={int(lim['out_mb'])}m,mode=1777",
           "--tmpfs", f"/tmp:rw,nosuid,nodev,noexec,size={int(lim['tmp_mb'])}m,mode=1777",
           "-v", f"{os.path.abspath(cand_dir)}:/cand:ro",
           "-v", f"{os.path.abspath(in_dir)}:/in:ro",
           "-e", "HOME=/tmp", "-e", "NODE_OPTIONS=", "--workdir", "/cand",
           "--entrypoint", "/bin/sh", image, "-c", inner]
    t0 = time.time()
    try:
        p = subprocess.run(cmd, capture_output=True, timeout=int(lim["seconds"]) + 120)
    except subprocess.TimeoutExpired as e:
        subprocess.run(["docker", "kill", name], capture_output=True)
        raise SandboxError("optimizer sandbox exceeded the wall-clock limit") from e
    dt = time.time() - t0
    if len(p.stdout) > MAX_OUTPUT:
        raise SandboxError("optimizer output too large")
    if p.returncode != 0 or not p.stdout:
        raise SandboxError(f"optimizer sandbox failed (docker exit {p.returncode}): "
                           f"{p.stderr.decode(errors='replace')[-500:]}")
    os.makedirs(out_dir, exist_ok=False)
    _safe_extract_tar_bytes(p.stdout, out_dir)
    try:
        code = int(open(os.path.join(out_dir, ".sandbox-exit")).read().strip())
        log = open(os.path.join(out_dir, ".sandbox-log"), errors="replace").read()
    except (OSError, ValueError) as e:
        raise SandboxError("optimizer sandbox did not report an exit status") from e
    os.unlink(os.path.join(out_dir, ".sandbox-exit"))
    os.unlink(os.path.join(out_dir, ".sandbox-log"))
    return {"exit": code, "log": log, "seconds": round(dt, 3)}


# --------------------------------------------------------------- sandbox-exec

def _profile(read_paths: list[str], write_paths: list[str], exec_paths: list[str]) -> str:
    q = lambda p: '"' + os.path.realpath(p).replace('\\', '\\\\').replace('"', '\\"') + '"'  # noqa: E731
    lines = ["(version 1)", "(allow default)", "(deny network*)",
             "(deny file-write*)",
             '(allow file-write* (literal "/dev/null") (literal "/dev/tty"))']
    for w in write_paths:
        lines.append(f"(allow file-write* (subpath {q(w)}))")
    home = os.path.expanduser("~")
    # no file CONTENT below the user's home is readable except the paths we
    # need (metadata stays readable: path resolution stats parent directories)
    lines.append(f"(deny file-read-data (subpath {q(home)}))")
    # (the operation must be named exactly: a wildcard `file-read*` allow does not
    #  override the more specific `file-read-data` deny)
    for r in read_paths + exec_paths + write_paths:
        lines.append(f"(allow file-read-data (subpath {q(r)}))")
        lines.append(f"(allow file-map-executable (subpath {q(r)}))")
    return "\n".join(lines)


def _limits(cpu_seconds: int, fsize_mb: int):
    def apply():
        resource.setrlimit(resource.RLIMIT_CPU, (cpu_seconds, cpu_seconds))
        resource.setrlimit(resource.RLIMIT_FSIZE, (fsize_mb << 20, fsize_mb << 20))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        os.setsid()
    return apply


def run_confined(cmd: list[str], *, read_paths: list[str], write_paths: list[str],
                 env: dict | None = None, cpu_seconds: int = 600, wall_seconds: int = 900,
                 fsize_mb: int = 1024, cwd: str | None = None, input: bytes | None = None
                 ) -> subprocess.CompletedProcess:
    """Run a trusted tool or a compiled workload with no network, confined writes,
    no access to the user's home except `read_paths`, an empty-ish environment
    and resource limits."""
    exec_paths = [os.path.dirname(os.path.realpath(shutil.which(cmd[0]) or cmd[0]))]
    prof = _profile(read_paths, write_paths, exec_paths)
    full = ["/usr/bin/sandbox-exec", "-p", prof] + cmd if sys.platform == "darwin" else cmd
    base_env = {"PATH": "/usr/bin:/bin", "LANG": "C", "LC_ALL": "C"}
    if env:
        base_env.update(env)
    try:
        return subprocess.run(full, capture_output=True, env=base_env, cwd=cwd, input=input,
                              timeout=wall_seconds, preexec_fn=_limits(cpu_seconds, fsize_mb))
    except subprocess.TimeoutExpired as e:
        raise SandboxError(f"{os.path.basename(cmd[0])} exceeded {wall_seconds}s") from e


def scratch(prefix: str) -> str:
    return tempfile.mkdtemp(prefix=f"bendverify-{prefix}-")
