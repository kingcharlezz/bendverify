"""Canonical submission archives (.tar.zst). TRUSTED.

pack():  deterministic archive of a submission directory
         (sorted entries, mtime 0, uid/gid 0, modes 0755/0644 from the
         executable bit only, PAX format, zstd level 19 single-threaded).
unpack(): hostile-input extraction. Rejects, instead of "fixing":
         absolute paths, "..", ".", empty or non-NFC components, backslashes,
         control characters, entries outside the single top-level directory
         `submission/`, symlinks, hard links, devices, FIFOs, sparse/other
         entry types, duplicate or case-colliding names, and archives exceeding
         the size/count limits. Files are created with O_EXCL|O_NOFOLLOW inside
         a fresh directory, so nothing outside it can be touched.
"""

from __future__ import annotations

import io
import os
import subprocess
import tarfile
import tempfile

from .competition import canon_hash

MAX_COMPRESSED = 256 * 1024 * 1024
MAX_UNCOMPRESSED = 512 * 1024 * 1024
MAX_ENTRIES = 25000
TOP = "submission"


class ArchiveError(Exception):
    pass


def pack(src_dir: str, out_path: str, zstd: str = "zstd") -> None:
    if os.path.islink(src_dir) or not os.path.isdir(src_dir):
        raise ArchiveError(f"{src_dir}: not a directory")
    entries = []
    for dirpath, dirnames, filenames in os.walk(src_dir):
        dirnames.sort()
        rel_dir = os.path.relpath(dirpath, src_dir)
        for d in dirnames:
            full = os.path.join(dirpath, d)
            if os.path.islink(full):
                raise ArchiveError(f"symlink not allowed: {full}")
            entries.append((os.path.normpath(os.path.join(rel_dir, d)), full, True))
        for f in sorted(filenames):
            full = os.path.join(dirpath, f)
            if os.path.islink(full) or not os.path.isfile(full):
                raise ArchiveError(f"only regular files may be packaged: {full}")
            entries.append((os.path.normpath(os.path.join(rel_dir, f)), full, False))
    entries.sort(key=lambda e: e[0].encode("utf-8"))
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w", format=tarfile.PAX_FORMAT) as tar:
        root = tarfile.TarInfo(TOP)
        root.type, root.mode, root.mtime = tarfile.DIRTYPE, 0o755, 0
        tar.addfile(root)
        for rel, full, is_dir in entries:
            ti = tarfile.TarInfo(f"{TOP}/{rel.replace(os.sep, '/')}")
            ti.mtime, ti.uid, ti.gid, ti.uname, ti.gname = 0, 0, 0, "", ""
            if is_dir:
                ti.type, ti.mode = tarfile.DIRTYPE, 0o755
                tar.addfile(ti)
            else:
                ti.type = tarfile.REGTYPE
                ti.mode = 0o755 if os.stat(full).st_mode & 0o111 else 0o644
                ti.size = os.path.getsize(full)
                with open(full, "rb") as fh:
                    tar.addfile(ti, fh)
    r = subprocess.run([zstd, "-19", "-T1", "-q", "-c", "--no-progress"], input=buf.getvalue(),
                       capture_output=True)
    if r.returncode != 0:
        raise ArchiveError(f"zstd failed: {r.stderr.decode(errors='replace')}")
    with open(out_path, "wb") as f:
        f.write(r.stdout)


def _decompress(path: str, zstd: str) -> str:
    if not os.path.isfile(path) or os.path.islink(path):
        raise ArchiveError(f"{path}: not a regular file")
    if os.path.getsize(path) > MAX_COMPRESSED:
        raise ArchiveError("archive too large")
    fd, tmp = tempfile.mkstemp(suffix=".tar")
    total = 0
    with os.fdopen(fd, "wb") as out:
        p = subprocess.Popen([zstd, "-d", "-c", "-q", "--memory=256MB", path],
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        assert p.stdout is not None
        while True:
            chunk = p.stdout.read(1 << 20)
            if not chunk:
                break
            total += len(chunk)
            if total > MAX_UNCOMPRESSED:
                p.kill()
                p.wait()
                os.unlink(tmp)
                raise ArchiveError("archive expands beyond the size limit (decompression bomb?)")
            out.write(chunk)
        if p.wait() != 0:
            os.unlink(tmp)
            raise ArchiveError("archive is not valid zstd")
    return tmp


def _check_name(name: str) -> list[str]:
    if name.startswith("/") or "\\" in name:
        raise ArchiveError(f"illegal entry name {name!r}")
    parts = name.rstrip("/").split("/")
    for c in parts:
        try:
            canon_hash._check_component(c)
        except canon_hash.HashError as e:
            raise ArchiveError(f"illegal entry name {name!r}: {e}") from e
    if parts[0] != TOP:
        raise ArchiveError(f"entry outside '{TOP}/': {name!r}")
    return parts


def unpack(archive: str, dest: str, zstd: str = "zstd") -> str:
    """Extract into the (new, empty) directory `dest`; return dest/submission."""
    os.makedirs(dest, exist_ok=False)
    tmp = _decompress(archive, zstd)
    try:
        try:
            tar = tarfile.open(tmp, mode="r:")
        except tarfile.TarError as e:
            raise ArchiveError(f"not a tar archive: {e}") from e
        seen: dict[str, str] = {}
        count = 0
        with tar:
            for m in tar:
                count += 1
                if count > MAX_ENTRIES:
                    raise ArchiveError("too many entries")
                parts = _check_name(m.name)
                key = "/".join(parts).casefold()
                if key in seen:
                    raise ArchiveError(f"duplicate or case-colliding entry {m.name!r}")
                seen[key] = m.name
                target = os.path.join(dest, *parts)
                real_dest = os.path.realpath(dest)
                if not os.path.realpath(os.path.dirname(target)).startswith(real_dest):
                    raise ArchiveError(f"entry escapes the extraction directory: {m.name!r}")
                if m.type == tarfile.DIRTYPE:
                    os.makedirs(target, exist_ok=True)
                    continue
                if m.type not in (tarfile.REGTYPE, tarfile.AREGTYPE):
                    kind = {tarfile.SYMTYPE: "symlink", tarfile.LNKTYPE: "hard link",
                            tarfile.CHRTYPE: "device", tarfile.BLKTYPE: "device",
                            tarfile.FIFOTYPE: "fifo"}.get(m.type, f"type {m.type!r}")
                    raise ArchiveError(f"{kind} entries are not allowed: {m.name!r}")
                if m.sparse is not None:
                    raise ArchiveError(f"sparse entries are not allowed: {m.name!r}")
                os.makedirs(os.path.dirname(target), exist_ok=True)
                if os.path.islink(os.path.dirname(target)):
                    raise ArchiveError("symlinked directory in extraction path")
                src = tar.extractfile(m)
                assert src is not None
                flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0)
                mode = 0o755 if m.mode & 0o111 else 0o644
                fd = os.open(target, flags, mode)
                with os.fdopen(fd, "wb") as out:
                    while True:
                        chunk = src.read(1 << 20)
                        if not chunk:
                            break
                        out.write(chunk)
                os.chmod(target, mode)
    finally:
        os.unlink(tmp)
    top = os.path.join(dest, TOP)
    if not os.path.isdir(top):
        raise ArchiveError("archive has no submission/ directory")
    return top
