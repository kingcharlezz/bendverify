"""Proof obligation generation and independent proof checking. TRUSTED.

1. `obligation.generate` (trusted/proof-generator) renders the exact
   proposition from the verifier's own copies of the programs.
2. The obligation module is compiled by the pinned Lean toolchain. Library-rule
   steps are proved *inside* it by kernel evaluation of the rule checker, so a
   false rule claim makes compilation fail.
3. The competitor's proof export is inspected in Python (structure, allowed
   declaration kinds, forbidden constants, declared imports), independently of
   Lean.
4. The Lean replay checker (trusted/verifier/checker) re-checks every exported
   declaration in the kernel, requires each lemma-step proof to have exactly the
   generated goal as its type, composes the root theorem, and audits the axiom
   closure.
5. The checker's JSON verdict is parsed structurally and every field is
   re-validated here; the exit code alone is never trusted.
"""

from __future__ import annotations

import json
import os
import re
import shutil

from . import sandbox
from .competition import ROOT, canon_hash

import obligation  # trusted/proof-generator/obligation.py

FORBIDDEN_CONSTANTS = {"sorryAx", "Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler",
                       "Lean.reduceBool", "Lean.reduceNat"}
IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*$")


class ProofError(Exception):
    pass


# ------------------------------------------------------------------ toolchain

def lean_bin(tc: dict, name: str) -> str:
    return os.path.join(tc["lean_toolchain"], "bin", name)


def build_spec_library(tc: dict, cache: str, spec_hash: str) -> str:
    """Build BendVerify from the pinned sources into a verifier-owned cache
    (never from a candidate). Returns the directory to put on LEAN_PATH."""
    out = os.path.join(cache, "spec-" + spec_hash.split(":")[1][:24])
    lib = os.path.join(out, ".lake", "build", "lib", "lean")
    if os.path.isfile(os.path.join(lib, "BendVerify.olean")):
        return lib
    tmp = out + ".tmp"
    shutil.rmtree(tmp, ignore_errors=True)
    src = os.path.join(ROOT, "trusted", "spec", "lean")
    shutil.copytree(src, tmp, ignore=shutil.ignore_patterns(".lake", "lake-manifest.json"))
    r = sandbox.run_confined([lean_bin(tc, "lake"), "build"], cwd=tmp,
                             read_paths=[tmp, tc["lean_toolchain"]], write_paths=[tmp],
                             env={"PATH": os.path.join(tc["lean_toolchain"], "bin") + ":/usr/bin:/bin"},
                             cpu_seconds=1800, wall_seconds=2400)
    if r.returncode != 0:
        raise ProofError(f"building the trusted spec failed:\n{r.stdout.decode()[-2000:]}")
    os.replace(tmp, out)
    return lib


def build_checker(tc: dict, cache: str, verifier_hash: str) -> str:
    out = os.path.join(cache, "checker-" + verifier_hash.split(":")[1][:24])
    exe = os.path.join(out, ".lake", "build", "bin", "bendverify-check")
    if os.path.isfile(exe):
        return exe
    tmp = out + ".tmp"
    shutil.rmtree(tmp, ignore_errors=True)
    shutil.copytree(os.path.join(ROOT, "trusted", "verifier", "checker"), tmp,
                    ignore=shutil.ignore_patterns(".lake", "lake-manifest.json"))
    r = sandbox.run_confined([lean_bin(tc, "lake"), "build"], cwd=tmp,
                             read_paths=[tmp, tc["lean_toolchain"], "/Library/Developer"],
                             write_paths=[tmp, "/private/var/folders", "/private/tmp"],
                             env={"PATH": os.path.join(tc["lean_toolchain"], "bin") + ":/usr/bin:/bin",
                                  "TMPDIR": tmp},
                             cpu_seconds=1800, wall_seconds=2400)
    if r.returncode != 0:
        raise ProofError(f"building the trusted checker failed:\n{r.stdout.decode()[-2000:]}")
    os.replace(tmp, out)
    return exe


# ------------------------------------------------------------------ obligation

def _failed_steps(text: str, out: str) -> list[str]:
    """Diagnostics only: the generated `w.step_k` declarations that Lean's errors point into."""
    lines = text.split("\n")
    found = set()
    for m in re.finditer(r"Obligation\.lean:(\d+):\d+: error", out):
        ns = decl = None
        for ln in lines[:int(m.group(1))]:
            if (d := re.match(r"namespace (\S+)$", ln)) and d.group(1) != "Contest.Obligation":
                ns = d.group(1)
            if (d := re.match(r"theorem (step_\d+) ", ln)):
                decl = d.group(1)
            elif re.match(r"(theorem|def) ", ln):
                decl = None
        if ns and decl:
            found.add(f"{ns}.{decl}")
    return sorted(found)


def make_obligation(tc: dict, spec_lib: str, work: str, workloads: list, stamp: str) -> dict:
    text, goals = obligation.generate(workloads, stamp)
    obl = os.path.join(work, "obligation")
    os.makedirs(os.path.join(obl, "Contest"), exist_ok=True)
    src = os.path.join(obl, "Contest", "Obligation.lean")
    with open(src, "w") as f:
        f.write(text)
    r = sandbox.run_confined(
        [lean_bin(tc, "lean"), "-o", os.path.join(obl, "Contest", "Obligation.olean"),
         os.path.join("Contest", "Obligation.lean")],
        cwd=obl, read_paths=[obl, spec_lib, tc["lean_toolchain"]], write_paths=[obl],
        env={"LEAN_PATH": f"{spec_lib}:{obl}"}, cpu_seconds=1800, wall_seconds=2400)
    if r.returncode != 0:
        out = (r.stdout + r.stderr).decode(errors="replace")
        failed = _failed_steps(text, out)
        where = f" (library-rule step(s) {', '.join(failed)} do not check)" if failed else ""
        raise ProofError(f"obligation rejected by Lean{where}:\n{out[-1500:]}")
    return {"dir": obl, "source_digest": canon_hash.file_digest(src), "goals": goals}


# ------------------------------------------------------------------ export inspection

def inspect_export(path: str, allowed_imports: list[str], max_bytes: int = 64 << 20) -> dict:
    """Independent (non-Lean) structural inspection of a proof export."""
    if os.path.getsize(path) > max_bytes:
        raise ProofError("proof export too large")
    try:
        with open(path, "rb") as f:
            ex = json.loads(f.read().decode("utf-8"))
    except (ValueError, UnicodeDecodeError) as e:
        raise ProofError(f"proof export is not JSON: {e}") from e
    if not isinstance(ex, dict) or set(ex) != {"format", "imports", "names", "levels", "exprs", "decls"}:
        raise ProofError("proof export has unexpected top-level fields")
    if ex["format"] != "bendverify-export-v1":
        raise ProofError("unsupported proof export format")
    for imp in ex["imports"]:
        if not isinstance(imp, str) or not any(imp == a or imp.startswith(a + ".") for a in allowed_imports):
            raise ProofError(f"proof imports a module outside the trusted allowlist: {imp}")
    names: list[str] = [""]
    for j in ex["names"]:
        if not (isinstance(j, list) and len(j) == 3 and j[0] in ("s", "n") and isinstance(j[1], int)
                and 0 <= j[1] < len(names)):
            raise ProofError("malformed name table")
        parent = names[j[1]]
        comp = j[2] if j[0] == "s" else str(j[2])
        names.append(f"{parent}.{comp}" if parent else comp)
    referenced = set()
    for j in ex["exprs"]:
        if not isinstance(j, list) or not j:
            raise ProofError("malformed expression table")
        if j[0] == "c":
            if not (isinstance(j[1], int) and 0 <= j[1] < len(names)):
                raise ProofError("malformed constant reference")
            referenced.add(names[j[1]])
    bad = sorted(referenced & FORBIDDEN_CONSTANTS)
    if bad:
        raise ProofError(f"proof references forbidden constant(s): {', '.join(bad)}")
    decl_names = []

    def name_of(i):
        if not (isinstance(i, int) and 0 <= i < len(names)):
            raise ProofError("malformed declaration name")
        return names[i]

    for d in ex["decls"]:
        if not isinstance(d, dict) or d.get("k") not in ("thm", "def", "ind"):
            raise ProofError(f"forbidden declaration kind {d.get('k') if isinstance(d, dict) else d!r}")
        if d["k"] == "ind":
            if not isinstance(d.get("types"), list) or not d["types"]:
                raise ProofError("malformed inductive block")
            new = []
            for ty in d["types"]:
                if not isinstance(ty, dict) or not isinstance(ty.get("ctors"), list):
                    raise ProofError("malformed inductive type")
                new.append(name_of(ty.get("n")))
                new += [name_of(c.get("n")) if isinstance(c, dict) else name_of(None) for c in ty["ctors"]]
        else:
            new = [name_of(d.get("n"))]
        for n in new:
            if n.split(".")[0] == "Contest":
                raise ProofError(f"declaration {n} is in the reserved Contest namespace")
        decl_names += new
    if len(set(decl_names)) != len(decl_names):
        raise ProofError("duplicate declarations in proof export")
    return {"declarations": len(decl_names), "names": sorted(decl_names),
            "referenced_constants": len(referenced), "imports": ex["imports"]}


# ------------------------------------------------------------------ kernel check

def kernel_check(tc: dict, checker: str, spec_lib: str, obl: dict, export: str, proofs: list[str],
                 comp: dict, work: str) -> dict:
    goals = obl["goals"]
    if len(goals) != len(proofs):
        raise ProofError("number of lemma proofs does not match the number of lemma steps")
    for p in proofs:
        if not IDENT_RE.match(p) or p.split(".")[0] == "Contest":
            raise ProofError(f"invalid proof constant name {p!r}")
    req = {
        "lean_sysroot": tc["lean_toolchain"],
        "imports": comp["rules"]["trusted_imports"],
        "export": export,
        "goals": [{"goal": g, "proof": p} for g, p in zip(goals, proofs)],
        "compose": {"name": "Contest.Certified.root", "type": "Contest.Obligation.RootGoal",
                    "fn": "Contest.Obligation.root_of_steps"},
        "allowed_axioms": comp["rules"]["allowed_axioms"],
        "reserved_prefixes": ["Contest"],
    }
    req_path = os.path.join(work, "check-request.json")
    with open(req_path, "w") as f:
        json.dump(req, f)
    r = sandbox.run_confined([checker, req_path],
                             read_paths=[work, spec_lib, obl["dir"], tc["lean_toolchain"], os.path.dirname(export),
                                         os.path.dirname(checker)],
                             write_paths=[work], env={"LEAN_PATH": f"{spec_lib}:{obl['dir']}"},
                             cpu_seconds=3600, wall_seconds=3600, fsize_mb=64)
    out = r.stdout.decode(errors="replace").strip()
    lines = out.splitlines()
    if len(lines) != 1:
        raise ProofError(f"checker produced malformed output (exit {r.returncode}): {out[-500:]} "
                         f"{r.stderr.decode(errors='replace')[-500:]}")
    try:
        res = json.loads(lines[0])
    except ValueError as e:
        raise ProofError("checker output is not JSON") from e
    if not isinstance(res, dict):
        raise ProofError("checker output is not an object")
    if res.get("result") != "PASS":
        raise ProofError(f"kernel check failed: {res.get('reason', 'no reason given')}")
    # structural re-validation of a PASS verdict (never trust the exit code alone)
    if r.returncode != 0:
        raise ProofError("checker reported PASS with a non-zero exit code")
    if set(res) != {"result", "kernel_replayed", "goals", "root"}:
        raise ProofError("checker PASS verdict has unexpected fields")
    allowed = set(comp["rules"]["allowed_axioms"])
    got = [(g.get("goal"), g.get("proof")) for g in res["goals"]]
    want = [(x["goal"], x["proof"]) for x in req["goals"]]
    if got != want:
        raise ProofError("checker verdict does not cover exactly the generated goals")
    for g in res["goals"]:
        if not set(g.get("axioms", ["?"])) <= allowed:
            raise ProofError(f"non-allowlisted axioms {g.get('axioms')}")
    root = res["root"]
    if root.get("name") != "Contest.Certified.root" or root.get("type") != "Contest.Obligation.RootGoal":
        raise ProofError("checker verdict certifies an unexpected root")
    if not set(root.get("axioms", ["?"])) <= allowed:
        raise ProofError(f"root uses non-allowlisted axioms {root.get('axioms')}")
    return res
