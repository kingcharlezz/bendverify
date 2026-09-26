"""Shared machinery for the adversarial tests.

Builds ONE honest, valid submission (the valid example: tree-radix and lexer, with its
Lean proofs) and lets each test derive a hostile variant from a fresh copy.
Every exploit found while building the system is a permanent test here.
"""
from __future__ import annotations

import io
import json
import os
import shutil
import subprocess
import sys
import tarfile

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "trusted", "verifier"))
sys.path.insert(0, os.path.join(ROOT, "trusted", "benchmark"))

from bendverify import archive, verify as V  # noqa: E402
from bendverify.competition import canon_hash, load as load_competition  # noqa: E402

WORK = os.path.join(ROOT, "work", "adversarial")
BASE = os.path.join(WORK, "base")


def sh(*cmd, cwd=ROOT, check=True):
    r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    if check and r.returncode != 0:
        raise RuntimeError(f"{cmd} failed:\n{r.stdout}\n{r.stderr}")
    return r


def ensure_base() -> str:
    """Materialize + prove the valid candidate once (per competition version)."""
    comp = load_competition(self_check=False)
    stamp = os.path.join(BASE, ".competition")
    if os.path.isfile(stamp) and open(stamp).read() == comp["competition_id"]:
        return BASE
    shutil.rmtree(BASE, ignore_errors=True)
    os.makedirs(WORK, exist_ok=True)
    sh(os.path.join(ROOT, "examples", "materialize"), os.path.join(ROOT, "examples", "valid-optimization"), BASE)
    sh(os.path.join(ROOT, "competitor-sdk", "tools", "prove-candidate"), BASE)
    with open(stamp, "w") as f:
        f.write(comp["competition_id"])
    return BASE


def fresh(name: str) -> str:
    """A private copy of the valid candidate directory."""
    ensure_base()
    d = os.path.join(WORK, name)
    shutil.rmtree(d, ignore_errors=True)
    shutil.copytree(BASE, d, ignore=shutil.ignore_patterns(".competition"))
    return d


def package(cand: str, out: str | None = None) -> str:
    out = out or cand + ".tar.zst"
    sh(os.path.join(ROOT, "scripts", "package-submission"), cand, "-o", out)
    return out


def verify(archive_path: str) -> dict:
    return V.verify(archive_path, log=lambda *a: None)


def reprove(cand: str) -> None:
    sh(os.path.join(ROOT, "competitor-sdk", "tools", "prove-candidate"), cand)


def reclaim(cand: str) -> None:
    """Recompute claims but keep the (possibly stale) proof/ directory."""
    sh(os.path.join(ROOT, "competitor-sdk", "tools", "prove-candidate"), cand, "--no-prove")


def edit_json(path: str, fn) -> None:
    with open(path) as f:
        data = json.load(f)
    r = fn(data)          # edits in place; a returned dict replaces the document
    if isinstance(r, dict):
        data = r
    with open(path, "w") as f:
        json.dump(data, f)


def raw_archive(out: str, members: list[tuple[tarfile.TarInfo, bytes | None]]) -> str:
    """Write a hand-crafted (hostile) tar.zst."""
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w", format=tarfile.PAX_FORMAT) as t:
        for ti, data in members:
            t.addfile(ti, io.BytesIO(data) if data is not None else None)
    r = subprocess.run(["zstd", "-q", "-c"], input=buf.getvalue(), capture_output=True)
    with open(out, "wb") as f:
        f.write(r.stdout)
    return out


def tinfo(name: str, kind=tarfile.REGTYPE, size: int = 0, linkname: str = "", mode: int = 0o644):
    ti = tarfile.TarInfo(name)
    ti.type, ti.size, ti.linkname, ti.mode, ti.mtime = kind, size, linkname, mode, 0
    return ti


def valid_members_prefix() -> list:
    """The manifest of the valid submission as a raw member list (for crafting archives)."""
    cand = ensure_base()
    comp = load_competition(self_check=False)
    sub = json.load(open(os.path.join(cand, "submission.json")))
    m = {"schema": "bendverify-submission-v1", "competition_id": comp["competition_id"],
         "reference_commit": comp["rules"]["reference_commit"],
         "candidate_repo_hash": "sha256:" + "0" * 64, "proof_hash": "sha256:" + "0" * 64,
         "proof": sub["proof"], "workloads": sub["workloads"]}
    data = json.dumps(m).encode()
    return [(tinfo("submission", tarfile.DIRTYPE, mode=0o755), None),
            (tinfo("submission/manifest.json", size=len(data)), data)]
