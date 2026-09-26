"""Competition definition, trusted-base self-check and competition id. TRUSTED.

`competition.json` (repository root) pins everything that must be immutable
for one competition version: the formal semantics, the verifier, the proof
obligation generator, the hash algorithm and normalisation, the submission
schema, the benchmark definition, the allowed targets and assumptions, the
toolchain identities and the reference Bend commit.

On every run the verifier recomputes the digest of every trusted file and of
every group, recomputes the competition id, and REFUSES TO RUN if anything
differs ("modified verifier / modified spec").

    competition_id = sha256( "bendverify-competition-id-v1\\n"
                             || spec_hash || "\\n" || verifier_hash || "\\n"
                             || benchmark_hash || "\\n" || rules_hash )
"""

from __future__ import annotations

import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "trusted", "hasher"))
sys.path.insert(0, os.path.join(ROOT, "trusted", "schema"))
sys.path.insert(0, os.path.join(ROOT, "trusted", "proof-generator"))
sys.path.insert(0, os.path.join(ROOT, "trusted", "verifier", "bend"))

import canon_hash  # noqa: E402

COMPETITION_FILE = os.path.join(ROOT, "competition.json")

# Which files belong to each trusted group. Build outputs are excluded (they
# are regenerated from the pinned sources by the verifier itself).
GROUPS = {
    "spec": ["trusted/spec"],
    "verifier": ["trusted/verifier", "trusted/proof-generator", "trusted/hasher",
                 "trusted/schema", "scripts"],
    "benchmark": ["trusted/benchmark"],
}
EXCLUDE_DIRS = {".lake", "__pycache__", ".git"}
EXCLUDE_FILES = {".DS_Store", "lake-manifest.json"}


class CompetitionError(Exception):
    pass


def _group_files(roots: list[str]) -> list[str]:
    out = []
    for r in roots:
        base = os.path.join(ROOT, r)
        for dirpath, dirnames, filenames in os.walk(base):
            dirnames[:] = sorted(d for d in dirnames if d not in EXCLUDE_DIRS)
            for f in sorted(filenames):
                if f in EXCLUDE_FILES or f.endswith(".pyc"):
                    continue
                full = os.path.join(dirpath, f)
                if os.path.islink(full):
                    raise CompetitionError(f"symlink inside the trusted base: {full}")
                out.append(os.path.relpath(full, ROOT).replace(os.sep, "/"))
    return sorted(out)


def file_table() -> dict[str, dict[str, str]]:
    return {g: {p: canon_hash.file_digest(os.path.join(ROOT, p)) for p in _group_files(roots)}
            for g, roots in GROUPS.items()}


def group_digest(table: dict[str, str]) -> str:
    h = hashlib.sha256(b"bendverify-group-v1\n")
    for p in sorted(table):
        h.update(p.encode() + b"\x00" + table[p].encode() + b"\n")
    return "sha256:" + h.hexdigest()


def competition_id(spec_hash: str, verifier_hash: str, benchmark_hash: str, rules_hash: str) -> str:
    data = "bendverify-competition-id-v1\n" + "\n".join([spec_hash, verifier_hash, benchmark_hash, rules_hash])
    return "sha256:" + hashlib.sha256(data.encode()).hexdigest()


def load(self_check: bool = True) -> dict:
    """Load competition.json and (by default) verify the trusted base against it."""
    try:
        with open(COMPETITION_FILE, "rb") as f:
            comp = json.loads(f.read().decode("utf-8"))
    except (OSError, ValueError) as e:
        raise CompetitionError(f"cannot read competition.json: {e}") from e
    rules_hash = canon_hash.json_digest(comp["rules"])
    if rules_hash != comp["hashes"]["rules_hash"]:
        raise CompetitionError("competition rules differ from their pinned digest")
    if self_check:
        table = file_table()
        for g in GROUPS:
            pinned = comp["trusted_files"][g]
            if set(pinned) != set(table[g]):
                extra = sorted(set(table[g]) ^ set(pinned))
                raise CompetitionError(f"trusted base modified: file set of '{g}' differs: {extra[:5]}")
            for p, d in table[g].items():
                if pinned[p] != d:
                    raise CompetitionError(f"trusted base modified: {p}")
            if group_digest(table[g]) != comp["hashes"][f"{g}_hash"]:
                raise CompetitionError(f"trusted base modified: group {g}")
    cid = competition_id(comp["hashes"]["spec_hash"], comp["hashes"]["verifier_hash"],
                         comp["hashes"]["benchmark_hash"], rules_hash)
    if cid != comp["competition_id"]:
        raise CompetitionError("competition id does not match the pinned data")
    return comp
