"""Submission manifest and certificate-chain schemas (competition v1). TRUSTED.

manifest.json  (competitor-written; every hash in it is a CLAIM that the
verifier recomputes and compares):

  {
    "schema": "bendverify-submission-v1",
    "competition_id": "sha256:<64 hex>",
    "reference_commit": "<40 hex>",
    "candidate_repo_hash": "sha256:<64 hex>",     # bendverify-tree-v1 digest of bend/
    "proof_hash": "sha256:<64 hex>",              # bendverify-tree-v1 digest of proof/
    "proof": {"export": "<file in proof/>", "imports": ["<module>", ...]},
    "workloads": {"<name>": {"candidate_ir_hash": "sha256:<64 hex>"}}
  }

chain.json  (written by the competitor's optimizer inside the sandbox):

  {
    "format": "bendverify-chain-v1",
    "workload": "<name>",
    "steps": [
      {"kind": "rule", "fn": int, "path": [int, ...],
       "rule": {"name": "inline" | "caseCtr" | "natLit"} | {"name": "fold", "bool_adt": int},
       "program": "<file>.ir.json"},
      {"kind": "lemma", "proof": "<Lean constant name>", "program": "<file>.ir.json"}
    ]
  }
"""

from __future__ import annotations

import re

HASH_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")
FILE_RE = re.compile(r"^[A-Za-z0-9_][A-Za-z0-9_.-]{0,63}$")
PROGRAM_RE = re.compile(r"^[A-Za-z0-9_][A-Za-z0-9_.-]{0,55}\.ir\.json$")
MODULE_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*$")
CONST_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*$")
WORKLOAD_RE = re.compile(r"^[a-z0-9][a-z0-9-]{0,63}$")


class SchemaError(Exception):
    pass


def _exact(obj, keys, what):
    if not isinstance(obj, dict) or set(obj) != set(keys):
        raise SchemaError(f"{what}: expected exactly the fields {sorted(keys)}")


def _int(x, what, lo=0, hi=2 ** 31):
    if not (isinstance(x, int) and not isinstance(x, bool) and lo <= x < hi):
        raise SchemaError(f"{what}: expected an integer in [{lo}, {hi})")
    return x


def validate_manifest(m) -> dict:
    _exact(m, ["schema", "competition_id", "reference_commit", "candidate_repo_hash", "proof_hash",
               "proof", "workloads"], "manifest")
    if m["schema"] != "bendverify-submission-v1":
        raise SchemaError("manifest: unsupported schema")
    for k in ("competition_id", "candidate_repo_hash", "proof_hash"):
        if not isinstance(m[k], str) or not HASH_RE.match(m[k]):
            raise SchemaError(f"manifest: {k} is not a sha256 digest")
    if not isinstance(m["reference_commit"], str) or not COMMIT_RE.match(m["reference_commit"]):
        raise SchemaError("manifest: reference_commit")
    _exact(m["proof"], ["export", "imports"], "manifest.proof")
    if m["proof"]["export"] is not None and (not isinstance(m["proof"]["export"], str)
                                             or not FILE_RE.match(m["proof"]["export"])):
        raise SchemaError("manifest.proof.export must be a plain file name in proof/ or null")
    if not isinstance(m["proof"]["imports"], list) or len(m["proof"]["imports"]) > 64:
        raise SchemaError("manifest.proof.imports")
    for i in m["proof"]["imports"]:
        if not isinstance(i, str) or not MODULE_RE.match(i):
            raise SchemaError("manifest.proof.imports: invalid module name")
    if not isinstance(m["workloads"], dict) or not m["workloads"]:
        raise SchemaError("manifest.workloads")
    for w, v in m["workloads"].items():
        if not WORKLOAD_RE.match(w):
            raise SchemaError("manifest.workloads: invalid workload name")
        _exact(v, ["candidate_ir_hash"], f"manifest.workloads.{w}")
        if not isinstance(v["candidate_ir_hash"], str) or not HASH_RE.match(v["candidate_ir_hash"]):
            raise SchemaError(f"manifest.workloads.{w}.candidate_ir_hash")
    return m


def validate_chain(c, workload: str, max_steps: int) -> dict:
    _exact(c, ["format", "workload", "steps"], "chain")
    if c["format"] != "bendverify-chain-v1" or c["workload"] != workload:
        raise SchemaError("chain: wrong format or workload")
    if not isinstance(c["steps"], list) or len(c["steps"]) > max_steps:
        raise SchemaError("chain: too many steps")
    for k, s in enumerate(c["steps"]):
        if not isinstance(s, dict):
            raise SchemaError(f"chain step {k}: not an object")
        if s.get("kind") == "rule":
            _exact(s, ["kind", "fn", "path", "rule", "program"], f"chain step {k}")
            _int(s["fn"], f"chain step {k}.fn", 0, 4096)
            if not isinstance(s["path"], list) or len(s["path"]) > 256:
                raise SchemaError(f"chain step {k}.path")
            for p in s["path"]:
                _int(p, f"chain step {k}.path", 0, 4096)
            r = s["rule"]
            if not isinstance(r, dict):
                raise SchemaError(f"chain step {k}.rule")
            if r.get("name") == "fold":
                _exact(r, ["name", "bool_adt"], f"chain step {k}.rule")
                _int(r["bool_adt"], f"chain step {k}.rule.bool_adt", 0, 256)
            elif r.get("name") in ("inline", "caseCtr", "natLit"):
                _exact(r, ["name"], f"chain step {k}.rule")
            else:
                raise SchemaError(f"chain step {k}: unknown library rule {r.get('name')!r}")
        elif s.get("kind") == "lemma":
            _exact(s, ["kind", "proof", "program"], f"chain step {k}")
            if not isinstance(s["proof"], str) or not CONST_RE.match(s["proof"]) or len(s["proof"]) > 256:
                raise SchemaError(f"chain step {k}: invalid proof constant name")
        else:
            raise SchemaError(f"chain step {k}: unknown kind")
        if not isinstance(s["program"], str) or not PROGRAM_RE.match(s["program"]):
            raise SchemaError(f"chain step {k}: invalid program file name")
    return c
