"""Submission verification: the complete trusted flow. TRUSTED.

    submission.tar.zst
      -> safe extraction                       (archive.unpack)
      -> manifest schema                       (schema/submission.py)
      -> competition id                        (must equal ours)
      -> candidate digest (bend/), proof digest (proof/)  recomputed, compared
      -> boundary: bend/ == pinned reference tree outside bend2/opt/
      -> run the candidate optimizer in the sandbox on the pinned reference IR
      -> validate chain + every program; recompute every intermediate digest
      -> candidate IR == manifest claim
      -> BUILD the exact candidate IR: lower -> reference Bend check -> C
         -> round-trip validation -> clang; hash every artifact
      -> proof obligation (generated here) -> Lean kernel replay of the proof
      -> certificate.json + preserved artifacts in the store

Nothing produced by the competitor is trusted: all digests are recomputed,
the proposition is generated here, the proof is kernel-checked, and the
benchmarked binary is exactly the one built here from the proven IR.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import time

from . import archive, bendtools, proofcheck, sandbox
from .competition import ROOT, canon_hash, load as load_competition

import submission as schema  # trusted/schema/submission.py
import verifiedir            # trusted/schema/verifiedir.py

CERT_SCHEMA = "bendverify-certificate-v1"
CLAIM_B = ("For every workload w of the competition, the exact candidate VerifiedIR program Q_w "
           "(produced by the exact candidate repository) is semantically equivalent to the pinned "
           "reference program P_w: for all well-typed entry arguments and every value v, P_w "
           "terminates with v iff Q_w terminates with v (BendVerify.Equiv), checked by the Lean kernel.")
NOT_CLAIMED = ("NOT claimed (Claim C): that the native executable implements Bend semantics. The "
               "extractor, the reference Bend checker/compiler (comp.ts), clang, the C runtime and the "
               "hardware remain trusted, unverified links.")


class Reject(Exception):
    """The submission is invalid. `stage` names the step that rejected it."""

    def __init__(self, stage: str, msg: str):
        super().__init__(f"[{stage}] {msg}")
        self.stage = stage
        self.msg = msg


def toolchain(comp: dict) -> dict:
    """Locate the pinned tools and check their identities."""
    pins = comp["toolchain"]
    tc_name = "leanprover--lean4---" + pins["lean"]
    candidates = [os.environ.get("BENDVERIFY_LEAN_TOOLCHAIN", ""),
                  os.path.join(os.environ.get("ELAN_HOME", ""), "toolchains", tc_name),
                  os.path.expanduser(os.path.join("~/.elan/toolchains", tc_name))]
    lean_tc = next((c for c in candidates if c and os.path.isfile(os.path.join(c, "bin", "lean"))),
                   candidates[-1])
    tc = {
        "lean_toolchain": lean_tc,
        "node": os.environ.get("BENDVERIFY_NODE", shutil.which("node") or "node"),
        "clang": os.environ.get("BENDVERIFY_CLANG", shutil.which("clang") or "clang"),
        "zstd": os.environ.get("BENDVERIFY_ZSTD", shutil.which("zstd") or "zstd"),
    }
    lean = os.path.join(tc["lean_toolchain"], "bin", "lean")
    try:
        v = subprocess.run([lean, "--version"], capture_output=True, text=True).stdout
    except OSError:
        v = ""
    if pins["lean_commit"] not in v:
        raise Reject("toolchain", f"pinned Lean {pins['lean']} ({pins['lean_commit'][:12]}) not found "
                                  f"at {tc['lean_toolchain']} (set BENDVERIFY_LEAN_TOOLCHAIN)")
    nv = subprocess.run([tc["node"], "--version"], capture_output=True, text=True).stdout.strip()
    if nv != pins["node"]:
        raise Reject("toolchain", f"pinned node {pins['node']} required, found {nv!r} (set BENDVERIFY_NODE)")
    cv = subprocess.run([tc["clang"], "--version"], capture_output=True, text=True).stdout.splitlines()
    if not cv or cv[0].strip() != pins["clang"]:
        raise Reject("toolchain", f"pinned clang '{pins['clang']}' required (set BENDVERIFY_CLANG)")
    return tc


def work_root() -> str:
    # Docker (colima) only shares paths under $HOME, so the workspace lives here.
    return os.environ.get("BENDVERIFY_WORK", os.path.join(ROOT, "work"))


def store_root(comp: dict) -> str:
    return os.path.join(os.environ.get("BENDVERIFY_STORE", os.path.join(ROOT, "store")),
                        comp["competition_id"].split(":")[1][:16])


def check_reference_tree(comp: dict) -> None:
    ref = os.path.join(ROOT, "reference", "bend")
    with open(os.path.join(ROOT, "trusted", "spec", "reference_tree.json")) as f:
        pinned = json.load(f)
    for rel, (execb, digest) in pinned["files"].items():
        p = os.path.join(ref, *rel.split("/"))
        if os.path.islink(p) or not os.path.isfile(p) or canon_hash.file_digest(p) != digest:
            raise Reject("reference", f"reference Bend checkout differs from commit "
                                      f"{pinned['commit'][:12]} at {rel}")


def build_reference(comp: dict, tc: dict, base_names: set[str]) -> dict:
    """Build the reference binaries once (same trusted pipeline as candidates)."""
    out = {}
    for w in comp["rules"]["workloads"]:
        d = os.path.join(store_root(comp), "reference", w["name"])
        meta_path = os.path.join(d, "artifacts.json")
        if os.path.isfile(meta_path):
            with open(meta_path) as f:
                meta = json.load(f)
            if canon_hash.file_digest(meta["paths"]["binary"]) == meta["digests"]["binary"]:
                out[w["name"]] = meta
                continue
        shutil.rmtree(d, ignore_errors=True)
        ir = load_reference_ir(w)
        paths = bendtools.build(tc, ir, w["entry"], d, base_names)
        meta = {"paths": paths, "digests": {k: canon_hash.file_digest(v) for k, v in paths.items()}}
        with open(meta_path, "w") as f:
            json.dump(meta, f, indent=1)
        out[w["name"]] = meta
    return out


def load_reference_ir(w: dict) -> dict:
    p = os.path.join(ROOT, w["reference_ir"])
    with open(p) as f:
        ir = json.load(f)
    if canon_hash.json_digest(ir) != w["reference_ir_hash"]:
        raise Reject("reference", f"pinned reference IR for {w['name']} was modified")
    return verifiedir.validate(ir)


def boundary_check(comp: dict, bend_dir: str, entries: list) -> None:
    with open(os.path.join(ROOT, "trusted", "spec", "reference_tree.json")) as f:
        ref = json.load(f)["files"]
    allowed = tuple(comp["rules"]["allowed_modifications"])
    got = {e.path: e for e in entries}
    for path, (execb, digest) in ref.items():
        if path.startswith(allowed):
            continue
        e = got.get(path)
        if e is None:
            raise Reject("boundary", f"file {path} of the reference repository is missing")
        if e.sha256 != digest or e.executable != execb:
            raise Reject("boundary", f"{path} differs from the reference commit; competition v1 only "
                                     f"allows changes under {', '.join(allowed)}")
    for path in got:
        if path not in ref and not path.startswith(allowed):
            raise Reject("boundary", f"new file {path} outside {', '.join(allowed)}")
    if comp["rules"]["optimizer"]["entry"] not in got:
        raise Reject("boundary", f"missing optimizer entry point {comp['rules']['optimizer']['entry']}")


def verify(archive_path: str, *, log=print) -> dict:
    t_start = time.time()
    comp = load_competition(self_check=True)
    cid = comp["competition_id"]
    tc = toolchain(comp)
    check_reference_tree(comp)
    rules = comp["rules"]
    base_names = set(json.load(open(os.path.join(ROOT, "trusted", "spec", "base_names.json"))))
    os.makedirs(work_root(), exist_ok=True)
    work = os.path.join(work_root(), "v-" + os.urandom(6).hex())
    os.makedirs(work)
    report: dict = {"competition_id": cid, "stages": []}

    def stage(name, msg):
        report["stages"].append({"stage": name, "result": msg})
        log(f"  [{name}] {msg}")

    try:
        # 1. extraction
        try:
            sub = archive.unpack(archive_path, os.path.join(work, "x"), zstd=tc["zstd"])
        except archive.ArchiveError as e:
            raise Reject("archive", str(e))
        top = sorted(os.listdir(sub))
        if top != ["bend", "manifest.json", "proof"]:
            raise Reject("archive", f"submission must contain exactly bend/, proof/, manifest.json (got {top})")
        stage("archive", "extracted safely")
        # 2. manifest
        try:
            with open(os.path.join(sub, "manifest.json"), "rb") as f:
                manifest = schema.validate_manifest(json.loads(f.read().decode("utf-8")))
        except (ValueError, UnicodeDecodeError, schema.SchemaError) as e:
            raise Reject("manifest", str(e))
        if manifest["competition_id"] != cid:
            raise Reject("manifest", "submission targets a different competition id")
        if manifest["reference_commit"] != rules["reference_commit"]:
            raise Reject("manifest", "submission is based on a different reference commit")
        stage("manifest", "schema OK, competition id matches")
        # 3. digests (recomputed; claims only compared)
        try:
            cand_hash, entries = canon_hash.tree_digest(os.path.join(sub, "bend"))
            proof_hash, _ = canon_hash.tree_digest(os.path.join(sub, "proof"))
        except canon_hash.HashError as e:
            raise Reject("hash", str(e))
        if cand_hash != manifest["candidate_repo_hash"]:
            raise Reject("hash", f"candidate digest mismatch: manifest claims {manifest['candidate_repo_hash']}, "
                                 f"recomputed {cand_hash}")
        if proof_hash != manifest["proof_hash"]:
            raise Reject("hash", "proof digest mismatch (proof/ changed after packaging)")
        report["candidate_repo_hash"] = cand_hash
        stage("hash", f"candidate {cand_hash}")
        # 4. boundary
        boundary_check(comp, os.path.join(sub, "bend"), entries)
        stage("boundary", f"only {', '.join(rules['allowed_modifications'])} differs from the reference")
        # 5. optimizer in the sandbox
        in_dir = os.path.join(work, "opt-in")
        os.makedirs(in_dir)
        req = {"competition_id": cid, "workloads": []}
        refs = {}
        for w in rules["workloads"]:
            refs[w["name"]] = load_reference_ir(w)
            with open(os.path.join(in_dir, f"{w['name']}.ir.json"), "w") as f:
                json.dump(refs[w["name"]], f)
            req["workloads"].append({"name": w["name"], "entry": w["entry"], "input": f"{w['name']}.ir.json"})
        with open(os.path.join(in_dir, "request.json"), "w") as f:
            json.dump(req, f)
        opt_out = os.path.join(work, "opt-out")
        try:
            res = sandbox.run_optimizer(os.path.join(sub, "bend"), in_dir, opt_out, rules["optimizer"])
        except (sandbox.SandboxError, Exception) as e:  # noqa: BLE001 - any sandbox failure rejects
            raise Reject("optimizer", f"sandboxed optimizer failed: {e}")
        if res["exit"] != 0:
            raise Reject("optimizer", f"optimizer exited with {res['exit']}: {res['log'][-400:]}")
        stage("optimizer", f"ran in sandbox ({res['seconds']}s)")
        # 6. chains, programs, digests
        cert_workloads = {}
        spec_lib = proofcheck.build_spec_library(tc, os.path.join(work_root(), "cache"), comp["hashes"]["spec_hash"])
        checker = proofcheck.build_checker(tc, os.path.join(work_root(), "cache"), comp["hashes"]["verifier_hash"])
        export_path = None
        if manifest["proof"]["export"] is not None:
            export_path = os.path.join(sub, "proof", manifest["proof"]["export"])
            if not os.path.isfile(export_path):
                raise Reject("proof", "declared proof export is missing")
            try:
                info = proofcheck.inspect_export(export_path, rules["trusted_imports"])
            except proofcheck.ProofError as e:
                raise Reject("proof", str(e))
            if sorted(info["imports"]) != sorted(manifest["proof"]["imports"]):
                raise Reject("proof", "proof's import graph differs from the declared imports")
            stage("proof-inspect", f"{info['declarations']} declarations, imports within allowlist")
        if set(manifest["workloads"]) != {w["name"] for w in rules["workloads"]}:
            raise Reject("manifest", "manifest must list exactly the competition's workloads")
        for w in rules["workloads"]:
            name = w["name"]
            wdir = os.path.join(opt_out, name)
            try:
                with open(os.path.join(wdir, "chain.json"), "rb") as f:
                    chain = schema.validate_chain(json.loads(f.read().decode("utf-8")), name, rules["max_steps"])
            except (OSError, ValueError, UnicodeDecodeError, schema.SchemaError) as e:
                raise Reject("chain", f"{name}: {e}")
            programs = [refs[name]]
            digests = [canon_hash.json_digest(refs[name])]
            for k, s in enumerate(chain["steps"]):
                try:
                    with open(os.path.join(wdir, s["program"]), "rb") as f:
                        prog = verifiedir.validate(json.loads(f.read().decode("utf-8")))
                except (OSError, ValueError, UnicodeDecodeError, verifiedir.IRError) as e:
                    raise Reject("chain", f"{name} step {k}: invalid program: {e}")
                programs.append(prog)
                digests.append(canon_hash.json_digest(prog))
            q = programs[-1]
            q_hash = digests[-1]
            if q_hash != manifest["workloads"][name]["candidate_ir_hash"]:
                raise Reject("artifact", f"{name}: the candidate IR produced by the submitted code "
                                         f"({q_hash}) is not the one the manifest claims")
            stage("chain", f"{name}: {len(chain['steps'])} step(s), candidate IR {q_hash}")
            # 7. build EXACTLY this IR (and validate the lowering)
            try:
                paths = bendtools.build(tc, q, w["entry"], os.path.join(work, "build", name), base_names)
            except bendtools.BuildError as e:
                raise Reject("build", f"{name}: {e}")
            art = {k: canon_hash.file_digest(v) for k, v in paths.items()}
            stage("build", f"{name}: lowered, reference-checked, compiled, round-trip OK")
            ref_fn = next(f for f in refs[name]["fns"] if f["name"] == w["entry"])
            ctx = {"adts": refs[name]["adts"], "entry": w["entry"], "params": ref_fn["params"],
                   "ret": ref_fn["ret"]}
            cert_workloads[name] = {
                "reference_ir_hash": digests[0],
                "candidate_ir_hash": q_hash,
                "chain": [{"kind": s["kind"],
                           **({"rule": s["rule"], "fn": s["fn"], "path": s["path"]} if s["kind"] == "rule"
                              else {"proof": s["proof"]}),
                           "input_hash": digests[k], "output_hash": digests[k + 1]}
                          for k, s in enumerate(chain["steps"])],
                "artifacts": art,
                "_paths": paths,
                "_ir": q,
                "_obl": {"name": name, "ctx": ctx, "programs": programs, "steps": chain["steps"]},
            }
        # 8. the proposition (ONE root for all workloads) and the proof
        stamp = f"bendverify/v1/{cid}/{cand_hash}"
        lemmas = [s["proof"] for w in rules["workloads"]
                  for s in cert_workloads[w["name"]]["_obl"]["steps"] if s["kind"] == "lemma"]
        try:
            obl = proofcheck.make_obligation(tc, spec_lib, os.path.join(work, "proof"),
                                             [cert_workloads[w["name"]]["_obl"] for w in rules["workloads"]],
                                             stamp)
            exp = export_path
            if exp is None:
                if lemmas:
                    raise proofcheck.ProofError("lemma steps require a proof export")
                exp = os.path.join(work, "empty-export.json")
                with open(exp, "w") as f:
                    json.dump({"format": "bendverify-export-v1", "imports": [], "names": [],
                               "levels": [], "exprs": [], "decls": []}, f)
            verdict = proofcheck.kernel_check(tc, checker, spec_lib, obl, exp, lemmas, comp,
                                              os.path.join(work, "proof"))
        except proofcheck.ProofError as e:
            raise Reject("proof", str(e))
        stage("proof", f"kernel replayed {verdict['kernel_replayed']} declarations; root "
                       f"CandidateValid proved with axioms {verdict['root']['axioms']}")
        root = {"theorem": "Contest.Certified.root : Contest.Obligation.RootGoal",
                "statement": f"Stamped \"{stamp}\" (" + " ∧ ".join(
                    f"{proofcheck.obligation.lean_ns(w['name'])}.Claim" for w in rules["workloads"]) + ")",
                "stamp": stamp,
                "obligation_source_hash": obl["source_digest"],
                "lemma_goals": obl["goals"], "lemma_proofs": lemmas,
                "kernel": {"replayed_declarations": verdict["kernel_replayed"],
                           "root_axioms": verdict["root"]["axioms"]}}
        # 9. certificate + preserved artifacts
        cert = {
            "schema": CERT_SCHEMA,
            "competition_id": cid,
            "claim": "B",
            "claim_statement": CLAIM_B,
            "not_claimed": NOT_CLAIMED,
            "reference_commit": rules["reference_commit"],
            "candidate_repo_hash": cand_hash,
            "proof_hash": proof_hash,
            "manifest_hash": canon_hash.json_digest(manifest),
            "spec_hash": comp["hashes"]["spec_hash"],
            "verifier_hash": comp["hashes"]["verifier_hash"],
            "benchmark_hash": comp["hashes"]["benchmark_hash"],
            "rules_hash": comp["hashes"]["rules_hash"],
            "toolchain": comp["toolchain"],
            "root": root,
            "workloads": {k: {kk: vv for kk, vv in v.items() if not kk.startswith("_")}
                          for k, v in cert_workloads.items()},
            "verdict": {"proof_valid": True, "semantics_preserved": True, "eligible": True},
        }
        dest = os.path.join(store_root(comp), "candidates", cand_hash.split(":")[1])
        shutil.rmtree(dest, ignore_errors=True)
        os.makedirs(dest)
        for name, v in cert_workloads.items():
            wd = os.path.join(dest, name)
            os.makedirs(wd)
            for k, p in v["_paths"].items():
                shutil.copy2(p, os.path.join(wd, os.path.basename(p)))
            with open(os.path.join(wd, "candidate.ir.json"), "w") as f:
                json.dump(v["_ir"], f)
        with open(os.path.join(dest, "certificate.json"), "w") as f:
            json.dump(cert, f, indent=1, sort_keys=True)
        report.update({"result": "VALID", "certificate": os.path.join(dest, "certificate.json"),
                       "candidate_repo_hash": cand_hash, "seconds": round(time.time() - t_start, 1)})
        return report
    except Reject as e:
        report.update({"result": "INVALID", "stage": e.stage, "reason": e.msg,
                       "seconds": round(time.time() - t_start, 1)})
        return report
    finally:
        if not os.environ.get("BENDVERIFY_KEEP_WORK"):
            shutil.rmtree(work, ignore_errors=True)
