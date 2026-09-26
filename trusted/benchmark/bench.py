"""Benchmark harness (competition v1). TRUSTED.

Benchmarks ONLY the artifact that was verified:

  1. recompute the candidate digest, proof digest and manifest digest from the
     submitted package;
  2. load the certificate that verification stored under that candidate digest;
     REFUSE unless every digest in it matches the package, the competition id
     and every trusted-base digest match the running verifier, and the verdict
     is eligible;
  3. re-hash the PRESERVED binary (built by the verifier from the proven IR,
     never supplied by the competitor, never rebuilt) and REFUSE unless it is
     byte-identical to the certificate's artifact digest;
  4. run the reference and candidate binaries alternately under the sandbox on
     the pinned inputs; any output difference is reported as a trusted-base
     failure (the proof says the IR programs are equivalent);
  5. report medians and the speedup. There is no correctness score:
     correctness is the binary verdict of step 2.
"""

from __future__ import annotations

import json
import os
import shutil
import statistics
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "verifier"))

from bendverify import archive, sandbox, verify as V  # noqa: E402
from bendverify.competition import ROOT, canon_hash, load as load_competition  # noqa: E402

import submission as schema  # noqa: E402


class Refuse(Exception):
    pass


def _run(binary: str, args: list[str], threads: int) -> tuple[str, float]:
    t0 = time.perf_counter()
    r = sandbox.run_confined([binary, "--threads", str(threads), "--gpu", "off", *args],
                             read_paths=[os.path.dirname(binary)], write_paths=[],
                             cpu_seconds=3600, wall_seconds=3600, fsize_mb=1)
    dt = time.perf_counter() - t0
    if r.returncode != 0:
        raise Refuse(f"{os.path.basename(os.path.dirname(binary))} exited {r.returncode}: "
                     f"{r.stderr.decode(errors='replace')[-300:]}")
    return r.stdout.decode(errors="replace").strip(), dt


def load_certificate(comp: dict, archive_path: str, tc: dict) -> tuple[dict, str]:
    work = os.path.join(V.work_root(), "b-" + os.urandom(6).hex())
    try:
        sub = archive.unpack(archive_path, work, zstd=tc["zstd"])
        with open(os.path.join(sub, "manifest.json"), "rb") as f:
            manifest = schema.validate_manifest(json.loads(f.read().decode("utf-8")))
        cand_hash, _ = canon_hash.tree_digest(os.path.join(sub, "bend"))
        proof_hash, _ = canon_hash.tree_digest(os.path.join(sub, "proof"))
    except Exception as e:  # noqa: BLE001
        raise Refuse(f"cannot read the submission: {e}")
    finally:
        shutil.rmtree(work, ignore_errors=True)
    d = os.path.join(V.store_root(comp), "candidates", cand_hash.split(":")[1])
    cpath = os.path.join(d, "certificate.json")
    if not os.path.isfile(cpath):
        raise Refuse("no certificate for this exact candidate: it has not passed verification")
    with open(cpath) as f:
        cert = json.load(f)
    checks = {
        "schema": cert.get("schema") == V.CERT_SCHEMA,
        "competition": cert.get("competition_id") == comp["competition_id"],
        "candidate": cert.get("candidate_repo_hash") == cand_hash,
        "proof": cert.get("proof_hash") == proof_hash,
        "manifest": cert.get("manifest_hash") == canon_hash.json_digest(manifest),
        "spec": cert.get("spec_hash") == comp["hashes"]["spec_hash"],
        "verifier": cert.get("verifier_hash") == comp["hashes"]["verifier_hash"],
        "benchmark": cert.get("benchmark_hash") == comp["hashes"]["benchmark_hash"],
        "eligible": cert.get("verdict", {}).get("eligible") is True,
    }
    bad = [k for k, ok in checks.items() if not ok]
    if bad:
        raise Refuse(f"certificate does not match this submission / verifier: {', '.join(bad)}")
    for name, w in cert["workloads"].items():
        for kind, fname in (("binary", "program.bin"), ("c", "program.c"), ("bend", "program.bend")):
            p = os.path.join(d, name, fname)
            if not os.path.isfile(p) or canon_hash.file_digest(p) != w["artifacts"][kind]:
                raise Refuse(f"{name}: preserved {kind} artifact differs from the verified one")
    return cert, d


def benchmark(archive_path: str, reps: int = 5, log=print) -> dict:
    comp = load_competition(self_check=True)
    tc = V.toolchain(comp)
    V.check_reference_tree(comp)
    cert, d = load_certificate(comp, archive_path, tc)
    log(f"  [certificate] matches candidate {cert['candidate_repo_hash']}")
    base_names = set(json.load(open(os.path.join(ROOT, "trusted", "spec", "base_names.json"))))
    refs = V.build_reference(comp, tc, base_names)
    bench = comp["rules"]["benchmark"]
    out = {"candidate_repo_hash": cert["candidate_repo_hash"], "competition_id": comp["competition_id"],
           "workloads": {}}
    for w in comp["rules"]["workloads"]:
        name = w["name"]
        ref_bin = refs[name]["paths"]["binary"]
        cand_bin = os.path.join(d, name, "program.bin")
        # sanity: identical outputs on the pinned inputs (both are proven-equivalent IR)
        for args, expect in w["sanity"]:
            ro, _ = _run(ref_bin, args, 1)
            co, _ = _run(cand_bin, args, 1)
            if (expect is not None and ro != expect) or co != ro:
                raise Refuse(f"{name}{args}: reference printed {ro!r}, candidate {co!r}, "
                             f"expected {expect!r}. The IR programs are proven equivalent, so this is a "
                             "failure of the trusted lowering/compiler/runtime (Claim-C gap).")
        log(f"  [sanity] {name}: outputs identical on {len(w['sanity'])} pinned inputs")
        res = {}
        for cfg in bench["configs"]:
            for args in w["benchmark_inputs"]:
                rt, ct = [], []
                for _ in range(reps):
                    ro, t = _run(ref_bin, args, cfg["threads"])
                    rt.append(t)
                    co, t = _run(cand_bin, args, cfg["threads"])
                    ct.append(t)
                    if co != ro:
                        raise Refuse(f"{name}{args}: output mismatch during benchmark")
                key = f"threads={cfg['threads']} args={' '.join(args)}"
                res[key] = {"reference_s": round(statistics.median(rt), 4),
                            "candidate_s": round(statistics.median(ct), 4),
                            "speedup": round(statistics.median(rt) / statistics.median(ct), 3),
                            "output": ro, "reps": reps}
                log(f"  [bench] {name} {key}: reference {res[key]['reference_s']}s, "
                    f"candidate {res[key]['candidate_s']}s, speedup {res[key]['speedup']}x")
        out["workloads"][name] = res
    scored = [r["speedup"] for w in out["workloads"].values() for k, r in w.items()
              if k.startswith(f"threads={bench['score_threads']} ")]
    out["score_speedup"] = round(statistics.geometric_mean(scored), 3)
    return out
