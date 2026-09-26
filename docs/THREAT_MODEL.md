# Threat model

## Adversary

The miner controls **everything in the submission archive**: the Bend repository (including any
"optimizer", build script, test, or verifier it contains), the proof export, the manifest and
every digest in it, and the file-system structure of the archive itself. The miner knows the
verifier's source code, the benchmark inputs and the reference outputs. The miner wants either
(a) a *valid* verdict for a candidate that is not semantically equivalent to the reference, or
(b) a *better score* than the verified candidate deserves, or (c) to compromise the verifier
host.

Out of scope: an attacker who can modify the verifier host (its trusted files, toolchains or
artifact store) — though tampering with trusted files is *detected* (the verifier refuses to
run), and tampering with stored artifacts is detected by the benchmark harness.

## Attack surface and defences

| # | attack | defence | test |
|---|---|---|---|
| 1 | archive tricks: symlinks, hard links, devices, FIFOs, `../`, absolute paths, duplicate or case-colliding names, non-NFC names, extra top-level entries (e.g. a bundled "verifier" or binary), decompression bombs | `archive.unpack`: strict name rules, only regular files/dirs, `O_EXCL|O_NOFOLLOW` creation inside a fresh directory, size/count caps, exactly `bend/`, `proof/`, `manifest.json` | T02 |
| 2 | fake digests in the manifest | every digest is recomputed and only compared | T03 |
| 3 | proof for another candidate / older commit / older competition | the proposition embeds `Stamp "<competition_id>/<candidate digest>"`; the kernel rejects a proof term built for any other string | T03d, T06l |
| 4 | change one semantic line and reuse proof A | the re-run optimizer produces a different IR, so the obligation differs (and the stamp differs) | T03e |
| 5 | candidate changed after the proof (even one comment byte) | the candidate digest changes, so the stamp differs | T03d |
| 6 | modify the Bend front end / compiler / Base in the fork, add foreign code or `@unsafe` defs | competition v1 allows changes only under `bend2/opt/`; every other file must equal the pinned reference commit; the trusted pipeline never uses the fork's copies anyway | T04 |
| 7 | modify the verifier / spec / rules on the verifier host | every trusted file is pinned in `competition.json`; the competition id is recomputed; the verifier refuses to run on any difference | T05 |
| 8 | proof of a weaker theorem | the checker requires each lemma proof's type to be *syntactically* the generated goal constant | T06c |
| 9 | open holes (`sorry`), extra axioms, `native_decide` (`Lean.ofReduceBool`), `Lean.trustCompiler` | the export format cannot express axioms; Python inspection rejects forbidden constants; the kernel-side axiom audit of the root allows only `propext`, `Quot.sound`, `Classical.choice` | T06d, T06e, T06f |
| 10 | redeclare / shadow a trusted constant; declare into `Contest.*` | redeclaration is refused (the kernel environment already contains it); `Contest` is reserved | T06g, T06h |
| 11 | unsafe / partial / opaque declarations, forged recursors, unsafe constants in the proof graph | unrepresentable in the export format (inductive blocks carry only type and constructor signatures; the kernel checks positivity and generates constructors/recursors itself); the kernel rejects safe declarations using unsafe constants; the axiom walk rejects unsafe leaves | T06i |
| 12 | proof importing untrusted modules; import graph differing from the declaration | the declared imports must lie inside the trusted import set and equal the export's; the replay environment is built **only** from trusted modules, so any other constant must be in the export and is kernel-checked | T06j, T06k |
| 13 | missing law (lemma step without proof, proof constant absent) | the checker requires one exported theorem per generated goal | T06a, T06b |
| 14 | false claim about a library rule | the kernel evaluates the rule checker inside the verifier-generated obligation | T06m |
| 15 | malicious Lean elaboration (metaprograms, `#eval`, environment hacking, `debug.skipKernelTC`) | **the verifier never elaborates competitor Lean.** It decodes a flat declaration list with a strict, loop-free decoder and hands each declaration to the kernel | by design |
| 16 | hostile IR (out-of-scope variables, bad arities, huge or deep terms, injection into the generated Lean) | strict schema validation before anything else; the generator renders only validated identifiers and integers | T07a |
| 17 | IR that is equivalent but compiles differently from what was proven (lowering bug) | the lowered Bend is re-extracted and must give back the proven IR exactly | build stage, round-trip |
| 18 | reserved names (`main`, `harness.*`), Base collisions, unlowerable IR | the lowering rejects them; the reference checker must accept the lowered program | T07c, T07d |
| 19 | prove artifact A, benchmark artifact B (swap the binary, ship a binary, rebuild differently) | the benchmarked binary is built by the verifier from the proven IR, preserved in the store, and re-hashed against the certificate before every run; submission-supplied binaries are never used | T09 |
| 20 | benchmark an unverified or tampered candidate | the harness recomputes candidate/proof/manifest digests from the package and requires a matching eligible certificate for the current competition | T09a, T09c |
| 21 | precompute the answer / special-case the benchmark input | workloads take their size and seed at run time; the obligation quantifies over **all** well-typed inputs | examples/invalid-optimization |
| 22 | arbitrary command execution by the optimizer: network, exfiltration, writing trusted files, fork bombs, infinite loops, disk/output bombs | Docker (colima VM): `--network none`, `--read-only`, `--cap-drop ALL`, `no-new-privileges`, uid 65534, pids/memory/CPU limits, wall-clock `timeout -s KILL`, tmpfs-only writable space with size caps, only the candidate repo and the reference IR mounted, read-only; the trusted base is not mounted; results leave as a size-capped tar stream and are re-validated | T08 |
| 23 | nondeterministic or misreported optimizer output | the verifier's own sandbox run is authoritative; it must match the manifest's claimed candidate IR digest | T03f |
| 24 | attacks on trusted tools that parse derived data (Node + Bend front end, the Lean checker, clang, the benchmarked binaries) | they run under macOS `sandbox-exec`: no network, writes confined to a scratch directory, no reads of the user's home except the needed paths, CPU/file-size rlimits | sandbox probes |
| 25 | Bend hub imports fetching code during `book_load` | lowered programs may only `import Base` (checked textually before loading); Node runs without network | compile.mjs |

## Residual risks (known, accepted for the POC)

* **Kernel or checker bugs.** A Lean kernel soundness bug, or a bug in the ~410-line decoder and
  checker, could admit a false proof. Mitigation: small, auditable checker; the root is
  re-checked through the kernel; independent Python inspection of the export; defence in depth
  (stamp, digests).
* **The Claim-C chain** (extractor, `bend.ts`, `comp.ts`, C runtime, clang, hardware) is trusted
  but unverified (`TRUST_MODEL.md`). The sanity-output comparison in the benchmark can only detect
  some failures.
* **Timing side channels / noisy neighbours**: timings are medians of interleaved runs on a shared
  machine; the benchmark is not adversarially robust against, e.g., a workload tuned to the
  machine's frequency scaling. Correctness does not depend on timing.
* **Sandbox escapes** via kernel/VM vulnerabilities (Docker in colima; `sandbox-exec`) are out of
  scope for a POC; production should add gVisor/Firecracker and dedicated hosts.
* **Resource exhaustion of the verifier** by expensive-but-valid proofs (huge exports, costly
  kernel reductions) is bounded by wall-clock/CPU limits, which reject the submission.
