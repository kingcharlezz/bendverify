# Final report: BendVerify, proof-carrying compiler optimisation for Bend (POC)

Competition `sha256:0df4bd2c614a57d08f01c09f92af39c123ecfe423c858bbe572a7f4ff62477b8` · Bend reference commit `574b6d39a235b539eb19a5c532993a0abb3d11ad` ·
Lean v4.27.0 · Node v24.4.1 · Apple clang 16 · Apple M4 (macOS 26) · 2026-09-26

## 1. What was built

A competition in which miners optimise Bend programs and a submission is **eligible only if an
immutable verifier establishes, with a Lean-kernel-checked proof, that the exact submitted
repository produces a program equivalent to the reference**. Only then is the artifact built from
that exact proven program benchmarked.

```
candidate repo + proof export
  → hostile-archive unpack, recompute every digest (claims only compared)
  → boundary check: only bend2/opt/ may differ from the pinned reference tree
  → re-run the candidate's optimizer in a locked-down container → exact candidate VerifiedIR chain
  → the verifier generates the proof obligation (Lean), stamped with competition id + candidate digest
  → independent checker replays the exported declarations through the Lean kernel,
    requires each proof's type to be exactly the generated goal, composes the root theorem,
    audits axioms
  → FAIL: stop (benchmark BLOCKED)      PASS: lower → re-extract (must round-trip) → compile →
                                              store artifact + certificate → benchmark that artifact
```

**Guarantee: Claim B only.** For every workload, the candidate VerifiedIR produced by the exact
submitted repository is equivalent to the pinned reference VerifiedIR for all well-typed inputs
(same results, including non-termination). **Claim C — that the native executable implements
Bend semantics — is not made.** This is not a "fully verified Bend compiler".

## 2. Demo results (final run, `examples/run-demo`, 5 alternated repetitions, median)

Valid candidate `sha256:fddbeca0…`: **PROOF PASS → benchmarked** (outputs identical to the
reference on the benchmark and all sanity inputs).

| workload | input | threads | reference | candidate | speedup |
|---|---|---|---|---|---|
| tree-radix | `run(22, 0)` | 1 | 5.457 s | 4.721 s | **1.16×** |
| tree-radix | `run(22, 0)` | 8 | 1.059 s | 0.964 s | 1.10× |
| lexer | `run(23, 0)` | 1 | 2.413 s | 0.743 s | **3.25×** |
| lexer | `run(23, 0)` | 8 | 0.513 s | 0.160 s | 3.21× |

Score (geometric mean of the 1-thread speedups): **≈ 1.94×**.

Rejected candidates (never benchmarked by the contest):

| candidate | what it does | verdict | benchmark |
|---|---|---|---|
| `hardcoded-answer` | `run` returns the benchmark answer; reuses the valid proof | **PROOF FAIL** (kernel: the proof mentions `tree_radix.P_2`, which this obligation does not contain) | **BLOCKED** |
| `seed-dropped` | the valid optimizer plus one line replacing the seed by `0`; reuses the valid proof | **PROOF FAIL** (kernel: declaration type mismatch) | **BLOCKED** |
| `malicious-submission` | sandbox escape attempts + a forged `fold` library-rule step | **PROOF FAIL** (library-rule steps `lexer.step_0`, `tree_radix.step_0` do not check) | **BLOCKED** |

For illustration only, *outside* the contest pipeline, the rejected candidates were also built
and timed once at 1 thread: hardcoded-answer 0.18–0.19 s on both workloads (vs 5.73 s / 2.65 s for the
reference), seed-dropped 5.08 s / 0.97 s; on other inputs (`run(10, 123456789)`,
`run(10, 987654)`) hardcoded-answer prints 1998173798 / 2401049475 and seed-dropped
417894213 / 1984695642, where the reference prints 3623821598 / 3574048025. They really are faster (or as fast as the valid candidate)
and correct on the benchmark input, and they print wrong answers on other inputs; the contest
never measured them.

Proof binding (same run):

| scenario | verdict |
|---|---|
| candidate A + proof A | PASS |
| one semantic line of the optimizer changed + proof A | FAIL (proof) |
| one comment byte changed + proof A | FAIL (proof: the stamp names the old candidate digest) |
| the comment-changed candidate, re-proved | PASS |

The valid submission: tree-radix = one library-rule step (`inline`, checked by the kernel
*evaluating* the proven rule checker) + one novel two-level deforestation lemma (~330 lines of
Lean); lexer = one novel fold/build fusion lemma (~520 lines). 185 competitor declarations
are replayed through the kernel; the root theorem `Contest.Certified.root` depends only on
`propext`, `Quot.sound`, `Classical.choice`.

## 3. Definition of done

| requirement | status | evidence |
|---|---|---|
| miner supplies code + proof | done | `competitor-sdk/`, `examples/valid-optimization` (optimizer in `bend2/opt/`, `proof/export.json`) |
| the verifier generates the theorem | done | `trusted/proof-generator/obligation.py`; the statement `BendVerify.Equiv` is in the pinned spec; the miner only names a proof constant per lemma step |
| proof binds the exact candidate | done | `Stamp "bendverify/v1/<cid>/<candidate digest>/…"` is part of every goal; T03d, T06l, demo "comment byte" |
| miner cannot alter spec/verifier/theorem | done | the fork may differ only in `bend2/opt/` (T04); trusted files are pinned and self-checked (T05); proofs must have exactly the goal type (T06c); `Contest.*` is reserved (T06h) |
| unsafe assumptions fail | done | axioms, `sorry`, `native_decide`, unsafe constants, untrusted imports, redeclarations, non-positive inductives, forged recursors: T06d–k, T06n–p |
| code changes break proofs | done | T03d, T03e, demo proof binding |
| invalid optimizations never benchmark | done | demo (hardcoded-answer, seed-dropped, malicious); T09a; the harness refuses without a matching eligible certificate |
| valid ones benchmark the verified artifact | done | the binary is built by the verifier from the proven IR, stored, and re-hashed against the certificate before each run (T09b, T09d) |
| third parties can reproduce PASS | done | §5 |
| Bend audit | done | `docs/BEND_AUDIT.md` |
| immutable trusted boundary + `competition.json` | done | `competition.json` pins every trusted file, toolchains, the reference commit and the rules; `competition_id` = hash of all of them |
| MVP boundary: only pure modelled Bend | done | extractor rejects `@unsafe`, foreign C/JS, IO, templates, open laws, holes, F32, arrays, closures (`tests/integration/test_extractor.py`) |
| Lean semantics + generated theorem `∀ input, eval P = eval Q` | done | `Semantics.lean`, `Equiv.lean` (`↔` over all results, which also covers non-termination) |
| proof-carrying chains `P0 ≡ … ≡ Pn`, pre-proven rules + novel lemmas | done | `Rules.lean` (`applyStep_sound`), chain composition with `Equiv.trans` |
| sandbox | done | Docker for the optimizer, `sandbox-exec` + rlimits for trusted tools and binaries (T08, malicious example) |
| CLI | done | `scripts/{package-submission,verify-submission,benchmark-submission,run-contest}` |

## 4. Adversarial testing

`tests/adversarial/test_attacks.py`: **51 tests, all pass** on the final build (competition
`sha256:0df4bd2c…`, 1,244 s). Every attack is rejected at the intended stage with the intended
reason; the positive control is accepted.

| group | attacks |
|---|---|
| T01 | correct candidate + correct proof is accepted (the positive control) |
| T02 archive | symlink, `../`, absolute path, hard link, device/FIFO, duplicate and case-colliding names, decompression bomb, extra top-level file (own verifier / binary) |
| T03 hashes | wrong competition id, fake candidate digest, proof modified after packaging, candidate changed after proving (one comment byte), one semantic line changed with proof reused, manifest claims another candidate IR |
| T04 boundary | modified compiler dependency, `@unsafe` def added to Base, foreign code added, reference file deleted, symlink in the candidate tree |
| T05 trusted base | modified spec, verifier, rules on the verifier host (refuses to run) |
| T06 proofs | no proof, missing proof constant, weaker theorem (`True`), `sorry`, extra axiom, `native_decide`, redeclared trusted constant, `Contest.*` declaration, unsafe constant, untrusted import, import graph mismatch, proof for another candidate, false library-rule claim, non-positive inductive (would prove `False`), inductive redeclaring an existing type, forged recursor |
| T07 optimizer output | ill-formed IR, symlink in the output, unlowerable IR, reserved function name |
| T08 sandbox | arbitrary commands (network, secrets, trusted files), infinite loop, fork bomb, output bomb |
| T09 benchmark | unverified submission, artifact substituted after the proof, tampered certificate, binary shipped in the submission |

Also: `tests/integration/test_prim_conformance.py` (256 primitive edge cases checked three ways:
Lean spec by kernel `rfl`, Base's pure-Bend definitions in the reference checker, compiled C)
and `tests/integration/test_extractor.py` (12 extractor acceptance/rejection cases).

The malicious example (`examples/malicious-submission`) tries network access, reading SSH keys,
rewriting the verifier and its own repository, reading secrets from the environment and a 500-
process spawn; all fail inside the container (253 spawns hit the pids limit). It then forges a
library-rule `fold` step that "turns `run` into the benchmark answer": the obligation the verifier
generates asks the kernel to evaluate `applyStep`, which does not yield the claimed program, so the
submission is rejected at the proof stage and never benchmarked.

## 5. Third-party reproduction

A fresh `git clone --recurse-submodules` of the repository (no build caches, no `work/`, no `store/`) in a
separate directory, with the Lean components built from source, ran
`./scripts/verify-submission` on the valid archive: **Proof VALID, Eligible YES**, 185 declarations kernel-replayed, and a
`certificate.json` **byte-identical** to the organiser's (sha256 `aa836715006b4afe…`, including the
native binary's digest, since it was the same machine and toolchain). The same copy rejected the
`seed-dropped` archive (Proof INVALID, Eligible NO). Commands:

```bash
git clone --recurse-submodules https://github.com/kingcharlezz/bendverify thirdparty/repo
cd thirdparty/repo
(cd trusted/spec/lean && lake build) && (cd trusted/verifier/checker && lake build)
./scripts/verify-submission ../submission.tar.zst
```

This reproduction ran on the same machine (a clean copy, separate caches, work directory and
artifact store); a second machine with the pinned toolchains was not available. On another
machine every digest in the certificate except the native binary's is expected to match.

The verifier first recomputes the digest of every trusted file and the competition id and refuses
to run on any mismatch, so a third party is checking with exactly the pinned verifier, not with
whatever the organiser ran.

## 6. What remains trusted

For **Claim B** (the certificate's meaning):

1. **The Lean 4 kernel** (v4.27.0, GMP-accelerated `Nat` and string literals).
2. **The statement**: `BendVerify.Syntax`, `BendVerify.Semantics` and `BendVerify.Equiv` (~390
   lines). That it is the *right* statement — that `ev` models Bend's pure fragment and `Prim.eval`
   matches Base — is a modelling assumption, spot-checked by the 256-case three-way conformance
   test, not proven.
3. **The obligation generator** (~200 lines of Python): renders the verifier's own IR as Lean
   terms and states the root goal. Input is schema-validated first; no competitor text reaches
   Lean as syntax.
4. **The replay checker** (~410 lines of Lean): the export decoder, in-order kernel submission,
   the exact-goal-type check, root composition and the axiom audit.
5. **The orchestration, hasher, schemas and archive reader** (~1,700 lines of Python): recomputing digests,
   the boundary check, re-running the optimizer and comparing its output with the claims.
6. **The sandbox** (Docker in colima; macOS `sandbox-exec`) for *host* integrity; Claim B does not
   depend on it, since every result that leaves the sandbox is re-validated.

The lemma files (Lemmas, Simulate, Lift, Rules, Support) are *proofs*, re-checked by the kernel;
competitors' proofs are re-checked by the kernel. Neither is trusted.

## 7. The gap between Claim B and an executable guarantee (Claim C)

Claim B is about VerifiedIR programs. Between the proven program and the timed binary, these links
are **trusted and unverified**:

| link | mitigation today |
|---|---|
| Bend source → VerifiedIR (`extract.mjs`, for the reference workloads) | pinned reference checker runs first; `Def.e` (compiled) and `Def.v` (checked) must translate to the same IR; everything outside the fragment is rejected |
| meaning of Base primitives vs `comp.ts` templates | three-way differential conformance test |
| VerifiedIR → Bend (`lower.py`) | **validated per artifact**: the lowered file is re-extracted and must equal the proven IR |
| the reference `bend.ts` checker, `comp.ts` (~6,300 lines, no internal IR) and its C runtime | none beyond pinning; `BEND_AUDIT.md` lists the known `bend.ts`/`bend.lean` mismatches |
| clang `-O3`, libc, macOS, the CPU | none |
| `Nat` ≥ 2^48 at run time | the runtime fail-stops where the IR semantics continues; equivalence says nothing there |
| timing | measured, not proven |

The benchmark compares reference and candidate outputs on pinned sanity inputs and refuses to score
on any difference; because the IR programs are proven equivalent, a difference would expose a bug
in this unverified chain, not in the candidate. `ROADMAP.md` orders the work to close each link
(verified extraction, a certificate-emitting `comp.ts`, a verified C path).

## 8. Limitations of the POC

* **Small fragment**: first-order, pure, no F32, no arrays, no closures, only Base `Bool`/`Char`/
  `String` and one pair instance. Two benchmark workloads (`tree-radix`, `lexer`) fit.
* **Only `bend2/opt/` may change.** Competitors optimise *programs* through a formal IR, using the
  pinned reference front end and compiler; changing `bend.ts`/`comp.ts` themselves needs the
  certificate-producing compiler interface in `ROADMAP.md`.
* **Proof effort is high for novel transformations** (hundreds of lines per fusion). Library rules
  are cheap; generic proven deforestation would turn the demo lemmas into rule steps.
* **macOS-specific isolation** (`sandbox-exec` is deprecated; Docker runs in a colima VM). A
  production verifier should use Linux with gVisor/Firecracker and a dedicated benchmark host.
* **Benchmark noise**: medians of 5 alternated runs on a laptop, no pinned cores or frequency;
  tree-radix's gain (~1.1×; 1.12–1.17× at 1 thread across the demo runs made during development) is modest
  and its variance has not been characterised.
* The competition id changes whenever any trusted file changes, and every proof must then be
  regenerated (the stamp includes it). That is intended.
