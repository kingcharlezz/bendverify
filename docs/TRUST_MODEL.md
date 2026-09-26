# Trust model

## The rule

```
TRUST:        a small, immutable specification + an independent verifier
DO NOT TRUST: the miner, the miner's code, optimizer, proof generator, theorem statement,
              build scripts, tests, verifier, and every digest the miner claims
```

A competitor may write any optimizer (AI, search, superoptimizer, hand-written, malicious) and
any proof. A submission is eligible **only** if the immutable verifier establishes the required
theorem about the exact artifact that will be benchmarked.

## Three different claims (and which one this competition makes)

| | claim | status in competition v1 |
|---|---|---|
| **A** | "The proof type-checks." | Necessary, meaningless on its own: a proof of `True` type-checks. Never used as a verdict. |
| **B** | "The exact candidate VerifiedIR is formally equivalent to the specified reference VerifiedIR." | **This is what v1 certifies.** For every workload `w`: for all well-typed entry arguments and every value `v`, the reference program terminates with `v` **iff** the candidate program does (`BendVerify.Equiv`), proved in Lean and re-checked by the kernel, for the IR produced by the exact submitted repository. |
| **C** | "The final native executable, running on real hardware, implements the original Bend semantics." | **NOT claimed.** It would need proofs (or per-artifact translation validation) for the extractor, the lowering, the Bend compiler `comp.ts`, its C runtime, clang, the OS and the CPU. The benchmark's output check is a sanity test, not a proof. |

Every certificate carries both the claim and the explicit non-claim (`claim_statement`,
`not_claimed`), and every CLI prints "Claim B … NOT Claim C". This project never uses the phrase
"fully verified Bend compiler".

## The trust boundary on disk

```
trusted/                     immutable for one competition version (every file pinned in
├── spec/                    competition.json; the verifier refuses to run if any differs)
│   ├── lean/BendVerify/     the formal VerifiedIR: Syntax, Semantics, Equiv (THE statement),
│   │                        plus kernel-checked lemmas: Lemmas, Simulate, Lift, Rules, Support
│   ├── workloads/<w>/       reference Bend source and its extracted reference IR (digest-pinned)
│   ├── reference_tree.json  every file of the reference Bend commit (path, exec bit, sha256)
│   └── base_names.json      Base's names (lowering collision check)
├── verifier/                orchestration (bendverify/), Bend front end + lowering (bend/),
│   └── checker/             the independent Lean kernel-replay checker
├── proof-generator/         obligation generator (IR -> the Lean proposition)
├── schema/                  VerifiedIR, manifest and chain schemas
├── hasher/                  canonical hashing (tree and JSON digests)
└── benchmark/               the benchmark harness
competition.json             pins all of the above + toolchains + rules; defines competition_id
reference/bend               the pinned Bend commit (checked file-by-file against reference_tree.json)
```

A competitor's Bend fork lives **only** inside `submission/bend/`. Nothing from it is ever
imported, compiled into the trusted pipeline, or executed outside the sandbox; the only thing
executed is `bend2/opt/optimize.mjs`, inside a locked-down container (`THREAT_MODEL.md`).

## What is trusted, exactly (the TCB of Claim B)

1. **The Lean 4 kernel**, pinned to v4.27.0 (commit `db93fe16…`), including its GMP-accelerated
   `Nat` and string literals. Declarations are sent to it by `Lean.Environment.replay`.
2. **The statement**: `BendVerify.Syntax`, `BendVerify.Semantics` (`ev`, `Prim.eval`, `Eval`,
   `Run`) and `BendVerify.Equiv` (`HasTy`, `Ctx`, `WfEntry`, `Equiv`, `Stamp`, `Stamped`), ~390
   lines including the decidable `wfEntryB` and its soundness proof. The lemma files (Lemmas, Simulate, Lift, Rules, Support) are proofs, re-checked by the
   kernel; they are trusted only in the sense that they are part of the pinned environment.
3. **The obligation generator** (`trusted/proof-generator/obligation.py`, ~200 lines): that it
   renders the verifier's own copies of P and Q faithfully as Lean terms, and states
   `RootGoal := Stamped "<cid>/<candidate>" (w.Claim ∧ …)` with `w.Claim := Equiv ctx P_0 P_n`.
   The IR is schema-validated first, so no competitor text reaches Lean as syntax.
4. **The replay checker** (`trusted/verifier/checker`, ~410 lines of Lean): the JSON decoder
   (a declaration can only be a theorem, a safe definition, or an inductive block given by its type
   and constructor signatures — the kernel checks it and generates constructors and recursors
   itself; axioms, opaques, quotients, unsafe and partial definitions are unrepresentable), the
   in-order submission of every declaration to the kernel, the checks that no trusted constant is
   redeclared and that each lemma proof's type is *syntactically* the generated goal, the root
   composition, and the axiom audit (allowlist: `propext`, `Quot.sound`, `Classical.choice`).
5. **The orchestration** (`trusted/verifier/bendverify`): recomputing every digest, the boundary
   check, the chain handling, and structural validation of the checker's verdict.
6. **The hasher and the archive reader** (canonical encodings; hostile-input extraction).

With these, Claim B is: *the IR programs the verifier holds are equivalent*, and *the candidate IR
is exactly the output of the exact submitted repository* (the verifier re-runs the optimizer and
compares digests; the proof term itself embeds the candidate digest via `Stamp`).

## What additionally stands between Claim B and the running binary (the Claim-C gap)

| link | status |
|---|---|
| Bend source ⇒ VerifiedIR (`extract.mjs`) | trusted, unverified. Mitigations: runs the pinned reference checker first; translates both `Def.e` (compiled) and `Def.v` (checked) and requires agreement; rejects everything outside the fragment. |
| Meaning of Base primitives (`Prim.eval` vs Base's pure-Bend definitions vs `comp.ts` templates) | trusted, spot-checked by differential tests. |
| VerifiedIR ⇒ Bend (`lower.py`) | **validated per artifact**: the lowered file is re-extracted and must give back the proven IR exactly (translation validation), so a printing bug cannot silently change meaning. |
| reference Bend checker (`bend.ts`) accepting the lowered program | trusted (and itself not verified; see the `bend.lean` mismatches in `BEND_AUDIT.md`). |
| `comp.ts` (Bend ⇒ C) and its C runtime | trusted, unverified, "99% AI-written" per its README; ~6,300 lines with no internal IR. |
| clang `-O3`, libc, macOS, Apple M-series hardware | trusted. |
| Nat values ≥ 2^48 at run time | a compiled program fail-stops where the IR semantics continues. Equivalence of IR programs says nothing here. |
| Timing | measured, not proven. The sandbox and the harness bound interference but cannot prove it absent. |

The benchmark harness runs the reference and candidate binaries on pinned sanity inputs and
refuses to score if their outputs differ. Because the IR programs are proven equivalent, any
such difference would expose a bug in this unverified chain, not in the candidate.

## Why the proof binds to the exact candidate

* The verifier computes `candidate_repo_hash` from `submission/bend/` itself (bendverify-tree-v1).
* It re-runs the candidate's optimizer on the pinned reference IR, in the sandbox, and requires
  the produced candidate IR to be byte-for-byte the one the manifest claims.
* It generates the proposition with `Stamp "bendverify/v1/<competition_id>/<candidate_repo_hash>…"`.
  `Stamp s` is an inductive predicate whose only constructor is `Stamp.mk s`, so **a proof term
  must contain the literal digest**. A proof produced for candidate A is rejected by the kernel
  for candidate B, even if B differs from A in a single comment byte and even if B's IR is
  identical. The same holds across competition versions.
* The benchmark uses the binary built from exactly that IR, preserved in the store and re-hashed
  against the certificate before every run.

## Reproducing a verdict without trusting the organiser

A third party needs this repository at the competition's commit (whose trusted files must hash
to `competition.json`), the pinned toolchains (Lean v4.27.0, Node v24.4.1, the pinned clang, the
pinned Docker image) and the submission archive. See `README.md` ("Reproduce a verdict").
The verdict and every digest in `certificate.json` are recomputed from scratch; only the native
binary's digest is machine-specific.
