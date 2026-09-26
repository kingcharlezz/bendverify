# BendVerify: proof-carrying compiler optimisation for Bend (proof of concept)

Competitors optimise Bend programs. A submission counts **only if an independent, immutable
verifier establishes — with a Lean-kernel-checked proof — that the exact submitted code produces
a program semantically equivalent to the reference**, and only then is *that exact artifact*
benchmarked.

```
candidate repo + proof
        │
        ▼
hash candidate (recomputed; claims only compared)
        │
        ▼
re-run the candidate's optimizer in a sandbox  ─►  exact candidate VerifiedIR
        │
        ▼
generate the fixed proof obligation (the verifier writes the theorem, never the miner)
        │
        ▼
independent proof checker (Lean kernel replay; stamp binds proof to this exact candidate)
        │
    ┌───┴────┐
  FAIL      PASS ──► build exactly that IR ──► preserve artifact ──► benchmark that artifact
    │
 BLOCKED (never benchmarked)
```

**Guarantee provided: Claim B** — the exact candidate VerifiedIR is formally equivalent to the
reference VerifiedIR for all well-typed inputs. **Not Claim C** — the native executable is *not*
proven to implement Bend semantics; the Bend front end, `comp.ts`, clang and the hardware remain
trusted (see `docs/TRUST_MODEL.md`). This is not a "fully verified Bend compiler".

## Demo results (Apple M4, Bend `574b6d39`, workloads `bench/runtime/tree-radix` and `bench/runtime/lexer`)

`./examples/run-demo`, competition `sha256:0df4bd2c…`, median of 5 alternated runs:

| submission | proof | benchmark | outcome |
|---|---|---|---|
| **valid**: tree-radix = library-rule `inline` + a novel two-level deforestation (Lean, ~330 lines); lexer = a novel fold/build fusion (Lean, ~520 lines) | **PASS** (185 declarations kernel-replayed; axioms `propext`, `Quot.sound`, `Classical.choice`) | tree-radix 5.46 s → 4.72 s (**1.16×**, 1 thread; 1.10× at 8); lexer 2.41 s → 0.74 s (**3.25×**, 1 thread; 3.21× at 8); score ≈ 1.94× | **eligible** |
| **invalid, faster**: returns the benchmark's answer, reusing the valid proof | **FAIL** (kernel) | **BLOCKED** | ineligible |
| **invalid, faster**: the valid optimizer + ignores the seed (correct only for `x = 0`, i.e. on the benchmark input) | **FAIL** (kernel) | **BLOCKED** | ineligible |
| **malicious**: sandbox escape attempts + a forged library-rule step | **FAIL** (rule steps do not check) | **BLOCKED** | ineligible |
| valid candidate with one semantic line changed, proof A reused | **FAIL** | **BLOCKED** | ineligible |
| valid candidate with one comment byte changed, proof A reused | **FAIL** (stamp mismatch) | **BLOCKED** | ineligible |

A clean third-party copy reproduces the PASS with a byte-identical certificate. Full results,
the trusted computing base and the Claim B / Claim C gap are in `docs/REPORT.md`.

## Repository layout

```
competition.json            the frozen competition: pinned hashes of every trusted file, toolchains,
                            rules, workloads; competition_id = H(spec || verifier || benchmark || rules)
trusted/                    IMMUTABLE for one competition version
  spec/lean/BendVerify/     VerifiedIR syntax, semantics, THE theorem (Equiv), proven rule library
  spec/workloads/           reference Bend workloads + pinned reference IR
  verifier/bendverify/      orchestration: archive, hashing, boundary, sandbox, build, proof check
  verifier/bend/            trusted Bend front end (extract.mjs), lowering, compile driver, round trip
  verifier/checker/         the independent Lean kernel-replay proof checker
  proof-generator/          IR -> Lean proof obligation
  schema/  hasher/          VerifiedIR / manifest / chain schemas; canonical hashing
  benchmark/                benchmark harness (only runs verified, re-hashed artifacts)
reference/bend              pinned bendlang/bend checkout (verified file-by-file)
competitor-sdk/             untrusted helpers: declaration exporter, prove-candidate workflow, docs
examples/                   valid-optimization, invalid-optimization/*, malicious-submission
tests/adversarial/          the attack suite (every exploit becomes a regression test)
tests/integration/          primitive conformance (Lean spec vs Bend checker vs compiled C), extractor
scripts/                    make-competition, package-submission, verify-submission,
                            benchmark-submission, run-contest
docs/                       BEND_AUDIT, TRUST_MODEL, SEMANTICS, THREAT_MODEL, ROADMAP, REPORT
```

## Requirements

macOS (Apple Silicon) with: Lean **v4.27.0** (elan toolchain; set `ELAN_HOME` or
`BENDVERIFY_LEAN_TOOLCHAIN`), Node **v24.4.1**, Apple clang 16, `zstd`, Docker (colima) with image
`node:24-bookworm-slim` pinned by id. The workspace must live under `$HOME` (colima shares only
`$HOME`). The verifier checks every tool identity against `competition.json`.

Build the Lean components once:

```bash
(cd trusted/spec/lean && lake build) && (cd trusted/verifier/checker && lake build) && (cd competitor-sdk/exporter && lake build)
```

## Command line

```bash
./scripts/package-submission ./candidate -o submission.tar.zst   # canonical package (claims only)
./scripts/verify-submission submission.tar.zst                   # independent verification
./scripts/benchmark-submission submission.tar.zst                # refuses unless certificate matches
./scripts/run-contest submission.tar.zst                         # verify, then benchmark on PASS only
./examples/run-demo                                              # the full end-to-end demonstration
```

`verify-submission` prints

```
Competition: sha256:…
Candidate:   sha256:…
Guarantee:   Claim B (VerifiedIR equivalence) - NOT Claim C (native executable)
Proof:       VALID            (or INVALID + the stage and reason)
Eligible:    YES              (or NO)
```

and stores `certificate.json` plus the exact verified artifacts under `store/`.

## Competing

Read `competitor-sdk/README.md`. In short: put an optimizer at `bend2/opt/optimize.mjs` in your
Bend fork (it reads the reference VerifiedIR and emits a chain of programs with one certificate
step per rewrite), write Lean proofs for any non-library steps against the generated obligation,
run `competitor-sdk/tools/prove-candidate`, then `scripts/package-submission`.

## Reproduce a verdict (third party)

1. Clone this repository at the competition's commit **with its submodule**:
   `git clone --recurse-submodules https://github.com/kingcharlezz/bendverify`. `reference/bend` is a submodule pinned to Bend
   commit `574b6d39…`; the verifier also checks it file by file.
2. Install the pinned toolchains; build the Lean components as above.
3. `./scripts/verify-submission submission.tar.zst` — it first recomputes the digest of every
   trusted file and the competition id and refuses to run on any mismatch, then recomputes
   everything else from the archive. Compare the printed verdict and `certificate.json`
   (identical except the machine-specific binary digest).

No output of the organiser's servers is trusted in this process.

## Tests

```bash
python3 -m unittest discover -s tests/adversarial -p "test_*.py" -v   # 51 attacks, ~20 min
python3 -m unittest discover -s tests/integration -p "test_*.py" -v
```
