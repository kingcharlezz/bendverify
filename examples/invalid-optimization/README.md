# Invalid (but faster) optimizations

Both candidates are *wrong* programs that print the right answer on the benchmark inputs, and both
reuse the valid submission's proof export (`proof/export.json` from `examples/valid-optimization`).

| example | what it does | benchmark input | any other input |
|---|---|---|---|
| `hardcoded-answer` | replaces each entry by the benchmark answer (`run(n, x) = 1998173798`, `run(d, i) = 2401049475`) | correct, 14–31× faster than the reference (≈0.19 s vs 2.6–5.7 s) | wrong |
| `seed-dropped` | the valid optimizer plus one extra line that replaces the seed argument by `0` ("the seed is always 0 in the benchmark") | correct, as fast as the valid candidate | wrong whenever the seed ≠ 0 |

Expected outcome (`examples/run-demo`):

* `hardcoded-answer`: **PROOF FAIL** — the proof export refers to intermediate programs of the
  valid chain that this candidate's obligation does not contain, and its lemma's type is not the
  new goal (`Equiv ctx P_0 P_1` with `P_1` = "return the constant" is false, so no proof exists);
* `seed-dropped`: **PROOF FAIL** — the reused lemma proves equivalence with the valid candidate's
  program, not with this one (and the stamp names a different candidate digest);
* both: **BENCHMARK BLOCKED** — the benchmark harness refuses any candidate without a matching
  eligible certificate.

```bash
./examples/materialize examples/valid-optimization work/valid && ./competitor-sdk/tools/prove-candidate work/valid
./examples/materialize examples/invalid-optimization/seed-dropped work/bad
cp -R work/valid/proof work/bad/proof
./competitor-sdk/tools/prove-candidate work/bad --no-prove
./scripts/package-submission work/bad -o work/bad.tar.zst
./scripts/run-contest work/bad.tar.zst
```
