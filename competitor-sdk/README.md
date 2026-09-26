# Competitor SDK (competition v1)

Everything in this directory is **untrusted convenience tooling**. The verifier recomputes and
re-checks everything it produces.

## What you submit

```
submission/
├── bend/            your Bend fork: the pinned reference tree + your files under bend2/opt/
├── proof/           export.json (kernel declarations of your Lean proofs) + anything informative
└── manifest.json    written by scripts/package-submission (digests are claims)
```

In v1 **only `bend2/opt/` may differ** from the reference commit `574b6d39…`. Every other file must
be byte-identical (the verifier uses its own pinned copies of `bend.ts`, `comp.ts` and `base.bend`
anyway).

## The optimizer interface (fixed)

```
node bend2/opt/optimize.mjs <in_dir> <out_dir>
```

* `in_dir/request.json`: `{"competition_id": …, "workloads": [{"name", "entry", "input"}]}`
* `in_dir/<workload>.ir.json`: the reference program `P_0` (VerifiedIR, `schema/verifiedir-v1.schema.json`)
* write `out_dir/<workload>/chain.json` (`schema/chain-v1.schema.json`) and every intermediate
  program it names. An empty `steps` list means "no change".

It runs in Docker (`node:24-bookworm-slim`, pinned by image id) with **no network, read-only root,
uid 65534, 2 CPUs, 2 GiB, 256 processes, 300 s**, your repo mounted read-only at `/cand`, and 64 MiB
of writable `/out` and `/tmp`. It must be **deterministic**: the verifier re-runs it and requires the
exact IR your manifest claims.

## Certificate steps

For each rewrite `P_k → P_{k+1}` emit one step:

* **library rule** — `{"kind": "rule", "fn": f, "path": [...], "rule": {"name": "inline"|"caseCtr"|"natLit"}|{"name": "fold", "bool_adt": b}, "program": "…"}`.
  No proof needed: the kernel evaluates the proven rule checker (`BendVerify.Rules.applyStep`) at the
  location you name and must obtain exactly your `P_{k+1}`. Paths index children: arguments of
  prim/ctr/call; 0/1 for let; 0/1/2 for par; 0 = scrutinee, `j+1` = body of arm `j` for mat; 0/1/2
  for natCase.
* **lemma** — `{"kind": "lemma", "proof": "<Lean constant>", "program": "…"}`. You must supply, in
  `proof/export.json`, a theorem named `<Lean constant>` whose type is **exactly**
  `Contest.Obligation.<workload>.goal_k`, i.e.

  ```lean
  Stamped "bendverify/v1/<competition_id>/<candidate_repo_hash>/<workload>/step/k" (Equiv ctx P_k P_{k+1})
  ```

  The stamp contains your candidate digest, so the proof must be regenerated whenever any byte of
  `bend/` changes. Write `⟨Stamp.mk _, …⟩`; elaboration fills in the literal.

## Proving

```bash
examples/materialize examples/valid-optimization work/my-cand     # or build your own candidate dir
competitor-sdk/tools/prove-candidate work/my-cand                        # runs your optimizer (same container),
                                                                    # generates the obligation, compiles
                                                                    # proof-src/, exports, writes submission.json
scripts/package-submission work/my-cand -o submission.tar.zst
scripts/run-contest submission.tar.zst
```

`proof-src/` holds your Lean sources (module root); `prove.json` lists the modules to compile, e.g.
`{"modules": ["Submission.TreeRadix"]}`. Import only `Contest.Obligation` (which imports `BendVerify`).
Useful tools in `BendVerify.Support`: `App`, `App_iff`, `Eval_call_App`, `Eval_mat_var`,
`Eval_natCase_var`, `exists_EvalList_cons`, `simulate_on`, `agreeOnB_sound`. See
`examples/valid-optimization/proof-src/Submission/TreeRadix.lean` and `Lexer.lean` for complete
proofs; with several proof modules, list an aggregating module last in `prove.json` (it is the
export root).

## What gets rejected

Anything in `docs/THREAT_MODEL.md`, in particular: axioms other than `propext`, `Quot.sound`,
`Classical.choice` (so no `sorry`, no `native_decide`); opaque/unsafe/partial
declarations (structures and inductive types are fine: the kernel re-checks them); redeclaring
any existing constant; proofs whose type is not exactly
the generated goal; IR that does not lower to Bend directly (matches only on parameters or pattern
variables; let/par/match only in statement position); function names `main` or `harness.*`.
