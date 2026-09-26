# VerifiedIR v1: syntax, semantics, the required theorem, and proofs

Source of truth: `trusted/spec/lean/BendVerify/*.lean` (Lean 4.27, core only, no Mathlib).

## 1. Where VerifiedIR sits

```
Bend source ──(pinned bend.ts: parse, check, elaborate)──► checked Book (Def.e / Def.v)
    │                                                           │
    │                                   trusted extractor (extract.mjs): Def.e ≡ Def.v required
    ▼                                                           ▼
                             reference VerifiedIR  P_0   (pinned in competition.json)
                                         │
                   UNTRUSTED OPTIMIZER (candidate's bend2/opt/, sandboxed)
                                         │   emits P_1 … P_n and one certificate step per arrow
                                         ▼
                             candidate VerifiedIR  Q = P_n
                                         │
     proof:  Equiv ctx P_0 P_n   (library-rule steps + kernel-checked lemma steps)
                                         │
      trusted lowering (lower.py) ──► Bend source ──► re-extraction must give Q back exactly
                                         │
                   pinned reference bend.ts check ──► pinned comp.ts ──► C ──► clang ──► binary
```

`comp.ts` has no internal IR (`BEND_AUDIT.md` §C), so the untrusted optimisation boundary is
placed on a formal IR extracted from the checked Book, and the unmodified reference compiler is
used after it.

## 2. Syntax

```lean
inductive Ty   | u32 | nat | adt (id : Nat)
inductive Prim | u32_add | u32_sub | … | nat_is_ge | bool_and | bool_or | bool_not   -- 37 Base operations
inductive Expr
  | var (i : Nat)                         -- de Bruijn (0 = innermost)
  | u32 (k : Nat) | nat (k : Nat)         -- literals
  | prim (p : Prim) (args : List Expr)
  | ctr (adt tag : Nat) (args : List Expr)
  | call (f : Nat) (args : List Expr)     -- first-order, possibly recursive
  | let_ (e body : Expr)
  | par (e₁ e₂ body : Expr)               -- Bend's parallel let  a b = f(..) g(..)
  | mat (adt : Nat) (scrut : Expr) (arms : List (Nat × Expr))   -- arm t = (arity, body)
  | natCase (scrut zero succ : Expr)      -- match on 0n / 1n+p
structure Fn   where name : String; params : List Ty; ret : Ty; body : Expr
structure Prog where adts : List Adt; fns : List Fn
inductive Val  | u32 (n : Nat) | nat (n : Nat) | ctr (tag : Nat) (fields : List Val)
```

The JSON form (`trusted/schema/verifiedir.py`) is a one-to-one serialisation, validated strictly:
exact field sets, identifier regexes, index ranges, constructor/call/primitive arities, one arm
per constructor with the right arity, variables in scope, literal ranges (u32 < 2^32,
nat < 2^48), size and depth limits.

**Fragment (v1).** Values; user datatypes (`is Data`, no parameters); Base `Bool`, `Char`
(`Chr{code}`) and `String` (`SNil | SCon{Char, String}`) with their exact Base shapes, including
string and character literals; **one** monomorphic pair instance `A & B` (Base
`Sigma<&1,&1,A,_=>B>`, constructor `Tuple`); constructors, pattern matching (nested/multi-column
matches are flattened by Bend and extracted as nested `mat`/`natCase`), first-order calls,
recursion (any: Bend's checker has already required termination, and the semantics does not
need it), U32 and Nat arithmetic/comparisons/bit operations, `Bool.and/or/not`, `let`, and
parallel `let` (pure, so semantically sequential). **Rejected, not approximated:** F32, arrays,
closures/lambdas, templates, `@unsafe`, foreign C/JS, IO, open laws and `?TODO`, other
parameterised datatypes (`List`, `Maybe`, …), more than one pair instance, U32/string literal
patterns, parallel lets with more than two bindings. Memory representation (boxing, refcounts, reuse) is
abstracted away: values are finite trees, which is sound for Bend's pure, affine fragment.

## 3. Semantics

A deterministic, fuel-indexed big-step evaluator (`BendVerify.Semantics.ev`):

```lean
def ev : Nat → Prog → Env → Expr → Option Val     -- none = out of fuel or stuck
def Eval (P) (ρ) (e) (v) : Prop := ∃ n, ev n P ρ e = some v
def Run  (P) (name) (args) (v) : Prop := ∃ i fn, P.findFn name = some (i, fn) ∧ ∃ n, runFn n P i args = some v
```

Strict, left-to-right evaluation; a call binds its argument values with the last parameter as
variable 0; `mat` requires the scrutinee to be a constructor whose arm has exactly its field
count; `natCase` binds the predecessor. Fuel monotonicity (`ev_mono`) and determinism
(`Eval_det`) are proved, as are fuel-free characterisations of every construct (`Eval_call`,
`Eval_mat`, …).

**Primitives** (`Prim.eval`) follow Base's pure-Bend definitions exactly: U32 operations are
modulo 2^32; `div(a,0) = 0`; `mod(a,0) = a`; `shln/shrn` by ≥ 32 give 0; `shl/shr` shift by one;
comparisons return Base `Bool` (`False` = tag 0, `True` = tag 1); `Nat.sub` truncates;
`Nat.div(a,0) = 0`, `Nat.mod(a,0) = a`; `Bool.and(False,_) = False`, `Bool.and(True,b) = b`
(dually for `or`). Operands are reduced mod 2^32 first, so every operation is total on raw
naturals. `tests/integration/test_prim_conformance.py` checks 256 edge cases three ways: the Lean
spec (kernel `rfl`), Base's pure-Bend definitions (the reference checker's `{==}`), and the
compiled C.

## 4. The theorem the verifier requires (competitors never write it)

```lean
structure Ctx where adts : List Adt; entry : String; params : List Ty; ret : Ty

def WfEntry (c : Ctx) (P : Prog) : Prop :=
  c.adts <+: P.adts ∧ ∃ i fn, P.findFn c.entry = some (i, fn) ∧ fn.params = c.params ∧ fn.ret = c.ret

def Equiv (c : Ctx) (P Q : Prog) : Prop :=
  WfEntry c P ∧ WfEntry c Q ∧
  ∀ args, HasTys c.adts c.params args → ∀ v, Run P c.entry args v ↔ Run Q c.entry args v
```

`ctx` is fixed by the verifier from the reference program (entry name and signature, reference
datatypes). For every well-typed input, both programs have the same results, **including
non-termination and getting stuck** (the `↔` over all `v`). The candidate may add datatypes and
functions but must expose the entry with the reference signature. Benchmarks take their size and
seed as *runtime* inputs (`run(n, x)`), so a candidate cannot precompute the answer: that would
make `Equiv` false for other inputs, and no proof can exist.

The generated module `Contest.Obligation` states, per workload `w`,
`w.Claim := Equiv ctx P_0 P_n`, and the single root

```lean
def RootGoal : Prop := Stamped "bendverify/v1/<competition_id>/<candidate_repo_hash>" (w₁.Claim ∧ w₂.Claim ∧ …)
```

`Stamped s p := Stamp s ∧ p`, where `Stamp s` has the single constructor `Stamp.mk s`. The
verifier's replay checker adds `theorem Contest.Certified.root : RootGoal` through the kernel;
that one theorem is `CandidateValid(competition_id, candidate_repo_hash)`.

## 5. Proof-carrying optimisation: chains, library rules, novel lemmas

The optimizer emits `P_0 → P_1 → … → P_n` and one step per arrow; the verifier recomputes every
intermediate digest itself and composes the steps with the proven `Equiv.trans`.

**Library-rule steps** (pre-proven rewrite rules; the competitor names only the rule and the
location). `Rules.lean` defines an *executable* checker `applyStep : Prog → Step → Option Prog`
and proves once and for all

```lean
theorem applyStep_sound : applyStep P s = some Q → WfEntry c P → Equiv c P Q
```

Rules in v1: `fold` (a primitive on literals becomes its value), `caseCtr` (match on an explicit
constructor becomes lets + that arm), `natLit` (natCase on a literal), `inline` (a call to another
function becomes lets + its closed body). The generated obligation proves each rule step as
`step_equiv ctx P_k P_{k+1} s (by decide) rfl`: the kernel *evaluates* the checker and compares
its output with the claimed `P_{k+1}`, so a false claim does not compile. Soundness rests on three
general theorems:

* `Simulate.simulate` / `equiv_of_bodies`: if every changed function body simulates the old one
  *in the new program* (and vice versa), the programs are equivalent at every entry — this is what
  makes local rewrites sound through recursion;
* `replaceAt_sound`: a local equivalence is a congruence for every expression context;
* `Lift.ev_lift`: de Bruijn lifting commutes with evaluation (fuel for fuel), which justifies the
  sequential lets introduced by `caseCtr`/`inline`.

**Lemma steps** (novel transformations). The generated obligation contains
`def goal_k : Prop := Stamped "<stamp>/<w>/step/k" (Equiv ctx P_k P_{k+1})`, and the competitor
supplies a proof term of exactly that type. The spec ships proven tools for such proofs
(`Support.lean`): `App` (calls on values), existential-eliminating `simp` lemmas for symbolic
evaluation, `Expr.beq` with soundness, `callsIn`/`simulate_on`/`agreeOnB` (evaluation of
call-closed code transfers between programs that agree on the reachable functions).

**Demo.** *tree-radix*: step 0 is a library `inline` of `sort` into `run`; step 1 is a novel
deforestation lemma: `to_map ∘ gen` becomes `to_map.gen` and `chk ∘ to_arr` becomes
`chk.to_arr` (`proof-src/Submission/TreeRadix.lean`, ~330 lines: symbolic characterisation of
the six functions involved, induction on the depth, well-founded induction on the trie, transfer
of the unchanged functions with `simulate_on`). *lexer*: one novel fold/build-fusion lemma:
`lex(gen(tpl, s, k), r)` becomes `lex.fin(lex.gen(tpl, s, k, r))`, with state-threading twins of
`gen.at`, `expand`, `ident`, `num`, `op` (`proof-src/Submission/Lexer.lean`, ~520 lines:
`lex(P(args, rest), r) = lex(rest, P'(args, r))` for every producer, well-founded induction on
the template string, and a two-direction transfer — `simulate` one way, and through an auxiliary
program plus `simulate_on` the other way, because the changed function `line` is called from
`batch`, not the entry).

## 6. What the semantics deliberately does not say

It says nothing about time or memory: two equivalent programs may differ arbitrarily in cost,
which is exactly what the competition measures. It models Nat as unbounded (the compiled runtime
fail-stops at 2^48, see `TRUST_MODEL.md`). It gives no meaning to F32, arrays, IO or foreign code,
which are therefore outside the fragment.
