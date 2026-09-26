/-
BendVerify.Syntax — the VerifiedIR, competition version 1.

TRUSTED. Part of the immutable BendVerify specification. This file (together
with Semantics.lean and Equiv.lean) *is* the definition of what an
optimisation must preserve. Nothing here may be supplied by a competitor.

VerifiedIR is a first-order, pure, strict functional language: exactly the
fragment of checked Bend 2 that the trusted extractor (trusted/verifier/bend)
accepts. It has no closures, no IO, no arrays, no floats, no foreign code,
no @unsafe definitions. Variables are de Bruijn indices (index 0 = most
recently bound value).
-/
namespace BendVerify

/-- Types. `adt i` refers to entry `i` of the program's ADT table. Types are
used by the obligation (to quantify over well-typed entry arguments) and by
the trusted lowering back to Bend. The evaluator ignores them. -/
inductive Ty where
  | u32
  | nat
  | adt (id : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Primitive operations. Each one corresponds to a definition of Bend's Base
library (bend2/base.bend at the pinned commit); the meaning of each is given by
`Prim.eval` in Semantics.lean, which follows Base's pure-Bend definitions
(e.g. `U32.div(a, 0) = 0`, `U32.mod(a, 0) = a`, `U32.shln(a, n) = 0` for
`n ≥ 32`, `Nat.sub` truncates; `Bool.and(True, b) = b`). -/
inductive Prim where
  | u32_add | u32_sub | u32_mul | u32_div | u32_mod
  | u32_and | u32_or  | u32_xor | u32_not
  | u32_shl | u32_shr | u32_shln | u32_shrn
  | u32_inc
  | u32_is_eq | u32_is_ne | u32_is_lt | u32_is_le | u32_is_gt | u32_is_ge
  | u32_is_zero
  | u32_to_nat | u32_from_nat
  | nat_add | nat_sub | nat_mul | nat_div | nat_mod
  | nat_is_eq | nat_is_ne | nat_is_lt | nat_is_le | nat_is_gt | nat_is_ge
  | bool_and | bool_or | bool_not
  deriving DecidableEq, Repr, Inhabited

/-- Expressions.

* `var i`            — de Bruijn variable.
* `u32 k`, `nat k`   — literals (`u32 k` denotes `k mod 2^32`).
* `prim p args`      — primitive operation.
* `ctr adt tag args` — constructor `tag` of ADT `adt` (the ADT id is used only
                        by the lowering; values carry only the tag).
* `call f args`      — call of function `f` (index into `Prog.fns`).
* `let_ e b`         — `b` sees the value of `e` as variable 0.
* `par e1 e2 b`      — Bend's parallel let `a b = f(x) g(y)`; `b` sees the value
                        of `e1` as variable 1 and of `e2` as variable 0.
                        Semantically identical to two lets (the language is
                        pure); it is kept only as a code-generation hint.
* `mat adt s arms`   — match on a constructor value; arm `t` is `(k, body)`
                        and handles constructor `t` with exactly `k` fields,
                        bound so that the LAST field is variable 0.
* `natCase s z k`    — match on a Nat: `z` if 0, else `k` with the
                        predecessor as variable 0. -/
inductive Expr where
  | var (i : Nat)
  | u32 (k : Nat)
  | nat (k : Nat)
  | prim (p : Prim) (args : List Expr)
  | ctr (adt tag : Nat) (args : List Expr)
  | call (f : Nat) (args : List Expr)
  | let_ (e body : Expr)
  | par (e1 e2 body : Expr)
  | mat (adt : Nat) (scrut : Expr) (arms : List (Nat × Expr))
  | natCase (scrut zero succ : Expr)
  deriving Repr, Inhabited

/-- A constructor declaration: name and field types. -/
structure Ctor where
  name : String
  fields : List Ty
  deriving DecidableEq, Repr, Inhabited

/-- An algebraic datatype declaration. -/
structure Adt where
  name : String
  ctors : List Ctor
  deriving DecidableEq, Repr, Inhabited

/-- A function: its name (used to find entry points and by the lowering),
its parameter types, its return type and its body (the body sees the
parameters with the LAST parameter as variable 0). -/
structure Fn where
  name : String
  params : List Ty
  ret : Ty
  body : Expr
  deriving Repr, Inhabited

/-- A program: ADT table and function table. -/
structure Prog where
  adts : List Adt
  fns : List Fn
  deriving Repr, Inhabited

/-- Runtime values. Booleans are Base's `Bool` (`False{}` = tag 0,
`True{}` = tag 1) and comparisons return Base's `Cmp` (LT/EQ/GT = 0/1/2). -/
inductive Val where
  | u32 (n : Nat)
  | nat (n : Nat)
  | ctr (tag : Nat) (fields : List Val)
  deriving Repr, Inhabited

/-- Find the first function with a given name. -/
def Prog.findFn (P : Prog) (name : String) : Option (Nat × Fn) :=
  go P.fns 0
where
  go : List Fn → Nat → Option (Nat × Fn)
    | [], _ => none
    | f :: fs, i => if f.name = name then some (i, f) else go fs (i + 1)

end BendVerify
