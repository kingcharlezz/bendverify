/-
BendVerify.Semantics — deterministic big-step semantics of VerifiedIR.

TRUSTED. `ev n P ρ e` evaluates `e` in environment `ρ` with fuel `n`; it
returns `none` when fuel runs out or evaluation is stuck (ill-typed
primitive, missing arm, unknown function, arity mismatch). A program
*terminates with value v* when some fuel produces `some v`
(`Eval`, below); fuel monotonicity (Lemmas.lean) makes this independent of
the particular fuel.
-/
import BendVerify.Syntax

namespace BendVerify

/-- 2^32. -/
def M32 : Nat := 4294967296

abbrev Env := List Val

def boolV (b : Bool) : Val := if b then .ctr 1 [] else .ctr 0 []

/-- Base's `U32.shln`: shifting by 32 or more yields 0. -/
def shln32 (a n : Nat) : Nat := if n < 32 then (a % M32 * 2 ^ n) % M32 else 0

/-- Base's `U32.shrn`. -/
def shrn32 (a n : Nat) : Nat := if n < 32 then (a % M32) / 2 ^ n else 0

/-- Meaning of every primitive. Operands are reduced mod 2^32 first, so every
operation is total on raw naturals and always returns a canonical U32. -/
def Prim.eval : Prim → List Val → Option Val
  | .u32_add,  [.u32 a, .u32 b] => some (.u32 ((a + b) % M32))
  | .u32_sub,  [.u32 a, .u32 b] => some (.u32 ((a % M32 + (M32 - b % M32)) % M32))
  | .u32_mul,  [.u32 a, .u32 b] => some (.u32 ((a * b) % M32))
  | .u32_div,  [.u32 a, .u32 b] => some (.u32 (if b % M32 = 0 then 0 else (a % M32) / (b % M32)))
  | .u32_mod,  [.u32 a, .u32 b] => some (.u32 (if b % M32 = 0 then a % M32 else (a % M32) % (b % M32)))
  | .u32_and,  [.u32 a, .u32 b] => some (.u32 ((a % M32) &&& (b % M32)))
  | .u32_or,   [.u32 a, .u32 b] => some (.u32 ((a % M32) ||| (b % M32)))
  | .u32_xor,  [.u32 a, .u32 b] => some (.u32 ((a % M32) ^^^ (b % M32)))
  | .u32_not,  [.u32 a]         => some (.u32 (M32 - 1 - a % M32))
  | .u32_shl,  [.u32 a]         => some (.u32 ((a * 2) % M32))
  | .u32_shr,  [.u32 a]         => some (.u32 ((a % M32) / 2))
  | .u32_shln, [.u32 a, .nat n] => some (.u32 (shln32 a n))
  | .u32_shrn, [.u32 a, .nat n] => some (.u32 (shrn32 a n))
  | .u32_inc,  [.u32 a]         => some (.u32 ((a + 1) % M32))
  | .u32_is_eq, [.u32 a, .u32 b] => some (boolV (a % M32 == b % M32))
  | .u32_is_ne, [.u32 a, .u32 b] => some (boolV (a % M32 != b % M32))
  | .u32_is_lt, [.u32 a, .u32 b] => some (boolV (decide (a % M32 < b % M32)))
  | .u32_is_le, [.u32 a, .u32 b] => some (boolV (decide (a % M32 ≤ b % M32)))
  | .u32_is_gt, [.u32 a, .u32 b] => some (boolV (decide (a % M32 > b % M32)))
  | .u32_is_ge, [.u32 a, .u32 b] => some (boolV (decide (a % M32 ≥ b % M32)))
  | .u32_is_zero, [.u32 a]      => some (boolV (a % M32 == 0))
  | .u32_to_nat, [.u32 a]       => some (.nat (a % M32))
  | .u32_from_nat, [.nat n]     => some (.u32 (n % M32))
  | .nat_add, [.nat a, .nat b]  => some (.nat (a + b))
  | .nat_sub, [.nat a, .nat b]  => some (.nat (a - b))
  | .nat_mul, [.nat a, .nat b]  => some (.nat (a * b))
  | .nat_div, [.nat a, .nat b]  => some (.nat (if b = 0 then 0 else a / b))
  | .nat_mod, [.nat a, .nat b]  => some (.nat (if b = 0 then a else a % b))
  | .nat_is_eq, [.nat a, .nat b] => some (boolV (a == b))
  | .nat_is_ne, [.nat a, .nat b] => some (boolV (a != b))
  | .nat_is_lt, [.nat a, .nat b] => some (boolV (decide (a < b)))
  | .nat_is_le, [.nat a, .nat b] => some (boolV (decide (a ≤ b)))
  | .nat_is_gt, [.nat a, .nat b] => some (boolV (decide (a > b)))
  | .nat_is_ge, [.nat a, .nat b] => some (boolV (decide (a ≥ b)))
  -- Base: `Bool.and(False, _) = False`, `Bool.and(True, b) = b` (and dually for `or`)
  | .bool_and, [.ctr 0 [], _]   => some (.ctr 0 [])
  | .bool_and, [.ctr 1 [], b]   => some b
  | .bool_or,  [.ctr 1 [], _]   => some (.ctr 1 [])
  | .bool_or,  [.ctr 0 [], b]   => some b
  | .bool_not, [.ctr 0 []]      => some (.ctr 1 [])
  | .bool_not, [.ctr 1 []]      => some (.ctr 0 [])
  | _, _ => none

/-- Map a partial function over a list; `none` if any element fails. -/
def mapOpt {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs =>
    match f x with
    | none => none
    | some y =>
      match mapOpt f xs with
      | none => none
      | some ys => some (y :: ys)

/-- Evaluation with fuel. Every node consumes one unit of fuel, and the
sub-evaluations of a node receive the remaining fuel. -/
def ev : Nat → Prog → Env → Expr → Option Val
  | 0, _, _, _ => none
  | n + 1, P, ρ, e =>
    match e with
    | .var i => ρ[i]?
    | .u32 k => some (.u32 (k % M32))
    | .nat k => some (.nat k)
    | .prim p as =>
      match mapOpt (ev n P ρ) as with
      | none => none
      | some vs => p.eval vs
    | .ctr _ t as =>
      match mapOpt (ev n P ρ) as with
      | none => none
      | some vs => some (.ctr t vs)
    | .call f as =>
      match mapOpt (ev n P ρ) as with
      | none => none
      | some vs =>
        match P.fns[f]? with
        | none => none
        | some fn => if vs.length = fn.params.length then ev n P vs.reverse fn.body else none
    | .let_ e₁ b =>
      match ev n P ρ e₁ with
      | none => none
      | some v => ev n P (v :: ρ) b
    | .par e₁ e₂ b =>
      match ev n P ρ e₁ with
      | none => none
      | some v₁ =>
        match ev n P ρ e₂ with
        | none => none
        | some v₂ => ev n P (v₂ :: v₁ :: ρ) b
    | .mat _ s arms =>
      match ev n P ρ s with
      | some (.ctr t fs) =>
        match arms[t]? with
        | none => none
        | some (k, body) => if fs.length = k then ev n P (fs.reverse ++ ρ) body else none
      | _ => none
    | .natCase s z k =>
      match ev n P ρ s with
      | some (.nat 0) => ev n P ρ z
      | some (.nat (m + 1)) => ev n P (.nat m :: ρ) k
      | _ => none

/-- `e` terminates with value `v` (for some amount of fuel). -/
def Eval (P : Prog) (ρ : Env) (e : Expr) (v : Val) : Prop :=
  ∃ n, ev n P ρ e = some v

/-- Call function number `f` on argument values `args` (with fuel). -/
def runFn (n : Nat) (P : Prog) (f : Nat) (args : List Val) : Option Val :=
  match P.fns[f]? with
  | none => none
  | some fn => if args.length = fn.params.length then ev n P args.reverse fn.body else none

/-- The function named `name` terminates on `args` with value `v`. -/
def Run (P : Prog) (name : String) (args : List Val) (v : Val) : Prop :=
  ∃ i fn, P.findFn name = some (i, fn) ∧ ∃ n, runFn n P i args = some v

end BendVerify
