/-
BendVerify.Equiv — THE proposition the verifier requires.

TRUSTED. For a workload with context `c` (entry name, entry signature and
the reference ADT table, all fixed by the verifier from the reference
program), a candidate program `Q` is accepted against the reference `P`
only with a kernel-checked proof of `Equiv c P Q`:

  * both programs expose the entry function with the reference signature
    and keep the reference ADT table as a prefix of their own, and
  * for EVERY well-typed argument list and EVERY value `v`,
    the reference terminates with `v` iff the candidate terminates with `v`.

Competitors never write this statement. The obligation generator
instantiates it with the exact programs and wraps miner-facing goals in
`Stamped`, which forces a proof term to mention the exact candidate digest.
-/
import BendVerify.Lemmas

namespace BendVerify

/-! ## Typing of entry arguments -/

mutual
/-- `HasTy adts T v`: value `v` inhabits type `T` under the ADT table. -/
inductive HasTy (adts : List Adt) : Ty → Val → Prop
  | u32 {n : Nat} : n < M32 → HasTy adts .u32 (.u32 n)
  | nat {n : Nat} : HasTy adts .nat (.nat n)
  | ctr {d t : Nat} {a : Adt} {c : Ctor} {fs : List Val} :
      adts[d]? = some a → a.ctors[t]? = some c → HasTys adts c.fields fs →
      HasTy adts (.adt d) (.ctr t fs)

/-- Pointwise typing of a list of values. -/
inductive HasTys (adts : List Adt) : List Ty → List Val → Prop
  | nil : HasTys adts [] []
  | cons {T : Ty} {Ts : List Ty} {v : Val} {vs : List Val} :
      HasTy adts T v → HasTys adts Ts vs → HasTys adts (T :: Ts) (v :: vs)
end

/-! ## The workload context fixed by the verifier -/

/-- Everything about a workload that the competitor may NOT change. -/
structure Ctx where
  adts : List Adt
  entry : String
  params : List Ty
  ret : Ty
  deriving Repr

/-- `P` exposes the entry with the fixed signature and extends the fixed
ADT table. -/
def WfEntry (c : Ctx) (P : Prog) : Prop :=
  c.adts <+: P.adts ∧
  ∃ i fn, P.findFn c.entry = some (i, fn) ∧ fn.params = c.params ∧ fn.ret = c.ret

/-- **Semantic equivalence at the entry**: the required correctness property. -/
def Equiv (c : Ctx) (P Q : Prog) : Prop :=
  WfEntry c P ∧ WfEntry c Q ∧
  ∀ args, HasTys c.adts c.params args →
    ∀ v, Run P c.entry args v ↔ Run Q c.entry args v

theorem Equiv.refl {c : Ctx} {P : Prog} (h : WfEntry c P) : Equiv c P P :=
  ⟨h, h, fun _ _ _ => Iff.rfl⟩

theorem Equiv.symm {c : Ctx} {P Q : Prog} (h : Equiv c P Q) : Equiv c Q P :=
  ⟨h.2.1, h.1, fun args ha v => (h.2.2 args ha v).symm⟩

theorem Equiv.trans {c : Ctx} {P Q R : Prog} (h₁ : Equiv c P Q) (h₂ : Equiv c Q R) :
    Equiv c P R :=
  ⟨h₁.1, h₂.2.1, fun args ha v => (h₁.2.2 args ha v).trans (h₂.2.2 args ha v)⟩

/-! ## Binding a proof to an exact candidate -/

/-- `Stamp s` is inhabited only by `Stamp.mk s`: a proof of `Stamp s` must
contain the literal `s`. The obligation generator puts the competition id and
the candidate digest into `s`, so a proof term produced for one candidate is
rejected by the kernel for any other candidate. -/
inductive Stamp : String → Prop
  | mk (s : String) : Stamp s

/-- A miner-facing goal: the stamp for the exact candidate, and the claim. -/
def Stamped (s : String) (p : Prop) : Prop := Stamp s ∧ p

theorem Stamped.claim {s : String} {p : Prop} (h : Stamped s p) : p := h.2

/-! ## Decidable checks used by generated (trusted) proofs -/

def isPrefixB {α : Type} [DecidableEq α] : List α → List α → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => decide (a = b) && isPrefixB as bs

theorem isPrefixB_sound {α : Type} [DecidableEq α] :
    ∀ {l₁ l₂ : List α}, isPrefixB l₁ l₂ = true → l₁ <+: l₂
  | [], l₂, _ => ⟨l₂, rfl⟩
  | _ :: _, [], h => by simp [isPrefixB] at h
  | a :: as, b :: bs, h => by
    simp only [isPrefixB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨t, ht⟩ := isPrefixB_sound h
    exact ⟨t, by simp [← ht]⟩

/-- Executable check for `WfEntry`. -/
def wfEntryB (c : Ctx) (P : Prog) : Bool :=
  isPrefixB c.adts P.adts &&
  match P.findFn c.entry with
  | none => false
  | some (_, fn) => decide (fn.params = c.params) && decide (fn.ret = c.ret)

theorem wfEntryB_sound {c : Ctx} {P : Prog} (h : wfEntryB c P = true) : WfEntry c P := by
  unfold wfEntryB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨isPrefixB_sound h1, ?_⟩
  cases hf : P.findFn c.entry with
  | none => simp [hf] at h2
  | some r =>
    obtain ⟨i, fn⟩ := r
    simp only [hf, Bool.and_eq_true, decide_eq_true_eq] at h2
    exact ⟨i, fn, rfl, h2.1, h2.2⟩

end BendVerify
