/-
BendVerify.Lift — de Bruijn lifting, closedness and sequential lets.

`e.lift c d` adds `d` to every variable of `e` that is ≥ `c` (i.e. free at
cut-off `c`). The key fact (`ev_lift`) is that evaluating a lifted expression
in an environment with `d` extra entries inserted at position `c` is exactly
the same computation, fuel for fuel.
-/
import BendVerify.Simulate

namespace BendVerify

mutual
def Expr.lift (c d : Nat) : Expr → Expr
  | .var i => .var (if i < c then i else i + d)
  | .u32 k => .u32 k
  | .nat k => .nat k
  | .prim p as => .prim p (liftList c d as)
  | .ctr a t as => .ctr a t (liftList c d as)
  | .call f as => .call f (liftList c d as)
  | .let_ e b => .let_ (e.lift c d) (b.lift (c + 1) d)
  | .par e₁ e₂ b => .par (e₁.lift c d) (e₂.lift c d) (b.lift (c + 2) d)
  | .mat a s arms => .mat a (s.lift c d) (liftArms c d arms)
  | .natCase s z k => .natCase (s.lift c d) (z.lift c d) (k.lift (c + 1) d)

def liftList (c d : Nat) : List Expr → List Expr
  | [] => []
  | e :: es => e.lift c d :: liftList c d es

def liftArms (c d : Nat) : List (Nat × Expr) → List (Nat × Expr)
  | [] => []
  | (k, e) :: as => (k, e.lift (c + k) d) :: liftArms c d as
end

theorem liftArms_getElem? (c d : Nat) :
    ∀ (arms : List (Nat × Expr)) (t : Nat),
      (liftArms c d arms)[t]? = (arms[t]?).map (fun kb => (kb.1, kb.2.lift (c + kb.1) d))
  | [], t => by simp [liftArms]
  | (k, e) :: as, 0 => by simp [liftArms]
  | (k, e) :: as, t + 1 => by simp [liftArms, liftArms_getElem? c d as t]

theorem getElem?_insert {ρ₁ ρ' ρ₂ : List Val} (i : Nat) :
    (ρ₁ ++ ρ₂)[i]? = (ρ₁ ++ ρ' ++ ρ₂)[if i < ρ₁.length then i else i + ρ'.length]? := by
  by_cases h : i < ρ₁.length
  · simp only [h, if_true]
    rw [List.getElem?_append_left h, List.append_assoc, List.getElem?_append_left h]
  · simp only [h, if_false]
    have h' : ρ₁.length ≤ i := Nat.le_of_not_lt h
    rw [List.getElem?_append_right h', List.append_assoc,
      List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    congr 1; omega

/-- Lifting commutes with evaluation, with identical fuel. -/
theorem ev_lift : ∀ (n : Nat) (Pg : Prog) (ρ₁ ρ' ρ₂ : Env) (e : Expr),
    ev n Pg (ρ₁ ++ ρ₂) e = ev n Pg (ρ₁ ++ ρ' ++ ρ₂) (e.lift ρ₁.length ρ'.length) := by
  intro n
  induction n with
  | zero => intros; simp [ev_zero]
  | succ n ih =>
    intro Pg ρ₁ ρ' ρ₂ e
    have hl : ∀ (as : List Expr), mapOpt (ev n Pg (ρ₁ ++ ρ₂)) as =
        mapOpt (ev n Pg (ρ₁ ++ ρ' ++ ρ₂)) (liftList ρ₁.length ρ'.length as) := by
      intro as
      induction as with
      | nil => simp [liftList, mapOpt]
      | cons a as iha => simp only [liftList, mapOpt, ← ih Pg ρ₁ ρ' ρ₂ a, iha]
    cases e with
    | var i => simp only [Expr.lift, ev_var]; exact getElem?_insert i
    | u32 k => simp only [Expr.lift, ev_u32]
    | nat k => simp only [Expr.lift, ev_nat]
    | prim p as => simp only [Expr.lift, ev_prim, hl]
    | ctr a t as => simp only [Expr.lift, ev_ctr, hl]
    | call f as => simp only [Expr.lift, ev_call, hl]
    | let_ e b =>
      simp only [Expr.lift, ev_let, ← ih Pg ρ₁ ρ' ρ₂ e]
      cases ev n Pg (ρ₁ ++ ρ₂) e with
      | none => rfl
      | some w =>
        simp only
        have := ih Pg (w :: ρ₁) ρ' ρ₂ b
        simpa using this
    | par e₁ e₂ b =>
      simp only [Expr.lift, ev_par, ← ih Pg ρ₁ ρ' ρ₂ e₁, ← ih Pg ρ₁ ρ' ρ₂ e₂]
      cases ev n Pg (ρ₁ ++ ρ₂) e₁ with
      | none => rfl
      | some w₁ =>
        cases ev n Pg (ρ₁ ++ ρ₂) e₂ with
        | none => rfl
        | some w₂ =>
          simp only
          have := ih Pg (w₂ :: w₁ :: ρ₁) ρ' ρ₂ b
          simpa [Nat.add_assoc] using this
    | mat a s arms =>
      simp only [Expr.lift, ev_mat, ← ih Pg ρ₁ ρ' ρ₂ s]
      cases ev n Pg (ρ₁ ++ ρ₂) s with
      | none => rfl
      | some sv =>
        cases sv with
        | u32 _ => rfl
        | nat _ => rfl
        | ctr t fs =>
          simp only [liftArms_getElem?]
          cases arms[t]? with
          | none => rfl
          | some kb =>
            obtain ⟨k, body⟩ := kb
            simp only [Option.map_some]
            by_cases hk : fs.length = k
            · simp only [hk, if_true]
              have := ih Pg (fs.reverse ++ ρ₁) ρ' ρ₂ body
              simp only [List.length_append, List.length_reverse, hk, List.append_assoc] at this
              rw [Nat.add_comm] at this
              simpa [List.append_assoc] using this
            · simp [hk]
    | natCase s z k =>
      simp only [Expr.lift, ev_natCase, ← ih Pg ρ₁ ρ' ρ₂ s]
      cases ev n Pg (ρ₁ ++ ρ₂) s with
      | none => rfl
      | some sv =>
        cases sv with
        | u32 _ => rfl
        | ctr _ _ => rfl
        | nat m =>
          cases m with
          | zero => simp only; exact ih Pg ρ₁ ρ' ρ₂ z
          | succ m =>
            simp only
            have := ih Pg (.nat m :: ρ₁) ρ' ρ₂ k
            simpa using this

theorem Eval_lift {Pg : Prog} {ρ₁ ρ' ρ₂ : Env} {e : Expr} {v : Val} :
    Eval Pg (ρ₁ ++ ρ₂) e v ↔ Eval Pg (ρ₁ ++ ρ' ++ ρ₂) (e.lift ρ₁.length ρ'.length) v := by
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, by rw [← ev_lift]; exact hn⟩
  · rintro ⟨n, hn⟩; exact ⟨n, by rw [ev_lift n Pg ρ₁ ρ' ρ₂]; exact hn⟩

/-- Evaluating a lifted expression with a prefix inserted at the front. -/
theorem Eval_lift0 {Pg : Prog} {ρ' ρ : Env} {e : Expr} {v : Val} :
    Eval Pg (ρ' ++ ρ) (e.lift 0 ρ'.length) v ↔ Eval Pg ρ e v := by
  have := @Eval_lift Pg [] ρ' ρ e v
  simp only [List.nil_append, List.length_nil] at this
  exact this.symm

/-! ## Closed expressions -/

mutual
/-- `closedB k e`: every free variable of `e` is `< k`. -/
def closedB (k : Nat) : Expr → Bool
  | .var i => decide (i < k)
  | .u32 _ => true
  | .nat _ => true
  | .prim _ as => closedListB k as
  | .ctr _ _ as => closedListB k as
  | .call _ as => closedListB k as
  | .let_ e b => closedB k e && closedB (k + 1) b
  | .par e₁ e₂ b => closedB k e₁ && closedB k e₂ && closedB (k + 2) b
  | .mat _ s arms => closedB k s && closedArmsB k arms
  | .natCase s z n => closedB k s && closedB k z && closedB (k + 1) n

def closedListB (k : Nat) : List Expr → Bool
  | [] => true
  | e :: es => closedB k e && closedListB k es

def closedArmsB (k : Nat) : List (Nat × Expr) → Bool
  | [] => true
  | (j, e) :: as => closedB (k + j) e && closedArmsB k as
end

mutual
theorem lift_closed (k d : Nat) : ∀ (e : Expr), closedB k e = true → e.lift k d = e
  | .var i, h => by simp only [closedB, decide_eq_true_eq] at h; simp [Expr.lift, h]
  | .u32 _, _ => rfl
  | .nat _, _ => rfl
  | .prim _ as, h => by simp only [closedB] at h; simp only [Expr.lift, liftList_closed k d as h]
  | .ctr _ _ as, h => by simp only [closedB] at h; simp only [Expr.lift, liftList_closed k d as h]
  | .call _ as, h => by simp only [closedB] at h; simp only [Expr.lift, liftList_closed k d as h]
  | .let_ e b, h => by
    simp only [closedB, Bool.and_eq_true] at h
    simp only [Expr.lift, lift_closed k d e h.1, lift_closed (k + 1) d b h.2]
  | .par e₁ e₂ b, h => by
    simp only [closedB, Bool.and_eq_true] at h
    simp only [Expr.lift, lift_closed k d e₁ h.1.1, lift_closed k d e₂ h.1.2,
      lift_closed (k + 2) d b h.2]
  | .mat _ s arms, h => by
    simp only [closedB, Bool.and_eq_true] at h
    simp only [Expr.lift, lift_closed k d s h.1, liftArms_closed k d arms h.2]
  | .natCase s z n, h => by
    simp only [closedB, Bool.and_eq_true] at h
    simp only [Expr.lift, lift_closed k d s h.1.1, lift_closed k d z h.1.2,
      lift_closed (k + 1) d n h.2]

theorem liftList_closed (k d : Nat) : ∀ (as : List Expr), closedListB k as = true → liftList k d as = as
  | [], _ => rfl
  | e :: es, h => by
    simp only [closedListB, Bool.and_eq_true] at h
    simp only [liftList, lift_closed k d e h.1, liftList_closed k d es h.2]

theorem liftArms_closed (k d : Nat) :
    ∀ (arms : List (Nat × Expr)), closedArmsB k arms = true → liftArms k d arms = arms
  | [], _ => rfl
  | (j, e) :: as, h => by
    simp only [closedArmsB, Bool.and_eq_true] at h
    simp only [liftArms, lift_closed (k + j) d e h.1, liftArms_closed k d as h.2]
end

/-- A closed expression ignores entries appended after the first `k`. -/
theorem Eval_closed {Pg : Prog} {ρ ρ' : Env} {e : Expr} {v : Val}
    (h : closedB ρ.length e = true) : Eval Pg (ρ ++ ρ') e v ↔ Eval Pg ρ e v := by
  have := @Eval_lift Pg ρ ρ' [] e v
  simp only [List.append_nil, lift_closed _ _ e h] at this
  exact this.symm

/-! ## Sequential lets -/

/-- `letsSeq.go as j b` binds `as` left to right; argument number `i` is
lifted over the `j + i` values bound before it. -/
def letsSeq.go : List Expr → Nat → Expr → Expr
  | [], _, b => b
  | a :: as, j, b => .let_ (a.lift 0 j) (letsSeq.go as (j + 1) b)

def letsSeq (as : List Expr) (b : Expr) : Expr := letsSeq.go as 0 b

theorem Eval_letsSeq_go {Pg : Prog} {ρ : Env} {b : Expr} {v : Val} :
    ∀ (as : List Expr) (acc : Env),
      Eval Pg (acc ++ ρ) (letsSeq.go as acc.length b) v ↔
        ∃ vs, EvalList Pg ρ as vs ∧ Eval Pg (vs.reverse ++ acc ++ ρ) b v
  | [], acc => by
    simp only [letsSeq.go]
    constructor
    · intro h; exact ⟨[], EvalList_nil Pg ρ, by simpa using h⟩
    · rintro ⟨vs, hvs, h⟩
      rw [EvalList_nil_iff.mp hvs] at h; simpa using h
  | a :: as, acc => by
    simp only [letsSeq.go, Eval_let]
    constructor
    · rintro ⟨w, hw, h⟩
      have hw' : Eval Pg ρ a w := Eval_lift0.mp hw
      have := (Eval_letsSeq_go as (w :: acc)).mp (by simpa using h)
      obtain ⟨vs, hvs, hb⟩ := this
      exact ⟨w :: vs, EvalList_cons hw' hvs, by simpa using hb⟩
    · rintro ⟨ws, hws, hb⟩
      obtain ⟨w, vs, rfl, hw, hvs⟩ := EvalList_cons_iff.mp hws
      refine ⟨w, Eval_lift0.mpr hw, ?_⟩
      have := (Eval_letsSeq_go as (w :: acc)).mpr ⟨vs, hvs, by simpa using hb⟩
      simpa using this

theorem Eval_letsSeq {Pg : Prog} {ρ : Env} {as : List Expr} {b : Expr} {v : Val} :
    Eval Pg ρ (letsSeq as b) v ↔ ∃ vs, EvalList Pg ρ as vs ∧ Eval Pg (vs.reverse ++ ρ) b v := by
  have := @Eval_letsSeq_go Pg ρ b v as []
  simpa [letsSeq] using this

end BendVerify
