/-
BendVerify.Support — reusable, kernel-checked lemmas for competitors' proofs.

Nothing here is part of the *statement* competitors must prove (that is
Syntax + Semantics + Equiv); these are proven tools shipped with the spec so
that novel-transformation proofs can be short:

* `App P f vs v`        — calling function `f` on argument VALUES.
* `Expr.beq`            — executable structural equality (with soundness).
* `callsIn S e`         — every call in `e` targets a function in `S`.
* `simulate_on`         — evaluation of call-closed code transfers between two
                          programs that agree on the functions it can reach.
* `agreeOnB`            — executable check of that agreement.
-/
import BendVerify.Rules

namespace BendVerify

/-! ## Calls on values -/

def App (P : Prog) (f : Nat) (vs : List Val) (v : Val) : Prop :=
  ∃ fn, P.fns[f]? = some fn ∧ vs.length = fn.params.length ∧ Eval P vs.reverse fn.body v

theorem Eval_call_App {P : Prog} {ρ : Env} {f : Nat} {as : List Expr} {v : Val} :
    Eval P ρ (.call f as) v ↔ ∃ vs, EvalList P ρ as vs ∧ App P f vs v := by
  rw [Eval_call]
  constructor
  · rintro ⟨vs, fn, h1, h2, h3, h4⟩; exact ⟨vs, h1, fn, h2, h3, h4⟩
  · rintro ⟨vs, h1, fn, h2, h3, h4⟩; exact ⟨vs, fn, h1, h2, h3, h4⟩

theorem App_iff {P : Prog} {f : Nat} {fn : Fn} (h : P.fns[f]? = some fn) {vs : List Val} {v : Val} :
    App P f vs v ↔ vs.length = fn.params.length ∧ Eval P vs.reverse fn.body v := by
  constructor
  · rintro ⟨fn', h', hl, he⟩; rw [h] at h'; cases h'; exact ⟨hl, he⟩
  · rintro ⟨hl, he⟩; exact ⟨fn, h, hl, he⟩

/-! ## Existential-eliminating forms (for symbolic evaluation with `simp`) -/

theorem exists_EvalList_nil {P : Prog} {ρ : Env} {p : List Val → Prop} :
    (∃ vs, EvalList P ρ [] vs ∧ p vs) ↔ p [] := by
  constructor
  · rintro ⟨vs, h, hp⟩; rw [EvalList_nil_iff.mp h] at hp; exact hp
  · intro h; exact ⟨[], EvalList_nil P ρ, h⟩

theorem exists_EvalList_cons {P : Prog} {ρ : Env} {a : Expr} {as : List Expr}
    {p : List Val → Prop} :
    (∃ vs, EvalList P ρ (a :: as) vs ∧ p vs) ↔
      ∃ v, Eval P ρ a v ∧ ∃ vs, EvalList P ρ as vs ∧ p (v :: vs) := by
  constructor
  · rintro ⟨ws, h, hp⟩
    obtain ⟨v, vs, rfl, hv, hvs⟩ := EvalList_cons_iff.mp h
    exact ⟨v, hv, vs, hvs, hp⟩
  · rintro ⟨v, hv, vs, hvs, hp⟩
    exact ⟨v :: vs, EvalList_cons hv hvs, hp⟩

/-- A match whose scrutinee is a variable, with the arm selected explicitly. -/
theorem Eval_mat_var {P : Prog} {ρ : Env} {a i : Nat} {arms : List (Nat × Expr)} {v : Val} :
    Eval P ρ (.mat a (.var i) arms) v ↔
      ∃ t fs, ρ[i]? = some (.ctr t fs) ∧ ∃ body, arms[t]? = some (fs.length, body) ∧
        Eval P (fs.reverse ++ ρ) body v := by
  rw [Eval_mat]
  constructor
  · rintro ⟨t, fs, k, body, hs, harm, hl, hb⟩
    subst hl
    exact ⟨t, fs, Eval_var.mp hs, body, harm, hb⟩
  · rintro ⟨t, fs, hs, body, harm, hb⟩
    exact ⟨t, fs, fs.length, body, Eval_var.mpr hs, harm, rfl, hb⟩

/-- A single-arm match on a variable (a record or pair destructuring). -/
theorem Eval_mat1_var {P : Prog} {ρ : Env} {a i k : Nat} {body : Expr} {v : Val} :
    Eval P ρ (.mat a (.var i) [(k, body)]) v ↔
      ∃ fs, ρ[i]? = some (.ctr 0 fs) ∧ fs.length = k ∧ Eval P (fs.reverse ++ ρ) body v := by
  rw [Eval_mat_var]
  constructor
  · rintro ⟨t, fs, hs, b, harm, hb⟩
    cases t with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at harm
      obtain ⟨hk, rfl⟩ := harm
      exact ⟨fs, hs, hk.symm, hb⟩
    | succ t => simp at harm
  · rintro ⟨fs, hs, hk, hb⟩
    exact ⟨0, fs, hs, body, by simp [hk], hb⟩

theorem Eval_mat1_var1 {P : Prog} {ρ : Env} {a i : Nat} {body : Expr} {v : Val} :
    Eval P ρ (.mat a (.var i) [(1, body)]) v ↔
      ∃ x, ρ[i]? = some (.ctr 0 [x]) ∧ Eval P (x :: ρ) body v := by
  rw [Eval_mat1_var]
  constructor
  · rintro ⟨fs, hs, hk, hb⟩
    match fs, hk with
    | [x], _ => exact ⟨x, hs, by simpa using hb⟩
  · rintro ⟨x, hs, hb⟩
    exact ⟨[x], hs, rfl, by simpa using hb⟩

theorem Eval_mat1_var2 {P : Prog} {ρ : Env} {a i : Nat} {body : Expr} {v : Val} :
    Eval P ρ (.mat a (.var i) [(2, body)]) v ↔
      ∃ x y, ρ[i]? = some (.ctr 0 [x, y]) ∧ Eval P (y :: x :: ρ) body v := by
  rw [Eval_mat1_var]
  constructor
  · rintro ⟨fs, hs, hk, hb⟩
    match fs, hk with
    | [x, y], _ => exact ⟨x, y, hs, by simpa using hb⟩
  · rintro ⟨x, y, hs, hb⟩
    exact ⟨[x, y], hs, rfl, by simpa using hb⟩

/-- `Eval` of a natCase on a variable. -/
theorem Eval_natCase_var {P : Prog} {ρ : Env} {i : Nat} {z k : Expr} {v : Val} :
    Eval P ρ (.natCase (.var i) z k) v ↔
      (ρ[i]? = some (.nat 0) ∧ Eval P ρ z v) ∨
      (∃ m, ρ[i]? = some (.nat (m + 1)) ∧ Eval P (.nat m :: ρ) k v) := by
  rw [Eval_natCase, Eval_var]
  simp only [Eval_var]

/-! ## Executable structural equality -/

mutual
def Expr.beq : Expr → Expr → Bool
  | .var i, .var j => i == j
  | .u32 i, .u32 j => i == j
  | .nat i, .nat j => i == j
  | .prim p as, .prim q bs => decide (p = q) && Expr.beqList as bs
  | .ctr a t as, .ctr b u bs => a == b && t == u && Expr.beqList as bs
  | .call f as, .call g bs => f == g && Expr.beqList as bs
  | .let_ e b, .let_ e' b' => Expr.beq e e' && Expr.beq b b'
  | .par a b c, .par a' b' c' => Expr.beq a a' && Expr.beq b b' && Expr.beq c c'
  | .mat a s arms, .mat b s' arms' => a == b && Expr.beq s s' && Expr.beqArms arms arms'
  | .natCase s z k, .natCase s' z' k' => Expr.beq s s' && Expr.beq z z' && Expr.beq k k'
  | _, _ => false

def Expr.beqList : List Expr → List Expr → Bool
  | [], [] => true
  | a :: as, b :: bs => Expr.beq a b && Expr.beqList as bs
  | _, _ => false

def Expr.beqArms : List (Nat × Expr) → List (Nat × Expr) → Bool
  | [], [] => true
  | (i, a) :: as, (j, b) :: bs => i == j && Expr.beq a b && Expr.beqArms as bs
  | _, _ => false
end

mutual
theorem Expr.eq_of_beq : ∀ {a b : Expr}, Expr.beq a b = true → a = b
  | .var i, .var j, h => by simp [Expr.beq] at h; rw [h]
  | .u32 i, .u32 j, h => by simp [Expr.beq] at h; rw [h]
  | .nat i, .nat j, h => by simp [Expr.beq] at h; rw [h]
  | .prim p as, .prim q bs, h => by
    simp only [Expr.beq, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1, Expr.eq_of_beqList h.2]
  | .ctr a t as, .ctr b u bs, h => by
    simp only [Expr.beq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1, h.1.2, Expr.eq_of_beqList h.2]
  | .call f as, .call g bs, h => by
    simp only [Expr.beq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, Expr.eq_of_beqList h.2]
  | .let_ e b, .let_ e' b', h => by
    simp only [Expr.beq, Bool.and_eq_true] at h
    rw [Expr.eq_of_beq h.1, Expr.eq_of_beq h.2]
  | .par a b c, .par a' b' c', h => by
    simp only [Expr.beq, Bool.and_eq_true] at h
    rw [Expr.eq_of_beq h.1.1, Expr.eq_of_beq h.1.2, Expr.eq_of_beq h.2]
  | .mat a s arms, .mat b s' arms', h => by
    simp only [Expr.beq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1, Expr.eq_of_beq h.1.2, Expr.eq_of_beqArms h.2]
  | .natCase s z k, .natCase s' z' k', h => by
    simp only [Expr.beq, Bool.and_eq_true] at h
    rw [Expr.eq_of_beq h.1.1, Expr.eq_of_beq h.1.2, Expr.eq_of_beq h.2]
  | .var _, .u32 _, h | .var _, .nat _, h | .var _, .prim _ _, h | .var _, .ctr _ _ _, h
  | .var _, .call _ _, h | .var _, .let_ _ _, h | .var _, .par _ _ _, h | .var _, .mat _ _ _, h
  | .var _, .natCase _ _ _, h => by simp [Expr.beq] at h
  | .u32 _, .var _, h | .u32 _, .nat _, h | .u32 _, .prim _ _, h | .u32 _, .ctr _ _ _, h
  | .u32 _, .call _ _, h | .u32 _, .let_ _ _, h | .u32 _, .par _ _ _, h | .u32 _, .mat _ _ _, h
  | .u32 _, .natCase _ _ _, h => by simp [Expr.beq] at h
  | .nat _, .var _, h | .nat _, .u32 _, h | .nat _, .prim _ _, h | .nat _, .ctr _ _ _, h
  | .nat _, .call _ _, h | .nat _, .let_ _ _, h | .nat _, .par _ _ _, h | .nat _, .mat _ _ _, h
  | .nat _, .natCase _ _ _, h => by simp [Expr.beq] at h
  | .prim _ _, .var _, h | .prim _ _, .u32 _, h | .prim _ _, .nat _, h | .prim _ _, .ctr _ _ _, h
  | .prim _ _, .call _ _, h | .prim _ _, .let_ _ _, h | .prim _ _, .par _ _ _, h
  | .prim _ _, .mat _ _ _, h | .prim _ _, .natCase _ _ _, h => by simp [Expr.beq] at h
  | .ctr _ _ _, .var _, h | .ctr _ _ _, .u32 _, h | .ctr _ _ _, .nat _, h | .ctr _ _ _, .prim _ _, h
  | .ctr _ _ _, .call _ _, h | .ctr _ _ _, .let_ _ _, h | .ctr _ _ _, .par _ _ _, h
  | .ctr _ _ _, .mat _ _ _, h | .ctr _ _ _, .natCase _ _ _, h => by simp [Expr.beq] at h
  | .call _ _, .var _, h | .call _ _, .u32 _, h | .call _ _, .nat _, h | .call _ _, .prim _ _, h
  | .call _ _, .ctr _ _ _, h | .call _ _, .let_ _ _, h | .call _ _, .par _ _ _, h
  | .call _ _, .mat _ _ _, h | .call _ _, .natCase _ _ _, h => by simp [Expr.beq] at h
  | .let_ _ _, .var _, h | .let_ _ _, .u32 _, h | .let_ _ _, .nat _, h | .let_ _ _, .prim _ _, h
  | .let_ _ _, .ctr _ _ _, h | .let_ _ _, .call _ _, h | .let_ _ _, .par _ _ _, h
  | .let_ _ _, .mat _ _ _, h | .let_ _ _, .natCase _ _ _, h => by simp [Expr.beq] at h
  | .par _ _ _, .var _, h | .par _ _ _, .u32 _, h | .par _ _ _, .nat _, h
  | .par _ _ _, .prim _ _, h | .par _ _ _, .ctr _ _ _, h | .par _ _ _, .call _ _, h
  | .par _ _ _, .let_ _ _, h | .par _ _ _, .mat _ _ _, h | .par _ _ _, .natCase _ _ _, h => by
    simp [Expr.beq] at h
  | .mat _ _ _, .var _, h | .mat _ _ _, .u32 _, h | .mat _ _ _, .nat _, h
  | .mat _ _ _, .prim _ _, h | .mat _ _ _, .ctr _ _ _, h | .mat _ _ _, .call _ _, h
  | .mat _ _ _, .let_ _ _, h | .mat _ _ _, .par _ _ _, h | .mat _ _ _, .natCase _ _ _, h => by
    simp [Expr.beq] at h
  | .natCase _ _ _, .var _, h | .natCase _ _ _, .u32 _, h | .natCase _ _ _, .nat _, h
  | .natCase _ _ _, .prim _ _, h | .natCase _ _ _, .ctr _ _ _, h | .natCase _ _ _, .call _ _, h
  | .natCase _ _ _, .let_ _ _, h | .natCase _ _ _, .par _ _ _, h
  | .natCase _ _ _, .mat _ _ _, h => by simp [Expr.beq] at h

theorem Expr.eq_of_beqList : ∀ {as bs : List Expr}, Expr.beqList as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [Expr.beqList, Bool.and_eq_true] at h
    rw [Expr.eq_of_beq h.1, Expr.eq_of_beqList h.2]
  | [], _ :: _, h => by simp [Expr.beqList] at h
  | _ :: _, [], h => by simp [Expr.beqList] at h

theorem Expr.eq_of_beqArms : ∀ {as bs : List (Nat × Expr)}, Expr.beqArms as bs = true → as = bs
  | [], [], _ => rfl
  | (i, a) :: as, (j, b) :: bs, h => by
    simp only [Expr.beqArms, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1, Expr.eq_of_beq h.1.2, Expr.eq_of_beqArms h.2]
  | [], _ :: _, h => by simp [Expr.beqArms] at h
  | _ :: _, [], h => by simp [Expr.beqArms] at h
end

def Fn.beq (f g : Fn) : Bool :=
  decide (f.name = g.name) && decide (f.params = g.params) && decide (f.ret = g.ret) &&
    Expr.beq f.body g.body

theorem Fn.eq_of_beq {f g : Fn} (h : Fn.beq f g = true) : f = g := by
  cases f; cases g
  simp only [Fn.beq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  rw [h1, h2, h3, Expr.eq_of_beq h4]

/-! ## Call-closed code -/

mutual
def callsIn (S : Nat → Bool) : Expr → Bool
  | .var _ => true
  | .u32 _ => true
  | .nat _ => true
  | .prim _ as => callsInList S as
  | .ctr _ _ as => callsInList S as
  | .call f as => S f && callsInList S as
  | .let_ e b => callsIn S e && callsIn S b
  | .par a b c => callsIn S a && callsIn S b && callsIn S c
  | .mat _ s arms => callsIn S s && callsInArms S arms
  | .natCase s z k => callsIn S s && callsIn S z && callsIn S k

def callsInList (S : Nat → Bool) : List Expr → Bool
  | [] => true
  | e :: es => callsIn S e && callsInList S es

def callsInArms (S : Nat → Bool) : List (Nat × Expr) → Bool
  | [] => true
  | (_, e) :: as => callsIn S e && callsInArms S as
end

theorem callsInList_mem {S : Nat → Bool} :
    ∀ {as : List Expr}, callsInList S as = true → ∀ a ∈ as, callsIn S a = true
  | [], _, _, h => by simp at h
  | e :: es, h, a, ha => by
    simp only [callsInList, Bool.and_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h.1
    · exact callsInList_mem h.2 a ha

theorem callsInArms_get {S : Nat → Bool} :
    ∀ {arms : List (Nat × Expr)} {t k : Nat} {b : Expr}, callsInArms S arms = true →
      arms[t]? = some (k, b) → callsIn S b = true
  | [], _, _, _, _, h => by simp at h
  | (j, e) :: as, 0, k, b, h, hg => by
    simp only [callsInArms, Bool.and_eq_true] at h
    simp at hg; obtain ⟨_, rfl⟩ := hg; exact h.1
  | (j, e) :: as, t + 1, k, b, h, hg => by
    simp only [callsInArms, Bool.and_eq_true] at h
    simp at hg; exact callsInArms_get h.2 hg

theorem mapOpt_to_EvalList_on {n : Nat} {P Q : Prog} {ρ : Env} {S : Nat → Bool}
    (ih : ∀ e v, callsIn S e = true → ev n P ρ e = some v → Eval Q ρ e v) :
    ∀ {as : List Expr} {vs : List Val}, callsInList S as = true →
      mapOpt (ev n P ρ) as = some vs → EvalList Q ρ as vs
  | [], vs, _, h => by rw [mapOpt_nil_inv h]; exact EvalList_nil Q ρ
  | a :: as, zs, hc, h => by
    simp only [callsInList, Bool.and_eq_true] at hc
    obtain ⟨v, vs, rfl, hv, hvs⟩ := mapOpt_cons_inv h
    exact EvalList_cons (ih a v hc.1 hv) (mapOpt_to_EvalList_on ih hc.2 hvs)

/-- Evaluation of code that only calls functions in `S` transfers from `P` to
`Q` when `Q` has the same functions as `P` on `S` and those functions are
themselves call-closed in `S`. -/
theorem simulate_on {P Q : Prog} (S : Nat → Bool)
    (hS : ∀ (i : Nat) (fn : Fn), S i = true → P.fns[i]? = some fn →
      Q.fns[i]? = some fn ∧ callsIn S fn.body = true) :
    ∀ {ρ : Env} {e : Expr} {v : Val}, callsIn S e = true → Eval P ρ e v → Eval Q ρ e v := by
  suffices H : ∀ n ρ e v, callsIn S e = true → ev n P ρ e = some v → Eval Q ρ e v by
    rintro ρ e v hc ⟨n, hn⟩; exact H n ρ e v hc hn
  intro n
  induction n with
  | zero => intro ρ e v _ h; simp [ev_zero] at h
  | succ n ih =>
    intro ρ e v hc h
    cases e with
    | var i => exact Eval_var.mpr h
    | u32 k => exact ⟨n + 1, h⟩
    | nat k => exact ⟨n + 1, h⟩
    | prim p as =>
      simp only [callsIn] at hc
      rw [ev_prim] at h
      cases hvs : mapOpt (ev n P ρ) as with
      | none => simp [hvs] at h
      | some vs =>
        simp only [hvs] at h
        exact Eval_prim.mpr ⟨vs, mapOpt_to_EvalList_on (ih ρ) hc hvs, h⟩
    | ctr a t as =>
      simp only [callsIn] at hc
      rw [ev_ctr] at h
      cases hvs : mapOpt (ev n P ρ) as with
      | none => simp [hvs] at h
      | some vs =>
        simp only [hvs] at h
        exact Eval_ctr.mpr ⟨vs, mapOpt_to_EvalList_on (ih ρ) hc hvs, (Option.some.inj h).symm⟩
    | call f as =>
      simp only [callsIn, Bool.and_eq_true] at hc
      rw [ev_call] at h
      cases hvs : mapOpt (ev n P ρ) as with
      | none => simp [hvs] at h
      | some vs =>
        simp only [hvs] at h
        cases hf : P.fns[f]? with
        | none => simp [hf] at h
        | some fp =>
          simp only [hf] at h
          by_cases hl : vs.length = fp.params.length
          · simp only [hl, if_true] at h
            obtain ⟨hq, hcb⟩ := hS f fp hc.1 hf
            exact Eval_call.mpr ⟨vs, fp, mapOpt_to_EvalList_on (ih ρ) hc.2 hvs, hq, hl,
              ih _ _ _ hcb h⟩
          · simp [hl] at h
    | let_ e₁ b =>
      simp only [callsIn, Bool.and_eq_true] at hc
      rw [ev_let] at h
      cases hw : ev n P ρ e₁ with
      | none => simp [hw] at h
      | some w =>
        simp only [hw] at h
        exact Eval_let.mpr ⟨w, ih _ _ _ hc.1 hw, ih _ _ _ hc.2 h⟩
    | par e₁ e₂ b =>
      simp only [callsIn, Bool.and_eq_true] at hc
      rw [ev_par] at h
      cases hw₁ : ev n P ρ e₁ with
      | none => simp [hw₁] at h
      | some w₁ =>
        simp only [hw₁] at h
        cases hw₂ : ev n P ρ e₂ with
        | none => simp [hw₂] at h
        | some w₂ =>
          simp only [hw₂] at h
          exact Eval_par.mpr ⟨w₁, w₂, ih _ _ _ hc.1.1 hw₁, ih _ _ _ hc.1.2 hw₂, ih _ _ _ hc.2 h⟩
    | mat a s arms =>
      simp only [callsIn, Bool.and_eq_true] at hc
      rw [ev_mat] at h
      cases hs : ev n P ρ s with
      | none => simp [hs] at h
      | some sv =>
        cases sv with
        | u32 _ => simp [hs] at h
        | nat _ => simp [hs] at h
        | ctr t fs =>
          simp only [hs] at h
          cases harm : arms[t]? with
          | none => simp [harm] at h
          | some kb =>
            obtain ⟨k, body⟩ := kb
            simp only [harm] at h
            by_cases hl : fs.length = k
            · simp only [hl, if_true] at h
              exact Eval_mat.mpr ⟨t, fs, k, body, ih _ _ _ hc.1 hs, harm, hl,
                ih _ _ _ (callsInArms_get hc.2 harm) h⟩
            · simp [hl] at h
    | natCase s z k =>
      simp only [callsIn, Bool.and_eq_true] at hc
      rw [ev_natCase] at h
      cases hs : ev n P ρ s with
      | none => simp [hs] at h
      | some sv =>
        cases sv with
        | u32 _ => simp [hs] at h
        | ctr _ _ => simp [hs] at h
        | nat m =>
          cases m with
          | zero =>
            simp only [hs] at h
            exact Eval_natCase.mpr (Or.inl ⟨ih _ _ _ hc.1.1 hs, ih _ _ _ hc.1.2 h⟩)
          | succ m =>
            simp only [hs] at h
            exact Eval_natCase.mpr (Or.inr ⟨m, ih _ _ _ hc.1.1 hs, ih _ _ _ hc.2 h⟩)

/-- Executable agreement check: on `S` (below `bound`), `P` and `Q` have equal
functions and those are call-closed in `S`; `S` holds nowhere at or above `bound`. -/
def agreeOnB (S : Nat → Bool) (bound : Nat) (P Q : Prog) : Bool :=
  (List.range bound).all (fun i =>
    !S i || match P.fns[i]?, Q.fns[i]? with
      | some f, some g => Fn.beq f g && callsIn S f.body
      | _, _ => false)

theorem agreeOnB_sound {S : Nat → Bool} {bound : Nat} {P Q : Prog}
    (hb : ∀ i, bound ≤ i → S i = false) (h : agreeOnB S bound P Q = true) :
    ∀ (i : Nat) (fn : Fn), S i = true → P.fns[i]? = some fn →
      Q.fns[i]? = some fn ∧ callsIn S fn.body = true := by
  intro i fn hi hp
  have hib : i < bound := by
    rcases Nat.lt_or_ge i bound with h' | h'
    · exact h'
    · rw [hb i h'] at hi; cases hi
  unfold agreeOnB at h
  have := List.all_eq_true.mp h i (List.mem_range.mpr hib)
  rw [hi, hp] at this
  simp only [Bool.not_true, Bool.false_or] at this
  cases hq : Q.fns[i]? with
  | none => rw [hq] at this; simp at this
  | some g =>
    rw [hq] at this
    simp only [Bool.and_eq_true] at this
    rw [Fn.eq_of_beq this.1]
    exact ⟨rfl, Fn.eq_of_beq this.1 ▸ this.2⟩

end BendVerify
