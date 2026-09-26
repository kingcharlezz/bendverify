/-
Proof for the tree-radix deforestation step (competitor-written, UNTRUSTED).

The step turns
    run(n, x) = chk_out(chk(let a = gen(n, x) in to_arr(to_map(a), 0)))
into
    run(n, x) = chk_out(chk.to_arr(to_map.gen(n, x), 0))
where the two fused functions are new. The proof:
  1. characterises each involved IR function by symbolic evaluation;
  2. proves `to_map(gen(n,x)) ≃ to_map.gen(n,x)` by induction on n;
  3. proves `chk(to_arr(m,k)) ≃ chk.to_arr(m,k)` by induction on the trie m;
  4. transfers the old entry body from P_1 to P_2 (they agree on every
     function it can reach) and concludes `Equiv ctx P_1 P_2`.
The verifier does not trust any of this: the kernel re-checks the exported
terms, and the statement proved must be exactly the generated `goal_1`.
-/
import Contest.Obligation
open BendVerify Contest.Obligation.tree_radix

namespace Submission.TreeRadix

/-! ## The function bodies, stated literally (checked by `rfl`) -/

def genB : Expr := .natCase (.var 1) (.ctr 1 1 [.call 5 [.var 0]])
  (.par (.call 1 [.var 0, .prim .u32_shl [.var 1]])
        (.call 1 [.var 0, .prim .u32_inc [.prim .u32_shl [.var 1]]])
        (.ctr 1 2 [.var 1, .var 0]))
def tmB : Expr := .mat 1 (.var 0)
  [(0, .ctr 2 0 []), (1, .call 10 [.nat 24, .var 0, .u32 1, .ctr 2 1 []]),
   (2, .par (.call 6 [.var 1]) (.call 6 [.var 0]) (.call 11 [.var 1, .var 0]))]
def gmB : Expr := .natCase (.var 1) (.call 10 [.nat 24, .call 5 [.var 0], .u32 1, .ctr 2 1 []])
  (.par (.call 15 [.var 0, .prim .u32_shl [.var 1]])
        (.call 15 [.var 0, .prim .u32_inc [.prim .u32_shl [.var 1]]])
        (.call 11 [.var 1, .var 0]))
def taB : Expr := .mat 2 (.var 1)
  [(0, .ctr 1 0 []), (0, .ctr 1 1 [.var 0]),
   (2, .par (.call 7 [.var 1, .prim .u32_shl [.var 2]])
            (.call 7 [.var 0, .prim .u32_inc [.prim .u32_shl [.var 2]]])
            (.ctr 1 2 [.var 1, .var 0]))]
def ckB : Expr := .mat 1 (.var 0)
  [(0, .ctr 0 0 []), (1, .ctr 0 1 [.var 0, .var 0, .u32 1, .u32 1, .var 0]),
   (2, .par (.call 3 [.var 1]) (.call 3 [.var 0]) (.call 8 [.var 1, .var 0]))]
def tcB : Expr := .mat 2 (.var 1)
  [(0, .ctr 0 0 []), (0, .ctr 0 1 [.var 0, .var 0, .u32 1, .u32 1, .var 0]),
   (2, .par (.call 16 [.var 1, .prim .u32_shl [.var 2]])
            (.call 16 [.var 0, .prim .u32_inc [.prim .u32_shl [.var 2]]])
            (.call 8 [.var 1, .var 0]))]

theorem f1 : P_2.fns[1]? = some ⟨"gen", [.nat, .u32], .adt 1, genB⟩ := rfl
theorem f6 : P_2.fns[6]? = some ⟨"to_map", [.adt 1], .adt 2, tmB⟩ := rfl
theorem f15 : P_2.fns[15]? = some ⟨"to_map.gen", [.nat, .u32], .adt 2, gmB⟩ := rfl
theorem f7 : P_2.fns[7]? = some ⟨"to_arr", [.adt 2, .u32], .adt 1, taB⟩ := rfl
theorem f3 : P_2.fns[3]? = some ⟨"chk", [.adt 1], .adt 0, ckB⟩ := rfl
theorem f16 : P_2.fns[16]? = some ⟨"chk.to_arr", [.adt 2, .u32], .adt 0, tcB⟩ := rfl

theorem one32 : (1 : Nat) % M32 = 1 := rfl
theorem zero32 : (0 : Nat) % M32 = 0 := rfl

attribute [local simp] Eval_var Eval_u32 Eval_nat Eval_prim Eval_ctr Eval_call_App Eval_let
  Eval_par Eval_natCase_var Eval_mat_var exists_EvalList_cons exists_EvalList_nil one32 and_assoc

/-- Both recursive calls evaluate `shl x` separately; determinism merges them. -/
theorem reshape {S : Option Val} {I : Val → Option Val} {A B C : Val → Val → Prop} :
    (∃ w₁, (∃ v, S = some v ∧ A v w₁) ∧
      ∃ w₂, (∃ v, (∃ v₁, S = some v₁ ∧ I v₁ = some v) ∧ B v w₂) ∧ C w₁ w₂) ↔
    ∃ y₁ y₂ w₁ w₂, S = some y₁ ∧ I y₁ = some y₂ ∧ A y₁ w₁ ∧ B y₂ w₂ ∧ C w₁ w₂ := by
  constructor
  · rintro ⟨w₁, ⟨v, hS, hA⟩, w₂, ⟨u, ⟨v₁, hS', hI⟩, hB⟩, hC⟩
    rw [hS] at hS'; cases hS'
    exact ⟨v, u, w₁, w₂, hS, hI, hA, hB, hC⟩
  · rintro ⟨y₁, y₂, w₁, w₂, hS, hI, hA, hB, hC⟩
    exact ⟨w₁, ⟨y₁, hS, hA⟩, w₂, ⟨y₂, ⟨y₁, hS, hI⟩, hB⟩, hC⟩

abbrev SHL (x : Val) : Option Val := Prim.eval .u32_shl [x]
abbrev INC (x : Val) : Option Val := Prim.eval .u32_inc [x]

/-! ## gen / to_map / to_map.gen -/

theorem gen_zero (x a : Val) :
    App P_2 1 [.nat 0, x] a ↔ ∃ k, App P_2 5 [x] k ∧ a = .ctr 1 [k] := by
  rw [App_iff f1]; simp [genB]

theorem gen_succ (m : Nat) (x a : Val) : App P_2 1 [.nat (m + 1), x] a ↔
    ∃ y₁ y₂ l r, SHL x = some y₁ ∧ INC y₁ = some y₂ ∧
      App P_2 1 [.nat m, y₁] l ∧ App P_2 1 [.nat m, y₂] r ∧ a = .ctr 2 [l, r] := by
  have h : App P_2 1 [.nat (m + 1), x] a ↔
      ∃ w₁, (∃ v, SHL x = some v ∧ App P_2 1 [.nat m, v] w₁) ∧
        ∃ w₂, (∃ v, (∃ v₁, SHL x = some v₁ ∧ INC v₁ = some v) ∧ App P_2 1 [.nat m, v] w₂) ∧
          a = .ctr 2 [w₁, w₂] := by
    rw [App_iff f1]; simp [genB]
  exact h.trans reshape

theorem tm_single (k t : Val) :
    App P_2 6 [.ctr 1 [k]] t ↔ App P_2 10 [.nat 24, k, .u32 1, .ctr 1 []] t := by
  rw [App_iff f6]; simp [tmB]

theorem tm_concat (l r t : Val) : App P_2 6 [.ctr 2 [l, r]] t ↔
    ∃ tl, App P_2 6 [l] tl ∧ ∃ tr, App P_2 6 [r] tr ∧ App P_2 11 [tl, tr] t := by
  rw [App_iff f6]; simp [tmB]

theorem gm_zero (x t : Val) : App P_2 15 [.nat 0, x] t ↔
    ∃ k, App P_2 5 [x] k ∧ App P_2 10 [.nat 24, k, .u32 1, .ctr 1 []] t := by
  rw [App_iff f15]; simp [gmB]

theorem gm_succ (m : Nat) (x t : Val) : App P_2 15 [.nat (m + 1), x] t ↔
    ∃ y₁ y₂ tl tr, SHL x = some y₁ ∧ INC y₁ = some y₂ ∧
      App P_2 15 [.nat m, y₁] tl ∧ App P_2 15 [.nat m, y₂] tr ∧ App P_2 11 [tl, tr] t := by
  have h : App P_2 15 [.nat (m + 1), x] t ↔
      ∃ w₁, (∃ v, SHL x = some v ∧ App P_2 15 [.nat m, v] w₁) ∧
        ∃ w₂, (∃ v, (∃ v₁, SHL x = some v₁ ∧ INC v₁ = some v) ∧ App P_2 15 [.nat m, v] w₂) ∧
          App P_2 11 [w₁, w₂] t := by
    rw [App_iff f15]; simp [gmB]
  exact h.trans reshape

/-- **Fusion 1**: `to_map (gen n x)` and `to_map.gen n x` have the same results. -/
theorem fuse_map : ∀ (n : Nat) (x t : Val),
    (∃ a, App P_2 1 [.nat n, x] a ∧ App P_2 6 [a] t) ↔ App P_2 15 [.nat n, x] t := by
  intro n
  induction n with
  | zero =>
    intro x t
    rw [gm_zero]
    constructor
    · rintro ⟨a, ha, ht⟩
      obtain ⟨k, hk, rfl⟩ := (gen_zero x a).mp ha
      exact ⟨k, hk, (tm_single k t).mp ht⟩
    · rintro ⟨k, hk, ht⟩
      exact ⟨.ctr 1 [k], (gen_zero x _).mpr ⟨k, hk, rfl⟩, (tm_single k t).mpr ht⟩
  | succ m ih =>
    intro x t
    rw [gm_succ]
    constructor
    · rintro ⟨a, ha, ht⟩
      obtain ⟨y₁, y₂, l, r, h1, h2, hl, hr, rfl⟩ := (gen_succ m x a).mp ha
      obtain ⟨tl, htl, tr, htr, hm⟩ := (tm_concat l r t).mp ht
      exact ⟨y₁, y₂, tl, tr, h1, h2, (ih y₁ tl).mp ⟨l, hl, htl⟩, (ih y₂ tr).mp ⟨r, hr, htr⟩, hm⟩
    · rintro ⟨y₁, y₂, tl, tr, h1, h2, htl, htr, hm⟩
      obtain ⟨l, hl, htl'⟩ := (ih y₁ tl).mpr htl
      obtain ⟨r, hr, htr'⟩ := (ih y₂ tr).mpr htr
      exact ⟨.ctr 2 [l, r], (gen_succ m x _).mpr ⟨y₁, y₂, l, r, h1, h2, hl, hr, rfl⟩,
        (tm_concat l r t).mpr ⟨tl, htl', tr, htr', hm⟩⟩

/-- For a non-Nat first argument both sides are stuck. -/
theorem fuse_map' (d x t : Val) :
    (∃ a, App P_2 1 [d, x] a ∧ App P_2 6 [a] t) ↔ App P_2 15 [d, x] t := by
  cases d with
  | nat n => exact fuse_map n x t
  | u32 k =>
    constructor
    · rintro ⟨a, ha, _⟩; rw [App_iff f1] at ha; simp [genB] at ha
    · intro h; rw [App_iff f15] at h; simp [gmB] at h
  | ctr c fs =>
    constructor
    · rintro ⟨a, ha, _⟩; rw [App_iff f1] at ha; simp [genB] at ha
    · intro h; rw [App_iff f15] at h; simp [gmB] at h

/-! ## to_arr / chk / chk.to_arr -/

theorem ta_free (k a : Val) : App P_2 7 [.ctr 0 [], k] a ↔ a = .ctr 0 [] := by
  rw [App_iff f7]; simp [taB]
theorem ta_busy (k a : Val) : App P_2 7 [.ctr 1 [], k] a ↔ a = .ctr 1 [k] := by
  rw [App_iff f7]; simp [taB]
theorem ta_node (l r k a : Val) : App P_2 7 [.ctr 2 [l, r], k] a ↔
    ∃ y₁ y₂ la ra, SHL k = some y₁ ∧ INC y₁ = some y₂ ∧
      App P_2 7 [l, y₁] la ∧ App P_2 7 [r, y₂] ra ∧ a = .ctr 2 [la, ra] := by
  have h : App P_2 7 [.ctr 2 [l, r], k] a ↔
      ∃ w₁, (∃ v, SHL k = some v ∧ App P_2 7 [l, v] w₁) ∧
        ∃ w₂, (∃ v, (∃ v₁, SHL k = some v₁ ∧ INC v₁ = some v) ∧ App P_2 7 [r, v] w₂) ∧
          a = .ctr 2 [w₁, w₂] := by
    rw [App_iff f7]; simp [taB]
  exact h.trans reshape

theorem tc_free (k c : Val) : App P_2 16 [.ctr 0 [], k] c ↔ c = .ctr 0 [] := by
  rw [App_iff f16]; simp [tcB]
theorem tc_busy (k c : Val) : App P_2 16 [.ctr 1 [], k] c ↔ c = .ctr 1 [k, k, .u32 1, .u32 1, k] := by
  rw [App_iff f16]; simp [tcB]
theorem tc_node (l r k c : Val) : App P_2 16 [.ctr 2 [l, r], k] c ↔
    ∃ y₁ y₂ ca cb, SHL k = some y₁ ∧ INC y₁ = some y₂ ∧
      App P_2 16 [l, y₁] ca ∧ App P_2 16 [r, y₂] cb ∧ App P_2 8 [ca, cb] c := by
  have h : App P_2 16 [.ctr 2 [l, r], k] c ↔
      ∃ w₁, (∃ v, SHL k = some v ∧ App P_2 16 [l, v] w₁) ∧
        ∃ w₂, (∃ v, (∃ v₁, SHL k = some v₁ ∧ INC v₁ = some v) ∧ App P_2 16 [r, v] w₂) ∧
          App P_2 8 [w₁, w₂] c := by
    rw [App_iff f16]; simp [tcB]
  exact h.trans reshape

theorem ck_emp (c : Val) : App P_2 3 [.ctr 0 []] c ↔ c = .ctr 0 [] := by
  rw [App_iff f3]; simp [ckB]
theorem ck_single (k c : Val) : App P_2 3 [.ctr 1 [k]] c ↔ c = .ctr 1 [k, k, .u32 1, .u32 1, k] := by
  rw [App_iff f3]; simp [ckB]
theorem ck_concat (la ra c : Val) : App P_2 3 [.ctr 2 [la, ra]] c ↔
    ∃ ca, App P_2 3 [la] ca ∧ ∃ cb, App P_2 3 [ra] cb ∧ App P_2 8 [ca, cb] c := by
  rw [App_iff f3]; simp [ckB]

/-- Shapes that are not a well-formed trie node make both functions stuck. -/
theorem bad_shape (m k a c : Val) (h0 : m ≠ .ctr 0 []) (h1 : m ≠ .ctr 1 [])
    (h2 : ∀ l r, m ≠ .ctr 2 [l, r]) : ¬ App P_2 7 [m, k] a ∧ ¬ App P_2 16 [m, k] c := by
  constructor
  · intro h
    rw [App_iff f7] at h; simp [taB] at h
    obtain ⟨t, fs, rfl, body, harm, _⟩ := h
    match t, fs, harm with
    | 0, [], _ => exact h0 rfl
    | 1, [], _ => exact h1 rfl
    | 2, [l, r], _ => exact h2 l r rfl
    | 0, _ :: _, harm => simp at harm
    | 1, _ :: _, harm => simp at harm
    | 2, [], harm => simp at harm
    | 2, [_], harm => simp at harm
    | 2, _ :: _ :: _ :: _, harm => simp at harm
    | _ + 3, _, harm => simp at harm
  · intro h
    rw [App_iff f16] at h; simp [tcB] at h
    obtain ⟨t, fs, rfl, body, harm, _⟩ := h
    match t, fs, harm with
    | 0, [], _ => exact h0 rfl
    | 1, [], _ => exact h1 rfl
    | 2, [l, r], _ => exact h2 l r rfl
    | 0, _ :: _, harm => simp at harm
    | 1, _ :: _, harm => simp at harm
    | 2, [], harm => simp at harm
    | 2, [_], harm => simp at harm
    | 2, _ :: _ :: _ :: _, harm => simp at harm
    | _ + 3, _, harm => simp at harm

/-- **Fusion 2**: `chk (to_arr m k)` and `chk.to_arr m k` have the same results. -/
theorem fuse_chk (m : Val) : ∀ (k c : Val),
    (∃ a, App P_2 7 [m, k] a ∧ App P_2 3 [a] c) ↔ App P_2 16 [m, k] c := by
  intro k c
  by_cases h0 : m = .ctr 0 []
  · subst h0
    rw [tc_free]
    constructor
    · rintro ⟨a, ha, hc⟩; rw [ta_free] at ha; subst ha; exact (ck_emp c).mp hc
    · rintro rfl; exact ⟨.ctr 0 [], (ta_free k _).mpr rfl, (ck_emp _).mpr rfl⟩
  by_cases h1 : m = .ctr 1 []
  · subst h1
    rw [tc_busy]
    constructor
    · rintro ⟨a, ha, hc⟩; rw [ta_busy] at ha; subst ha; exact (ck_single k c).mp hc
    · rintro rfl; exact ⟨.ctr 1 [k], (ta_busy k _).mpr rfl, (ck_single k _).mpr rfl⟩
  by_cases h2 : ∃ l r, m = .ctr 2 [l, r]
  · obtain ⟨l, r, hm⟩ := h2
    have ihl := fuse_chk l
    have ihr := fuse_chk r
    subst hm
    rw [tc_node]
    constructor
    · rintro ⟨a, ha, hc⟩
      obtain ⟨y₁, y₂, la, ra, e1, e2, hla, hra, rfl⟩ := (ta_node l r k a).mp ha
      obtain ⟨ca, hca, cb, hcb, hj⟩ := (ck_concat la ra c).mp hc
      exact ⟨y₁, y₂, ca, cb, e1, e2, (ihl y₁ ca).mp ⟨la, hla, hca⟩, (ihr y₂ cb).mp ⟨ra, hra, hcb⟩, hj⟩
    · rintro ⟨y₁, y₂, ca, cb, e1, e2, hca, hcb, hj⟩
      obtain ⟨la, hla, hca'⟩ := (ihl y₁ ca).mpr hca
      obtain ⟨ra, hra, hcb'⟩ := (ihr y₂ cb).mpr hcb
      exact ⟨.ctr 2 [la, ra], (ta_node l r k _).mpr ⟨y₁, y₂, la, ra, e1, e2, hla, hra, rfl⟩,
        (ck_concat la ra c).mpr ⟨ca, hca', cb, hcb', hj⟩⟩
  · have hb := bad_shape m k
    have h2' : ∀ l r, m ≠ .ctr 2 [l, r] := fun l r e => h2 ⟨l, r, e⟩
    constructor
    · rintro ⟨a, ha, _⟩; exact ((hb a c h0 h1 h2').1 ha).elim
    · intro h; exact ((hb (.ctr 0 []) c h0 h1 h2').2 h).elim
termination_by sizeOf m
decreasing_by all_goals (subst hm; simp; omega)

/-! ## The entry -/

def run1 : Expr :=
  .call 4 [.call 3 [.let_ (.call 1 [.var 1, .var 0]) (.call 7 [.call 6 [.var 0], .u32 0])]]
def run2 : Expr := .call 4 [.call 16 [.call 15 [.var 1, .var 0], .u32 0]]

theorem r1 : P_1.findFn "run" = some (0, ⟨"run", [.nat, .u32], .u32, run1⟩) := rfl
theorem r2 : P_2.findFn "run" = some (0, ⟨"run", [.nat, .u32], .u32, run2⟩) := rfl
theorem r1' : P_1.fns[0]? = some ⟨"run", [.nat, .u32], .u32, run1⟩ := rfl
theorem r2' : P_2.fns[0]? = some ⟨"run", [.nat, .u32], .u32, run2⟩ := rfl

/-- In P_2, the old entry body and the fused one have the same results. -/
theorem fuse_run (d x v : Val) : Eval P_2 [x, d] run1 v ↔ Eval P_2 [x, d] run2 v := by
  simp only [run1, run2, Eval_call_App, exists_EvalList_cons, exists_EvalList_nil, Eval_let,
    Eval_var, Eval_u32, zero32]
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
    exists_eq_left', exists_eq_left]
  constructor
  · rintro ⟨c, ⟨a2, ⟨a1, h1, t, h6, h7⟩, h3⟩, h4⟩
    exact ⟨c, ⟨t, (fuse_map' d x t).mp ⟨a1, h1, h6⟩, (fuse_chk t (.u32 0) c).mp ⟨a2, h7, h3⟩⟩, h4⟩
  · rintro ⟨c, ⟨t, h15, h16⟩, h4⟩
    obtain ⟨a1, h1, h6⟩ := (fuse_map' d x t).mpr h15
    obtain ⟨a2, h7, h3⟩ := (fuse_chk t (.u32 0) c).mpr h16
    exact ⟨c, ⟨a2, ⟨a1, h1, t, h6, h7⟩, h3⟩, h4⟩

/-- Functions 1..14 are identical in P_1 and P_2 and only call each other. -/
def S : Nat → Bool := fun i => decide (1 ≤ i ∧ i ≤ 14)
theorem S_bound : ∀ i, 15 ≤ i → S i = false := by intro i h; simp [S]; omega
theorem agree12 : agreeOnB S 15 P_1 P_2 = true := by decide
theorem agree21 : agreeOnB S 15 P_2 P_1 = true := by decide
theorem closed1 : callsIn S run1 = true := by decide

theorem transfer (ρ : Env) (v : Val) : Eval P_1 ρ run1 v ↔ Eval P_2 ρ run1 v :=
  ⟨simulate_on S (agreeOnB_sound S_bound agree12) closed1,
   simulate_on S (agreeOnB_sound S_bound agree21) closed1⟩

theorem step : Equiv ctx P_1 P_2 := by
  refine ⟨wfEntryB_sound (by decide), wfEntryB_sound (by decide), ?_⟩
  intro args _ v
  have he : ctx.entry = "run" := rfl
  rw [Run_iff, Run_iff, he]
  constructor
  · rintro ⟨i, fn, hf, hfn, hl, he⟩
    rw [r1] at hf; simp only [Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    match args, hl with
    | [d, x], _ =>
      refine ⟨0, _, r2, r2', rfl, ?_⟩
      exact (fuse_run d x v).mp ((transfer _ v).mp he)
  · rintro ⟨i, fn, hf, hfn, hl, he⟩
    rw [r2] at hf; simp only [Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    match args, hl with
    | [d, x], _ =>
      refine ⟨0, _, r1, r1', rfl, ?_⟩
      exact (transfer _ v).mpr ((fuse_run d x v).mpr he)

/-- The lemma step's goal, exactly as generated by the verifier (the stamp is
filled in by elaboration from the goal's own statement). -/
theorem fusion : goal_1 := ⟨Stamp.mk _, step⟩

end Submission.TreeRadix
