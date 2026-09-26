/-
BendVerify.Simulate — whole-program simulation.

If every function body of `P`, evaluated in `Q`, implies the corresponding
body of `Q` (evaluated in `Q`), then every terminating evaluation in `P` is a
terminating evaluation (to the same value) in `Q`. Applied in both directions
this turns *local* facts about changed function bodies into equivalence of
whole programs, including through recursion. This is how pre-proven rewrite
rules are shown sound once and for all.
-/
import BendVerify.Equiv

namespace BendVerify

theorem mapOpt_to_EvalList {n : Nat} {P Q : Prog} {ρ : Env}
    (ih : ∀ e v, ev n P ρ e = some v → Eval Q ρ e v) :
    ∀ {as : List Expr} {vs : List Val}, mapOpt (ev n P ρ) as = some vs → EvalList Q ρ as vs
  | [], vs, h => by rw [mapOpt_nil_inv h]; exact EvalList_nil Q ρ
  | a :: as, zs, h => by
    obtain ⟨v, vs, rfl, hv, hvs⟩ := mapOpt_cons_inv h
    exact EvalList_cons (ih a v hv) (mapOpt_to_EvalList ih hvs)

/-- One-directional simulation of `P` by `Q`. -/
theorem simulate {P Q : Prog}
    (hfn : ∀ (i : Nat) (fp : Fn), P.fns[i]? = some fp → ∃ fq : Fn, Q.fns[i]? = some fq ∧
      fq.params.length = fp.params.length ∧ ∀ ρ v, Eval Q ρ fp.body v → Eval Q ρ fq.body v) :
    ∀ {ρ : Env} {e : Expr} {v : Val}, Eval P ρ e v → Eval Q ρ e v := by
  suffices H : ∀ n ρ e v, ev n P ρ e = some v → Eval Q ρ e v by
    rintro ρ e v ⟨n, hn⟩; exact H n ρ e v hn
  intro n
  induction n with
  | zero => intro ρ e v h; simp [ev_zero] at h
  | succ n ih =>
    intro ρ e v h
    cases e with
    | var i => exact Eval_var.mpr h
    | u32 k => exact ⟨n + 1, h⟩
    | nat k => exact ⟨n + 1, h⟩
    | prim p as =>
      rw [ev_prim] at h
      cases hvs : mapOpt (ev n P ρ) as with
      | none => simp [hvs] at h
      | some vs =>
        simp only [hvs] at h
        exact Eval_prim.mpr ⟨vs, mapOpt_to_EvalList (ih ρ) hvs, h⟩
    | ctr a t as =>
      rw [ev_ctr] at h
      cases hvs : mapOpt (ev n P ρ) as with
      | none => simp [hvs] at h
      | some vs =>
        simp only [hvs] at h
        exact Eval_ctr.mpr ⟨vs, mapOpt_to_EvalList (ih ρ) hvs, (Option.some.inj h).symm⟩
    | call f as =>
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
            obtain ⟨fq, hq, hql, hbody⟩ := hfn f fp hf
            exact Eval_call.mpr ⟨vs, fq, mapOpt_to_EvalList (ih ρ) hvs, hq, by omega,
              hbody _ _ (ih _ _ _ h)⟩
          · simp [hl] at h
    | let_ e₁ b =>
      rw [ev_let] at h
      cases hw : ev n P ρ e₁ with
      | none => simp [hw] at h
      | some w =>
        simp only [hw] at h
        exact Eval_let.mpr ⟨w, ih _ _ _ hw, ih _ _ _ h⟩
    | par e₁ e₂ b =>
      rw [ev_par] at h
      cases hw₁ : ev n P ρ e₁ with
      | none => simp [hw₁] at h
      | some w₁ =>
        simp only [hw₁] at h
        cases hw₂ : ev n P ρ e₂ with
        | none => simp [hw₂] at h
        | some w₂ =>
          simp only [hw₂] at h
          exact Eval_par.mpr ⟨w₁, w₂, ih _ _ _ hw₁, ih _ _ _ hw₂, ih _ _ _ h⟩
    | mat a s arms =>
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
              exact Eval_mat.mpr ⟨t, fs, k, body, ih _ _ _ hs, harm, hl, ih _ _ _ h⟩
            · simp [hl] at h
    | natCase s z k =>
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
            exact Eval_natCase.mpr (Or.inl ⟨ih _ _ _ hs, ih _ _ _ h⟩)
          | succ m =>
            simp only [hs] at h
            exact Eval_natCase.mpr (Or.inr ⟨m, ih _ _ _ hs, ih _ _ _ h⟩)

/-! ## Programs of the same shape -/

/-- Name, parameter types and return type of every function. -/
def Prog.sigs (P : Prog) : List (String × List Ty × Ty) :=
  P.fns.map fun f => (f.name, f.params, f.ret)

theorem findFn_go_index {name : String} :
    ∀ {l₁ l₂ : List Fn} {j : Nat},
      l₁.map (fun f => (f.name, f.params, f.ret)) = l₂.map (fun f => (f.name, f.params, f.ret)) →
      ∀ {i : Nat} {f₁ : Fn}, Prog.findFn.go name l₁ j = some (i, f₁) →
        ∃ f₂, Prog.findFn.go name l₂ j = some (i, f₂) ∧ f₂.name = f₁.name ∧
          f₂.params = f₁.params ∧ f₂.ret = f₁.ret
  | [], [], _, _, _, _, h => by simp [Prog.findFn.go] at h
  | [], _ :: _, _, hs, _, _, _ => by simp at hs
  | _ :: _, [], _, hs, _, _, _ => by simp at hs
  | g₁ :: gs₁, g₂ :: gs₂, j, hs, i, f₁, h => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at hs
    obtain ⟨⟨hn, hp, hr⟩, hs⟩ := hs
    simp only [Prog.findFn.go] at h ⊢
    by_cases hg : g₁.name = name
    · simp only [hg, if_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨g₂, by simp [← hn, hg], hn.symm, hp.symm, hr.symm⟩
    · simp only [hg, if_false] at h
      have hg2 : ¬ g₂.name = name := by rw [← hn]; exact hg
      simp only [hg2, if_false]
      exact findFn_go_index hs h

theorem findFn_same_shape {P Q : Prog} (hs : P.sigs = Q.sigs) {name : String} {i : Nat} {f₁ : Fn}
    (h : P.findFn name = some (i, f₁)) :
    ∃ f₂, Q.findFn name = some (i, f₂) ∧ f₂.name = f₁.name ∧ f₂.params = f₁.params ∧
      f₂.ret = f₁.ret :=
  findFn_go_index hs h

theorem wfEntry_same_shape {c : Ctx} {P Q : Prog} (hs : P.sigs = Q.sigs) (ha : P.adts = Q.adts)
    (h : WfEntry c P) : WfEntry c Q := by
  obtain ⟨hp, i, fn, hf, hpar, hret⟩ := h
  obtain ⟨f₂, hf₂, _, hp₂, hr₂⟩ := findFn_same_shape hs hf
  exact ⟨ha ▸ hp, i, f₂, hf₂, hp₂.trans hpar, hr₂.trans hret⟩

theorem sigs_getElem {P Q : Prog} (hs : P.sigs = Q.sigs) {i : Nat} {fp : Fn}
    (h : P.fns[i]? = some fp) : ∃ fq, Q.fns[i]? = some fq ∧ fq.name = fp.name ∧
      fq.params = fp.params ∧ fq.ret = fp.ret := by
  have hl : P.fns.length = Q.fns.length := by
    have := congrArg List.length hs; simpa [Prog.sigs] using this
  have hi : i < P.fns.length := by
    rcases Nat.lt_or_ge i P.fns.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; simp at h
  have hq : i < Q.fns.length := hl ▸ hi
  refine ⟨Q.fns[i], List.getElem?_eq_getElem hq, ?_⟩
  have e1 : P.fns[i] = fp := by rw [List.getElem?_eq_getElem hi] at h; exact Option.some.inj h
  have hx := congrArg (fun l => l[i]?) hs
  simp only [Prog.sigs, List.getElem?_map, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hq, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hx
  rw [e1] at hx
  exact ⟨hx.1.symm, hx.2.1.symm, hx.2.2.symm⟩

/-- **Body simulation ⇒ equivalence.** Two programs with the same ADT table
and the same function signatures, whose corresponding bodies simulate each
other in both directions, are equivalent for every context. -/
theorem equiv_of_bodies {c : Ctx} {P Q : Prog} (ha : P.adts = Q.adts) (hs : P.sigs = Q.sigs)
    (hPQ : ∀ (i : Nat) (fp fq : Fn), P.fns[i]? = some fp → Q.fns[i]? = some fq →
      ∀ ρ v, Eval Q ρ fp.body v → Eval Q ρ fq.body v)
    (hQP : ∀ (i : Nat) (fp fq : Fn), P.fns[i]? = some fp → Q.fns[i]? = some fq →
      ∀ ρ v, Eval P ρ fq.body v → Eval P ρ fp.body v)
    (hw : WfEntry c P) : Equiv c P Q := by
  have simPQ : ∀ {ρ e v}, Eval P ρ e v → Eval Q ρ e v := simulate (fun i fp hp => by
    obtain ⟨fq, hq, _, hpar, _⟩ := sigs_getElem hs hp
    exact ⟨fq, hq, by rw [hpar], hPQ i fp fq hp hq⟩)
  have simQP : ∀ {ρ e v}, Eval Q ρ e v → Eval P ρ e v := simulate (fun i fq hq => by
    obtain ⟨fp, hp, _, hpar, _⟩ := sigs_getElem hs.symm hq
    exact ⟨fp, hp, by rw [hpar], hQP i fp fq hp hq⟩)
  refine ⟨hw, wfEntry_same_shape hs ha hw, fun args _ v => ?_⟩
  constructor
  · intro h
    obtain ⟨i, fp, hf, hp, hl, he⟩ := Run_iff.mp h
    obtain ⟨fq, hq, _, hpar, _⟩ := sigs_getElem hs hp
    obtain ⟨f₂, hf₂, _, _, _⟩ := findFn_same_shape hs hf
    have hfq := Run_iff.findFn_get hf₂
    rw [hq] at hfq; cases hfq
    exact Run_iff.mpr ⟨i, fq, hf₂, hq, by rw [hpar]; exact hl, hPQ i fp fq hp hq _ _ (simPQ he)⟩
  · intro h
    obtain ⟨i, fq, hf, hq, hl, he⟩ := Run_iff.mp h
    obtain ⟨fp, hp, _, hpar, _⟩ := sigs_getElem hs.symm hq
    obtain ⟨f₂, hf₂, _, _, _⟩ := findFn_same_shape hs.symm hf
    have hfp := Run_iff.findFn_get hf₂
    rw [hp] at hfp; cases hfp
    exact Run_iff.mpr ⟨i, fp, hf₂, hp, by rw [hpar]; exact hl, hQP i fp fq hp hq _ _ (simQP he)⟩

end BendVerify
