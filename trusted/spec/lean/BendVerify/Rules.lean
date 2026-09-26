/-
BendVerify.Rules — the pre-proven rewrite-rule library (competition v1).

A *step* names a function, a path inside its body and a rule. `applyStep`
is an executable checker: it recomputes the rewritten program itself (a
competitor only says *where* a rule applies) and returns `none` whenever the
rule does not apply. `applyStep_sound` proves, once and for all, that any
program it returns is `Equiv`alent to its input. A certificate step using a
library rule is therefore checked by the kernel *evaluating*
`applyStep P s = some Q`, then instantiating `applyStep_sound`.

Rules:
* `fold b`  — a primitive applied to literals becomes its literal result
              (`b` = ADT id used for a Bool result, for the lowering only).
* `caseCtr` — `match` on an explicit constructor becomes lets + that arm.
* `natLit`  — `natCase` on a Nat literal selects its branch.
* `inline`  — a call to a (different) function becomes lets + its closed body.
-/
import BendVerify.Lift

namespace BendVerify

/-! ## Literals -/

def litVal : Expr → Option Val
  | .u32 k => some (.u32 (k % M32))
  | .nat k => some (.nat k)
  | .ctr _ t [] => some (.ctr t [])
  | _ => none

theorem litVal_Eval {Pg : Prog} {ρ : Env} {e : Expr} {v : Val} (h : litVal e = some v) :
    ∀ w, Eval Pg ρ e w ↔ w = v := by
  intro w
  cases e with
  | u32 k => simp only [litVal, Option.some.injEq] at h; subst h; exact Eval_u32
  | nat k => simp only [litVal, Option.some.injEq] at h; subst h; exact Eval_nat
  | ctr a t as =>
    cases as with
    | nil =>
      simp only [litVal, Option.some.injEq] at h; subst h
      rw [Eval_ctr]
      constructor
      · rintro ⟨vs, hvs, rfl⟩; rw [EvalList_nil_iff.mp hvs]
      · rintro rfl; exact ⟨[], EvalList_nil _ _, rfl⟩
    | cons _ _ => simp [litVal] at h
  | _ => simp [litVal] at h

theorem litVals_EvalList {Pg : Prog} {ρ : Env} :
    ∀ {as : List Expr} {vs : List Val}, mapOpt litVal as = some vs →
      ∀ ws, EvalList Pg ρ as ws ↔ ws = vs
  | [], vs, h, ws => by rw [mapOpt_nil_inv h]; exact EvalList_nil_iff
  | a :: as, zs, h, ws => by
    obtain ⟨v, vs, rfl, hv, hvs⟩ := mapOpt_cons_inv h
    rw [EvalList_cons_iff]
    constructor
    · rintro ⟨w, ws', rfl, hw, hws⟩
      rw [(litVal_Eval hv w).mp hw, (litVals_EvalList hvs ws').mp hws]
    · rintro rfl
      exact ⟨v, vs, rfl, (litVal_Eval hv v).mpr rfl, (litVals_EvalList hvs vs).mpr rfl⟩

def valLit (boolAdt : Nat) : Val → Option Expr
  | .u32 n => if n < M32 then some (.u32 n) else none
  | .nat n => some (.nat n)
  | .ctr t [] => some (.ctr boolAdt t [])
  | _ => none

theorem valLit_Eval {Pg : Prog} {ρ : Env} {b : Nat} {v : Val} {e : Expr}
    (h : valLit b v = some e) : ∀ w, Eval Pg ρ e w ↔ w = v := by
  intro w
  cases v with
  | u32 n =>
    simp only [valLit] at h
    split at h
    · rename_i hn
      simp only [Option.some.injEq] at h; subst h
      rw [Eval_u32, Nat.mod_eq_of_lt hn]
    · simp at h
  | nat n => simp only [valLit, Option.some.injEq] at h; subst h; exact Eval_nat
  | ctr t fs =>
    cases fs with
    | nil =>
      simp only [valLit, Option.some.injEq] at h; subst h
      exact litVal_Eval (e := .ctr b t []) rfl w
    | cons _ _ => simp [valLit] at h

/-! ## Rules -/

inductive Rule where
  | fold (boolAdt : Nat)
  | caseCtr
  | natLit
  | inline
  deriving Repr, DecidableEq, Inhabited

/-- The local rewrite performed by a rule at one expression; `self` is the
function being rewritten (a function may not be inlined into itself). -/
def Rule.rewrite (P : Prog) (self : Nat) : Rule → Expr → Option Expr
  | .fold b, .prim p as =>
    match mapOpt litVal as with
    | none => none
    | some vs =>
      match p.eval vs with
      | none => none
      | some r => valLit b r
  | .caseCtr, .mat _ (.ctr _ t as) arms =>
    match arms[t]? with
    | some (k, body) => if as.length = k then some (letsSeq as body) else none
    | none => none
  | .natLit, .natCase (.nat 0) z _ => some z
  | .natLit, .natCase (.nat (m + 1)) _ s => some (.let_ (.nat m) s)
  | .inline, .call f as =>
    if f = self then none else
    match P.fns[f]? with
    | some fn =>
      if as.length = fn.params.length ∧ closedB fn.params.length fn.body = true
      then some (letsSeq as fn.body) else none
    | none => none
  | _, _ => none

/-- `Pg` agrees with `P` on every function except `self`. -/
def Agree (P Pg : Prog) (self : Nat) : Prop := ∀ f, f ≠ self → Pg.fns[f]? = P.fns[f]?

/-- Expressions related by `g` are interchangeable in `Pg`. -/
def LocalEq (Pg : Prog) (g : Expr → Option Expr) : Prop :=
  ∀ x x', g x = some x' → ∀ ρ v, Eval Pg ρ x v ↔ Eval Pg ρ x' v

/-- **Local soundness of every library rule.** -/
theorem Rule.rewrite_sound {P Pg : Prog} {self : Nat} (hag : Agree P Pg self) (r : Rule) :
    LocalEq Pg (r.rewrite P self) := by
  intro e e' h ρ v
  cases r with
  | fold b =>
    cases e with
    | prim p as =>
      simp only [Rule.rewrite] at h
      cases hvs : mapOpt litVal as with
      | none => simp [hvs] at h
      | some vs =>
        simp only [hvs] at h
        cases hr : p.eval vs with
        | none => simp [hr] at h
        | some r =>
          simp only [hr] at h
          rw [Eval_prim, valLit_Eval h v]
          constructor
          · rintro ⟨ws, hws, hp⟩
            rw [(litVals_EvalList hvs ws).mp hws, hr] at hp; exact (Option.some.inj hp).symm
          · rintro rfl; exact ⟨vs, (litVals_EvalList hvs vs).mpr rfl, hr⟩
    | _ => simp [Rule.rewrite] at h
  | caseCtr =>
    cases e with
    | mat a s arms =>
      cases s with
      | ctr a' t as =>
        simp only [Rule.rewrite] at h
        cases harm : arms[t]? with
        | none => simp [harm] at h
        | some kb =>
          obtain ⟨k, body⟩ := kb
          simp only [harm] at h
          by_cases hk : as.length = k
          · simp only [hk, if_true, Option.some.injEq] at h
            subst h
            rw [Eval_mat, Eval_letsSeq]
            constructor
            · rintro ⟨t', fs, k', body', hs, harm', hl, hb⟩
              obtain ⟨vs, hvs, heq⟩ := Eval_ctr.mp hs
              simp only [Val.ctr.injEq] at heq
              obtain ⟨rfl, rfl⟩ := heq
              exact ⟨fs, hvs, by rw [harm] at harm'; cases harm'; exact hb⟩
            · rintro ⟨vs, hvs, hb⟩
              obtain ⟨n, hn⟩ := hvs
              refine ⟨t, vs, k, body, Eval_ctr.mpr ⟨vs, ⟨n, hn⟩, rfl⟩, harm, ?_, hb⟩
              rw [mapOpt_length hn, hk]
          · simp [hk] at h
      | _ => simp [Rule.rewrite] at h
    | _ => simp [Rule.rewrite] at h
  | natLit =>
    cases e with
    | natCase s z k =>
      cases s with
      | nat m =>
        cases m with
        | zero =>
          simp only [Rule.rewrite, Option.some.injEq] at h; subst h
          rw [Eval_natCase]
          constructor
          · rintro (⟨_, hz⟩ | ⟨m, hs, _⟩)
            · exact hz
            · simp [Eval_nat] at hs
          · intro hz; exact Or.inl ⟨Eval_nat.mpr rfl, hz⟩
        | succ m =>
          simp only [Rule.rewrite, Option.some.injEq] at h; subst h
          rw [Eval_natCase, Eval_let]
          constructor
          · rintro (⟨hs, _⟩ | ⟨m', hs, hk⟩)
            · simp [Eval_nat] at hs
            · simp only [Eval_nat, Val.nat.injEq] at hs
              have : m' = m := by omega
              subst this
              exact ⟨.nat m', Eval_nat.mpr rfl, hk⟩
          · rintro ⟨w, hw, hk⟩
            rw [Eval_nat] at hw; subst hw
            exact Or.inr ⟨m, Eval_nat.mpr rfl, hk⟩
      | _ => simp [Rule.rewrite] at h
    | _ => simp [Rule.rewrite] at h
  | inline =>
    cases e with
    | call f as =>
      simp only [Rule.rewrite] at h
      by_cases hf : f = self
      · simp [hf] at h
      · simp only [hf, if_false] at h
        cases hfn : P.fns[f]? with
        | none => simp [hfn] at h
        | some fn =>
          simp only [hfn] at h
          by_cases hc : as.length = fn.params.length ∧ closedB fn.params.length fn.body = true
          · simp only [hc, and_self, if_true, Option.some.injEq] at h
            subst h
            have hg : Pg.fns[f]? = some fn := by rw [hag f hf, hfn]
            rw [Eval_call, Eval_letsSeq]
            constructor
            · rintro ⟨vs, fn', hvs, hfn', hl, hb⟩
              rw [hg] at hfn'; cases hfn'
              refine ⟨vs, hvs, ?_⟩
              have hlen : vs.reverse.length = fn.params.length := by simp [hl]
              exact (Eval_closed (ρ' := ρ) (by rw [hlen]; exact hc.2)).mpr hb
            · rintro ⟨vs, hvs, hb⟩
              obtain ⟨n, hn⟩ := hvs
              have hl : vs.length = fn.params.length := by rw [mapOpt_length hn, hc.1]
              have hlen : vs.reverse.length = fn.params.length := by simp [hl]
              exact ⟨vs, fn, ⟨n, hn⟩, hg, hl,
                (Eval_closed (ρ' := ρ) (by rw [hlen]; exact hc.2)).mp hb⟩
          · simp [hc] at h
    | _ => simp [Rule.rewrite] at h

/-! ## Positions and congruence -/

def listReplace (h : Expr → Option Expr) : Nat → List Expr → Option (List Expr)
  | _, [] => none
  | 0, a :: as => (h a).map (· :: as)
  | k + 1, a :: as => (listReplace h k as).map (a :: ·)

def armsReplace (h : Expr → Option Expr) : Nat → List (Nat × Expr) → Option (List (Nat × Expr))
  | _, [] => none
  | 0, (j, a) :: as => (h a).map (fun a' => (j, a') :: as)
  | k + 1, x :: as => (armsReplace h k as).map (x :: ·)

/-- Apply `g` to the sub-expression at `path` (child indices: the arguments of
prim/ctr/call; 0/1 for let; 0/1/2 for par; 0 = scrutinee and `j+1` = body of
arm `j` for mat; 0/1/2 for natCase). -/
def replaceAt (g : Expr → Option Expr) : List Nat → Expr → Option Expr
  | [], e => g e
  | k :: ps, e =>
    match e, k with
    | .prim p as, k => (listReplace (replaceAt g ps) k as).map (.prim p)
    | .ctr a t as, k => (listReplace (replaceAt g ps) k as).map (.ctr a t)
    | .call f as, k => (listReplace (replaceAt g ps) k as).map (.call f)
    | .let_ e b, 0 => (replaceAt g ps e).map (fun x => .let_ x b)
    | .let_ e b, 1 => (replaceAt g ps b).map (fun x => .let_ e x)
    | .par e₁ e₂ b, 0 => (replaceAt g ps e₁).map (fun x => .par x e₂ b)
    | .par e₁ e₂ b, 1 => (replaceAt g ps e₂).map (fun x => .par e₁ x b)
    | .par e₁ e₂ b, 2 => (replaceAt g ps b).map (fun x => .par e₁ e₂ x)
    | .mat a s arms, 0 => (replaceAt g ps s).map (fun x => .mat a x arms)
    | .mat a s arms, j + 1 => (armsReplace (replaceAt g ps) j arms).map (.mat a s)
    | .natCase s z n, 0 => (replaceAt g ps s).map (fun x => .natCase x z n)
    | .natCase s z n, 1 => (replaceAt g ps z).map (fun x => .natCase s x n)
    | .natCase s z n, 2 => (replaceAt g ps n).map (fun x => .natCase s z x)
    | _, _ => none

theorem listReplace_EvalList {Pg : Prog} {h : Expr → Option Expr} (hl : LocalEq Pg h) :
    ∀ {k : Nat} {as as' : List Expr}, listReplace h k as = some as' →
      ∀ ρ vs, EvalList Pg ρ as vs ↔ EvalList Pg ρ as' vs
  | _, [], _, hr, _, _ => by simp [listReplace] at hr
  | 0, a :: as, zs, hr, ρ, ws => by
    simp only [listReplace, Option.map_eq_some_iff] at hr
    obtain ⟨a', ha, rfl⟩ := hr
    rw [EvalList_cons_iff, EvalList_cons_iff]
    constructor
    · rintro ⟨v, vs, rfl, hv, hvs⟩; exact ⟨v, vs, rfl, (hl a a' ha ρ v).mp hv, hvs⟩
    · rintro ⟨v, vs, rfl, hv, hvs⟩; exact ⟨v, vs, rfl, (hl a a' ha ρ v).mpr hv, hvs⟩
  | k + 1, a :: as, zs, hr, ρ, ws => by
    simp only [listReplace, Option.map_eq_some_iff] at hr
    obtain ⟨as', ha, rfl⟩ := hr
    rw [EvalList_cons_iff, EvalList_cons_iff]
    constructor
    · rintro ⟨v, vs, rfl, hv, hvs⟩; exact ⟨v, vs, rfl, hv, (listReplace_EvalList hl ha ρ vs).mp hvs⟩
    · rintro ⟨v, vs, rfl, hv, hvs⟩; exact ⟨v, vs, rfl, hv, (listReplace_EvalList hl ha ρ vs).mpr hvs⟩

theorem armsReplace_spec {h : Expr → Option Expr} :
    ∀ {j : Nat} {arms arms' : List (Nat × Expr)}, armsReplace h j arms = some arms' →
      ∀ (t : Nat), (arms[t]? = none ∧ arms'[t]? = none) ∨
        (∃ k b b', arms[t]? = some (k, b) ∧ arms'[t]? = some (k, b') ∧ (b = b' ∨ h b = some b'))
  | _, [], _, hr, _ => by simp [armsReplace] at hr
  | 0, (i, a) :: as, zs, hr, t => by
    simp only [armsReplace, Option.map_eq_some_iff] at hr
    obtain ⟨a', ha, rfl⟩ := hr
    cases t with
    | zero => exact Or.inr ⟨i, a, a', rfl, rfl, Or.inr ha⟩
    | succ t =>
      simp only [List.getElem?_cons_succ]
      cases hx : as[t]? with
      | none => exact Or.inl ⟨rfl, rfl⟩
      | some kb => exact Or.inr ⟨kb.1, kb.2, kb.2, rfl, rfl, Or.inl rfl⟩
  | k + 1, x :: as, zs, hr, t => by
    simp only [armsReplace, Option.map_eq_some_iff] at hr
    obtain ⟨as', ha, rfl⟩ := hr
    cases t with
    | zero => exact Or.inr ⟨x.1, x.2, x.2, rfl, rfl, Or.inl rfl⟩
    | succ t => simpa using armsReplace_spec ha t

theorem replaceAt_sound {Pg : Prog} {g : Expr → Option Expr} (hg : LocalEq Pg g) :
    ∀ (path : List Nat), LocalEq Pg (replaceAt g path)
  | [] => hg
  | k :: ps => by
    have ih := replaceAt_sound hg ps
    intro e e' hr ρ v
    cases e with
    | var _ => simp [replaceAt] at hr
    | u32 _ => simp [replaceAt] at hr
    | nat _ => simp [replaceAt] at hr
    | prim p as =>
      simp only [replaceAt, Option.map_eq_some_iff] at hr
      obtain ⟨as', ha, rfl⟩ := hr
      rw [Eval_prim, Eval_prim]
      constructor
      · rintro ⟨vs, hvs, hp⟩; exact ⟨vs, (listReplace_EvalList ih ha ρ vs).mp hvs, hp⟩
      · rintro ⟨vs, hvs, hp⟩; exact ⟨vs, (listReplace_EvalList ih ha ρ vs).mpr hvs, hp⟩
    | ctr a t as =>
      simp only [replaceAt, Option.map_eq_some_iff] at hr
      obtain ⟨as', ha, rfl⟩ := hr
      rw [Eval_ctr, Eval_ctr]
      constructor
      · rintro ⟨vs, hvs, hp⟩; exact ⟨vs, (listReplace_EvalList ih ha ρ vs).mp hvs, hp⟩
      · rintro ⟨vs, hvs, hp⟩; exact ⟨vs, (listReplace_EvalList ih ha ρ vs).mpr hvs, hp⟩
    | call f as =>
      simp only [replaceAt, Option.map_eq_some_iff] at hr
      obtain ⟨as', ha, rfl⟩ := hr
      rw [Eval_call, Eval_call]
      constructor
      · rintro ⟨vs, fn, hvs, h2⟩; exact ⟨vs, fn, (listReplace_EvalList ih ha ρ vs).mp hvs, h2⟩
      · rintro ⟨vs, fn, hvs, h2⟩; exact ⟨vs, fn, (listReplace_EvalList ih ha ρ vs).mpr hvs, h2⟩
    | let_ e b =>
      cases k with
      | zero =>
        simp only [replaceAt, Option.map_eq_some_iff] at hr
        obtain ⟨x, hx, rfl⟩ := hr
        rw [Eval_let, Eval_let]
        constructor
        · rintro ⟨w, hw, hb⟩; exact ⟨w, (ih e x hx ρ w).mp hw, hb⟩
        · rintro ⟨w, hw, hb⟩; exact ⟨w, (ih e x hx ρ w).mpr hw, hb⟩
      | succ k =>
        cases k with
        | zero =>
          simp only [replaceAt, Option.map_eq_some_iff] at hr
          obtain ⟨x, hx, rfl⟩ := hr
          rw [Eval_let, Eval_let]
          constructor
          · rintro ⟨w, hw, hb⟩; exact ⟨w, hw, (ih b x hx _ v).mp hb⟩
          · rintro ⟨w, hw, hb⟩; exact ⟨w, hw, (ih b x hx _ v).mpr hb⟩
        | succ _ => simp [replaceAt] at hr
    | par e₁ e₂ b =>
      match k, hr with
      | 0, hr =>
        simp only [replaceAt, Option.map_eq_some_iff] at hr
        obtain ⟨x, hx, rfl⟩ := hr
        rw [Eval_par, Eval_par]
        constructor
        · rintro ⟨w₁, w₂, h₁, h₂, hb⟩; exact ⟨w₁, w₂, (ih e₁ x hx ρ w₁).mp h₁, h₂, hb⟩
        · rintro ⟨w₁, w₂, h₁, h₂, hb⟩; exact ⟨w₁, w₂, (ih e₁ x hx ρ w₁).mpr h₁, h₂, hb⟩
      | 1, hr =>
        simp only [replaceAt, Option.map_eq_some_iff] at hr
        obtain ⟨x, hx, rfl⟩ := hr
        rw [Eval_par, Eval_par]
        constructor
        · rintro ⟨w₁, w₂, h₁, h₂, hb⟩; exact ⟨w₁, w₂, h₁, (ih e₂ x hx ρ w₂).mp h₂, hb⟩
        · rintro ⟨w₁, w₂, h₁, h₂, hb⟩; exact ⟨w₁, w₂, h₁, (ih e₂ x hx ρ w₂).mpr h₂, hb⟩
      | 2, hr =>
        simp only [replaceAt, Option.map_eq_some_iff] at hr
        obtain ⟨x, hx, rfl⟩ := hr
        rw [Eval_par, Eval_par]
        constructor
        · rintro ⟨w₁, w₂, h₁, h₂, hb⟩; exact ⟨w₁, w₂, h₁, h₂, (ih b x hx _ v).mp hb⟩
        · rintro ⟨w₁, w₂, h₁, h₂, hb⟩; exact ⟨w₁, w₂, h₁, h₂, (ih b x hx _ v).mpr hb⟩
      | _ + 3, hr => simp [replaceAt] at hr
    | mat a s arms =>
      cases k with
      | zero =>
        simp only [replaceAt, Option.map_eq_some_iff] at hr
        obtain ⟨x, hx, rfl⟩ := hr
        rw [Eval_mat, Eval_mat]
        constructor
        · rintro ⟨t, fs, k, body, hs, h2⟩; exact ⟨t, fs, k, body, (ih s x hx ρ _).mp hs, h2⟩
        · rintro ⟨t, fs, k, body, hs, h2⟩; exact ⟨t, fs, k, body, (ih s x hx ρ _).mpr hs, h2⟩
      | succ j =>
        simp only [replaceAt, Option.map_eq_some_iff] at hr
        obtain ⟨arms', ha, rfl⟩ := hr
        rw [Eval_mat, Eval_mat]
        constructor
        · rintro ⟨t, fs, k, body, hs, harm, hl, hb⟩
          rcases armsReplace_spec ha t with ⟨h1, _⟩ | ⟨k', b, b', h1, h2, h3⟩
          · rw [h1] at harm; cases harm
          · rw [h1] at harm; cases harm
            refine ⟨t, fs, k, b', hs, h2, hl, ?_⟩
            rcases h3 with rfl | h3
            · exact hb
            · exact (ih _ _ h3 _ v).mp hb
        · rintro ⟨t, fs, k, body, hs, harm, hl, hb⟩
          rcases armsReplace_spec ha t with ⟨_, h1⟩ | ⟨k', b, b', h1, h2, h3⟩
          · rw [h1] at harm; cases harm
          · rw [h2] at harm; cases harm
            refine ⟨t, fs, k, b, hs, h1, hl, ?_⟩
            rcases h3 with rfl | h3
            · exact hb
            · exact (ih _ _ h3 _ v).mpr hb
    | natCase s z n =>
      match k, hr with
      | 0, hr =>
        simp only [replaceAt, Option.map_eq_some_iff] at hr
        obtain ⟨x, hx, rfl⟩ := hr
        rw [Eval_natCase, Eval_natCase]
        constructor
        · rintro (⟨hs, hz⟩ | ⟨m, hs, hk⟩)
          · exact Or.inl ⟨(ih s x hx ρ _).mp hs, hz⟩
          · exact Or.inr ⟨m, (ih s x hx ρ _).mp hs, hk⟩
        · rintro (⟨hs, hz⟩ | ⟨m, hs, hk⟩)
          · exact Or.inl ⟨(ih s x hx ρ _).mpr hs, hz⟩
          · exact Or.inr ⟨m, (ih s x hx ρ _).mpr hs, hk⟩
      | 1, hr =>
        simp only [replaceAt, Option.map_eq_some_iff] at hr
        obtain ⟨x, hx, rfl⟩ := hr
        rw [Eval_natCase, Eval_natCase]
        constructor
        · rintro (⟨hs, hz⟩ | ⟨m, hs, hk⟩)
          · exact Or.inl ⟨hs, (ih z x hx ρ v).mp hz⟩
          · exact Or.inr ⟨m, hs, hk⟩
        · rintro (⟨hs, hz⟩ | ⟨m, hs, hk⟩)
          · exact Or.inl ⟨hs, (ih z x hx ρ v).mpr hz⟩
          · exact Or.inr ⟨m, hs, hk⟩
      | 2, hr =>
        simp only [replaceAt, Option.map_eq_some_iff] at hr
        obtain ⟨x, hx, rfl⟩ := hr
        rw [Eval_natCase, Eval_natCase]
        constructor
        · rintro (⟨hs, hz⟩ | ⟨m, hs, hk⟩)
          · exact Or.inl ⟨hs, hz⟩
          · exact Or.inr ⟨m, hs, (ih n x hx _ v).mp hk⟩
        · rintro (⟨hs, hz⟩ | ⟨m, hs, hk⟩)
          · exact Or.inl ⟨hs, hz⟩
          · exact Or.inr ⟨m, hs, (ih n x hx _ v).mpr hk⟩
      | _ + 3, hr => simp [replaceAt] at hr

/-! ## Steps and their soundness -/

structure Step where
  fn : Nat
  path : List Nat
  rule : Rule
  deriving Repr, Inhabited

/-- Executable step checker: recompute the rewritten program. -/
def applyStep (P : Prog) (s : Step) : Option Prog :=
  match P.fns[s.fn]? with
  | none => none
  | some fn =>
    match replaceAt (s.rule.rewrite P s.fn) s.path fn.body with
    | none => none
    | some b' => some { P with fns := P.fns.set s.fn { fn with body := b' } }

theorem map_set_same {α β : Type} (f : α → β) :
    ∀ (l : List α) (i : Nat) (x y : α), l[i]? = some x → f y = f x → (l.set i y).map f = l.map f
  | [], _, _, _, h, _ => by simp at h
  | a :: l, 0, x, y, h, hf => by simp at h; subst h; simp [hf]
  | a :: l, i + 1, x, y, h, hf => by
    simp only [List.getElem?_cons_succ] at h
    simp [map_set_same f l i x y h hf]

/-- **Soundness of the rule library**: any program produced by `applyStep`
is equivalent to its input, for every context whose entry `P` exposes. -/
theorem applyStep_sound {c : Ctx} {P Q : Prog} {s : Step} (h : applyStep P s = some Q)
    (hw : WfEntry c P) : Equiv c P Q := by
  unfold applyStep at h
  cases hfn : P.fns[s.fn]? with
  | none => simp [hfn] at h
  | some fn =>
    simp only [hfn] at h
    cases hb : replaceAt (s.rule.rewrite P s.fn) s.path fn.body with
    | none => simp [hb] at h
    | some b' =>
      simp only [hb, Option.some.injEq] at h
      subst h
      have hi : s.fn < P.fns.length := by
        rcases Nat.lt_or_ge s.fn P.fns.length with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none h'] at hfn; simp at hfn
      let Q : Prog := { P with fns := P.fns.set s.fn { fn with body := b' } }
      have hQs : Q.fns[s.fn]? = some { fn with body := b' } := by
        simp [Q, List.getElem?_set_self hi]
      have hQo : ∀ i, i ≠ s.fn → Q.fns[i]? = P.fns[i]? := by
        intro i hne; simp only [Q]; rw [List.getElem?_set_ne (Ne.symm hne)]
      have agQ : Agree P Q s.fn := hQo
      have agP : Agree P P s.fn := fun _ _ => rfl
      refine equiv_of_bodies (P := P) (Q := Q) (show P.adts = Q.adts from rfl) ?_ ?_ ?_ hw
      · exact (map_set_same (fun f => (f.name, f.params, f.ret)) P.fns s.fn fn { fn with body := b' } hfn rfl).symm
      · intro i fp fq hp hq ρ v he
        by_cases hi' : i = s.fn
        · subst hi'
          rw [hfn] at hp; cases hp
          rw [hQs] at hq; cases hq
          exact (replaceAt_sound (Rule.rewrite_sound agQ s.rule) s.path _ b' hb ρ v).mp he
        · rw [hQo i hi', hp] at hq; cases hq; exact he
      · intro i fp fq hp hq ρ v he
        by_cases hi' : i = s.fn
        · subst hi'
          rw [hfn] at hp; cases hp
          rw [hQs] at hq; cases hq
          exact (replaceAt_sound (Rule.rewrite_sound agP s.rule) s.path _ b' hb ρ v).mpr he
        · rw [hQo i hi', hp] at hq; cases hq; exact he

/-- Form used by generated proofs: the kernel evaluates both checks. -/
theorem step_equiv (c : Ctx) (P Q : Prog) (s : Step)
    (hw : wfEntryB c P = true) (h : applyStep P s = some Q) : Equiv c P Q :=
  applyStep_sound h (wfEntryB_sound hw)

end BendVerify
