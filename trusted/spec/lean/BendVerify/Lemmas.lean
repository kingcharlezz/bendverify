/-
BendVerify.Lemmas — metatheory of the fuel semantics.

Fuel monotonicity, determinism, and fuel-free ("compositional")
characterisations of `Eval` for every construct. These are ordinary
kernel-checked theorems; they are part of the trusted library only in the
sense that the obligation generator relies on them to compose proofs.
-/
import BendVerify.Semantics

namespace BendVerify

/-! ## mapOpt -/

theorem mapOpt_nil {α β : Type} (f : α → Option β) : mapOpt f [] = some [] := rfl

theorem mapOpt_cons_some {α β : Type} {f : α → Option β} {x : α} {xs : List α} {y : β}
    {ys : List β} (h1 : f x = some y) (h2 : mapOpt f xs = some ys) :
    mapOpt f (x :: xs) = some (y :: ys) := by
  simp [mapOpt, h1, h2]

theorem mapOpt_cons_inv {α β : Type} {f : α → Option β} {x : α} {xs : List α} {zs : List β}
    (h : mapOpt f (x :: xs) = some zs) :
    ∃ y ys, zs = y :: ys ∧ f x = some y ∧ mapOpt f xs = some ys := by
  simp only [mapOpt] at h
  split at h
  · simp at h
  · rename_i y hy
    split at h
    · simp at h
    · rename_i ys hys
      exact ⟨y, ys, (Option.some.inj h).symm, hy, hys⟩

theorem mapOpt_nil_inv {α β : Type} {f : α → Option β} {zs : List β}
    (h : mapOpt f [] = some zs) : zs = [] := by
  exact (Option.some.inj (h : some [] = some zs)).symm

theorem mapOpt_mono {α β : Type} {f g : α → Option β} :
    ∀ {xs : List α} {ys : List β}, (∀ x ∈ xs, ∀ y, f x = some y → g x = some y) →
      mapOpt f xs = some ys → mapOpt g xs = some ys
  | [], ys, _, h => h
  | x :: xs, zs, hfg, h => by
    obtain ⟨y, ys, rfl, hy, hys⟩ := mapOpt_cons_inv h
    have h1 := hfg x (List.mem_cons_self) y hy
    have h2 := mapOpt_mono (fun x' hx' y' hy' => hfg x' (List.mem_cons_of_mem _ hx') y' hy') hys
    exact mapOpt_cons_some h1 h2

theorem mapOpt_length {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, mapOpt f xs = some ys → ys.length = xs.length
  | [], ys, h => by rw [mapOpt_nil_inv h]; rfl
  | x :: xs, zs, h => by
    obtain ⟨y, ys, rfl, _, hys⟩ := mapOpt_cons_inv h
    simp [mapOpt_length hys]


/-! ## Equation lemmas (definitional; used to unfold one step at a time) -/

section Eqns
variable {n : Nat} {P : Prog} {ρ : Env}
theorem ev_zero (e : Expr) : ev 0 P ρ e = none := rfl
theorem ev_var (i : Nat) : ev (n + 1) P ρ (.var i) = ρ[i]? := rfl
theorem ev_u32 (k : Nat) : ev (n + 1) P ρ (.u32 k) = some (.u32 (k % M32)) := rfl
theorem ev_nat (k : Nat) : ev (n + 1) P ρ (.nat k) = some (.nat k) := rfl
theorem ev_prim (p : Prim) (as : List Expr) : ev (n + 1) P ρ (.prim p as) =
    (match mapOpt (ev n P ρ) as with
     | none => none
     | some vs => p.eval vs) := rfl
theorem ev_ctr (a t : Nat) (as : List Expr) : ev (n + 1) P ρ (.ctr a t as) =
    (match mapOpt (ev n P ρ) as with
     | none => none
     | some vs => some (.ctr t vs)) := rfl
theorem ev_call (f : Nat) (as : List Expr) : ev (n + 1) P ρ (.call f as) =
    (match mapOpt (ev n P ρ) as with
     | none => none
     | some vs =>
       match P.fns[f]? with
       | none => none
       | some fn => if vs.length = fn.params.length then ev n P vs.reverse fn.body else none) := rfl
theorem ev_let (e b : Expr) : ev (n + 1) P ρ (.let_ e b) =
    (match ev n P ρ e with
     | none => none
     | some v => ev n P (v :: ρ) b) := rfl
theorem ev_par (e₁ e₂ b : Expr) : ev (n + 1) P ρ (.par e₁ e₂ b) =
    (match ev n P ρ e₁ with
     | none => none
     | some v₁ =>
       match ev n P ρ e₂ with
       | none => none
       | some v₂ => ev n P (v₂ :: v₁ :: ρ) b) := rfl
theorem ev_mat (a : Nat) (s : Expr) (arms : List (Nat × Expr)) : ev (n + 1) P ρ (.mat a s arms) =
    (match ev n P ρ s with
     | some (.ctr t fs) =>
       match arms[t]? with
       | none => none
       | some (k, body) => if fs.length = k then ev n P (fs.reverse ++ ρ) body else none
     | _ => none) := rfl
theorem ev_natCase (s z k : Expr) : ev (n + 1) P ρ (.natCase s z k) =
    (match ev n P ρ s with
     | some (.nat 0) => ev n P ρ z
     | some (.nat (m + 1)) => ev n P (.nat m :: ρ) k
     | _ => none) := rfl
end Eqns

/-! ## Fuel monotonicity -/

theorem ev_mono_succ : ∀ {n : Nat} {P : Prog} {ρ : Env} {e : Expr} {v : Val},
    ev n P ρ e = some v → ev (n + 1) P ρ e = some v := by
  intro n
  induction n with
  | zero => intro P ρ e v h; simp [ev_zero] at h
  | succ n ih =>
    intro P ρ e v h
    have ihl : ∀ {ρ' : Env} {as : List Expr} {vs : List Val},
        mapOpt (ev n P ρ') as = some vs → mapOpt (ev (n + 1) P ρ') as = some vs :=
      fun hm => mapOpt_mono (fun _ _ _ hy => ih hy) hm
    cases e with
    | var i => exact h
    | u32 k => exact h
    | nat k => exact h
    | prim p as =>
      rw [ev_prim] at h ⊢
      cases hvs : mapOpt (ev n P ρ) as with
      | none => simp [hvs] at h
      | some vs => simp only [hvs] at h; simp only [ihl hvs]; exact h
    | ctr a t as =>
      rw [ev_ctr] at h ⊢
      cases hvs : mapOpt (ev n P ρ) as with
      | none => simp [hvs] at h
      | some vs => simp only [hvs] at h; simp only [ihl hvs]; exact h
    | call f as =>
      rw [ev_call] at h ⊢
      cases hvs : mapOpt (ev n P ρ) as with
      | none => simp [hvs] at h
      | some vs =>
        simp only [hvs] at h
        simp only [ihl hvs]
        cases hfn : P.fns[f]? with
        | none => simp [hfn] at h
        | some fn =>
          simp only [hfn] at h ⊢
          by_cases hl : vs.length = fn.params.length
          · simp only [hl, if_true] at h ⊢; exact ih h
          · simp [hl] at h
    | let_ e₁ b =>
      rw [ev_let] at h ⊢
      cases hw : ev n P ρ e₁ with
      | none => simp [hw] at h
      | some w => simp only [hw] at h; simp only [ih hw]; exact ih h
    | par e₁ e₂ b =>
      rw [ev_par] at h ⊢
      cases hw₁ : ev n P ρ e₁ with
      | none => simp [hw₁] at h
      | some w₁ =>
        simp only [hw₁] at h; simp only [ih hw₁]
        cases hw₂ : ev n P ρ e₂ with
        | none => simp [hw₂] at h
        | some w₂ => simp only [hw₂] at h; simp only [ih hw₂]; exact ih h
    | mat a s arms =>
      rw [ev_mat] at h ⊢
      cases hs : ev n P ρ s with
      | none => simp [hs] at h
      | some sv =>
        cases sv with
        | u32 _ => simp [hs] at h
        | nat _ => simp [hs] at h
        | ctr t fs =>
          simp only [hs] at h; simp only [ih hs]
          cases harm : arms[t]? with
          | none => simp [harm] at h
          | some kb =>
            obtain ⟨k, body⟩ := kb
            simp only [harm] at h ⊢
            by_cases hl : fs.length = k
            · simp only [hl, if_true] at h ⊢; exact ih h
            · simp [hl] at h
    | natCase s z k =>
      rw [ev_natCase] at h ⊢
      cases hs : ev n P ρ s with
      | none => simp [hs] at h
      | some sv =>
        cases sv with
        | u32 _ => simp [hs] at h
        | ctr _ _ => simp [hs] at h
        | nat m =>
          cases m with
          | zero => simp only [hs] at h; simp only [ih hs]; exact ih h
          | succ m => simp only [hs] at h; simp only [ih hs]; exact ih h

theorem ev_mono : ∀ {n m : Nat} {P : Prog} {ρ : Env} {e : Expr} {v : Val},
    n ≤ m → ev n P ρ e = some v → ev m P ρ e = some v := by
  intro n m P ρ e v hle h
  induction hle with
  | refl => exact h
  | step _ ih => exact ev_mono_succ ih

theorem ev_det {n m : Nat} {P : Prog} {ρ : Env} {e : Expr} {v w : Val}
    (h1 : ev n P ρ e = some v) (h2 : ev m P ρ e = some w) : v = w := by
  have a := ev_mono (Nat.le_max_left n m) h1
  have b := ev_mono (Nat.le_max_right n m) h2
  rw [a] at b; exact Option.some.inj b

theorem Eval_det {P : Prog} {ρ : Env} {e : Expr} {v w : Val}
    (h1 : Eval P ρ e v) (h2 : Eval P ρ e w) : v = w := by
  obtain ⟨n, hn⟩ := h1; obtain ⟨m, hm⟩ := h2; exact ev_det hn hm

/-! ## Evaluation of argument lists without fuel -/

/-- All of `as` terminate, with values `vs`. -/
def EvalList (P : Prog) (ρ : Env) (as : List Expr) (vs : List Val) : Prop :=
  ∃ n, mapOpt (ev n P ρ) as = some vs

theorem mapOpt_ev_mono {n m : Nat} {P : Prog} {ρ : Env} {as : List Expr} {vs : List Val}
    (hle : n ≤ m) (h : mapOpt (ev n P ρ) as = some vs) : mapOpt (ev m P ρ) as = some vs :=
  mapOpt_mono (fun _ _ _ hy => ev_mono hle hy) h

theorem EvalList_nil (P : Prog) (ρ : Env) : EvalList P ρ [] [] := ⟨0, rfl⟩

theorem EvalList_cons {P : Prog} {ρ : Env} {a : Expr} {as : List Expr} {v : Val} {vs : List Val}
    (h1 : Eval P ρ a v) (h2 : EvalList P ρ as vs) : EvalList P ρ (a :: as) (v :: vs) := by
  obtain ⟨n, hn⟩ := h1; obtain ⟨m, hm⟩ := h2
  refine ⟨max n m, mapOpt_cons_some (ev_mono (Nat.le_max_left n m) hn)
    (mapOpt_ev_mono (Nat.le_max_right n m) hm)⟩

theorem EvalList_cons_iff {P : Prog} {ρ : Env} {a : Expr} {as : List Expr} {ws : List Val} :
    EvalList P ρ (a :: as) ws ↔ ∃ v vs, ws = v :: vs ∧ Eval P ρ a v ∧ EvalList P ρ as vs := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨v, vs, rfl, hv, hvs⟩ := mapOpt_cons_inv hn
    exact ⟨v, vs, rfl, ⟨n, hv⟩, ⟨n, hvs⟩⟩
  · rintro ⟨v, vs, rfl, hv, hvs⟩
    exact EvalList_cons hv hvs

theorem EvalList_nil_iff {P : Prog} {ρ : Env} {ws : List Val} :
    EvalList P ρ [] ws ↔ ws = [] := by
  constructor
  · rintro ⟨n, hn⟩; exact mapOpt_nil_inv hn
  · rintro rfl; exact EvalList_nil P ρ

/-- Pointwise characterisation: EvalList is "Forall₂ Eval". -/
theorem EvalList_of_forall {P Q : Prog} {ρ ρ' : Env} :
    ∀ {as bs : List Expr} {vs : List Val}, as.length = bs.length →
      (∀ (i : Nat) (a b : Expr) (v : Val), as[i]? = some a → bs[i]? = some b → Eval P ρ a v → Eval Q ρ' b v) →
      EvalList P ρ as vs → EvalList Q ρ' bs vs
  | [], [], vs, _, _, h => by rw [EvalList_nil_iff.mp h]; exact EvalList_nil Q ρ'
  | [], _ :: _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, hl, _, _ => by simp at hl
  | a :: as, b :: bs, ws, hl, hab, h => by
    obtain ⟨v, vs, rfl, hv, hvs⟩ := EvalList_cons_iff.mp h
    refine EvalList_cons (hab 0 a b v rfl rfl hv) ?_
    exact EvalList_of_forall (by simpa using hl)
      (fun i a' b' v' ha hb he => hab (i + 1) a' b' v' (by simpa using ha) (by simpa using hb) he) hvs

/-! ## Compositional characterisations of `Eval` -/

theorem Eval_var {P : Prog} {ρ : Env} {i : Nat} {v : Val} :
    Eval P ρ (.var i) v ↔ ρ[i]? = some v := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [ev_zero] at hn
    | succ n => exact hn
  · intro h; exact ⟨1, h⟩

theorem Eval_u32 {P : Prog} {ρ : Env} {k : Nat} {v : Val} :
    Eval P ρ (.u32 k) v ↔ v = .u32 (k % M32) := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [ev_zero] at hn
    | succ n => exact (Option.some.inj hn).symm
  · rintro rfl; exact ⟨1, rfl⟩

theorem Eval_nat {P : Prog} {ρ : Env} {k : Nat} {v : Val} :
    Eval P ρ (.nat k) v ↔ v = .nat k := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [ev_zero] at hn
    | succ n => exact (Option.some.inj hn).symm
  · rintro rfl; exact ⟨1, rfl⟩

theorem Eval_prim {P : Prog} {ρ : Env} {p : Prim} {as : List Expr} {v : Val} :
    Eval P ρ (.prim p as) v ↔ ∃ vs, EvalList P ρ as vs ∧ p.eval vs = some v := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [ev_zero] at hn
    | succ n =>
      rw [ev_prim] at hn
      cases hvs : mapOpt (ev n P ρ) as with
      | none => simp [hvs] at hn
      | some vs => simp only [hvs] at hn; exact ⟨vs, ⟨n, hvs⟩, hn⟩
  · rintro ⟨vs, ⟨n, hn⟩, hp⟩
    exact ⟨n + 1, by rw [ev_prim]; simp only [hn]; exact hp⟩

theorem Eval_ctr {P : Prog} {ρ : Env} {a t : Nat} {as : List Expr} {v : Val} :
    Eval P ρ (.ctr a t as) v ↔ ∃ vs, EvalList P ρ as vs ∧ v = .ctr t vs := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [ev_zero] at hn
    | succ n =>
      rw [ev_ctr] at hn
      cases hvs : mapOpt (ev n P ρ) as with
      | none => simp [hvs] at hn
      | some vs => simp only [hvs] at hn; exact ⟨vs, ⟨n, hvs⟩, (Option.some.inj hn).symm⟩
  · rintro ⟨vs, ⟨n, hn⟩, rfl⟩
    exact ⟨n + 1, by rw [ev_ctr]; simp only [hn]⟩

theorem Eval_call {P : Prog} {ρ : Env} {f : Nat} {as : List Expr} {v : Val} :
    Eval P ρ (.call f as) v ↔ ∃ vs fn, EvalList P ρ as vs ∧ P.fns[f]? = some fn ∧
      vs.length = fn.params.length ∧ Eval P vs.reverse fn.body v := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [ev_zero] at hn
    | succ n =>
      rw [ev_call] at hn
      cases hvs : mapOpt (ev n P ρ) as with
      | none => simp [hvs] at hn
      | some vs =>
        simp only [hvs] at hn
        cases hfn : P.fns[f]? with
        | none => simp [hfn] at hn
        | some fn =>
          simp only [hfn] at hn
          by_cases hl : vs.length = fn.params.length
          · simp only [hl, if_true] at hn; exact ⟨vs, fn, ⟨n, hvs⟩, rfl, hl, ⟨n, hn⟩⟩
          · simp [hl] at hn
  · rintro ⟨vs, fn, ⟨n, hn⟩, hfn, hl, ⟨m, hm⟩⟩
    refine ⟨max n m + 1, ?_⟩
    rw [ev_call]
    simp only [mapOpt_ev_mono (Nat.le_max_left n m) hn, hfn, hl, if_true]
    exact ev_mono (Nat.le_max_right n m) hm

theorem Eval_let {P : Prog} {ρ : Env} {e b : Expr} {v : Val} :
    Eval P ρ (.let_ e b) v ↔ ∃ w, Eval P ρ e w ∧ Eval P (w :: ρ) b v := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [ev_zero] at hn
    | succ n =>
      rw [ev_let] at hn
      cases hw : ev n P ρ e with
      | none => simp [hw] at hn
      | some w => simp only [hw] at hn; exact ⟨w, ⟨n, hw⟩, ⟨n, hn⟩⟩
  · rintro ⟨w, ⟨n, hn⟩, ⟨m, hm⟩⟩
    refine ⟨max n m + 1, ?_⟩
    rw [ev_let]
    simp only [ev_mono (Nat.le_max_left n m) hn]
    exact ev_mono (Nat.le_max_right n m) hm

theorem Eval_par {P : Prog} {ρ : Env} {e₁ e₂ b : Expr} {v : Val} :
    Eval P ρ (.par e₁ e₂ b) v ↔
      ∃ w₁ w₂, Eval P ρ e₁ w₁ ∧ Eval P ρ e₂ w₂ ∧ Eval P (w₂ :: w₁ :: ρ) b v := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [ev_zero] at hn
    | succ n =>
      rw [ev_par] at hn
      cases hw₁ : ev n P ρ e₁ with
      | none => simp [hw₁] at hn
      | some w₁ =>
        simp only [hw₁] at hn
        cases hw₂ : ev n P ρ e₂ with
        | none => simp [hw₂] at hn
        | some w₂ => simp only [hw₂] at hn; exact ⟨w₁, w₂, ⟨n, hw₁⟩, ⟨n, hw₂⟩, ⟨n, hn⟩⟩
  · rintro ⟨w₁, w₂, ⟨n₁, h₁⟩, ⟨n₂, h₂⟩, ⟨m, hm⟩⟩
    refine ⟨max (max n₁ n₂) m + 1, ?_⟩
    have le1 : n₁ ≤ max (max n₁ n₂) m := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    have le2 : n₂ ≤ max (max n₁ n₂) m := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
    rw [ev_par]
    simp only [ev_mono le1 h₁, ev_mono le2 h₂]
    exact ev_mono (Nat.le_max_right _ _) hm

theorem Eval_mat {P : Prog} {ρ : Env} {a : Nat} {s : Expr} {arms : List (Nat × Expr)} {v : Val} :
    Eval P ρ (.mat a s arms) v ↔ ∃ t fs k body, Eval P ρ s (.ctr t fs) ∧
      arms[t]? = some (k, body) ∧ fs.length = k ∧ Eval P (fs.reverse ++ ρ) body v := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [ev_zero] at hn
    | succ n =>
      rw [ev_mat] at hn
      cases hs : ev n P ρ s with
      | none => simp [hs] at hn
      | some sv =>
        cases sv with
        | u32 _ => simp [hs] at hn
        | nat _ => simp [hs] at hn
        | ctr t fs =>
          simp only [hs] at hn
          cases harm : arms[t]? with
          | none => simp [harm] at hn
          | some kb =>
            obtain ⟨k, body⟩ := kb
            simp only [harm] at hn
            by_cases hl : fs.length = k
            · simp only [hl, if_true] at hn; exact ⟨t, fs, k, body, ⟨n, hs⟩, harm, hl, ⟨n, hn⟩⟩
            · simp [hl] at hn
  · rintro ⟨t, fs, k, body, ⟨n, hn⟩, harm, hl, ⟨m, hm⟩⟩
    refine ⟨max n m + 1, ?_⟩
    rw [ev_mat]
    simp only [ev_mono (Nat.le_max_left n m) hn, harm, hl, if_true]
    exact ev_mono (Nat.le_max_right n m) hm

theorem Eval_natCase {P : Prog} {ρ : Env} {s z k : Expr} {v : Val} :
    Eval P ρ (.natCase s z k) v ↔
      (Eval P ρ s (.nat 0) ∧ Eval P ρ z v) ∨
      (∃ m, Eval P ρ s (.nat (m + 1)) ∧ Eval P (.nat m :: ρ) k v) := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [ev_zero] at hn
    | succ n =>
      rw [ev_natCase] at hn
      cases hs : ev n P ρ s with
      | none => simp [hs] at hn
      | some sv =>
        cases sv with
        | u32 _ => simp [hs] at hn
        | ctr _ _ => simp [hs] at hn
        | nat m =>
          cases m with
          | zero => simp only [hs] at hn; exact Or.inl ⟨⟨n, hs⟩, ⟨n, hn⟩⟩
          | succ m => simp only [hs] at hn; exact Or.inr ⟨m, ⟨n, hs⟩, ⟨n, hn⟩⟩
  · rintro (⟨⟨n, hn⟩, ⟨m, hm⟩⟩ | ⟨j, ⟨n, hn⟩, ⟨m, hm⟩⟩)
    · refine ⟨max n m + 1, ?_⟩
      rw [ev_natCase]
      simp only [ev_mono (Nat.le_max_left n m) hn]
      exact ev_mono (Nat.le_max_right n m) hm
    · refine ⟨max n m + 1, ?_⟩
      rw [ev_natCase]
      simp only [ev_mono (Nat.le_max_left n m) hn]
      exact ev_mono (Nat.le_max_right n m) hm

/-! ## Calling functions -/

theorem runFn_iff {P : Prog} {f : Nat} {args : List Val} {v : Val} :
    (∃ n, runFn n P f args = some v) ↔
      ∃ fn, P.fns[f]? = some fn ∧ args.length = fn.params.length ∧ Eval P args.reverse fn.body v := by
  constructor
  · rintro ⟨n, hn⟩
    unfold runFn at hn
    split at hn
    · simp at hn
    · rename_i fn hfn
      split at hn
      · rename_i hl; exact ⟨fn, hfn, hl, ⟨n, hn⟩⟩
      · simp at hn
  · rintro ⟨fn, hfn, hl, ⟨n, hn⟩⟩
    exact ⟨n, by unfold runFn; simp only [hfn, if_pos hl]; exact hn⟩

theorem Run_iff {P : Prog} {name : String} {args : List Val} {v : Val} :
    Run P name args v ↔ ∃ i fn, P.findFn name = some (i, fn) ∧ P.fns[i]? = some fn ∧
      args.length = fn.params.length ∧ Eval P args.reverse fn.body v := by
  constructor
  · rintro ⟨i, fn, hf, h⟩
    obtain ⟨fn', hfn', hl, he⟩ := runFn_iff.mp h
    exact ⟨i, fn', by
      -- `findFn` returns the function stored at the index it reports
      have := findFn_get hf
      rw [hfn'] at this
      cases this; exact hf, hfn', hl, he⟩
  · rintro ⟨i, fn, hf, hfn, hl, he⟩
    exact ⟨i, fn, hf, runFn_iff.mpr ⟨fn, hfn, hl, he⟩⟩
where
  findFn_get {P : Prog} {name : String} {i : Nat} {fn : Fn}
      (h : P.findFn name = some (i, fn)) : P.fns[i]? = some fn := by
    unfold Prog.findFn at h
    suffices ∀ (l : List Fn) (j : Nat), Prog.findFn.go name l j = some (i, fn) →
        j ≤ i ∧ l[i - j]? = some fn by
      have := this P.fns 0 h; simpa using this.2
    intro l
    induction l with
    | nil => intro j h; simp [Prog.findFn.go] at h
    | cons g gs ih =>
      intro j h
      simp only [Prog.findFn.go] at h
      split at h
      · simp at h; obtain ⟨rfl, rfl⟩ := h; simp
      · obtain ⟨h1, h2⟩ := ih (j + 1) h
        refine ⟨by omega, ?_⟩
        have : i - j = (i - (j + 1)) + 1 := by omega
        rw [this]; simpa using h2

end BendVerify
