/-
Proof for the lexer fold/build fusion step (competitor-written, UNTRUSTED).

The step replaces
    line(i) = lex(gen(tpl(), seed(i), 0), (Gap{}, 0))
by
    line(i) = lex.fin(lex.gen(tpl(), seed(i), 0, (Gap{}, 0)))
where lex.gen, lex.gen.at, lex.expand, lex.ident, lex.num, lex.op thread the
lexer state through the generator instead of building the String, and
lex.feed / lex.fin are one lexer step / the final flush.

  * producers: lex(P(args, rest), r) = lex(rest, P'(args, r))
      ident, num (induction on the count), op, expand (cases on the slot), gen.at;
  * terminal:  lex(gen(tpl, s, k), r) = lex.fin(lex.gen(tpl, s, k, r))
      (well-founded induction on the template string);
  * transfer:  run is unchanged; line (called by batch) changed. P_0 -> P_1 by
      `simulate`; P_1 -> P_0 through Q' (= P_1 with the old line) and
      `simulate_on` over the 24 original functions.
-/
import Contest.Obligation
open BendVerify Contest.Obligation.lexer

namespace Submission.Lexer

def genB : Expr := (.mat 2 (.var 2) [(0, (.ctr 2 0 [])), (2, (.mat 3 (.var 1) [(1, (.call 9 [(.var 0), (.call 8 [(.var 4), (.var 3)]), (.call 5 [(.var 1), (.var 4), (.prim .u32_add [(.var 3), (.u32 1)])])]))]))])
def lexB : Expr := (.mat 2 (.var 1) [(0, (.mat 1 (.var 0) [(2, (.call 10 [(.var 1), (.var 0)]))])), (2, (.mat 3 (.var 1) [(1, (.mat 1 (.var 3) [(2, (.call 6 [(.var 3), (.call 11 [(.var 1), (.var 2), (.var 0)])]))]))]))])
def genAtB : Expr := (.call 13 [(.call 12 [(.var 2)]), (.var 2), (.var 1), (.var 0)])
def expandB : Expr := (.mat 4 (.var 3) [(0, (.call 18 [(.prim .u32_to_nat [(.prim .u32_add [(.u32 1), (.prim .u32_and [(.var 1), (.u32 7)])])]), (.var 1), (.var 0)])), (0, (.call 19 [(.prim .u32_to_nat [(.prim .u32_add [(.u32 1), (.prim .u32_mod [(.var 1), (.u32 6)])])]), (.var 1), (.var 0)])), (0, (.call 20 [(.var 1), (.var 0)])), (0, (.ctr 2 1 [(.ctr 3 0 [(.var 2)]), (.var 0)]))])
def identB : Expr := (.natCase (.var 2) (.var 0) (.let_ (.call 7 [(.var 2)]) (.ctr 2 1 [(.ctr 3 0 [(.prim .u32_add [(.u32 97), (.prim .u32_mod [(.var 0), (.u32 26)])])]), (.call 18 [(.var 1), (.var 0), (.var 2)])])))
def numB : Expr := (.natCase (.var 2) (.var 0) (.let_ (.call 7 [(.var 2)]) (.ctr 2 1 [(.ctr 3 0 [(.prim .u32_add [(.u32 48), (.prim .u32_mod [(.var 0), (.u32 10)])])]), (.call 19 [(.var 1), (.var 0), (.var 2)])])))
def opB : Expr := (.ctr 2 1 [(.call 23 [(.prim .u32_is_ne [(.prim .u32_and [(.var 1), (.u32 2)]), (.u32 0)]), (.prim .u32_is_ne [(.prim .u32_and [(.var 1), (.u32 1)]), (.u32 0)])]), (.var 0)])
def feedB : Expr := (.mat 3 (.var 1) [(1, (.mat 1 (.var 1) [(2, (.call 11 [(.var 1), (.var 2), (.var 0)]))]))])
def finB : Expr := (.mat 1 (.var 0) [(2, (.call 10 [(.var 1), (.var 0)]))])
def lgenB : Expr := (.mat 2 (.var 3) [(0, (.var 0)), (2, (.mat 3 (.var 1) [(1, (.call 26 [(.var 1), (.var 5), (.prim .u32_add [(.var 4), (.u32 1)]), (.call 27 [(.var 0), (.call 8 [(.var 5), (.var 4)]), (.var 3)])]))]))])
def lgenAtB : Expr := (.call 28 [(.call 12 [(.var 2)]), (.var 2), (.var 1), (.var 0)])
def lexpandB : Expr := (.mat 4 (.var 3) [(0, (.call 29 [(.prim .u32_to_nat [(.prim .u32_add [(.u32 1), (.prim .u32_and [(.var 1), (.u32 7)])])]), (.var 1), (.var 0)])), (0, (.call 30 [(.prim .u32_to_nat [(.prim .u32_add [(.u32 1), (.prim .u32_mod [(.var 1), (.u32 6)])])]), (.var 1), (.var 0)])), (0, (.call 31 [(.var 1), (.var 0)])), (0, (.call 24 [(.ctr 3 0 [(.var 2)]), (.var 0)]))])
def lidentB : Expr := (.natCase (.var 2) (.var 0) (.let_ (.call 7 [(.var 2)]) (.call 29 [(.var 1), (.var 0), (.call 24 [(.ctr 3 0 [(.prim .u32_add [(.u32 97), (.prim .u32_mod [(.var 0), (.u32 26)])])]), (.var 2)])])))
def lnumB : Expr := (.natCase (.var 2) (.var 0) (.let_ (.call 7 [(.var 2)]) (.call 30 [(.var 1), (.var 0), (.call 24 [(.ctr 3 0 [(.prim .u32_add [(.u32 48), (.prim .u32_mod [(.var 0), (.u32 10)])])]), (.var 2)])])))
def lopB : Expr := (.call 24 [(.call 23 [(.prim .u32_is_ne [(.prim .u32_and [(.var 1), (.u32 2)]), (.u32 0)]), (.prim .u32_is_ne [(.prim .u32_and [(.var 1), (.u32 1)]), (.u32 0)])]), (.var 0)])
def lineOld : Expr := (.call 6 [(.call 5 [(.call 3 []), (.call 4 [(.var 0)]), (.u32 0)]), (.ctr 1 0 [(.ctr 0 0 []), (.u32 0)])])
def lineNew : Expr := (.call 25 [(.call 26 [(.call 3 []), (.call 4 [(.var 0)]), (.u32 0), (.ctr 1 0 [(.ctr 0 0 []), (.u32 0)])])])
def runB : Expr := (.call 1 [(.var 1), (.var 0)])

structure Has (Pg : Prog) : Prop where
  f5 : Pg.fns[5]? = some ⟨"gen", [(.adt 2), .u32, .u32], (.adt 2), genB⟩
  f6 : Pg.fns[6]? = some ⟨"lex", [(.adt 2), (.adt 1)], .u32, lexB⟩
  f9 : Pg.fns[9]? = some ⟨"gen.at", [.u32, .u32, (.adt 2)], (.adt 2), genAtB⟩
  f13 : Pg.fns[13]? = some ⟨"expand", [(.adt 4), .u32, .u32, (.adt 2)], (.adt 2), expandB⟩
  f18 : Pg.fns[18]? = some ⟨"ident", [.nat, .u32, (.adt 2)], (.adt 2), identB⟩
  f19 : Pg.fns[19]? = some ⟨"num", [.nat, .u32, (.adt 2)], (.adt 2), numB⟩
  f20 : Pg.fns[20]? = some ⟨"op", [.u32, (.adt 2)], (.adt 2), opB⟩
  f24 : Pg.fns[24]? = some ⟨"lex.feed", [(.adt 3), (.adt 1)], (.adt 1), feedB⟩
  f25 : Pg.fns[25]? = some ⟨"lex.fin", [(.adt 1)], .u32, finB⟩
  f26 : Pg.fns[26]? = some ⟨"lex.gen", [(.adt 2), .u32, .u32, (.adt 1)], (.adt 1), lgenB⟩
  f27 : Pg.fns[27]? = some ⟨"lex.gen.at", [.u32, .u32, (.adt 1)], (.adt 1), lgenAtB⟩
  f28 : Pg.fns[28]? = some ⟨"lex.expand", [(.adt 4), .u32, .u32, (.adt 1)], (.adt 1), lexpandB⟩
  f29 : Pg.fns[29]? = some ⟨"lex.ident", [.nat, .u32, (.adt 1)], (.adt 1), lidentB⟩
  f30 : Pg.fns[30]? = some ⟨"lex.num", [.nat, .u32, (.adt 1)], (.adt 1), lnumB⟩
  f31 : Pg.fns[31]? = some ⟨"lex.op", [.u32, (.adt 1)], (.adt 1), lopB⟩


theorem one32 : (1 : Nat) % M32 = 1 := rfl
theorem zero32 : (0 : Nat) % M32 = 0 := rfl

attribute [local simp] Eval_var Eval_u32 Eval_nat Eval_prim Eval_ctr Eval_call_App Eval_let
  Eval_par Eval_natCase_var Eval_mat_var exists_EvalList_cons exists_EvalList_nil one32 zero32 and_assoc
attribute [local simp 1100] Eval_mat1_var1 Eval_mat1_var2

/-- lex(P(pre ++ [rest]), r) behaves like lex(rest, P'(pre ++ [r])). -/
def Fuses (Pg : Prog) (p p' : Nat) (pre : List Val) : Prop :=
  ∀ rest r v, (∃ s, App Pg p (pre ++ [rest]) s ∧ App Pg 6 [s, r] v) ↔
    (∃ r', App Pg p' (pre ++ [r]) r' ∧ App Pg 6 [rest, r'] v)

/-- the character computations of ident / num and the operator character -/
def CH (m b : Nat) (w c : Val) : Prop :=
  ∃ v2, Prim.eval .u32_mod [w, .u32 (m % M32)] = some v2 ∧ Prim.eval .u32_add [.u32 (b % M32), v2] = some c
def OPK (Pg : Prog) (t h : Val) : Prop :=
  ∃ v, (∃ v2, Prim.eval .u32_and [t, .u32 (2 % M32)] = some v2 ∧ Prim.eval .u32_is_ne [v2, .u32 0] = some v) ∧
    ∃ v2, (∃ v', Prim.eval .u32_and [t, .u32 1] = some v' ∧ Prim.eval .u32_is_ne [v', .u32 0] = some v2) ∧
      App Pg 23 [v, v2] h
def LEN (m : Nat) (t n : Val) : Prop :=
  ∃ v, (∃ v2, Prim.eval (if m = 7 then .u32_and else .u32_mod) [t, .u32 (m % M32)] = some v2 ∧
    Prim.eval .u32_add [.u32 1, v2] = some v) ∧ Prim.eval .u32_to_nat [v] = some n

section
variable {Pg : Prog} (H : Has Pg)
include H

theorem feed_iff (h r w : Val) : App Pg 24 [h, r] w ↔
    ∃ x, h = .ctr 0 [x] ∧ ∃ m acc, r = .ctr 0 [m, acc] ∧ App Pg 11 [m, x, acc] w := by
  rw [App_iff H.f24]; simp [feedB]

theorem fin_iff (r v : Val) : App Pg 25 [r] v ↔ ∃ m acc, r = .ctr 0 [m, acc] ∧ App Pg 10 [m, acc] v := by
  rw [App_iff H.f25]; simp [finB]

theorem lex_nil (r v : Val) : App Pg 6 [.ctr 0 [], r] v ↔ App Pg 25 [r] v := by
  rw [fin_iff H, App_iff H.f6]; simp [lexB]

theorem lex_cons (h t r v : Val) : App Pg 6 [.ctr 1 [h, t], r] v ↔ ∃ w, App Pg 24 [h, r] w ∧ App Pg 6 [t, w] v := by
  have e : App Pg 6 [.ctr 1 [h, t], r] v ↔ ∃ x, h = .ctr 0 [x] ∧ ∃ m acc, r = .ctr 0 [m, acc] ∧
      ∃ w, App Pg 11 [m, x, acc] w ∧ App Pg 6 [t, w] v := by
    rw [App_iff H.f6]; simp [lexB]
  rw [e]; simp only [feed_iff H]
  constructor
  · rintro ⟨x, rfl, m, acc, rfl, w, hs, hl⟩; exact ⟨w, ⟨x, rfl, m, acc, rfl, hs⟩, hl⟩
  · rintro ⟨w, ⟨x, rfl, m, acc, rfl, hs⟩, hl⟩; exact ⟨x, rfl, m, acc, rfl, w, hs, hl⟩

/-! ### ident / num -/

theorem ident_zero (t rest v : Val) : App Pg 18 [.nat 0, t, rest] v ↔ v = rest := by
  rw [App_iff H.f18]; simp [identB]; exact eq_comm
theorem lident_zero (t r v : Val) : App Pg 29 [.nat 0, t, r] v ↔ v = r := by
  rw [App_iff H.f29]; simp [lidentB]; exact eq_comm
theorem ident_succ (n : Nat) (t rest v : Val) : App Pg 18 [.nat (n + 1), t, rest] v ↔
    ∃ w, App Pg 7 [t] w ∧ ∃ h, (∃ c, CH 26 97 w c ∧ h = .ctr 0 [c]) ∧
      ∃ tl, App Pg 18 [.nat n, w, rest] tl ∧ v = .ctr 1 [h, tl] := by
  rw [App_iff H.f18]; simp [identB, CH]
theorem lident_succ (n : Nat) (t r v : Val) : App Pg 29 [.nat (n + 1), t, r] v ↔
    ∃ w, App Pg 7 [t] w ∧ ∃ r1, (∃ h, (∃ c, CH 26 97 w c ∧ h = .ctr 0 [c]) ∧ App Pg 24 [h, r] r1) ∧
      App Pg 29 [.nat n, w, r1] v := by
  rw [App_iff H.f29]; simp [lidentB, CH]
theorem num_zero (t rest v : Val) : App Pg 19 [.nat 0, t, rest] v ↔ v = rest := by
  rw [App_iff H.f19]; simp [numB]; exact eq_comm
theorem lnum_zero (t r v : Val) : App Pg 30 [.nat 0, t, r] v ↔ v = r := by
  rw [App_iff H.f30]; simp [lnumB]; exact eq_comm
theorem num_succ (n : Nat) (t rest v : Val) : App Pg 19 [.nat (n + 1), t, rest] v ↔
    ∃ w, App Pg 7 [t] w ∧ ∃ h, (∃ c, CH 10 48 w c ∧ h = .ctr 0 [c]) ∧
      ∃ tl, App Pg 19 [.nat n, w, rest] tl ∧ v = .ctr 1 [h, tl] := by
  rw [App_iff H.f19]; simp [numB, CH]
theorem lnum_succ (n : Nat) (t r v : Val) : App Pg 30 [.nat (n + 1), t, r] v ↔
    ∃ w, App Pg 7 [t] w ∧ ∃ r1, (∃ h, (∃ c, CH 10 48 w c ∧ h = .ctr 0 [c]) ∧ App Pg 24 [h, r] r1) ∧
      App Pg 30 [.nat n, w, r1] v := by
  rw [App_iff H.f30]; simp [lnumB, CH]

theorem ident_fuses : ∀ (n : Nat) (t : Val), Fuses Pg 18 29 [.nat n, t] := by
  intro n
  induction n with
  | zero =>
    intro t rest r v
    simp only [List.cons_append, List.nil_append, ident_zero H, lident_zero H]
    constructor
    · rintro ⟨s, rfl, h⟩; exact ⟨r, rfl, h⟩
    · rintro ⟨r', rfl, h⟩; exact ⟨rest, rfl, h⟩
  | succ n ih =>
    intro t rest r v
    simp only [List.cons_append, List.nil_append, ident_succ H, lident_succ H]
    constructor
    · rintro ⟨s, ⟨w, hw, h, ⟨c, hc, rfl⟩, tl, htl, rfl⟩, hlex⟩
      obtain ⟨r1, hfeed, hrest⟩ := (lex_cons H _ _ _ _).mp hlex
      obtain ⟨r2, h29, hfin⟩ := (ih w rest r1 v).mp ⟨tl, htl, hrest⟩
      exact ⟨r2, ⟨w, hw, r1, ⟨_, ⟨c, hc, rfl⟩, hfeed⟩, h29⟩, hfin⟩
    · rintro ⟨r2, ⟨w, hw, r1, ⟨h, ⟨c, hc, rfl⟩, hfeed⟩, h29⟩, hfin⟩
      obtain ⟨tl, htl, hrest⟩ := (ih w rest r1 v).mpr ⟨r2, h29, hfin⟩
      exact ⟨_, ⟨w, hw, _, ⟨c, hc, rfl⟩, tl, htl, rfl⟩, (lex_cons H _ _ _ _).mpr ⟨r1, hfeed, hrest⟩⟩

theorem num_fuses : ∀ (n : Nat) (t : Val), Fuses Pg 19 30 [.nat n, t] := by
  intro n
  induction n with
  | zero =>
    intro t rest r v
    simp only [List.cons_append, List.nil_append, num_zero H, lnum_zero H]
    constructor
    · rintro ⟨s, rfl, h⟩; exact ⟨r, rfl, h⟩
    · rintro ⟨r', rfl, h⟩; exact ⟨rest, rfl, h⟩
  | succ n ih =>
    intro t rest r v
    simp only [List.cons_append, List.nil_append, num_succ H, lnum_succ H]
    constructor
    · rintro ⟨s, ⟨w, hw, h, ⟨c, hc, rfl⟩, tl, htl, rfl⟩, hlex⟩
      obtain ⟨r1, hfeed, hrest⟩ := (lex_cons H _ _ _ _).mp hlex
      obtain ⟨r2, h30, hfin⟩ := (ih w rest r1 v).mp ⟨tl, htl, hrest⟩
      exact ⟨r2, ⟨w, hw, r1, ⟨_, ⟨c, hc, rfl⟩, hfeed⟩, h30⟩, hfin⟩
    · rintro ⟨r2, ⟨w, hw, r1, ⟨h, ⟨c, hc, rfl⟩, hfeed⟩, h30⟩, hfin⟩
      obtain ⟨tl, htl, hrest⟩ := (ih w rest r1 v).mpr ⟨r2, h30, hfin⟩
      exact ⟨_, ⟨w, hw, _, ⟨c, hc, rfl⟩, tl, htl, rfl⟩, (lex_cons H _ _ _ _).mpr ⟨r1, hfeed, hrest⟩⟩

/-- For a first argument that is not a Nat, both are stuck. -/
theorem ident_fuses' (d t : Val) : Fuses Pg 18 29 [d, t] := by
  cases d with
  | nat n => exact ident_fuses H n t
  | u32 k =>
    intro rest r v; simp only [List.cons_append, List.nil_append]
    constructor
    · rintro ⟨s, hs, _⟩; rw [App_iff H.f18] at hs; simp [identB] at hs
    · rintro ⟨r', hr, _⟩; rw [App_iff H.f29] at hr; simp [lidentB] at hr
  | ctr c fs =>
    intro rest r v; simp only [List.cons_append, List.nil_append]
    constructor
    · rintro ⟨s, hs, _⟩; rw [App_iff H.f18] at hs; simp [identB] at hs
    · rintro ⟨r', hr, _⟩; rw [App_iff H.f29] at hr; simp [lidentB] at hr

theorem num_fuses' (d t : Val) : Fuses Pg 19 30 [d, t] := by
  cases d with
  | nat n => exact num_fuses H n t
  | u32 k =>
    intro rest r v; simp only [List.cons_append, List.nil_append]
    constructor
    · rintro ⟨s, hs, _⟩; rw [App_iff H.f19] at hs; simp [numB] at hs
    · rintro ⟨r', hr, _⟩; rw [App_iff H.f30] at hr; simp [lnumB] at hr
  | ctr c fs =>
    intro rest r v; simp only [List.cons_append, List.nil_append]
    constructor
    · rintro ⟨s, hs, _⟩; rw [App_iff H.f19] at hs; simp [numB] at hs
    · rintro ⟨r', hr, _⟩; rw [App_iff H.f30] at hr; simp [lnumB] at hr

/-! ### op -/

theorem op_iff (t rest v : Val) : App Pg 20 [t, rest] v ↔ ∃ h, OPK Pg t h ∧ v = .ctr 1 [h, rest] := by
  rw [App_iff H.f20]; simp [opB, OPK]
theorem lop_iff (t r v : Val) : App Pg 31 [t, r] v ↔ ∃ h, OPK Pg t h ∧ App Pg 24 [h, r] v := by
  rw [App_iff H.f31]; simp [lopB, OPK]

theorem op_fuses (t : Val) : Fuses Pg 20 31 [t] := by
  intro rest r v
  simp only [List.cons_append, List.nil_append, op_iff H, lop_iff H]
  constructor
  · rintro ⟨s, ⟨h, hk, rfl⟩, hlex⟩
    obtain ⟨r1, hfeed, hrest⟩ := (lex_cons H _ _ _ _).mp hlex
    exact ⟨r1, ⟨h, hk, hfeed⟩, hrest⟩
  · rintro ⟨r1, ⟨h, hk, hfeed⟩, hrest⟩
    exact ⟨_, ⟨h, hk, rfl⟩, (lex_cons H _ _ _ _).mpr ⟨r1, hfeed, hrest⟩⟩

/-! ### expand -/

theorem expand_id (c t rest v : Val) : App Pg 13 [.ctr 0 [], c, t, rest] v ↔
    ∃ n, LEN 7 t n ∧ App Pg 18 [n, t, rest] v := by
  rw [App_iff H.f13]; simp [expandB, LEN]
theorem lexpand_id (c t r v : Val) : App Pg 28 [.ctr 0 [], c, t, r] v ↔
    ∃ n, LEN 7 t n ∧ App Pg 29 [n, t, r] v := by
  rw [App_iff H.f28]; simp [lexpandB, LEN]
theorem expand_nm (c t rest v : Val) : App Pg 13 [.ctr 1 [], c, t, rest] v ↔
    ∃ n, LEN 6 t n ∧ App Pg 19 [n, t, rest] v := by
  rw [App_iff H.f13]; simp [expandB, LEN]
theorem lexpand_nm (c t r v : Val) : App Pg 28 [.ctr 1 [], c, t, r] v ↔
    ∃ n, LEN 6 t n ∧ App Pg 30 [n, t, r] v := by
  rw [App_iff H.f28]; simp [lexpandB, LEN]
theorem expand_op (c t rest v : Val) : App Pg 13 [.ctr 2 [], c, t, rest] v ↔ App Pg 20 [t, rest] v := by
  rw [App_iff H.f13]; simp [expandB]
theorem lexpand_op (c t r v : Val) : App Pg 28 [.ctr 2 [], c, t, r] v ↔ App Pg 31 [t, r] v := by
  rw [App_iff H.f28]; simp [lexpandB]
theorem expand_lit (c t rest v : Val) : App Pg 13 [.ctr 3 [], c, t, rest] v ↔ v = .ctr 1 [.ctr 0 [c], rest] := by
  rw [App_iff H.f13]; simp [expandB]
theorem lexpand_lit (c t r v : Val) : App Pg 28 [.ctr 3 [], c, t, r] v ↔ App Pg 24 [.ctr 0 [c], r] v := by
  rw [App_iff H.f28]; simp [lexpandB]

theorem expand_bad (sl c t rest r v w : Val) (h0 : sl ≠ .ctr 0 []) (h1 : sl ≠ .ctr 1 [])
    (h2 : sl ≠ .ctr 2 []) (h3 : sl ≠ .ctr 3 []) :
    ¬ App Pg 13 [sl, c, t, rest] v ∧ ¬ App Pg 28 [sl, c, t, r] w := by
  constructor
  · intro h
    rw [App_iff H.f13] at h; simp [expandB] at h
    obtain ⟨tg, fs, rfl, body, harm, _⟩ := h
    match tg, fs, harm with
    | 0, [], _ => exact h0 rfl
    | 1, [], _ => exact h1 rfl
    | 2, [], _ => exact h2 rfl
    | 3, [], _ => exact h3 rfl
    | 0, _ :: _, harm => simp at harm
    | 1, _ :: _, harm => simp at harm
    | 2, _ :: _, harm => simp at harm
    | 3, _ :: _, harm => simp at harm
    | _ + 4, _, harm => simp at harm
  · intro h
    rw [App_iff H.f28] at h; simp [lexpandB] at h
    obtain ⟨tg, fs, rfl, body, harm, _⟩ := h
    match tg, fs, harm with
    | 0, [], _ => exact h0 rfl
    | 1, [], _ => exact h1 rfl
    | 2, [], _ => exact h2 rfl
    | 3, [], _ => exact h3 rfl
    | 0, _ :: _, harm => simp at harm
    | 1, _ :: _, harm => simp at harm
    | 2, _ :: _, harm => simp at harm
    | 3, _ :: _, harm => simp at harm
    | _ + 4, _, harm => simp at harm

theorem expand_fuses (sl c t : Val) : Fuses Pg 13 28 [sl, c, t] := by
  intro rest r v
  simp only [List.cons_append, List.nil_append]
  by_cases h0 : sl = .ctr 0 []
  · subst h0
    simp only [expand_id H, lexpand_id H]
    constructor
    · rintro ⟨s, ⟨n, hn, hs⟩, hlex⟩
      obtain ⟨r', h29, hr⟩ := (ident_fuses' H n t rest r v).mp ⟨s, hs, hlex⟩
      exact ⟨r', ⟨n, hn, h29⟩, hr⟩
    · rintro ⟨r', ⟨n, hn, h29⟩, hr⟩
      obtain ⟨s, hs, hlex⟩ := (ident_fuses' H n t rest r v).mpr ⟨r', h29, hr⟩
      exact ⟨s, ⟨n, hn, hs⟩, hlex⟩
  by_cases h1 : sl = .ctr 1 []
  · subst h1
    simp only [expand_nm H, lexpand_nm H]
    constructor
    · rintro ⟨s, ⟨n, hn, hs⟩, hlex⟩
      obtain ⟨r', h30, hr⟩ := (num_fuses' H n t rest r v).mp ⟨s, hs, hlex⟩
      exact ⟨r', ⟨n, hn, h30⟩, hr⟩
    · rintro ⟨r', ⟨n, hn, h30⟩, hr⟩
      obtain ⟨s, hs, hlex⟩ := (num_fuses' H n t rest r v).mpr ⟨r', h30, hr⟩
      exact ⟨s, ⟨n, hn, hs⟩, hlex⟩
  by_cases h2 : sl = .ctr 2 []
  · subst h2
    simp only [expand_op H, lexpand_op H]
    exact op_fuses H t rest r v
  by_cases h3 : sl = .ctr 3 []
  · subst h3
    simp only [expand_lit H, lexpand_lit H]
    constructor
    · rintro ⟨s, rfl, hlex⟩; exact (lex_cons H _ _ _ _).mp hlex
    · intro h; exact ⟨_, rfl, (lex_cons H _ _ _ _).mpr h⟩
  constructor
  · rintro ⟨s, hs, _⟩; exact ((expand_bad H sl c t rest r s s h0 h1 h2 h3).1 hs).elim
  · rintro ⟨r', hr, _⟩; exact ((expand_bad H sl c t rest r r' r' h0 h1 h2 h3).2 hr).elim

/-! ### gen.at -/

theorem genat_iff (c t rest v : Val) : App Pg 9 [c, t, rest] v ↔ ∃ sl, App Pg 12 [c] sl ∧ App Pg 13 [sl, c, t, rest] v := by
  rw [App_iff H.f9]; simp [genAtB]
theorem lgenat_iff (c t r v : Val) : App Pg 27 [c, t, r] v ↔ ∃ sl, App Pg 12 [c] sl ∧ App Pg 28 [sl, c, t, r] v := by
  rw [App_iff H.f27]; simp [lgenAtB]

theorem genat_fuses (c t : Val) : Fuses Pg 9 27 [c, t] := by
  intro rest r v
  simp only [List.cons_append, List.nil_append, genat_iff H, lgenat_iff H]
  constructor
  · rintro ⟨s, ⟨sl, hsl, hs⟩, hlex⟩
    obtain ⟨r', h28, hr⟩ := (expand_fuses H sl c t rest r v).mp ⟨s, hs, hlex⟩
    exact ⟨r', ⟨sl, hsl, h28⟩, hr⟩
  · rintro ⟨r', ⟨sl, hsl, h28⟩, hr⟩
    obtain ⟨s, hs, hlex⟩ := (expand_fuses H sl c t rest r v).mpr ⟨r', h28, hr⟩
    exact ⟨s, ⟨sl, hsl, hs⟩, hlex⟩

/-! ### gen (terminal producer) -/

theorem gen_nil (s k v : Val) : App Pg 5 [.ctr 0 [], s, k] v ↔ v = .ctr 0 [] := by
  rw [App_iff H.f5]; simp [genB]
theorem lgen_nil (s k r v : Val) : App Pg 26 [.ctr 0 [], s, k, r] v ↔ v = r := by
  rw [App_iff H.f26]; simp [lgenB]; exact eq_comm
theorem gen_cons (c u s k v : Val) : App Pg 5 [.ctr 1 [.ctr 0 [c], u], s, k] v ↔
    ∃ σ, App Pg 8 [s, k] σ ∧ ∃ tl, (∃ k1, Prim.eval .u32_add [k, .u32 1] = some k1 ∧ App Pg 5 [u, s, k1] tl) ∧
      App Pg 9 [c, σ, tl] v := by
  rw [App_iff H.f5]; simp [genB]
theorem lgen_cons (c u s k r v : Val) : App Pg 26 [.ctr 1 [.ctr 0 [c], u], s, k, r] v ↔
    ∃ k1, Prim.eval .u32_add [k, .u32 1] = some k1 ∧ ∃ r1, (∃ σ, App Pg 8 [s, k] σ ∧ App Pg 27 [c, σ, r] r1) ∧
      App Pg 26 [u, s, k1, r1] v := by
  rw [App_iff H.f26]; simp [lgenB]

theorem gen_bad (tpl s k r v w : Val) (h0 : tpl ≠ .ctr 0 []) (h1 : ∀ c u, tpl ≠ .ctr 1 [.ctr 0 [c], u]) :
    ¬ App Pg 5 [tpl, s, k] v ∧ ¬ App Pg 26 [tpl, s, k, r] w := by
  constructor
  · intro h
    rw [App_iff H.f5] at h; simp [genB] at h
    obtain ⟨tg, fs, rfl, body, harm, hb⟩ := h
    match tg, fs, harm with
    | 0, [], _ => exact h0 rfl
    | 1, [hd, u], harm =>
      simp at harm; subst harm; simp at hb
      obtain ⟨x, rfl, _⟩ := hb
      exact h1 x u rfl
    | 0, _ :: _, harm => simp at harm
    | 1, [], harm => simp at harm
    | 1, [_], harm => simp at harm
    | 1, _ :: _ :: _ :: _, harm => simp at harm
    | _ + 2, _, harm => simp at harm
  · intro h
    rw [App_iff H.f26] at h; simp [lgenB] at h
    obtain ⟨tg, fs, rfl, body, harm, hb⟩ := h
    match tg, fs, harm with
    | 0, [], _ => exact h0 rfl
    | 1, [hd, u], harm =>
      simp at harm; subst harm; simp at hb
      obtain ⟨x, rfl, _⟩ := hb
      exact h1 x u rfl
    | 0, _ :: _, harm => simp at harm
    | 1, [], harm => simp at harm
    | 1, [_], harm => simp at harm
    | 1, _ :: _ :: _ :: _, harm => simp at harm
    | _ + 2, _, harm => simp at harm

theorem gen_fuses (tpl : Val) : ∀ (s k r v : Val),
    (∃ str, App Pg 5 [tpl, s, k] str ∧ App Pg 6 [str, r] v) ↔
    (∃ r', App Pg 26 [tpl, s, k, r] r' ∧ App Pg 25 [r'] v) := by
  intro s k r v
  by_cases h0 : tpl = .ctr 0 []
  · subst h0
    simp only [gen_nil H, lgen_nil H]
    constructor
    · rintro ⟨str, rfl, hlex⟩; exact ⟨r, rfl, (lex_nil H r v).mp hlex⟩
    · rintro ⟨r', rfl, hf⟩; exact ⟨_, rfl, (lex_nil H r' v).mpr hf⟩
  by_cases h1 : ∃ c u, tpl = .ctr 1 [.ctr 0 [c], u]
  · obtain ⟨c, u, hu⟩ := h1
    have ih := gen_fuses u
    subst hu
    simp only [gen_cons H, lgen_cons H]
    constructor
    · rintro ⟨str, ⟨σ, hσ, tl, ⟨k1, hk1, htl⟩, hat⟩, hlex⟩
      obtain ⟨r1, h27, hrest⟩ := (genat_fuses H c σ tl r v).mp ⟨str, hat, hlex⟩
      obtain ⟨r', h26, hf⟩ := (ih s k1 r1 v).mp ⟨tl, htl, hrest⟩
      exact ⟨r', ⟨k1, hk1, r1, ⟨σ, hσ, h27⟩, h26⟩, hf⟩
    · rintro ⟨r', ⟨k1, hk1, r1, ⟨σ, hσ, h27⟩, h26⟩, hf⟩
      obtain ⟨tl, htl, hrest⟩ := (ih s k1 r1 v).mpr ⟨r', h26, hf⟩
      obtain ⟨str, hat, hlex⟩ := (genat_fuses H c σ tl r v).mpr ⟨r1, h27, hrest⟩
      exact ⟨str, ⟨σ, hσ, tl, ⟨k1, hk1, htl⟩, hat⟩, hlex⟩
  have h1' : ∀ c u, tpl ≠ .ctr 1 [.ctr 0 [c], u] := fun c u e => h1 ⟨c, u, e⟩
  constructor
  · rintro ⟨str, hs, _⟩; exact ((gen_bad H tpl s k r str str h0 h1').1 hs).elim
  · rintro ⟨r', hr, _⟩; exact ((gen_bad H tpl s k r r' r' h0 h1').2 hr).elim
termination_by sizeOf tpl
decreasing_by all_goals (subst hu; simp; omega)

/-! ### line -/

theorem line_fuses (ρ : Env) (v : Val) : Eval Pg ρ lineOld v ↔ Eval Pg ρ lineNew v := by
  simp only [lineOld, lineNew, Eval_call_App, exists_EvalList_cons, exists_EvalList_nil, Eval_ctr,
    Eval_u32, zero32, exists_eq_left]
  constructor
  · rintro ⟨str, ⟨tp, htp, σ, hσ, h5⟩, hlex⟩
    obtain ⟨r', h26, hf⟩ := (gen_fuses H tp σ (.u32 0) _ v).mp ⟨str, h5, hlex⟩
    exact ⟨r', ⟨tp, htp, σ, hσ, h26⟩, hf⟩
  · rintro ⟨r', ⟨tp, htp, σ, hσ, h26⟩, hf⟩
    obtain ⟨str, h5, hlex⟩ := (gen_fuses H tp σ (.u32 0) _ v).mpr ⟨r', h26, hf⟩
    exact ⟨str, ⟨tp, htp, σ, hσ, h5⟩, hlex⟩

end

/-! ## Transfer to the whole program -/

def lineFnOld : Fn := ⟨"line", [.u32], .u32, lineOld⟩
def lineFnNew : Fn := ⟨"line", [.u32], .u32, lineNew⟩
def runFnL : Fn := ⟨"run", [.nat, .u32], .u32, runB⟩

theorem hasP1 : Has P_1 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- P_1 with the old `line` put back: has every function both proofs need. -/
def Q' : Prog := { P_1 with fns := P_1.fns.set 2 lineFnOld }

theorem hasQ' : Has Q' := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem l0 : P_0.fns[2]? = some lineFnOld := rfl
theorem l1 : P_1.fns[2]? = some lineFnNew := rfl
theorem lq : Q'.fns[2]? = some lineFnOld := rfl
theorem r0 : P_0.findFn "run" = some (0, runFnL) := rfl
theorem r1 : P_1.findFn "run" = some (0, runFnL) := rfl
theorem r0' : P_0.fns[0]? = some runFnL := rfl
theorem r1' : P_1.fns[0]? = some runFnL := rfl

def sameFn (P Q : Prog) (i : Nat) : Bool :=
  match P.fns[i]?, Q.fns[i]? with
  | some f, some g => Fn.beq f g
  | _, _ => false

theorem sameFn_sound {P Q : Prog} {i : Nat} (h : sameFn P Q i = true) : Q.fns[i]? = P.fns[i]? := by
  unfold sameFn at h
  cases hp : P.fns[i]? with
  | none => simp [hp] at h
  | some f =>
    cases hq : Q.fns[i]? with
    | none => simp [hp, hq] at h
    | some g => simp only [hp, hq] at h; rw [Fn.eq_of_beq h]

theorem same01 : (List.range 24).all (fun i => i == 2 || sameFn P_0 P_1 i) = true := by decide

theorem agree01 (i : Nat) (hi : i < 24) (h2 : i ≠ 2) : P_1.fns[i]? = P_0.fns[i]? := by
  have := List.all_eq_true.mp same01 i (List.mem_range.mpr hi)
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with h | h
  · exact absurd h h2
  · exact sameFn_sound h

theorem len0 : P_0.fns.length = 24 := rfl

theorem simPQ : ∀ {ρ : Env} {e : Expr} {v : Val}, Eval P_0 ρ e v → Eval P_1 ρ e v :=
  simulate (fun i fp hp => by
    have hi : i < 24 := by
      rcases Nat.lt_or_ge i 24 with h | h
      · exact h
      · rw [List.getElem?_eq_none (by rw [len0]; exact h)] at hp; cases hp
    by_cases h2 : i = 2
    · subst h2; rw [l0] at hp; cases hp
      exact ⟨lineFnNew, l1, rfl, fun ρ v he => (line_fuses hasP1 ρ v).mp he⟩
    · exact ⟨fp, by rw [agree01 i hi h2, hp], rfl, fun _ _ he => he⟩)

theorem simPQ' : ∀ {ρ : Env} {e : Expr} {v : Val}, Eval P_1 ρ e v → Eval Q' ρ e v :=
  simulate (fun i fp hp => by
    by_cases h2 : i = 2
    · subst h2; rw [l1] at hp; cases hp
      exact ⟨lineFnOld, lq, rfl, fun ρ v he => (line_fuses hasQ' ρ v).mpr he⟩
    · refine ⟨fp, ?_, rfl, fun _ _ he => he⟩
      show (P_1.fns.set 2 lineFnOld)[i]? = some fp
      rw [List.getElem?_set_ne (Ne.symm h2)]; exact hp)

def S24 : Nat → Bool := fun i => decide (i < 24)
theorem S24_bound : ∀ i, 24 ≤ i → S24 i = false := by intro i h; simp [S24]; omega
theorem agreeQ0 : agreeOnB S24 24 Q' P_0 = true := by decide
theorem closedRun : callsIn S24 runB = true := by decide

theorem simQ'P {ρ : Env} {v : Val} (h : Eval Q' ρ runB v) : Eval P_0 ρ runB v :=
  simulate_on S24 (agreeOnB_sound S24_bound agreeQ0) closedRun h

theorem step : Equiv ctx P_0 P_1 := by
  refine ⟨wfEntryB_sound (by decide), wfEntryB_sound (by decide), ?_⟩
  intro args _ v
  have he : ctx.entry = "run" := rfl
  rw [Run_iff, Run_iff, he]
  constructor
  · rintro ⟨i, fn, hf, hfn, hl, hb⟩
    rw [r0] at hf; simp only [Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    exact ⟨0, _, r1, r1', hl, simPQ hb⟩
  · rintro ⟨i, fn, hf, hfn, hl, hb⟩
    rw [r1] at hf; simp only [Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    exact ⟨0, _, r0, r0', hl, simQ'P (simPQ' hb)⟩

/-- The lemma step's goal, exactly as generated by the verifier. -/
theorem fusion : goal_0 := ⟨Stamp.mk _, step⟩

end Submission.Lexer
