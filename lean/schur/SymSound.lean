import Mathlib
import Schur.SchurStatement
import Schur.SymValid
import Std.Tactic.BVDecide.LRAT.Checker

namespace Schur

open Std.Sat

def symExprInt (e : Expr) (U : Nat) : Int :=
  Int.ofNat e.a * Int.ofNat U + e.b

def symExprValue (e : Expr) (U : Nat) : Nat :=
  (symExprInt e U).toNat

def symColorOfNat (color : Nat) : Fin 3 :=
  ⟨color % 3, Nat.mod_lt _ (by omega)⟩

theorem symFin3_color_cases (color : Fin 3) :
    color = symColorOfNat 0 ∨ color = symColorOfNat 1 ∨
      color = symColorOfNat 2 := by
  fin_cases color <;> simp [symColorOfNat]

theorem symColorOfNat_ne_01 : symColorOfNat 0 ≠ symColorOfNat 1 := by
  decide

theorem symColorOfNat_ne_02 : symColorOfNat 0 ≠ symColorOfNat 2 := by
  decide

theorem symColorOfNat_ne_12 : symColorOfNat 1 ≠ symColorOfNat 2 := by
  decide

def symReachable (N : Nat) (χ : Nat → Fin 3) (color j value : Nat) : Prop :=
  ∃ l : List Nat, l.length = j ∧
    (∀ x ∈ l, 1 ≤ x ∧ x ≤ N ∧ χ x = symColorOfNat color) ∧
    l.sum = value

def symPadded (U N : Nat) (χ : Nat → Fin 3) (c j value : Nat) : Prop :=
  χ c = symColorOfNat 2 ∧
    ∃ l : List Nat, l.length = j ∧
      (∀ x ∈ l, 1 ≤ x ∧ x ≤ N ∧ χ x = symColorOfNat 2) ∧
      (U - 1 - j) * c + l.sum = value

noncomputable def symReachBool
    (N : Nat) (χ : Nat → Fin 3) (color j value : Nat) : Bool := by
  classical
  exact decide (symReachable N χ color j value)

noncomputable def symPaddedBool
    (U N : Nat) (χ : Nat → Fin 3) (c j value : Nat) : Bool := by
  classical
  exact decide (symPadded U N χ c j value)

theorem symReachBool_true_iff {N color j value : Nat}
    {χ : Nat → Fin 3} :
    symReachBool N χ color j value = true ↔
      symReachable N χ color j value := by
  classical
  simp [symReachBool]

theorem symReachBool_false_iff {N color j value : Nat}
    {χ : Nat → Fin 3} :
    symReachBool N χ color j value = false ↔
      ¬ symReachable N χ color j value := by
  classical
  simp [symReachBool]

theorem symPaddedBool_true_iff {U N c j value : Nat}
    {χ : Nat → Fin 3} :
    symPaddedBool U N χ c j value = true ↔
      symPadded U N χ c j value := by
  classical
  simp [symPaddedBool]

theorem symPaddedBool_false_iff {U N c j value : Nat}
    {χ : Nat → Fin 3} :
    symPaddedBool U N χ c j value = false ↔
      ¬ symPadded U N χ c j value := by
  classical
  simp [symPaddedBool]

noncomputable def symAssignment
    (s t B J U N : Nat) (χ : Nat → Fin 3) (v : Nat) : Bool := by
  classical
  exact match decodeVar s t B J v with
  | none => false
  | some info =>
    match info.kind with
    | 0 => decide (χ (symExprValue info.expr U) = symColorOfNat info.color)
    | 1 => decide (symReachable N χ info.color info.j
        (symExprValue info.expr U))
    | 2 => decide (symPadded U N χ info.c info.j
        (symExprValue info.expr U))
    | _ => false

theorem litIs_true {s t B J kind color c j : Nat} {e : Expr}
    {v : Nat} {sign : Bool}
    (h : litIs s t B J (v, sign) kind color c j e true = true) :
    inE s t B e = true ∧ sign = true ∧
      decodeVar s t B J v = some ⟨kind, color, c, j, e⟩ := by
  cases hd : decodeVar s t B J v with
  | none =>
      simp [litIs, hd] at h
  | some info =>
      simp [litIs, hd] at h
      rcases h with ⟨he, hs, hi⟩
      exact ⟨he, hs, by simpa [hd] using hi⟩

theorem symAssignment_col {s t B J U N color : Nat}
    (χ : Nat → Fin 3) {v : Nat} {e : Expr}
    (hdecode : decodeVar s t B J v = some ⟨0, color, 0, 0, e⟩) :
    symAssignment s t B J U N χ v =
      decide (χ (symExprValue e U) = symColorOfNat color) := by
  simp [symAssignment, hdecode]

theorem symAssignment_col_info {s t B J U N : Nat}
    (χ : Nat → Fin 3) {v : Nat} {info : VarInfo}
    (hdecode : decodeVar s t B J v = some info)
    (hkind : info.kind = 0) :
    symAssignment s t B J U N χ v =
      decide (χ (symExprValue info.expr U) =
        symColorOfNat info.color) := by
  cases info with
  | mk kind color c j expr =>
    cases kind <;> simp_all [symAssignment, hdecode]

theorem symAssignment_col_info_true_iff {s t B J U N : Nat}
    (χ : Nat → Fin 3) {v : Nat} {info : VarInfo}
    (hdecode : decodeVar s t B J v = some info)
    (hkind : info.kind = 0) :
    symAssignment s t B J U N χ v = true ↔
      χ (symExprValue info.expr U) = symColorOfNat info.color := by
  rw [symAssignment_col_info χ hdecode hkind]
  simp

theorem symAssignment_col_true_iff {s t B J U N color : Nat}
    (χ : Nat → Fin 3) {v : Nat} {e : Expr}
    (hdecode : decodeVar s t B J v = some ⟨0, color, 0, 0, e⟩) :
    symAssignment s t B J U N χ v = true ↔
      χ (symExprValue e U) = symColorOfNat color := by
  rw [symAssignment_col χ hdecode]
  simp

theorem symAssignment_col_false_iff {s t B J U N color : Nat}
    (χ : Nat → Fin 3) {v : Nat} {e : Expr}
    (hdecode : decodeVar s t B J v = some ⟨0, color, 0, 0, e⟩) :
    symAssignment s t B J U N χ v = false ↔
      χ (symExprValue e U) ≠ symColorOfNat color := by
  rw [symAssignment_col χ hdecode]
  simp

theorem symAssignment_reach {s t B J U N color j : Nat}
    (χ : Nat → Fin 3) {v : Nat} {e : Expr}
    (hdecode : decodeVar s t B J v = some ⟨1, color, 0, j, e⟩) :
    symAssignment s t B J U N χ v =
    symReachBool N χ color j (symExprValue e U) := by
  classical
  simp [symAssignment, hdecode, symReachBool]

theorem symAssignment_reach_info {s t B J U N : Nat}
    (χ : Nat → Fin 3) {v : Nat} {info : VarInfo}
    (hdecode : decodeVar s t B J v = some info)
    (hkind : info.kind = 1) :
    symAssignment s t B J U N χ v =
      symReachBool N χ info.color info.j
        (symExprValue info.expr U) := by
  classical
  cases info with
  | mk kind color c j expr =>
    cases kind <;> simp_all [symAssignment, hdecode, symReachBool]

theorem symAssignment_reach_info_true_iff {s t B J U N : Nat}
    (χ : Nat → Fin 3) {v : Nat} {info : VarInfo}
    (hdecode : decodeVar s t B J v = some info)
    (hkind : info.kind = 1) :
    symAssignment s t B J U N χ v = true ↔
      symReachable N χ info.color info.j (symExprValue info.expr U) := by
  rw [symAssignment_reach_info χ hdecode hkind]
  exact symReachBool_true_iff

theorem symAssignment_reach_true_iff {s t B J U N color j : Nat}
    (χ : Nat → Fin 3) {v : Nat} {e : Expr}
    (hdecode : decodeVar s t B J v = some ⟨1, color, 0, j, e⟩) :
    symAssignment s t B J U N χ v = true ↔
      symReachable N χ color j (symExprValue e U) := by
  rw [symAssignment_reach χ hdecode]
  exact symReachBool_true_iff

theorem symAssignment_reach_false_iff {s t B J U N color j : Nat}
    (χ : Nat → Fin 3) {v : Nat} {e : Expr}
    (hdecode : decodeVar s t B J v = some ⟨1, color, 0, j, e⟩) :
    symAssignment s t B J U N χ v = false ↔
      ¬ symReachable N χ color j (symExprValue e U) := by
  rw [symAssignment_reach χ hdecode]
  exact symReachBool_false_iff

theorem symAssignment_padding {s t B J U N c j : Nat}
    (χ : Nat → Fin 3) {v : Nat} {e : Expr}
    (hdecode : decodeVar s t B J v = some ⟨2, 2, c, j, e⟩) :
    symAssignment s t B J U N χ v =
    symPaddedBool U N χ c j (symExprValue e U) := by
  classical
  simp [symAssignment, hdecode, symPaddedBool]

theorem symAssignment_padding_info {s t B J U N : Nat}
    (χ : Nat → Fin 3) {v : Nat} {info : VarInfo}
    (hdecode : decodeVar s t B J v = some info)
    (hkind : info.kind = 2) :
    symAssignment s t B J U N χ v =
      symPaddedBool U N χ info.c info.j
        (symExprValue info.expr U) := by
  classical
  cases info with
  | mk kind color c j expr =>
    cases kind <;> simp_all [symAssignment, hdecode, symPaddedBool]

theorem symAssignment_padding_info_true_iff
    {s t B J U N : Nat} (χ : Nat → Fin 3)
    {v : Nat} {info : VarInfo}
    (hdecode : decodeVar s t B J v = some info)
    (hkind : info.kind = 2) :
    symAssignment s t B J U N χ v = true ↔
      symPadded U N χ info.c info.j (symExprValue info.expr U) := by
  rw [symAssignment_padding_info χ hdecode hkind]
  exact symPaddedBool_true_iff

theorem symAssignment_padding_true_iff
    {s t B J U N c j : Nat} (χ : Nat → Fin 3)
    {v : Nat} {e : Expr}
    (hdecode : decodeVar s t B J v = some ⟨2, 2, c, j, e⟩) :
    symAssignment s t B J U N χ v = true ↔
      symPadded U N χ c j (symExprValue e U) := by
  rw [symAssignment_padding χ hdecode]
  exact symPaddedBool_true_iff

theorem symAssignment_padding_false_iff
    {s t B J U N c j : Nat} (χ : Nat → Fin 3)
    {v : Nat} {e : Expr}
    (hdecode : decodeVar s t B J v = some ⟨2, 2, c, j, e⟩) :
    symAssignment s t B J U N χ v = false ↔
      ¬ symPadded U N χ c j (symExprValue e U) := by
  rw [symAssignment_padding χ hdecode]
  exact symPaddedBool_false_iff

theorem symTwoLiteral_implication_eval (a : Nat → Bool) (x y : Nat)
    (h : a x = true → a y = true) :
    CNF.Clause.eval a [(x, false), (y, true)] = true := by
  cases hx : a x <;> cases hy : a y <;>
    simp [CNF.Clause.eval, hx, hy]
  case true.false =>
    have h' := h hx
    rw [hy] at h'
    contradiction

theorem symThreeLiteral_implication_eval (a : Nat → Bool)
    (x y z : Nat)
    (h : a x = true → a y = true → a z = true) :
    CNF.Clause.eval a [(x, false), (y, false), (z, true)] = true := by
  cases hx : a x <;> cases hy : a y <;> cases hz : a z <;>
    simp [CNF.Clause.eval, hx, hy, hz]
  case true.true.false =>
    have h' := h hx hy
    rw [hz] at h'
    contradiction

theorem symTwoNegative_eval (a : Nat → Bool) (x y : Nat)
    (h : ¬ (a x = true ∧ a y = true)) :
    CNF.Clause.eval a [(x, false), (y, false)] = true := by
  cases hx : a x <;> cases hy : a y <;>
    simp [CNF.Clause.eval, hx, hy] <;>
    try exact False.elim (h ⟨hx, hy⟩)

theorem symThreePositive_eval (a : Nat → Bool) (x y z : Nat)
    (h : a x = true ∨ a y = true ∨ a z = true) :
    CNF.Clause.eval a [(x, true), (y, true), (z, true)] = true := by
  rcases h with hx | hy | hz
  · simp [CNF.Clause.eval, hx]
  · simp [CNF.Clause.eval, hy]
  · simp [CNF.Clause.eval, hz]

private theorem symBool_eq_true_or_false (b : Bool) :
    b = true ∨ b = false := by
  by_cases hb : b = true
  · exact Or.inl hb
  · right
    cases b <;> simp_all

private theorem symValidColorClause_satisfied
    {s t B J U N : Nat} {χ : Nat → Fin 3}
    {c : CNF.Clause Nat}
    (hvalid : validColorClause s t B J c = true) :
    CNF.Clause.eval (symAssignment s t B J U N χ) c = true := by
  cases c with
  | nil => simp [validColorClause] at hvalid
  | cons lit0 rest0 =>
    rcases lit0 with ⟨v0, p0⟩
    cases rest0 with
    | nil => simp [validColorClause] at hvalid
    | cons lit1 rest1 =>
      rcases lit1 with ⟨v1, p1⟩
      cases rest1 with
      | nil =>
        rcases symBool_eq_true_or_false p0 with hp0 | hp0
        · simp [validColorClause, hp0] at hvalid
        · rcases symBool_eq_true_or_false p1 with hp1 | hp1
          · simp [validColorClause, hp0, hp1] at hvalid
          · simp [validColorClause, hp0, hp1] at hvalid
            cases hd0 : decodeVar s t B J v0 with
            | none => simp [validColorClause, hp0, hp1, hd0] at hvalid
            | some x =>
              cases hd1 : decodeVar s t B J v1 with
              | none => simp [validColorClause, hp0, hp1, hd0, hd1] at hvalid
              | some y =>
                simp [validColorClause, hp0, hp1, hd0, hd1] at hvalid
                rcases hvalid with ⟨hrest, hxcolor⟩
                rcases hrest with ⟨hrest, _⟩
                rcases hrest with ⟨hrest, hxyexpr⟩
                rcases hrest with ⟨hxkind, hykind⟩
                have hcolorCases :
                    ((x.color = 0 ∧ y.color = 1) ∨
                      (x.color = 0 ∧ y.color = 2)) ∨
                    (x.color = 1 ∧ y.color = 2) := by
                  simpa using hxcolor
                have hnot : ¬
                    (symAssignment s t B J U N χ v0 = true ∧
                     symAssignment s t B J U N χ v1 = true) := by
                  intro ⟨hax, hay⟩
                  have hxχ :
                      χ (symExprValue x.expr U) =
                        symColorOfNat x.color := by
                    have := hax
                    rw [symAssignment_col_info χ hd0 hxkind] at this
                    exact of_decide_eq_true this
                  have hyχ :
                      χ (symExprValue y.expr U) =
                        symColorOfNat y.color := by
                    have := hay
                    rw [symAssignment_col_info χ hd1 hykind] at this
                    exact of_decide_eq_true this
                  rw [← hxyexpr] at hyχ
                  rcases hcolorCases with h01or02 | h12
                  · rcases h01or02 with ⟨hxc, hyc⟩ | ⟨hxc, hyc⟩
                    · have hxχ' : χ (symExprValue x.expr U) =
                        symColorOfNat 0 := by simpa [hxc] using hxχ
                      have hyχ' : χ (symExprValue x.expr U) =
                        symColorOfNat 1 := by simpa [hyc] using hyχ
                      exact symColorOfNat_ne_01 (hxχ'.symm.trans hyχ')
                    · have hxχ' : χ (symExprValue x.expr U) =
                        symColorOfNat 0 := by simpa [hxc] using hxχ
                      have hyχ' : χ (symExprValue x.expr U) =
                        symColorOfNat 2 := by simpa [hyc] using hyχ
                      exact symColorOfNat_ne_02 (hxχ'.symm.trans hyχ')
                  · rcases h12 with ⟨hxc, hyc⟩
                    have hxχ' : χ (symExprValue x.expr U) =
                        symColorOfNat 1 := by simpa [hxc] using hxχ
                    have hyχ' : χ (symExprValue x.expr U) =
                        symColorOfNat 2 := by simpa [hyc] using hyχ
                    exact symColorOfNat_ne_12 (hxχ'.symm.trans hyχ')
                simpa [hp0, hp1] using
                  symTwoNegative_eval _ _ _ hnot
      | cons lit2 rest2 =>
        rcases lit2 with ⟨v2, p2⟩
        cases rest2 with
        | nil =>
          rcases symBool_eq_true_or_false p0 with hp0 | hp0
          · rcases symBool_eq_true_or_false p1 with hp1 | hp1
            · rcases symBool_eq_true_or_false p2 with hp2 | hp2
              · simp [validColorClause, hp0, hp1, hp2] at hvalid
                cases hd0 : decodeVar s t B J v0 with
                | none =>
                  simp [validColorClause, hp0, hp1, hp2, hd0] at hvalid
                | some x =>
                  cases x with
                  | mk kind color cx jx ex =>
                    simp [validColorClause, hp0, hp1, hp2, hd0] at hvalid
                    rcases hvalid with ⟨hrest, hcolor⟩
                    rcases hrest with ⟨hrest, hkind⟩
                    rcases hrest with ⟨hLit1, hLit2⟩
                    have ⟨he, _, hd1⟩ := litIs_true hLit1
                    have ⟨_, _, hd2⟩ := litIs_true hLit2
                    have hA0 :
                        symAssignment s t B J U N χ v0 = true ↔
                          χ (symExprValue ex U) =
                            symColorOfNat 0 := by
                      have hk : kind = 0 := by simpa using hkind
                      have hc : color = 0 := by simpa using hcolor
                      rw [symAssignment_col_info χ hd0 hk]
                      simp [hc]
                    have hA1 :
                        symAssignment s t B J U N χ v1 = true ↔
                          χ (symExprValue ex U) =
                            symColorOfNat 1 := by
                      rw [symAssignment_col_true_iff χ hd1]
                    have hA2 :
                        symAssignment s t B J U N χ v2 = true ↔
                          χ (symExprValue ex U) =
                            symColorOfNat 2 := by
                      rw [symAssignment_col_true_iff χ hd2]
                    have hsome := symFin3_color_cases (χ (symExprValue ex U))
                    have hdisj :
                        symAssignment s t B J U N χ v0 = true ∨
                        symAssignment s t B J U N χ v1 = true ∨
                        symAssignment s t B J U N χ v2 = true := by
                      rcases hsome with h0 | h1 | h2
                      · exact Or.inl (hA0.mpr h0)
                      · exact Or.inr (Or.inl (hA1.mpr h1))
                      · exact Or.inr (Or.inr (hA2.mpr h2))
                    simpa [hp0, hp1, hp2] using
                      symThreePositive_eval _ _ _ _ hdisj
              · simp [validColorClause, hp0, hp1, hp2] at hvalid
            · simp [validColorClause, hp0, hp1] at hvalid
          · simp [validColorClause, hp0] at hvalid
        | cons _ _ => simp [validColorClause] at hvalid

theorem symExprInt_add (x y : Expr) (U : Nat) :
    symExprInt (symExprAdd x y) U = symExprInt x U + symExprInt y U := by
  simp [symExprInt, symExprAdd]
  ring

theorem symExprInt_replace (x y : Expr) (c U : Nat) :
    symExprInt (symExprReplace x c y) U =
      symExprInt x U - Int.ofNat c + symExprInt y U := by
  simp [symExprInt, symExprReplace]
  ring

theorem symExprValue_bounds {s t B J U : Nat} (hM : 1 ≤ symM s t)
    (hU : symU0 s t B J ≤ U) {e : Expr}
    (he : inE s t B e = true) :
    1 ≤ symExprValue e U ∧ symExprValue e U ≤ symM s t * U - 1 := by
  have he' :
      e.a ≤ symM s t ∧
        -Int.ofNat B ≤ e.b ∧ e.b ≤ Int.ofNat B ∧
        (e.a = 0 → 1 ≤ e.b) ∧
        (e.a = symM s t → e.b ≤ -1) := by
    change decide
      (e.a ≤ symM s t ∧
        -Int.ofNat B ≤ e.b ∧ e.b ≤ Int.ofNat B ∧
        (e.a = 0 → 1 ≤ e.b) ∧
        (e.a = symM s t → e.b ≤ -1)) = true at he
    exact of_decide_eq_true he
  rcases he' with ⟨ha, hblo, hbhi, hzero, htop⟩
  have hUB : B + 1 ≤ U := by
    unfold symU0 at hU
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _) hU))
  have hUpos : 1 ≤ U := by omega
  have hMU : U ≤ symM s t * U := by
    calc
      U = 1 * U := by simp
      _ ≤ symM s t * U := Nat.mul_le_mul_right U hM
  have hMUp : 1 ≤ symM s t * U := by omega
  have hcastUB : Int.ofNat B + 1 ≤ Int.ofNat U := by
    simpa using (Int.ofNat_le.mpr hUB)
  have hcastMU : Int.ofNat U ≤ Int.ofNat (symM s t * U) := by
    exact Int.ofNat_le.mpr hMU
  have hcastMUp : 1 ≤ Int.ofNat (symM s t * U) := by
    simpa using (Int.ofNat_le.mpr hMUp)
  have hprodLower (ha0 : e.a ≠ 0) :
      Int.ofNat U ≤ Int.ofNat (e.a * U) := by
    have hmul : 1 * U ≤ e.a * U :=
      Nat.mul_le_mul_right U (by omega)
    simpa using (Int.ofNat_le.mpr hmul)
  have hprodUpper (haM : e.a < symM s t) :
      Int.ofNat (e.a * U) + Int.ofNat U ≤
        Int.ofNat (symM s t * U) := by
    have hmul : (e.a + 1) * U ≤ symM s t * U :=
      Nat.mul_le_mul_right U (by omega)
    have hmul' : e.a * U + U ≤ symM s t * U := by
      simpa [Nat.add_mul] using hmul
    have hcast : Int.ofNat (e.a * U + U) ≤
        Int.ofNat (symM s t * U) := by
      exact Int.ofNat_le.mpr hmul'
    simpa using hcast
  have hraw : 1 ≤ symExprInt e U ∧
      symExprInt e U ≤ Int.ofNat (symM s t * U) - 1 := by
    by_cases ha0 : e.a = 0
    · have hlo := hzero ha0
      constructor
      · simpa [symExprInt, ha0] using hlo
      · have hbupper : e.b ≤ Int.ofNat U - 1 := by omega
        have hbupper' : e.b ≤ Int.ofNat (symM s t * U) - 1 := by
          omega
        simpa [symExprInt, ha0] using hbupper'
    · by_cases haM : e.a = symM s t
      · have hlo : 1 ≤ Int.ofNat (symM s t * U) + e.b := by
          have hb : -(Int.ofNat B) ≤ e.b := hblo
          omega
        have hhi : Int.ofNat (symM s t * U) + e.b ≤
            Int.ofNat (symM s t * U) - 1 := by
          have hb := htop haM
          omega
        constructor
        · simpa [symExprInt, haM, Nat.cast_mul] using hlo
        · simpa [symExprInt, haM, Nat.cast_mul] using hhi
      · have haPos : 1 ≤ e.a := by omega
        have haLt : e.a < symM s t := by omega
        have hlower := hprodLower ha0
        have hupper := hprodUpper haLt
        have hlo : 1 ≤ Int.ofNat (e.a * U) + e.b := by
          have hb := hblo
          omega
        have hhi : Int.ofNat (e.a * U) + e.b ≤
            Int.ofNat (symM s t * U) - 1 := by
          have hb := hbhi
          omega
        constructor
        · simpa [symExprInt, Nat.cast_mul] using hlo
        · simpa [symExprInt, Nat.cast_mul] using hhi
  have hnonneg : 0 ≤ symExprInt e U := by omega
  have hvalue : Int.ofNat (symExprValue e U) = symExprInt e U :=
    Int.toNat_of_nonneg hnonneg
  constructor
  · have : (1 : Int) ≤ Int.ofNat (symExprValue e U) := by
      rw [hvalue]
      exact hraw.1
    exact Int.ofNat_le.mp this
  · have hNat : Int.ofNat (symExprValue e U) ≤
      Int.ofNat (symM s t * U - 1) := by
      rw [hvalue]
      have hsubAdd : Int.ofNat (symM s t * U - 1) + 1 =
          Int.ofNat (symM s t * U) := by
        calc
          Int.ofNat (symM s t * U - 1) + 1 =
              Int.ofNat (symM s t * U - 1 + 1) := by simp
          _ = Int.ofNat (symM s t * U) := by
            rw [Nat.sub_add_cancel hMUp]
      have hsub : Int.ofNat (symM s t * U) - 1 =
          Int.ofNat (symM s t * U - 1) := by omega
      rw [← hsub]
      exact hraw.2
    exact Int.ofNat_le.mp hNat

theorem symExprInt_pos_of_inE {s t B J U : Nat} (hM : 1 ≤ symM s t)
    (hU : symU0 s t B J ≤ U) {e : Expr}
    (he : inE s t B e = true) : 0 < symExprInt e U := by
  have hv := symExprValue_bounds hM hU he
  apply Int.pos_iff_toNat_pos.mpr
  simpa [symExprValue] using (show 0 < symExprValue e U by omega)

theorem symExprValue_add {s t B J U : Nat} (hM : 1 ≤ symM s t)
    (hU : symU0 s t B J ≤ U) {x y : Expr}
    (hx : inE s t B x = true) (hy : inE s t B y = true) :
    symExprValue (symExprAdd x y) U =
      symExprValue x U + symExprValue y U := by
  have hxpos := symExprInt_pos_of_inE hM hU hx
  have hypos := symExprInt_pos_of_inE hM hU hy
  unfold symExprValue
  rw [symExprInt_add, Int.toNat_add (by omega) (by omega)]

theorem symExprValue_replace {s t B J U c : Nat} (hM : 1 ≤ symM s t)
    (hU : symU0 s t B J ≤ U) {x y : Expr}
    (hx : inE s t B x = true) (hy : inE s t B y = true)
    (hcx : c ≤ symExprValue x U) :
    symExprValue (symExprReplace x c y) U =
      symExprValue x U - c + symExprValue y U := by
  have hxpos := symExprInt_pos_of_inE hM hU hx
  have hypos := symExprInt_pos_of_inE hM hU hy
  have hsubpos : 0 ≤ symExprInt x U - Int.ofNat c := by
    have hxval : Int.ofNat (symExprValue x U) = symExprInt x U :=
      Int.toNat_of_nonneg (by omega)
    rw [← hxval]
    have hcx' : Int.ofNat c ≤ Int.ofNat (symExprValue x U) :=
      Int.ofNat_le.mpr hcx
    exact Int.sub_nonneg.mpr hcx'
  have hsub :
      (symExprInt x U - Int.ofNat c).toNat =
        symExprValue x U - c := by
    change (symExprInt x U - (c : Int)).toNat = _
    calc
      (symExprInt x U - (c : Int)).toNat =
          (symExprInt x U).toNat - (c : Int).toNat :=
        Int.toNat_sub'' (by omega) (Int.natCast_nonneg c)
      _ = symExprValue x U - c := by simp [symExprValue]
  unfold symExprValue
  rw [symExprInt_replace]
  rw [Int.toNat_add (by omega) (by omega), hsub]
  simp [symExprValue]

theorem symReachable_extend {N color j value y : Nat}
    {χ : Nat → Fin 3}
    (hreach : symReachable N χ color j value)
    (hy : 1 ≤ y ∧ y ≤ N ∧ χ y = symColorOfNat color) :
    symReachable N χ color (j + 1) (value + y) := by
  rcases hreach with ⟨l, hlen, hmem, hsum⟩
  refine ⟨l ++ [y], ?_, ?_, ?_⟩
  · simp [hlen]
  · intro z hz
    simp only [List.mem_append, List.mem_singleton] at hz
    rcases hz with hz | rfl
    · exact hmem z hz
    · exact hy
  · simp [List.sum_append, hsum]

theorem symReachable_extend_expr {s t B J U N color j : Nat}
    {χ : Nat → Fin 3} {x y z : Expr}
    (hM : 1 ≤ symM s t) (hU : symU0 s t B J ≤ U)
    (hx : inE s t B x = true) (hy : inE s t B y = true)
    (hz : z = symExprAdd x y)
    (hreach : symReachable N χ color j (symExprValue x U))
    (hcolor : χ (symExprValue y U) = symColorOfNat color)
    (hbounds : 1 ≤ symExprValue y U ∧ symExprValue y U ≤ N) :
    symReachable N χ color (j + 1) (symExprValue z U) := by
  rw [hz, symExprValue_add hM hU hx hy]
  exact symReachable_extend hreach ⟨hbounds.1, hbounds.2, hcolor⟩

theorem symReachable_singleton {N color value : Nat}
    {χ : Nat → Fin 3}
    (hvalue : 1 ≤ value ∧ value ≤ N)
    (hcolor : χ value = symColorOfNat color) :
    symReachable N χ color 1 value := by
  refine ⟨[value], by simp, ?_, by simp⟩
  intro x hx
  simp only [List.mem_singleton] at hx
  subst x
  exact ⟨hvalue.1, hvalue.2, hcolor⟩

theorem symExprValue_const {U c : Nat} :
    symExprValue ⟨0, Int.ofNat c⟩ U = c := by
  simp [symExprValue, symExprInt]

theorem symMonoSol_of_padded {U N c j value : Nat}
    {χ : Nat → Fin 3}
    (hj : j ≤ U - 1)
    (hcRange : 1 ≤ c ∧ c ≤ N)
    (hpad : symPadded U N χ c j value)
    (hvalue : 1 ≤ value ∧ value ≤ N)
    (hcolor : χ value = symColorOfNat 2) :
    MonoSol N U χ (symColorOfNat 2) := by
  rcases hpad with ⟨hc, l, hlen, hmem, hsum⟩
  let l' := List.replicate (U - 1 - j) c ++ l
  have hlen' : l'.length = U - 1 := by
    simp [l', hlen]
    omega
  have hmem' : ∀ x ∈ l', 1 ≤ x ∧ x ≤ N ∧ χ x = symColorOfNat 2 := by
    intro x hx
    simp only [l', List.mem_append] at hx
    rcases hx with hx | hx
    · simp only [List.mem_replicate] at hx
      rcases hx with ⟨_, heq⟩
      subst x
      exact ⟨hcRange.1, hcRange.2, hc⟩
    · exact hmem x hx
  have hsum' : l'.sum = value := by
    dsimp [l']
    simp only [List.sum_append, List.sum_replicate_nat]
    exact hsum
  refine ⟨l', hlen', hmem', ?_, ?_, ?_⟩
  · rw [hsum']
    exact hvalue.1
  · rw [hsum']
    exact hvalue.2
  · rw [hsum']
    exact hcolor

theorem symExprValue_c_padding {U c : Nat} (hU : 1 ≤ U) :
    symExprValue ⟨c, -Int.ofNat c⟩ U = (U - 1) * c := by
  have hUcast : Int.ofNat U = Int.ofNat (U - 1) + 1 := by
    simpa using (congrArg Int.ofNat (Nat.sub_add_cancel hU)).symm
  have hraw :
      symExprInt ⟨c, -Int.ofNat c⟩ U =
        Int.ofNat ((U - 1) * c) := by
    simp only [symExprInt]
    rw [hUcast]
    calc
      Int.ofNat c * (Int.ofNat (U - 1) + 1) + -Int.ofNat c =
          Int.ofNat (U - 1) * Int.ofNat c := by ring
      _ = Int.ofNat ((U - 1) * c) :=
        (Int.natCast_mul (U - 1) c).symm
  unfold symExprValue
  rw [hraw]
  rfl

theorem symPadded_initial {U N c : Nat} {χ : Nat → Fin 3}
    (hcolor : χ c = symColorOfNat 2) :
    symPadded U N χ c 0 ((U - 1) * c) := by
  simp [symPadded, hcolor]

theorem symPadded_extend {U N c j value y : Nat} {χ : Nat → Fin 3}
    (hpad : symPadded U N χ c j value)
    (hy : 1 ≤ y ∧ y ≤ N ∧ χ y = symColorOfNat 2)
    (hj : j + 1 ≤ U - 1) :
    symPadded U N χ c (j + 1) (value - c + y) := by
  rcases hpad with ⟨hcolor, l, hlen, hmem, hvalue⟩
  refine ⟨hcolor, l ++ [y], ?_, ?_, ?_⟩
  · simp [hlen]
  · intro z hz
    simp only [List.mem_append, List.mem_singleton] at hz
    rcases hz with hz | rfl
    · exact hmem z hz
    · exact hy
  · rw [List.sum_append]
    simp only [List.sum_singleton]
    have hcount : U - 1 - j = (U - 1 - (j + 1)) + 1 := by omega
    have hvalue' :
        ((U - 1 - (j + 1)) + 1) * c + l.sum = value := by
      simpa only [hcount] using hvalue
    have hvalue'' :
        (U - 1 - (j + 1)) * c + c + l.sum = value := by
      simpa [Nat.add_mul] using hvalue'
    have hvalue''' :
        value = ((U - 1 - (j + 1)) * c + l.sum) + c := by
      calc
        value = (U - 1 - (j + 1)) * c + c + l.sum :=
          hvalue''.symm
        _ = ((U - 1 - (j + 1)) * c + l.sum) + c := by omega
    have hsub :
        value - c = (U - 1 - (j + 1)) * c + l.sum := by
      rw [hvalue''']
      omega
    rw [hsub]
    omega

theorem symPadded_extend_expr {s t B J U N c j : Nat}
    {χ : Nat → Fin 3} {x y z : Expr}
    (hM : 1 ≤ symM s t) (hU : symU0 s t B J ≤ U)
    (hj : j + 1 ≤ J)
    (hx : inE s t B x = true) (hy : inE s t B y = true)
    (hz : z = symExprReplace x c y)
    (hpad : symPadded U N χ c j (symExprValue x U))
    (hcolor : χ (symExprValue y U) = symColorOfNat 2)
    (hby : 1 ≤ symExprValue y U ∧ symExprValue y U ≤ N) :
    symPadded U N χ c (j + 1) (symExprValue z U) := by
  have hpadCopy := hpad
  have hJ : J + 1 ≤ U := by
    unfold symU0 at hU
    exact (le_max_right _ _).trans
      ((le_max_left _ _).trans ((le_max_left _ _).trans hU))
  have hremain : 1 ≤ U - 1 - j := by omega
  have hcvalue : c ≤ symExprValue x U := by
    rcases hpad with ⟨_, l, _, _, hsum⟩
    calc
      c = 1 * c := by simp
      _ ≤ (U - 1 - j) * c := Nat.mul_le_mul_right c hremain
      _ ≤ (U - 1 - j) * c + l.sum := Nat.le_add_right _ _
      _ = symExprValue x U := hsum
  have hstep : j + 1 ≤ U - 1 := by omega
  have hpad' := symPadded_extend hpadCopy
      ⟨hby.1, hby.2, hcolor⟩ hstep
  rw [hz, symExprValue_replace hM hU hx hy hcvalue]
  exact hpad'

private theorem symMonoSol_of_reachable_aux {N k color value : Nat}
    {χ : Nat → Fin 3}
    (hreach : symReachable N χ color (k - 1) value)
    (hvalue : 1 ≤ value ∧ value ≤ N)
    (hcolor : χ value = symColorOfNat color) :
    MonoSol N k χ (symColorOfNat color) := by
  rcases hreach with ⟨l, hlen, hmem, hsum⟩
  have htarget : χ l.sum = symColorOfNat color := by
    rw [hsum]
    exact hcolor
  refine ⟨l, hlen, hmem, ?_, ?_, htarget⟩
  · simpa [hsum] using hvalue.1
  · simpa [hsum] using hvalue.2

private theorem symValidReachClause_satisfied
    {s t B J U N : Nat} {χ : Nat → Fin 3}
    (hM : 1 ≤ symM s t) (hU : symU0 s t B J ≤ U)
    (hN : N = symM s t * U - 1)
    (hNo0 : ¬ MonoSol N s χ 0) (hNo1 : ¬ MonoSol N t χ 1)
    {c : CNF.Clause Nat}
    (hvalid : validReachClause s t B J c = true) :
    CNF.Clause.eval (symAssignment s t B J U N χ) c = true := by
  cases c with
  | nil => simp [validReachClause] at hvalid
  | cons lit0 rest0 =>
    rcases lit0 with ⟨v0, p0⟩
    cases rest0 with
    | nil => simp [validReachClause] at hvalid
    | cons lit1 rest1 =>
      rcases lit1 with ⟨v1, p1⟩
      cases rest1 with
      | nil =>
        rcases symBool_eq_true_or_false p0 with hp0 | hp0
        · simp [validReachClause, hp0] at hvalid
        · rcases symBool_eq_true_or_false p1 with hp1 | hp1
          ·
            cases hd0 : decodeVar s t B J v0 with
            | none => simp [validReachClause, hp0, hp1, hd0] at hvalid
            | some x =>
              cases hd1 : decodeVar s t B J v1 with
              | none =>
                simp [validReachClause, hp0, hp1, hd0, hd1] at hvalid
              | some y =>
                simp [validReachClause, hp0, hp1, hd0, hd1] at hvalid
                rcases hvalid with ⟨hrest, hyE⟩
                rcases hrest with ⟨hrest, hxE⟩
                rcases hrest with ⟨hrest, _⟩
                rcases hrest with ⟨hrest, hxyexpr⟩
                rcases hrest with ⟨hrest, hyj⟩
                rcases hrest with ⟨hrest, hykind⟩
                rcases hrest with ⟨hxkind, hxycolor⟩
                have himp :
                    symAssignment s t B J U N χ v0 = true →
                      symAssignment s t B J U N χ v1 = true := by
                  intro hcol
                  have hχx :
                      χ (symExprValue x.expr U) =
                        symColorOfNat x.color :=
                    (symAssignment_col_info_true_iff χ hd0 hxkind).mp hcol
                  have hχy :
                      χ (symExprValue y.expr U) =
                        symColorOfNat y.color := by
                    rw [← hxyexpr, ← hxycolor]
                    exact hχx
                  have hbounds : 1 ≤ symExprValue y.expr U ∧
                      symExprValue y.expr U ≤ N := by
                    have hb := symExprValue_bounds hM hU hyE
                    rw [hN]
                    exact hb
                  have hreach := symReachable_singleton hbounds hχy
                  apply (symAssignment_reach_info_true_iff χ hd1 hykind).2
                  simpa [hyj] using hreach
                simpa [hp0, hp1] using
                  symTwoLiteral_implication_eval _ _ _ himp
          ·
            cases hd0 : decodeVar s t B J v0 with
            | none => simp [validReachClause, hp0, hp1, hd0] at hvalid
            | some x =>
              cases hd1 : decodeVar s t B J v1 with
              | none =>
                simp [validReachClause, hp0, hp1, hd0, hd1] at hvalid
              | some y =>
                simp [validReachClause, hp0, hp1, hd0, hd1] at hvalid
                rcases hvalid with ⟨hrest, hyE⟩
                rcases hrest with ⟨hrest, hxE⟩
                rcases hrest with ⟨hrest, hterminal⟩
                rcases hrest with ⟨hrest, hxyexpr⟩
                rcases hrest with ⟨hrest, hxycolor⟩
                rcases hrest with ⟨hxkind, hykind⟩
                have hterminal' :
                    (x.color = 0 ∧ x.j = s - 1) ∨
                    (x.color = 1 ∧ x.j = t - 1) := by
                  simpa using hterminal
                have hnot : ¬
                    (symAssignment s t B J U N χ v0 = true ∧
                     symAssignment s t B J U N χ v1 = true) := by
                  intro ⟨hr, hc⟩
                  have hreach :
                      symReachable N χ x.color x.j
                        (symExprValue x.expr U) :=
                    (symAssignment_reach_info_true_iff χ hd0 hxkind).mp hr
                  have hχy :
                      χ (symExprValue y.expr U) =
                        symColorOfNat y.color :=
                    (symAssignment_col_info_true_iff χ hd1 hykind).mp hc
                  have hχx :
                      χ (symExprValue x.expr U) =
                        symColorOfNat x.color := by
                    rw [← hxyexpr, ← hxycolor] at hχy
                    exact hχy
                  have hbounds : 1 ≤ symExprValue x.expr U ∧
                      symExprValue x.expr U ≤ N := by
                    have hb := symExprValue_bounds hM hU hxE
                    rw [hN]
                    exact hb
                  rcases hterminal' with ⟨hcolor, hlevel⟩ |
                    ⟨hcolor, hlevel⟩
                  · have hsol := symMonoSol_of_reachable_aux
                        (by simpa [hlevel] using hreach)
                        hbounds (by simpa [hcolor] using hχx)
                    exact hNo0 (by
                      simpa [hcolor, symColorOfNat] using hsol)
                  · have hsol := symMonoSol_of_reachable_aux
                        (by simpa [hlevel] using hreach)
                        hbounds (by simpa [hcolor] using hχx)
                    exact hNo1 (by
                      simpa [hcolor, symColorOfNat] using hsol)
                simpa [hp0, hp1] using
                  symTwoNegative_eval _ _ _ hnot
      | cons lit2 rest2 =>
        rcases lit2 with ⟨v2, p2⟩
        cases rest2 with
        | nil =>
          rcases symBool_eq_true_or_false p0 with hp0 | hp0
          · simp [validReachClause, hp0] at hvalid
          · rcases symBool_eq_true_or_false p1 with hp1 | hp1
            · simp [validReachClause, hp0, hp1] at hvalid
            · rcases symBool_eq_true_or_false p2 with hp2 | hp2
              ·
                cases hd0 : decodeVar s t B J v0 with
                | none =>
                  simp [validReachClause, hp0, hp1, hp2, hd0] at hvalid
                | some x =>
                  cases hd1 : decodeVar s t B J v1 with
                  | none =>
                    simp [validReachClause, hp0, hp1, hp2, hd0, hd1] at hvalid
                  | some y =>
                    cases hd2 : decodeVar s t B J v2 with
                    | none =>
                      simp [validReachClause, hp0, hp1, hp2,
                        hd0, hd1, hd2] at hvalid
                    | some z =>
                      simp [validReachClause, hp0, hp1, hp2,
                        hd0, hd1, hd2] at hvalid
                      rcases hvalid with ⟨hrest, hzE⟩
                      rcases hrest with ⟨hrest, hyE⟩
                      rcases hrest with ⟨hrest, hxE⟩
                      rcases hrest with ⟨hrest, hexpr⟩
                      rcases hrest with ⟨hrest, _⟩
                      rcases hrest with ⟨hrest, hlevel⟩
                      rcases hrest with ⟨hrest, hyzcolor⟩
                      rcases hrest with ⟨hrest, hxycolor⟩
                      rcases hrest with ⟨hrest, hzkind⟩
                      rcases hrest with ⟨hxkind, hykind⟩
                      have himp :
                          symAssignment s t B J U N χ v0 = true →
                            symAssignment s t B J U N χ v1 = true →
                              symAssignment s t B J U N χ v2 = true := by
                        intro hr hc
                        have hreach :
                            symReachable N χ x.color x.j
                              (symExprValue x.expr U) :=
                          (symAssignment_reach_info_true_iff χ hd0 hxkind).mp hr
                        have hχy :
                            χ (symExprValue y.expr U) =
                              symColorOfNat y.color :=
                          (symAssignment_col_info_true_iff χ hd1 hykind).mp hc
                        have hχy' :
                            χ (symExprValue y.expr U) =
                              symColorOfNat x.color := by
                          simpa [hxycolor] using hχy
                        have hbounds : 1 ≤ symExprValue y.expr U ∧
                            symExprValue y.expr U ≤ N := by
                          have hb := symExprValue_bounds hM hU hyE
                          rw [hN]
                          exact hb
                        have hreach' := symReachable_extend_expr
                          hM hU hxE hyE hexpr hreach hχy' hbounds
                        apply (symAssignment_reach_info_true_iff
                          χ hd2 hzkind).2
                        simpa [hxycolor, hyzcolor, hlevel, hexpr] using hreach'
                      simpa [hp0, hp1, hp2] using
                        symThreeLiteral_implication_eval _ _ _ _ himp
              · simp [validReachClause, hp0, hp1, hp2] at hvalid
        | cons _ _ => simp [validReachClause] at hvalid

private theorem symU0_ge_J {s t B J U : Nat}
    (hU : symU0 s t B J ≤ U) : J + 1 ≤ U := by
  unfold symU0 at hU
  exact (le_max_right _ _).trans
    ((le_max_left _ _).trans ((le_max_left _ _).trans hU))

private theorem symU0_ge_four {s t B J U : Nat}
    (hU : symU0 s t B J ≤ U) : 4 ≤ U := by
  unfold symU0 at hU
  exact (le_max_right _ _).trans hU

private theorem symConstant_le_N {s t B J U c : Nat}
    (_hM : 1 ≤ symM s t) (hU : symU0 s t B J ≤ U)
    (hc : c ≤ symM s t) :
    c ≤ symM s t * U - 1 := by
  have hU2 : 2 ≤ U := le_trans (by omega) (symU0_ge_four hU)
  have hmul0 : symM s t * 2 ≤ symM s t * U :=
    Nat.mul_le_mul_left _ hU2
  have hmul : symM s t + symM s t ≤ symM s t * U := by
    simpa [Nat.mul_two] using hmul0
  have hbound : symM s t ≤ symM s t * U - 1 := by omega
  exact le_trans hc hbound

private theorem symValidPaddingClause_satisfied
    {s t B J U N : Nat} {χ : Nat → Fin 3}
    (hM : 1 ≤ symM s t) (hU : symU0 s t B J ≤ U)
    (hN : N = symM s t * U - 1)
    (hNo2 : ¬ MonoSol N U χ 2)
    {c : CNF.Clause Nat}
    (hvalid : validPaddingClause s t B J c = true) :
    CNF.Clause.eval (symAssignment s t B J U N χ) c = true := by
  cases c with
  | nil => simp [validPaddingClause] at hvalid
  | cons lit0 rest0 =>
    rcases lit0 with ⟨v0, p0⟩
    cases rest0 with
    | nil => simp [validPaddingClause] at hvalid
    | cons lit1 rest1 =>
      rcases lit1 with ⟨v1, p1⟩
      cases rest1 with
      | nil =>
        rcases symBool_eq_true_or_false p0 with hp0 | hp0
        · simp [validPaddingClause, hp0] at hvalid
        · rcases symBool_eq_true_or_false p1 with hp1 | hp1
          ·
            cases hd0 : decodeVar s t B J v0 with
            | none => simp [validPaddingClause, hp0, hp1, hd0] at hvalid
            | some x =>
              cases hd1 : decodeVar s t B J v1 with
              | none =>
                simp [validPaddingClause, hp0, hp1, hd0, hd1] at hvalid
              | some y =>
                simp [validPaddingClause, hp0, hp1, hd0, hd1] at hvalid
                rcases hvalid with ⟨hrest, hyE⟩
                rcases hrest with ⟨hrest, hxE⟩
                rcases hrest with ⟨hrest, hchi⟩
                rcases hrest with ⟨hrest, hclo⟩
                rcases hrest with ⟨hrest, hyexpr⟩
                rcases hrest with ⟨hrest, hyj⟩
                rcases hrest with ⟨hrest, hyc⟩
                rcases hrest with ⟨hrest, hycolor⟩
                rcases hrest with ⟨hrest, hykind⟩
                rcases hrest with ⟨hrest, hxbhi⟩
                rcases hrest with ⟨hrest, hxblo⟩
                rcases hrest with ⟨hrest, hxa⟩
                rcases hrest with ⟨hxkind, hxcolor⟩
                have himp :
                    symAssignment s t B J U N χ v0 = true →
                      symAssignment s t B J U N χ v1 = true := by
                  intro hcol
                  have hχx :
                      χ (symExprValue x.expr U) =
                        symColorOfNat x.color :=
                    (symAssignment_col_info_true_iff χ hd0 hxkind).mp hcol
                  have hvalue :
                      symExprValue x.expr U = x.expr.b.toNat := by
                    simp [symExprValue, symExprInt, hxa]
                  have hχc : χ y.c = symColorOfNat 2 := by
                    have hxy : symExprValue x.expr U = y.c := by
                      simpa [hyc] using hvalue
                    simpa [hxcolor, hxy] using hχx
                  have hinitial :=
                    symPadded_initial (U := U) (N := N) hχc
                  have hvalueY :
                      symExprValue y.expr U = (U - 1) * y.c := by
                    rw [hyexpr, ← hyc]
                    have hcast : Int.ofNat y.c = x.expr.b := by
                      rw [hyc]
                      exact Int.toNat_of_nonneg (by omega)
                    have hmax : max x.expr.b 0 = Int.ofNat y.c := by
                      rw [max_eq_left (show 0 ≤ x.expr.b by omega)]
                      exact hcast.symm
                    rw [hmax]
                    have hU1 : 1 ≤ U :=
                      le_trans (by decide : 1 ≤ 4) (symU0_ge_four hU)
                    exact symExprValue_c_padding (U := U) (c := y.c)
                      hU1
                  have hpadY :
                      symPadded U N χ y.c 0
                        (symExprValue y.expr U) := by
                    rw [hvalueY]
                    exact hinitial
                  exact (symAssignment_padding_info_true_iff
                    χ hd1 hykind).2 (by simpa [hyj] using hpadY)
                simpa [hp0, hp1] using
                  symTwoLiteral_implication_eval _ _ _ himp
          ·
            cases hd0 : decodeVar s t B J v0 with
            | none => simp [validPaddingClause, hp0, hp1, hd0] at hvalid
            | some x =>
              cases hd1 : decodeVar s t B J v1 with
              | none =>
                simp [validPaddingClause, hp0, hp1, hd0, hd1] at hvalid
              | some y =>
                simp [validPaddingClause, hp0, hp1, hd0, hd1] at hvalid
                rcases hvalid with ⟨hrest, hyE⟩
                rcases hrest with ⟨hrest, hxE⟩
                rcases hrest with ⟨hrest, hxyexpr⟩
                rcases hrest with ⟨hrest, hxj⟩
                rcases hrest with ⟨hrest, hxcHi⟩
                rcases hrest with ⟨hrest, hxcLo⟩
                rcases hrest with ⟨hrest, hxcolor⟩
                rcases hrest with ⟨hrest, hycolor⟩
                rcases hrest with ⟨hxkind, hykind⟩
                have hnot : ¬
                    (symAssignment s t B J U N χ v0 = true ∧
                     symAssignment s t B J U N χ v1 = true) := by
                  intro ⟨hp, hc⟩
                  have hpad :
                      symPadded U N χ x.c x.j
                        (symExprValue x.expr U) :=
                    (symAssignment_padding_info_true_iff χ hd0 hxkind).mp hp
                  have hχy :
                      χ (symExprValue y.expr U) =
                        symColorOfNat y.color :=
                    (symAssignment_col_info_true_iff χ hd1 hykind).mp hc
                  have hχx :
                      χ (symExprValue x.expr U) =
                        symColorOfNat 2 := by
                    simpa [← hxyexpr, hycolor, hxcolor] using hχy
                  have hbounds : 1 ≤ symExprValue x.expr U ∧
                      symExprValue x.expr U ≤ N := by
                    have hb := symExprValue_bounds hM hU hxE
                    rw [hN]
                    exact hb
                  have hcRange : 1 ≤ x.c ∧ x.c ≤ N := by
                    constructor
                    · exact hxcLo
                    · rw [hN]
                      exact symConstant_le_N hM hU hxcHi
                  have hj : x.j ≤ U - 1 := by
                    have hJU := symU0_ge_J hU
                    omega
                  have hsol := symMonoSol_of_padded
                    hj hcRange hpad hbounds hχx
                  exact hNo2 (by simpa [symColorOfNat] using hsol)
                simpa [hp0, hp1] using
                  symTwoNegative_eval _ _ _ hnot
      | cons lit2 rest2 =>
        rcases lit2 with ⟨v2, p2⟩
        cases rest2 with
        | nil =>
          rcases symBool_eq_true_or_false p0 with hp0 | hp0
          · simp [validPaddingClause, hp0] at hvalid
          · rcases symBool_eq_true_or_false p1 with hp1 | hp1
            · simp [validPaddingClause, hp0, hp1] at hvalid
            · rcases symBool_eq_true_or_false p2 with hp2 | hp2
              ·
                cases hd0 : decodeVar s t B J v0 with
                | none =>
                  simp [validPaddingClause, hp0, hp1, hp2, hd0] at hvalid
                | some x =>
                  cases hd1 : decodeVar s t B J v1 with
                  | none =>
                    simp [validPaddingClause, hp0, hp1, hp2,
                      hd0, hd1] at hvalid
                  | some y =>
                    cases hd2 : decodeVar s t B J v2 with
                    | none =>
                      simp [validPaddingClause, hp0, hp1, hp2,
                        hd0, hd1, hd2] at hvalid
                    | some z =>
                      simp [validPaddingClause, hp0, hp1, hp2,
                        hd0, hd1, hd2] at hvalid
                      rcases hvalid with ⟨hrest, hzE⟩
                      rcases hrest with ⟨hrest, hyE⟩
                      rcases hrest with ⟨hrest, hxE⟩
                      rcases hrest with ⟨hrest, hexpr⟩
                      rcases hrest with ⟨hrest, hjhi⟩
                      rcases hrest with ⟨hrest, hjlo⟩
                      rcases hrest with ⟨hrest, hlevel⟩
                      rcases hrest with ⟨hrest, hxzc⟩
                      rcases hrest with ⟨hrest, hxcolor⟩
                      rcases hrest with ⟨hrest, hycolor⟩
                      rcases hrest with ⟨hrest, hzkind⟩
                      rcases hrest with ⟨hxkind, hykind⟩
                      have himp :
                          symAssignment s t B J U N χ v0 = true →
                            symAssignment s t B J U N χ v1 = true →
                              symAssignment s t B J U N χ v2 = true := by
                        intro hp hc
                        have hpad :
                            symPadded U N χ x.c x.j
                              (symExprValue x.expr U) :=
                          (symAssignment_padding_info_true_iff χ hd0 hxkind).mp hp
                        have hχy :
                            χ (symExprValue y.expr U) =
                              symColorOfNat 2 := by
                          simpa [hycolor] using
                            (symAssignment_col_info_true_iff
                              χ hd1 hykind).mp hc
                        have hbounds : 1 ≤ symExprValue y.expr U ∧
                            symExprValue y.expr U ≤ N := by
                          have hb := symExprValue_bounds hM hU hyE
                          rw [hN]
                          exact hb
                        have hj : x.j + 1 ≤ J := by omega
                        have hpad' := symPadded_extend_expr
                          hM hU hj hxE hyE hexpr hpad hχy hbounds
                        exact (symAssignment_padding_info_true_iff
                          χ hd2 hzkind).2
                          (by simpa [hxzc, hlevel, hexpr] using hpad')
                      simpa [hp0, hp1, hp2] using
                        symThreeLiteral_implication_eval _ _ _ _ himp
              · simp [validPaddingClause, hp0, hp1, hp2] at hvalid
        | cons _ _ => simp [validPaddingClause] at hvalid

theorem symMonoSol_of_reachable {N k color value : Nat}
    {χ : Nat → Fin 3}
    (hreach : symReachable N χ color (k - 1) value)
    (hvalue : 1 ≤ value ∧ value ≤ N)
    (hcolor : χ value = symColorOfNat color) :
    MonoSol N k χ (symColorOfNat color) := by
  rcases hreach with ⟨l, hlen, hmem, hsum⟩
  have htarget : χ l.sum = symColorOfNat color := by
    rw [hsum]
    exact hcolor
  refine ⟨l, hlen, hmem, ?_, ?_, htarget⟩
  · simpa [hsum] using hvalue.1
  · simpa [hsum] using hvalue.2

theorem symValidClause_satisfied
    {s t B J U N : Nat} {χ : Nat → Fin 3}
    (hM : 1 ≤ symM s t) (hU : symU0 s t B J ≤ U)
    (hN : N = symM s t * U - 1)
    (hNo0 : ¬ MonoSol N s χ 0) (hNo1 : ¬ MonoSol N t χ 1)
    (hNo2 : ¬ MonoSol N U χ 2)
    {c : CNF.Clause Nat} (hvalid : validClause s t B J c = true) :
    CNF.Clause.eval (symAssignment s t B J U N χ) c = true := by
  have hfamilies :
      (validColorClause s t B J c = true ∨
        validReachClause s t B J c = true) ∨
        validPaddingClause s t B J c = true := by
    simpa [validClause, Bool.or_eq_true] using hvalid
  rcases hfamilies with hleft | hpadding
  · rcases hleft with hcolor | hreach
    · exact symValidColorClause_satisfied hcolor
    · exact symValidReachClause_satisfied
        hM hU hN hNo0 hNo1 hreach
  · exact symValidPaddingClause_satisfied
      hM hU hN hNo2 hpadding

theorem symForces_of_check
    {s t B J U : Nat}
    (hM : 1 ≤ symM s t) (hU : symU0 s t B J ≤ U)
    (hAllValid :
      (symCNF s t B J).clauses.all (validClause s t B J) = true)
    (cert : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck :
      Std.Tactic.BVDecide.LRAT.check cert (symCNF s t B J) = true) :
    Forces (symM s t * U - 1) s t U := by
  intro χ
  by_cases hNo0 : MonoSol (symM s t * U - 1) s χ 0
  · exact Or.inl hNo0
  by_cases hNo1 : MonoSol (symM s t * U - 1) t χ 1
  · exact Or.inr (Or.inl hNo1)
  by_cases hNo2 : MonoSol (symM s t * U - 1) U χ 2
  · exact Or.inr (Or.inr hNo2)
  have hunsat :=
    Std.Tactic.BVDecide.LRAT.check_sound cert (symCNF s t B J) hcheck
  have hsat :
      CNF.eval (symAssignment s t B J U
        (symM s t * U - 1) χ) (symCNF s t B J) = true := by
    change (symCNF s t B J).clauses.all
      (fun c => CNF.Clause.eval
        (symAssignment s t B J U (symM s t * U - 1) χ) c) = true
    apply Array.all_eq_true.mpr
    intro i hi
    let c := (symCNF s t B J).clauses[i]
    have hvalid : validClause s t B J c = true :=
      (Array.all_eq_true.mp hAllValid) i hi
    exact symValidClause_satisfied hM hU rfl hNo0 hNo1 hNo2 hvalid
  have hfalse := hunsat (symAssignment s t B J U
    (symM s t * U - 1) χ)
  rw [hsat] at hfalse
  cases hfalse

theorem symForces_of_check_forall
    {s t B J : Nat}
    (hM : 1 ≤ symM s t)
    (hAllValid :
      (symCNF s t B J).clauses.all (validClause s t B J) = true)
    (cert : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck :
      Std.Tactic.BVDecide.LRAT.check cert (symCNF s t B J) = true) :
    ∀ U, symU0 s t B J ≤ U →
      Forces (symM s t * U - 1) s t U := by
  intro U hU
  exact symForces_of_check hM hU hAllValid cert hcheck

end Schur
