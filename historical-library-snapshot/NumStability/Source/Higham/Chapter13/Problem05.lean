import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Analysis.MatrixAlgebra

/-!
# Source.Higham.Chapter13.Problem05

This module formalizes the source-facing Chapter 13 statements for
`Problem05`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, p. 258, Problem 13.5:
    off-diagonal mass of a leading block column.  For a partition
    `[[A11, A12], [A21, A22]]`, this is the scalar off-diagonal part of column
    `j` inside `A11`. -/
noncomputable def higham13_problem13_5_columnOff {r : ℕ}
    (A11 : Fin r → Fin r → ℝ) (j : Fin r) : ℝ :=
  ∑ i : Fin r, (if i = j then 0 else |A11 i j|)

/-- Higham, 2nd ed., Chapter 13, p. 258, Problem 13.5:
    trailing-block mass below the leading block in column `j`. -/
noncomputable def higham13_problem13_5_trailingCol {r s : ℕ}
    (A21 : Fin s → Fin r → ℝ) (j : Fin r) : ℝ :=
  ∑ i : Fin s, |A21 i j|

/-- Higham, 2nd ed., Chapter 13, p. 258, Problem 13.5:
    a triangle-inequality step bounding the action of the trailing block by its
    column sums. -/
theorem higham13_problem13_5_tail_action_le_weighted_tail {r s : ℕ}
    (A21 : Fin s → Fin r → ℝ) (y : Fin r → ℝ) :
    ∑ i : Fin s, |∑ j : Fin r, A21 i j * y j| ≤
      ∑ j : Fin r, higham13_problem13_5_trailingCol A21 j * |y j| := by
  calc
    ∑ i : Fin s, |∑ j : Fin r, A21 i j * y j|
        ≤ ∑ i : Fin s, ∑ j : Fin r, |A21 i j * y j| := by
          apply Finset.sum_le_sum
          intro i _
          exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin s, ∑ j : Fin r, |A21 i j| * |y j| := by
          simp [abs_mul]
    _ = ∑ j : Fin r, ∑ i : Fin s, |A21 i j| * |y j| := by
          exact Finset.sum_comm
    _ = ∑ j : Fin r, higham13_problem13_5_trailingCol A21 j * |y j| := by
          simp [higham13_problem13_5_trailingCol, Finset.sum_mul]

/-- Higham, 2nd ed., Chapter 13, p. 258, Problem 13.5:
    Varah-style diagonal-weight inequality for the leading block. -/
theorem higham13_problem13_5_diag_weight_le_action_plus_off {r : ℕ}
    (A11 : Fin r → Fin r → ℝ) (y : Fin r → ℝ) :
    ∑ i : Fin r, |A11 i i| * |y i| ≤
      (∑ i : Fin r, |∑ j : Fin r, A11 i j * y j|) +
        ∑ j : Fin r, higham13_problem13_5_columnOff A11 j * |y j| := by
  have hrow : ∀ i : Fin r,
      |A11 i i| * |y i| ≤
        |∑ j : Fin r, A11 i j * y j| +
          ∑ j : Fin r, (if j = i then 0 else |A11 i j| * |y j|) := by
    intro i
    let off : ℝ := ∑ j : Fin r, (if j = i then 0 else A11 i j * y j)
    have hoff_total :
        off = (∑ j : Fin r, A11 i j * y j) - A11 i i * y i := by
      classical
      calc
        off = ∑ j : Fin r,
            (A11 i j * y j - if j = i then A11 i j * y j else 0) := by
            unfold off
            apply Finset.sum_congr rfl
            intro j _
            by_cases hji : j = i <;> simp [hji]
        _ = (∑ j : Fin r, A11 i j * y j) -
              ∑ j : Fin r, (if j = i then A11 i j * y j else 0) := by
            rw [Finset.sum_sub_distrib]
        _ = (∑ j : Fin r, A11 i j * y j) - A11 i i * y i := by
            rw [Finset.sum_ite_eq']
            simp
    have hsplit :
        (∑ j : Fin r, A11 i j * y j) = A11 i i * y i + off := by
      classical
      rw [hoff_total]
      ring
    have hoff_abs :
        |off| ≤ ∑ j : Fin r, (if j = i then 0 else |A11 i j| * |y j|) := by
      calc
        |off| = |∑ j : Fin r, (if j = i then 0 else A11 i j * y j)| := rfl
        _ ≤ ∑ j : Fin r, |if j = i then 0 else A11 i j * y j| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j : Fin r, (if j = i then 0 else |A11 i j| * |y j|) := by
            apply Finset.sum_congr rfl
            intro j _
            by_cases hji : j = i <;> simp [hji, abs_mul]
    have hdiag :
        |A11 i i * y i| ≤ |∑ j : Fin r, A11 i j * y j| + |off| := by
      have hsub : A11 i i * y i = (∑ j : Fin r, A11 i j * y j) - off := by
        rw [hsplit]
        ring
      calc
        |A11 i i * y i| = |(∑ j : Fin r, A11 i j * y j) - off| := by rw [hsub]
        _ ≤ |∑ j : Fin r, A11 i j * y j| + |off| := by
            simpa [sub_eq_add_neg, abs_neg] using
              abs_add_le (∑ j : Fin r, A11 i j * y j) (-off)
    calc
      |A11 i i| * |y i| = |A11 i i * y i| := by rw [abs_mul]
      _ ≤ |∑ j : Fin r, A11 i j * y j| + |off| := hdiag
      _ ≤ |∑ j : Fin r, A11 i j * y j| +
          ∑ j : Fin r, (if j = i then 0 else |A11 i j| * |y j|) := by
          linarith
  calc
    ∑ i : Fin r, |A11 i i| * |y i|
        ≤ ∑ i : Fin r,
            (|∑ j : Fin r, A11 i j * y j| +
              ∑ j : Fin r, (if j = i then 0 else |A11 i j| * |y j|)) := by
          apply Finset.sum_le_sum
          intro i _
          exact hrow i
    _ = (∑ i : Fin r, |∑ j : Fin r, A11 i j * y j|) +
          ∑ i : Fin r, ∑ j : Fin r, (if j = i then 0 else |A11 i j| * |y j|) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ i : Fin r, |∑ j : Fin r, A11 i j * y j|) +
          ∑ j : Fin r, higham13_problem13_5_columnOff A11 j * |y j| := by
          congr 1
          calc
            ∑ i : Fin r, ∑ j : Fin r, (if j = i then 0 else |A11 i j| * |y j|)
                = ∑ j : Fin r, ∑ i : Fin r,
                    (if j = i then 0 else |A11 i j| * |y j|) := by
                  exact Finset.sum_comm
            _ = ∑ j : Fin r, higham13_problem13_5_columnOff A11 j * |y j| := by
                  simp [higham13_problem13_5_columnOff, Finset.sum_mul, eq_comm]

/-- Higham, 2nd ed., Chapter 13, p. 258, Problem 13.5:
    point column diagonal dominance transfers trailing-column mass to the action
    of the leading block. -/
theorem higham13_problem13_5_weighted_tail_le_action {r s : ℕ}
    (A11 : Fin r → Fin r → ℝ) (A21 : Fin s → Fin r → ℝ) (y : Fin r → ℝ)
    (hdom : ∀ j : Fin r,
      higham13_problem13_5_columnOff A11 j +
        higham13_problem13_5_trailingCol A21 j ≤ |A11 j j|) :
    ∑ j : Fin r, higham13_problem13_5_trailingCol A21 j * |y j| ≤
      ∑ i : Fin r, |∑ j : Fin r, A11 i j * y j| := by
  let offWeighted : ℝ :=
    ∑ j : Fin r, higham13_problem13_5_columnOff A11 j * |y j|
  let tailWeighted : ℝ :=
    ∑ j : Fin r, higham13_problem13_5_trailingCol A21 j * |y j|
  let diagWeighted : ℝ := ∑ j : Fin r, |A11 j j| * |y j|
  let action : ℝ := ∑ i : Fin r, |∑ j : Fin r, A11 i j * y j|
  have hdom_weight : offWeighted + tailWeighted ≤ diagWeighted := by
    calc
      offWeighted + tailWeighted
          = ∑ j : Fin r,
              (higham13_problem13_5_columnOff A11 j * |y j| +
                higham13_problem13_5_trailingCol A21 j * |y j|) := by
              simp [offWeighted, tailWeighted, Finset.sum_add_distrib]
      _ = ∑ j : Fin r,
              (higham13_problem13_5_columnOff A11 j +
                higham13_problem13_5_trailingCol A21 j) * |y j| := by
              simp [add_mul]
      _ ≤ ∑ j : Fin r, |A11 j j| * |y j| := by
              apply Finset.sum_le_sum
              intro j _
              exact mul_le_mul_of_nonneg_right (hdom j) (abs_nonneg (y j))
      _ = diagWeighted := rfl
  have hdiag : diagWeighted ≤ action + offWeighted := by
    simpa [diagWeighted, action, offWeighted] using
      higham13_problem13_5_diag_weight_le_action_plus_off A11 y
  have hoff_nonneg : 0 ≤ offWeighted := by
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg
      (Finset.sum_nonneg (fun i _ => by by_cases hij : i = j <;> simp [hij]))
      (abs_nonneg (y j))
  change tailWeighted ≤ action
  linarith

/-- Higham, 2nd ed., Chapter 13, p. 258, Problem 13.5:
    for any vector `y`, the trailing block action is bounded by the leading
    block action under point column diagonal dominance. -/
theorem higham13_problem13_5_tail_action_le_action {r s : ℕ}
    (A11 : Fin r → Fin r → ℝ) (A21 : Fin s → Fin r → ℝ) (y : Fin r → ℝ)
    (hdom : ∀ j : Fin r,
      higham13_problem13_5_columnOff A11 j +
        higham13_problem13_5_trailingCol A21 j ≤ |A11 j j|) :
    ∑ i : Fin s, |∑ j : Fin r, A21 i j * y j| ≤
      ∑ i : Fin r, |∑ j : Fin r, A11 i j * y j| :=
  le_trans (higham13_problem13_5_tail_action_le_weighted_tail A21 y)
    (higham13_problem13_5_weighted_tail_le_action A11 A21 y hdom)

/-- **Problem 13.5** (Higham, 2nd ed., Chapter 13, p. 258):
    if `A = [[A11, A12], [A21, A22]]` is point diagonally dominant by columns
    on the leading block columns and `A11_inv` is a right inverse of `A11`, then
    `‖A21 A11⁻¹‖₁ ≤ 1`.

    The nonsingularity assumption on `A11` is represented by the explicit
    right-inverse equation `A11 * A11_inv = I`, matching the repository's
    function-matrix API. -/
theorem higham13_problem13_5_oneNormRect_bound {r s : ℕ}
    (A11 : Fin r → Fin r → ℝ) (A21 : Fin s → Fin r → ℝ)
    (A11_inv : Fin r → Fin r → ℝ)
    (hdom : ∀ j : Fin r,
      higham13_problem13_5_columnOff A11 j +
        higham13_problem13_5_trailingCol A21 j ≤ |A11 j j|)
    (hright : ∀ i j : Fin r,
      ∑ k : Fin r, A11 i k * A11_inv k j = if i = j then 1 else 0) :
    oneNormRect (rectMatMul A21 A11_inv) ≤ 1 := by
  apply oneNormRect_le_of_col_sum_le
  · intro j
    have htail :=
      higham13_problem13_5_tail_action_le_action A11 A21 (fun k => A11_inv k j) hdom
    have hunit :
        (∑ i : Fin r, |∑ k : Fin r, A11 i k * A11_inv k j|) = 1 := by
      classical
      calc
        ∑ i : Fin r, |∑ k : Fin r, A11 i k * A11_inv k j|
            = ∑ i : Fin r, |if i = j then (1 : ℝ) else 0| := by
              apply Finset.sum_congr rfl
              intro i _
              rw [hright i j]
        _ = ∑ i : Fin r, (if i = j then (1 : ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro i _
              by_cases hij : i = j <;> simp [hij]
        _ = 1 := by
              rw [Finset.sum_ite_eq']
              simp
    calc
      ∑ i : Fin s, |rectMatMul A21 A11_inv i j|
          = ∑ i : Fin s, |∑ k : Fin r, A21 i k * A11_inv k j| := by
            rfl
      _ ≤ ∑ i : Fin r, |∑ k : Fin r, A11 i k * A11_inv k j| := htail
      _ = 1 := hunit
  · norm_num

end NumStability
