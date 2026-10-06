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

/-!
# Source.Higham.Chapter13.Problem01

This module formalizes the source-facing Chapter 13 statements for
`Problem01`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


-- ============================================================
-- Chapter 13 exercises: exact block-matrix algebra
-- ============================================================

/-- **Problem 13.1** (Higham, 2nd ed., Chapter 13, p. 257), column-dominant
    block-tridiagonal LU step, in norm-level form.

    For a block tridiagonal `A = L U` with `L` and `U` block bidiagonal and
    `U_{i-1,i} = A_{i-1,i}`, the local subordinate-norm estimate
    `‖L_{i,i-1}‖ ≤ ‖A_{i,i-1}‖ ‖U_{i-1,i-1}^{-1}‖`, together with the inherited
    column block diagonal dominance bound
    `‖A_{i,i-1}‖ ‖U_{i-1,i-1}^{-1}‖ ≤ 1`, gives the source bounds
    `‖L_{i,i-1}‖ ≤ 1` and
    `‖U_{ii}‖ ≤ ‖A_{ii}‖ + ‖A_{i-1,i}‖`. -/
theorem higham13_problem13_1_column_step_bounds
    (ellNorm uDiagNorm aDiagNorm aLowerNorm aUpperNorm uPrevInvNorm : ℝ)
    (hEll : ellNorm ≤ aLowerNorm * uPrevInvNorm)
    (hColDom : aLowerNorm * uPrevInvNorm ≤ 1)
    (hUDiag : uDiagNorm ≤ aDiagNorm + ellNorm * aUpperNorm)
    (hUpperNonneg : 0 ≤ aUpperNorm) :
    ellNorm ≤ 1 ∧ uDiagNorm ≤ aDiagNorm + aUpperNorm := by
  have hEllOne : ellNorm ≤ 1 := le_trans hEll hColDom
  have hProd : ellNorm * aUpperNorm ≤ aUpperNorm := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hEllOne hUpperNonneg
  exact ⟨hEllOne, by linarith⟩

/-- **Problem 13.1** (Higham, 2nd ed., Chapter 13, p. 257), row-dominant
    block-tridiagonal LU step, in norm-level form.

    The row-dominant local hypothesis
    `‖U_{i-1,i-1}^{-1}‖ ‖A_{i-1,i}‖ ≤ 1` implies
    `‖U_{i-1,i-1}^{-1}‖ ≤ 1 / ‖A_{i-1,i}‖` when the off-diagonal norm is
    positive.  Combined with the bidiagonal LU norm estimate, this gives
    `‖L_{i,i-1}‖ ≤ ‖A_{i,i-1}‖ / ‖A_{i-1,i}‖` and hence
    `‖U_{ii}‖ ≤ ‖A_{ii}‖ + ‖A_{i,i-1}‖`. -/
theorem higham13_problem13_1_row_step_bounds
    (ellNorm uDiagNorm aDiagNorm aLowerNorm aUpperNorm uPrevInvNorm : ℝ)
    (hEll : ellNorm ≤ aLowerNorm * uPrevInvNorm)
    (hRowDom : uPrevInvNorm * aUpperNorm ≤ 1)
    (hUDiag : uDiagNorm ≤ aDiagNorm + ellNorm * aUpperNorm)
    (hLowerNonneg : 0 ≤ aLowerNorm)
    (hUpperPos : 0 < aUpperNorm) :
    ellNorm ≤ aLowerNorm / aUpperNorm ∧
      uDiagNorm ≤ aDiagNorm + aLowerNorm := by
  have hInv : uPrevInvNorm ≤ 1 / aUpperNorm := by
    rw [le_div_iff₀ hUpperPos]
    simpa [mul_comm] using hRowDom
  have hEllDiv : ellNorm ≤ aLowerNorm / aUpperNorm := by
    calc
      ellNorm ≤ aLowerNorm * uPrevInvNorm := hEll
      _ ≤ aLowerNorm * (1 / aUpperNorm) :=
          mul_le_mul_of_nonneg_left hInv hLowerNonneg
      _ = aLowerNorm / aUpperNorm := by ring
  have hProd : ellNorm * aUpperNorm ≤ aLowerNorm := by
    calc
      ellNorm * aUpperNorm ≤ (aLowerNorm / aUpperNorm) * aUpperNorm :=
        mul_le_mul_of_nonneg_right hEllDiv (le_of_lt hUpperPos)
      _ = aLowerNorm := by
        field_simp [ne_of_gt hUpperPos]
  exact ⟨hEllDiv, by linarith⟩

end NumStability
