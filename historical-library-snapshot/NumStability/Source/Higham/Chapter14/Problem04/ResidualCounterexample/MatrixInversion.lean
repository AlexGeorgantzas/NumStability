import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.MatrixInversion.Residuals.MatrixInversion
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Chapter14 Problem04 ResidualCounterexample MatrixInversion

Canonical destination for material split out of
`NumStability.Algorithms.MatrixInversion` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Higham, 2nd ed., Chapter 14, Problem 14.4 matrix `A(eps)`.

The source uses this two-by-two family, with `0 < eps << 1`, to show that
the right residual `AX-I` can be arbitrarily larger than the left residual
`XA-I`. -/
noncomputable def higham14_problem14_4_A (eps : ℝ) :
    Fin 2 → Fin 2 → ℝ :=
  ![![1 / eps, 1], ![1 / eps ^ 2 - 1, 1 / eps]]

/-- Higham, 2nd ed., Chapter 14, Problem 14.4 approximate inverse family. -/
noncomputable def higham14_problem14_4_X (eps : ℝ) :
    Fin 2 → Fin 2 → ℝ :=
  ![![1 - eps + 2 / eps, -2 - eps],
    ![2 - eps + 1 / eps - 1 / eps ^ 2, -1 - eps + 1 / eps]]

/-- Higham, 2nd ed., Chapter 14, Problem 14.4 exact left product:
    `X(eps) A(eps) = [[1+eps,-eps],[eps,1-eps]]`. -/
theorem higham14_problem14_4_XA_eq (eps : ℝ) (heps : eps ≠ 0) :
    matMul 2 (higham14_problem14_4_X eps) (higham14_problem14_4_A eps) =
      ![![1 + eps, -eps], ![eps, 1 - eps]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [higham14_problem14_4_X, higham14_problem14_4_A, matMul]
  all_goals
    field_simp [heps]
    ring

/-- Higham, 2nd ed., Chapter 14, Problem 14.4 exact right product. -/
theorem higham14_problem14_4_AX_eq (eps : ℝ) (heps : eps ≠ 0) :
    matMul 2 (higham14_problem14_4_A eps) (higham14_problem14_4_X eps) =
      ![![1 / eps ^ 2 + 2 / eps + 1 - eps, -2 - eps - 1 / eps],
        ![1 / eps ^ 3 + 2 / eps ^ 2 - 1 / eps - 2 + eps,
          -1 / eps ^ 2 - 2 / eps + 1 + eps]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [higham14_problem14_4_X, higham14_problem14_4_A, matMul]
  all_goals
    field_simp [heps]
    ring

/-- Higham, 2nd ed., Chapter 14, Problem 14.4:
    the left residual is the small matrix with entries `±eps`. -/
theorem higham14_problem14_4_left_residual_eq
    (eps : ℝ) (heps : eps ≠ 0) :
    inverseLeftResidual 2
        (higham14_problem14_4_A eps) (higham14_problem14_4_X eps) =
      ![![eps, -eps], ![eps, -eps]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inverseLeftResidual, idMatrix,
      higham14_problem14_4_XA_eq eps heps]

/-- Higham, 2nd ed., Chapter 14, Problem 14.4:
    for `0 <= eps`, `||X(eps)A(eps)-I||_∞ = 2 eps`. -/
theorem higham14_problem14_4_left_residual_infNorm_eq
    (eps : ℝ) (hpos : 0 ≤ eps) (heps : eps ≠ 0) :
    infNorm (inverseLeftResidual 2
      (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) =
      2 * eps := by
  rw [higham14_problem14_4_left_residual_eq eps heps]
  apply le_antisymm
  · apply infNorm_le_of_row_sum_le
    · intro i
      fin_cases i <;> simp [hpos, abs_of_nonneg, abs_of_nonpos] <;> linarith
    · nlinarith [hpos]
  · have hrow :=
      row_sum_le_infNorm (![![eps, -eps], ![eps, -eps]] :
        Fin 2 → Fin 2 → ℝ) (0 : Fin 2)
    have hsum :
        (∑ j : Fin 2,
          |(![![eps, -eps], ![eps, -eps]] :
            Fin 2 → Fin 2 → ℝ) (0 : Fin 2) j|) = 2 * eps := by
      simp [hpos, abs_of_nonneg, abs_of_nonpos]
      ring
    linarith

/-- Higham, 2nd ed., Chapter 14, Problem 14.4 support:
    the displayed lower-left entry of `AX-I` dominates `eps^{-3}` for
    `0 < eps <= 1`. -/
lemma higham14_problem14_4_right_residual_entry_ge_inv_cube
    (eps : ℝ) (hpos : 0 < eps) (hle : eps ≤ 1) :
    1 / eps ^ 3 ≤
      1 / eps ^ 3 + 2 / eps ^ 2 - 1 / eps - 2 + eps := by
  field_simp [ne_of_gt hpos]
  nlinarith [hpos, hle, sq_nonneg eps, sq_nonneg (eps - 1)]

/-- Higham, 2nd ed., Chapter 14, Problem 14.4:
    for `0 < eps <= 1`, the right residual has infinity norm at least
    `eps^{-3}`. -/
theorem higham14_problem14_4_right_residual_infNorm_ge_inv_cube
    (eps : ℝ) (hpos : 0 < eps) (hle : eps ≤ 1) :
    1 / eps ^ 3 ≤
      infNorm (inverseRightResidual 2
        (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) := by
  have heps : eps ≠ 0 := ne_of_gt hpos
  let M := inverseRightResidual 2
    (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)
  have hentry : M (1 : Fin 2) (0 : Fin 2) =
      1 / eps ^ 3 + 2 / eps ^ 2 - 1 / eps - 2 + eps := by
    simp [M, inverseRightResidual, idMatrix,
      higham14_problem14_4_AX_eq eps heps]
  have hentry_ge : 1 / eps ^ 3 ≤ M (1 : Fin 2) (0 : Fin 2) := by
    rw [hentry]
    exact higham14_problem14_4_right_residual_entry_ge_inv_cube eps hpos hle
  have habs : M (1 : Fin 2) (0 : Fin 2) ≤ |M (1 : Fin 2) (0 : Fin 2)| :=
    le_abs_self _
  have hsingle :
      |M (1 : Fin 2) (0 : Fin 2)| ≤ ∑ j : Fin 2, |M (1 : Fin 2) j| := by
    simp
  exact le_trans hentry_ge
    (le_trans habs (le_trans hsingle (row_sum_le_infNorm M (1 : Fin 2))))

/-- Higham, 2nd ed., Chapter 14, Problem 14.4:
    the right-over-left residual ratio is bounded below by `1/(2 eps^4)`. -/
theorem higham14_problem14_4_right_over_left_ratio_ge
    (eps : ℝ) (hpos : 0 < eps) (hle : eps ≤ 1) :
    1 / (2 * eps ^ 4) ≤
      infNorm (inverseRightResidual 2
        (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) /
        infNorm (inverseLeftResidual 2
          (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) := by
  have heps : eps ≠ 0 := ne_of_gt hpos
  have hleft :=
    higham14_problem14_4_left_residual_infNorm_eq eps (le_of_lt hpos) heps
  have hleft_pos :
      0 < infNorm (inverseLeftResidual 2
        (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) := by
    rw [hleft]
    nlinarith
  have hright :=
    higham14_problem14_4_right_residual_infNorm_ge_inv_cube eps hpos hle
  calc
    1 / (2 * eps ^ 4) = (1 / eps ^ 3) / (2 * eps) := by
      field_simp [heps]
    _ = (1 / eps ^ 3) /
        infNorm (inverseLeftResidual 2
          (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) := by
      rw [hleft]
    _ ≤ infNorm (inverseRightResidual 2
          (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) /
        infNorm (inverseLeftResidual 2
          (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) :=
      div_le_div_of_nonneg_right hright (le_of_lt hleft_pos)

/-- Higham, 2nd ed., Chapter 14, Problem 14.4:
    the ratio `||AX-I||_∞ / ||XA-I||_∞` is arbitrarily large for the displayed
    two-by-two family. -/
theorem higham14_problem14_4_right_over_left_ratio_arbitrarily_large
    (K : ℝ) :
    ∃ eps : ℝ,
      0 < eps ∧ eps ≤ 1 ∧
        K <
          infNorm (inverseRightResidual 2
            (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) /
            infNorm (inverseLeftResidual 2
              (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) := by
  let eps : ℝ := (2 * (|K| + 1))⁻¹
  have hden : 0 < 2 * (|K| + 1) := by positivity
  have hpos : 0 < eps := by
    dsimp [eps]
    exact inv_pos.mpr hden
  have hle : eps ≤ 1 := by
    dsimp [eps]
    have hden_ge_one : 1 ≤ 2 * (|K| + 1) := by
      have habs : 0 ≤ |K| := abs_nonneg K
      nlinarith
    exact inv_le_one_of_one_le₀ hden_ge_one
  refine ⟨eps, hpos, hle, ?_⟩
  have hlower :=
    higham14_problem14_4_right_over_left_ratio_ge eps hpos hle
  have htarget : K < 1 / (2 * eps ^ 4) := by
    dsimp [eps]
    have hK_lt : K < |K| + 1 := by
      have hKle : K ≤ |K| := le_abs_self K
      linarith
    have hnon : 0 ≤ |K| := abs_nonneg K
    have ht_ge_one : 1 ≤ |K| + 1 := by linarith
    have ht_nonneg : 0 ≤ |K| + 1 := by linarith
    have ht_le_pow4 : |K| + 1 ≤ (|K| + 1) ^ 4 := by
      nlinarith [ht_ge_one, ht_nonneg,
        sq_nonneg ((|K| + 1) ^ 2 - (|K| + 1))]
    have ht_le_8pow4 : |K| + 1 ≤ 2 ^ 3 * (|K| + 1) ^ 4 := by
      nlinarith
    field_simp [ne_of_gt hden]
    nlinarith [hK_lt, ht_le_8pow4]
  exact lt_of_lt_of_le htarget hlower

end NumStability
