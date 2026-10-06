-- NumStability/Source/Higham/Chapter08/Problem02/ComparisonMatrixWitness/ArbitraryRatios/Theorems.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Split component of a mixed/multi-destination owner.
-- Historical owner: `NumStability.Algorithms.HighamChapter8`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Data.Finset.Max
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Order.Interval.Finset.Fin
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LinearSystems.Triangular
import NumStability.Algorithms.MMatrix
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.ArbitraryOrder
import NumStability.Source.Higham.Chapter08.Equation15.GlobalEnvelopeCounterexample.All
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.ConditionNumbers
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.ForwardErrorKernels
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem05
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem09Exact
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem04
import NumStability.Source.Higham.Chapter08.Equation14.FanInExecutor.Executor
import NumStability.Source.Higham.Chapter08.Lemma08.CorrectedCondition.RowDominance
import NumStability.Source.Higham.Chapter08.Lemma08.Entrywise.Basic
import NumStability.Source.Higham.Chapter08.Problem01.NoGuardSubstitution.Aliases
import NumStability.Source.Higham.Chapter08.Problem02.ComparisonMatrixWitness.RatioWitness
import NumStability.Source.Higham.Chapter08.Problem03.UnitTriangularSubstitution.Bound
import NumStability.Source.Higham.Chapter08.Problem04.MMatrixSubstitution.Comparison
import NumStability.Source.Higham.Chapter08.Problem05.InverseNormBounds.ZInverse
import NumStability.Source.Higham.Chapter08.Problem06.ComparisonInverseBounds.VectorBounds
import NumStability.Source.Higham.Chapter08.Problem07.DiagonalScaling.Bounds
import NumStability.Source.Higham.Chapter08.Problem08.SingleEntrySingularity.RankOne
import NumStability.Source.Higham.Chapter08.Problem09.KahanSingularValues.KahanMatrix
import NumStability.Source.Higham.Chapter08.Section01.BackwardErrorAnalysis.Core
import NumStability.Source.Higham.Chapter08.Section02.ForwardErrorAnalysis.ComparisonBounds
import NumStability.Source.Higham.Chapter08.Section02.ForwardErrorAnalysis.ComparisonBoundsPrelude
import NumStability.Source.Higham.Chapter08.Section02.ForwardErrorAnalysis.NormBounds
import NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.InverseBoundsLower
import NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.InverseBoundsPrelude
import NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.InverseBoundsUpper
import NumStability.Source.Higham.Chapter08.Section04.FanInCore.AllOrdersEnvelope
import NumStability.Source.Higham.Chapter08.Section04.FanInCore.Factors
import NumStability.Source.Higham.Chapter08.Section04.FanInCore.ResidualForwardBounds

/-!
# Theorems

Relocated from `NumStability.Algorithms.HighamChapter8` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


-- Algorithms/HighamChapter8.lean
--
-- Source-facing entry points for Higham Chapter 8, "Triangular Systems".
-- The detailed proofs remain in the focused triangular-system modules; this
-- file provides stable chapter labels and light wrappers around those results.















namespace NumStability

open scoped BigOperators

/-! ## §8.1 Backward Error Analysis -/

















































































































/-! ## §8.2 Forward Error Analysis -/













































































private theorem higham8_2_ratioWitnessInv_row0_abs_sum (lam : ℝ) (hlam : 0 ≤ lam) :
    ∑ j : Fin 3, |higham8_2_ratioWitnessInv lam 0 j| = lam + lam ^ 2 := by
  simp [Fin.sum_univ_three, higham8_2_ratioWitnessInv, abs_of_nonneg hlam,
    abs_of_nonneg (sq_nonneg lam)]


private theorem higham8_2_ratioWitnessComparisonInv_row0_abs_sum (lam : ℝ)
    (hlam : 0 ≤ lam) :
    ∑ j : Fin 3, |higham8_2_ratioWitnessComparisonInv lam 0 j| =
      lam + lam ^ 2 + 2 * lam ^ 3 := by
  have hcube : 0 ≤ lam ^ 3 := by
    calc
      0 ≤ lam * lam ^ 2 := mul_nonneg hlam (sq_nonneg lam)
      _ = lam ^ 3 := by ring
  simp [Fin.sum_univ_three, higham8_2_ratioWitnessComparisonInv,
    abs_of_nonneg hlam, abs_of_nonneg (sq_nonneg lam), abs_of_nonneg hcube]


private theorem higham8_2_ratioWitnessComparisonInv_col2_abs_sum (lam : ℝ)
    (hlam : 0 ≤ lam) :
    ∑ i : Fin 3, |higham8_2_ratioWitnessComparisonInv lam i 2| =
      2 * lam ^ 3 + 2 * lam ^ 2 := by
  have hcube : 0 ≤ lam ^ 3 := by
    calc
      0 ≤ lam * lam ^ 2 := mul_nonneg hlam (sq_nonneg lam)
      _ = lam ^ 3 := by ring
  simp [Fin.sum_univ_three, higham8_2_ratioWitnessComparisonInv,
    abs_of_nonneg (sq_nonneg lam), abs_of_nonneg hcube]
  ring


private theorem higham8_2_ratioWitnessInv_infNorm_le (lam : ℝ) (hlam : 1 ≤ lam) :
    infNorm (higham8_2_ratioWitnessInv lam) ≤ 2 * lam ^ 2 := by
  have hlam0 : 0 ≤ lam := by linarith
  apply infNorm_le_of_row_sum_le
  · intro i
    fin_cases i
    · simp [Fin.sum_univ_three, higham8_2_ratioWitnessInv, abs_of_nonneg hlam0,
        abs_of_nonneg (sq_nonneg lam)]
      nlinarith
    · simp [Fin.sum_univ_three, higham8_2_ratioWitnessInv,
        abs_of_nonneg hlam0, abs_of_nonneg (sq_nonneg lam)]
      nlinarith
    · simp [Fin.sum_univ_three, higham8_2_ratioWitnessInv,
        abs_of_nonneg (sq_nonneg lam)]
      nlinarith
  · nlinarith


private theorem higham8_2_ratioWitnessInv_oneNorm_le (lam : ℝ) (hlam : 1 ≤ lam) :
    oneNorm (higham8_2_ratioWitnessInv lam) ≤ 2 * lam ^ 2 := by
  have hlam0 : 0 ≤ lam := by linarith
  apply oneNorm_le_of_col_sum_le
  · intro j
    fin_cases j
    · simp [Fin.sum_univ_three, higham8_2_ratioWitnessInv, abs_of_nonneg hlam0]
      nlinarith
    · simp [Fin.sum_univ_three, higham8_2_ratioWitnessInv,
        abs_of_nonneg hlam0, abs_of_nonneg (sq_nonneg lam)]
      nlinarith
    · simp [Fin.sum_univ_three, higham8_2_ratioWitnessInv,
        abs_of_nonneg (sq_nonneg lam)]
      nlinarith
  · nlinarith


/-- **Problem 8.2**, appendix witness in the infinity norm:
for `λ ≥ 1`, the ratio `‖M(T(λ))⁻¹‖∞ / ‖T(λ)⁻¹‖∞` is at least `λ`. -/
theorem higham8_2_comparisonInverseInfNormRatio_ge_lambda (lam : ℝ) (hlam : 1 ≤ lam) :
    lam ≤
      infNorm (higham8_2_ratioWitnessComparisonInv lam) /
        infNorm (higham8_2_ratioWitnessInv lam) := by
  have hlam0 : 0 ≤ lam := by linarith
  have hlamne : lam ≠ 0 := by linarith
  have hnum_row :=
    row_sum_le_infNorm (higham8_2_ratioWitnessComparisonInv lam) (0 : Fin 3)
  rw [higham8_2_ratioWitnessComparisonInv_row0_abs_sum lam hlam0] at hnum_row
  have hnum : 2 * lam ^ 3 ≤ infNorm (higham8_2_ratioWitnessComparisonInv lam) := by
    nlinarith
  have hden := higham8_2_ratioWitnessInv_infNorm_le lam hlam
  have hden_row := row_sum_le_infNorm (higham8_2_ratioWitnessInv lam) (0 : Fin 3)
  rw [higham8_2_ratioWitnessInv_row0_abs_sum lam hlam0] at hden_row
  have hden_pos : 0 < infNorm (higham8_2_ratioWitnessInv lam) := by
    nlinarith
  have hscale_pos : 0 < 2 * lam ^ 2 := by nlinarith
  have hmid :
      infNorm (higham8_2_ratioWitnessComparisonInv lam) / (2 * lam ^ 2) ≤
        infNorm (higham8_2_ratioWitnessComparisonInv lam) /
          infNorm (higham8_2_ratioWitnessInv lam) := by
    field_simp [hscale_pos.ne', hden_pos.ne']
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hden
        (infNorm_nonneg (higham8_2_ratioWitnessComparisonInv lam)))
  calc
    lam = (2 * lam ^ 3) / (2 * lam ^ 2) := by
          field_simp [hlamne]
    _ ≤ infNorm (higham8_2_ratioWitnessComparisonInv lam) / (2 * lam ^ 2) :=
          div_le_div_of_nonneg_right hnum hscale_pos.le
    _ ≤ infNorm (higham8_2_ratioWitnessComparisonInv lam) /
          infNorm (higham8_2_ratioWitnessInv lam) := hmid


/-- **Problem 8.2**, appendix witness in the one norm:
for `λ ≥ 1`, the ratio `‖M(T(λ))⁻¹‖₁ / ‖T(λ)⁻¹‖₁` is at least `λ`. -/
theorem higham8_2_comparisonInverseOneNormRatio_ge_lambda (lam : ℝ) (hlam : 1 ≤ lam) :
    lam ≤
      oneNorm (higham8_2_ratioWitnessComparisonInv lam) /
        oneNorm (higham8_2_ratioWitnessInv lam) := by
  have hlam0 : 0 ≤ lam := by linarith
  have hlamne : lam ≠ 0 := by linarith
  have hnum_col :=
    col_sum_le_oneNorm (higham8_2_ratioWitnessComparisonInv lam) (2 : Fin 3)
  rw [higham8_2_ratioWitnessComparisonInv_col2_abs_sum lam hlam0] at hnum_col
  have hnum : 2 * lam ^ 3 ≤ oneNorm (higham8_2_ratioWitnessComparisonInv lam) := by
    nlinarith
  have hden := higham8_2_ratioWitnessInv_oneNorm_le lam hlam
  have hden_col :=
    col_sum_le_oneNorm (higham8_2_ratioWitnessInv lam) (2 : Fin 3)
  simp [Fin.sum_univ_three, higham8_2_ratioWitnessInv, abs_of_nonneg (sq_nonneg lam)]
    at hden_col
  have hden_pos : 0 < oneNorm (higham8_2_ratioWitnessInv lam) := by
    nlinarith
  have hscale_pos : 0 < 2 * lam ^ 2 := by nlinarith
  have hmid :
      oneNorm (higham8_2_ratioWitnessComparisonInv lam) / (2 * lam ^ 2) ≤
        oneNorm (higham8_2_ratioWitnessComparisonInv lam) /
          oneNorm (higham8_2_ratioWitnessInv lam) := by
    field_simp [hscale_pos.ne', hden_pos.ne']
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hden
        (oneNorm_nonneg (higham8_2_ratioWitnessComparisonInv lam)))
  calc
    lam = (2 * lam ^ 3) / (2 * lam ^ 2) := by
          field_simp [hlamne]
    _ ≤ oneNorm (higham8_2_ratioWitnessComparisonInv lam) / (2 * lam ^ 2) :=
          div_le_div_of_nonneg_right hnum hscale_pos.le
    _ ≤ oneNorm (higham8_2_ratioWitnessComparisonInv lam) /
          oneNorm (higham8_2_ratioWitnessInv lam) := hmid


/-- **Problem 8.2**: the Appendix A witness makes both the `1`- and `∞`-norm
comparison-inverse ratios arbitrarily large. -/
theorem higham8_2_comparisonInverseRatios_arbitrarily_large (R : ℝ) :
    ∃ lam : ℝ, 1 ≤ lam ∧
      R ≤ infNorm (higham8_2_ratioWitnessComparisonInv lam) /
            infNorm (higham8_2_ratioWitnessInv lam) ∧
      R ≤ oneNorm (higham8_2_ratioWitnessComparisonInv lam) /
            oneNorm (higham8_2_ratioWitnessInv lam) := by
  refine ⟨max 1 R, le_max_left _ _, ?_, ?_⟩
  · exact le_trans (le_max_right _ _) <|
      higham8_2_comparisonInverseInfNormRatio_ge_lambda (max 1 R) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) <|
      higham8_2_comparisonInverseOneNormRatio_ge_lambda (max 1 R) (le_max_left _ _)

end NumStability
