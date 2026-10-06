/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GinibreIntegral

/-! # Higham Chapter 28: Gaussian Ginibre determinant integral

This file specializes the unconditional incidence-area identity to the
standard real-Ginibre density.  The regular-set restriction disappears:
outside the regular set the incidence Jacobian determinant is zero.

The result is the exact determinant-integral reduction preceding the
remaining analytic evaluation.  It does not assume a finite-dimensional
expectation formula or a recurrence for that expectation.
-/

namespace NumStability

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

noncomputable section

/-- The Gaussian-weighted real-root count in matrix coordinates is exactly
the unrestricted incidence integral of the absolute deflated characteristic
determinant.  This is the fully specialized Kac--Rice/coarea reduction; only
its scalar analytic evaluation remains. -/
theorem lintegral_ginibreIncidence_gaussian_eq_rootCount
    (n : ℕ) (μ : Measure (GinibreIncidenceCoordinates n))
    [μ.IsAddHaarMeasure] :
    ∫⁻ q,
        ENNReal.ofReal |(ginibreIncidenceDeflatedBlock q -
          ginibreIncidenceEigenvalue q • (1 : RSqMat n)).det| *
          ENNReal.ofReal (realGinibreDensityReal (n + 1)
            (ginibreCoordinatesFinMatrix (ginibreIncidenceChart q))) ∂μ =
      ∫⁻ p, (realEigenvalueCount (n + 1)
          (ginibreCoordinatesFinMatrix p) : ℝ≥0∞) *
        ENNReal.ofReal (realGinibreDensityReal (n + 1)
          (ginibreCoordinatesFinMatrix p)) ∂μ := by
  let g : GinibreIncidenceCoordinates n → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (realGinibreDensityReal (n + 1)
      (ginibreCoordinatesFinMatrix p))
  have hg : Measurable g :=
    (measurable_realGinibreDensityReal (n + 1)).ennreal_ofReal.comp
      measurable_ginibreCoordinatesFinMatrix
  rw [← lintegral_ginibreIncidence_regular_eq_rootCount n μ g hg]
  rw [← lintegral_indicator (measurableSet_ginibreIncidenceRegularSet n)]
  apply lintegral_congr
  intro q
  by_cases hq : q ∈ ginibreIncidenceRegularSet n
  · rw [Set.indicator_of_mem hq]
    rw [abs_ginibreIncidenceDerivativeLinearMap_det]
  · rw [Set.indicator_of_notMem hq]
    have hdet : (ginibreIncidenceTangentMatrix q).det = 0 := by
      simpa [ginibreIncidenceRegularSet] using hq
    have hderiv : (ginibreIncidenceDerivativeLinearMap q).det = 0 := by
      rw [ginibreIncidenceDerivativeLinearMap_det, hdet]
    have habs : |(ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat n)).det| = 0 := by
      rw [← abs_ginibreIncidenceDerivativeLinearMap_det, hderiv]
      simp
    rw [habs]
    simp

end
end NumStability
