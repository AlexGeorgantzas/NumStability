/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GinibreDeterminantIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Higham Chapter 28: the Gaussian incidence integral is the expectation

This file supplies the normalization bridge between the affine incidence
coordinates and the matrix coordinates used to define the real-Ginibre law.
The coordinate map is bundled as a continuous linear equivalence.  Pulling
standard matrix Lebesgue measure back along that equivalence gives an additive
Haar measure on incidence coordinates whose pushforward is exactly
`realGinibreLebesgueMeasure`.

Consequently, the unconditional Gaussian incidence integral proved in
`Higham28GinibreDeterminantIntegral` is exactly the nonnegative real-Ginibre
expected real-eigenvalue count.  The further orthogonal eigenvector-coordinate
reduction to an expectation of `|det (A₀ - λI)|` is separate.
-/

namespace NumStability

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

noncomputable section

private local instance ginibreGaussianBridgeMeasurableSpaceRSqMat (n : ℕ) :
    MeasurableSpace (RSqMat n) := MeasurableSpace.pi
private local instance ginibreGaussianBridgeStandardBorelNuisance (n : ℕ) :
    StandardBorelSpace (GinibreIncidenceNuisance n) :=
  StandardBorelSpace.prod
private local instance ginibreGaussianBridgeStandardBorelCoordinates (n : ℕ) :
    StandardBorelSpace (GinibreIncidenceCoordinates n) :=
  StandardBorelSpace.prod

private instance matrixVolume_isAddHaarMeasure (n : ℕ) :
    (volume : Measure (GinibreRawMatrix n)).IsAddHaarMeasure where
  toIsFiniteMeasureOnCompacts := inferInstance
  toIsAddLeftInvariant := inferInstance
  toIsOpenPosMeasure := inferInstance

/-- Extract the four affine blocks from a matrix whose last row and column
are distinguished by `ginibreBlockIndexEquiv`. -/
def ginibreFinMatrixCoordinates {n : ℕ}
    (A : GinibreRawMatrix (n + 1)) : GinibreIncidenceCoordinates n :=
  let M : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
    Matrix.reindex (ginibreBlockIndexEquiv n).symm
      (ginibreBlockIndexEquiv n).symm (Matrix.of A)
  (((fun i j => M (Sum.inl i) (Sum.inl j),
      fun j => M (Sum.inr ()) (Sum.inl j)),
    M (Sum.inr ()) (Sum.inr ())),
    fun i => M (Sum.inl i) (Sum.inr ()))

/-- Reassembling affine matrix coordinates and extracting them again are
inverse linear operations. -/
noncomputable def ginibreCoordinatesLinearEquiv (n : ℕ) :
    GinibreIncidenceCoordinates n ≃ₗ[ℝ] GinibreRawMatrix (n + 1) where
  toFun := ginibreCoordinatesFinMatrix
  invFun := ginibreFinMatrixCoordinates
  left_inv p := by
    rcases p with ⟨⟨⟨B, w⟩, b⟩, v⟩
    simp [ginibreFinMatrixCoordinates, ginibreCoordinatesFinMatrix,
      ginibreCoordinatesMatrix, Matrix.reindex]
  right_inv A := by
    ext i j
    let ii := (ginibreBlockIndexEquiv n).symm i
    let jj := (ginibreBlockIndexEquiv n).symm j
    have hi : ginibreBlockIndexEquiv n ii = i :=
      (ginibreBlockIndexEquiv n).apply_symm_apply i
    have hj : ginibreBlockIndexEquiv n jj = j :=
      (ginibreBlockIndexEquiv n).apply_symm_apply j
    change Matrix.fromBlocks _ _ _ _ ii jj = A i j
    rcases ii with ii | ii <;> rcases jj with jj | jj
    all_goals simp [ginibreFinMatrixCoordinates, Matrix.reindex] at hi hj ⊢
    all_goals simp_all
  map_add' p q := by
    ext i j
    change ginibreCoordinatesMatrix (p + q)
        ((ginibreBlockIndexEquiv n).symm i)
        ((ginibreBlockIndexEquiv n).symm j) =
      ginibreCoordinatesMatrix p ((ginibreBlockIndexEquiv n).symm i)
          ((ginibreBlockIndexEquiv n).symm j) +
        ginibreCoordinatesMatrix q ((ginibreBlockIndexEquiv n).symm i)
          ((ginibreBlockIndexEquiv n).symm j)
    generalize (ginibreBlockIndexEquiv n).symm i = ii
    generalize (ginibreBlockIndexEquiv n).symm j = jj
    rcases ii with ii | ii <;> rcases jj with jj | jj
    all_goals simp [ginibreCoordinatesMatrix]
  map_smul' c p := by
    ext i j
    change ginibreCoordinatesMatrix (c • p)
        ((ginibreBlockIndexEquiv n).symm i)
        ((ginibreBlockIndexEquiv n).symm j) =
      c * ginibreCoordinatesMatrix p ((ginibreBlockIndexEquiv n).symm i)
        ((ginibreBlockIndexEquiv n).symm j)
    generalize (ginibreBlockIndexEquiv n).symm i = ii
    generalize (ginibreBlockIndexEquiv n).symm j = jj
    rcases ii with ii | ii <;> rcases jj with jj | jj
    all_goals simp [ginibreCoordinatesMatrix]

/-- The affine block assembly equivalence, with its automatic
finite-dimensional continuity. -/
noncomputable def ginibreCoordinatesContinuousLinearEquiv (n : ℕ) :
    GinibreIncidenceCoordinates n ≃L[ℝ] GinibreRawMatrix (n + 1) :=
  (ginibreCoordinatesLinearEquiv n).toContinuousLinearEquiv

/-- Standard matrix Lebesgue measure pulled back to affine incidence
coordinates. -/
noncomputable def ginibreIncidenceLebesgueMeasure (n : ℕ) :
    Measure (GinibreIncidenceCoordinates n) :=
  Measure.map (ginibreCoordinatesContinuousLinearEquiv n).symm
    (volume : Measure (GinibreRawMatrix (n + 1)))

local instance ginibreIncidenceLebesgueMeasure_isAddHaarMeasure (n : ℕ) :
    (ginibreIncidenceLebesgueMeasure n).IsAddHaarMeasure := by
  unfold ginibreIncidenceLebesgueMeasure
  exact ContinuousLinearEquiv.isAddHaarMeasure_map
    (ginibreCoordinatesContinuousLinearEquiv n).symm
      (volume : Measure (GinibreRawMatrix (n + 1)))

/-- The affine block assembly map sends incidence Lebesgue measure to the
standard nested product Lebesgue measure on matrices, with no scalar
renormalization. -/
theorem ginibreIncidenceLebesgueMeasure_map (n : ℕ) :
    Measure.map ginibreCoordinatesFinMatrix
        (ginibreIncidenceLebesgueMeasure n) =
      realGinibreLebesgueMeasure (n + 1) := by
  unfold ginibreIncidenceLebesgueMeasure
  rw [Measure.map_map]
  · have hfun : ginibreCoordinatesFinMatrix ∘
        (ginibreCoordinatesContinuousLinearEquiv n).symm = id := by
      funext A
      exact (ginibreCoordinatesLinearEquiv n).apply_symm_apply A
    rw [hfun, Measure.map_id]
    symm
    simp [realGinibreLebesgueMeasure, volume_pi]
  · exact measurable_ginibreCoordinatesFinMatrix
  · exact (ginibreCoordinatesContinuousLinearEquiv n).symm.continuous.measurable

/-- The Gaussian density-weighted root-count `lintegral` in affine block
coordinates is the nonnegative embedding of the real-Ginibre expectation. -/
theorem lintegral_ginibreCoordinate_rootCount_density_eq_expected
    (n : ℕ) :
    (∫⁻ p, (realEigenvalueCount (n + 1)
          (ginibreCoordinatesFinMatrix p) : ℝ≥0∞) *
        ENNReal.ofReal (realGinibreDensityReal (n + 1)
          (ginibreCoordinatesFinMatrix p))
      ∂ginibreIncidenceLebesgueMeasure n) =
      ENNReal.ofReal (expectedRealEigenvalueCount (n + 1)) := by
  let F : GinibreRawMatrix (n + 1) → ℝ≥0∞ := fun A =>
    (realEigenvalueCount (n + 1) A : ℝ≥0∞) *
      ENNReal.ofReal (realGinibreDensityReal (n + 1) A)
  have hmp : MeasurePreserving ginibreCoordinatesFinMatrix
      (ginibreIncidenceLebesgueMeasure n)
      (realGinibreLebesgueMeasure (n + 1)) :=
    ⟨measurable_ginibreCoordinatesFinMatrix,
      ginibreIncidenceLebesgueMeasure_map n⟩
  calc
    (∫⁻ p, (realEigenvalueCount (n + 1)
          (ginibreCoordinatesFinMatrix p) : ℝ≥0∞) *
        ENNReal.ofReal (realGinibreDensityReal (n + 1)
          (ginibreCoordinatesFinMatrix p))
      ∂ginibreIncidenceLebesgueMeasure n) =
        ∫⁻ A, F A ∂realGinibreLebesgueMeasure (n + 1) := by
      exact hmp.lintegral_comp_emb
        (ginibreCoordinatesContinuousLinearEquiv n).toHomeomorph.measurableEmbedding F
    _ = ∫⁻ A, (realEigenvalueCount (n + 1) A : ℝ≥0∞)
        ∂realGinibreMeasure (n + 1) := by
      rw [realGinibreMeasure_eq_withDensity,
        lintegral_withDensity_eq_lintegral_mul]
      · apply lintegral_congr
        intro A
        simp [F, mul_comm]
      · exact (measurable_realGinibreDensityReal (n + 1)).ennreal_ofReal
      · exact (measurable_of_countable _).comp
          (measurable_realEigenvalueCount (n + 1))
    _ = ENNReal.ofReal (expectedRealEigenvalueCount (n + 1)) := by
      unfold expectedRealEigenvalueCount
      symm
      simpa using (ofReal_integral_eq_lintegral_ofReal
        (integrable_realEigenvalueCount (n + 1))
        (ae_of_all _ fun A => Nat.cast_nonneg _))

/-- With the correctly normalized affine Lebesgue measure, the unrestricted
Gaussian incidence determinant integral is exactly the real-Ginibre expected
real-eigenvalue count. -/
theorem lintegral_ginibreIncidence_gaussian_eq_expected (n : ℕ) :
    (∫⁻ q,
        ENNReal.ofReal |(ginibreIncidenceDeflatedBlock q -
          ginibreIncidenceEigenvalue q • (1 : RSqMat n)).det| *
          ENNReal.ofReal (realGinibreDensityReal (n + 1)
            (ginibreCoordinatesFinMatrix (ginibreIncidenceChart q)))
      ∂ginibreIncidenceLebesgueMeasure n) =
      ENNReal.ofReal (expectedRealEigenvalueCount (n + 1)) := by
  rw [lintegral_ginibreIncidence_gaussian_eq_rootCount n
    (ginibreIncidenceLebesgueMeasure n)]
  exact lintegral_ginibreCoordinate_rootCount_density_eq_expected n

end
end NumStability
