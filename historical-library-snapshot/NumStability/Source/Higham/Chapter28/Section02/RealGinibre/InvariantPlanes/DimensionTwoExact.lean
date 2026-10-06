import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.FiniteExpectation.ClosedFormAsymptotics
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.FiniteExpectation.Ginibre
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.FiniteExpectation.GinibreAbsoluteDetRecurrence
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw.LebesgueMomentDensities
import NumStability.Upstream.Lindemann.MonoidAlgebraCompat

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28GinibreAbsoluteDetRecurrence, NumStability.Algorithms.TestMatrices.Higham28GinibreDimensionTwo under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

noncomputable section

namespace NumStability

open Filter MeasureTheory Polynomial ProbabilityTheory Set

open scoped ENNReal BigOperators

local instance instMeasurableSpaceRSqMat_5 (n : ℕ) : MeasurableSpace (RSqMat n) := MeasurableSpace.pi

theorem measurable_ginibreTwoEntryVector :
    Measurable ginibreTwoEntryVector := by
  unfold ginibreTwoEntryVector
  fun_prop

/-- Flattening the nested real-Ginibre product measure gives the explicit
four-dimensional standard Gaussian product measure. -/
theorem realGinibreMeasure_two_map_ginibreTwoEntryVector :
    (realGinibreMeasure 2).map ginibreTwoEntryVector =
      standardGaussianVectorMeasure 4 := by
  unfold realGinibreMeasure standardGaussianVectorMeasure
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply measurable_ginibreTwoEntryVector
    (MeasurableSet.univ_pi hs)]
  have hpre : ginibreTwoEntryVector ⁻¹' (Set.univ.pi s) =
      Set.univ.pi (fun i : Fin 2 =>
        Set.univ.pi (fun j : Fin 2 => s (finProdFinEquiv (i, j)))) := by
    ext A
    simp only [mem_preimage, Set.mem_pi]
    constructor
    · intro h i hi j hj
      simpa [ginibreTwoEntryVector] using
        h (finProdFinEquiv (i, j)) (by simp)
    · intro h k hk
      let p : Fin 2 × Fin 2 :=
        (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm k
      have hk := h p.1 (by simp) p.2 (by simp)
      have hp : (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4) p = k := by
        exact (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).apply_symm_apply k
      change A p.1 p.2 ∈ s k
      change A p.1 p.2 ∈ s (finProdFinEquiv (p.1, p.2)) at hk
      have heta : (p.1, p.2) = p := Prod.eta p
      rw [heta, hp] at hk
      exact hk
  rw [hpre]
  calc
    (Measure.pi (fun _ : Fin 2 =>
        Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)))
        (Set.univ.pi (fun i : Fin 2 =>
          Set.univ.pi (fun j : Fin 2 => s (finProdFinEquiv (i, j))))) =
      ∏ i : Fin 2, (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1))
        (Set.univ.pi (fun j : Fin 2 => s (finProdFinEquiv (i, j)))) := by
          exact Measure.pi_pi _ _
    _ = ∏ i : Fin 2, ∏ j : Fin 2,
        gaussianReal 0 1 (s (finProdFinEquiv (i, j))) := by
          congr 1
          funext i
          exact Measure.pi_pi _ _
    _ = ∏ k : Fin 4, gaussianReal 0 1 (s k) := by
      rw [← Fintype.prod_prod_type']
      exact Fintype.prod_equiv finProdFinEquiv
        (fun p : Fin 2 × Fin 2 => gaussianReal 0 1 (s (finProdFinEquiv p)))
        (fun k : Fin 4 => gaussianReal 0 1 (s k))
        (fun p => by simp)

theorem measurableSet_realGinibreTwoNonnegativeDiscriminantSet :
    MeasurableSet realGinibreTwoNonnegativeDiscriminantSet := by
  unfold realGinibreTwoNonnegativeDiscriminantSet
  apply measurableSet_le measurable_const
  unfold realGinibreTwoDiscriminant
  fun_prop

/-- The exact probability that a real `2 × 2` Ginibre matrix has
nonnegative characteristic discriminant. -/
theorem realGinibreMeasure_two_discriminant_nonnegative_real :
    (realGinibreMeasure 2).real
        realGinibreTwoNonnegativeDiscriminantSet =
      Real.sqrt 2 / 2 := by
  calc
    (realGinibreMeasure 2).real
        realGinibreTwoNonnegativeDiscriminantSet =
        (realGinibreMeasure 2).real
          (ginibreTwoEntryVector ⁻¹' ginibreVectorDiscriminantEvent) := by
      rw [ginibreTwoEntryVector_preimage_discriminantEvent]
    _ = ((realGinibreMeasure 2).map ginibreTwoEntryVector).real
          ginibreVectorDiscriminantEvent := by
      rw [map_measureReal_apply measurable_ginibreTwoEntryVector
        measurableSet_ginibreVectorDiscriminantEvent]
    _ = (standardGaussianVectorMeasure 4).real
          ginibreVectorDiscriminantEvent := by
      rw [realGinibreMeasure_two_map_ginibreTwoEntryVector]
    _ = _ := standardGaussianVectorMeasure_four_discriminant_real

/-- The genuine matrix expectation in dimension two. -/
theorem expectedRealEigenvalueCount_two :
    expectedRealEigenvalueCount 2 = Real.sqrt 2 := by
  unfold expectedRealEigenvalueCount
  have hfun : (fun A : RSqMat 2 => (realEigenvalueCount 2 A : ℝ)) =
      realGinibreTwoNonnegativeDiscriminantSet.indicator
        (fun _ : RSqMat 2 => (2 : ℝ)) := by
    funext A
    rw [realEigenvalueCount_two_eq_ite]
    by_cases hD : 0 ≤ realGinibreTwoDiscriminant A
    · simp [realGinibreTwoNonnegativeDiscriminantSet, hD]
    · simp [realGinibreTwoNonnegativeDiscriminantSet, hD]
  rw [hfun, integral_indicator_const (2 : ℝ)
    measurableSet_realGinibreTwoNonnegativeDiscriminantSet]
  rw [realGinibreMeasure_two_discriminant_nonnegative_real]
  simp [smul_eq_mul]

/-- Dimension two of the finite real-Ginibre expectation formula, now as an
equality between the genuine expectation and the closed form. -/
theorem expectedRealEigenvalueCount_eq_closedForm_two :
    expectedRealEigenvalueCount 2 =
      realGinibreExpectedCountClosedForm 2 := by
  rw [expectedRealEigenvalueCount_two,
    realGinibreExpectedCountClosedForm_two]

end NumStability

end

noncomputable section

namespace NumStability

open Filter MeasureTheory ProbabilityTheory Set

open scoped BigOperators ENNReal

set_option maxHeartbeats 800000

private local instance ginibreAbsoluteDetRecurrenceMeasurableSpace (n : ℕ) :
    MeasurableSpace (RSqMat n) := MeasurableSpace.pi

private local instance ginibreAbsoluteDetRecurrenceSigmaFinite (n : ℕ) :
    SigmaFinite (realGinibreMeasure n) := by
  change SigmaFinite (Measure.pi (fun _ : Fin n =>
    Measure.pi (fun _ : Fin n => gaussianReal 0 1)))
  infer_instance

private theorem ginibre_natRawCast_one {R : Type*} [AddMonoidWithOne R] :
    Nat.rawCast 1 = (1 : R) := by
  simp [Nat.rawCast]

private theorem ginibre_natRawCast_zero {R : Type*} [AddMonoidWithOne R] :
    Nat.rawCast 0 = (0 : R) := by
  simp [Nat.rawCast]

private theorem ginibre_natRawCast_three {R : Type*} [AddMonoidWithOne R] :
    Nat.rawCast 3 = (3 : R) := by
  simp [Nat.rawCast]

private theorem ginibre_natRawCast_two {R : Type*} [AddMonoidWithOne R] :
    Nat.rawCast 2 = (2 : R) := by
  simp [Nat.rawCast]

private theorem ginibre_natRawCast_six {R : Type*} [AddMonoidWithOne R] :
    Nat.rawCast 6 = (6 : R) := by
  simp [Nat.rawCast]

private theorem ginibre_natRawCast_twelve {R : Type*} [AddMonoidWithOne R] :
    Nat.rawCast 12 = (12 : R) := by
  simp [Nat.rawCast]

theorem measurable_ginibreAbsDetTwoEntryVector :
    Measurable ginibreAbsDetTwoEntryVector := by
  apply measurable_pi_lambda
  intro i
  fin_cases i <;> simp [ginibreAbsDetTwoEntryVector] <;> fun_prop

/-- The flattened matrix entries and scalar shift are exactly five independent
standard real Gaussians. -/
theorem measurePreserving_ginibreAbsDetTwoEntryVector :
    MeasurePreserving ginibreAbsDetTwoEntryVector
      ((realGinibreMeasure 2).prod (gaussianReal 0 1))
      (standardGaussianVectorMeasure 5) := by
  let hA : MeasurePreserving ginibreTwoEntryVector
      (realGinibreMeasure 2) (standardGaussianVectorMeasure 4) :=
    ⟨measurable_ginibreTwoEntryVector,
      realGinibreMeasure_two_map_ginibreTwoEntryVector⟩
  let hscalar : MeasurePreserving (fun x : ℝ => fun _ : Fin 1 => x)
      (gaussianReal 0 1) (standardGaussianVectorMeasure 1) := by
    refine ⟨by fun_prop, ?_⟩
    unfold standardGaussianVectorMeasure
    symm
    apply Measure.pi_eq
    intro s hs
    rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
    have hpre : (fun x : ℝ => fun _ : Fin 1 => x) ⁻¹' (Set.univ.pi s) = s 0 := by
      ext x
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const]
      constructor
      · intro h
        exact h 0
      · intro hx i
        fin_cases i
        exact hx
    rw [hpre]
    simp
  have hprod := hA.prod hscalar
  have hjoin := (measurePreserving_ginibreGaussianVectorSplit 4 1).symm
    (ginibreGaussianVectorSplitEquiv 4 1)
  have h := hjoin.comp hprod
  convert h using 1
  funext p
  simpa only [Function.comp_apply, Prod.map_apply] using
    ginibreAbsDetTwoEntryVector_eq_splitInverse p

/-- The joint absolute determinant is reduced unconditionally to the standard
five-dimensional Gaussian normal-form integral. -/
theorem realGinibreAbsoluteCharacteristicMoment_two_eq_normalFormIntegral :
    realGinibreAbsoluteCharacteristicMoment 2 =
      ∫ x : Fin 5 → ℝ, ginibreAbsDetTwoNormalForm x
        ∂standardGaussianVectorMeasure 5 := by
  let μ := (realGinibreMeasure 2).prod (gaussianReal 0 1)
  let T : (Fin 5 → ℝ) → (Fin 5 → ℝ) := fun x =>
    Matrix.mulVec ginibreAbsDetTwoRotationMatrix x
  have hT : Measurable T := by fun_prop
  have hflat := measurePreserving_ginibreAbsDetTwoEntryVector
  have hrot : (standardGaussianVectorMeasure 5).map T =
      standardGaussianVectorMeasure 5 :=
    standardGaussianVectorMeasure_map_orthogonalGroup 5
      ginibreAbsDetTwoRotationOrthogonal
  unfold realGinibreAbsoluteCharacteristicMoment
  calc
    (∫ p : RSqMat 2 × ℝ, |(p.1 - p.2 • (1 : RSqMat 2)).det| ∂μ) =
        ∫ p : RSqMat 2 × ℝ,
          ginibreAbsDetTwoNormalForm (T (ginibreAbsDetTwoEntryVector p)) ∂μ := by
      apply integral_congr_ae
      filter_upwards with p
      exact abs_det_two_eq_normalForm_rotation p
    _ = ∫ x : Fin 5 → ℝ, ginibreAbsDetTwoNormalForm (T x)
          ∂standardGaussianVectorMeasure 5 := by
      have hmap := integral_map
        measurable_ginibreAbsDetTwoEntryVector.aemeasurable
        ((measurable_ginibreAbsDetTwoNormalForm.comp hT).aestronglyMeasurable)
        (μ := μ)
      rw [hflat.map_eq] at hmap
      simpa only [Function.comp_apply] using hmap.symm
    _ = ∫ x : Fin 5 → ℝ, ginibreAbsDetTwoNormalForm x
          ∂(standardGaussianVectorMeasure 5).map T := by
      symm
      exact integral_map hT.aemeasurable
        measurable_ginibreAbsDetTwoNormalForm.aestronglyMeasurable
    _ = _ := by rw [hrot]

end NumStability

end
