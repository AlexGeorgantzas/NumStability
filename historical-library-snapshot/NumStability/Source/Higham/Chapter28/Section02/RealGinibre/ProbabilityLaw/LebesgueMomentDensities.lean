import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Source.Higham.Chapter07.Corollary06.Equilibration.Basic
import NumStability.Source.Higham.Chapter26.IntervalArithmetic.ExactOperations
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.FiniteExpectation.GinibreDeterminantMoment
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw.GinibreJointDensity
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw.GinibreTraceDensity
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw.Probability
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw.ProductLaw
import NumStability.Upstream.Lindemann.MonoidAlgebraCompat

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28GinibreDeterminantMoment, NumStability.Algorithms.TestMatrices.Higham28GinibreJointDensity, NumStability.Algorithms.TestMatrices.Higham28GinibreMeasure, NumStability.Algorithms.TestMatrices.Higham28GinibreTraceDensity under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

noncomputable section

namespace NumStability

open MeasureTheory ProbabilityTheory

local instance ginibreDeterminantMomentMeasurableSpace (n : ℕ) :
    MeasurableSpace (RSqMat n) := MeasurableSpace.pi

local instance ginibreDeterminantMomentSigmaFinite (n : ℕ) :
    SigmaFinite (realGinibreMeasure n) := by
  change SigmaFinite (Measure.pi (fun _ : Fin n =>
    Measure.pi (fun _ : Fin n => gaussianReal 0 1)))
  infer_instance

/-- The absolute characteristic determinant averaged over an independent
standard real-Ginibre matrix and standard real Gaussian shift. -/
noncomputable def realGinibreAbsoluteCharacteristicMoment (n : ℕ) : ℝ :=
  ∫ p : RSqMat n × ℝ,
    |(p.1 - p.2 • (1 : RSqMat n)).det|
    ∂(realGinibreMeasure n).prod (gaussianReal 0 1)

/-- The only entry of a standard `1 × 1` real-Ginibre matrix has the
standard real Gaussian law. -/
theorem realGinibreMeasure_one_map_entry :
    (realGinibreMeasure 1).map (fun A : RSqMat 1 => A 0 0) =
      gaussianReal 0 1 := by
  unfold realGinibreMeasure
  rw [show (fun A : RSqMat 1 => A 0 0) =
      (fun r : Fin 1 → ℝ => r 0) ∘ (fun A : RSqMat 1 => A 0) by rfl]
  rw [← Measure.map_map (measurable_pi_apply 0) (measurable_pi_apply 0)]
  change Measure.map (Function.eval 0)
    (Measure.map (Function.eval 0)
      (Measure.pi fun _ : Fin 1 =>
        Measure.pi fun _ : Fin 1 => gaussianReal 0 1)) = _
  have hrow : (Measure.pi fun _ : Fin 1 =>
      Measure.pi fun _ : Fin 1 => gaussianReal 0 1).map
        (Function.eval 0) = Measure.pi fun _ : Fin 1 => gaussianReal 0 1 := by
    rw [Measure.pi_map_eval]
    simp
  rw [hrow]
  change (Measure.pi fun _ : Fin 1 => gaussianReal 0 1).map
    (Function.eval 0) = gaussianReal 0 1
  rw [Measure.pi_map_eval]
  simp

/-- Jointly retaining the sole matrix entry and the independent scalar shift
gives exactly two independent standard real Gaussians. -/
theorem realGinibreMeasure_one_prod_map_entry :
    ((realGinibreMeasure 1).prod (gaussianReal 0 1)).map
        (fun p : RSqMat 1 × ℝ => (p.1 0 0, p.2)) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  let hA : MeasurePreserving (fun A : RSqMat 1 => A 0 0)
      (realGinibreMeasure 1) (gaussianReal 0 1) :=
    ⟨by fun_prop, realGinibreMeasure_one_map_entry⟩
  have h := hA.prod (MeasurePreserving.id (gaussianReal 0 1))
  simpa [Prod.map] using h.map_eq

/-- The empty determinant has absolute characteristic moment one. -/
theorem realGinibreAbsoluteCharacteristicMoment_zero :
    realGinibreAbsoluteCharacteristicMoment 0 = 1 := by
  unfold realGinibreAbsoluteCharacteristicMoment
  simp only [Matrix.det_isEmpty, abs_one, integral_const, measureReal_def]
  have hprod : ((realGinibreMeasure 0).prod (gaussianReal 0 1)) Set.univ = 1 := by
    rw [Measure.prod_apply MeasurableSet.univ]
    simp [realGinibreMeasure_univ]
  rw [hprod, ENNReal.toReal_one]
  simp

/-- The one-dimensional determinant is the difference of two independent
standard Gaussians, so its absolute moment is `2 / √π`. -/
theorem realGinibreAbsoluteCharacteristicMoment_one :
    realGinibreAbsoluteCharacteristicMoment 1 =
      2 / Real.sqrt Real.pi := by
  unfold realGinibreAbsoluteCharacteristicMoment
  let F : RSqMat 1 × ℝ → ℝ × ℝ := fun p => (p.1 0 0, p.2)
  let μ := (realGinibreMeasure 1).prod (gaussianReal 0 1)
  have hF : AEMeasurable F μ := by fun_prop
  calc
    (∫ p : RSqMat 1 × ℝ, |(p.1 - p.2 • (1 : RSqMat 1)).det| ∂μ) =
        ∫ p : RSqMat 1 × ℝ, |p.1 0 0 - p.2| ∂μ := by
          apply integral_congr_ae
          filter_upwards with p
          simp
    _ = ∫ p : ℝ × ℝ, |p.1 - p.2| ∂μ.map F := by
          exact (integral_map hF
            ((measurable_fst.sub measurable_snd).abs.aestronglyMeasurable)).symm
    _ = ∫ p : ℝ × ℝ, |p.1 - p.2|
          ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
          rw [show μ.map F =
            (gaussianReal 0 1).prod (gaussianReal 0 1) by
              simpa [μ, F] using realGinibreMeasure_one_prod_map_entry]
    _ = 2 / Real.sqrt Real.pi := integral_abs_standardGaussian_difference

end NumStability

end

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace NumStability

open ProbabilityTheory

local instance instMeasurableSpaceRSqMat_3 (n : ℕ) : MeasurableSpace (RSqMat n) := MeasurableSpace.pi

/-- The nested finite product of one-dimensional Lebesgue measures on real
`n × n` matrices. -/
noncomputable def realGinibreLebesgueMeasure (n : ℕ) : Measure (RSqMat n) :=
  Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => volume))

theorem measurable_realGinibreDensityReal (n : ℕ) :
    Measurable (realGinibreDensityReal n) := by
  unfold realGinibreDensityReal
  fun_prop

theorem integrable_realGinibreDensityReal (n : ℕ) :
    Integrable (realGinibreDensityReal n) (realGinibreLebesgueMeasure n) := by
  unfold realGinibreDensityReal realGinibreLebesgueMeasure
  refine Integrable.fintype_prod
    (f := fun _ : Fin n => fun row : Fin n → ℝ =>
      ∏ j : Fin n, gaussianPDFReal 0 1 (row j))
    (μ := fun _ : Fin n => Measure.pi (fun _ : Fin n => volume)) ?_
  intro i
  refine Integrable.fintype_prod
    (f := fun _ : Fin n => gaussianPDFReal 0 1)
    (μ := fun _ : Fin n => volume) ?_
  intro j
  exact integrable_gaussianPDFReal 0 1

/-- Exact joint-density identity for the standard real-Ginibre matrix law. -/
theorem realGinibreMeasure_eq_withDensity (n : ℕ) :
    realGinibreMeasure n =
      (realGinibreLebesgueMeasure n).withDensity
        (fun A => ENNReal.ofReal (realGinibreDensityReal n A)) := by
  let rowLebesgue : Measure (Fin n → ℝ) :=
    Measure.pi (fun _ : Fin n => volume)
  let rowDensity : (Fin n → ℝ) → ℝ :=
    fun x => ∏ j : Fin n, gaussianPDFReal 0 1 (x j)
  have hrowIntegrable : Integrable rowDensity rowLebesgue := by
    dsimp [rowDensity, rowLebesgue]
    apply Integrable.fintype_prod
    intro j
    exact integrable_gaussianPDFReal 0 1
  have hrowNonneg : ∀ x, 0 ≤ rowDensity x := by
    intro x
    exact Finset.prod_nonneg fun j _ => gaussianPDFReal_nonneg 0 1 (x j)
  have hrow : Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
      rowLebesgue.withDensity (fun x => ENNReal.ofReal (rowDensity x)) := by
    have h := Measure.pi_withDensity_ofReal
      (fun _ : Fin n => volume)
      (fun _ : Fin n => gaussianPDFReal 0 1)
      (fun _ => integrable_gaussianPDFReal 0 1)
      (fun _ => gaussianPDFReal_nonneg 0 1)
    simpa [rowLebesgue, rowDensity, gaussianReal_of_var_ne_zero,
      gaussianPDF] using h
  unfold realGinibreMeasure realGinibreLebesgueMeasure realGinibreDensityReal
  rw [show (fun _ : Fin n => Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
      (fun _ : Fin n => rowLebesgue.withDensity
        (fun x => ENNReal.ofReal (rowDensity x))) by
    funext i
    exact hrow]
  simpa [rowLebesgue, rowDensity] using
    (Measure.pi_withDensity_ofReal
      (fun _ : Fin n => rowLebesgue)
      (fun _ : Fin n => rowDensity)
      (fun _ => hrowIntegrable)
      (fun _ => hrowNonneg))

/-- Every Lebesgue-null matrix event is real-Ginibre-null. -/
theorem realGinibreMeasure_absolutelyContinuous_lebesgue (n : ℕ) :
    realGinibreMeasure n ≪ realGinibreLebesgueMeasure n := by
  rw [realGinibreMeasure_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _

/-- The strictly positive Gaussian density also gives the converse null-set
transfer: real-Ginibre and matrix Lebesgue measure are equivalent. -/
theorem realGinibreLebesgueMeasure_absolutelyContinuous (n : ℕ) :
    realGinibreLebesgueMeasure n ≪ realGinibreMeasure n := by
  rw [realGinibreMeasure_eq_withDensity]
  apply withDensity_absolutelyContinuous'
  · exact (measurable_realGinibreDensityReal n).ennreal_ofReal.aemeasurable
  · filter_upwards with A
    exact (ENNReal.ofReal_pos.2 (realGinibreDensityReal_pos n A)).ne'

/-- The expected real-eigenvalue count is exactly its density-weighted
Lebesgue matrix integral.  This is the measure-theoretic starting point for
the missing Kac--Rice/coarea evaluation. -/
theorem expectedRealEigenvalueCount_eq_lebesgue (n : ℕ) :
    expectedRealEigenvalueCount n =
      ∫ A : RSqMat n,
        realGinibreDensityReal n A * (realEigenvalueCount n A : ℝ)
        ∂realGinibreLebesgueMeasure n := by
  unfold expectedRealEigenvalueCount
  rw [realGinibreMeasure_eq_withDensity]
  calc
    (∫ A : RSqMat n, (realEigenvalueCount n A : ℝ)
        ∂(realGinibreLebesgueMeasure n).withDensity
          (fun A => ENNReal.ofReal (realGinibreDensityReal n A))) =
        ∫ A : RSqMat n,
          (ENNReal.ofReal (realGinibreDensityReal n A)).toReal •
            (realEigenvalueCount n A : ℝ)
          ∂realGinibreLebesgueMeasure n :=
      integral_withDensity_eq_integral_toReal_smul
        (measurable_realGinibreDensityReal n).ennreal_ofReal
        (ae_of_all _ fun A => ENNReal.ofReal_lt_top)
        (fun A : RSqMat n => (realEigenvalueCount n A : ℝ))
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with A
      rw [ENNReal.toReal_ofReal (le_of_lt (realGinibreDensityReal_pos n A))]
      simp [smul_eq_mul]

end NumStability

end

noncomputable section

namespace NumStability

open MeasureTheory ProbabilityTheory

private local instance ginibreJointDensityMeasurableSpaceRSqMat (n : ℕ) :
    MeasurableSpace (RSqMat n) := MeasurableSpace.pi

/-- Convert an integral under the independent real-Ginibre and standard
Gaussian laws into the corresponding density-weighted product-Lebesgue
integral. -/
theorem integral_realGinibre_prod_gaussian_eq_jointDensity
    (n : ℕ) (g : RSqMat n × ℝ → ℝ) :
    (∫ p, g p ∂((realGinibreMeasure n).prod (gaussianReal 0 1))) =
      ∫ p,
        (realGinibreDensityReal n p.1 * gaussianPDFReal 0 1 p.2) * g p
        ∂((realGinibreLebesgueMeasure n).prod volume) := by
  rw [realGinibreMeasure_eq_withDensity]
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num)]
  rw [prod_withDensity
    (measurable_realGinibreDensityReal n).ennreal_ofReal
    (measurable_gaussianPDF 0 1)]
  have hdensity : Measurable (fun p : RSqMat n × ℝ =>
      ENNReal.ofReal (realGinibreDensityReal n p.1) *
        gaussianPDF 0 1 p.2) :=
    (((measurable_realGinibreDensityReal n).ennreal_ofReal.comp
      measurable_fst).mul
        ((measurable_gaussianPDF 0 1).comp measurable_snd))
  rw [integral_withDensity_eq_integral_toReal_smul hdensity]
  · apply integral_congr_ae
    filter_upwards with p
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal
        (le_of_lt (realGinibreDensityReal_pos n p.1)),
      toReal_gaussianPDF]
    simp only [smul_eq_mul]
  · filter_upwards with p
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top gaussianPDF_lt_top

end NumStability

end

noncomputable section

namespace NumStability

open MeasureTheory ProbabilityTheory

open scoped BigOperators ENNReal

private local instance instMeasurableSpaceRSqMat_4 (n : ℕ) : MeasurableSpace (RSqMat n) := MeasurableSpace.pi

private local instance instOpensMeasurableSpaceRSqMat (n : ℕ) : OpensMeasurableSpace (RSqMat n) :=
  Pi.opensMeasurableSpace

private local instance instBorelSpaceRSqMat (n : ℕ) : BorelSpace (RSqMat n) := Pi.borelSpace

theorem measurable_ginibreTraceCorrelatedDensityReal (n : ℕ) :
    Measurable (ginibreTraceCorrelatedDensityReal n) := by
  unfold ginibreTraceCorrelatedDensityReal ginibreTraceQuadratic ginibreMatrixSq
  fun_prop

private local instance ginibreLebesgueSigmaFinite (n : ℕ) :
    SigmaFinite (realGinibreLebesgueMeasure n) := by
  change SigmaFinite (Measure.pi (fun _ : Fin n =>
    Measure.pi (fun _ : Fin n => volume)))
  infer_instance

private local instance ginibreLebesgueIsAddRightInvariant (n : ℕ) :
    (realGinibreLebesgueMeasure n).IsAddRightInvariant := by
  change Measure.IsAddRightInvariant (Measure.pi (fun _ : Fin n =>
    Measure.pi (fun _ : Fin n => volume)))
  infer_instance

theorem measurable_ginibreShiftShear (n : ℕ) : Measurable (ginibreShiftShear n) := by
  apply Measurable.prodMk _ measurable_snd
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have hij : Measurable (fun A : RSqMat n => A i j) := by fun_prop
  exact (hij.comp measurable_fst).sub
    (measurable_snd.mul measurable_const)

theorem measurable_ginibreUnshiftShear (n : ℕ) : Measurable (ginibreUnshiftShear n) := by
  apply Measurable.prodMk _ measurable_snd
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have hij : Measurable (fun A : RSqMat n => A i j) := by fun_prop
  exact (hij.comp measurable_fst).add
    (measurable_snd.mul measurable_const)

/-- The affine substitution has Jacobian one, expressed intrinsically as
preservation of matrix-by-scalar Lebesgue measure. -/
theorem measurePreserving_ginibreShiftShear (n : ℕ) :
    MeasurePreserving (ginibreShiftShear n)
      ((realGinibreLebesgueMeasure n).prod volume)
      ((realGinibreLebesgueMeasure n).prod volume) := by
  let μ := realGinibreLebesgueMeasure n
  have htranslate : ∀ x : ℝ,
      Measure.map (fun A : RSqMat n => A - x • (1 : RSqMat n)) μ = μ := by
    intro x
    simpa [sub_eq_add_neg] using
      (map_add_right_eq_self μ (-(x • (1 : RSqMat n))))
  have hskewMeas : Measurable
      (Function.uncurry
        (fun x : ℝ => fun A : RSqMat n => A - x • (1 : RSqMat n))) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    have hij : Measurable (fun A : RSqMat n => A i j) := by fun_prop
    exact (hij.comp measurable_snd).sub
      (measurable_fst.mul measurable_const)
  have hskew : MeasurePreserving
      (fun p : ℝ × RSqMat n => (p.1, p.2 - p.1 • (1 : RSqMat n)))
      (volume.prod μ) (volume.prod μ) :=
    (MeasurePreserving.id volume).skew_product hskewMeas
      (ae_of_all _ htranslate)
  have h := (Measure.measurePreserving_swap (μ := volume) (ν := μ)).comp
    (hskew.comp (Measure.measurePreserving_swap (μ := μ) (ν := volume)))
  simpa [μ, ginibreShiftShear, Function.comp_def] using h

/-- Nonnegative-integral version of the absolute characteristic moment. -/
noncomputable def realGinibreAbsoluteCharacteristicMomentLIntegral (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ p : RSqMat n × ℝ,
    ENNReal.ofReal |(p.1 - p.2 • (1 : RSqMat n)).det|
    ∂(realGinibreMeasure n).prod (gaussianReal 0 1)

theorem measurable_abs_det_ginibreShiftReal (n : ℕ) :
    Measurable (fun p : RSqMat n × ℝ =>
      |(p.1 - p.2 • (1 : RSqMat n)).det|) := by
  apply Measurable.abs
  simp_rw [Matrix.det_apply]
  apply Finset.measurable_sum
  intro σ hσ
  apply Measurable.const_smul
  apply Finset.measurable_prod
  intro i hi
  have hij : Measurable (fun A : RSqMat n => A (σ i) i) := by fun_prop
  exact (hij.comp measurable_fst).sub (measurable_snd.mul measurable_const)

theorem measurable_abs_det_ginibreShift (n : ℕ) :
    Measurable (fun p : RSqMat n × ℝ =>
      ENNReal.ofReal |(p.1 - p.2 • (1 : RSqMat n)).det|) :=
  (measurable_abs_det_ginibreShiftReal n).ennreal_ofReal

theorem measurable_abs_det_matrixReal (n : ℕ) :
    Measurable (fun A : RSqMat n => |A.det|) :=
  continuous_id.matrix_det.abs.measurable

theorem measurable_abs_det_matrix (n : ℕ) :
    Measurable (fun A : RSqMat n => ENNReal.ofReal |A.det|) := by
  exact (measurable_abs_det_matrixReal n).ennreal_ofReal

/-- The ordinary expectation is the real value of its nonnegative integral.
This is unconditional: Mathlib's conventions agree even in the nonintegrable
case (`integral = 0` and `ENNReal.toReal ∞ = 0`). -/
theorem realGinibreAbsoluteCharacteristicMoment_eq_toReal_lintegral (n : ℕ) :
    realGinibreAbsoluteCharacteristicMoment n =
      (realGinibreAbsoluteCharacteristicMomentLIntegral n).toReal := by
  unfold realGinibreAbsoluteCharacteristicMoment
  unfold realGinibreAbsoluteCharacteristicMomentLIntegral
  exact integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun p => abs_nonneg _)
    (measurable_abs_det_ginibreShiftReal n).aestronglyMeasurable

theorem realGinibreAbsoluteCharacteristicMomentLIntegral_eq_jointDensity
    (n : ℕ) :
    realGinibreAbsoluteCharacteristicMomentLIntegral n =
      ∫⁻ p : RSqMat n × ℝ,
        ENNReal.ofReal |(p.1 - p.2 • (1 : RSqMat n)).det| *
          ENNReal.ofReal
            (realGinibreDensityReal n p.1 * gaussianPDFReal 0 1 p.2)
        ∂(realGinibreLebesgueMeasure n).prod volume := by
  unfold realGinibreAbsoluteCharacteristicMomentLIntegral
  rw [realGinibreMeasure_eq_withDensity]
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num)]
  rw [prod_withDensity
    (measurable_realGinibreDensityReal n).ennreal_ofReal
    (measurable_gaussianPDF 0 1)]
  have hdensity : Measurable (fun z : RSqMat n × ℝ =>
      ENNReal.ofReal (realGinibreDensityReal n z.1) * gaussianPDF 0 1 z.2) :=
    (((measurable_realGinibreDensityReal n).ennreal_ofReal.comp measurable_fst).mul
      ((measurable_gaussianPDF 0 1).comp measurable_snd))
  rw [lintegral_withDensity_eq_lintegral_mul _ hdensity
    (measurable_abs_det_ginibreShift n)]
  apply lintegral_congr
  intro p
  simp only [Pi.mul_apply, gaussianPDF]
  rw [ENNReal.ofReal_mul (le_of_lt (realGinibreDensityReal_pos n p.1))]
  ring

theorem realGinibreAbsoluteCharacteristicMomentLIntegral_eq_shiftedJointDensity
    (n : ℕ) :
    realGinibreAbsoluteCharacteristicMomentLIntegral n =
      ∫⁻ p : RSqMat n × ℝ,
        ENNReal.ofReal |p.1.det| *
          ENNReal.ofReal
            (realGinibreDensityReal n
                (p.1 + p.2 • (1 : RSqMat n)) *
              gaussianPDFReal 0 1 p.2)
        ∂(realGinibreLebesgueMeasure n).prod volume := by
  rw [realGinibreAbsoluteCharacteristicMomentLIntegral_eq_jointDensity]
  let G : RSqMat n × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal |p.1.det| *
      ENNReal.ofReal
        (realGinibreDensityReal n (p.1 + p.2 • (1 : RSqMat n)) *
          gaussianPDFReal 0 1 p.2)
  have hdet : Measurable (fun p : RSqMat n × ℝ =>
      ENNReal.ofReal |p.1.det|) := by
    exact (measurable_abs_det_matrix n).comp measurable_fst
  have hjoint : Measurable (fun p : RSqMat n × ℝ =>
      ENNReal.ofReal
        (realGinibreDensityReal n (p.1 + p.2 • (1 : RSqMat n)) *
          gaussianPDFReal 0 1 p.2)) := by
    apply Measurable.ennreal_ofReal
    exact ((measurable_realGinibreDensityReal n).comp
      (measurable_fst.comp (measurable_ginibreUnshiftShear n))).mul
        ((measurable_gaussianPDFReal 0 1).comp measurable_snd)
  have hG : Measurable G := hdet.mul hjoint
  calc
    (∫⁻ p : RSqMat n × ℝ,
        ENNReal.ofReal |(p.1 - p.2 • (1 : RSqMat n)).det| *
          ENNReal.ofReal
            (realGinibreDensityReal n p.1 * gaussianPDFReal 0 1 p.2)
        ∂(realGinibreLebesgueMeasure n).prod volume) =
      ∫⁻ p, G (ginibreShiftShear n p)
        ∂(realGinibreLebesgueMeasure n).prod volume := by
          apply lintegral_congr
          intro p
          change ENNReal.ofReal |(p.1 - p.2 • (1 : RSqMat n)).det| *
              ENNReal.ofReal
                (realGinibreDensityReal n p.1 * gaussianPDFReal 0 1 p.2) =
            ENNReal.ofReal |(p.1 - p.2 • (1 : RSqMat n)).det| *
              ENNReal.ofReal
                (realGinibreDensityReal n
                    ((p.1 - p.2 • (1 : RSqMat n)) +
                      p.2 • (1 : RSqMat n)) *
                  gaussianPDFReal 0 1 p.2)
          rw [sub_add_cancel]
    _ = ∫⁻ p, G p ∂(realGinibreLebesgueMeasure n).prod volume :=
      (measurePreserving_ginibreShiftShear n).lintegral_comp hG

/-- The unconditional change-of-variables identity: the absolute
characteristic moment is the determinant integral against the exact
trace-correlated Gaussian density. -/
theorem realGinibreAbsoluteCharacteristicMomentLIntegral_eq_traceDensity
    (n : ℕ) :
    realGinibreAbsoluteCharacteristicMomentLIntegral n =
      ∫⁻ B : RSqMat n,
        ENNReal.ofReal |B.det| *
          ENNReal.ofReal (ginibreTraceCorrelatedDensityReal n B)
        ∂realGinibreLebesgueMeasure n := by
  rw [realGinibreAbsoluteCharacteristicMomentLIntegral_eq_shiftedJointDensity]
  let d : RSqMat n → ℝ≥0∞ := fun B => ENNReal.ofReal |B.det|
  let j : RSqMat n × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal
      (realGinibreDensityReal n (p.1 + p.2 • (1 : RSqMat n)) *
        gaussianPDFReal 0 1 p.2)
  have hd : Measurable d := by
    simpa only [d] using measurable_abs_det_matrix n
  have hj : Measurable j := by
    apply Measurable.ennreal_ofReal
    exact ((measurable_realGinibreDensityReal n).comp
      (measurable_fst.comp (measurable_ginibreUnshiftShear n))).mul
        ((measurable_gaussianPDFReal 0 1).comp measurable_snd)
  change (∫⁻ p : RSqMat n × ℝ, d p.1 * j p
      ∂(realGinibreLebesgueMeasure n).prod volume) =
    ∫⁻ B : RSqMat n, d B *
      ENNReal.ofReal (ginibreTraceCorrelatedDensityReal n B)
      ∂realGinibreLebesgueMeasure n
  rw [lintegral_prod (fun p : RSqMat n × ℝ => d p.1 * j p)
    ((hd.comp measurable_fst).mul hj).aemeasurable]
  apply lintegral_congr
  intro B
  have hinner : Measurable (fun x : ℝ => j (B, x)) :=
    hj.comp (measurable_const.prodMk measurable_id)
  change (∫⁻ x : ℝ, d B * j (B, x)) =
    d B * ENNReal.ofReal (ginibreTraceCorrelatedDensityReal n B)
  rw [lintegral_const_mul _ hinner]
  change d B * (∫⁻ x : ℝ, ENNReal.ofReal
      (realGinibreDensityReal n (B + x • (1 : RSqMat n)) *
        gaussianPDFReal 0 1 x)) = _
  rw [lintegral_ginibreShiftJointDensity]

/-- Ordinary-integral form of the same unconditional identity, directly
connected to `realGinibreAbsoluteCharacteristicMoment`. -/
theorem realGinibreAbsoluteCharacteristicMoment_eq_traceDensityIntegral
    (n : ℕ) :
    realGinibreAbsoluteCharacteristicMoment n =
      ∫ B : RSqMat n,
        |B.det| * ginibreTraceCorrelatedDensityReal n B
        ∂realGinibreLebesgueMeasure n := by
  calc
    realGinibreAbsoluteCharacteristicMoment n =
        (realGinibreAbsoluteCharacteristicMomentLIntegral n).toReal :=
      realGinibreAbsoluteCharacteristicMoment_eq_toReal_lintegral n
    _ = (∫⁻ B : RSqMat n,
          ENNReal.ofReal |B.det| *
            ENNReal.ofReal (ginibreTraceCorrelatedDensityReal n B)
          ∂realGinibreLebesgueMeasure n).toReal := by
      rw [realGinibreAbsoluteCharacteristicMomentLIntegral_eq_traceDensity]
    _ = (∫⁻ B : RSqMat n,
          ENNReal.ofReal
            (|B.det| * ginibreTraceCorrelatedDensityReal n B)
          ∂realGinibreLebesgueMeasure n).toReal := by
      congr 1
      apply lintegral_congr
      intro B
      rw [ENNReal.ofReal_mul (abs_nonneg B.det)]
    _ = ∫ B : RSqMat n,
          |B.det| * ginibreTraceCorrelatedDensityReal n B
          ∂realGinibreLebesgueMeasure n := by
      symm
      exact integral_eq_lintegral_of_nonneg_ae
        (ae_of_all _ fun B => mul_nonneg (abs_nonneg _)
          (le_of_lt (ginibreTraceCorrelatedDensityReal_pos n B)))
        ((measurable_abs_det_matrixReal n).mul
          (measurable_ginibreTraceCorrelatedDensityReal n)).aestronglyMeasurable

end NumStability

end
