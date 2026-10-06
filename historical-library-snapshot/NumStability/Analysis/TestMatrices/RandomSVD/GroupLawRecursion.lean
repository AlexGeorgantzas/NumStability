import NumStability.Analysis.FirstOrder.AsymptoticFamilies
import NumStability.Analysis.TestMatrices.Orthogonal.HaarFiberMeasure
import NumStability.Analysis.TestMatrices.RandomSVD.StewartRecursion
import NumStability.Upstream.Lindemann.MonoidAlgebraCompat

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28StewartRecursion under the R09/R10 completion waves; reusable-tier destination per the reviewed route ledger.
-/

namespace NumStability

open MeasureTheory ProbabilityTheory

theorem measurable_stewartHouseholderGroupOutput (d : ℕ) :
    Measurable (stewartHouseholderGroupOutput d) := by
  exact measurable_stewartHouseholderListProduct.subtype_mk

theorem measurable_stewartTailRotation (d : ℕ) :
    Measurable (stewartTailRotation d) := by
  exact (continuous_orthogonalTailEmbedding d).measurable.comp
    (measurable_stewartHouseholderGroupOutput d)

theorem measurable_stewartTailRotateVector (d : ℕ) :
    Measurable (stewartTailRotateVector d) := by
  unfold stewartTailRotateVector
  have hQ : Measurable fun p : StewartGaussianInputs d ×
      (Fin (d + 1) → ℝ) => (stewartTailRotation d p.1)⁻¹ :=
    (measurable_stewartTailRotation d).comp measurable_fst |>.inv
  have hM : Measurable fun p : StewartGaussianInputs d ×
      (Fin (d + 1) → ℝ) =>
      (((stewartTailRotation d p.1)⁻¹ : RealOrthogonalGroup (d + 1)) :
        Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :=
    continuous_subtype_val.measurable.comp hQ
  refine measurable_pi_lambda _ fun i => ?_
  exact Finset.measurable_fun_sum Finset.univ fun j _ =>
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hM)).mul
      ((measurable_pi_apply j).comp measurable_snd)

theorem stewartTailRotate_measurePreserving (d : ℕ) :
    MeasurePreserving
      (fun p : StewartGaussianInputs d × (Fin (d + 1) → ℝ) =>
        (p.1, stewartTailRotateVector d p))
      ((stewartGaussianInputMeasure d).prod
        (standardGaussianVectorMeasure (d + 1)))
      ((stewartGaussianInputMeasure d).prod
        (standardGaussianVectorMeasure (d + 1))) := by
  letI : IsProbabilityMeasure (standardGaussianVectorMeasure (d + 1)) :=
    standardGaussianVectorMeasure_isProbabilityMeasure (d + 1)
  letI : SFinite (standardGaussianVectorMeasure (d + 1)) := inferInstance
  letI : SFinite (stewartGaussianInputMeasure d) := inferInstance
  refine (MeasurePreserving.id (stewartGaussianInputMeasure d)).skew_product
    (g := fun t x => stewartTailRotateVector d (t, x)) ?_ ?_
  · simpa [Function.uncurry] using measurable_stewartTailRotateVector d
  filter_upwards [] with t
  simpa [stewartTailRotateVector] using
    standardGaussianVectorMeasure_map_orthogonalGroup (d + 1)
      ((stewartTailRotation d t)⁻¹)

theorem measurable_stewartGaussianFiberProducer (d : ℕ) :
    Measurable (stewartGaussianFiberProducer d) := by
  exact ((continuous_orthogonalTailEmbedding d).measurable.comp measurable_fst).mul
    ((measurable_stewartFirstSection d).comp measurable_snd)

instance stewartOrthogonalGroupLaw_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (stewartOrthogonalGroupLaw n) := by
  unfold stewartOrthogonalGroupLaw
  exact Measure.isProbabilityMeasure_map
    measurable_stewartOrthogonalGroupOutput.aemeasurable

theorem stewartOrthogonalGroupLaw_zero :
    stewartOrthogonalGroupLaw 0 = normalizedOrthogonalHaar 0 := by
  letI : Subsingleton (RealOrthogonalGroup 0) := by
    constructor
    intro Q R
    apply Subtype.ext
    ext i
    exact Fin.elim0 i
  exact measure_eq_of_subsingleton_probability _ _

theorem stewartOrthogonalGroupLaw_succ
    (d : ℕ)
    (hd : stewartOrthogonalGroupLaw d = normalizedOrthogonalHaar d)
    (hraw : Measure.map (stewartGaussianFiberProducer d)
        ((normalizedOrthogonalHaar d).prod
          (standardGaussianVectorMeasure (d + 1))) =
        normalizedOrthogonalHaar (d + 1)) :
    stewartOrthogonalGroupLaw (d + 1) =
      normalizedOrthogonalHaar (d + 1) := by
  let γ := standardGaussianVectorMeasure (d + 1)
  let μ := stewartGaussianInputMeasure d
  letI : IsProbabilityMeasure γ :=
    standardGaussianVectorMeasure_isProbabilityMeasure (d + 1)
  letI : SFinite γ := inferInstance
  letI : SFinite μ := inferInstance
  have hsplit0 := (Measure.measurePreserving_swap (μ := γ) (ν := μ)).comp
    (stewartInputSplitEquiv_measurePreserving d)
  have hsplit : MeasurePreserving (stewartSplitTailFirst d)
      (stewartGaussianInputMeasure (d + 1)) (μ.prod γ) := by
    simpa [stewartSplitTailFirst, Function.comp_def, γ, μ] using hsplit0
  have hrotate : MeasurePreserving (stewartTailRotateMap d)
      (μ.prod γ) (μ.prod γ) := by
    simpa [stewartTailRotateMap, γ, μ] using
      stewartTailRotate_measurePreserving d
  have hout0 :=
    (measurable_stewartOrthogonalGroupOutput.measurePreserving μ).prod
      (MeasurePreserving.id γ)
  have hmap : Measure.map (stewartOrthogonalGroupOutput (n := d)) μ =
      normalizedOrthogonalHaar d := by
    simpa [stewartOrthogonalGroupLaw, μ] using hd
  rw [hmap] at hout0
  have hout : MeasurePreserving (stewartTailOutputMap d)
      (μ.prod γ) ((normalizedOrthogonalHaar d).prod γ) := by
    simpa [stewartTailOutputMap, γ, μ, Prod.map] using hout0
  have hproducer : MeasurePreserving (stewartGaussianFiberProducer d)
      ((normalizedOrthogonalHaar d).prod γ)
      (normalizedOrthogonalHaar (d + 1)) :=
    ⟨measurable_stewartGaussianFiberProducer d, by simpa [γ] using hraw⟩
  have hcomp := hproducer.comp (hout.comp (hrotate.comp hsplit))
  have hcomp' : MeasurePreserving (stewartSuccessorComposite d)
      (stewartGaussianInputMeasure (d + 1))
      (normalizedOrthogonalHaar (d + 1)) := by
    simpa [stewartSuccessorComposite, Function.comp_def] using hcomp
  rw [stewartSuccessorComposite_eq] at hcomp'
  simpa [stewartOrthogonalGroupLaw] using hcomp'.map_eq

end NumStability
