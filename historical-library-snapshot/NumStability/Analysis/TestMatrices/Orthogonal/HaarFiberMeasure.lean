import NumStability.Analysis.FirstOrder.AsymptoticFamilies
import NumStability.Analysis.TestMatrices.Orthogonal.OrthogonalFibers
import NumStability.Analysis.TestMatrices.RandomSVD.StewartMeasurability
import NumStability.Upstream.Lindemann.MonoidAlgebraCompat

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28OrthogonalFibers under the R09/R10 completion waves; reusable-tier destination per the reviewed route ledger.
-/

namespace NumStability

open MeasureTheory

open scoped RealInnerProductSpace

theorem measurable_stewartFirstSectionMatrix (d : ℕ) :
    Measurable (stewartFirstSectionMatrix d) := by
  unfold stewartFirstSectionMatrix
  exact measurable_matMul_of_measurable
    (measurable_stewartFirstSignMatrix d)
    (measurable_stewartHouseholder.comp
      (measurable_householderVector (by omega : 0 < d + 1)))

theorem measurable_stewartFirstSection (d : ℕ) :
    Measurable (stewartFirstSection d) := by
  exact (measurable_stewartFirstSectionMatrix d).subtype_mk

theorem measurable_stewartSphereSection (d : ℕ) :
    Measurable (stewartSphereSection d) := by
  apply (measurable_stewartFirstSection d).comp
  exact ((PiLp.continuous_ofLp 2 (fun _ : Fin (d + 1) => ℝ)).comp
    continuous_subtype_val).measurable

theorem measurable_orthogonalHaarFiberProducer (d : ℕ) :
    Measurable (orthogonalHaarFiberProducer d) := by
  exact ((continuous_orthogonalTailEmbedding d).measurable.comp measurable_fst).mul
    ((measurable_stewartSphereSection d).comp measurable_snd)

instance orthogonalHaarFiberMeasure_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (orthogonalHaarFiberMeasure d) :=
  Measure.isProbabilityMeasure_map
    (measurable_orthogonalHaarFiberProducer d).aemeasurable

theorem orthogonalHaarFiberMeasure_firstRow (d : ℕ) :
    Measure.map (orthogonalFirstRow d) (orthogonalHaarFiberMeasure d) =
      standardGaussianDirectionMeasure d := by
  rw [orthogonalHaarFiberMeasure,
    Measure.map_map (continuous_orthogonalFirstRow d).measurable
      (measurable_orthogonalHaarFiberProducer d)]
  have hcomp : orthogonalFirstRow d ∘ orthogonalHaarFiberProducer d =
      Prod.snd := by
    funext p
    exact orthogonalFirstRow_orthogonalHaarFiberProducer d p
  rw [hcomp, Measure.map_snd_prod, normalizedOrthogonalHaar_univ, one_smul]

theorem orthogonalHaarFiberMeasure_left_invariant (d : ℕ)
    (H : RealOrthogonalGroup d) :
    Measure.map (fun Q : RealOrthogonalGroup (d + 1) =>
        orthogonalTailEmbedding d H * Q)
        (orthogonalHaarFiberMeasure d) =
      orthogonalHaarFiberMeasure d := by
  let T : RealOrthogonalGroup d × OrthogonalSphere (d + 1) →
      RealOrthogonalGroup d × OrthogonalSphere (d + 1) :=
    Prod.map (fun K => H * K) id
  have hT : Measurable T :=
    ((continuous_const.mul continuous_id).measurable).prodMap measurable_id
  have hprod : Measure.map T
      ((normalizedOrthogonalHaar d).prod
        (standardGaussianDirectionMeasure d)) =
      (normalizedOrthogonalHaar d).prod
        (standardGaussianDirectionMeasure d) := by
    rw [← Measure.map_prod_map]
    · rw [MeasureTheory.map_mul_left_eq_self, Measure.map_id]
    · exact (continuous_const.mul continuous_id).measurable
    · exact measurable_id
  have hleft : Measurable (fun Q : RealOrthogonalGroup (d + 1) =>
      orthogonalTailEmbedding d H * Q) :=
    measurable_const.mul measurable_id
  rw [orthogonalHaarFiberMeasure,
    Measure.map_map hleft
      (measurable_orthogonalHaarFiberProducer d)]
  have hcomp : (fun Q : RealOrthogonalGroup (d + 1) =>
      orthogonalTailEmbedding d H * Q) ∘ orthogonalHaarFiberProducer d =
      orthogonalHaarFiberProducer d ∘ T := by
    funext p
    simp [orthogonalHaarFiberProducer, T, mul_assoc]
  rw [hcomp, ← Measure.map_map
    (measurable_orthogonalHaarFiberProducer d) hT, hprod]

/-- Normalized Haar probability on `O(d+1)` is reconstructed exactly from
normalized Haar on the stabilizer `O(d)` and one invariant sphere direction. -/
theorem orthogonalHaarFiberMeasure_eq_normalizedHaar (d : ℕ) :
    orthogonalHaarFiberMeasure d = normalizedOrthogonalHaar (d + 1) := by
  apply MeasureTheory.measure_eq_of_left_fiber_average
    (orthogonalTailEmbedding d)
    (continuous_orthogonalTailEmbedding d).measurable
    (orthogonalFirstRow d)
    (continuous_orthogonalFirstRow d).measurable
    (stewartSphereSection d)
    (measurable_stewartSphereSection d)
    (orthogonal_firstRow_fiber_factorization d)
    (normalizedOrthogonalHaar d)
  · exact orthogonalHaarFiberMeasure_left_invariant d
  · intro K
    exact MeasureTheory.map_mul_left_eq_self
      (normalizedOrthogonalHaar (d + 1)) (orthogonalTailEmbedding d K)
  · rw [orthogonalHaarFiberMeasure_firstRow,
      orthogonalHaarFirstRowMeasure_eq_standardGaussianDirection]

end NumStability
