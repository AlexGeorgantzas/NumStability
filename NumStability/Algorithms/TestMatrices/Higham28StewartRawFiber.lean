/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28StewartRecursion

namespace NumStability

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

noncomputable def stewartRawFiberProducer (d : ℕ)
    (p : RealOrthogonalGroup d × (Fin (d + 1) → ℝ)) :
    RealOrthogonalGroup (d + 1) :=
  orthogonalTailEmbedding d p.1 * stewartFirstSection d p.2

theorem measurable_stewartRawFiberProducer (d : ℕ) :
    Measurable (stewartRawFiberProducer d) := by
  exact ((continuous_orthogonalTailEmbedding d).measurable.comp measurable_fst).mul
    ((measurable_stewartFirstSection d).comp measurable_snd)

noncomputable def stewartRawFiberMeasure (d : ℕ) :
    Measure (RealOrthogonalGroup (d + 1)) :=
  Measure.map (stewartRawFiberProducer d)
    ((normalizedOrthogonalHaar d).prod
      (standardGaussianVectorMeasure (d + 1)))

instance stewartRawFiberMeasure_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (stewartRawFiberMeasure d) := by
  letI : IsProbabilityMeasure (standardGaussianVectorMeasure (d + 1)) :=
    standardGaussianVectorMeasure_isProbabilityMeasure (d + 1)
  exact Measure.isProbabilityMeasure_map
    (measurable_stewartRawFiberProducer d).aemeasurable

theorem orthogonalFirstRow_stewartFirstSection_of_ne_zero (d : ℕ)
    (x : Fin (d + 1) → ℝ) (hx : x ≠ 0) :
    orthogonalFirstRow d (stewartFirstSection d x) =
      gaussianUnitDirection d x := by
  apply Subtype.ext
  apply WithLp.ofLp_injective
  funext j
  change (stewartFirstSection d x :
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) 0 j =
    WithLp.ofLp ((gaussianUnitDirection d x : OrthogonalSphere (d + 1)) :
      EuclideanSpace ℝ (Fin (d + 1))) j
  rw [stewartFirstSection_firstRow_of_ne_zero d x hx j]
  simp [gaussianUnitDirection, gaussianUnitDirectionValue, hx]

theorem orthogonalFirstRow_stewartRawFiberProducer_of_ne_zero (d : ℕ)
    (p : RealOrthogonalGroup d × (Fin (d + 1) → ℝ))
    (hp : p.2 ≠ 0) :
    orthogonalFirstRow d (stewartRawFiberProducer d p) =
      gaussianUnitDirection d p.2 := by
  rw [stewartRawFiberProducer,
    orthogonalFirstRow_mul_of_fixesFirstRow _ _
      (orthogonalTailEmbedding_fixesFirstRow d p.1),
    orthogonalFirstRow_stewartFirstSection_of_ne_zero d p.2 hp]

theorem stewartRawFiberMeasure_firstRow (d : ℕ) :
    Measure.map (orthogonalFirstRow d) (stewartRawFiberMeasure d) =
      standardGaussianDirectionMeasure d := by
  let μ := normalizedOrthogonalHaar d
  let ν := standardGaussianVectorMeasure (d + 1)
  letI : IsProbabilityMeasure ν :=
    standardGaussianVectorMeasure_isProbabilityMeasure (d + 1)
  letI : SFinite ν := inferInstance
  letI : SFinite μ := inferInstance
  rw [stewartRawFiberMeasure,
    Measure.map_map (continuous_orthogonalFirstRow d).measurable
      (measurable_stewartRawFiberProducer d)]
  have hne : ∀ᵐ x ∂ν, x ≠ 0 := by
    rw [ae_iff]
    simpa only [not_ne_iff, Set.setOf_eq_eq_singleton] using
      standardGaussianVectorMeasure_singleton_zero d
  have hneprod : ∀ᵐ p ∂μ.prod ν, p.2 ≠ 0 := by
    rw [Measure.ae_prod_iff_ae_ae]
    · filter_upwards [] with K
      exact hne
    · exact (measurableSet_singleton
        (0 : Fin (d + 1) → ℝ)).compl.preimage measurable_snd
  have hae : (orthogonalFirstRow d ∘ stewartRawFiberProducer d) =ᵐ[μ.prod ν]
      (gaussianUnitDirection d ∘ Prod.snd) := by
    filter_upwards [hneprod] with p hp
    exact orthogonalFirstRow_stewartRawFiberProducer_of_ne_zero d p hp
  rw [Measure.map_congr hae]
  rw [← Measure.map_map (measurable_gaussianUnitDirection d) measurable_snd]
  rw [Measure.map_snd_prod, normalizedOrthogonalHaar_univ, one_smul]
  rfl

theorem stewartRawFiberMeasure_left_invariant (d : ℕ)
    (H : RealOrthogonalGroup d) :
    Measure.map (fun Q : RealOrthogonalGroup (d + 1) ↦
        orthogonalTailEmbedding d H * Q)
        (stewartRawFiberMeasure d) =
      stewartRawFiberMeasure d := by
  let ν := standardGaussianVectorMeasure (d + 1)
  let T : RealOrthogonalGroup d × (Fin (d + 1) → ℝ) →
      RealOrthogonalGroup d × (Fin (d + 1) → ℝ) :=
    Prod.map (fun K ↦ H * K) id
  have hT : Measurable T :=
    ((continuous_const.mul continuous_id).measurable).prodMap measurable_id
  have hprod : Measure.map T
      ((normalizedOrthogonalHaar d).prod ν) =
      (normalizedOrthogonalHaar d).prod ν := by
    rw [← Measure.map_prod_map]
    · rw [MeasureTheory.map_mul_left_eq_self, Measure.map_id]
    · exact (continuous_const.mul continuous_id).measurable
    · exact measurable_id
  have hleft : Measurable (fun Q : RealOrthogonalGroup (d + 1) ↦
      orthogonalTailEmbedding d H * Q) :=
    measurable_const.mul measurable_id
  rw [stewartRawFiberMeasure,
    Measure.map_map hleft
      (measurable_stewartRawFiberProducer d)]
  have hcomp : (fun Q : RealOrthogonalGroup (d + 1) ↦
      orthogonalTailEmbedding d H * Q) ∘ stewartRawFiberProducer d =
      stewartRawFiberProducer d ∘ T := by
    funext p
    simp [stewartRawFiberProducer, T, mul_assoc]
  rw [hcomp, ← Measure.map_map
    (measurable_stewartRawFiberProducer d) hT, hprod]

theorem stewartRawFiberMeasure_eq_normalizedHaar (d : ℕ) :
    stewartRawFiberMeasure d = normalizedOrthogonalHaar (d + 1) := by
  apply MeasureTheory.measure_eq_of_left_fiber_average
    (orthogonalTailEmbedding d)
    (continuous_orthogonalTailEmbedding d).measurable
    (orthogonalFirstRow d)
    (continuous_orthogonalFirstRow d).measurable
    (stewartSphereSection d)
    (measurable_stewartSphereSection d)
    (orthogonal_firstRow_fiber_factorization d)
    (normalizedOrthogonalHaar d)
  · exact stewartRawFiberMeasure_left_invariant d
  · intro K
    exact MeasureTheory.map_mul_left_eq_self
      (normalizedOrthogonalHaar (d + 1)) (orthogonalTailEmbedding d K)
  · rw [stewartRawFiberMeasure_firstRow,
      orthogonalHaarFirstRowMeasure_eq_standardGaussianDirection]

theorem stewartRawFiberLaw (d : ℕ) :
    Measure.map
        (fun p : RealOrthogonalGroup d × (Fin (d + 1) → ℝ) ↦
          orthogonalTailEmbedding d p.1 * stewartFirstSection d p.2)
        ((normalizedOrthogonalHaar d).prod
          (standardGaussianVectorMeasure (d + 1))) =
      normalizedOrthogonalHaar (d + 1) := by
  exact stewartRawFiberMeasure_eq_normalizedHaar d

/-- Stewart's concrete Gaussian Householder producer has exactly normalized
Haar law in every dimension. -/
theorem stewartOrthogonalGroupLaw_eq_normalizedOrthogonalHaar (n : ℕ) :
    stewartOrthogonalGroupLaw n = normalizedOrthogonalHaar n := by
  induction n with
  | zero => exact stewartOrthogonalGroupLaw_zero
  | succ d hd =>
      apply stewartOrthogonalGroupLaw_succ d hd
      simpa [stewartGaussianFiberProducer] using stewartRawFiberLaw d

/-- The exact Haar-distribution conclusion of Higham's Theorem 28.1. -/
theorem stewartTheorem28_1HaarConclusion (n : ℕ) :
    StewartTheorem28_1HaarConclusion n := by
  constructor
  · rw [stewartOrthogonalGroupLaw_eq_normalizedOrthogonalHaar]
    infer_instance
  · exact stewartOrthogonalGroupLaw_univ n

end NumStability
