/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28OrthogonalSphere

namespace NumStability

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

/-! # The invariant direction of a finite standard Gaussian vector -/

/-- A fixed point on the nonempty sphere, used only on the Gaussian-null
zero-vector branch of radial normalization. -/
noncomputable def orthogonalSphereBase (d : ℕ) :
    OrthogonalSphere (d + 1) :=
  ⟨WithLp.toLp 2 (Pi.single (0 : Fin (d + 1)) 1), by
    rw [Metric.mem_sphere, dist_zero_right]
    simpa using
      PiLp.norm_toLp_single 2 (fun _ : Fin (d + 1) => ℝ) 0 1⟩

/-- Ambient value of radial normalization. -/
noncomputable def gaussianUnitDirectionValue (d : ℕ)
    (x : Fin (d + 1) → ℝ) : EuclideanSpace ℝ (Fin (d + 1)) :=
  if x = 0 then orthogonalSphereBase d
  else ‖WithLp.toLp 2 x‖⁻¹ • WithLp.toLp 2 x

theorem gaussianUnitDirectionValue_mem (d : ℕ)
    (x : Fin (d + 1) → ℝ) :
    gaussianUnitDirectionValue d x ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1 := by
  by_cases hx : x = 0
  · simpa only [gaussianUnitDirectionValue, hx, if_pos] using
      (orthogonalSphereBase d).property
  · simp only [gaussianUnitDirectionValue, hx, if_false]
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr (show WithLp.toLp 2 x ≠ 0 by
      intro h
      apply hx
      simpa using congrArg WithLp.ofLp h)

/-- Total radial normalization into the unit sphere. -/
noncomputable def gaussianUnitDirection (d : ℕ)
    (x : Fin (d + 1) → ℝ) : OrthogonalSphere (d + 1) :=
  ⟨gaussianUnitDirectionValue d x, gaussianUnitDirectionValue_mem d x⟩

theorem measurable_gaussianUnitDirection (d : ℕ) :
    Measurable (gaussianUnitDirection d) := by
  apply Measurable.subtype_mk
  unfold gaussianUnitDirectionValue
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    ((PiLp.continuous_toLp 2
      (fun _ : Fin (d + 1) => ℝ)).measurable.norm.inv.smul
        (PiLp.continuous_toLp 2
          (fun _ : Fin (d + 1) => ℝ)).measurable)

/-- The only exceptional input of radial normalization has zero probability.
The proof uses one standard-Gaussian coordinate, so it avoids any hidden
nondegeneracy premise on the whole vector law. -/
theorem standardGaussianVectorMeasure_singleton_zero (d : ℕ) :
    standardGaussianVectorMeasure (d + 1)
      ({0} : Set (Fin (d + 1) → ℝ)) = 0 := by
  let i : Fin (d + 1) := ⟨0, by omega⟩
  have hsubset : ({0} : Set (Fin (d + 1) → ℝ)) ⊆
      (fun x => x i) ⁻¹' ({0} : Set ℝ) := by
    intro x hx
    simp only [Set.mem_singleton_iff] at hx ⊢
    subst x
    rfl
  apply le_antisymm
  · refine (measure_mono hsubset).trans ?_
    rw [← Measure.map_apply (measurable_pi_apply i)
      (measurableSet_singleton 0)]
    rw [(standardGaussianVectorCoordinate_hasLaw (d + 1) i).map_eq]
    letI : NoAtoms (gaussianReal 0 1) :=
      noAtoms_gaussianReal one_ne_zero
    exact (measure_singleton (μ := gaussianReal 0 1) 0).le
  · exact bot_le

/-- Radial direction is equivariant under an orthogonal matrix away from the
null zero-vector branch. -/
theorem gaussianUnitDirection_equivariant_of_ne_zero (d : ℕ)
    (Q : Matrix.orthogonalGroup (Fin (d + 1)) ℝ)
    (x : Fin (d + 1) → ℝ) (hx : x ≠ 0) :
    gaussianUnitDirection d
        (Matrix.mulVec
          (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) x) =
      Q • gaussianUnitDirection d x := by
  have hQx : Matrix.mulVec
      (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) x ≠ 0 := by
    intro h
    apply hx
    apply (Matrix.UnitaryGroup.toLinearEquiv Q).injective
    change Matrix.mulVec
      (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) x =
      Matrix.mulVec
        (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) 0
    simpa using h
  apply Subtype.ext
  simp only [gaussianUnitDirection, gaussianUnitDirectionValue, hx, hQx,
    if_false]
  change ‖Matrix.toEuclideanLin
      (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
        (WithLp.toLp 2 x)‖⁻¹ •
      Matrix.toEuclideanLin
        (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
        (WithLp.toLp 2 x) =
    Matrix.toEuclideanLin
      (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
      (‖WithLp.toLp 2 x‖⁻¹ • WithLp.toLp 2 x)
  have hnorm : ‖Matrix.toEuclideanLin
      (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
        (WithLp.toLp 2 x)‖ = ‖WithLp.toLp 2 x‖ :=
    (orthogonalGroupEuclideanLinearIsometryEquiv (d + 1) Q).norm_map _
  rw [hnorm]
  exact ((Matrix.toEuclideanLin
    (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)).map_smul _ _).symm

/-- The probability law of the direction of a standard Gaussian vector. -/
noncomputable def standardGaussianDirectionMeasure (d : ℕ) :
    Measure (OrthogonalSphere (d + 1)) :=
  Measure.map (gaussianUnitDirection d)
    (standardGaussianVectorMeasure (d + 1))

instance standardGaussianDirectionMeasure_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (standardGaussianDirectionMeasure d) := by
  refine ⟨?_⟩
  rw [standardGaussianDirectionMeasure,
    Measure.map_apply (measurable_gaussianUnitDirection d) MeasurableSet.univ]
  exact standardGaussianVectorMeasure_univ (d + 1)

/-- Orthogonal invariance of normalized Gaussian direction. -/
theorem standardGaussianDirectionMeasure_invariant (d : ℕ)
    (Q : Matrix.orthogonalGroup (Fin (d + 1)) ℝ) :
    Measure.map (fun x : OrthogonalSphere (d + 1) => Q • x)
        (standardGaussianDirectionMeasure d) =
      standardGaussianDirectionMeasure d := by
  let T : (Fin (d + 1) → ℝ) → (Fin (d + 1) → ℝ) :=
    fun x => Matrix.mulVec
      (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) x
  have hT : Measurable T := by fun_prop
  have hsmul : Measurable
      (fun x : OrthogonalSphere (d + 1) => Q • x) :=
    (continuous_const.smul continuous_id).measurable
  rw [standardGaussianDirectionMeasure,
    Measure.map_map hsmul (measurable_gaussianUnitDirection d)]
  have hne : ∀ᵐ x ∂standardGaussianVectorMeasure (d + 1), x ≠ 0 := by
    rw [ae_iff]
    simpa only [not_ne_iff, Set.setOf_eq_eq_singleton] using
      standardGaussianVectorMeasure_singleton_zero d
  have hae : (fun x => Q • gaussianUnitDirection d x) =ᵐ[
      standardGaussianVectorMeasure (d + 1)]
      (fun x => gaussianUnitDirection d (T x)) := by
    filter_upwards [hne] with x hx
    exact (gaussianUnitDirection_equivariant_of_ne_zero d Q x hx).symm
  have hae' : ((fun x : OrthogonalSphere (d + 1) => Q • x) ∘
      gaussianUnitDirection d) =ᵐ[standardGaussianVectorMeasure (d + 1)]
      gaussianUnitDirection d ∘ T := by
    simpa [Function.comp_def] using hae
  rw [Measure.map_congr hae']
  rw [← Measure.map_map (measurable_gaussianUnitDirection d) hT]
  rw [standardGaussianVectorMeasure_map_orthogonalGroup (d + 1) Q]

end NumStability
