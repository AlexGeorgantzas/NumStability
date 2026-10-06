/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GaussianDirection
import NumStability.Algorithms.TestMatrices.Higham28OrthogonalHaar

namespace NumStability

open MeasureTheory
open scoped RealInnerProductSpace

/-! # First-coordinate quotients of orthogonal Haar probability -/

noncomputable instance orthogonalSphereNonempty (d : ℕ) :
    Nonempty (OrthogonalSphere (d + 1)) :=
  ⟨orthogonalSphereBase d⟩

/-- The first column of an orthogonal matrix, as a unit Euclidean vector. -/
noncomputable def orthogonalFirstColumn (d : ℕ)
    (Q : RealOrthogonalGroup (d + 1)) : OrthogonalSphere (d + 1) :=
  ⟨WithLp.toLp 2 (fun i =>
      (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) i ⟨0, by omega⟩), by
    rw [Metric.mem_sphere, dist_zero_right]
    have hcol : (∑ i : Fin (d + 1),
        (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) i ⟨0, by omega⟩ *
          (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) i ⟨0, by omega⟩) = 1 := by
      have h := congrFun (congrFun Q.property.1 ⟨0, by omega⟩) ⟨0, by omega⟩
      simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply, starRingEnd_apply, Matrix.one_apply]
        using h
    have hsq : ‖WithLp.toLp 2 (fun i =>
        (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) i
          ⟨0, by omega⟩)‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      simpa [Real.norm_eq_abs, sq_abs, pow_two] using hcol
    nlinarith [norm_nonneg (WithLp.toLp 2 (fun i =>
      (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) i
        ⟨0, by omega⟩))]⟩

/-- The first row, viewed as a column vector in the same unit sphere. -/
noncomputable def orthogonalFirstRow (d : ℕ)
    (Q : RealOrthogonalGroup (d + 1)) : OrthogonalSphere (d + 1) :=
  ⟨WithLp.toLp 2 (fun j =>
      (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) ⟨0, by omega⟩ j), by
    rw [Metric.mem_sphere, dist_zero_right]
    have hrow : (∑ j : Fin (d + 1),
        (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) ⟨0, by omega⟩ j *
          (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) ⟨0, by omega⟩ j) = 1 := by
      have horth : (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) *
          (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ).transpose = 1 :=
        (Matrix.mem_orthogonalGroup_iff (Fin (d + 1)) ℝ).mp Q.property
      have h := congrFun (congrFun horth ⟨0, by omega⟩) ⟨0, by omega⟩
      simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h
    have hsq : ‖WithLp.toLp 2 (fun j =>
        (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) ⟨0, by omega⟩ j)‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      simpa [Real.norm_eq_abs, sq_abs, pow_two] using hrow
    nlinarith [norm_nonneg (WithLp.toLp 2 (fun j =>
      (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) ⟨0, by omega⟩ j))]⟩

theorem continuous_orthogonalFirstColumn (d : ℕ) :
    Continuous (orthogonalFirstColumn d) := by
  let e₀ : Fin (d + 1) := ⟨0, by omega⟩
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (d + 1) => ℝ)).comp
  exact continuous_pi fun i =>
    continuous_subtype_val.matrix_elem i e₀

theorem continuous_orthogonalFirstRow (d : ℕ) :
    Continuous (orthogonalFirstRow d) := by
  let e₀ : Fin (d + 1) := ⟨0, by omega⟩
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (d + 1) => ℝ)).comp
  exact continuous_pi fun j =>
    continuous_subtype_val.matrix_elem e₀ j

theorem orthogonalFirstColumn_mul (d : ℕ)
    (R Q : RealOrthogonalGroup (d + 1)) :
    orthogonalFirstColumn d (R * Q) = R • orthogonalFirstColumn d Q := by
  apply Subtype.ext
  apply WithLp.ofLp_injective
  funext i
  change (∑ j : Fin (d + 1),
      (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) i j *
        (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) j ⟨0, by omega⟩) =
    ∑ j : Fin (d + 1),
      (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) i j *
        (Q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) j ⟨0, by omega⟩
  rfl

theorem orthogonalFirstRow_eq_firstColumn_inv (d : ℕ)
    (Q : RealOrthogonalGroup (d + 1)) :
    orthogonalFirstRow d Q = orthogonalFirstColumn d Q⁻¹ := by
  apply Subtype.ext
  apply WithLp.ofLp_injective
  funext j
  rfl

/-- First-column law of normalized orthogonal Haar probability. -/
noncomputable def orthogonalHaarFirstColumnMeasure (d : ℕ) :
    Measure (OrthogonalSphere (d + 1)) :=
  Measure.map (orthogonalFirstColumn d) (normalizedOrthogonalHaar (d + 1))

instance orthogonalHaarFirstColumnMeasure_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (orthogonalHaarFirstColumnMeasure d) :=
  Measure.isProbabilityMeasure_map
    (continuous_orthogonalFirstColumn d).measurable.aemeasurable

theorem orthogonalHaarFirstColumnMeasure_invariant (d : ℕ)
    (R : RealOrthogonalGroup (d + 1)) :
    Measure.map (fun x : OrthogonalSphere (d + 1) => R • x)
        (orthogonalHaarFirstColumnMeasure d) =
      orthogonalHaarFirstColumnMeasure d := by
  let L : RealOrthogonalGroup (d + 1) →
      RealOrthogonalGroup (d + 1) := fun Q => R * Q
  have hL : Measurable L := (continuous_const.mul continuous_id).measurable
  have hcol : Measurable (orthogonalFirstColumn d) :=
    (continuous_orthogonalFirstColumn d).measurable
  have hact : Measurable
      (fun x : OrthogonalSphere (d + 1) => R • x) :=
    (continuous_const.smul continuous_id).measurable
  rw [orthogonalHaarFirstColumnMeasure,
    Measure.map_map hact hcol]
  have hcomp : (fun x : OrthogonalSphere (d + 1) => R • x) ∘
      orthogonalFirstColumn d = orthogonalFirstColumn d ∘ L := by
    funext Q
    exact (orthogonalFirstColumn_mul d R Q).symm
  rw [hcomp, ← Measure.map_map hcol hL]
  rw [MeasureTheory.map_mul_left_eq_self]

/-- The first column of normalized orthogonal Haar probability has exactly
the normalized standard-Gaussian direction law. -/
theorem orthogonalHaarFirstColumnMeasure_eq_standardGaussianDirection (d : ℕ) :
    orthogonalHaarFirstColumnMeasure d =
      standardGaussianDirectionMeasure d := by
  exact MeasureTheory.measure_eq_of_invariant_probability_of_pretransitive
    (orthogonalGroup_action_pretransitive (d + 1))
    (normalizedOrthogonalHaar (d + 1))
    (orthogonalHaarFirstColumnMeasure d)
    (standardGaussianDirectionMeasure d)
    (orthogonalHaarFirstColumnMeasure_invariant d)
    (standardGaussianDirectionMeasure_invariant d)

/-- The first-row quotient has the same invariant Gaussian-direction law. -/
theorem orthogonalHaarFirstRowMeasure_eq_standardGaussianDirection (d : ℕ) :
    Measure.map (orthogonalFirstRow d) (normalizedOrthogonalHaar (d + 1)) =
      standardGaussianDirectionMeasure d := by
  have hrow : orthogonalFirstRow d =
      orthogonalFirstColumn d ∘ Inv.inv := by
    funext Q
    exact orthogonalFirstRow_eq_firstColumn_inv d Q
  rw [hrow, ← Measure.map_map
    (continuous_orthogonalFirstColumn d).measurable continuous_inv.measurable]
  rw [normalizedOrthogonalHaar_map_inv]
  exact orthogonalHaarFirstColumnMeasure_eq_standardGaussianDirection d

end NumStability
