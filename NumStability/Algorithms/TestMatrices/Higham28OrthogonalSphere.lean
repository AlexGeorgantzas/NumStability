/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GaussianOrthogonal
import NumStability.Algorithms.TestMatrices.Higham28HaarFibers
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

namespace NumStability

open MeasureTheory
open scoped RealInnerProductSpace

/-! # The transitive orthogonal action on the Euclidean unit sphere -/

/-- The Euclidean unit sphere in the coordinate space used by the finite
standard Gaussian law. -/
abbrev OrthogonalSphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1

/-- Orthogonal matrices act on the Euclidean unit sphere. -/
noncomputable instance orthogonalGroupSMulOrthogonalSphere (n : ℕ) :
    SMul (Matrix.orthogonalGroup (Fin n) ℝ) (OrthogonalSphere n) where
  smul Q x :=
    ⟨orthogonalGroupEuclideanLinearIsometryEquiv n Q x, by
      rw [Metric.mem_sphere]
      simpa using
        (orthogonalGroupEuclideanLinearIsometryEquiv n Q).norm_map x⟩

noncomputable instance orthogonalGroupMulActionOrthogonalSphere (n : ℕ) :
    MulAction (Matrix.orthogonalGroup (Fin n) ℝ) (OrthogonalSphere n) where
  one_smul x := by
    apply Subtype.ext
    change Matrix.toEuclideanLin (1 : Matrix (Fin n) (Fin n) ℝ) x = x
    simp
  mul_smul Q R x := by
    apply Subtype.ext
    change Matrix.toEuclideanLin
        ((Q : Matrix (Fin n) (Fin n) ℝ) *
          (R : Matrix (Fin n) (Fin n) ℝ)) x =
      Matrix.toEuclideanLin (Q : Matrix (Fin n) (Fin n) ℝ)
        (Matrix.toEuclideanLin (R : Matrix (Fin n) (Fin n) ℝ) x)
    exact LinearMap.congr_fun
      (Matrix.toLpLin_mul_same 2
        (Q : Matrix (Fin n) (Fin n) ℝ)
        (R : Matrix (Fin n) (Fin n) ℝ)) x

/-- The matrix-vector action is jointly continuous, hence jointly
measurable. -/
theorem continuous_orthogonalGroup_smul_orthogonalSphere (n : ℕ) :
    Continuous (fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
      OrthogonalSphere n => p.1 • p.2) := by
  apply Continuous.subtype_mk
  change Continuous fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
      OrthogonalSphere n =>
    WithLp.toLp 2
      (Matrix.mulVec (p.1 : Matrix (Fin n) (Fin n) ℝ)
        (WithLp.ofLp (p.2 : EuclideanSpace ℝ (Fin n))))
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
  apply continuous_pi
  intro i
  exact continuous_finset_sum Finset.univ fun j _ =>
    (((continuous_subtype_val.comp continuous_fst).matrix_elem i j).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).comp
        (continuous_subtype_val.comp continuous_snd)))

noncomputable instance orthogonalGroupContinuousSMulOrthogonalSphere (n : ℕ) :
    ContinuousSMul (Matrix.orthogonalGroup (Fin n) ℝ)
      (OrthogonalSphere n) where
  continuous_smul := continuous_orthogonalGroup_smul_orthogonalSphere n

/-- The real orthogonal group acts transitively on every nonempty unit
sphere.  The witness is the reflection in the orthogonal complement of the
line spanned by `x-y`. -/
theorem orthogonalGroup_action_pretransitive
    (n : ℕ) (x y : OrthogonalSphere n) :
    ∃ Q : Matrix.orthogonalGroup (Fin n) ℝ, y = Q • x := by
  let U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin n) :=
    (ℝ ∙ ((x : EuclideanSpace ℝ (Fin n)) - y))ᗮ.reflection
  let Q := orthogonalGroupOfEuclideanLinearIsometryEquiv n U
  refine ⟨Q, ?_⟩
  apply Subtype.ext
  symm
  change (orthogonalGroupEuclideanLinearIsometryEquiv n Q) x = y
  rw [orthogonalGroupEuclideanLinearIsometryEquiv_apply]
  rw [orthogonalGroupOfEuclideanLinearIsometryEquiv_apply]
  exact Submodule.reflection_sub
    (by simpa [Metric.mem_sphere] using x.property.trans y.property.symm)

end NumStability
