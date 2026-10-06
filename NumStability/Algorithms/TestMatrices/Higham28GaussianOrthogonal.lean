/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Real

namespace NumStability

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

/-! # Finite standard Gaussian vectors and orthogonal invariance

This file supplies the finite-dimensional Gaussian invariance layer needed by
Stewart's Householder/Haar argument in Higham's Theorem 28.1.  The product
measure is kept explicit, so the result applies directly to the independent
Gaussian tails used by the algorithm.
-/

/-- The explicit law of a vector of independent standard real Gaussians. -/
noncomputable def standardGaussianVectorMeasure (n : ℕ) :
    Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => gaussianReal 0 1)

theorem standardGaussianVectorMeasure_univ (n : ℕ) :
    standardGaussianVectorMeasure n Set.univ = 1 := by
  simp [standardGaussianVectorMeasure]

instance standardGaussianVectorMeasure_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (standardGaussianVectorMeasure n) :=
  ⟨standardGaussianVectorMeasure_univ n⟩

/-- Every coordinate has exactly the standard real Gaussian law. -/
theorem standardGaussianVectorCoordinate_hasLaw (n : ℕ) (i : Fin n) :
    HasLaw (fun x : Fin n → ℝ => x i) (gaussianReal 0 1)
      (standardGaussianVectorMeasure n) := by
  refine ⟨(measurable_pi_apply i).aemeasurable, ?_⟩
  unfold standardGaussianVectorMeasure
  rw [Measure.pi_map_eval]
  simp

/-- The coordinate projections of the explicit product law are independent. -/
theorem standardGaussianVectorCoordinates_iIndep (n : ℕ) :
    iIndepFun (fun i : Fin n => fun x : Fin n → ℝ => x i)
      (standardGaussianVectorMeasure n) := by
  unfold standardGaussianVectorMeasure
  simpa using
    (iIndepFun_pi
      (μ := fun _ : Fin n => gaussianReal 0 1)
      (X := fun _ : Fin n => id)
      (fun _ => aemeasurable_id))

/-- The explicit product law is genuinely a Gaussian measure, not merely a
collection of Gaussian marginals. -/
theorem standardGaussianVector_hasGaussianLaw (n : ℕ) :
    HasGaussianLaw id (standardGaussianVectorMeasure n) := by
  have hcoord : ∀ i : Fin n,
      HasGaussianLaw (fun x : Fin n → ℝ => x i)
        (standardGaussianVectorMeasure n) := by
    intro i
    exact (standardGaussianVectorCoordinate_hasLaw n i).hasGaussianLaw
  simpa only [id_eq] using
    (standardGaussianVectorCoordinates_iIndep n).hasGaussianLaw hcoord

instance standardGaussianVectorMeasure_isGaussian (n : ℕ) :
    IsGaussian (standardGaussianVectorMeasure n) := by
  have h := (standardGaussianVector_hasGaussianLaw n).isGaussian_map
  simpa using h

theorem standardGaussianVectorCoordinate_memLp_two (n : ℕ) (i : Fin n) :
    MemLp (fun x : Fin n → ℝ => x i) 2
      (standardGaussianVectorMeasure n) :=
  ((standardGaussianVectorCoordinate_hasLaw n i).hasGaussianLaw).memLp_two

/-- The explicit product vector is centered. -/
theorem standardGaussianVectorMeasure_mean (n : ℕ) :
    (standardGaussianVectorMeasure n)[id] = 0 := by
  apply funext
  intro i
  let L : (Fin n → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i
  change L (∫ x, id x ∂standardGaussianVectorMeasure n) = 0
  rw [← L.integral_comp_comm
    (IsGaussian.integrable_id (μ := standardGaussianVectorMeasure n))]
  simpa [L, Function.comp_def] using
    (standardGaussianVectorCoordinate_hasLaw n i).integral_eq

/-- Exact covariance matrix of the independent standard coordinates. -/
theorem standardGaussianVectorCoordinate_covariance (n : ℕ) (i j : Fin n) :
    cov[fun x : Fin n → ℝ => x i, fun x : Fin n → ℝ => x j;
      standardGaussianVectorMeasure n] = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, covariance_self]
    · rw [(standardGaussianVectorCoordinate_hasLaw n i).variance_eq,
        variance_id_gaussianReal]
      norm_num
    · exact (standardGaussianVectorCoordinate_memLp_two n i).aemeasurable
  · rw [if_neg hij]
    exact (standardGaussianVectorCoordinates_iIndep n).indepFun hij |>.covariance_eq_zero
      (standardGaussianVectorCoordinate_memLp_two n i)
      (standardGaussianVectorCoordinate_memLp_two n j)

/-- The same product law, transported to the Euclidean (`ℓ²`) model. -/
noncomputable def standardGaussianEuclideanMeasure (n : ℕ) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  (standardGaussianVectorMeasure n).map (WithLp.toLp 2)

instance standardGaussianEuclideanMeasure_isGaussian (n : ℕ) :
    IsGaussian (standardGaussianEuclideanMeasure n) := by
  unfold standardGaussianEuclideanMeasure
  change IsGaussian
    ((standardGaussianVectorMeasure n).map
      ((PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : Fin n => ℝ)).symm : (Fin n → ℝ) →L[ℝ]
          EuclideanSpace ℝ (Fin n)))
  infer_instance

theorem standardGaussianEuclideanMeasure_memLp_two (n : ℕ) :
    MemLp id 2 (standardGaussianEuclideanMeasure n) :=
  IsGaussian.memLp_id _ 2 (by norm_num)

/-- The Euclidean standard Gaussian is centered. -/
theorem standardGaussianEuclideanMeasure_mean (n : ℕ) :
    (standardGaussianEuclideanMeasure n)[id] = 0 := by
  let L : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
  change (∫ x, x ∂(standardGaussianVectorMeasure n).map L) = 0
  rw [ContinuousLinearMap.integral_id_map
    (IsGaussian.integrable_id (μ := standardGaussianVectorMeasure n)) L]
  have hm := congrArg L (standardGaussianVectorMeasure_mean n)
  simpa only [id_eq, map_zero] using hm

/-- The covariance bilinear form is the Euclidean inner product. -/
theorem standardGaussianEuclideanMeasure_covariance (n : ℕ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    covarianceBilin (standardGaussianEuclideanMeasure n) x y = ⟪x, y⟫ := by
  rw [standardGaussianEuclideanMeasure]
  rw [covarianceBilin_apply_pi
    (μ := standardGaussianVectorMeasure n)
    (X := fun i : Fin n => fun z : Fin n → ℝ => z i)
    (fun i => standardGaussianVectorCoordinate_memLp_two n i)]
  simp_rw [standardGaussianVectorCoordinate_covariance]
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ j, x i * y j * if i = j then 1 else 0) = y i * x i
  simp [mul_comm]

/-- A centered Gaussian whose covariance is the ambient inner product is
invariant under every surjective linear isometry. -/
theorem centeredIsotropicGaussian_map_linearIsometryEquiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [SecondCountableTopology E]
    (μ : Measure E) [IsGaussian μ]
    (hmean : μ[id] = 0)
    (hcov : ∀ x y : E, covarianceBilin μ x y = ⟪x, y⟫)
    (U : E ≃ₗᵢ[ℝ] E) :
    μ.map U = μ := by
  letI : IsGaussian (μ.map U) := isGaussian_map (U : E →L[ℝ] E)
  apply IsGaussian.ext
  · rw [hmean]
    change (∫ x, x ∂μ.map (U : E →L[ℝ] E)) = 0
    rw [ContinuousLinearMap.integral_id_map (IsGaussian.integrable_id (μ := μ))
      (U : E →L[ℝ] E)]
    have hm : (∫ x, x ∂μ) = 0 := by simpa only [id_eq] using hmean
    rw [hm]
    exact U.map_zero
  · ext x y
    change covarianceBilin (μ.map (U : E →L[ℝ] E)) x y =
      covarianceBilin μ x y
    rw [covarianceBilin_map (IsGaussian.memLp_id μ 2 (by norm_num))
      (U : E →L[ℝ] E) x y]
    rw [U.adjoint_eq_symm]
    rw [hcov, hcov]
    exact U.symm.inner_map_map x y

/-- Orthogonal invariance of the explicit finite standard Gaussian product
law in its Euclidean model. -/
theorem standardGaussianEuclideanMeasure_map_linearIsometryEquiv
    (n : ℕ) (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin n)) :
    (standardGaussianEuclideanMeasure n).map U =
      standardGaussianEuclideanMeasure n := by
  exact centeredIsotropicGaussian_map_linearIsometryEquiv
    (standardGaussianEuclideanMeasure n)
    (standardGaussianEuclideanMeasure_mean n)
    (standardGaussianEuclideanMeasure_covariance n) U

/-! ## Orthogonal matrices as Euclidean isometries -/

/-- The ordinary linear equivalence induced by an element of the real
orthogonal group, transported to the Euclidean (`ℓ²`) model. -/
noncomputable def orthogonalGroupEuclideanLinearEquiv (n : ℕ)
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).toLinearEquiv |>.trans
    (Matrix.UnitaryGroup.toLinearEquiv Q) |>.trans
      (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : Fin n => ℝ)).symm.toLinearEquiv

@[simp] theorem orthogonalGroupEuclideanLinearEquiv_apply (n : ℕ)
    (Q : Matrix.orthogonalGroup (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    orthogonalGroupEuclideanLinearEquiv n Q x =
      Matrix.toEuclideanLin (Q : Matrix (Fin n) (Fin n) ℝ) x := by
  rfl

/-- An orthogonal matrix acts as a surjective Euclidean linear isometry. -/
noncomputable def orthogonalGroupEuclideanLinearIsometryEquiv (n : ℕ)
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (orthogonalGroupEuclideanLinearEquiv n Q).isometryOfInner (by
    intro x y
    let A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
      Matrix.toEuclideanLin (Q : Matrix (Fin n) (Fin n) ℝ)
    change ⟪A x, A y⟫ = ⟪x, y⟫
    have hcomp : A.adjoint.comp A = LinearMap.id := by
      rw [show A.adjoint = Matrix.toEuclideanLin
          (Q : Matrix (Fin n) (Fin n) ℝ).conjTranspose by
        simpa [A] using
          (Matrix.toEuclideanLin_conjTranspose_eq_adjoint
            (Q : Matrix (Fin n) (Fin n) ℝ)).symm]
      rw [← Matrix.toLpLin_mul_same]
      have hQ :
          (Q : Matrix (Fin n) (Fin n) ℝ).conjTranspose *
              (Q : Matrix (Fin n) (Fin n) ℝ) = 1 := by
        simpa only [Matrix.star_eq_conjTranspose] using
          (Matrix.UnitaryGroup.star_mul_self Q)
      rw [hQ, Matrix.toLpLin_one]
    calc
      ⟪A x, A y⟫ = ⟪x, A.adjoint (A y)⟫ :=
        (LinearMap.adjoint_inner_right A x (A y)).symm
      _ = ⟪x, y⟫ := by
        rw [← LinearMap.comp_apply, hcomp, LinearMap.id_apply])

@[simp] theorem orthogonalGroupEuclideanLinearIsometryEquiv_apply (n : ℕ)
    (Q : Matrix.orthogonalGroup (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    orthogonalGroupEuclideanLinearIsometryEquiv n Q x =
      Matrix.toEuclideanLin (Q : Matrix (Fin n) (Fin n) ℝ) x := by
  rfl

/-- The explicit standard Gaussian Euclidean law is invariant under the
action of every real orthogonal matrix. -/
theorem standardGaussianEuclideanMeasure_map_orthogonalGroup (n : ℕ)
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    (standardGaussianEuclideanMeasure n).map
        (orthogonalGroupEuclideanLinearIsometryEquiv n Q) =
      standardGaussianEuclideanMeasure n :=
  standardGaussianEuclideanMeasure_map_linearIsometryEquiv n
    (orthogonalGroupEuclideanLinearIsometryEquiv n Q)

/-- Orthogonal invariance in the original coordinate-function model.  This
is the form used by the independent Gaussian tail vectors in Stewart's
algorithm. -/
theorem standardGaussianVectorMeasure_map_orthogonalGroup (n : ℕ)
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    (standardGaussianVectorMeasure n).map
        (fun x => Matrix.mulVec (Q : Matrix (Fin n) (Fin n) ℝ) x) =
      standardGaussianVectorMeasure n := by
  let e : (Fin n → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin n) :=
    MeasurableEquiv.toLp 2 (Fin n → ℝ)
  apply e.measurableEmbedding.map_injective
  rw [Measure.map_map e.measurable (by fun_prop)]
  have h := standardGaussianEuclideanMeasure_map_orthogonalGroup n Q
  rw [standardGaussianEuclideanMeasure,
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  convert h using 1

/-! ## The converse matrix/isometry bridge -/

/-- Every Euclidean linear isometry equivalence has an orthogonal matrix in
the standard coordinate basis.  This is the converse of
`orthogonalGroupEuclideanLinearIsometryEquiv` and is useful for the
transitivity of the orthogonal action on a sphere. -/
noncomputable def orthogonalGroupOfEuclideanLinearIsometryEquiv (n : ℕ)
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin n)) :
    Matrix.orthogonalGroup (Fin n) ℝ := by
  let A : Matrix (Fin n) (Fin n) ℝ :=
    (Matrix.toLpLin 2 2).symm
      (U : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n))
  refine ⟨A, ?_⟩
  rw [Matrix.mem_orthogonalGroup_iff']
  apply (Matrix.toLpLin 2 2).injective
  rw [Matrix.toLpLin_mul_same]
  have htrans : Matrix.toLpLin 2 2 A.transpose =
      LinearMap.adjoint (Matrix.toLpLin 2 2 A) := by
    change Matrix.toEuclideanLin A.transpose =
      LinearMap.adjoint (Matrix.toEuclideanLin A)
    simpa [Matrix.conjTranspose] using
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
  rw [htrans, Matrix.toLpLin_one]
  have hA : Matrix.toLpLin 2 2 A = U.toLinearMap := by
    apply LinearMap.ext
    intro x
    simp [A]
  rw [hA, U.adjoint_toLinearMap_eq_symm]
  ext x
  simp

@[simp] theorem orthogonalGroupOfEuclideanLinearIsometryEquiv_apply
    (n : ℕ) (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin
        (orthogonalGroupOfEuclideanLinearIsometryEquiv n U :
          Matrix (Fin n) (Fin n) ℝ) x = U x := by
  simp only [orthogonalGroupOfEuclideanLinearIsometryEquiv]
  change Matrix.toEuclideanLin
      ((Matrix.toLpLin 2 2).symm
        (U : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n))) x = U x
  change Matrix.toLpLin 2 2
      ((Matrix.toLpLin 2 2).symm
        (U : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n))) x = U x
  simp

end NumStability
