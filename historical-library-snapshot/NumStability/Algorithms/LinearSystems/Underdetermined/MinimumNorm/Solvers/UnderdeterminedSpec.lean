import Mathlib.Data.Real.Basic
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Pseudoinverse.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Specifications.UnderdeterminedSpec
import NumStability.Analysis.MatrixAlgebra

/-!
# Algorithms.LinearSystems.Underdetermined.MinimumNorm.Solvers.UnderdeterminedSpec

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Algorithms/Underdetermined/UnderdeterminedSpec.lean
--
-- Solution methods and perturbation theory for underdetermined systems
-- (Higham §21.1-§21.2).
--
-- An underdetermined system Ax = b with A ∈ ℝ^{m×n}, m < n, has
-- infinitely many solutions. The minimum 2-norm solution is
-- x_LS = Aᵀ(AAᵀ)⁻¹b = A⁺b.
--
-- Two solution methods use the QR factorization Aᵀ = Q[R; 0]:
-- - Q method: solve Rᵀy₁ = b, form x = Q[y₁; 0]ᵀ
-- - SNE method: solve RᵀRy = b, form x = Aᵀy
--
-- Theorem 21.1 (Demmel-Higham): Componentwise perturbation bound
-- for the minimum-norm solution.
-- Lemma 21.2 (Kielbasiński-Schwetlick): Asymmetric normal equation
-- perturbations can be symmetrized without increasing the bound.




namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- §21.1  Minimum-norm solution specification
-- ============================================================






































































































































/-- A rectangular-system solution that is orthogonal to the nullspace of `A`
    is a minimum Euclidean-norm solution. -/
theorem rectMinNormSolution_of_system_eq_and_nullspace_orthogonal {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ)
    (hx : rectMatMulVec A x = b)
    (horth : ∀ e : Fin n → ℝ,
      rectMatMulVec A e = (0 : Fin m → ℝ) →
        (∑ j : Fin n, x j * e j) = 0) :
    RectMinNormSolution m n A b x := by
  constructor
  · exact hx
  · intro z hz
    let e : Fin n → ℝ := fun j => z j - x j
    have he_kernel : rectMatMulVec A e = (0 : Fin m → ℝ) := by
      unfold e
      rw [rectMatMulVec_sub, hz, hx]
      ext i
      simp
    have hinner : (∑ j : Fin n, x j * e j) = 0 :=
      horth e he_kernel
    have hz_decomp : z = fun j : Fin n => x j + e j := by
      ext j
      unfold e
      ring
    have hpyth : vecNorm2Sq z = vecNorm2Sq x + vecNorm2Sq e := by
      rw [hz_decomp]
      simpa [finiteVecNorm2Sq_fin] using
        (finiteVecNorm2Sq_add_of_inner_eq_zero x e hinner)
    unfold vecNorm2
    exact Real.sqrt_le_sqrt
      (by
        rw [hpyth]
        exact le_add_of_nonneg_right (vecNorm2Sq_nonneg e))



































































/-- Every finite-dimensional minimum 2-norm solution belongs to the range of
    the transposed coefficient matrix. -/
theorem RectMinNormSolution.exists_transpose_witness
    {m n : ℕ}
    {B : Fin m → Fin n → ℝ} {c : Fin m → ℝ} {y : Fin n → ℝ}
    (h : RectMinNormSolution m n B c y) :
    ∃ z : Fin m → ℝ, rectTransposeMulVec B z = y := by
  let BM : Matrix (Fin m) (Fin n) ℝ := B
  let Tlin : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
    Matrix.toEuclideanLin BM
  let T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    Tlin.toContinuousLinearMap
  let Y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 y
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
    LinearMap.ker T.toLinearMap

  rcases K.exists_add_mem_mem_orthogonal Y with
    ⟨u, hu, v, hv, hY⟩

  have hTu : T u = 0 := hu
  have hTvY : T v = T Y := by
    have hmap := congrArg T hY
    simpa [map_add, hTu] using hmap.symm
  have hTY : T Y = WithLp.toLp 2 c := by
    have hsystem := h.system_eq
    change T Y = WithLp.toLp 2 c
    rw [show T Y = WithLp.toLp 2 (rectMatMulVec B y) by
      ext i
      simp [T, Tlin, Y, BM, Matrix.toLpLin_apply,
        Matrix.mulVec, dotProduct, rectMatMulVec]]
    exact congrArg (WithLp.toLp 2) hsystem
  have hv_system : rectMatMulVec B (WithLp.ofLp v) = c := by
    have hz := congrArg WithLp.ofLp (hTvY.trans hTY)
    simpa [T, Tlin, BM, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, rectMatMulVec] using hz

  have hmin : vecNorm2 y ≤ vecNorm2 (WithLp.ofLp v) :=
    h.min_norm (WithLp.ofLp v) hv_system
  have hYnorm : ‖Y‖ = vecNorm2 y := by
    unfold Y vecNorm2 vecNorm2Sq
    rw [EuclideanSpace.norm_eq]
    simp [Real.norm_eq_abs, sq_abs]
  have hvnorm : ‖v‖ = vecNorm2 (WithLp.ofLp v) := by
    unfold vecNorm2 vecNorm2Sq
    rw [EuclideanSpace.norm_eq]
    simp [Real.norm_eq_abs, sq_abs]
  have hnorm : ‖Y‖ ≤ ‖v‖ := by
    simpa [hYnorm, hvnorm] using hmin
  have hinner : inner ℝ u v = 0 :=
    (K.mem_orthogonal v).mp hv u hu
  have hpyth : ‖Y‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    rw [hY]
    simpa [pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u v hinner
  have hnormsq : ‖Y‖ ^ 2 ≤ ‖v‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg Y) (norm_nonneg v)).2 hnorm
  have hu_norm : ‖u‖ = 0 := by
    nlinarith [sq_nonneg ‖u‖]
  have hu_zero : u = 0 := norm_eq_zero.mp hu_norm
  have hYv : Y = v := by
    simpa [hu_zero] using hY
  have hYorth : Y ∈ Kᗮ := hYv.symm ▸ hv

  have hYclosure : Y ∈ T.adjoint.range.topologicalClosure := by
    rw [← T.orthogonal_ker]
    exact hYorth
  have hYrange : Y ∈ T.adjoint.range := by
    simpa using hYclosure
  rcases hYrange with ⟨z, hz⟩
  refine ⟨WithLp.ofLp z, ?_⟩
  have hzlin : Matrix.toEuclideanLin BM.conjTranspose z = Y := by
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    simpa [T, Tlin, LinearMap.adjoint_eq_toCLM_adjoint] using hz
  have hzfun := congrArg WithLp.ofLp hzlin
  simpa [Y, BM, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, rectTransposeMulVec] using hzfun

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.4):
    algebraic normal-equation identity `A (Aᵀ y) = (A Aᵀ) y`. -/
theorem rectMatMulVec_rectTransposeMulVec {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (y : Fin m → ℝ) :
    rectMatMulVec A (rectTransposeMulVec A y) =
      matMulVec m (rectGram A) y := by
  ext i
  unfold rectMatMulVec rectTransposeMulVec matMulVec rectGram
  calc
    (∑ j : Fin n, A i j * ∑ r : Fin m, A r j * y r)
        = ∑ j : Fin n, ∑ r : Fin m, A i j * (A r j * y r) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
    _ = ∑ r : Fin m, ∑ j : Fin n, A i j * (A r j * y r) := by
            rw [Finset.sum_comm]
    _ = ∑ r : Fin m, (∑ j : Fin n, A i j * A r j) * y r := by
            apply Finset.sum_congr rfl
            intro r _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            ring

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.4):
    if `y` solves `(A Aᵀ)y = b`, then `Aᵀy` solves `A x = b`. -/
theorem rectTransposeMulVec_solves_of_gram_normal_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (AAT : Fin m → Fin m → ℝ)
    (b y : Fin m → ℝ)
    (hAAT : ∀ i j : Fin m, AAT i j = rectGram A i j)
    (hy : ∀ i : Fin m, matMulVec m AAT y i = b i) :
    rectMatMulVec A (rectTransposeMulVec A y) = b := by
  ext i
  rw [rectMatMulVec_rectTransposeMulVec]
  calc
    matMulVec m (rectGram A) y i = matMulVec m AAT y i := by
      unfold matMulVec
      apply Finset.sum_congr rfl
      intro j _
      rw [(hAAT i j).symm]
    _ = b i := hy i






































































































































































































































































































































































































































-- ============================================================
-- §21.2  Theorem 21.1: Demmel-Higham perturbation bound
-- ============================================================
































-- ============================================================
-- §21.2  Lemma 21.2: Kielbasiński-Schwetlick symmetrization
-- ============================================================





























end NumStability
