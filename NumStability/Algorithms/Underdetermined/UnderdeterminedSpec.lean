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

import Mathlib.Data.Real.Basic
import NumStability.Analysis.MatrixAlgebra

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- §21.1  Minimum-norm solution specification
-- ============================================================

/-- **Minimum 2-norm solution of an underdetermined system** (Higham §21.1).

    For Ax = b with A ∈ ℝ^{m×n} (m < n), the minimum-norm solution is
    x_LS = Aᵀ(AAᵀ)⁻¹b. In the QR factorization framework with
    Aᵀ = Q[R; 0], this becomes x_LS = Q[R⁻ᵀb; 0].

    Since A is rectangular, we work with the m×m Gram matrix AAᵀ.
    The structure captures: (AAᵀ)⁻¹ exists (A has full row rank),
    and x solves the normal equations AAᵀy = b with x = Aᵀy. -/
structure MinNormSolution (m : ℕ)
    (AAT AAT_inv : Fin m → Fin m → ℝ)
    (b y : Fin m → ℝ) : Prop where
  /-- AAᵀ is invertible. -/
  gram_inv : IsInverse m AAT AAT_inv
  /-- y solves the normal equations AAᵀy = b. -/
  normal_eq : ∀ i, matMulVec m AAT y i = b i

/-- Euclidean norm of row `i` of a rectangular matrix. -/
noncomputable def rectRowNorm2 {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (i : Fin m) : ℝ :=
  vecNorm2 (fun j : Fin n => A i j)

/-- A rectangular row 2-norm is nonnegative. -/
theorem rectRowNorm2_nonneg {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (i : Fin m) : 0 ≤ rectRowNorm2 A i :=
  vecNorm2_nonneg _

/-- Higham, 2nd ed., Chapter 21, Section 21.1:
    exact minimum 2-norm solution predicate for a rectangular
    underdetermined system `A x = b`. -/
structure RectMinNormSolution (m n : ℕ)
    (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (x : Fin n → ℝ) : Prop where
  /-- The candidate solves the rectangular system. -/
  system_eq : rectMatMulVec A x = b
  /-- The candidate has no larger Euclidean norm than any other solution. -/
  min_norm : ∀ z : Fin n → ℝ, rectMatMulVec A z = b → vecNorm2 x ≤ vecNorm2 z

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.4):
    four-equation Moore--Penrose certificate for a rectangular table `Aplus`.

    For the full-row-rank underdetermined case, the concrete source table
    `Aᵀ(AAᵀ)⁻¹` should satisfy these identities and is therefore the source
    pseudoinverse `A⁺`. -/
structure RectMoorePenrosePseudoinverse (m n : ℕ)
    (A : Fin m → Fin n → ℝ)
    (Aplus : Fin n → Fin m → ℝ) : Prop where
  /-- Penrose equation `A A⁺ A = A`. -/
  reproduces_matrix :
    rectMatMul (rectMatMul A Aplus) A = A
  /-- Penrose equation `A⁺ A A⁺ = A⁺`. -/
  reproduces_pseudoinverse :
    rectMatMul (rectMatMul Aplus A) Aplus = Aplus
  /-- Penrose symmetry condition for `A A⁺`. -/
  range_projection_symmetric :
    IsSymmetricFiniteMatrix (rectMatMul A Aplus)
  /-- Penrose symmetry condition for `A⁺ A`. -/
  domain_projection_symmetric :
    IsSymmetricFiniteMatrix (rectMatMul Aplus A)

/-- A rectangular right inverse with a symmetric domain projection satisfies
    the four Moore--Penrose equations. -/
theorem rectMoorePenrosePseudoinverse_of_right_inverse_and_domain_symmetric
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ)
    (hright : rectMatMul A Aplus = idMatrix m)
    (hdomain : IsSymmetricFiniteMatrix (rectMatMul Aplus A)) :
    RectMoorePenrosePseudoinverse m n A Aplus := by
  constructor
  · calc
      rectMatMul (rectMatMul A Aplus) A
          = rectMatMul (idMatrix m) A := by rw [hright]
      _ = A := rectMatMul_id_left A
  · calc
      rectMatMul (rectMatMul Aplus A) Aplus
          = rectMatMul Aplus (rectMatMul A Aplus) :=
              rectMatMul_assoc Aplus A Aplus
      _ = rectMatMul Aplus (idMatrix m) := by rw [hright]
      _ = Aplus := rectMatMul_id_right Aplus
  · rw [hright]
    intro i j
    simp [idMatrix, eq_comm]
  · exact hdomain

/-- Rectangular Gram matrix `A Aᵀ` for an underdetermined system. -/
noncomputable def rectGram {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    Fin m → Fin m → ℝ :=
  fun i j => ∑ k : Fin n, A i k * A j k

/-- The rectangular Gram matrix `A Aᵀ` is symmetric. -/
theorem rectGram_symmetric {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    IsSymmetricFiniteMatrix (rectGram A) := by
  intro i j
  unfold rectGram
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Transpose-times-vector action `Aᵀ y` for a rectangular matrix. -/
noncomputable def rectTransposeMulVec {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (y : Fin m → ℝ) : Fin n → ℝ :=
  fun j => ∑ i : Fin m, A i j * y i

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.4):
    every vector of the form `Aᵀ y` is orthogonal to the nullspace of `A`.
    This is the algebraic orthogonality fact behind the minimum-norm
    characterization of `Aᵀ(AAᵀ)⁻¹b`. -/
theorem higham21_eq21_4_rect_transpose_nullspace_orthogonal {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (y : Fin m → ℝ) (z : Fin n → ℝ)
    (hz : rectMatMulVec A z = (0 : Fin m → ℝ)) :
    ∑ j : Fin n, rectTransposeMulVec A y j * z j = 0 := by
  unfold rectTransposeMulVec
  calc
    ∑ j : Fin n, (∑ i : Fin m, A i j * y i) * z j
        = ∑ j : Fin n, ∑ i : Fin m, (A i j * y i) * z j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
    _ = ∑ i : Fin m, ∑ j : Fin n, (A i j * y i) * z j := by
            rw [Finset.sum_comm]
    _ = ∑ i : Fin m, y i * rectMatMulVec A z i := by
            apply Finset.sum_congr rfl
            intro i _
            unfold rectMatMulVec
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = 0 := by
            rw [hz]
            simp

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

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.4):
    if a vector of the form `Aᵀ y` solves `A x = b`, then it is the
    minimum 2-norm solution of the rectangular underdetermined system.
    This closes the minimum-norm direction of the normal-equation formula;
    the explicit inverse/pseudoinverse construction remains separate. -/
theorem higham21_eq21_4_rect_transpose_min_norm_of_solves {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin m → ℝ)
    (hsolve : rectMatMulVec A (rectTransposeMulVec A y) = b) :
    RectMinNormSolution m n A b (rectTransposeMulVec A y) :=
  rectMinNormSolution_of_system_eq_and_nullspace_orthogonal
    A b (rectTransposeMulVec A y) hsolve
    (fun e he =>
      higham21_eq21_4_rect_transpose_nullspace_orthogonal A y e he)

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.4):
    uniqueness of the minimum 2-norm solution against a feasible transpose-form
    solution.  If `x` is already known to be a minimum-norm solution of
    `A x = b` and some vector `Aᵀ y` solves the same system, then `x = Aᵀ y`.

    This is the range/transpose bridge used by later Chapter 21 perturbation
    handoffs: a source minimum-norm candidate can be rewritten in transpose
    form once the perturbed normal equations provide the feasible dual vector. -/
theorem rectMinNormSolution_eq_of_transpose_solution {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ)
    (hx : RectMinNormSolution m n A b x)
    (hy : rectMatMulVec A (rectTransposeMulVec A y) = b) :
    x = rectTransposeMulVec A y := by
  let z : Fin n → ℝ := rectTransposeMulVec A y
  let e : Fin n → ℝ := fun j => x j - z j
  have he_kernel : rectMatMulVec A e = (0 : Fin m → ℝ) := by
    unfold e z
    rw [rectMatMulVec_sub, hx.system_eq, hy]
    ext i
    simp
  have horth : (∑ j : Fin n, z j * e j) = 0 := by
    simpa [z, e] using
      higham21_eq21_4_rect_transpose_nullspace_orthogonal A y e he_kernel
  have hx_decomp : x = fun j : Fin n => z j + e j := by
    ext j
    simp [z, e]
  have hpyth : vecNorm2Sq x = vecNorm2Sq z + vecNorm2Sq e := by
    rw [hx_decomp]
    simpa [finiteVecNorm2Sq_fin] using
      finiteVecNorm2Sq_add_of_inner_eq_zero z e horth
  have hnorm_le : vecNorm2 x ≤ vecNorm2 z :=
    hx.min_norm z hy
  have hsquare_le_norm : vecNorm2 x ^ 2 ≤ vecNorm2 z ^ 2 := by
    nlinarith [hnorm_le, vecNorm2_nonneg x, vecNorm2_nonneg z]
  have hsquare_le : vecNorm2Sq x ≤ vecNorm2Sq z := by
    rw [← vecNorm2_sq x, ← vecNorm2_sq z]
    exact hsquare_le_norm
  have he_zero_sq : vecNorm2Sq e = 0 := by
    nlinarith [hpyth, hsquare_le, vecNorm2Sq_nonneg e]
  have he_norm_zero : vecNorm2 e = 0 := by
    have hs : vecNorm2 e ^ 2 = 0 := by
      simpa [vecNorm2_sq e] using he_zero_sq
    exact sq_eq_zero_iff.mp hs
  have he_zero : e = 0 := by
    ext j
    exact (vecNorm2_eq_zero_iff e).mp he_norm_zero j
  ext j
  have hj := congrFun he_zero j
  simp [e, z] at hj
  exact sub_eq_zero.mp hj

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

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.4):
    source-facing wrapper for the normal-equation direction of
    `x_LS = Aᵀ(AAᵀ)⁻¹b`.  The minimum-norm and pseudoinverse parts remain
    separate selected targets. -/
theorem higham21_eq21_4_rect_transpose_solves {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (AAT : Fin m → Fin m → ℝ)
    (b y : Fin m → ℝ)
    (hAAT : ∀ i j : Fin m, AAT i j = rectGram A i j)
    (hy : ∀ i : Fin m, matMulVec m AAT y i = b i) :
    rectMatMulVec A (rectTransposeMulVec A y) = b :=
  rectTransposeMulVec_solves_of_gram_normal_eq A AAT b y hAAT hy

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.4):
    source-facing normal-equation minimum-norm wrapper.  If `y` solves
    `(A Aᵀ)y = b`, then the formed vector `Aᵀy` is an exact minimum
    2-norm solution of `A x = b`.  The explicit inverse/pseudoinverse
    construction remains a separate selected target. -/
theorem higham21_eq21_4_rect_transpose_min_norm_of_gram_normal_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (AAT : Fin m → Fin m → ℝ)
    (b y : Fin m → ℝ)
    (hAAT : ∀ i j : Fin m, AAT i j = rectGram A i j)
    (hy : ∀ i : Fin m, matMulVec m AAT y i = b i) :
    RectMinNormSolution m n A b (rectTransposeMulVec A y) :=
  higham21_eq21_4_rect_transpose_min_norm_of_solves A b y
    (rectTransposeMulVec_solves_of_gram_normal_eq A AAT b y hAAT hy)

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.4):
    normal-equation range rewrite for an already-known minimum-norm solution.
    If `x` is the minimum 2-norm solution of `A x = b` and `y` solves
    `(A Aᵀ)y = b`, then the minimum-norm solution is the transpose-form vector
    `Aᵀ y`.

    This is a source-facing bridge for later perturbation arguments: after
    a perturbed Gram normal equation supplies the dual vector, a minimum-norm
    candidate can be rewritten in the required transpose/range form. -/
theorem rectMinNormSolution_eq_transpose_of_gram_normal_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (AAT : Fin m → Fin m → ℝ)
    (b y : Fin m → ℝ)
    (x : Fin n → ℝ)
    (hx : RectMinNormSolution m n A b x)
    (hAAT : ∀ i j : Fin m, AAT i j = rectGram A i j)
    (hy : ∀ i : Fin m, matMulVec m AAT y i = b i) :
    x = rectTransposeMulVec A y :=
  rectMinNormSolution_eq_of_transpose_solution A b x y hx
    (rectTransposeMulVec_solves_of_gram_normal_eq A AAT b y hAAT hy)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    perturbed-Gram specialization of the transpose/range rewrite.  For
    `B = A + DeltaA2`, a minimum-norm solution of `B x = b` equals `Bᵀ y`
    once `y` solves the perturbed Gram normal equation `(B Bᵀ)y = b`.

    The remaining source perturbation work is to produce this perturbed Gram
    dual solution and prove the associated nonsingularity/operator estimates. -/
theorem higham21_lemma21_2_transpose_range_of_min_norm_and_perturbed_gram_normal_eq
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (DeltaA2 : Fin m → Fin n → ℝ)
    (b y : Fin m → ℝ)
    (x : Fin n → ℝ)
    (hx : RectMinNormSolution m n (fun i j => A i j + DeltaA2 i j) b x)
    (hy : ∀ i : Fin m,
      matMulVec m (rectGram (fun i j => A i j + DeltaA2 i j)) y i = b i) :
    x = rectTransposeMulVec (fun i j => A i j + DeltaA2 i j) y :=
  rectMinNormSolution_eq_transpose_of_gram_normal_eq
    (fun i j => A i j + DeltaA2 i j)
    (rectGram (fun i j => A i j + DeltaA2 i j)) b y x hx
    (by intro i j; rfl) hy

/-- Concrete table for the source expression `Aᵀ(AAᵀ)⁻¹` in Higham,
    2nd ed., Chapter 21, Section 21.1, equation (21.4), parameterized by a
    supplied inverse candidate for `AAᵀ`. -/
noncomputable def undetAplusOfGramInv {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ) : Fin n → Fin m → ℝ :=
  fun j i => ∑ k : Fin m, A k j * AAT_inv k i

/-- Repository nonsingular inverse candidate for the underdetermined Gram
    matrix `AAᵀ` in Higham, 2nd ed., Chapter 21, equation (21.4). -/
noncomputable def undetGramNonsingInv {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin m → Fin m → ℝ :=
  nonsingInv m (rectGram A)

/-- Concrete determinant-facing table for `Aᵀ(AAᵀ)⁻¹` using the repository
    nonsingular inverse candidate for `AAᵀ`. -/
noncomputable def undetAplusOfGramNonsingInv {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin n → Fin m → ℝ :=
  undetAplusOfGramInv A (undetGramNonsingInv A)

/-- The concrete table `Aᵀ AAT_inv` is the rectangular product of `Aᵀ`
    with the supplied Gram inverse candidate. -/
theorem undetAplusOfGramInv_eq_rectMatMul_finiteTranspose {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ) :
    undetAplusOfGramInv A AAT_inv =
      rectMatMul (finiteTranspose A) AAT_inv := by
  ext j i
  rfl

/-- Higham, 2nd ed., Chapter 21, equation (21.4) and Lemma 21.2:
    operator-bound handoff for the concrete Gram pseudoinverse table.
    Bounds on `A` and a supplied Gram inverse candidate imply an operator bound
    for `Aᵀ AAT_inv`.  This is a reusable dependency for the remaining
    perturbed-pseudoinverse operator estimate. -/
theorem rectOpNorm2Le_undetAplusOfGramInv_of_bounds {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    {sigma eta : ℝ}
    (hsigma : 0 ≤ sigma)
    (hA : rectOpNorm2Le A sigma)
    (hAAT_inv : rectOpNorm2Le AAT_inv eta) :
    rectOpNorm2Le (undetAplusOfGramInv A AAT_inv) (sigma * eta) := by
  rw [undetAplusOfGramInv_eq_rectMatMul_finiteTranspose]
  exact
    rectOpNorm2Le_rectMatMul (finiteTranspose A) AAT_inv hsigma
      (rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le A hsigma hA)
      hAAT_inv

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    determinant-facing operator-bound handoff for the concrete perturbed Gram
    pseudoinverse table `Aᵀ(AAᵀ)⁻¹` using the repository nonsingular inverse
    candidate.  The remaining source work is to bound the perturbed matrix and
    the nonsingular inverse candidate. -/
theorem rectOpNorm2Le_undetAplusOfGramNonsingInv_of_bounds {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    {sigma eta : ℝ}
    (hsigma : 0 ≤ sigma)
    (hA : rectOpNorm2Le A sigma)
    (hGramInv : rectOpNorm2Le (undetGramNonsingInv A) eta) :
    rectOpNorm2Le (undetAplusOfGramNonsingInv A) (sigma * eta) :=
  rectOpNorm2Le_undetAplusOfGramInv_of_bounds
    A (undetGramNonsingInv A) hsigma hA hGramInv

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    determinant-facing version of the perturbed transpose/range rewrite.  If
    `B = A + DeltaA2` has nonsingular Gram matrix and `x` is the minimum-norm
    solution of `B x = b`, then `x` is the transpose-form vector obtained from
    the repository nonsingular inverse candidate for `B Bᵀ`.

    This discharges the explicit dual-vector construction once the source
    perturbation proof has supplied perturbed Gram nonsingularity. -/
theorem higham21_lemma21_2_transpose_range_of_min_norm_and_perturbed_gram_det_ne_zero
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (DeltaA2 : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (x : Fin n → ℝ)
    (hx : RectMinNormSolution m n (fun i j => A i j + DeltaA2 i j) b x)
    (hdet :
      Matrix.det
          (rectGram (fun i j => A i j + DeltaA2 i j) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0) :
    x =
      rectTransposeMulVec (fun i j => A i j + DeltaA2 i j)
        (matMulVec m
          (undetGramNonsingInv (fun i j => A i j + DeltaA2 i j)) b) := by
  let B : Fin m → Fin n → ℝ := fun i j => A i j + DeltaA2 i j
  have hdetB : Matrix.det (rectGram B : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
    simpa [B] using hdet
  have hInv : IsInverse m (rectGram B) (undetGramNonsingInv B) :=
    isInverse_nonsingInv_of_det_ne_zero m (rectGram B) hdetB
  have hy : ∀ i : Fin m,
      matMulVec m (rectGram B)
          (matMulVec m (undetGramNonsingInv B) b) i = b i := by
    intro i
    exact congrFun
      (matMulVec_of_isRightInverse
        (rectGram B) (undetGramNonsingInv B) hInv.2 b) i
  simpa [B] using
    higham21_lemma21_2_transpose_range_of_min_norm_and_perturbed_gram_normal_eq
      A DeltaA2 b (matMulVec m (undetGramNonsingInv B) b) x hx
      (by simpa [B] using hy)

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.4):
    the concrete table `Aᵀ(AAᵀ)⁻¹` is a right inverse of `A` when the
    supplied inverse candidate is an inverse of `AAᵀ`. -/
theorem higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_inverse
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (AAT AAT_inv : Fin m → Fin m → ℝ)
    (hAAT : ∀ i j : Fin m, AAT i j = rectGram A i j)
    (hInv : IsInverse m AAT AAT_inv) :
    rectMatMul A (undetAplusOfGramInv A AAT_inv) = idMatrix m := by
  ext i j
  unfold rectMatMul undetAplusOfGramInv idMatrix
  calc
    ∑ k : Fin n, A i k * (∑ r : Fin m, A r k * AAT_inv r j)
        = ∑ k : Fin n, ∑ r : Fin m, A i k * (A r k * AAT_inv r j) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.mul_sum]
    _ = ∑ r : Fin m, ∑ k : Fin n, A i k * (A r k * AAT_inv r j) := by
            rw [Finset.sum_comm]
    _ = ∑ r : Fin m, (∑ k : Fin n, A i k * A r k) * AAT_inv r j := by
            apply Finset.sum_congr rfl
            intro r _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ = ∑ r : Fin m, AAT i r * AAT_inv r j := by
            apply Finset.sum_congr rfl
            intro r _
            simpa [rectGram] using
              congrArg (fun t : ℝ => t * AAT_inv r j) (hAAT i r).symm
    _ = if i = j then 1 else 0 := hInv.2 i j

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.4):
    determinant-facing right-inverse form of `Aᵀ(AAᵀ)⁻¹`. -/
theorem higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) ≠ 0) :
    rectMatMul A (undetAplusOfGramNonsingInv A) = idMatrix m :=
  higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_inverse
    A (rectGram A) (undetGramNonsingInv A)
    (by intro i j; rfl)
    (isInverse_nonsingInv_of_det_ne_zero m (rectGram A) hdet)

/-- Applying the concrete table `Aᵀ(AAᵀ)⁻¹` to `b` is the same as first
    solving for `y = (AAᵀ)⁻¹b` and then forming `Aᵀy`. -/
theorem rectMatMulVec_undetAplusOfGramInv {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (b : Fin m → ℝ) :
    rectMatMulVec (undetAplusOfGramInv A AAT_inv) b =
      rectTransposeMulVec A (matMulVec m AAT_inv b) := by
  ext j
  unfold rectMatMulVec undetAplusOfGramInv rectTransposeMulVec matMulVec
  calc
    ∑ i : Fin m, (∑ k : Fin m, A k j * AAT_inv k i) * b i
        = ∑ i : Fin m, ∑ k : Fin m, (A k j * AAT_inv k i) * b i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
    _ = ∑ k : Fin m, ∑ i : Fin m, (A k j * AAT_inv k i) * b i := by
            rw [Finset.sum_comm]
    _ = ∑ k : Fin m, A k j * ∑ i : Fin m, AAT_inv k i * b i := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.4):
    determinant/inverse-candidate-facing form of the formula
    `x_LS = Aᵀ(AAᵀ)⁻¹b`.  If `AAT_inv` is an inverse of the Gram matrix
    `AAᵀ`, then the concrete table `Aᵀ AAT_inv` applied to `b` is an exact
    minimum 2-norm solution of `A x = b`.

    This proves the explicit inverse-action part of (21.4); identifying the
    same table with the Moore--Penrose pseudoinverse `A⁺` remains a separate
    selected target. -/
theorem higham21_eq21_4_rect_pseudoinverse_formula_min_norm_of_gram_inverse
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (AAT AAT_inv : Fin m → Fin m → ℝ)
    (b : Fin m → ℝ)
    (hAAT : ∀ i j : Fin m, AAT i j = rectGram A i j)
    (hInv : IsInverse m AAT AAT_inv) :
    RectMinNormSolution m n A b
      (rectMatMulVec (undetAplusOfGramInv A AAT_inv) b) := by
  rw [rectMatMulVec_undetAplusOfGramInv]
  exact higham21_eq21_4_rect_transpose_min_norm_of_gram_normal_eq
    A AAT b (matMulVec m AAT_inv b) hAAT
    (fun i => congrFun (matMulVec_of_isRightInverse AAT AAT_inv hInv.2 b) i)

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.4):
    determinant-facing concrete form of `x_LS = Aᵀ(AAᵀ)⁻¹b`.  If the Gram
    matrix `AAᵀ` has nonzero determinant, then the repository nonsingular
    inverse candidate gives an exact minimum 2-norm solution. -/
theorem higham21_eq21_4_rect_pseudoinverse_formula_min_norm_of_gram_det_ne_zero
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) ≠ 0) :
    RectMinNormSolution m n A b
      (rectMatMulVec (undetAplusOfGramNonsingInv A) b) :=
  higham21_eq21_4_rect_pseudoinverse_formula_min_norm_of_gram_inverse
    A (rectGram A) (undetGramNonsingInv A) b
    (by intro i j; rfl)
    (isInverse_nonsingInv_of_det_ne_zero m (rectGram A) hdet)

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.4):
    the domain-side projection `Aᵀ(AAᵀ)⁻¹ A` is symmetric when the supplied
    inverse table for `AAᵀ` is symmetric. -/
theorem undetAplusOfGramInv_domain_projection_symmetric {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (AAT_inv : Fin m → Fin m → ℝ)
    (hInvSym : IsSymmetricFiniteMatrix AAT_inv) :
    IsSymmetricFiniteMatrix (rectMatMul (undetAplusOfGramInv A AAT_inv) A) := by
  intro j k
  unfold rectMatMul undetAplusOfGramInv
  calc
    ∑ l : Fin m, (∑ r : Fin m, A r j * AAT_inv r l) * A l k
        = ∑ l : Fin m, ∑ r : Fin m,
            (A r j * AAT_inv r l) * A l k := by
            apply Finset.sum_congr rfl
            intro l _
            rw [Finset.sum_mul]
    _ = ∑ r : Fin m, ∑ l : Fin m,
            (A r j * AAT_inv r l) * A l k := by
            rw [Finset.sum_comm]
    _ = ∑ r : Fin m, ∑ l : Fin m,
            (A r j * AAT_inv l r) * A l k := by
            apply Finset.sum_congr rfl
            intro r _
            apply Finset.sum_congr rfl
            intro l _
            rw [hInvSym r l]
    _ = ∑ r : Fin m, ∑ l : Fin m,
            (A l k * AAT_inv l r) * A r j := by
            apply Finset.sum_congr rfl
            intro r _
            apply Finset.sum_congr rfl
            intro l _
            ring
    _ = ∑ l : Fin m, ∑ r : Fin m,
            (A r k * AAT_inv r l) * A l j := by
            rw [Finset.sum_comm]
    _ = ∑ l : Fin m, (∑ r : Fin m, A r k * AAT_inv r l) * A l j := by
            apply Finset.sum_congr rfl
            intro l _
            rw [Finset.sum_mul]

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.4):
    determinant-facing symmetry of the domain projection
    `Aᵀ(AAᵀ)⁻¹ A`. -/
theorem undetAplusOfGramNonsingInv_domain_projection_symmetric {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    IsSymmetricFiniteMatrix (rectMatMul (undetAplusOfGramNonsingInv A) A) :=
  undetAplusOfGramInv_domain_projection_symmetric A (undetGramNonsingInv A)
    (nonsingInv_symmetric_of_symmetric (rectGram A) (rectGram_symmetric A))

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.4):
    determinant-facing Moore--Penrose certificate for the concrete source table
    `Aᵀ(AAᵀ)⁻¹`.  This is the algebraic identification of that table with
    `A⁺` under the full-row-rank Gram nonsingularity hypothesis. -/
theorem higham21_eq21_4_rect_moore_penrose_of_gram_det_ne_zero
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) ≠ 0) :
    RectMoorePenrosePseudoinverse m n A (undetAplusOfGramNonsingInv A) :=
  rectMoorePenrosePseudoinverse_of_right_inverse_and_domain_symmetric
    A (undetAplusOfGramNonsingInv A)
    (higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero A hdet)
    (undetAplusOfGramNonsingInv_domain_projection_symmetric A)

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    the Moore--Penrose domain projection `A⁺A` fixes every vector explicitly
    represented in the range of `A⁺`.  This is the projection-fixes-`x`
    component needed by the perturbed-pseudoinverse route when the candidate
    `x` has already been identified as a pseudoinverse-applied right-hand side. -/
theorem rectMoorePenrosePseudoinverse_domain_projection_apply_range
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ)
    (hMP : RectMoorePenrosePseudoinverse m n A Aplus)
    (y : Fin m → ℝ) :
    rectMatMulVec (rectMatMul Aplus A) (rectMatMulVec Aplus y) =
      rectMatMulVec Aplus y := by
  rw [← rectMatMulVec_rectMatMul (rectMatMul Aplus A) Aplus y]
  rw [hMP.reproduces_pseudoinverse]

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    concrete determinant-facing version of the projection-fixes-range fact for
    the underdetermined Gram pseudoinverse table `Aᵀ(AAᵀ)⁻¹`. -/
theorem higham21_lemma21_2_gram_pseudoinverse_domain_projection_apply_range
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (y : Fin m → ℝ) :
    rectMatMulVec (rectMatMul (undetAplusOfGramNonsingInv A) A)
        (rectMatMulVec (undetAplusOfGramNonsingInv A) y) =
      rectMatMulVec (undetAplusOfGramNonsingInv A) y :=
  rectMoorePenrosePseudoinverse_domain_projection_apply_range
    A (undetAplusOfGramNonsingInv A)
    (higham21_eq21_4_rect_moore_penrose_of_gram_det_ne_zero A hdet) y

/-- Higham, 2nd ed., Chapter 21, Lemma 21.2:
    under full-row-rank Gram nonsingularity, every source vector of the form
    `Aᵀ y` is represented in the concrete Gram-pseudoinverse range.  The
    witness is `(A Aᵀ)y`, since `A⁺((AAᵀ)y) = Aᵀy`. -/
theorem higham21_lemma21_2_gram_pseudoinverse_range_of_transpose
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (y : Fin m → ℝ) :
    rectTransposeMulVec A y =
      rectMatMulVec (undetAplusOfGramNonsingInv A)
        (matMulVec m (rectGram A) y) := by
  have hInv : IsInverse m (rectGram A) (undetGramNonsingInv A) :=
    isInverse_nonsingInv_of_det_ne_zero m (rectGram A) hdet
  have hleft :
      matMulVec m (undetGramNonsingInv A)
          (matMulVec m (rectGram A) y) = y := by
    simpa [undetGramNonsingInv] using
      matMulVec_of_isRightInverse
        (nonsingInv m (rectGram A)) (rectGram A) hInv.1 y
  rw [undetAplusOfGramNonsingInv, rectMatMulVec_undetAplusOfGramInv]
  rw [hleft]

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.5):
    source-facing wrapper for the SNE formation step.  Once the seminormal
    equation matrix is identified with `A Aᵀ`, solving that Gram system and
    forming `x = Aᵀ y` gives a solution of the rectangular system `A x = b`.
    This does not assert the full minimum-norm or QR-derived stability result. -/
theorem higham21_eq21_5_sne_rect_transpose_solution {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (SNE : Fin m → Fin m → ℝ)
    (b y : Fin m → ℝ)
    (x : Fin n → ℝ)
    (hSNE : ∀ i j : Fin m, SNE i j = rectGram A i j)
    (hy : ∀ i : Fin m, matMulVec m SNE y i = b i)
    (hx : x = rectTransposeMulVec A y) :
    rectMatMulVec A x = b := by
  rw [hx]
  exact rectTransposeMulVec_solves_of_gram_normal_eq A SNE b y hSNE hy

-- ============================================================
-- §21.2  Theorem 21.1: Demmel-Higham perturbation bound
-- ============================================================

/-- **Theorem 21.1** (Demmel and Higham): Componentwise perturbation
    of the minimum 2-norm solution to an underdetermined system.

    Let A ∈ ℝ^{m×n} (m ≤ n) be of full rank, and let x, y be the
    minimum 2-norm solutions to Ax = b and (A+ΔA)y = b+Δb. Then:

    ‖x−y‖/‖x‖ ≤ (‖|I−A⁺A|·Eᵀ·|A⁺ᵀx|‖ + ‖|A⁺|·(f+E|x|)‖)·ε/‖x‖ + O(ε²)

    where |ΔA| ≤ εE, |Δb| ≤ εf.

    Special cases (eqs. 21.8-21.9):
    - E = |A|H, f = |b|: bound involves cond₂(A) = ‖|A⁺||A|‖₂
    - Normwise: ‖x−y‖₂/‖x‖₂ ≤ min{3,n−m+2}(mn)^{1/2}κ₂(A)ε + O(ε²)

    This legacy compatibility record predates the completed rectangular
    pseudoinverse development. It is not the source-facing proof of Theorem
    21.1; the proved expansion and finite-radius endpoints live in the
    `Higham21Perturbation` and `Higham21PerturbationRadius` modules. -/
structure DemmelHighamPerturbation (m : ℕ)
    (x y : Fin m → ℝ) (kappa eps : ℝ)
    (sol_bound : ℝ) : Prop where
  /-- κ₂(A) > 0. -/
  kappa_pos : 0 < kappa
  /-- ε is nonnegative. -/
  eps_nonneg : 0 ≤ eps
  /-- The perturbation is small enough. -/
  small_pert : kappa * eps < 1
  /-- Forward error bound (normwise form, eq. 21.9):
      ‖x−y‖₂ ≤ sol_bound. -/
  bound : ∀ i, |y i - x i| ≤ sol_bound

-- ============================================================
-- §21.2  Lemma 21.2: Kielbasiński-Schwetlick symmetrization
-- ============================================================

/-- **Lemma 21.2** (Kielbasiński and Schwetlick): Perturbation symmetrization
    for underdetermined normal equations.

    If x̄ satisfies (A+ΔA₁)x̄ = b and x̄ = (A+ΔA₂)ᵀȳ, then there
    exists a single ΔA with ΔA = ΔA₁G₁ + ΔA₂G₂ (G₁+G₂=I) such that
    x̄ is the minimum 2-norm solution to (A+ΔA)x = b.

    The normwise bound satisfies: ‖ΔA‖_p ≤ (‖ΔA₁‖²_p + ‖ΔA₂‖²_p)^{1/2}.

    This is the underdetermined analogue of Lemma 20.6. The structure is a
    legacy compatibility record and is not evidence for the source lemma;
    `higham21_lemma21_2_source_bundle` supplies the proved single-perturbation
    construction and norm bounds. -/
structure KielbasinskiSchwetlickUndet (m : ℕ)
    (AAT : Fin m → Fin m → ℝ)
    (b : Fin m → ℝ)
    (x_hat : Fin m → ℝ)
    (eps1 eps2 : ℝ) : Prop where
  /-- Perturbation bounds are nonneg. -/
  eps_nonneg : 0 ≤ eps1 ∧ 0 ≤ eps2
  /-- There exists a symmetrized perturbation ΔG to the Gram system
      with ‖ΔG‖ ≤ (eps1² + eps2²)^{1/2} such that x̂ is the
      minimum-norm solution to a nearby system. -/
  symmetrized : ∃ (ΔG : Fin m → Fin m → ℝ),
    frobNorm ΔG ≤
      Real.sqrt (eps1 ^ 2 + eps2 ^ 2) ∧
    (∀ i, matMulVec m (fun a b => AAT a b + ΔG a b) x_hat i = b i)

end NumStability
