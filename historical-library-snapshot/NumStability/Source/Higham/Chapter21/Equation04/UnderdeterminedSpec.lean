import Mathlib.Data.Real.Basic
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Pseudoinverse.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Solvers.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Specifications.UnderdeterminedSpec
import NumStability.Analysis.MatrixAlgebra

/-!
# Source.Higham.Chapter21.Equation04.UnderdeterminedSpec

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







































































-- ============================================================
-- §21.2  Theorem 21.1: Demmel-Higham perturbation bound
-- ============================================================
































-- ============================================================
-- §21.2  Lemma 21.2: Kielbasiński-Schwetlick symmetrization
-- ============================================================





























end NumStability
