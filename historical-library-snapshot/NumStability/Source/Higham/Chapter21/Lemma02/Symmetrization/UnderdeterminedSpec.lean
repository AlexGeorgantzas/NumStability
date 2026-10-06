import Mathlib.Data.Real.Basic
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Pseudoinverse.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Specifications.UnderdeterminedSpec
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter21.Equation04.UnderdeterminedSpec

/-!
# Source.Higham.Chapter21.Lemma02.Symmetrization.UnderdeterminedSpec

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


















-- ============================================================
-- §21.2  Theorem 21.1: Demmel-Higham perturbation bound
-- ============================================================
































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
