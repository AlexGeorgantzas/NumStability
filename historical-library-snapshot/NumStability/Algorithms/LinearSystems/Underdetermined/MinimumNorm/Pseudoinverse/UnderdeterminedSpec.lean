import Mathlib.Data.Real.Basic
import NumStability.Analysis.MatrixAlgebra

/-!
# Algorithms.LinearSystems.Underdetermined.MinimumNorm.Pseudoinverse.UnderdeterminedSpec

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
























































-- ============================================================
-- §21.2  Theorem 21.1: Demmel-Higham perturbation bound
-- ============================================================
































-- ============================================================
-- §21.2  Lemma 21.2: Kielbasiński-Schwetlick symmetrization
-- ============================================================





























end NumStability
