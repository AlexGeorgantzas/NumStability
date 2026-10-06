import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.LeastSquares.MGS
import NumStability.Algorithms.LinearSystems.QR.HouseholderQR
import NumStability.Algorithms.LinearSystems.QR.Householder.StoredQR
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Algorithms.LinearSystems.QR.QRSolve
import NumStability.Algorithms.LinearSystems.Triangular.DiagonalDominance
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.Analysis.SingularValues.Realification
import NumStability.Analysis.VectorNorms.Basic
import NumStability.FloatingPoint.Model

namespace NumStability

open scoped BigOperators
open scoped BigOperators Matrix.Norms.Frobenius

/-!
# Basic

Canonical reusable module extracted without change from Higham20AlternativeBound, Higham20ResidualQuality, LSQRSolve.
-/

/-- Rectangular normal-equation Gram matrix `Aᵀ A`. -/
noncomputable def rectLSGram {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun j k => ∑ i : Fin m, A i j * A i k
/-- Rectangular normal-equation right-hand side `Aᵀ b`. -/
noncomputable def rectLSRhs {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) : Fin n → ℝ :=
  fun j => ∑ i : Fin m, A i j * b i
/-- Least-squares residual vector `A x - b` for a rectangular matrix.

    Higham, 2nd ed., Chapter 20 uses the opposite sign `b - A x` for residuals
    in some displays; the squared objective is unchanged by this convention. -/
noncomputable def lsResidual {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => rectMatMulVec A x i - b i
/-- Squared least-squares objective `||A x - b||₂²`. -/
noncomputable def lsObjective {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) : ℝ :=
  vecNorm2Sq (lsResidual A b x)
/-- Row permutations preserve the least-squares residual, up to the same
    permutation of residual coordinates. -/
theorem lsResidual_permuteRows {m n : ℕ} (σ : Fin m ≃ Fin m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    lsResidual (rectPermuteRows σ A) (vecPermute σ b) x =
      vecPermute σ (lsResidual A b x) := by
  ext i
  rfl
/-- Row sorting/pivoting does not change the least-squares objective when the
    right-hand side is permuted by the same row map. -/
theorem lsObjective_permuteRows {m n : ℕ} (σ : Fin m ≃ Fin m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    lsObjective (rectPermuteRows σ A) (vecPermute σ b) x =
      lsObjective A b x := by
  unfold lsObjective
  rw [lsResidual_permuteRows, vecNorm2Sq_permute]
/-- Column permutations preserve the residual after pulling the coefficient
    vector back by the inverse column permutation. -/
theorem lsResidual_permuteCols {m n : ℕ} (π : Fin n ≃ Fin n)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    lsResidual (rectPermuteCols π A) b x =
      lsResidual A b (vecPermute π.symm x) := by
  unfold lsResidual
  rw [rectMatMulVec_permuteCols]
/-- Column pivoting does not change the least-squares objective after pulling
    the coefficient vector back by the inverse column permutation. -/
theorem lsObjective_permuteCols {m n : ℕ} (π : Fin n ≃ Fin n)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    lsObjective (rectPermuteCols π A) b x =
      lsObjective A b (vecPermute π.symm x) := by
  unfold lsObjective
  rw [lsResidual_permuteCols]
/-- Combined row sorting and column pivoting preserve residuals up to row
    permutation, after pulling coefficients back by the inverse column
    permutation. -/
theorem lsResidual_permuteRowsCols {m n : ℕ}
    (σ : Fin m ≃ Fin m) (π : Fin n ≃ Fin n)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    lsResidual (rectPermuteRows σ (rectPermuteCols π A)) (vecPermute σ b) x =
      vecPermute σ (lsResidual A b (vecPermute π.symm x)) := by
  rw [lsResidual_permuteRows, lsResidual_permuteCols]
/-- Row sorting plus column pivoting does not change the least-squares
    objective after pulling coefficients back by the inverse column
    permutation. -/
theorem lsObjective_permuteRowsCols {m n : ℕ}
    (σ : Fin m ≃ Fin m) (π : Fin n ≃ Fin n)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    lsObjective (rectPermuteRows σ (rectPermuteCols π A)) (vecPermute σ b) x =
      lsObjective A b (vecPermute π.symm x) := by
  unfold lsObjective
  rw [lsResidual_permuteRowsCols, vecNorm2Sq_permute]
/-- Rectangular matrix-vector multiplication after a square left factor:
    `(U A) x = U (A x)`. -/
theorem rectMatMulVec_matMulRectLeft {m n : ℕ}
    (U : Fin m → Fin m → ℝ) (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ) :
    rectMatMulVec (matMulRectLeft U A) x =
      matMulVec m U (rectMatMulVec A x) := by
  ext i
  unfold rectMatMulVec matMulRectLeft matMulVec
  calc
    ∑ j : Fin n, (∑ k : Fin m, U i k * A k j) * x j
        = ∑ j : Fin n, ∑ k : Fin m, (U i k * A k j) * x j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
    _ = ∑ k : Fin m, ∑ j : Fin n, (U i k * A k j) * x j := by
            rw [Finset.sum_comm]
    _ = ∑ k : Fin m, U i k * ∑ j : Fin n, A k j * x j := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
/-- Residuals transform equivariantly under a common square left factor:
    `(U A)x - U b = U(Ax - b)`. -/
theorem lsResidual_matMulRectLeft {m n : ℕ}
    (U : Fin m → Fin m → ℝ) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) :
    lsResidual (matMulRectLeft U A) (matMulVec m U b) x =
      matMulVec m U (lsResidual A b x) := by
  ext i
  unfold lsResidual
  rw [congrFun (rectMatMulVec_matMulRectLeft U A x) i]
  unfold matMulVec
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring
/-- Orthogonal row transformations preserve the squared least-squares
    objective when applied to both the matrix and the right-hand side. -/
theorem lsObjective_matMulRectLeft_orthogonal {m n : ℕ}
    (U : Fin m → Fin m → ℝ) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ)
    (hU : IsOrthogonal m U) :
    lsObjective (matMulRectLeft U A) (matMulVec m U b) x =
      lsObjective A b x := by
  unfold lsObjective
  rw [lsResidual_matMulRectLeft]
  exact vecNorm2Sq_orthogonal U (lsResidual A b x) hU
/-- Residuals commute with a right change of variables:
    `(A C)y - b = A(C y) - b`. -/
theorem lsResidual_rectMatMul_right {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (C : Fin n → Fin p → ℝ)
    (b : Fin m → ℝ) (y : Fin p → ℝ) :
    lsResidual (rectMatMul A C) b y =
      lsResidual A b (rectMatMulVec C y) := by
  ext i
  unfold lsResidual
  rw [congrFun (rectMatMulVec_rectMatMul A C y) i]
/-- The squared least-squares objective commutes with a right change of
    variables. -/
theorem lsObjective_rectMatMul_right {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (C : Fin n → Fin p → ℝ)
    (b : Fin m → ℝ) (y : Fin p → ℝ) :
    lsObjective (rectMatMul A C) b y =
      lsObjective A b (rectMatMulVec C y) := by
  unfold lsObjective
  rw [lsResidual_rectMatMul_right]
/-- Explicit-arity version of `lsObjective_rectMatMul_right`. -/
theorem lsObjective_matMulRect_right (m n p : ℕ)
    (A : Fin m → Fin n → ℝ) (C : Fin n → Fin p → ℝ)
    (b : Fin m → ℝ) (y : Fin p → ℝ) :
    lsObjective (matMulRect m n p A C) b y =
      lsObjective A b (rectMatMulVec C y) := by
  exact lsObjective_rectMatMul_right A C b y
/-- Normal-equation Gram matrix `A^T A` for a rectangular least-squares
    instance. -/
noncomputable def lsNormalMatrix {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  rectLSGram A
/-- Normal-equation right-hand side `A^T b` for a rectangular least-squares
    instance. -/
noncomputable def lsNormalRhs {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) : Fin n → ℝ :=
  rectLSRhs A b
/-- A vector is an exact minimizer of the least-squares objective. -/
def IsLeastSquaresMinimizer {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ y : Fin n → ℝ, lsObjective A b x ≤ lsObjective A b y
/-- An exact minimizer for a row-permuted least-squares problem is an exact
    minimizer for the original problem. -/
theorem IsLeastSquaresMinimizer.of_permuteRows {m n : ℕ} (σ : Fin m ≃ Fin m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ)
    (h : IsLeastSquaresMinimizer (rectPermuteRows σ A) (vecPermute σ b) x) :
    IsLeastSquaresMinimizer A b x := by
  intro y
  have hy := h y
  rw [lsObjective_permuteRows] at hy
  rw [lsObjective_permuteRows] at hy
  exact hy
/-- An exact minimizer for a column-permuted least-squares problem maps back
    to an exact minimizer of the original problem. -/
theorem IsLeastSquaresMinimizer.of_permuteCols {m n : ℕ} (π : Fin n ≃ Fin n)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ)
    (h : IsLeastSquaresMinimizer (rectPermuteCols π A) b x) :
    IsLeastSquaresMinimizer A b (vecPermute π.symm x) := by
  intro y
  have hy := h (vecPermute π y)
  rw [lsObjective_permuteCols] at hy
  rw [lsObjective_permuteCols] at hy
  simpa [vecPermute_symm_vecPermute] using hy
/-- An exact minimizer for a row-sorted and column-pivoted least-squares
    problem maps back to an exact minimizer of the original problem by undoing
    the column permutation. -/
theorem IsLeastSquaresMinimizer.of_permuteRowsCols {m n : ℕ}
    (σ : Fin m ≃ Fin m) (π : Fin n ≃ Fin n)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ)
    (h : IsLeastSquaresMinimizer
      (rectPermuteRows σ (rectPermuteCols π A)) (vecPermute σ b) x) :
    IsLeastSquaresMinimizer A b (vecPermute π.symm x) := by
  intro y
  have hy := h (vecPermute π y)
  rw [lsObjective_permuteRowsCols] at hy
  rw [lsObjective_permuteRowsCols] at hy
  simpa [vecPermute_symm_vecPermute] using hy
/-- Row permutations preserve the rectangular normal-equation Gram matrix. -/
theorem rectLSGram_permuteRows {m n : ℕ} (σ : Fin m ≃ Fin m)
    (A : Fin m → Fin n → ℝ) :
    rectLSGram (rectPermuteRows σ A) = rectLSGram A := by
  ext j k
  unfold rectLSGram rectPermuteRows
  exact
    Fintype.sum_equiv σ
      (fun i : Fin m => A (σ i) j * A (σ i) k)
      (fun i : Fin m => A i j * A i k)
      (fun _ => rfl)
/-- Row permutations preserve the rectangular normal-equation right-hand side,
    provided the right-hand side vector is permuted by the same row map. -/
theorem rectLSRhs_permuteRows {m n : ℕ} (σ : Fin m ≃ Fin m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    rectLSRhs (rectPermuteRows σ A) (vecPermute σ b) = rectLSRhs A b := by
  ext j
  unfold rectLSRhs rectPermuteRows vecPermute
  exact
    Fintype.sum_equiv σ
      (fun i : Fin m => A (σ i) j * b (σ i))
      (fun i : Fin m => A i j * b i)
      (fun _ => rfl)
/-- Column permutations relabel both coordinates of the rectangular
    normal-equation Gram matrix. -/
theorem rectLSGram_permuteCols {m n : ℕ} (π : Fin n ≃ Fin n)
    (A : Fin m → Fin n → ℝ) :
    rectLSGram (rectPermuteCols π A) =
      fun j k => rectLSGram A (π j) (π k) := by
  ext j k
  rfl
/-- Column permutations relabel the rectangular normal-equation right-hand
    side. -/
theorem rectLSRhs_permuteCols {m n : ℕ} (π : Fin n ≃ Fin n)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    rectLSRhs (rectPermuteCols π A) b = vecPermute π (rectLSRhs A b) := by
  ext j
  rfl
/-- Combined row sorting and column pivoting relabel the rectangular
    normal-equation Gram matrix only by the column permutation. -/
theorem rectLSGram_permuteRowsCols {m n : ℕ}
    (σ : Fin m ≃ Fin m) (π : Fin n ≃ Fin n)
    (A : Fin m → Fin n → ℝ) :
    rectLSGram (rectPermuteRows σ (rectPermuteCols π A)) =
      fun j k => rectLSGram A (π j) (π k) := by
  rw [rectLSGram_permuteRows]
  exact rectLSGram_permuteCols π A
/-- Combined row sorting and column pivoting relabel the rectangular
    normal-equation right-hand side only by the column permutation, provided
    the data vector follows the row permutation. -/
theorem rectLSRhs_permuteRowsCols {m n : ℕ}
    (σ : Fin m ≃ Fin m) (π : Fin n ≃ Fin n)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    rectLSRhs (rectPermuteRows σ (rectPermuteCols π A)) (vecPermute σ b) =
      vecPermute π (rectLSRhs A b) := by
  rw [rectLSRhs_permuteRows]
  exact rectLSRhs_permuteCols π A b
/-- Higham's signed least-squares residual `b - A x`.  The shared objective API
    uses `A x - b`; this source-facing alias records the sign convention in
    Chapter 20's augmented system. -/
noncomputable def lsResidualHigham {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => b i - rectMatMulVec A x i
theorem lsResidualHigham_eq_neg_lsResidual {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    lsResidualHigham A b x = fun i => -lsResidual A b x i := by
  ext i
  unfold lsResidualHigham lsResidual
  ring
/-- A zero Higham-signed residual is an exact solution of the data equations,
    hence an exact least-squares minimizer.  This is the zero-residual branch
    used by the normwise backward-error formula (20.20)-(20.21). -/
theorem IsLeastSquaresMinimizer.of_lsResidualHigham_eq_zero {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ} {x : Fin n → ℝ}
    (hres : lsResidualHigham A b x = 0) :
    IsLeastSquaresMinimizer A b x := by
  intro y
  have hres0 : lsResidual A b x = 0 := by
    ext i
    change lsResidual A b x i = (0 : ℝ)
    have hi : lsResidualHigham A b x i = 0 := by
      simpa using congrFun hres i
    unfold lsResidualHigham at hi
    unfold lsResidual
    linarith
  have hx_obj : lsObjective A b x = 0 := by
    unfold lsObjective
    rw [hres0]
    unfold vecNorm2Sq
    simp
  have hy_nonneg : 0 ≤ lsObjective A b y := by
    unfold lsObjective
    exact vecNorm2Sq_nonneg (lsResidual A b y)
  linarith
/-- Real symmetric-matrix orthogonality for distinct eigenvalues, stated in the
    repository's finite-matrix/vector-action language.  This is spectral
    infrastructure for equation (20.18): once two vectors are eigenvectors of
    the same symmetric matrix for different eigenvalues, their Euclidean dot
    product is zero. -/
theorem isSymmetricFiniteMatrix_eigenvectors_sum_mul_eq_zero {n : ℕ}
    {M : Fin n → Fin n → ℝ} (hM : IsSymmetricFiniteMatrix M)
    {lambda mu : ℝ} {x y : Fin n → ℝ}
    (hx : rectMatMulVec M x = fun i => lambda * x i)
    (hy : rectMatMulVec M y = fun i => mu * y i)
    (hlambda_mu : lambda ≠ mu) :
    (∑ i : Fin n, x i * y i) = 0 := by
  have hleft_eval :
      (∑ i : Fin n, rectMatMulVec M x i * y i) =
        lambda * ∑ i : Fin n, x i * y i := by
    calc
      (∑ i : Fin n, rectMatMulVec M x i * y i) =
          ∑ i : Fin n, (lambda * x i) * y i := by
            rw [hx]
      _ = ∑ i : Fin n, lambda * (x i * y i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = lambda * ∑ i : Fin n, x i * y i := by
            rw [Finset.mul_sum]
  have hright_eval :
      (∑ i : Fin n, x i * rectMatMulVec M y i) =
        mu * ∑ i : Fin n, x i * y i := by
    calc
      (∑ i : Fin n, x i * rectMatMulVec M y i) =
          ∑ i : Fin n, x i * (mu * y i) := by
            rw [hy]
      _ = ∑ i : Fin n, mu * (x i * y i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = mu * ∑ i : Fin n, x i * y i := by
            rw [Finset.mul_sum]
  have htranspose :
      (∑ i : Fin n, rectMatMulVec M x i * y i) =
        ∑ j : Fin n, x j * rectMatMulVec M y j := by
    unfold rectMatMulVec
    calc
      (∑ i : Fin n, (∑ j : Fin n, M i j * x j) * y i) =
          ∑ i : Fin n, ∑ j : Fin n, (M i j * x j) * y i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
      _ = ∑ j : Fin n, ∑ i : Fin n, (M i j * x j) * y i := by
            rw [Finset.sum_comm]
      _ = ∑ j : Fin n, ∑ i : Fin n, x j * (M j i * y i) := by
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro i _
            rw [hM i j]
            ring
      _ = ∑ j : Fin n, x j * ∑ i : Fin n, M j i * y i := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
  have hscalar :
      lambda * (∑ i : Fin n, x i * y i) =
        mu * (∑ i : Fin n, x i * y i) := by
    rw [← hleft_eval, htranspose, hright_eval]
  have hprod :
      (lambda - mu) * (∑ i : Fin n, x i * y i) = 0 := by
    nlinarith
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hlambda_mu)
/-- The top block in Higham, 2nd ed., Chapter 20, equation (20.6):
    `(I - A A^+) u + (A^+)^T v`.  This is the first component of the
    displayed inverse action for the augmented least-squares matrix
    `[I A; A^T 0]`. -/
noncomputable def lsAugmentedInverseActionTop {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ) : Fin m → ℝ :=
  fun i =>
    u i - rectMatMulVec A (rectMatMulVec Aplus u) i +
      ∑ j : Fin n, Aplus j i * v j
/-- The bottom block in Higham, 2nd ed., Chapter 20, equation (20.6):
    `A^+ u - (A^T A)^{-1} v`. -/
noncomputable def lsAugmentedInverseActionBottom {m n : ℕ}
    (Aplus : Fin n → Fin m → ℝ) (gramInv : Fin n → Fin n → ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ) : Fin n → ℝ :=
  fun j => rectMatMulVec Aplus u j - matMulVec n gramInv v j
/-- The Gram matrix `A^T A` used in Chapter 20 is symmetric. -/
theorem rectLSGram_symmetric {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    IsSymmetricFiniteMatrix (rectLSGram A) := by
  intro j k
  unfold rectLSGram
  apply Finset.sum_congr rfl
  intro i _
  ring
/-- Concrete Gram inverse candidate for the determinant-facing form of
    Higham's Chapter 20, equation (20.6). -/
noncomputable def lsGramNonsingInv {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  nonsingInv n (rectLSGram A)
/-- A nonzero determinant of `A^T A` supplies the concrete Gram-inverse
    certificate needed by the exact inverse action (20.6). -/
theorem lsGramNonsingInv_isInverse_of_det_ne_zero {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (hdet : Matrix.det (rectLSGram A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    IsInverse n (rectLSGram A) (lsGramNonsingInv A) := by
  exact isInverse_nonsingInv_of_det_ne_zero n (rectLSGram A) hdet
/-- The concrete Gram inverse candidate preserves the symmetry of `A^T A`. -/
theorem lsGramNonsingInv_symmetric {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    IsSymmetricFiniteMatrix (lsGramNonsingInv A) := by
  exact nonsingInv_symmetric_of_symmetric (rectLSGram A)
    (rectLSGram_symmetric A)
/-- Kernel inclusion for the Gram matrix: if `(Aᵀ A)x = 0`, then `Ax = 0`.

    This is the exact finite-dimensional bridge behind the source statement
    that full column rank of `A` makes the Gram matrix nonsingular. -/
theorem rectMatMulVec_eq_zero_of_rectLSGram_mulVec_eq_zero {m n : ℕ}
    (A : Fin m → Fin n → ℝ) {x : Fin n → ℝ}
    (hGx : rectMatMulVec (rectLSGram A) x = 0) :
    rectMatMulVec A x = 0 := by
  let M : Matrix (Fin m) (Fin n) ℝ := A
  have hker : x ∈ LinearMap.ker ((M.transpose * M).mulVecLin) := by
    change (M.transpose * M).mulVec x = 0
    ext j
    have hj := congrFun hGx j
    simpa [M, Matrix.mulVec, Matrix.mul_apply, rectMatMulVec, rectLSGram] using hj
  have hAx : x ∈ LinearMap.ker M.mulVecLin := by
    rw [← Matrix.ker_mulVecLin_transpose_mul_self M]
    exact hker
  ext i
  have hi := congrFun hAx i
  simpa [M, Matrix.mulVec, rectMatMulVec] using hi
/-- Full column rank of `A`, represented locally as injectivity of
    `x ↦ A x`, transfers to injectivity of the Gram action
    `x ↦ (Aᵀ A)x`. -/
theorem rectLSGram_rectMatMulVec_injective_of_rectMatMulVec_injective
    {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (hA : Function.Injective (rectMatMulVec A)) :
    Function.Injective (rectMatMulVec (rectLSGram A)) := by
  intro x y hxy
  apply hA
  have hdiffG : rectMatMulVec (rectLSGram A) (fun j => x j - y j) = 0 := by
    rw [rectMatMulVec_sub]
    ext j
    have hj := congrFun hxy j
    exact sub_eq_zero.mpr hj
  have hAdiff :=
    rectMatMulVec_eq_zero_of_rectLSGram_mulVec_eq_zero A hdiffG
  rw [rectMatMulVec_sub] at hAdiff
  exact sub_eq_zero.mp hAdiff
/-- A square function-shaped matrix with injective vector action has nonzero
    determinant. -/
theorem det_ne_zero_of_square_rectMatMulVec_injective {n : ℕ}
    {T : Fin n → Fin n → ℝ}
    (hinj : Function.Injective (rectMatMulVec T)) :
    Matrix.det (T : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  let M : Matrix (Fin n) (Fin n) ℝ := T
  have hM_inj : Function.Injective M.mulVec := by
    intro x y hxy
    apply hinj
    ext i
    have hi := congrFun hxy i
    simpa [M, rectMatMulVec, Matrix.mulVec] using hi
  have hunitM : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hM_inj
  have hdetUnit : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hunitM
  have hdetNe : M.det ≠ 0 := isUnit_iff_ne_zero.mp hdetUnit
  simpa [M] using hdetNe
/-- Source full-column-rank form of the nonsingular-Gram bridge:
    injectivity of `x ↦ A x` implies `det(AᵀA) ≠ 0`. -/
theorem rectLSGram_det_ne_zero_of_rectMatMulVec_injective {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (hA : Function.Injective (rectMatMulVec A)) :
    Matrix.det (rectLSGram A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  exact
    det_ne_zero_of_square_rectMatMulVec_injective
      (T := rectLSGram A)
      (rectLSGram_rectMatMulVec_injective_of_rectMatMulVec_injective A hA)
/-- The `I - A A^+` top-left block in Higham, 2nd ed., Chapter 20,
    equation (20.6). -/
noncomputable def lsAugmentedProjectionBlock {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ) :
    Fin m → Fin m → ℝ :=
  fun i k => idMatrix m i k - rectMatMulVec A (fun j => Aplus j k) i
/-- Vector action of the `I - A A^+` block from (20.6). -/
theorem lsAugmentedProjectionBlock_mulVec {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ)
    (u : Fin m → ℝ) :
    rectMatMulVec (lsAugmentedProjectionBlock A Aplus) u =
      fun i => u i - rectMatMulVec A (rectMatMulVec Aplus u) i := by
  ext i
  have hid := congrFun (idMatrix_mulVec m u) i
  have hcomp :
      (∑ k : Fin m, rectMatMulVec A (fun j => Aplus j k) i * u k) =
        rectMatMulVec A (rectMatMulVec Aplus u) i := by
    unfold rectMatMulVec
    calc
      ∑ k : Fin m, (∑ j : Fin n, A i j * Aplus j k) * u k
          = ∑ k : Fin m, ∑ j : Fin n, (A i j * Aplus j k) * u k := by
              apply Finset.sum_congr rfl
              intro k _
              rw [Finset.sum_mul]
      _ = ∑ j : Fin n, ∑ k : Fin m, (A i j * Aplus j k) * u k := by
              rw [Finset.sum_comm]
      _ = ∑ j : Fin n, A i j * (∑ k : Fin m, Aplus j k * u k) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring
  unfold rectMatMulVec lsAugmentedProjectionBlock
  calc
    ∑ k : Fin m,
        (idMatrix m i k - rectMatMulVec A (fun j => Aplus j k) i) * u k
        = (∑ k : Fin m, idMatrix m i k * u k) -
            ∑ k : Fin m, rectMatMulVec A (fun j => Aplus j k) i * u k := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ = u i - rectMatMulVec A (rectMatMulVec Aplus u) i := by
            rw [hid, hcomp]
/-- Source-shaped first right-hand-side block in (20.6):
    `Delta b - Delta A y`. -/
noncomputable def lsEq20_6RhsTop {m n : ℕ}
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    (y : Fin n → ℝ) : Fin m → ℝ :=
  fun i => Deltab i - rectMatMulVec DeltaA y i
/-- Source-shaped second right-hand-side block in (20.6):
    `-Delta A^T s`. -/
noncomputable def lsEq20_6RhsBottom {m n : ℕ}
    (DeltaA : Fin m → Fin n → ℝ) (s : Fin m → ℝ) : Fin n → ℝ :=
  fun j => -∑ i : Fin m, DeltaA i j * s i
/-- The Gram action `Aᵀ A x` is the transpose action applied to `A x`.

    This is the algebraic identity used to turn uniqueness of the augmented
    system into invertibility of `Aᵀ A`. -/
theorem rectLSGram_mulVec_eq_transpose_rectMatMulVec {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    matMulVec n (rectLSGram A) x =
      fun j => ∑ i : Fin m, A i j * rectMatMulVec A x i := by
  ext j
  unfold matMulVec rectLSGram rectMatMulVec
  calc
    ∑ k : Fin n, (∑ i : Fin m, A i j * A i k) * x k
        = ∑ k : Fin n, ∑ i : Fin m, (A i j * A i k) * x k := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_mul]
    _ = ∑ i : Fin m, ∑ k : Fin n, (A i j * A i k) * x k := by
            rw [Finset.sum_comm]
    _ = ∑ i : Fin m, A i j * ∑ k : Fin n, A i k * x k := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
/-- Dot product of two appended real vectors, split over the source row and
    column blocks used in the scaled augmented matrix `C(alpha)`. -/
theorem finAppend_sum_mul_eq {m n : ℕ}
    (x y : Fin m → ℝ) (z w : Fin n → ℝ) :
    (∑ k : Fin (m + n), Fin.append x z k * Fin.append y w k) =
      (∑ i : Fin m, x i * y i) + (∑ j : Fin n, z j * w j) := by
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]
/-- Dot product of source-normalized appended branch vectors, with arbitrary
    right-block scale factors.  This is the algebraic reduction used when
    building an orthogonal basis from singular-vector data in (20.18). -/
theorem finAppend_sum_mul_smul_eq {m n : ℕ}
    (u w : Fin m → ℝ) (v z : Fin n → ℝ) (beta gamma : ℝ) :
    (∑ k : Fin (m + n),
      Fin.append u (fun j => beta * v j) k *
        Fin.append w (fun j => gamma * z j) k) =
      (∑ i : Fin m, u i * w i) +
        beta * gamma * (∑ j : Fin n, v j * z j) := by
  rw [finAppend_sum_mul_eq]
  have hright :
      (∑ j : Fin n, (beta * v j) * (gamma * z j)) =
        beta * gamma * (∑ j : Fin n, v j * z j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hright]
/-- Rescaling two real vectors by the inverse of their Euclidean norms preserves
    a zero Euclidean dot product. -/
theorem vecNorm2_inv_smul_dot_eq_zero_of_dot_eq_zero {n : ℕ}
    (x y : Fin n → ℝ)
    (hxy : (∑ i : Fin n, x i * y i) = 0) :
    (∑ i : Fin n,
      ((vecNorm2 x)⁻¹ * x i) * ((vecNorm2 y)⁻¹ * y i)) = 0 := by
  calc
    (∑ i : Fin n,
      ((vecNorm2 x)⁻¹ * x i) * ((vecNorm2 y)⁻¹ * y i))
        = (vecNorm2 x)⁻¹ * (vecNorm2 y)⁻¹ *
            (∑ i : Fin n, x i * y i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = 0 := by rw [hxy, mul_zero]
/-- Rescaling a real eigenvector by the inverse of its Euclidean norm preserves
    the same eigenvector equation. -/
theorem rectMatMulVec_vecNorm2_inv_smul_eigenvector {n : ℕ}
    (M : Fin n → Fin n → ℝ) (lambda : ℝ) (x : Fin n → ℝ)
    (hx : rectMatMulVec M x = fun i => lambda * x i) :
    rectMatMulVec M (fun i => (vecNorm2 x)⁻¹ * x i) =
      fun i => lambda * ((vecNorm2 x)⁻¹ * x i) := by
  calc
    rectMatMulVec M (fun i => (vecNorm2 x)⁻¹ * x i)
        = fun i => (vecNorm2 x)⁻¹ * rectMatMulVec M x i := by
          exact rectMatMulVec_smul M (vecNorm2 x)⁻¹ x
    _ = fun i => lambda * ((vecNorm2 x)⁻¹ * x i) := by
          ext i
          rw [congrFun hx i]
          ring
/-- A Euclidean unit vector is nonzero. -/
theorem vecNorm2_eq_one_ne_zero {n : ℕ} {x : Fin n → ℝ}
    (hx : vecNorm2 x = 1) : x ≠ 0 := by
  intro hzero
  have hnorm : vecNorm2 x = 0 := by
    simpa [hzero] using (vecNorm2_zero (n := n))
  linarith
/-- Source-dimension embedding for completing `n` left singular columns by
    `m-n` left-null columns.  The two summands occupy the first `n` and last
    `m-n` coordinates of `Fin m`. -/
def lsSourceLeftCompletionEmbedding {m n : ℕ} (hmn : n ≤ m) :
    Fin n ⊕ Fin (m - n) ↪ Fin m where
  toFun
    | Sum.inl a => Fin.castLE hmn a
    | Sum.inr c => ⟨n + c.val, by omega⟩
  inj' := by
    intro x y hxy
    cases x with
    | inl a =>
        cases y with
        | inl b =>
            have hval :
                (Fin.castLE hmn a).val = (Fin.castLE hmn b).val :=
              congrArg Fin.val hxy
            exact congrArg Sum.inl (Fin.ext (by simpa using hval))
        | inr c =>
            have hlt : a.val < n := a.isLt
            have hge : n ≤ (n + c.val) := Nat.le_add_right n c.val
            have hval : a.val = n + c.val := by
              simpa using congrArg Fin.val hxy
            omega
    | inr c =>
        cases y with
        | inl b =>
            have hlt : b.val < n := b.isLt
            have hge : n ≤ (n + c.val) := Nat.le_add_right n c.val
            have hval : n + c.val = b.val := by
              simpa using congrArg Fin.val hxy
            omega
        | inr d =>
            have hval : n + c.val = n + d.val :=
              congrArg Fin.val hxy
            have hcd : c.val = d.val := by omega
            exact congrArg Sum.inr (Fin.ext hcd)
/-- Generic row-Gram quadratic-form identity:
    `x^T (B B^T) x = ||B^T x||_2^2`. -/
theorem finiteQuadraticForm_rowGram_transpose_eq_vecNorm2Sq_rectMatMulVec_finiteTranspose
    {m n : ℕ} (B : Fin m → Fin n → ℝ) (p : Fin m → ℝ) :
    finiteQuadraticForm (fun i k : Fin m => ∑ q : Fin n, B i q * B k q) p =
      vecNorm2Sq (rectMatMulVec (finiteTranspose B) p) := by
  unfold finiteQuadraticForm finiteMatVec vecNorm2Sq rectMatMulVec finiteTranspose
  calc
    (∑ i : Fin m, p i * ∑ j : Fin m, (∑ q : Fin n, B i q * B j q) * p j)
        = ∑ i : Fin m, ∑ j : Fin m, ∑ q : Fin n,
            p i * (B i q * B j q) * p j := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q _
            ring
    _ = ∑ q : Fin n, ∑ i : Fin m, ∑ j : Fin m,
            p i * (B i q * B j q) * p j := by
            calc
              (∑ i : Fin m, ∑ j : Fin m, ∑ q : Fin n,
                  p i * (B i q * B j q) * p j)
                  = ∑ i : Fin m, ∑ q : Fin n, ∑ j : Fin m,
                      p i * (B i q * B j q) * p j := by
                      apply Finset.sum_congr rfl
                      intro i _
                      rw [Finset.sum_comm]
              _ = ∑ q : Fin n, ∑ i : Fin m, ∑ j : Fin m,
                      p i * (B i q * B j q) * p j := by
                      rw [Finset.sum_comm]
    _ = ∑ q : Fin n, (∑ i : Fin m, B i q * p i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro q _
            rw [pow_two]
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
/-- Splitting a finite vector into two coordinate blocks preserves squared
    Euclidean norm additively. -/
theorem lsVecNorm2Sq_append {n m : ℕ}
    (x : Fin n → ℝ) (z : Fin m → ℝ) :
    vecNorm2Sq (Fin.append x z) = vecNorm2Sq x + vecNorm2Sq z := by
  unfold vecNorm2Sq
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]
/-- Triangle inequality for an appended finite vector, viewed as the sum of
    its left and right coordinate embeddings. -/
theorem lsVecNorm2_append_le_add {n m : ℕ}
    (x : Fin n → ℝ) (z : Fin m → ℝ) :
    vecNorm2 (Fin.append x z) ≤ vecNorm2 x + vecNorm2 z := by
  let x' : Fin (n + m) → ℝ := Fin.append x (0 : Fin m → ℝ)
  let z' : Fin (n + m) → ℝ := Fin.append (0 : Fin n → ℝ) z
  have happ :
      Fin.append x z = fun k : Fin (n + m) => x' k + z' k := by
    ext k
    refine Fin.addCases
      (motive := fun k : Fin (n + m) =>
        Fin.append x z k = x' k + z' k)
      ?left ?right k
    · intro i
      simp [x', z', Fin.append_left]
    · intro i
      simp [x', z', Fin.append_right]
  have hx' : vecNorm2 x' = vecNorm2 x := by
    unfold x'
    unfold vecNorm2
    rw [lsVecNorm2Sq_append]
    simp [vecNorm2Sq]
  have hz' : vecNorm2 z' = vecNorm2 z := by
    unfold z'
    unfold vecNorm2
    rw [lsVecNorm2Sq_append]
    simp [vecNorm2Sq]
  calc
    vecNorm2 (Fin.append x z) = vecNorm2 (fun k : Fin (n + m) => x' k + z' k) := by
      rw [happ]
    _ ≤ vecNorm2 x' + vecNorm2 z' := vecNorm2_add_le x' z'
    _ = vecNorm2 x + vecNorm2 z := by rw [hx', hz']
/-- The left coordinate block of an appended vector has no larger Euclidean
    norm than the whole vector. -/
theorem lsVecNorm2_left_le_append {n m : ℕ}
    (x : Fin n → ℝ) (z : Fin m → ℝ) :
    vecNorm2 x ≤ vecNorm2 (Fin.append x z) := by
  unfold vecNorm2
  apply Real.sqrt_le_sqrt
  rw [lsVecNorm2Sq_append]
  have hz := vecNorm2Sq_nonneg z
  linarith
/-- The right coordinate block of an appended vector has no larger Euclidean
    norm than the whole vector. -/
theorem lsVecNorm2_right_le_append {n m : ℕ}
    (x : Fin n → ℝ) (z : Fin m → ℝ) :
    vecNorm2 z ≤ vecNorm2 (Fin.append x z) := by
  unfold vecNorm2
  apply Real.sqrt_le_sqrt
  rw [lsVecNorm2Sq_append]
  have hx := vecNorm2Sq_nonneg x
  linarith
/-- The first `n` coordinates of a vector over `Fin (n+m)` have no larger
    Euclidean norm than the whole vector. -/
theorem lsVecNorm2_left_le_of_sum_coords {n m : ℕ}
    (z : Fin (n + m) → ℝ) :
    vecNorm2 (fun j : Fin n => z (Fin.castAdd m j)) ≤ vecNorm2 z := by
  let x : Fin n → ℝ := fun j => z (Fin.castAdd m j)
  let w : Fin m → ℝ := fun j => z (Fin.natAdd n j)
  have hle := lsVecNorm2_left_le_append x w
  have hz : Fin.append x w = z := by
    ext k
    refine Fin.addCases
      (motive := fun k : Fin (n + m) => Fin.append x w k = z k)
      ?left ?right k
    · intro i
      simp [x, w, Fin.append_left]
    · intro i
      simp [x, w, Fin.append_right]
  simpa [x, w, hz] using hle
/-- The last `m` coordinates of a vector over `Fin (n+m)` have no larger
    Euclidean norm than the whole vector. -/
theorem lsVecNorm2_right_le_of_sum_coords {n m : ℕ}
    (z : Fin (n + m) → ℝ) :
    vecNorm2 (fun j : Fin m => z (Fin.natAdd n j)) ≤ vecNorm2 z := by
  let x : Fin n → ℝ := fun j => z (Fin.castAdd m j)
  let w : Fin m → ℝ := fun j => z (Fin.natAdd n j)
  have hle := lsVecNorm2_right_le_append x w
  have hz : Fin.append x w = z := by
    ext k
    refine Fin.addCases
      (motive := fun k : Fin (n + m) => Fin.append x w k = z k)
      ?left ?right k
    · intro i
      simp [x, w, Fin.append_left]
    · intro i
      simp [x, w, Fin.append_right]
  simpa [x, w, hz] using hle
/-- The global Householder QR gamma-validity assumption used in Theorem 20.4
    also supplies the triangular-solve gamma-validity assumption. -/
theorem gammaValid_n_of_householderConstructApplyGammaValid
    (fp : FPModel) (m n : ℕ)
    (hvalid : gammaValid fp (n * householderConstructApplyGammaIndex m)) :
    gammaValid fp n := by
  have hK_pos : 0 < householderConstructApplyGammaIndex m := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  exact gammaValid_mono fp (Nat.le_mul_of_pos_right n hK_pos) hvalid
/-- The conservative gamma-factor RHS index used in the current Theorem 20.4
    implementation-backed `Delta f` package is positive for every nonempty
    panel. -/
theorem theorem20_4GammaFactorRhsIndex_pos {n k : ℕ} (hn : 0 < n) :
    0 < householderQRRhsPanelGammaClosedGrowthIndex (n + k) n := by
  have hm : 0 < n + k := Nat.lt_of_lt_of_le hn (Nat.le_add_right n k)
  have hF :
      0 < householderQRRhsPanelGammaClosedGrowthFactor (n + k) n :=
    householderQRRhsPanelGammaClosedGrowthFactor_pos (m := n + k) (p := n) hm
  have hK : 0 < householderConstructApplyGammaIndex (n + k) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hprinted : 0 < n * householderConstructApplyGammaIndex (n + k) :=
    Nat.mul_pos hn hK
  rw [householderQRRhsPanelGammaClosedGrowthIndex_eq_factor_mul_printedIndex]
  exact Nat.mul_pos hF hprinted
private theorem vecNorm2Sq_add_eq {m : ℕ} (r e : Fin m → ℝ) :
    vecNorm2Sq (fun i => r i + e i) =
      vecNorm2Sq r + 2 * (∑ i : Fin m, r i * e i) + vecNorm2Sq e := by
  unfold vecNorm2Sq
  simp_rw [show ∀ i : Fin m, (r i + e i) ^ 2 =
      r i ^ 2 + 2 * (r i * e i) + e i ^ 2 from fun i => by ring]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
private theorem lsResidual_add_direction {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (x d : Fin n → ℝ) :
    lsResidual A b (fun j => x j + d j) =
      fun i => lsResidual A b x i + rectMatMulVec A d i := by
  ext i
  calc
    lsResidual A b (fun j => x j + d j) i
        = rectMatMulVec A (fun j => x j + d j) i - b i := rfl
    _ = (rectMatMulVec A x i + rectMatMulVec A d i) - b i := by
          rw [congrFun (rectMatMulVec_add A x d) i]
    _ = lsResidual A b x i + rectMatMulVec A d i := by
          unfold lsResidual
          ring
private theorem ls_cross_term_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (x d : Fin n → ℝ) :
    ∑ i : Fin m, lsResidual A b x i * rectMatMulVec A d i =
      ∑ j : Fin n, d j * (∑ i : Fin m, A i j * lsResidual A b x i) := by
  calc
    ∑ i : Fin m, lsResidual A b x i * rectMatMulVec A d i
        = ∑ i : Fin m, ∑ j : Fin n,
            lsResidual A b x i * (A i j * d j) := by
          unfold rectMatMulVec
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
    _ = ∑ j : Fin n, ∑ i : Fin m,
            lsResidual A b x i * (A i j * d j) := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin n, d j *
            (∑ i : Fin m, A i j * lsResidual A b x i) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
/-- Squared residual objective after an additive coefficient perturbation. -/
theorem lsObjective_add_direction_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (x d : Fin n → ℝ) :
    lsObjective A b (fun j => x j + d j) =
      lsObjective A b x +
        2 * (∑ j : Fin n,
          d j * (∑ i : Fin m, A i j * lsResidual A b x i)) +
        vecNorm2Sq (rectMatMulVec A d) := by
  unfold lsObjective
  rw [lsResidual_add_direction, vecNorm2Sq_add_eq, ls_cross_term_eq]
/-- Perturbed-data expansion of Higham's signed residual:
    `(b + Delta b) - (A + Delta A)y = (b - A y) + Delta b - Delta A y`. -/
theorem lsResidualHigham_perturbed_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ) :
    lsResidualHigham
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y =
      fun i => lsResidualHigham A b y i + Deltab i -
        rectMatMulVec DeltaA y i := by
  ext i
  unfold lsResidualHigham rectMatMulVec
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  ring
/-- Pythagorean identity for rectangular Frobenius squares when the
    rectangular Frobenius inner product vanishes. -/
theorem frobNormSqRect_add_of_inner_eq_zero {m n : ℕ}
    (A B : Fin m → Fin n → ℝ)
    (hinner : (∑ i : Fin m, ∑ j : Fin n, A i j * B i j) = 0) :
    frobNormSqRect (fun i j => A i j + B i j) =
      frobNormSqRect A + frobNormSqRect B := by
  unfold frobNormSqRect
  calc
    (∑ i : Fin m, ∑ j : Fin n, (A i j + B i j) ^ 2)
        = ∑ i : Fin m, ∑ j : Fin n,
            (A i j ^ 2 + 2 * (A i j * B i j) + B i j ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ =
        (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) +
          2 * (∑ i : Fin m, ∑ j : Fin n, A i j * B i j) +
            ∑ i : Fin m, ∑ j : Fin n, B i j ^ 2 := by
          simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ =
        (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) +
          ∑ i : Fin m, ∑ j : Fin n, B i j ^ 2 := by
          rw [hinner]
          ring
/-- Exact top residual `R x - z` in Higham's Section 20.3 augmented
    modified-Gram-Schmidt least-squares factorization. -/
noncomputable def mgsAugmentedTopResidual {n : ℕ}
    (R : Fin n → Fin n → ℝ) (z x : Fin n → ℝ) : Fin n → ℝ :=
  fun k => matMulVec n R x k - z k
/-- Exact expanded residual `Q₁(Rx-z) - ρq` from Higham, 2nd ed.,
    Chapter 20, Section 20.3. -/
noncomputable def mgsAugmentedResidualExpansion {m n : ℕ}
    (Q1 : Fin m → Fin n → ℝ) (q : Fin m → ℝ)
    (R : Fin n → Fin n → ℝ) (z x : Fin n → ℝ) (rho : ℝ) :
    Fin m → ℝ :=
  fun i => rectMatMulVec Q1 (mgsAugmentedTopResidual R z x) i - rho * q i
private theorem mgsAugmented_matVec_eq {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {Q1 : Fin m → Fin n → ℝ}
    {R : Fin n → Fin n → ℝ} (x : Fin n → ℝ)
    (hA : ∀ i j, A i j = ∑ k : Fin n, Q1 i k * R k j)
    (i : Fin m) :
    rectMatMulVec A x i =
      ∑ k : Fin n, Q1 i k * matMulVec n R x k := by
  calc
    rectMatMulVec A x i
        = ∑ j : Fin n, A i j * x j := rfl
    _ = ∑ j : Fin n, (∑ k : Fin n, Q1 i k * R k j) * x j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hA i j]
    _ = ∑ j : Fin n, ∑ k : Fin n, (Q1 i k * R k j) * x j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
    _ = ∑ k : Fin n, ∑ j : Fin n, (Q1 i k * R k j) * x j := by
          rw [Finset.sum_comm]
    _ = ∑ k : Fin n, Q1 i k * matMulVec n R x k := by
          apply Finset.sum_congr rfl
          intro k _
          unfold matMulVec
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
private theorem mgsAugmented_sum_diff {m n : ℕ}
    (Q1 : Fin m → Fin n → ℝ) (R : Fin n → Fin n → ℝ)
    (z x : Fin n → ℝ) (i : Fin m) :
    (∑ k : Fin n, Q1 i k * matMulVec n R x k) -
        ∑ k : Fin n, Q1 i k * z k =
      ∑ k : Fin n, Q1 i k * mgsAugmentedTopResidual R z x k := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  unfold mgsAugmentedTopResidual
  ring
/-- Higham, 2nd ed., Chapter 20, Section 20.3:
    from `[A b] = [Q₁ q] [[R z], [0 ρ]]`,
    `A x - b = Q₁(Rx-z) - ρq`. -/
theorem MGSAugmentedLSFactorization.residual_eq {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {Q1 : Fin m → Fin n → ℝ} {q : Fin m → ℝ}
    {R : Fin n → Fin n → ℝ} {z : Fin n → ℝ} {rho : ℝ}
    (h : MGSAugmentedLSFactorization A b Q1 q R z rho)
    (x : Fin n → ℝ) :
    lsResidual A b x = mgsAugmentedResidualExpansion Q1 q R z x rho := by
  ext i
  unfold lsResidual mgsAugmentedResidualExpansion
  rw [mgsAugmented_matVec_eq x h.A_eq i, h.b_eq i]
  unfold rectMatMulVec
  rw [← mgsAugmented_sum_diff Q1 R z x i]
  ring
private theorem vecNorm2Sq_mgsAugmentedResidualExpansion {m n : ℕ}
    (Q1 : Fin m → Fin n → ℝ) (q : Fin m → ℝ)
    (R : Fin n → Fin n → ℝ) (z x : Fin n → ℝ) (rho : ℝ)
    (hQ1 : ∀ j k : Fin n, ∑ i : Fin m, Q1 i j * Q1 i k =
      if j = k then 1 else 0)
    (hqorth : ∀ j : Fin n, ∑ i : Fin m, Q1 i j * q i = 0)
    (hqnorm : vecNorm2Sq q = 1) :
    vecNorm2Sq (mgsAugmentedResidualExpansion Q1 q R z x rho) =
      vecNorm2Sq (mgsAugmentedTopResidual R z x) + rho ^ 2 := by
  let y : Fin n → ℝ := mgsAugmentedTopResidual R z x
  have hQnorm :
      (∑ i : Fin m, (∑ j : Fin n, Q1 i j * y j) ^ 2) =
        vecNorm2Sq y := by
    unfold vecNorm2Sq
    have expand : ∀ i : Fin m,
        (∑ j : Fin n, Q1 i j * y j) ^ 2 =
          ∑ j : Fin n, ∑ k : Fin n,
            Q1 i j * Q1 i k * (y j * y k) := by
      intro i
      rw [sq, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    simp_rw [expand]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    have factor : ∀ k : Fin n,
        ∑ i : Fin m, Q1 i j * Q1 i k * (y j * y k) =
          (∑ i : Fin m, Q1 i j * Q1 i k) * (y j * y k) := by
      intro k
      rw [← Finset.sum_mul]
    simp_rw [factor, hQ1]
    simp [Finset.sum_ite_eq, Finset.mem_univ]
    ring
  have hcross :
      (∑ i : Fin m, (∑ j : Fin n, Q1 i j * y j) * q i) = 0 := by
    calc
      (∑ i : Fin m, (∑ j : Fin n, Q1 i j * y j) * q i)
          = ∑ i : Fin m, ∑ j : Fin n, (Q1 i j * y j) * q i := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.sum_mul]
      _ = ∑ j : Fin n, ∑ i : Fin m, (Q1 i j * y j) * q i := by
              rw [Finset.sum_comm]
      _ = ∑ j : Fin n, y j * (∑ i : Fin m, Q1 i j * q i) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = 0 := by
              simp [hqorth]
  have hcrossTerm :
      (∑ i : Fin m, 2 * (∑ j : Fin n, Q1 i j * y j) * (rho * q i)) =
        2 * rho *
          (∑ i : Fin m, (∑ j : Fin n, Q1 i j * y j) * q i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hqnorm' : (∑ i : Fin m, (rho * q i) ^ 2) = rho ^ 2 := by
    calc
      (∑ i : Fin m, (rho * q i) ^ 2)
          = rho ^ 2 * ∑ i : Fin m, q i ^ 2 := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = rho ^ 2 := by
              have hqsum : (∑ i : Fin m, q i ^ 2) = 1 := by
                simpa [vecNorm2Sq] using hqnorm
              rw [hqsum, mul_one]
  have hmain :
      (∑ i : Fin m,
          ((∑ j : Fin n, Q1 i j * y j) - rho * q i) ^ 2) =
        (∑ i : Fin m, (∑ j : Fin n, Q1 i j * y j) ^ 2) -
          (∑ i : Fin m, 2 * (∑ j : Fin n, Q1 i j * y j) * (rho * q i)) +
          ∑ i : Fin m, (rho * q i) ^ 2 := by
    calc
      (∑ i : Fin m,
          ((∑ j : Fin n, Q1 i j * y j) - rho * q i) ^ 2)
          = ∑ i : Fin m,
              ((∑ j : Fin n, Q1 i j * y j) ^ 2 -
                2 * (∑ j : Fin n, Q1 i j * y j) * (rho * q i) +
                (rho * q i) ^ 2) := by
                apply Finset.sum_congr rfl
                intro i _
                ring
      _ = (∑ i : Fin m, (∑ j : Fin n, Q1 i j * y j) ^ 2) -
          (∑ i : Fin m, 2 * (∑ j : Fin n, Q1 i j * y j) * (rho * q i)) +
          ∑ i : Fin m, (rho * q i) ^ 2 := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  unfold vecNorm2Sq mgsAugmentedResidualExpansion rectMatMulVec
  dsimp [y] at hQnorm hcross hcrossTerm
  rw [hmain, hQnorm, hcrossTerm, hcross, hqnorm']
  unfold vecNorm2Sq
  ring
/-- Higham, 2nd ed., Chapter 20, Section 20.3:
    if `[A b] = [Q₁ q] [[R z], [0 ρ]]`, with `q` orthogonal to the columns of
    `Q₁`, then `||A x - b||₂² = ||R x - z||₂² + ρ²`.  The book writes the
    equivalent norm of `b - A x`. -/
theorem MGSAugmentedLSFactorization.objective_eq_top_plus_rho_sq
    {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {Q1 : Fin m → Fin n → ℝ} {q : Fin m → ℝ}
    {R : Fin n → Fin n → ℝ} {z : Fin n → ℝ} {rho : ℝ}
    (h : MGSAugmentedLSFactorization A b Q1 q R z rho)
    (x : Fin n → ℝ) :
    lsObjective A b x =
      vecNorm2Sq (mgsAugmentedTopResidual R z x) + rho ^ 2 := by
  unfold lsObjective
  rw [h.residual_eq x]
  exact
    vecNorm2Sq_mgsAugmentedResidualExpansion
      Q1 q R z x rho h.Q1_col_orthonormal h.q_orthogonal h.q_norm
/-- Higham, 2nd ed., Chapter 20, Section 20.3:
    the exact augmented-MGS least-squares algebra implies that any solution of
    `R x = z` is an exact least-squares minimizer for the original problem.
    This formalizes the source statement "the LS solution is `x = R^{-1} z`"
    without assuming a concrete inverse for `R`. -/
theorem MGSAugmentedLSFactorization.isLeastSquaresMinimizer_of_solve
    {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {Q1 : Fin m → Fin n → ℝ} {q : Fin m → ℝ}
    {R : Fin n → Fin n → ℝ} {z : Fin n → ℝ} {rho : ℝ}
    (h : MGSAugmentedLSFactorization A b Q1 q R z rho)
    {x : Fin n → ℝ}
    (hsolve : ∀ k : Fin n, matMulVec n R x k = z k) :
    IsLeastSquaresMinimizer A b x := by
  intro y
  rw [h.objective_eq_top_plus_rho_sq x, h.objective_eq_top_plus_rho_sq y]
  have htop_zero : vecNorm2Sq (mgsAugmentedTopResidual R z x) = 0 := by
    unfold vecNorm2Sq mgsAugmentedTopResidual
    apply Finset.sum_eq_zero
    intro k _
    rw [hsolve k]
    ring
  rw [htop_zero]
  have hnonneg : 0 ≤ vecNorm2Sq (mgsAugmentedTopResidual R z y) :=
    vecNorm2Sq_nonneg (mgsAugmentedTopResidual R z y)
  nlinarith
/-- Orthogonal row transformations preserve the rectangular Gram matrix. -/
theorem rectLSGram_matMulRectLeft_orthogonal {m n : ℕ}
    (U : Fin m → Fin m → ℝ) (A : Fin m → Fin n → ℝ)
    (hU : IsOrthogonal m U) :
    rectLSGram (matMulRectLeft U A) = rectLSGram A := by
  ext j k
  unfold rectLSGram matMulRectLeft
  have expand : ∀ i : Fin m,
      (∑ p : Fin m, U i p * A p j) *
          (∑ q : Fin m, U i q * A q k) =
        ∑ p : Fin m, ∑ q : Fin m,
          U i p * U i q * (A p j * A q k) := by
    intro i
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  simp_rw [expand]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  have factor : ∀ q : Fin m,
      ∑ i : Fin m, U i p * U i q * (A p j * A q k) =
        (∑ i : Fin m, U i p * U i q) * (A p j * A q k) := by
    intro q
    rw [← Finset.sum_mul]
  simp_rw [factor, hU.col_orthonormal]
  simp [Finset.sum_ite_eq, Finset.mem_univ]
/-- Orthogonal row transformations preserve the rectangular normal-equation
    right-hand side when applied to both `A` and `b`. -/
theorem rectLSRhs_matMulRectLeft_orthogonal {m n : ℕ}
    (U : Fin m → Fin m → ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hU : IsOrthogonal m U) :
    rectLSRhs (matMulRectLeft U A) (matMulVec m U b) = rectLSRhs A b := by
  ext j
  unfold rectLSRhs matMulRectLeft matMulVec
  have expand : ∀ i : Fin m,
      (∑ p : Fin m, U i p * A p j) *
          (∑ q : Fin m, U i q * b q) =
        ∑ p : Fin m, ∑ q : Fin m,
          U i p * U i q * (A p j * b q) := by
    intro i
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  simp_rw [expand]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  have factor : ∀ q : Fin m,
      ∑ i : Fin m, U i p * U i q * (A p j * b q) =
        (∑ i : Fin m, U i p * U i q) * (A p j * b q) := by
    intro q
    rw [← Finset.sum_mul]
  simp_rw [factor, hU.col_orthonormal]
  simp [Finset.sum_ite_eq, Finset.mem_univ]
/-- Nonnegativity of the QR geometric accumulation factor. -/
theorem qrSolveGeometricFactor_nonneg {n : ℕ} {cStep : ℝ}
    (hcStep : 0 ≤ cStep) :
    0 ≤ (1 + cStep) ^ n - 1 := by
  have hbase : 1 ≤ 1 + cStep := by linarith
  exact sub_nonneg.mpr (one_le_pow₀ hbase)
/-- Universal-form route elimination: upper-triangular nonsingular leading
    blocks together with positive active-block mass still do not imply the
    off-diagonal domination field required by
    `StoredQRSourceOffDiagonalControl`.

    This prevents the rectangular QR bottleneck from silently replacing the
    explicit off-diagonal-control hypothesis by the weaker nonbreakdown data
    available from rank/determinant arguments. -/
theorem not_forall_leadingBlock_upper_det_activeBlockPos_implies_offdiag_le_diag :
    ¬ (∀ (A_hat : ℕ → Fin 2 → Fin 2 → ℝ),
      (∀ k (hk : k < 2), ∀ i j : Fin (k + 1), j.val < i.val →
        qrLeadingBlock (A_hat k) (Nat.succ_le_iff.mpr hk) hk i j = 0) →
      (∀ k (hk : k < 2),
        Matrix.det
          (qrLeadingBlock (A_hat k) (Nat.succ_le_iff.mpr hk) hk :
            Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0) →
      (∀ k (hk : k < 2),
        0 < householderActiveBlockNorm2Sq
          ⟨k, hk⟩ ⟨k, hk⟩ (A_hat k)) →
      (∀ k (hk : k < 2), ∀ i j : Fin (k + 1), i.val < j.val →
        |qrLeadingBlock (A_hat k) (Nat.succ_le_iff.mpr hk) hk i j| ≤
          |qrLeadingBlock (A_hat k) (Nat.succ_le_iff.mpr hk) hk i i|)) := by
  intro h
  let A_hat : ℕ → Fin 2 → Fin 2 → ℝ := fun _ => diagDominanceCounterexample2
  have hupper : ∀ k (hk : k < 2), ∀ i j : Fin (k + 1), j.val < i.val →
      qrLeadingBlock (A_hat k) (Nat.succ_le_iff.mpr hk) hk i j = 0 := by
    intro k hk i j hji
    interval_cases k
    · fin_cases i
      fin_cases j
      omega
    · simpa [A_hat, qrLeadingBlock, qrLeadingRow, qrLeadingColumn] using
        diagDominanceCounterexample2_upper
          (qrLeadingRow 2 1 (Nat.succ_le_iff.mpr hk) i)
          (qrLeadingColumn 2 1 hk j)
          (by simpa [qrLeadingRow, qrLeadingColumn] using hji)
  have hdetLead : ∀ k (hk : k < 2),
      Matrix.det
        (qrLeadingBlock (A_hat k) (Nat.succ_le_iff.mpr hk) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0 := by
    intro k hk
    have hk_cases : k = 0 ∨ k = 1 := by omega
    rcases hk_cases with rfl | rfl
    · have hblock :
          (qrLeadingBlock diagDominanceCounterexample2
              (Nat.succ_le_iff.mpr hk) hk :
            Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℝ) =
            (fun _ _ => (1 : ℝ)) := by
        ext i j
        fin_cases i
        fin_cases j
        norm_num [qrLeadingBlock, qrLeadingRow, qrLeadingColumn,
          diagDominanceCounterexample2]
      rw [hblock, Matrix.det_fin_one]
      norm_num
    · have hblock :
          (qrLeadingBlock diagDominanceCounterexample2
              (Nat.succ_le_iff.mpr hk) hk :
            Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℝ) =
            (diagDominanceCounterexample2 : Matrix (Fin 2) (Fin 2) ℝ) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [qrLeadingBlock, qrLeadingRow, qrLeadingColumn]
      simpa [hblock] using diagDominanceCounterexample2_det_ne_zero
  have hactive : ∀ k (hk : k < 2),
      0 < householderActiveBlockNorm2Sq ⟨k, hk⟩ ⟨k, hk⟩ (A_hat k) := by
    intro k hk
    interval_cases k
    · simpa [A_hat] using
        householderActiveBlockNorm2Sq_pos_of_exists_active_entry_ne
          (p := (⟨0, by norm_num⟩ : Fin 2))
          (k := (⟨0, by norm_num⟩ : Fin 2))
          (A := diagDominanceCounterexample2)
          ⟨⟨0, by norm_num⟩, by norm_num,
            ⟨0, by norm_num⟩, by norm_num,
            by norm_num [diagDominanceCounterexample2]⟩
    · simpa [A_hat] using
        householderActiveBlockNorm2Sq_pos_of_exists_active_entry_ne
          (p := (⟨1, by norm_num⟩ : Fin 2))
          (k := (⟨1, by norm_num⟩ : Fin 2))
          (A := diagDominanceCounterexample2)
          ⟨⟨1, by norm_num⟩, by norm_num,
            ⟨1, by norm_num⟩, by norm_num,
            by norm_num [diagDominanceCounterexample2]⟩
  have hoffdiag := h A_hat hupper hdetLead hactive
  have hbad :=
    hoffdiag 1 (by norm_num)
      (⟨0, by norm_num⟩ : Fin (1 + 1))
      (⟨1, by norm_num⟩ : Fin (1 + 1))
      (by norm_num)
  norm_num [A_hat, qrLeadingBlock, qrLeadingRow, qrLeadingColumn,
    diagDominanceCounterexample2] at hbad
/-- The previous transposed leading block is nonsingular when the current
    leading block satisfies the repository's local diagonal-dominance predicate.

    The previous block is the transpose orientation of the top-left `k x k`
    part of the current `(k+1) x (k+1)` leading block.  Thus the
    upper-triangular/nonzero-diagonal fields inside `IsDiagDominantUpper`
    provide exactly the local lower-triangular/nonzero-diagonal certificate
    required by the QR determinant bridge. -/
theorem qrPreviousLeadingBlockTranspose_det_ne_zero_of_diagDominant_leadingBlock
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ)
    (hkmPrev : k ≤ m) (hkmLead : k + 1 ≤ m) (hk : k < n)
    (hDD : IsDiagDominantUpper (k + 1) (qrLeadingBlock A hkmLead hk)) :
    Matrix.det
      (qrPreviousLeadingBlockTranspose A hkmPrev hk :
        Matrix (Fin k) (Fin k) ℝ) ≠ 0 := by
  classical
  apply
    qrPreviousLeadingBlockTranspose_det_ne_zero_of_local_lower_triangular_diag_ne_zero
      A hkmPrev hk
  · intro i j hij
    have hzero := hDD.1 (Fin.castSucc j) (Fin.castSucc i) (by simpa using hij)
    simpa [qrPreviousLeadingBlockTranspose, qrLeadingBlock, qrPrefixRow,
      qrLeadingRow, qrPreviousColumn, qrLeadingColumn] using hzero
  · intro r
    have hdiag := hDD.2.1 (Fin.castSucc r)
    simpa [qrPreviousLeadingBlockTranspose, qrLeadingBlock, qrPrefixRow,
      qrLeadingRow, qrPreviousColumn, qrLeadingColumn] using hdiag
/-- The entrywise-absolute inverse block displayed after Theorem 20.2:
`[[|I-AA^+|, |A^+|^T], [|A^+|, |(A^T A)^-1|]]`. -/
noncomputable def higham20AlternativeAbsInverseBlock {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (gramInv : Fin n -> Fin n -> Real) :
    Fin (m + n) -> Fin (m + n) -> Real :=
  Fin.append
    (fun i : Fin m =>
      Fin.append
        (fun k : Fin m => |lsAugmentedProjectionBlock A Aplus i k|)
        (fun j : Fin n => |Aplus j i|))
    (fun j : Fin n =>
      Fin.append
        (fun i : Fin m => |Aplus j i|)
        (fun k : Fin n => |gramInv j k|))
/-- The off-diagonal componentwise data block
`[[0,E],[E^T,0]]` displayed after Theorem 20.2. -/
noncomputable def higham20AlternativeOffDiagonalBlock {m n : Nat}
    (E : Fin m -> Fin n -> Real) :
    Fin (m + n) -> Fin (m + n) -> Real :=
  Fin.append
    (fun i : Fin m =>
      Fin.append (fun _ : Fin m => 0) (fun j : Fin n => E i j))
    (fun j : Fin n =>
      Fin.append (fun i : Fin m => E i j) (fun _ : Fin n => 0))
/-- The exact matrix product occurring inside the alternative-bound norm. -/
noncomputable def higham20AlternativeCouplingMatrix {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (gramInv : Fin n -> Fin n -> Real) (E : Fin m -> Fin n -> Real) :
    Fin (m + n) -> Fin (m + n) -> Real :=
  rectMatMul (higham20AlternativeAbsInverseBlock A Aplus gramInv)
    (higham20AlternativeOffDiagonalBlock E)
theorem higham20AlternativeOffDiagonalBlock_mulVec {m n : Nat}
    (E : Fin m -> Fin n -> Real) (u : Fin m -> Real) (v : Fin n -> Real) :
    rectMatMulVec (higham20AlternativeOffDiagonalBlock E) (Fin.append u v) =
      Fin.append (rectMatMulVec E v)
        (fun j => Finset.univ.sum (fun i : Fin m => E i j * u i)) := by
  ext k
  refine Fin.addCases ?_ ?_ k
  · intro i
    simp [higham20AlternativeOffDiagonalBlock, rectMatMulVec,
      Fin.sum_univ_add]
  · intro j
    simp [higham20AlternativeOffDiagonalBlock, rectMatMulVec,
      Fin.sum_univ_add]
theorem higham20AlternativeAbsInverseBlock_nonneg {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (gramInv : Fin n -> Fin n -> Real) :
    forall i j, 0 <= higham20AlternativeAbsInverseBlock A Aplus gramInv i j := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro ii j
    refine Fin.addCases ?_ ?_ j <;> intro jj <;>
      simp [higham20AlternativeAbsInverseBlock]
  · intro ii j
    refine Fin.addCases ?_ ?_ j <;> intro jj <;>
      simp [higham20AlternativeAbsInverseBlock]
theorem higham20AlternativeOffDiagonalBlock_nonneg {m n : Nat}
    {E : Fin m -> Fin n -> Real} (hE : forall i j, 0 <= E i j) :
    forall i j, 0 <= higham20AlternativeOffDiagonalBlock E i j := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro ii j
    refine Fin.addCases ?_ ?_ j <;> intro jj
    · simp [higham20AlternativeOffDiagonalBlock]
    · simpa [higham20AlternativeOffDiagonalBlock] using hE ii jj
  · intro ii j
    refine Fin.addCases ?_ ?_ j <;> intro jj
    · simpa [higham20AlternativeOffDiagonalBlock] using hE jj ii
    · simp [higham20AlternativeOffDiagonalBlock]
theorem higham20AlternativeCouplingMatrix_nonneg {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (gramInv : Fin n -> Fin n -> Real)
    {E : Fin m -> Fin n -> Real} (hE : forall i j, 0 <= E i j) :
    forall i j, 0 <= higham20AlternativeCouplingMatrix A Aplus gramInv E i j := by
  intro i j
  unfold higham20AlternativeCouplingMatrix rectMatMul
  exact Finset.sum_nonneg (fun k _ => mul_nonneg
    (higham20AlternativeAbsInverseBlock_nonneg A Aplus gramInv i k)
    (higham20AlternativeOffDiagonalBlock_nonneg hE k j))
/-- Euclidean norm is bounded by the sum of coordinate absolute values. -/
theorem higham20_vecNorm2_le_sum_abs {d : Nat} (v : Fin d → Real) :
    vecNorm2 v ≤ ∑ i : Fin d, |v i| := by
  have hsq : vecNorm2 v ^ 2 ≤ (∑ i : Fin d, |v i|) ^ 2 := by
    rw [vecNorm2_sq]
    exact vecNorm2Sq_le_sum_abs_sq v
  have hv : 0 ≤ vecNorm2 v := vecNorm2_nonneg v
  have hs : 0 ≤ ∑ i : Fin d, |v i| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg (v i))
  nlinarith
/-- The repository's complex `L²` norm agrees with `vecNorm2` on embedded
real vectors. -/
theorem higham20_complexVecLpNorm_two_realVecToComplex_eq_vecNorm2
    {d : Nat} (v : Fin d → Real) :
    complexVecLpNorm (ENNReal.ofReal (2 : Real)) (realVecToComplex v) =
      vecNorm2 v := by
  calc
    complexVecLpNorm (ENNReal.ofReal (2 : Real)) (realVecToComplex v) =
        norm (WithLp.toLp (2 : ENNReal) (realVecToComplex v)) :=
      complexVecLpNorm_two_eq_toLp (realVecToComplex v)
    _ = norm (realVecToEuclidean v) := by rfl
    _ = vecNorm2 v := realVecToEuclidean_norm v

end NumStability
