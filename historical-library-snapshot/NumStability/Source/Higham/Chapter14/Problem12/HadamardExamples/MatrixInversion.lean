import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter14.Problem11.HadamardCondition.MatrixInversion

/-!
# Chapter14 Problem12 HadamardExamples MatrixInversion

Canonical destination for material split out of
`NumStability.Algorithms.MatrixInversion` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Higham, 2nd ed., Chapter 14, Problem 14.12:
    Euclidean norm of column `j`, the quantity `rho_j = ||R(:,j)||_2` in the
    QR formula for the Hadamard condition number. -/
noncomputable def higham14_colNorm2 {n : ℕ}
    (A : Fin n → Fin n → ℝ) (j : Fin n) : ℝ :=
  vecNorm2 (fun i : Fin n => A i j)

/-- Orthogonal real matrices have determinant of absolute value one. -/
lemma higham14_abs_det_eq_one_of_isOrthogonal {n : ℕ}
    {Q : Fin n → Fin n → ℝ} (hQ : IsOrthogonal n Q) :
    |Matrix.det (Q : Matrix (Fin n) (Fin n) ℝ)| = 1 := by
  let QM : Matrix (Fin n) (Fin n) ℝ := Q
  have hmat :
      Matrix.transpose QM * QM = 1 := by
    ext i j
    simpa [QM, Matrix.mul_apply, Matrix.transpose_apply, matTranspose, idMatrix]
      using hQ.left_inv i j
  have hsquare : Matrix.det QM ^ 2 = 1 := by
    have hdet := congrArg Matrix.det hmat
    simpa [Matrix.det_mul, Matrix.det_transpose, pow_two] using hdet
  have habs_square : |Matrix.det QM| ^ 2 = 1 := by
    rw [sq_abs, hsquare]
  rcases (sq_eq_one_iff.mp habs_square) with h | h
  · simpa [QM] using h
  · have hnonneg : 0 ≤ |Matrix.det QM| := abs_nonneg _
    linarith

/-- Left multiplication by an orthogonal matrix preserves each column
    Euclidean norm. -/
lemma higham14_colNorm2_matMul_orthogonal_left {n : ℕ}
    (Q R : Fin n → Fin n → ℝ) (hQ : IsOrthogonal n Q) (j : Fin n) :
    higham14_colNorm2 (matMul n Q R) j = higham14_colNorm2 R j := by
  unfold higham14_colNorm2 matMul
  exact vecNorm2_orthogonal Q (fun k : Fin n => R k j) hQ

/-- In a QR factorization of `A^T`, row norms of `A` are column norms of `R`. -/
lemma higham14_rowNorm2_eq_colNorm2_of_transpose_qr {n : ℕ}
    (A Q R : Fin n → Fin n → ℝ)
    (hQR : ∀ i j : Fin n, A j i = matMul n Q R i j)
    (hQ : IsOrthogonal n Q) (i : Fin n) :
    higham14_rowNorm2 A i = higham14_colNorm2 R i := by
  calc
    higham14_rowNorm2 A i = higham14_colNorm2 (matMul n Q R) i := by
      unfold higham14_rowNorm2 higham14_colNorm2
      congr 1
      ext j
      exact hQR j i
    _ = higham14_colNorm2 R i :=
        higham14_colNorm2_matMul_orthogonal_left Q R hQ i

/-- Higham, 2nd ed., Chapter 14, Problem 14.12(a):
    if `A^T = Q R` with `Q` orthogonal and `det(R) = prod_i r_ii`, then the
    Hadamard condition number satisfies
    `psi(A) = prod_i rho_i / |r_ii|`, where `rho_i = ||R(:,i)||_2`.

    The determinant-product hypothesis is separated out so callers can use any
    triangular or otherwise suitable QR certificate. -/
theorem higham14_problem14_12_hadamardConditionNumber_eq_prod_colNorm2_div_abs_diag_of_transpose_qr_det_product
    {n : ℕ} (A Q R : Fin n → Fin n → ℝ)
    (hQR : ∀ i j : Fin n, A j i = matMul n Q R i j)
    (hQ : IsOrthogonal n Q)
    (hdetR : Matrix.det (R : Matrix (Fin n) (Fin n) ℝ) = ∏ i : Fin n, R i i) :
    higham14_hadamardConditionNumber A =
      ∏ i : Fin n, higham14_colNorm2 R i / |R i i| := by
  have hrow : ∀ i : Fin n, higham14_rowNorm2 A i = higham14_colNorm2 R i :=
    higham14_rowNorm2_eq_colNorm2_of_transpose_qr A Q R hQR hQ
  have hQRmat :
      let AM : Matrix (Fin n) (Fin n) ℝ := A
      let QM : Matrix (Fin n) (Fin n) ℝ := Q
      let RM : Matrix (Fin n) (Fin n) ℝ := R
      Matrix.transpose AM = QM * RM := by
    dsimp only
    ext i j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, matMul] using hQR i j
  have hdetA :
      Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) =
        Matrix.det (Q : Matrix (Fin n) (Fin n) ℝ) * (∏ i : Fin n, R i i) := by
    let AM : Matrix (Fin n) (Fin n) ℝ := A
    let QM : Matrix (Fin n) (Fin n) ℝ := Q
    let RM : Matrix (Fin n) (Fin n) ℝ := R
    have hdet_trans :
        Matrix.det (Matrix.transpose AM) = Matrix.det (QM * RM) := by
      simpa [AM, QM, RM] using congrArg Matrix.det hQRmat
    rw [Matrix.det_transpose, Matrix.det_mul] at hdet_trans
    simpa [AM, QM, RM, hdetR] using hdet_trans
  have hden :
      |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| =
        ∏ i : Fin n, |R i i| := by
    rw [hdetA, abs_mul, higham14_abs_det_eq_one_of_isOrthogonal hQ, one_mul,
      Finset.abs_prod]
  unfold higham14_hadamardConditionNumber
  rw [Finset.prod_congr rfl (fun i _ => hrow i), hden]
  rw [← Finset.prod_div_distrib]

/-- Higham, 2nd ed., Chapter 14, Problem 14.12(a):
    source-shaped QR formula for `psi(A)` when `A^T = Q R`, `Q` is orthogonal,
    and `R` is upper triangular. -/
theorem higham14_problem14_12_hadamardConditionNumber_eq_prod_colNorm2_div_abs_diag_of_transpose_qr
    {n : ℕ} (A Q R : Fin n → Fin n → ℝ)
    (hQR : ∀ i j : Fin n, A j i = matMul n Q R i j)
    (hQ : IsOrthogonal n Q)
    (hRupper : (show Matrix (Fin n) (Fin n) ℝ from R).BlockTriangular id) :
    higham14_hadamardConditionNumber A =
      ∏ i : Fin n, higham14_colNorm2 R i / |R i i| :=
  higham14_problem14_12_hadamardConditionNumber_eq_prod_colNorm2_div_abs_diag_of_transpose_qr_det_product
    A Q R hQR hQ (Matrix.det_of_upperTriangular hRupper)

/-- Higham, 2nd ed., Chapter 14, Problem 14.12(b):
    the Pei matrix `A = (alpha - 1) I + e e^T`, equivalently diagonal entries
    `alpha` and off-diagonal entries `1`. -/
noncomputable def higham14_peiMatrix (n : ℕ) (α : ℝ) : Fin n → Fin n → ℝ :=
  fun i j => if i = j then α else 1

/-- Higham, 2nd ed., Chapter 14, Problem 14.12(b), dependency:
    every row of the Pei matrix has squared Euclidean norm
    `alpha^2 + n - 1`. -/
lemma higham14_problem14_12_peiMatrix_row_sq_sum
    (n : ℕ) (α : ℝ) (i : Fin n) :
    (∑ j : Fin n, (higham14_peiMatrix n α i j) ^ 2) =
      α ^ 2 + ((n - 1 : ℕ) : ℝ) := by
  calc
    (∑ j : Fin n, (higham14_peiMatrix n α i j) ^ 2)
        = ∑ j : Fin n, ((1 : ℝ) + if j = i then α ^ 2 - 1 else 0) := by
            apply Finset.sum_congr rfl
            intro j _
            by_cases hji : j = i
            · subst j
              simp [higham14_peiMatrix]
            · have hij : i ≠ j := by exact Ne.symm hji
              simp [higham14_peiMatrix, hij, hji]
    _ = α ^ 2 + ((n - 1 : ℕ) : ℝ) := by
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_const, Fintype.card_fin]
        have hnpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
        rw [Nat.cast_sub (Nat.succ_le_of_lt hnpos)]
        ring

/-- Higham, 2nd ed., Chapter 14, Problem 14.12(b), dependency:
    row norm of the Pei matrix. -/
lemma higham14_problem14_12_peiMatrix_rowNorm2
    (n : ℕ) (α : ℝ) (i : Fin n) :
    higham14_rowNorm2 (higham14_peiMatrix n α) i =
      Real.sqrt (α ^ 2 + ((n - 1 : ℕ) : ℝ)) := by
  have harg_nonneg : 0 ≤ α ^ 2 + ((n - 1 : ℕ) : ℝ) :=
    add_nonneg (sq_nonneg α) (Nat.cast_nonneg _)
  exact (sq_eq_sq₀ (higham14_rowNorm2_nonneg _ _) (Real.sqrt_nonneg _)).mp (by
    rw [higham14_rowNorm2, vecNorm2_sq, vecNorm2Sq]
    rw [Real.sq_sqrt harg_nonneg]
    exact higham14_problem14_12_peiMatrix_row_sq_sum n α i)

/-- Higham, 2nd ed., Chapter 14, Problem 14.12(b), dependency:
    numerator product of the Pei matrix Hadamard condition number. -/
lemma higham14_problem14_12_peiMatrix_prod_rowNorm2
    (n : ℕ) (α : ℝ) :
    (∏ i : Fin n, higham14_rowNorm2 (higham14_peiMatrix n α) i) =
      (Real.sqrt (α ^ 2 + ((n - 1 : ℕ) : ℝ))) ^ n := by
  calc
    (∏ i : Fin n, higham14_rowNorm2 (higham14_peiMatrix n α) i)
        = ∏ _i : Fin n, Real.sqrt (α ^ 2 + ((n - 1 : ℕ) : ℝ)) := by
            apply Finset.prod_congr rfl
            intro i _
            exact higham14_problem14_12_peiMatrix_rowNorm2 n α i
    _ = (Real.sqrt (α ^ 2 + ((n - 1 : ℕ) : ℝ))) ^ n := by
            simp [Fintype.card_fin]

end NumStability
