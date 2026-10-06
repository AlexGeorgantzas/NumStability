import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.Cholesky.Factorization.Spec
import NumStability.Algorithms.LinearSystems.Cholesky.Solve.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.RankGeometry
import NumStability.Algorithms.LinearSystems.QR.GramSchmidt
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Pseudoinverse.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Specifications.UnderdeterminedSpec
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Normwise
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter19.Core
import NumStability.Source.Higham.Chapter20.Theorem03.QRSolve
import NumStability.Source.Higham.Chapter21.Equation01.QRFoundations
import NumStability.Source.Higham.Chapter21.Equation03.QRFoundations
import NumStability.Source.Higham.Chapter21.Equation04.UnderdeterminedSpec

/-!
# Source.Higham.Chapter21.Equation04.QRFoundations

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/



namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-!
# Higham Chapter 21: QR foundations for equations (21.1)-(21.4)

This file packages the exact algebra on printed pages 408-409.  An exact QR
certificate for `A^T` has the repository shape

`finiteTranspose A = matMulRectLeft Q (lsQRTallBlock R)`.

The rounded Householder factor has a different domain: source full row rank is
paired with the explicit computed-top-block nonbreakdown condition already
recorded by `Higham21QMethodFullRowRankComputedQRDomain`.
-/










































































































































































































































































































/-- Equation (21.4): the Q-method vector and the canonical Gram
    pseudoinverse action are the same vector under one exact QR/full-rank
    domain. -/
theorem higham21_eq21_4_q_method_eq_gram_pseudoinverse_of_full_row_rank_exact_qr
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (R : Fin m → Fin m → ℝ)
    (b y1 : Fin m → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (hAT : finiteTranspose A =
      matMulRectLeft Q (lsQRTallBlock (k := k) R))
    (hfull : lsRealRectColRank (finiteTranspose A) = m)
    (hy1 : (fun j : Fin m => ∑ i : Fin m, R i j * y1 i) = b) :
    matMulVec (m + k) Q (Fin.append y1 (0 : Fin k → ℝ)) =
      rectMatMulVec (undetAplusOfGramNonsingInv A) b := by
  have hdetGram :
      Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
    higham21_rectGram_det_ne_zero_of_transpose_full_col_rank A hfull
  have hcanonical :
      RectMinNormSolution m (m + k) A b
        (rectMatMulVec (undetAplusOfGramNonsingInv A) b) :=
    higham21_eq21_4_rect_pseudoinverse_formula_min_norm_of_gram_det_ne_zero
      A b hdetGram
  have hunique :=
    (higham21_eq21_3_unique_min_norm_of_full_row_rank_exact_qr
      A Q R b y1 hQ hAT hfull hy1
        (rectMatMulVec (undetAplusOfGramNonsingInv A) b)).mp hcanonical
  exact hunique.symm















































































/-- Equation (21.4) in the printed `R^{-T}b` form. -/
theorem higham21_eq21_4_inverse_coordinates_eq_gram_pseudoinverse_of_full_row_rank_exact_qr
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (R : Fin m → Fin m → ℝ)
    (b : Fin m → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (hAT : finiteTranspose A =
      matMulRectLeft Q (lsQRTallBlock (k := k) R))
    (hfull : lsRealRectColRank (finiteTranspose A) = m) :
    matMulVec (m + k) Q
        (Fin.append
          (matMulVec m (nonsingInv m (matTranspose R)) b)
          (0 : Fin k → ℝ)) =
      rectMatMulVec (undetAplusOfGramNonsingInv A) b := by
  have hdetR :=
    higham21_eq21_1_top_R_det_ne_zero_of_full_row_rank_exact_qr
      A Q R hQ hAT hfull
  have hdetT :
      Matrix.det (matTranspose R : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
    change
      Matrix.det (Matrix.transpose (R : Matrix (Fin m) (Fin m) ℝ)) ≠ 0
    simpa [Matrix.det_transpose] using hdetR
  have hInv :=
    isInverse_nonsingInv_of_det_ne_zero m (matTranspose R) hdetT
  have hy1 :
      (fun j : Fin m =>
        ∑ i : Fin m,
          R i j * matMulVec m (nonsingInv m (matTranspose R)) b i) = b := by
    simpa [matMulVec, matTranspose] using
      matMulVec_of_isRightInverse
        (matTranspose R) (nonsingInv m (matTranspose R)) hInv.2 b
  exact
    higham21_eq21_4_q_method_eq_gram_pseudoinverse_of_full_row_rank_exact_qr
      A Q R b (matMulVec m (nonsingInv m (matTranspose R)) b)
        hQ hAT hfull hy1

end NumStability
