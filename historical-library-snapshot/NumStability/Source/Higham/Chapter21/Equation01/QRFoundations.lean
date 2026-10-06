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
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Normwise
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter19.Core
import NumStability.Source.Higham.Chapter20.Theorem03.QRSolve
import NumStability.Source.Higham.Chapter21.Equation05.UnderdeterminedSolve
import NumStability.Source.Higham.Chapter21.Theorem04.HouseholderQMethod.UnderdeterminedSolve

/-!
# Source.Higham.Chapter21.Equation01.QRFoundations

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

/-- Full row rank of `A`, represented as full column rank of `A^T`, makes
    the underdetermined Gram matrix `A A^T` nonsingular. -/
theorem higham21_rectGram_det_ne_zero_of_transpose_full_col_rank
    {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (hfull : lsRealRectColRank (finiteTranspose A) = m) :
    Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
  have hinj : Function.Injective (rectMatMulVec (finiteTranspose A)) :=
    lsRealRectColRank_rectMatMulVec_injective_of_colRank_eq_card
      (finiteTranspose A) hfull
  have hdet :
      Matrix.det
        (rectLSGram (finiteTranspose A) : Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
    rectLSGram_det_ne_zero_of_rectMatMulVec_injective
      (finiteTranspose A) hinj
  simpa [rectLSGram, rectGram, finiteTranspose] using hdet

/-- Under an exact factorization `A^T = Q [R;0]`, full row rank of `A`
    forces the square top factor `R` to be nonsingular. -/
theorem higham21_eq21_1_top_R_det_ne_zero_of_full_row_rank_exact_qr
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (R : Fin m → Fin m → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (hAT : finiteTranspose A =
      matMulRectLeft Q (lsQRTallBlock (k := k) R))
    (hfull : lsRealRectColRank (finiteTranspose A) = m) :
    Matrix.det (R : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
  have hA :
      A = finiteTranspose
        (matMulRectLeft Q (lsQRTallBlock (k := k) R)) := by
    ext i j
    have hij := congrFun (congrFun hAT j) i
    simpa [finiteTranspose] using hij
  have hdetGram :
      Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
    higham21_rectGram_det_ne_zero_of_transpose_full_col_rank A hfull
  have hgram :
      rectGram A =
        fun i j : Fin m => ∑ row : Fin m, R row i * R row j := by
    calc
      rectGram A =
          rectGram
            (finiteTranspose
              (matMulRectLeft Q (lsQRTallBlock (k := k) R))) :=
        congrArg rectGram hA
      _ = fun i j : Fin m => ∑ row : Fin m, R row i * R row j :=
        higham21_eq21_5_qr_sne_gram_eq Q hQ R
  let RM : Matrix (Fin m) (Fin m) ℝ := R
  intro hdetR
  apply hdetGram
  calc
    Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) =
        Matrix.det
          ((fun i j : Fin m => ∑ row : Fin m, R row i * R row j) :
            Matrix (Fin m) (Fin m) ℝ) :=
      congrArg Matrix.det hgram
    _ = Matrix.det (RM.transpose * RM) := by
      congr 1
    _ = Matrix.det RM.transpose * Matrix.det RM :=
      Matrix.det_mul _ _
    _ = 0 := by simp [RM, Matrix.det_transpose, hdetR]

/-- The concrete source domain includes exactly the nonbreakdown needed to
    make the computed Householder top block nonsingular.  No claim is made
    that source rank alone preserves rank after rounding. -/
theorem higham21_eq21_1_computed_top_R_det_ne_zero_of_full_row_rank_domain
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A) :
    Matrix.det
      ((fun i j =>
        fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
          (Fin.castAdd k i) j) : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
  let Rtop : Fin m → Fin m → ℝ := fun i j =>
    fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
      (Fin.castAdd k i) j
  have hupperTall :
      IsUpperTrapezoidal (m + k) m
        (fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)) :=
    fl_householderQRPanel_R_upper_trapezoidal fp (m + k) m
      (finiteTranspose A)
  have hupper : ∀ i j : Fin m, j.val < i.val → Rtop i j = 0 := by
    simpa [Rtop] using
      lsQRTallBlock_top_upper_of_upper_trapezoidal
        (fl_householderQRPanel_R fp (m + k) m (finiteTranspose A))
        hupperTall
  have hdiag : ∀ i : Fin m, Rtop i i ≠ 0 := by
    simpa [Rtop, Higham21QMethodTopBlockNonbreakdown,
      lsTheorem20_4ComputedQRNonbreakdown] using
      Higham21QMethodFullRowRankComputedQRDomain.nonbreakdown hdomain
  simpa [Rtop] using
    det_ne_zero_of_upper_triangular_diag_ne_zero m Rtop hupper hdiag






























































































































































































































































































































































end NumStability
