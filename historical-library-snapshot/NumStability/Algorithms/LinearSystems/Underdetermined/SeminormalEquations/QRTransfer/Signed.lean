import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Finset
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.CondEstimation
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Cholesky.Factorization.Spec
import NumStability.Algorithms.LinearSystems.Cholesky.Solve.Basic
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Assembly.Core
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Basic
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Certificates
import NumStability.Algorithms.LinearSystems.LeastSquares.AugmentedSystem
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations
import NumStability.Algorithms.LinearSystems.LeastSquares.QRSolve
import NumStability.Algorithms.LinearSystems.LeastSquares.RankGeometry
import NumStability.Algorithms.LinearSystems.LeastSquares.StoredQR
import NumStability.Algorithms.LinearSystems.QR.GivensQR
import NumStability.Algorithms.LinearSystems.QR.GramSchmidt
import NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication
import NumStability.Algorithms.LinearSystems.QR.Householder.StoredQR
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Algorithms.LinearSystems.QR.HouseholderQR
import NumStability.Algorithms.LinearSystems.QR.HouseholderSpec
import NumStability.Algorithms.LinearSystems.QR.QRSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.DiagonalDominance
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.InverseBounds
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Pseudoinverse.UnderdeterminedSpec
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Asymptotics.Bounds
import NumStability.Analysis.Conditioning.DistanceToSingularity
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.LinearOperators.Basic
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Basic
import NumStability.Analysis.MatrixNorms.Comparisons
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.MatrixNorms.SpectralRadius
import NumStability.Analysis.MatrixNorms.UnitarilyInvariant
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.OperatorNorms.Basic
import NumStability.Analysis.Perturbation.LeastSquares.AugmentedSystem
import NumStability.Analysis.Perturbation.LeastSquares.BackwardError
import NumStability.Analysis.Perturbation.LeastSquares.Basic
import NumStability.Analysis.Perturbation.LeastSquares.Normwise
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.Analysis.SingularValues.Basic
import NumStability.Analysis.SingularValues.Realification
import NumStability.Analysis.Summation.Signs
import NumStability.Analysis.VectorNorms.Basic
import NumStability.FloatingPoint.Model

/-!
# Algorithms.LinearSystems.Underdetermined.SeminormalEquations.QRTransfer.Signed

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Signed factorwise algebra for the seminormal-equations analysis.



namespace NumStability

open scoped BigOperators

/-!
# Signed SNE factorwise identities

This module retains the two triangular-solve perturbations separately.  Its
core identities are the exact finite counterparts of Demmel--Higham (1993),
equations (3.10)--(3.17); no asymptotic `O(u^2)` term is discarded.
-/








































































































































































































































































































































/-- Economy orthonormality in the rectangular-product notation used by the
SNE signed analysis. -/
theorem higham21_sne_qr_economy_gram_eq_id
    {m n : Nat} (Q : Fin n -> Fin m -> Real)
    (hQ : GramSchmidtOrthonormalColumns Q) :
    rectMatMul (finiteTranspose Q) Q = idMatrix m := by
  ext i j
  simpa [rectMatMul, finiteTranspose, rectangularGram] using hQ i j

/-- Transposed form of an economy factorization `B^T = Q R`. -/
theorem higham21_sne_qr_transpose_factor
    {m n : Nat} (B : Fin m -> Fin n -> Real)
    (Q : Fin n -> Fin m -> Real) (R : Fin m -> Fin m -> Real)
    (hFactor : finiteTranspose B = rectMatMul Q R) :
    B = rectMatMul (finiteTranspose R) (finiteTranspose Q) := by
  ext i j
  have hij := congrFun (congrFun hFactor j) i
  unfold finiteTranspose at hij
  rw [hij]
  unfold rectMatMul finiteTranspose
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The Gram matrix of an exact economy factor is `R^T R`. -/
theorem higham21_sne_qr_rectGram_eq
    {m n : Nat} (B : Fin m -> Fin n -> Real)
    (Q : Fin n -> Fin m -> Real) (R : Fin m -> Fin m -> Real)
    (hQ : GramSchmidtOrthonormalColumns Q)
    (hFactor : finiteTranspose B = rectMatMul Q R) :
    rectGram B = rectMatMul (finiteTranspose R) R := by
  have hB := higham21_sne_qr_transpose_factor B Q R hFactor
  have hQtQ := higham21_sne_qr_economy_gram_eq_id Q hQ
  have hGramProduct : rectGram B = rectMatMul B (finiteTranspose B) := by
    ext i j
    rfl
  rw [hGramProduct, hFactor, hB]
  calc
    rectMatMul
        (rectMatMul (finiteTranspose R) (finiteTranspose Q))
        (rectMatMul Q R) =
      rectMatMul (finiteTranspose R)
        (rectMatMul (finiteTranspose Q) (rectMatMul Q R)) := by
          exact rectMatMul_assoc
            (finiteTranspose R) (finiteTranspose Q) (rectMatMul Q R)
    _ = rectMatMul (finiteTranspose R)
        (rectMatMul (rectMatMul (finiteTranspose Q) Q) R) := by
          exact congrArg (rectMatMul (finiteTranspose R))
            (rectMatMul_assoc (finiteTranspose Q) Q R).symm
    _ = rectMatMul (finiteTranspose R)
        (rectMatMul (idMatrix m) R) := by rw [hQtQ]
    _ = rectMatMul (finiteTranspose R) R := by rw [rectMatMul_id_left]

/-- Canonical pseudoinverse compatibility with an invertible economy QR
factorization:

`B^+ = Q R^{-T}`.

The canonical Gram pseudoinverse is essential here; a generic right inverse of
`B` need not have this factor form. -/
theorem higham21_sne_qr_pseudoinverse_factor
    {m n : Nat} (B : Fin m -> Fin n -> Real)
    (Q : Fin n -> Fin m -> Real)
    (R Rinv : Fin m -> Fin m -> Real)
    (hQ : GramSchmidtOrthonormalColumns Q)
    (hFactor : finiteTranspose B = rectMatMul Q R)
    (hInv : IsInverse m R Rinv) :
    undetAplusOfGramNonsingInv B =
      rectMatMul Q (finiteTranspose Rinv) := by
  have hGram := higham21_sne_qr_rectGram_eq B Q R hQ hFactor
  have hRRinv : rectMatMul R Rinv = idMatrix m := by
    ext i j
    exact hInv.2 i j
  rw [undetAplusOfGramNonsingInv,
    undetAplusOfGramInv_eq_rectMatMul_finiteTranspose]
  rw [hFactor]
  rw [show undetGramNonsingInv B =
      rectMatMul Rinv (finiteTranspose Rinv) by
    unfold undetGramNonsingInv
    rw [hGram]
    exact nonsingInv_rectMatMul_transpose_self_of_IsInverse hInv]
  calc
    rectMatMul (rectMatMul Q R)
        (rectMatMul Rinv (finiteTranspose Rinv)) =
      rectMatMul Q
        (rectMatMul R (rectMatMul Rinv (finiteTranspose Rinv))) := by
          exact rectMatMul_assoc Q R
            (rectMatMul Rinv (finiteTranspose Rinv))
    _ = rectMatMul Q
        (rectMatMul (rectMatMul R Rinv) (finiteTranspose Rinv)) := by
          exact congrArg (rectMatMul Q)
            (rectMatMul_assoc R Rinv (finiteTranspose Rinv)).symm
    _ = rectMatMul Q
        (rectMatMul (idMatrix m) (finiteTranspose Rinv)) := by rw [hRRinv]
    _ = rectMatMul Q (finiteTranspose Rinv) := by rw [rectMatMul_id_left]

/-- Absolute-value operator bound for an economy matrix with `m`
orthonormal columns. -/
theorem higham21_sne_abs_economy_rectOpNorm2Le
    {m n : Nat} (hm : 0 < m) (Q : Fin n -> Fin m -> Real)
    (hQ : GramSchmidtOrthonormalColumns Q) :
    rectOpNorm2Le (absMatrixRect Q) (Real.sqrt (m : Real)) := by
  classical
  have hrank : realRectMatrixRank Q <= m := by
    unfold realRectMatrixRank complexMatrixRank
    simpa using
      (Matrix.rank_le_card_width
        (realRectToCMatrix Q : Matrix (Fin n) (Fin m) Complex))
  have hsqrt :
      Real.sqrt (realRectMatrixRank Q : Real) <= Real.sqrt (m : Real) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hrank)
  have hbase :=
    rectOpNorm2Le_absMatrixRect_sqrt_rank_mul_of_rectOpNorm2Le
      hm Q (by norm_num : (0 : Real) <= 1) hQ.rectOpNorm2Le_one
  exact rectOpNorm2Le_mono (by simpa only [mul_one] using hsqrt) hbase

/-- Transposed absolute-value operator bound for an economy matrix. -/
theorem higham21_sne_abs_economy_transpose_rectOpNorm2Le
    {m n : Nat} (hm : 0 < m) (Q : Fin n -> Fin m -> Real)
    (hQ : GramSchmidtOrthonormalColumns Q) :
    rectOpNorm2Le (absMatrixRect (finiteTranspose Q))
      (Real.sqrt (m : Real)) := by
  have hAbsTranspose :
      absMatrixRect (finiteTranspose Q) =
        finiteTranspose (absMatrixRect Q) := by
    ext i j
    rfl
  rw [hAbsTranspose]
  exact rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
    (absMatrixRect Q) (Real.sqrt_nonneg _)
      (higham21_sne_abs_economy_rectOpNorm2Le hm Q hQ)

/-- Absolute values of an exact rectangular product are bounded by the
product of the absolute-value factors. -/
theorem higham21_sne_abs_rectMatMul_entry_le
    {m n p : Nat} (A : Fin m -> Fin n -> Real)
    (B : Fin n -> Fin p -> Real) (i : Fin m) (j : Fin p) :
    absMatrixRect (rectMatMul A B) i j <=
      rectMatMul (absMatrixRect A) (absMatrixRect B) i j := by
  unfold absMatrixRect rectMatMul
  calc
    |∑ k : Fin n, A i k * B k j| <=
        ∑ k : Fin n, |A i k * B k j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |A i k| * |B k j| := by
      apply Finset.sum_congr rfl
      intro k hk
      exact abs_mul (A i k) (B k j)

/-- A componentwise relative matrix perturbation gives the corresponding
absolute matrix-vector majorant. -/
theorem higham21_sne_componentwise_matvec_majorant
    {m n : Nat} (theta : Real)
    (A Delta : Fin m -> Fin n -> Real)
    (hDelta : forall i j, |Delta i j| <= theta * |A i j|)
    (x : Fin n -> Real) (i : Fin m) :
    |rectMatMulVec Delta x i| <=
      theta * rectMatMulVec (absMatrixRect A) (fun j => |x j|) i := by
  calc
    |rectMatMulVec Delta x i| <=
        ∑ j : Fin n, |Delta i j| * |x j| :=
      abs_rectMatMulVec_le Delta x i
    _ <= ∑ j : Fin n, (theta * |A i j|) * |x j| := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (hDelta i j) (abs_nonneg _)
    _ = theta * rectMatMulVec (absMatrixRect A)
        (fun j => |x j|) i := by
      unfold rectMatMulVec absMatrixRect
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring









































































































































































































































































































































































































































































































































































































































































end NumStability
