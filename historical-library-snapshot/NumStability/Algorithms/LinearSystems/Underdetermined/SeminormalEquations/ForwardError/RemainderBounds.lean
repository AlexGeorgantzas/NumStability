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
# Algorithms.LinearSystems.Underdetermined.SeminormalEquations.ForwardError.RemainderBounds

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Uniform local bounds for the signed SNE higher-order terms.



namespace NumStability

open scoped BigOperators

set_option maxHeartbeats 1200000
































































































































































































































































































































































/-- Moving the vector in an absolute transpose action costs at most the
Frobenius norm of the matrix times the vector displacement. -/
theorem higham21_sne_source_abs_action_change
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (ybar yhat : Fin m -> Real) :
    vecNorm2
        (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)) <=
      vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|)) +
        frobNorm A * vecNorm2 (fun i => ybar i - yhat i) := by
  let wbar : Fin n -> Real :=
    rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|)
  let wd : Fin n -> Real :=
    rectTransposeMulVec (absMatrixRect A)
      (fun i => |ybar i - yhat i|)
  let what : Fin n -> Real :=
    rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)
  have hwbar : forall j, 0 <= wbar j := by
    intro j
    dsimp [wbar, rectTransposeMulVec, absMatrixRect]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hwd : forall j, 0 <= wd j := by
    intro j
    dsimp [wd, rectTransposeMulVec, absMatrixRect]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hwhat : forall j, 0 <= what j := by
    intro j
    dsimp [what, rectTransposeMulVec, absMatrixRect]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hpoint : forall j, |what j| <= wbar j + wd j := by
    intro j
    rw [abs_of_nonneg (hwhat j)]
    dsimp [what, wbar, wd, rectTransposeMulVec, absMatrixRect]
    calc
      ∑ i : Fin m, |A i j| * |yhat i| <=
          ∑ i : Fin m, |A i j| * (|ybar i| + |ybar i - yhat i|) := by
        apply Finset.sum_le_sum
        intro i _
        have hi : |yhat i| <= |ybar i| + |ybar i - yhat i| := by
          calc
            |yhat i| = |ybar i - (ybar i - yhat i)| := by
              congr 1
              ring
            _ <= |ybar i| + |ybar i - yhat i| := abs_sub _ _
        exact mul_le_mul_of_nonneg_left hi (abs_nonneg _)
      _ = (∑ i : Fin m, |A i j| * |ybar i|) +
          ∑ i : Fin m, |A i j| * |ybar i - yhat i| := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hmajor : vecNorm2 what <= vecNorm2 (fun j => wbar j + wd j) := by
    apply vecNorm2_le_of_abs_le
    intro j
    simpa [abs_of_nonneg (add_nonneg (hwbar j) (hwd j))] using hpoint j
  have hwdNorm : vecNorm2 wd <=
      frobNorm A * vecNorm2 (fun i => ybar i - yhat i) := by
    calc
      vecNorm2 wd <= frobNormRect (finiteTranspose (absMatrixRect A)) *
          vecNorm2 (fun i => |ybar i - yhat i|) := by
        simpa [wd, rectTransposeMulVec] using
          vecNorm2_rectMatMulVec_le_frobNormRect_mul
            (finiteTranspose (absMatrixRect A))
            (fun i => |ybar i - yhat i|)
      _ = frobNorm A * vecNorm2 (fun i => ybar i - yhat i) := by
        rw [frobNormRect_finiteTranspose]
        rw [show frobNormRect (absMatrixRect A) = frobNormRect A by
          simpa [absMatrixRect] using frobNormRect_abs A]
        rw [frobNormRect_eq_frobNormFn]
        rw [show vecNorm2 (fun i => |ybar i - yhat i|) =
            vecNorm2 (fun i => ybar i - yhat i) by
          simpa using vecNorm2_abs (fun i => ybar i - yhat i)]
  calc
    vecNorm2
        (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)) =
        vecNorm2 what := by rfl
    _ <= vecNorm2 (fun j => wbar j + wd j) := hmajor
    _ <= vecNorm2 wbar + vecNorm2 wd := vecNorm2_add_le wbar wd
    _ <= vecNorm2 wbar +
        frobNorm A * vecNorm2 (fun i => ybar i - yhat i) :=
      add_le_add le_rfl hwdNorm
    _ = vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|)) +
        frobNorm A * vecNorm2 (fun i => ybar i - yhat i) := by rfl

/-- Source-shaped leading/quadratic split for the final rounded `Aᵀ yhat`
formation.  The nearby dual action supplies the leading term; applying the
formation to `yhat-ybar` is quadratic. -/
theorem higham21_sne_formation_error_le_source_plus_quadratic
    {m n : Nat}
    (theta rho gamma Kd q : Real)
    (htheta : 0 <= theta)
    (_hrho : 0 <= rho) (hrho_theta : rho <= theta) (hrho_lt : rho < 1)
    (hgamma : 0 <= gamma) (hgamma_theta : gamma <= theta)
    (hKd : 0 <= Kd) (hq : 0 <= q)
    (A : Fin m -> Fin n -> Real)
    (ybar yhat : Fin m -> Real) (g : Fin n -> Real)
    (hFormation :
      vecNorm2 g <= gamma *
        vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)))
    (hbar :
      vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|)) <=
        q / (1 - rho))
    (hd : vecNorm2 (fun i => ybar i - yhat i) <= theta * Kd) :
    vecNorm2 g <=
      theta * q + theta ^ 2 * (q / (1 - rho) + frobNorm A * Kd) := by
  have hden : 0 < 1 - rho := sub_pos.mpr hrho_lt
  have hqdiv : 0 <= q / (1 - rho) := div_nonneg hq hden.le
  have hA : 0 <= frobNorm A := frobNorm_nonneg A
  have hsource := higham21_sne_source_abs_action_change A ybar yhat
  have hhat :
      vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)) <=
        q / (1 - rho) + frobNorm A * (theta * Kd) := by
    exact hsource.trans (add_le_add hbar
      (mul_le_mul_of_nonneg_left hd hA))
  have hgammaBound : vecNorm2 g <=
      theta * (q / (1 - rho) + frobNorm A * (theta * Kd)) := by
    calc
      vecNorm2 g <= gamma *
          vecNorm2
            (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)) :=
        hFormation
      _ <= gamma *
          (q / (1 - rho) + frobNorm A * (theta * Kd)) :=
        mul_le_mul_of_nonneg_left hhat hgamma
      _ <= theta *
          (q / (1 - rho) + frobNorm A * (theta * Kd)) :=
        mul_le_mul_of_nonneg_right hgamma_theta
          (add_nonneg hqdiv (mul_nonneg hA (mul_nonneg htheta hKd)))
  have hsplit : theta * (q / (1 - rho)) <=
      theta * q + theta ^ 2 * (q / (1 - rho)) := by
    have hidentity : q / (1 - rho) = q + rho * (q / (1 - rho)) := by
      field_simp [ne_of_gt hden]
      ring
    calc
      theta * (q / (1 - rho)) =
          theta * (q + rho * (q / (1 - rho))) :=
        congrArg (fun z => theta * z) hidentity
      _ =
          theta * q + theta * rho * (q / (1 - rho)) := by ring
      _ <= theta * q + theta * theta * (q / (1 - rho)) := by
        gcongr
      _ = theta * q + theta ^ 2 * (q / (1 - rho)) := by ring
  calc
    vecNorm2 g <=
        theta * (q / (1 - rho) + frobNorm A * (theta * Kd)) := hgammaBound
    _ = theta * (q / (1 - rho)) +
        theta ^ 2 * (frobNorm A * Kd) := by ring
    _ <= (theta * q + theta ^ 2 * (q / (1 - rho))) +
        theta ^ 2 * (frobNorm A * Kd) := add_le_add hsplit le_rfl
    _ = theta * q + theta ^ 2 * (q / (1 - rho) + frobNorm A * Kd) := by
      ring




































































































































































































































































































end NumStability
