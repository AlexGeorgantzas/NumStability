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
# Algorithms.LinearSystems.Underdetermined.QR.Givens.BackwardError.Core

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Theorem 21.4 through the concrete staged Givens QR factorization of A^T.



namespace NumStability












































































/-- Exact orthogonal witness attached to the concrete staged Givens QR
    backward-error certificate for `A^T`.

    This is a proof-selected exact factor, not a rounded formed-`Q` matrix. -/
noncomputable def higham21GivensQMethodQ
    (fp : FPModel) (m k : Nat)
    (A : Fin m -> Fin (m + k) -> Real)
    (hvalidGivens : gammaValid fp 8) :
    Fin (m + k) -> Fin (m + k) -> Real :=
  Classical.choose
    (fl_givensQRStageFold_sequence_columnFrob_backward_error_uniform
      fp (m + k) m (finiteTranspose A)
      (givensQRStageCount (m + k) m) hvalidGivens)

/-- Concrete upper-trapezoidal output of staged Givens QR applied to `A^T`. -/
noncomputable def higham21GivensQMethodRTall
    (fp : FPModel) (m k : Nat)
    (A : Fin m -> Fin (m + k) -> Real) :
    Fin (m + k) -> Fin m -> Real :=
  fl_givensQRStageFold fp (m + k) m
    (givensQRStageCount (m + k) m) (finiteTranspose A)

/-- Q-method vector obtained from the computed staged Givens `R_hat`, the
    rounded triangular solve, and the exact orthogonal certificate witness.

    A future fully rounded Givens endpoint should replace the final exact
    matrix-vector action by a stored-rotation application and prove its own
    action-error certificate. -/
noncomputable def higham21GivensQMethodOutput
    (fp : FPModel) (m k : Nat)
    (A : Fin m -> Fin (m + k) -> Real)
    (b : Fin m -> Real)
    (hvalidGivens : gammaValid fp 8) :
    Fin (m + k) -> Real :=
  let R_top : Fin m -> Fin m -> Real := fun i j =>
    higham21GivensQMethodRTall fp m k A (Fin.castAdd k i) j
  matMulVec (m + k)
    (higham21GivensQMethodQ fp m k A hvalidGivens)
    (Fin.append
      (fl_forwardSub fp m (matTranspose R_top) b)
      (0 : Fin k -> Real))
































































































end NumStability
