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
# Algorithms.LinearSystems.Underdetermined.SeminormalEquations.ForwardError.Forward

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Concrete forward-error closure for the seminormal-equations solve.



namespace NumStability

open scoped BigOperators

/-- The actual normal-equation vector returned by the two rounded triangular
solves in the SNE method. -/
noncomputable def higham21SNEComputedNormalSolution
    (fp : FPModel) (m : ℕ) (R_hat : Fin m → Fin m → ℝ)
    (b : Fin m → ℝ) : Fin m → ℝ :=
  fl_backSub fp m R_hat
    (fl_forwardSub fp m (fun i j : Fin m => R_hat j i) b)

/-- The finite coefficient in the componentwise Cholesky/triangular-solve
backward error used by the SNE method. -/
noncomputable def Higham21SNEBackwardCoefficient
    (fp : FPModel) (m : ℕ) : ℝ :=
  gamma fp (m + 1) + 2 * gamma fp m + gamma fp m ^ 2

/-- The entrywise `|R_hat^T| |R_hat|` backward-error envelope, including the
coefficient from the two rounded triangular solves.  Unfolding this definition
gives exactly the bound returned by `sne_backward_error`. -/
noncomputable def higham21SNERHatGramEnvelope
    (fp : FPModel) (m : ℕ) (R_hat : Fin m → Fin m → ℝ)
    (i j : Fin m) : ℝ :=
  Higham21SNEBackwardCoefficient fp m *
    ∑ k : Fin m, |R_hat k i| * |R_hat k j|

/-- The fully instantiated finite componentwise forward-error envelope for the
computed SNE normal-equation vector. -/
noncomputable def higham21SNEForwardEnvelope
    (fp : FPModel) (m : ℕ)
    (AAT_inv R_hat : Fin m → Fin m → ℝ)
    (y_hat : Fin m → ℝ) : Fin m → ℝ :=
  fun i =>
    ∑ j : Fin m, |AAT_inv i j| *
      ∑ k : Fin m,
        higham21SNERHatGramEnvelope fp m R_hat j k * |y_hat k|

/-- A named, exact finite coefficient for the relative Euclidean SNE forward
bound, expressed entirely by finite sums and Euclidean norms. -/
noncomputable def Higham21SNEForwardCoefficient
    (fp : FPModel) (m : ℕ)
    (AAT_inv R_hat : Fin m → Fin m → ℝ)
    (y y_hat : Fin m → ℝ) : ℝ :=
  vecNorm2 (higham21SNEForwardEnvelope fp m AAT_inv R_hat y_hat) /
    vecNorm2 y

/-- Aggregate a componentwise forward-error envelope into a Euclidean norm
bound. -/
theorem higham21_sne_vecNorm2_forward_error_of_componentwise
    {m : ℕ} (y y_hat envelope : Fin m → ℝ)
    (hcomponentwise : ∀ i : Fin m, |y_hat i - y i| ≤ envelope i) :
    vecNorm2 (fun i : Fin m => y_hat i - y i) ≤ vecNorm2 envelope :=
  vecNorm2_le_of_abs_le
    (fun i : Fin m => y_hat i - y i) envelope hcomponentwise

/-- Substitute the concrete SNE `DeltaC` estimate into the generic
componentwise forward perturbation bound. -/
theorem higham21_sne_forward_error_le_computed_envelope
    (fp : FPModel) (m : ℕ)
    (AAT_inv R_hat DeltaC : Fin m → Fin m → ℝ)
    (y y_hat : Fin m → ℝ)
    (hDeltaC : ∀ i j : Fin m,
      |DeltaC i j| ≤ higham21SNERHatGramEnvelope fp m R_hat i j)
    (hforward : ∀ i : Fin m,
      |y_hat i - y i| ≤
        ∑ j : Fin m, |AAT_inv i j| *
          ∑ k : Fin m, |DeltaC j k| * |y_hat k|) :
    ∀ i : Fin m,
      |y_hat i - y i| ≤
        higham21SNEForwardEnvelope fp m AAT_inv R_hat y_hat i := by
  intro i
  refine (hforward i).trans ?_
  simp only [higham21SNEForwardEnvelope]
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_right (hDeltaC j k) (abs_nonneg (y_hat k))
  · exact abs_nonneg (AAT_inv i j)






























































































































end NumStability
