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
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Specifications.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.Perturbation.Componentwise.UnderdeterminedSolve
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
# Algorithms.LinearSystems.Underdetermined.Perturbation.Componentwise.Radius

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- A derived fixed-radius neighborhood for Theorem 21.1 and equation (21.6).



namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius









































































/-- A pointwise envelope induced by row 2-norm bounds. -/
def higham21PerturbationEntryEnvelopeOfRow {m n : Nat}
    (r : Fin m -> Real) : Fin m -> Fin n -> Real :=
  fun i _ => r i



























































































































/-- Monotonicity of the componentwise Gram budget in its scalar quadratic
    radius. -/
theorem higham21_undetGramPerturbationComponentBudget_mono {m n : Nat}
    (A E : Fin m -> Fin n -> Real) {r s : Real}
    (hE : forall i j, 0 <= E i j) (hrs : r <= s) :
    forall i j,
      undetGramPerturbationComponentBudget A E r i j <=
        undetGramPerturbationComponentBudget A E s i j := by
  intro i j
  unfold undetGramPerturbationComponentBudget
  apply Finset.sum_le_sum
  intro k _
  have hquad : r * (E i k * E j k) <= s * (E i k * E j k) :=
    mul_le_mul_of_nonneg_right hrs (mul_nonneg (hE i k) (hE j k))
  exact add_le_add le_rfl (by simpa [mul_assoc] using hquad)






































































































































































































































































































theorem higham21PerturbationEntryEnvelopeOfRow_nonneg {m n : Nat}
    (r : Fin m -> Real) (hr : forall i, 0 <= r i) :
    forall i j, 0 <= higham21PerturbationEntryEnvelopeOfRow
      (n := n) r i j := by
  intro i j
  exact hr i

/-- A row 2-norm envelope induces the pointwise envelope used in the Gram
    budget. -/
theorem higham21_abs_entry_le_entryEnvelopeOfRow {m n : Nat}
    (D : Fin m -> Fin n -> Real) (r : Fin m -> Real)
    (hrow : forall i, rectRowNorm2 D i <= r i) :
    forall i j, abs (D i j) <=
      higham21PerturbationEntryEnvelopeOfRow r i j := by
  intro i j
  calc
    abs (D i j) <= rectRowNorm2 D i := by
      simpa [rectRowNorm2] using
        (abs_coord_le_vecNorm2 (fun k : Fin n => D i k) j)
    _ <= r i := hrow i
    _ = higham21PerturbationEntryEnvelopeOfRow r i j := rfl






































































































































































































































































































































































end NumStability
