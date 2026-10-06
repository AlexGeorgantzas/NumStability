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
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.ForwardError.Forward
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Normwise
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter19.Core
import NumStability.Source.Higham.Chapter20.Theorem03.QRSolve
import NumStability.Source.Higham.Chapter21.Theorem04.SeminormalEquations.Forward

/-!
# Source.Higham.Chapter21.Equation11.Forward

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Concrete forward-error closure for the seminormal-equations solve.



namespace NumStability

open scoped BigOperators























































































































































/-- Equation (21.11), SNE side, for the actually computed normal-equation
vector.  For a nonzero exact solution this packages the concrete witness and
both the exact componentwise and relative Euclidean forward bounds in one
statement.

The coefficient is the finite envelope justified by the currently available
SNE backward-error theorem.  Reducing it to the printed `cond2(A)` expression
would additionally require a proved source-level relation between `R_hat` and
the rectangular input matrix; that relation is not an assumption hidden here. -/
theorem higham21_eq21_11_sne_computed_relative_forward_error
    (fp : FPModel) (m : ℕ)
    (AAT AAT_inv R_hat : Fin m → Fin m → ℝ)
    (b y : Fin m → ℝ)
    (hInv : IsInverse m AAT AAT_inv)
    (hExact : ∀ i, matMulVec m AAT y i = b i)
    (hR_diag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hChol : CholeskyBackwardError m AAT R_hat (gamma fp (m + 1)))
    (hm1 : gammaValid fp (m + 1))
    (hy : 0 < vecNorm2 y) :
    let y_hat := higham21SNEComputedNormalSolution fp m R_hat b
    ∃ DeltaC : Fin m → Fin m → ℝ,
      (∀ i j : Fin m,
        |DeltaC i j| ≤ higham21SNERHatGramEnvelope fp m R_hat i j) ∧
      (∀ i : Fin m,
        ∑ j : Fin m, (AAT i j + DeltaC i j) * y_hat j = b i) ∧
      (∀ i : Fin m,
        |y_hat i - y i| ≤
          ∑ j : Fin m, |AAT_inv i j| *
            ∑ k : Fin m, |DeltaC j k| * |y_hat k|) ∧
      (∀ i : Fin m,
        |y_hat i - y i| ≤
          higham21SNEForwardEnvelope fp m AAT_inv R_hat y_hat i) ∧
      vecNorm2 (fun i : Fin m => y_hat i - y i) ≤
        vecNorm2 (higham21SNEForwardEnvelope fp m AAT_inv R_hat y_hat) ∧
      vecNorm2 (fun i : Fin m => y_hat i - y i) / vecNorm2 y ≤
        Higham21SNEForwardCoefficient fp m AAT_inv R_hat y y_hat := by
  dsimp only
  have hCore :=
    higham21_sne_computed_forward_error
      fp m AAT AAT_inv R_hat b y hInv hExact hR_diag hChol hm1
  dsimp only at hCore
  obtain ⟨DeltaC, hDeltaC, hPerturbed, hForward, hEnvelope, hNorm⟩ := hCore
  have hRelative :
      vecNorm2 (fun i : Fin m =>
        higham21SNEComputedNormalSolution fp m R_hat b i - y i) /
          vecNorm2 y ≤
        Higham21SNEForwardCoefficient fp m AAT_inv R_hat y
          (higham21SNEComputedNormalSolution fp m R_hat b) := by
    simpa only [Higham21SNEForwardCoefficient] using
      (div_le_div_of_nonneg_right hNorm (le_of_lt hy))
  exact
    ⟨DeltaC, hDeltaC, hPerturbed, hForward, hEnvelope, hNorm, hRelative⟩

end NumStability
