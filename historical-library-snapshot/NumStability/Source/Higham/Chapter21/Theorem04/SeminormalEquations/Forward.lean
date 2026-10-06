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
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.TriangularSolves.UnderdeterminedSolve
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Normwise
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter19.Core
import NumStability.Source.Higham.Chapter20.Theorem03.QRSolve
import NumStability.Source.Higham.Chapter21.Equation11.UnderdeterminedSolve

/-!
# Source.Higham.Chapter21.Theorem04.SeminormalEquations.Forward

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Concrete forward-error closure for the seminormal-equations solve.



namespace NumStability

open scoped BigOperators















































































/-- Concrete source-facing SNE forward theorem.  The witness `DeltaC`, the
perturbed equation, and the forward inequality all concern the actual
`fl_forwardSub`/`fl_backSub` output, rather than an uninstantiated vector.

Besides retaining the exact `DeltaC`-dependent componentwise inequality, the
theorem substitutes its proved backward-error bound and aggregates the result
in the Euclidean norm. -/
theorem higham21_sne_computed_forward_error
    (fp : FPModel) (m : ℕ)
    (AAT AAT_inv R_hat : Fin m → Fin m → ℝ)
    (b y : Fin m → ℝ)
    (hInv : IsInverse m AAT AAT_inv)
    (hExact : ∀ i, matMulVec m AAT y i = b i)
    (hR_diag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hChol : CholeskyBackwardError m AAT R_hat (gamma fp (m + 1)))
    (hm1 : gammaValid fp (m + 1)) :
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
        vecNorm2 (higham21SNEForwardEnvelope fp m AAT_inv R_hat y_hat) := by
  dsimp only
  obtain ⟨DeltaC, hDeltaC, hPerturbed⟩ :
      ∃ DeltaC : Fin m → Fin m → ℝ,
        (∀ i j : Fin m,
          |DeltaC i j| ≤ higham21SNERHatGramEnvelope fp m R_hat i j) ∧
        (∀ i : Fin m,
          ∑ j : Fin m, (AAT i j + DeltaC i j) *
            higham21SNEComputedNormalSolution fp m R_hat b j = b i) := by
    simpa only [higham21SNEComputedNormalSolution,
      higham21SNERHatGramEnvelope, Higham21SNEBackwardCoefficient] using
      (sne_backward_error fp m AAT R_hat b hR_diag hChol hm1)
  have hForward : ∀ i : Fin m,
      |higham21SNEComputedNormalSolution fp m R_hat b i - y i| ≤
        ∑ j : Fin m, |AAT_inv i j| *
          ∑ k : Fin m, |DeltaC j k| *
            |higham21SNEComputedNormalSolution fp m R_hat b k| := by
    exact
      higham21_sne_gram_forward_error_matches_q_method
        m AAT AAT_inv hInv b y
          (higham21SNEComputedNormalSolution fp m R_hat b)
          hExact DeltaC hPerturbed
  have hEnvelope : ∀ i : Fin m,
      |higham21SNEComputedNormalSolution fp m R_hat b i - y i| ≤
        higham21SNEForwardEnvelope fp m AAT_inv R_hat
          (higham21SNEComputedNormalSolution fp m R_hat b) i :=
    higham21_sne_forward_error_le_computed_envelope
      fp m AAT_inv R_hat DeltaC y
        (higham21SNEComputedNormalSolution fp m R_hat b)
        hDeltaC hForward
  have hNorm :
      vecNorm2 (fun i : Fin m =>
        higham21SNEComputedNormalSolution fp m R_hat b i - y i) ≤
        vecNorm2
          (higham21SNEForwardEnvelope fp m AAT_inv R_hat
            (higham21SNEComputedNormalSolution fp m R_hat b)) :=
    higham21_sne_vecNorm2_forward_error_of_componentwise
      y (higham21SNEComputedNormalSolution fp m R_hat b)
        (higham21SNEForwardEnvelope fp m AAT_inv R_hat
          (higham21SNEComputedNormalSolution fp m R_hat b)) hEnvelope
  exact ⟨DeltaC, hDeltaC, hPerturbed, hForward, hEnvelope, hNorm⟩






















































end NumStability
