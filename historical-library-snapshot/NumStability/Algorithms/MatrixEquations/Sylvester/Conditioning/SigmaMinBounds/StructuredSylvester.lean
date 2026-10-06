import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.FirstOrder
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.SingularValue
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.StructuredSylvester
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Basic
import NumStability.Analysis.MatrixAlgebra

/-!
# Algorithms.MatrixEquations.Sylvester.Conditioning.SigmaMinBounds.StructuredSylvester

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/Sylvester/Higham16PsiSigmaMin.lean
--
-- Source-facing sigma-min wrappers for Higham, Accuracy and Stability of
-- Numerical Algorithms, 2nd ed., Chapter 16.3, equations (16.23)-(16.24).



namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-- Higham, 2nd ed., §16.3, eq (16.24) (p. 313):
    a positive singular-value lower bound for the Sylvester operator
    instantiates the structured `Psi` predicate with the inverse-operator
    constant `M = 1 / sigma`.

    This is the sigma-min version of the safe `Psi` wrapper. It uses
    `sylvesterInverseOpBound_of_sigmaMin`, so the supplied hypothesis is the
    operator lower bound itself. -/
theorem sylvesterPsi_of_sigmaMin_isPsiFirstOrderBound (n : ℕ)
    (A B X : Fin n → Fin n → ℝ) (alpha beta gamma sigma : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (hX : 0 < frobNorm X)
    (hSigmaMin : ∀ Y : Fin n → Fin n → ℝ,
      sigma * frobNorm Y ≤ frobNorm (sylvesterOp n A B Y)) :
    SylvesterPsiFirstOrderBound n A B X alpha beta gamma
      (sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma)) := by
  have hInv := sylvesterInverseOpBound_of_sigmaMin n A B sigma hsigma hSigmaMin
  have hMnn : (0 : ℝ) ≤ 1 / sigma := by positivity
  exact sylvesterPsi_of_inverseOpBound_isPsiFirstOrderBound n
    A B X alpha beta gamma (1 / sigma)
    halpha hbeta hgamma hMnn hX hInv

/-- Higham, 2nd ed., §16.3, eq (16.24) (p. 313):
    source-facing sigma-min first-order Sylvester bound before the
    `sqrt 3 * eps` relative wrapper. This simply applies the structured `Psi`
    certificate instantiated by `sylvesterPsi_of_sigmaMin_isPsiFirstOrderBound`
    to a supplied linearized perturbation equation. -/
theorem sylvester_first_order_bound_of_sigmaMin (n : ℕ)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n → Fin n → ℝ)
    (alpha beta gamma sigma : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (hX : 0 < frobNorm X)
    (hSigmaMin : ∀ Y : Fin n → Fin n → ℝ,
      sigma * frobNorm Y ≤ frobNorm (sylvesterOp n A B Y))
    (hLin : ∀ i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX ≤
      sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) *
        frobNorm X *
        sylvesterScaledPerturbationTripleNorm n DeltaA DeltaB DeltaC
          alpha beta gamma := by
  exact
    sylvesterPsi_of_sigmaMin_isPsiFirstOrderBound n
      A B X alpha beta gamma sigma halpha hbeta hgamma hsigma hX hSigmaMin
      DeltaA DeltaB DeltaC DeltaX hLin























































































































end NumStability
