-- Algorithms/Sylvester/Higham16PsiSigmaMin.lean
--
-- Source-facing sigma-min wrappers for Higham, Accuracy and Stability of
-- Numerical Algorithms, 2nd ed., Chapter 16.3, equations (16.23)-(16.24).

import NumStability.Analysis.InverseOpNorm2

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

/-- Higham, 2nd ed., §16.3, eq. (16.23) (p. 313):
    source-numbered alias for the raw sigma-min first-order Sylvester
    perturbation bound. -/
theorem H16_eq16_23_sylvester_first_order_bound_of_sigmaMin (n : ℕ)
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
    sylvester_first_order_bound_of_sigmaMin n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma
      halpha hbeta hgamma hsigma hX hSigmaMin hLin

/-- Higham, 2nd ed., §16.3, eqs. (16.23)-(16.24) (p. 313):
    sigma-min structured first-order perturbation bound. If the Sylvester
    operator satisfies `sigma * ||Y||_F <= ||T(Y)||_F` for all `Y`, then the
    printed relative bound follows with
    `sylvesterPsi_of_inverseOpBound ... (1 / sigma)`.

    Scope: this is an exact-arithmetic theorem from a supplied singular-value
    lower-bound certificate for the Sylvester operator. The remaining unproved
    glue, documented in `InverseOpNorm2.lean`, is the automatic construction of
    this hypothesis from the concrete vec/Kronecker coefficient via a
    Frobenius/vec isometry. -/
theorem H16_eq16_24_structured_condition_of_sigmaMin (n : ℕ)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n → Fin n → ℝ)
    (alpha beta gamma sigma eps : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 ≤ eps)
    (hX : 0 < frobNorm X)
    (hSigmaMin : ∀ Y : Fin n → Fin n → ℝ,
      sigma * frobNorm Y ≤ frobNorm (sylvesterOp n A B Y))
    (hDeltaA : frobNorm DeltaA ≤ eps * alpha)
    (hDeltaB : frobNorm DeltaB ≤ eps * beta)
    (hDeltaC : frobNorm DeltaC ≤ eps * gamma)
    (hLin : ∀ i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X ≤
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  have hPsi :=
    sylvesterPsi_of_sigmaMin_isPsiFirstOrderBound n
      A B X alpha beta gamma sigma halpha hbeta hgamma hsigma hX hSigmaMin
  have hPsinn : 0 ≤ sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) := by
    unfold sylvesterPsi_of_inverseOpBound
    have hMnn : (0 : ℝ) ≤ 1 / sigma := by positivity
    have hnum : 0 ≤ (alpha + beta) * frobNorm X + gamma := by
      have hXnn : 0 ≤ frobNorm X := le_of_lt hX
      nlinarith [le_of_lt halpha, le_of_lt hbeta, le_of_lt hgamma, hXnn]
    positivity
  exact sylvester_relative_first_order_bound_of_psi n
    A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma
    (sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma)) eps
    hPsi hX hPsinn halpha hbeta hgamma heps hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., §16.3, eqs. (16.23)-(16.24) (p. 313):
    relative first-order Sylvester perturbation bound from a positive
    sigma-min lower bound for the Sylvester operator. -/
theorem sylvester_relative_first_order_bound_of_sigmaMin (n : ℕ)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n → Fin n → ℝ)
    (alpha beta gamma sigma eps : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 ≤ eps)
    (hX : 0 < frobNorm X)
    (hSigmaMin : ∀ Y : Fin n → Fin n → ℝ,
      sigma * frobNorm Y ≤ frobNorm (sylvesterOp n A B Y))
    (hDeltaA : frobNorm DeltaA ≤ eps * alpha)
    (hDeltaB : frobNorm DeltaB ≤ eps * beta)
    (hDeltaC : frobNorm DeltaC ≤ eps * gamma)
    (hLin : ∀ i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X ≤
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  exact
    H16_eq16_24_structured_condition_of_sigmaMin n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      halpha hbeta hgamma hsigma heps hX hSigmaMin
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., §16.3, eq. (16.24) (p. 313):
    source-numbered alias for the relative sigma-min first-order Sylvester
    perturbation endpoint. -/
theorem H16_eq16_24_sylvester_relative_first_order_bound_of_sigmaMin (n : ℕ)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n → Fin n → ℝ)
    (alpha beta gamma sigma eps : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 ≤ eps)
    (hX : 0 < frobNorm X)
    (hSigmaMin : ∀ Y : Fin n → Fin n → ℝ,
      sigma * frobNorm Y ≤ frobNorm (sylvesterOp n A B Y))
    (hDeltaA : frobNorm DeltaA ≤ eps * alpha)
    (hDeltaB : frobNorm DeltaB ≤ eps * beta)
    (hDeltaC : frobNorm DeltaC ≤ eps * gamma)
    (hLin : ∀ i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X ≤
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  exact
    sylvester_relative_first_order_bound_of_sigmaMin n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      halpha hbeta hgamma hsigma heps hX hSigmaMin
      hDeltaA hDeltaB hDeltaC hLin

end NumStability
