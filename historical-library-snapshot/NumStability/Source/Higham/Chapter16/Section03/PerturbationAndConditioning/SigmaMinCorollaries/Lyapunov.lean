import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.FirstOrder
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.Separation
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.SigmaMinBounds.Lyapunov
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.StructuredLyapunov
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Basic
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Lyapunov
import NumStability.Analysis.MatrixAlgebra

/-!
# Source.Higham.Chapter16.Section03.PerturbationAndConditioning.SigmaMinCorollaries.Lyapunov

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/Sylvester/Higham16LyapunovSigmaMin.lean
--
-- Source-facing sigma-min wrappers for Higham, Accuracy and Stability of
-- Numerical Algorithms, 2nd ed., Chapter 16.3, equation (16.27).



namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius













































/-- Higham, 2nd ed., Chapter 16.3, equation (16.26): source-numbered
    alias for the Lyapunov sigma-min route to `SepLowerBound(A,-A^T)`. -/
theorem H16_eq16_26_SepLowerBound_lyapunov_of_sigmaMin (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y)) :
    SepLowerBound n A (fun i j => -matTranspose A i j) sigma := by
  exact SepLowerBound_lyapunov_of_sigmaMin n A sigma hsigma hSigmaMin














































































/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for the supplied Lyapunov operator sigma-min
    exact-kernel theorem. -/
alias H16_eq16_27_lyapunovOp_eq_zero_iff_of_sigmaMin :=
  lyapunovOp_eq_zero_iff_of_sigmaMin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for exact Lyapunov uniqueness from a supplied
    operator sigma-min certificate. -/
alias H16_eq16_27_lyapunov_unique_solution_of_sigmaMin :=
  lyapunov_unique_solution_of_sigmaMin

/-- Higham, 2nd ed., Chapter 16.2.1 and 16.3, equations (16.26)-(16.27):
    source-numbered alias for residual-zero exact Lyapunov uniqueness from a
    supplied operator sigma-min certificate. -/
alias H16_eq16_27_lyapunov_solution_eq_of_residual_norm_zero_sigmaMin :=
  lyapunov_solution_eq_of_residual_norm_zero_sigmaMin




















/-- Higham, 2nd ed., Chapter 16.3, equation (16.26): source-numbered
    alias for the Lyapunov sigma-min lower bound on the exact `sep(A,-A^T)`
    infimum model. -/
theorem H16_eq16_26_sylvesterSepInf_lyapunov_ge_of_sigmaMin (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hn : 0 < n) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y)) :
    sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j) := by
  exact sylvesterSepInf_lyapunov_ge_of_sigmaMin n A sigma
    hn hsigma hSigmaMin




















/-- Higham, 2nd ed., Chapter 16.3, equation (16.26): source-numbered
    alias for strict positivity of the Lyapunov exact `sep(A,-A^T)` infimum
    from a supplied positive Lyapunov operator sigma-min certificate. -/
theorem H16_eq16_26_sylvesterSepInf_lyapunov_pos_of_sigmaMin (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hn : 0 < n) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y)) :
    0 < sylvesterSepInf n A (fun i j => -matTranspose A i j) := by
  exact sylvesterSepInf_lyapunov_pos_of_sigmaMin n A sigma
    hn hsigma hSigmaMin

/-- Higham, 2nd ed., Chapter 16.3-16.4, equations (16.26)-(16.27):
    source-numbered alias for strict positivity of `sep(A, -A^T)` from a
    supplied positive Lyapunov operator sigma-min certificate. -/
theorem H16_eq16_27_sylvesterSepInf_lyapunov_pos_of_sigmaMin (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hn : 0 < n) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y)) :
    0 < sylvesterSepInf n A (fun i j => -matTranspose A i j) := by
  exact
    sylvesterSepInf_lyapunov_pos_of_sigmaMin n A sigma
      hn hsigma hSigmaMin












































































/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the supplied sigma-min Lyapunov a posteriori
    residual-error bound. The underlying endpoint already handles zero error
    internally. -/
alias H16_eq16_28_lyapunov_aposteriori_bound_of_sigmaMin :=
  lyapunov_aposteriori_bound_of_sigmaMin

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the relative supplied sigma-min Lyapunov
    a posteriori residual-error bound. The absolute endpoint already handles
    zero error internally; the relative form still assumes `0 < ||X||_F`. -/
alias H16_eq16_28_lyapunov_relative_aposteriori_bound_of_sigmaMin :=
  lyapunov_relative_aposteriori_bound_of_sigmaMin






















/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the total supplied sigma-min Lyapunov
    a posteriori residual-error bound. -/
theorem H16_eq16_28_lyapunov_aposteriori_bound_of_sigmaMin_total (n : Nat)
    (A C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (hExact : forall i j, lyapunovOp n A X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (lyapunovResidual n A C Xhat) := by
  exact
    lyapunov_aposteriori_bound_of_sigmaMin_total n A C X Xhat sigma
      hsigma hSigmaMin hExact

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the total relative supplied sigma-min Lyapunov
    a posteriori residual-error bound. -/
theorem H16_eq16_28_lyapunov_relative_aposteriori_bound_of_sigmaMin_total
    (n : Nat)
    (A C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (hExact : forall i j, lyapunovOp n A X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (lyapunovResidual n A C Xhat)) /
        frobNorm X := by
  exact
    lyapunov_relative_aposteriori_bound_of_sigmaMin_total n
      A C X Xhat sigma hsigma hSigmaMin hExact hX_pos


























































/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-numbered alias for the total supplied sigma-min Lyapunov
    perturbation bound. -/
theorem H16_eq16_27_lyapunov_perturbation_bound_of_sigmaMin_total (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j) :
    frobNorm DeltaX <=
      (1 / sigma) * (2 * alpha * frobNorm X + gamma) * eps := by
  exact
    lyapunov_perturbation_bound_of_sigmaMin_total n
      A X DeltaA DeltaC DeltaX sigma hsigma hSigmaMin
      alpha gamma eps halpha hgamma heps hDeltaA hDeltaC hLin







































































/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-numbered alias for the total relative supplied sigma-min Lyapunov
    perturbation bound. -/
theorem H16_eq16_27_lyapunov_relative_perturbation_of_sigmaMin_total (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real) (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm DeltaX / frobNorm X <=
      condSylvester n A (fun i j => -matTranspose A i j) X
        alpha alpha gamma sigma * eps := by
  exact
    lyapunov_relative_perturbation_of_sigmaMin_total n
      A X DeltaA DeltaC DeltaX sigma hsigma hSigmaMin
      alpha gamma eps halpha hgamma heps hDeltaA hDeltaC hLin hX_pos




























/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-numbered alias for the supplied sigma-min first-order Lyapunov
    perturbation bound. -/
theorem H16_eq16_27_lyapunov_first_order_bound_of_sigmaMin (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma)
    (hX : 0 < frobNorm X)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX <=
      lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) *
        frobNorm X *
        lyapunovScaledPerturbationPairNorm n DeltaA DeltaC alpha gamma := by
  exact
    lyapunov_first_order_bound_of_sigmaMin n
      A X DeltaA DeltaC DeltaX alpha gamma sigma
      halpha hgamma hsigma hX hSigmaMin hLin

/-- Higham, 2nd ed., §16.3, eq (16.27) (p. 317):
    sigma-min Lyapunov first-order perturbation bound. If the Lyapunov operator
    satisfies `sigma * ||Y||_F <= ||L(Y)||_F` for all `Y`, then the printed
    relative bound follows with
    `lyapunovCond_of_inverseOpBound ... (1 / sigma)`.

    Scope: this is an exact-arithmetic theorem from a supplied singular-value
    lower-bound certificate for `L`. The remaining unproved glue, documented in
    `InverseOpNorm2.lean`, is the automatic construction of this hypothesis from
    the concrete vec/Kronecker coefficient via a Frobenius/vec isometry. -/
theorem H16_eq16_27_lyapunov_condition_of_sigmaMin (n : ℕ)
    (A X DeltaA DeltaC DeltaX : Fin n → Fin n → ℝ)
    (alpha gamma sigma eps : ℝ)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 ≤ eps)
    (hX : 0 < frobNorm X)
    (hSigmaMin : ∀ Y : Fin n → Fin n → ℝ,
      sigma * frobNorm Y ≤ frobNorm (lyapunovOp n A Y))
    (hDeltaA : frobNorm DeltaA ≤ eps * alpha)
    (hDeltaC : frobNorm DeltaC ≤ eps * gamma)
    (hLin : ∀ i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X ≤
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  have hCond :=
    lyapunovCond_of_sigmaMin_isLyapunovConditionFirstOrderBound n
      A X alpha gamma sigma halpha hgamma hsigma hX hSigmaMin
  have hPsinn : 0 ≤ lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) := by
    unfold lyapunovCond_of_inverseOpBound
    have hMnn : (0 : ℝ) ≤ 1 / sigma := by positivity
    have hnum : 0 ≤ 2 * alpha * frobNorm X + gamma := by
      have hXnn : 0 ≤ frobNorm X := le_of_lt hX
      nlinarith [le_of_lt halpha, le_of_lt hgamma, hXnn]
    positivity
  exact lyapunov_relative_first_order_bound_of_condition n
    A X DeltaA DeltaC DeltaX alpha gamma
    (lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma)) eps
    hCond hX hPsinn halpha hgamma heps hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    relative Lyapunov first-order perturbation bound from a supplied positive
    singular-value lower bound on the Lyapunov operator. -/
theorem lyapunov_relative_first_order_bound_of_sigmaMin (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma eps : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  exact
    H16_eq16_27_lyapunov_condition_of_sigmaMin n
      A X DeltaA DeltaC DeltaX alpha gamma sigma eps
      halpha hgamma hsigma heps hX hSigmaMin
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-numbered alias for the relative supplied sigma-min first-order
    Lyapunov perturbation bound. -/
theorem H16_eq16_27_lyapunov_relative_first_order_bound_of_sigmaMin (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma eps : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  exact
    lyapunov_relative_first_order_bound_of_sigmaMin n
      A X DeltaA DeltaC DeltaX alpha gamma sigma eps
      halpha hgamma hsigma heps hX hSigmaMin
      hDeltaA hDeltaC hLin

end NumStability
