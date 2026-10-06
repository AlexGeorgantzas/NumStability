import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.FirstOrder
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.Separation
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.SigmaMinBounds.SylvesterPerturbation
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Basic
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Rectangular
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter16.Foundations.Core

/-!
# Source.Higham.Chapter16.Section03.PerturbationAndConditioning.SigmaMinCorollaries.SylvesterPerturbation

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/Sylvester/Higham16PerturbationSigmaMin.lean
--
-- Sigma-min source wrappers for Higham, Accuracy and Stability of Numerical
-- Algorithms, 2nd ed., Chapter 16.3-16.4, equations (16.25) and (16.28).



namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius












/-- Higham, 2nd ed., Chapter 16.3-16.4, equation (16.26):
    source-numbered alias for the sigma-min `SepLowerBound` certificate. -/
theorem H16_eq16_26_sepLowerBound_of_sigmaMin (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hSigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y)) :
    SepLowerBound n A B sigma := by
  exact SepLowerBound_sylvester_of_sigmaMin n A B sigma hSigma hSigmaMin















/-- Higham, 2nd ed., Chapter 16.3-16.4, equation (16.26):
    source-numbered alias for the sigma-min lower bound on `sep(A,B)`. -/
theorem H16_eq16_26_sylvesterSepInf_ge_of_sigmaMin (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hn : 0 < n) (hSigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y)) :
    sigma <= sylvesterSepInf n A B := by
  exact sylvesterSepInf_ge_of_sigmaMin n A B sigma hn hSigma hSigmaMin














/-- Higham, 2nd ed., Chapter 16.3-16.4, equation (16.26):
    source-numbered alias for strict positivity of `sep(A,B)` from a positive
    Sylvester operator sigma-min certificate. -/
theorem H16_eq16_26_sylvesterSepInf_pos_of_sigmaMin (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hn : 0 < n) (hSigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y)) :
    0 < sylvesterSepInf n A B := by
  exact sylvesterSepInf_pos_of_sigmaMin n A B sigma hn hSigma hSigmaMin


























/-- Higham, 2nd ed., Chapter 16.3, equation (16.25):
    source-numbered alias for the direct sigma-min Sylvester perturbation
    bound retaining the nonzero perturbation side condition. -/
alias H16_eq16_25_sylvester_perturbation_bound_of_sigmaMin :=
  sylvester_perturbation_bound_of_sigmaMin




























/-- Higham, 2nd ed., Chapter 16.3, equation (16.25):
    source-numbered alias for the direct relative sigma-min Sylvester
    perturbation bound retaining the nonzero perturbation side conditions. -/
alias H16_eq16_25_sylvester_relative_perturbation_of_sigmaMin :=
  sylvester_relative_perturbation_of_sigmaMin


























/-- Higham, 2nd ed., Chapter 16.3, equation (16.25):
    source-numbered alias for the total sigma-min Sylvester perturbation bound. -/
theorem H16_eq16_25_sylvester_perturbation_bound_of_sigmaMin_total (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j) :
    frobNorm dX <=
      (1 / sigma) * ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound_of_sigmaMin_total n
      A B X dA dB dC dX sigma hSigma hSigmaMin
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin



























/-- Higham, 2nd ed., Chapter 16.3, equation (16.25):
    source-numbered alias for the total relative sigma-min perturbation bound. -/
theorem H16_eq16_25_sylvester_relative_perturbation_of_sigmaMin_total (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n A B X alpha beta gamma sigma * eps := by
  exact
    sylvester_relative_perturbation_of_sigmaMin_total n
      A B X dA dB dC dX sigma hSigma hSigmaMin
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hX_pos


















/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the direct sigma-min a posteriori bound retaining
    the nonzero error side condition. -/
alias H16_eq16_28_sylvester_aposteriori_bound_of_sigmaMin :=
  sylvester_aposteriori_bound_of_sigmaMin































/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the total sigma-min a posteriori bound. -/
theorem H16_eq16_28_sylvester_aposteriori_bound_of_sigmaMin_total (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (hExact : forall i j, sylvesterOp n A B X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat) := by
  exact
    sylvester_aposteriori_bound_of_sigmaMin_total n A B C X Xhat sigma
      hSigma hSigmaMin hExact




















/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the direct relative sigma-min a posteriori bound
    retaining the nonzero error side condition. -/
alias H16_eq16_28_sylvester_relative_aposteriori_bound_of_sigmaMin :=
  sylvester_relative_aposteriori_bound_of_sigmaMin



















































/-- Higham, 2nd ed., Chapter 16.2 and 16.4, equations (16.9) and (16.28):
    a Schur-coordinate Frobenius residual budget transfers through the exact
    orthogonal Schur reconstruction and gives the source-shaped relative
    Frobenius forward-error bound for the original Sylvester equation.  This is
    exact residual transport only; it does not model rounded Bartels-Stewart
    arithmetic or estimator production. -/
theorem sylvester_relative_error_le_of_sepLowerBound_schur_transform_residual_budget
    (n : Nat)
    (U R A : RMatFn n n) (V S B : RMatFn n n)
    (C X Y : RMatFn n n) (sigma eta : Real)
    (hSep : SepLowerBound n A B sigma)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hX_pos : 0 < frobNorm X)
    (hResidual :
      frobNormRect
        (sylvesterResidualRect n n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <=
        eta * sigma * frobNorm X) :
    frobNorm
        (fun i j => X i j -
          rectMatMul U (rectMatMul Y (matTranspose V)) i j) /
        frobNorm X <= eta := by
  let Xhat : RMatFn n n := rectMatMul U (rectMatMul Y (matTranspose V))
  have hResidualOrigRect :
      frobNormRect (sylvesterResidualRect n n A B C Xhat) <=
        eta * sigma * frobNorm X :=
    frobNormRect_sylvesterResidualRect_le_of_schur_transform
      n n U R A V S B C Y (eta * sigma * frobNorm X)
      hU hV hA hB hResidual
  have hResidualOrig :
      frobNorm (sylvesterResidual n A B C Xhat) <=
        eta * sigma * frobNorm X := by
    rw [<- frobNormRect_eq_frobNormFn]
    simpa [Xhat, sylvesterResidual, sylvesterResidualRect,
      sylvesterOp, sylvesterOpRect, matMul, matMulRect] using hResidualOrigRect
  exact
    sylvester_relative_error_le_of_sepLowerBound_residual_budget n
      A B C X Xhat sigma eta hSep hExact hX_pos hResidualOrig

/-- Higham, 2nd ed., Chapter 16.3-16.4, equations (16.26) and (16.28):
    a supplied Sylvester operator sigma-min certificate feeds the exact
    Schur-coordinate residual-budget relative Frobenius forward-error bridge. -/
theorem sylvester_relative_error_le_of_sigmaMin_schur_transform_residual_budget
    (n : Nat)
    (U R A : RMatFn n n) (V S B : RMatFn n n)
    (C X Y : RMatFn n n) (sigma eta : Real)
    (hSigma : 0 < sigma)
    (hSigmaMin : forall Z : RMatFn n n,
      sigma * frobNorm Z <= frobNorm (sylvesterOp n A B Z))
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hX_pos : 0 < frobNorm X)
    (hResidual :
      frobNormRect
        (sylvesterResidualRect n n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <=
        eta * sigma * frobNorm X) :
    frobNorm
        (fun i j => X i j -
          rectMatMul U (rectMatMul Y (matTranspose V)) i j) /
        frobNorm X <= eta := by
  exact
    sylvester_relative_error_le_of_sepLowerBound_schur_transform_residual_budget
      n U R A V S B C X Y sigma eta
      (SepLowerBound_sylvester_of_sigmaMin n A B sigma hSigma hSigmaMin)
      hU hV hA hB hExact hX_pos hResidual

/-- Higham, 2nd ed., Chapter 16.3-16.4, equations (16.26) and (16.28):
    a positive exact `sep(A,B)` lower bound feeds the exact Schur-coordinate
    residual-budget relative Frobenius forward-error bridge. -/
theorem sylvester_relative_error_le_of_pos_le_sylvesterSepInf_schur_transform_residual_budget
    (n : Nat)
    (U R A : RMatFn n n) (V S B : RMatFn n n)
    (C X Y : RMatFn n n) (sigma eta : Real)
    (hSigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hX_pos : 0 < frobNorm X)
    (hResidual :
      frobNormRect
        (sylvesterResidualRect n n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <=
        eta * sigma * frobNorm X) :
    frobNorm
        (fun i j => X i j -
          rectMatMul U (rectMatMul Y (matTranspose V)) i j) /
        frobNorm X <= eta := by
  exact
    sylvester_relative_error_le_of_sepLowerBound_schur_transform_residual_budget
      n U R A V S B C X Y sigma eta
      (SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma hSigma hle)
      hU hV hA hB hExact hX_pos hResidual






























































/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the total relative sigma-min a posteriori bound. -/
theorem H16_eq16_28_sylvester_relative_aposteriori_bound_of_sigmaMin_total
    (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat)) /
        frobNorm X := by
  exact
    sylvester_relative_aposteriori_bound_of_sigmaMin_total n
      A B C X Xhat sigma hSigma hSigmaMin hExact hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    source-numbered alias for the exact-`sep(A,B)` residual-budget relative
    Frobenius forward-error bound. -/
theorem H16_eq16_28_sylvester_relative_error_le_of_pos_le_sylvesterSepInf_residual_budget
    (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma eta : Real) (hSigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hX_pos : 0 < frobNorm X)
    (hResidual :
      frobNorm (sylvesterResidual n A B C Xhat) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  exact
    sylvester_relative_error_le_of_pos_le_sylvesterSepInf_residual_budget n
      A B C X Xhat sigma eta hSigma hle hExact hX_pos hResidual

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the `SepLowerBound` residual-budget relative
    Frobenius forward-error bound. -/
theorem H16_eq16_28_sylvester_relative_error_le_of_sepLowerBound_residual_budget
    (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma eta : Real) (hSep : SepLowerBound n A B sigma)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hX_pos : 0 < frobNorm X)
    (hResidual :
      frobNorm (sylvesterResidual n A B C Xhat) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  exact
    sylvester_relative_error_le_of_sepLowerBound_residual_budget n
      A B C X Xhat sigma eta hSep hExact hX_pos hResidual

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the Schur-coordinate residual-budget relative
    Frobenius forward-error bound. -/
theorem H16_eq16_28_sylvester_relative_error_le_of_sepLowerBound_schur_transform_residual_budget
    (n : Nat)
    (U R A : RMatFn n n) (V S B : RMatFn n n)
    (C X Y : RMatFn n n) (sigma eta : Real)
    (hSep : SepLowerBound n A B sigma)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hX_pos : 0 < frobNorm X)
    (hResidual :
      frobNormRect
        (sylvesterResidualRect n n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <=
        eta * sigma * frobNorm X) :
    frobNorm
        (fun i j => X i j -
          rectMatMul U (rectMatMul Y (matTranspose V)) i j) /
        frobNorm X <= eta := by
  exact
    sylvester_relative_error_le_of_sepLowerBound_schur_transform_residual_budget
      n U R A V S B C X Y sigma eta hSep hU hV hA hB hExact hX_pos
      hResidual

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    source-numbered alias for the supplied-operator-sigma-min Schur-coordinate
    residual-budget relative Frobenius forward-error bound. -/
theorem H16_eq16_28_sylvester_relative_error_le_of_sigmaMin_schur_transform_residual_budget
    (n : Nat)
    (U R A : RMatFn n n) (V S B : RMatFn n n)
    (C X Y : RMatFn n n) (sigma eta : Real)
    (hSigma : 0 < sigma)
    (hSigmaMin : forall Z : RMatFn n n,
      sigma * frobNorm Z <= frobNorm (sylvesterOp n A B Z))
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hX_pos : 0 < frobNorm X)
    (hResidual :
      frobNormRect
        (sylvesterResidualRect n n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <=
        eta * sigma * frobNorm X) :
    frobNorm
        (fun i j => X i j -
          rectMatMul U (rectMatMul Y (matTranspose V)) i j) /
        frobNorm X <= eta := by
  exact
    sylvester_relative_error_le_of_sigmaMin_schur_transform_residual_budget
      n U R A V S B C X Y sigma eta hSigma hSigmaMin hU hV hA hB
      hExact hX_pos hResidual

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    source-numbered alias for the exact-`sep(A,B)` Schur-coordinate
    residual-budget relative Frobenius forward-error bound. -/
theorem H16_eq16_28_sylvester_relative_error_le_of_pos_le_sylvesterSepInf_schur_transform_residual_budget
    (n : Nat)
    (U R A : RMatFn n n) (V S B : RMatFn n n)
    (C X Y : RMatFn n n) (sigma eta : Real)
    (hSigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hX_pos : 0 < frobNorm X)
    (hResidual :
      frobNormRect
        (sylvesterResidualRect n n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <=
        eta * sigma * frobNorm X) :
    frobNorm
        (fun i j => X i j -
          rectMatMul U (rectMatMul Y (matTranspose V)) i j) /
        frobNorm X <= eta := by
  exact
    sylvester_relative_error_le_of_pos_le_sylvesterSepInf_schur_transform_residual_budget
      n U R A V S B C X Y sigma eta hSigma hle hU hV hA hB
      hExact hX_pos hResidual

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    source-numbered alias for the supplied-operator-sigma-min residual-budget
    relative Frobenius forward-error bound. -/
theorem H16_eq16_28_sylvester_relative_error_le_of_sigmaMin_residual_budget
    (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma eta : Real) (hSigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hX_pos : 0 < frobNorm X)
    (hResidual :
      frobNorm (sylvesterResidual n A B C Xhat) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  exact
    sylvester_relative_error_le_of_sigmaMin_residual_budget n
      A B C X Xhat sigma eta hSigma hSigmaMin hExact hX_pos hResidual

end NumStability
