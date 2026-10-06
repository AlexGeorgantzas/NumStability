import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.FirstOrder
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.Separation
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.SingularValue
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Basic
import NumStability.Algorithms.MatrixEquations.Sylvester.Perturbation.Basic
import NumStability.Algorithms.MatrixEquations.Sylvester.Perturbation.SeparationBounds
import NumStability.Analysis.MatrixAlgebra

/-!
# Algorithms.MatrixEquations.Sylvester.Conditioning.SigmaMinBounds.SylvesterPerturbation

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/Sylvester/Higham16PerturbationSigmaMin.lean
--
-- Sigma-min source wrappers for Higham, Accuracy and Stability of Numerical
-- Algorithms, 2nd ed., Chapter 16.3-16.4, equations (16.25) and (16.28).



namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-- Higham Ch.16.3-16.4, equations (16.25)-(16.26):
    a positive singular-value lower-bound certificate for the Sylvester
    operator gives the corresponding `SepLowerBound`. -/
theorem SepLowerBound_sylvester_of_sigmaMin (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hSigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y)) :
    SepLowerBound n A B sigma := by
  exact sepLowerBound_of_sylvesterOp_sigmaMin n A B sigma hSigma hSigmaMin











/-- Higham Ch.16.3-16.4, equation (16.26):
    in positive dimension, a Sylvester operator sigma-min certificate
    lower-bounds the exact `sep(A,B)` infimum. -/
theorem sylvesterSepInf_ge_of_sigmaMin (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hn : 0 < n) (hSigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y)) :
    sigma <= sylvesterSepInf n A B := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_pos_dim n A B sigma
      (SepLowerBound_sylvester_of_sigmaMin n A B sigma hSigma hSigmaMin)
      hn











/-- Higham Ch.16.3-16.4, equation (16.26):
    in positive dimension, a positive Sylvester operator sigma-min certificate
    makes the exact `sep(A,B)` infimum strictly positive. -/
theorem sylvesterSepInf_pos_of_sigmaMin (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hn : 0 < n) (hSigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y)) :
    0 < sylvesterSepInf n A B := by
  exact
    lt_of_lt_of_le hSigma
      (sylvesterSepInf_ge_of_sigmaMin n A B sigma hn hSigma hSigmaMin)












/-- Higham, 2nd ed., Chapter 16.3, equations (16.25) and (16.26):
    a positive singular-value lower bound on the Sylvester operator
    instantiates the Frobenius first-order Sylvester perturbation bound. -/
theorem sylvester_perturbation_bound_of_sigmaMin (n : Nat)
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
    (hdX_ne : Not (frobNormSq dX = 0)) :
    frobNorm dX <=
      (1 / sigma) * ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound n A B X dA dB dC dX sigma hSigma
      (sepLowerBound_of_sylvesterOp_sigmaMin n A B sigma hSigma hSigmaMin)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne







/-- Higham, 2nd ed., Chapter 16.3, equations (16.25) and (16.26):
    the relative Sylvester perturbation bound follows from a positive
    singular-value lower bound on the Sylvester operator. -/
theorem sylvester_relative_perturbation_of_sigmaMin (n : Nat)
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
    (hdX_ne : Not (frobNormSq dX = 0))
    (hX_ne : Not (frobNorm X = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n A B X alpha beta gamma sigma * eps := by
  exact
    sylvester_relative_perturbation n A B X dA dB dC dX sigma hSigma
      (sepLowerBound_of_sylvesterOp_sigmaMin n A B sigma hSigma hSigmaMin)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne hX_ne hX_pos







/-- Higham, 2nd ed., Chapter 16.3, equations (16.25) and (16.26):
    total Sylvester perturbation bound from a supplied positive singular-value
    lower bound on the Sylvester operator. -/
theorem sylvester_perturbation_bound_of_sigmaMin_total (n : Nat)
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
    sylvester_perturbation_bound_of_sepLowerBound_total n
      A B X dA dB dC dX sigma
      (sepLowerBound_of_sylvesterOp_sigmaMin n A B sigma hSigma hSigmaMin)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin
























/-- Higham, 2nd ed., Chapter 16.3, equations (16.25) and (16.26):
    total relative Sylvester perturbation bound from a supplied positive
    singular-value lower bound on the Sylvester operator. -/
theorem sylvester_relative_perturbation_of_sigmaMin_total (n : Nat)
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
    sylvester_relative_perturbation_of_sepLowerBound_total n
      A B X dA dB dC dX sigma
      (sepLowerBound_of_sylvesterOp_sigmaMin n A B sigma hSigma hSigmaMin)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hX_pos

























/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    a positive singular-value lower bound on the Sylvester operator
    instantiates the Frobenius a posteriori error-residual bound. -/
theorem sylvester_aposteriori_bound_of_sigmaMin (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat) := by
  exact
    sylvester_aposteriori_bound n A B C X Xhat sigma hSigma
      (sepLowerBound_of_sylvesterOp_sigmaMin n A B sigma hSigma hSigmaMin)
      hExact hE_ne







/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    total a posteriori Sylvester residual-error bound from a supplied positive
    singular-value lower bound on the Sylvester operator.

    This removes the nonzero-error side condition by handling the zero-error
    case directly. -/
theorem sylvester_aposteriori_bound_of_sigmaMin_total (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (hExact : forall i j, sylvesterOp n A B X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat) := by
  by_cases hE_ne :
      Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)
  case pos =>
    exact
      sylvester_aposteriori_bound_of_sigmaMin n A B C X Xhat sigma
        hSigma hSigmaMin hExact hE_ne
  case neg =>
    have hE_sq :
        frobNormSq (fun i j => X i j - Xhat i j) = 0 :=
      Classical.not_not.mp hE_ne
    have hE :
        frobNorm (fun i j => X i j - Xhat i j) = 0 := by
      simp [frobNorm_eq_sqrt_frobNormSq, hE_sq]
    rw [hE]
    exact mul_nonneg (by positivity) (frobNorm_nonneg _)















/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    the source-shaped relative a posteriori bound follows from a positive
    singular-value lower bound on the Sylvester operator. -/
theorem sylvester_relative_aposteriori_bound_of_sigmaMin (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat)) /
        frobNorm X := by
  exact
    sylvester_relative_aposteriori_bound n A B C X Xhat sigma hSigma
      (sepLowerBound_of_sylvesterOp_sigmaMin n A B sigma hSigma hSigmaMin)
      hExact hE_ne hX_pos







/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    total relative a posteriori Sylvester residual-error bound from a supplied
    positive singular-value lower bound on the Sylvester operator.

    This is the total absolute bound divided by the positive Frobenius norm of
    the exact Sylvester solution. -/
theorem sylvester_relative_aposteriori_bound_of_sigmaMin_total (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat)) /
        frobNorm X := by
  have hAbs :=
    sylvester_aposteriori_bound_of_sigmaMin_total n A B C X Xhat sigma
      hSigma hSigmaMin hExact
  exact div_le_div_of_nonneg_right hAbs (le_of_lt hX_pos)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    a supplied exact `SepLowerBound` plus an exact residual budget gives a
    relative Frobenius forward-error budget for an approximate Sylvester
    solution. -/
theorem sylvester_relative_error_le_of_sepLowerBound_residual_budget (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma eta : Real) (hSep : SepLowerBound n A B sigma)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hX_pos : 0 < frobNorm X)
    (hResidual :
      frobNorm (sylvesterResidual n A B C Xhat) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  have hRel :=
    sylvester_relative_aposteriori_bound_of_sepLowerBound_total n
      A B C X Xhat sigma hSep hExact hX_pos
  have hScaled :
      ((1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat)) /
          frobNorm X <= eta := by
    rw [div_le_iff₀ hX_pos]
    rw [show (1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat) =
        frobNorm (sylvesterResidual n A B C Xhat) / sigma by ring]
    rw [div_le_iff₀ hSep.1]
    calc
      frobNorm (sylvesterResidual n A B C Xhat)
          <= eta * sigma * frobNorm X := hResidual
      _ = eta * frobNorm X * sigma := by ring
  exact le_trans hRel hScaled






































































































/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    a sigma-min lower bound plus an exact residual budget gives a clean
    relative Frobenius forward-error budget for an approximate Sylvester
    solution. -/
theorem sylvester_relative_error_le_of_sigmaMin_residual_budget (n : Nat)
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
  have hRel :=
    sylvester_relative_aposteriori_bound_of_sigmaMin_total n
      A B C X Xhat sigma hSigma hSigmaMin hExact hX_pos
  have hScaled :
      ((1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat)) /
          frobNorm X <= eta := by
    rw [div_le_iff₀ hX_pos]
    rw [show (1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat) =
        frobNorm (sylvesterResidual n A B C Xhat) / sigma by ring]
    rw [div_le_iff₀ hSigma]
    calc
      frobNorm (sylvesterResidual n A B C Xhat)
          <= eta * sigma * frobNorm X := hResidual
      _ = eta * frobNorm X * sigma := by ring
  exact le_trans hRel hScaled

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    a positive lower bound on the exact `sep(A,B)` infimum plus a Frobenius
    residual budget gives the source-shaped relative forward-error bound. -/
theorem sylvester_relative_error_le_of_pos_le_sylvesterSepInf_residual_budget
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
  have hRel :=
    sylvester_relative_aposteriori_bound_of_pos_le_sylvesterSepInf_total n
      A B C X Xhat sigma hSigma hle hExact hX_pos
  have hScaled :
      ((1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat)) /
          frobNorm X <= eta := by
    rw [div_le_iff₀ hX_pos]
    rw [show (1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat) =
        frobNorm (sylvesterResidual n A B C Xhat) / sigma by ring]
    rw [div_le_iff₀ hSigma]
    calc
      frobNorm (sylvesterResidual n A B C Xhat)
          <= eta * sigma * frobNorm X := hResidual
      _ = eta * frobNorm X * sigma := by ring
  exact le_trans hRel hScaled




























































































































































end NumStability
