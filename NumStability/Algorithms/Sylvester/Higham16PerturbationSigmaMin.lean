-- Algorithms/Sylvester/Higham16PerturbationSigmaMin.lean
--
-- Sigma-min source wrappers for Higham, Accuracy and Stability of Numerical
-- Algorithms, 2nd ed., Chapter 16.3-16.4, equations (16.25) and (16.28).

import NumStability.Analysis.InverseOpNorm2

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

/-- Higham, 2nd ed., Chapter 16.3-16.4, equation (16.26):
    source-numbered alias for the sigma-min `SepLowerBound` certificate. -/
theorem H16_eq16_26_sepLowerBound_of_sigmaMin (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hSigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y)) :
    SepLowerBound n A B sigma := by
  exact SepLowerBound_sylvester_of_sigmaMin n A B sigma hSigma hSigmaMin

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

/-- Higham, 2nd ed., Chapter 16.3-16.4, equation (16.26):
    source-numbered alias for the sigma-min lower bound on `sep(A,B)`. -/
theorem H16_eq16_26_sylvesterSepInf_ge_of_sigmaMin (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hn : 0 < n) (hSigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y)) :
    sigma <= sylvesterSepInf n A B := by
  exact sylvesterSepInf_ge_of_sigmaMin n A B sigma hn hSigma hSigmaMin

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

/-- Higham, 2nd ed., Chapter 16.3, equation (16.25):
    source-numbered alias for the direct sigma-min Sylvester perturbation
    bound retaining the nonzero perturbation side condition. -/
alias H16_eq16_25_sylvester_perturbation_bound_of_sigmaMin :=
  sylvester_perturbation_bound_of_sigmaMin

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

/-- Higham, 2nd ed., Chapter 16.3, equation (16.25):
    source-numbered alias for the direct relative sigma-min Sylvester
    perturbation bound retaining the nonzero perturbation side conditions. -/
alias H16_eq16_25_sylvester_relative_perturbation_of_sigmaMin :=
  sylvester_relative_perturbation_of_sigmaMin

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

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the direct sigma-min a posteriori bound retaining
    the nonzero error side condition. -/
alias H16_eq16_28_sylvester_aposteriori_bound_of_sigmaMin :=
  sylvester_aposteriori_bound_of_sigmaMin

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

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    source-numbered alias for the direct relative sigma-min a posteriori bound
    retaining the nonzero error side condition. -/
alias H16_eq16_28_sylvester_relative_aposteriori_bound_of_sigmaMin :=
  sylvester_relative_aposteriori_bound_of_sigmaMin

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
