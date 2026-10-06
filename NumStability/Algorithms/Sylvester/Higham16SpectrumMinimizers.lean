-- Algorithms/Sylvester/Higham16SpectrumMinimizers.lean
--
-- Floating-point computed-residual adapters for the supplied Schur endpoint
-- families in `Higham16Spectrum.lean`, using the residual model from
-- `Higham16Minimizers.lean`.

import NumStability.Algorithms.Sylvester.Higham16Spectrum
import NumStability.Algorithms.Sylvester.Higham16Minimizers

namespace NumStability

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate case: instantiate the practical error bound with the
    floating-point residual `flSylvesterResidualRect` and its rounding budget.
    Scope: the Schur factors and exact solution are supplied hypotheses; only
    the residual evaluation is modeled in floating point. -/
theorem sylvester_practical_error_bound_fl_of_schurTriangular (fp : FPModel)
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B)
          (flSylvesterResidualRect fp m n A B C Xhat)
          (flSylvesterResidualBudget fp m n A B C Xhat)) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate
      m n U R A V S B C X Xhat
      (flSylvesterResidualRect fp m n A B C Xhat)
      (flSylvesterResidualBudget fp m n A B C Xhat)
      hU hV hA hB hS hshift hX
      (isSylvesterComputedResidualBudget_fl fp m n A B C Xhat hm hn)
      hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    source-numbered alias for the supplied Schur triangular floating-point
    practical endpoint. -/
theorem H16_eq16_29_sylvester_practical_error_bound_fl_of_schurTriangular
    (fp : FPModel) (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B)
          (flSylvesterResidualRect fp m n A B C Xhat)
          (flSylvesterResidualBudget fp m n A B C Xhat)) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_fl_of_schurTriangular fp m n
      U R A V S B C X Xhat hU hV hA hB hS hshift hX hm hn hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate scalar cap for the floating-point residual practical
    budget. -/
theorem sylvester_practical_error_bound_fl_of_schurTriangular_scalar
    (fp : FPModel) (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B)
          (flSylvesterResidualRect fp m n A B C Xhat)
          (flSylvesterResidualBudget fp m n A B C Xhat) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate_scalar
      m n U R A V S B C X Xhat
      (flSylvesterResidualRect fp m n A B C Xhat)
      (flSylvesterResidualBudget fp m n A B C Xhat)
      eta hU hV hA hB hS hshift hX
      (isSylvesterComputedResidualBudget_fl fp m n A B C Xhat hm hn)
      heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    source-numbered alias for the supplied Schur triangular scalar
    floating-point practical endpoint. -/
theorem H16_eq16_29_sylvester_practical_error_bound_fl_of_schurTriangular_scalar
    (fp : FPModel) (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B)
          (flSylvesterResidualRect fp m n A B C Xhat)
          (flSylvesterResidualBudget fp m n A B C Xhat) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_fl_of_schurTriangular_scalar fp m n
      U R A V S B C X Xhat eta hU hV hA hB hS hshift hX hm hn
      heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate monotone endpoint: the floating-point residual and budget
    may be replaced by componentwise larger estimator inputs. -/
theorem sylvester_practical_error_bound_fl_of_schurTriangular_mono
    (fp : FPModel) (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat' Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp m n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp m n A B C Xhat i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate_mono
      m n U R A V S B C X Xhat
      (flSylvesterResidualRect fp m n A B C Xhat) Rhat'
      (flSylvesterResidualBudget fp m n A B C Xhat) Ru'
      PinvAbs' hU hV hA hB hS hshift hX
      (isSylvesterComputedResidualBudget_fl fp m n A B C Xhat hm hn)
      hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    source-numbered alias for the supplied Schur triangular monotone
    floating-point practical endpoint. -/
theorem H16_eq16_29_sylvester_practical_error_bound_fl_of_schurTriangular_mono
    (fp : FPModel) (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat' Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp m n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp m n A B C Xhat i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_fl_of_schurTriangular_mono fp m n
      U R A V S B C X Xhat Rhat' Ru' PinvAbs' hU hV hA hB hS hshift hX
      hm hn hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied triangular
    Schur-coordinate monotone scalar cap for enlarged estimator inputs. -/
theorem sylvester_practical_error_bound_fl_of_schurTriangular_mono_scalar
    (fp : FPModel) (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat' Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp m n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp m n A B C Xhat i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurTriangular_computed_residual_certificate_mono_scalar
      m n U R A V S B C X Xhat
      (flSylvesterResidualRect fp m n A B C Xhat) Rhat'
      (flSylvesterResidualBudget fp m n A B C Xhat) Ru'
      PinvAbs' eta hU hV hA hB hS hshift hX
      (isSylvesterComputedResidualBudget_fl fp m n A B C Xhat hm hn)
      hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    source-numbered alias for the supplied Schur triangular monotone scalar
    floating-point practical endpoint. -/
theorem H16_eq16_29_sylvester_practical_error_bound_fl_of_schurTriangular_mono_scalar
    (fp : FPModel) (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Xhat Rhat' Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hS : IsUpperTriangularFn n S)
    (hshift : forall k : Fin n,
      Not (Matrix.det (sylvesterTriangularShiftedCoeff m R (S k k)) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp m n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp m n A B C Xhat i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_fl_of_schurTriangular_mono_scalar fp m n
      U R A V S B C X Xhat Rhat' Ru' PinvAbs' eta hU hV hA hB hS hshift
      hX hm hn hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied real
    quasi-Schur strict-block-map case: instantiate the practical error bound
    with the floating-point residual and its rounding budget.  Scope: the
    strict block-map factors, determinant certificate, and exact solution are
    supplied; only the residual evaluation is modeled in floating point. -/
theorem sylvester_practical_error_bound_fl_of_realQuasiSchur_strictBlockMap
    (fp : FPModel) (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B)
          (flSylvesterResidualRect fp m n A B C Xhat)
          (flSylvesterResidualBudget fp m n A B C Xhat)) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate
      m n U R A V S B pA pB C X Xhat
      (flSylvesterResidualRect fp m n A B C Xhat)
      (flSylvesterResidualBudget fp m n A B C Xhat)
      hU hV hA hB hpAmono hpAcard hRstrict hpBmono hpBcard hSstrict
      hdet hX
      (isSylvesterComputedResidualBudget_fl fp m n A B C Xhat hm hn)
      hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    source-numbered alias for the supplied real-quasi-Schur strict-block-map
    floating-point practical endpoint. -/
theorem H16_eq16_29_sylvester_practical_error_bound_fl_of_realQuasiSchur_strictBlockMap
    (fp : FPModel) (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B)
          (flSylvesterResidualRect fp m n A B C Xhat)
          (flSylvesterResidualBudget fp m n A B C Xhat)) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_fl_of_realQuasiSchur_strictBlockMap fp m n
      U R A V S B pA pB C X Xhat hU hV hA hB hpAmono hpAcard hRstrict
      hpBmono hpBcard hSstrict hdet hX hm hn hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied real
    quasi-Schur strict-block-map scalar cap for the floating-point residual
    practical budget. -/
theorem sylvester_practical_error_bound_fl_of_realQuasiSchur_strictBlockMap_scalar
    (fp : FPModel) (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B)
          (flSylvesterResidualRect fp m n A B C Xhat)
          (flSylvesterResidualBudget fp m n A B C Xhat) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate_scalar
      m n U R A V S B pA pB C X Xhat
      (flSylvesterResidualRect fp m n A B C Xhat)
      (flSylvesterResidualBudget fp m n A B C Xhat)
      eta hU hV hA hB hpAmono hpAcard hRstrict hpBmono hpBcard hSstrict
      hdet hX
      (isSylvesterComputedResidualBudget_fl fp m n A B C Xhat hm hn)
      heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    source-numbered alias for the supplied real-quasi-Schur strict-block-map
    scalar floating-point practical endpoint. -/
theorem H16_eq16_29_sylvester_practical_error_bound_fl_of_realQuasiSchur_strictBlockMap_scalar
    (fp : FPModel) (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B)
          (flSylvesterResidualRect fp m n A B C Xhat)
          (flSylvesterResidualBudget fp m n A B C Xhat) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_fl_of_realQuasiSchur_strictBlockMap_scalar
      fp m n U R A V S B pA pB C X Xhat eta hU hV hA hB hpAmono hpAcard
      hRstrict hpBmono hpBcard hSstrict hdet hX hm hn heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied real
    quasi-Schur strict-block-map monotone endpoint: the floating-point
    residual and budget may be replaced by componentwise larger estimator
    inputs. -/
theorem sylvester_practical_error_bound_fl_of_realQuasiSchur_strictBlockMap_mono
    (fp : FPModel) (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat' Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp m n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp m n A B C Xhat i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate_mono
      m n U R A V S B pA pB C X Xhat
      (flSylvesterResidualRect fp m n A B C Xhat) Rhat'
      (flSylvesterResidualBudget fp m n A B C Xhat) Ru'
      PinvAbs' hU hV hA hB hpAmono hpAcard hRstrict hpBmono hpBcard hSstrict
      hdet hX
      (isSylvesterComputedResidualBudget_fl fp m n A B C Xhat hm hn)
      hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    source-numbered alias for the supplied real-quasi-Schur strict-block-map
    monotone floating-point practical endpoint. -/
theorem H16_eq16_29_sylvester_practical_error_bound_fl_of_realQuasiSchur_strictBlockMap_mono
    (fp : FPModel) (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat' Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp m n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp m n A B C Xhat i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_fl_of_realQuasiSchur_strictBlockMap_mono
      fp m n U R A V S B pA pB C X Xhat Rhat' Ru' PinvAbs'
      hU hV hA hB hpAmono hpAcard hRstrict hpBmono hpBcard hSstrict
      hdet hX hm hn hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied real
    quasi-Schur strict-block-map monotone scalar cap for enlarged estimator
    inputs. -/
theorem sylvester_practical_error_bound_fl_of_realQuasiSchur_strictBlockMap_mono_scalar
    (fp : FPModel) (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat' Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp m n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp m n A B C Xhat i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_realQuasiSchur_strictBlockMap_computed_residual_certificate_mono_scalar
      m n U R A V S B pA pB C X Xhat
      (flSylvesterResidualRect fp m n A B C Xhat) Rhat'
      (flSylvesterResidualBudget fp m n A B C Xhat) Ru'
      PinvAbs' eta hU hV hA hB hpAmono hpAcard hRstrict hpBmono hpBcard hSstrict
      hdet hX
      (isSylvesterComputedResidualBudget_fl fp m n A B C Xhat hm hn)
      hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    source-numbered alias for the supplied real-quasi-Schur strict-block-map
    monotone scalar floating-point practical endpoint. -/
theorem H16_eq16_29_sylvester_practical_error_bound_fl_of_realQuasiSchur_strictBlockMap_mono_scalar
    (fp : FPModel) (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (pA : Fin m -> Nat) (pB : Fin n -> Nat)
    (C X Xhat Rhat' Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hpAmono : Monotone pA)
    (hpAcard :
      forall c : Nat, (Finset.univ.filter (fun i : Fin m => pA i = c)).card <= 2)
    (hRstrict : forall i j : Fin m, pA j < pA i -> R i j = 0)
    (hpBmono : Monotone pB)
    (hpBcard :
      forall c : Nat, (Finset.univ.filter (fun j : Fin n => pB j = c)).card <= 2)
    (hSstrict : forall i j : Fin n, pB j < pB i -> S i j = 0)
    (hdet : Not (Matrix.det (sylvesterVecCoeff m n A B) = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp m n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp m n A B C Xhat i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_fl_of_realQuasiSchur_strictBlockMap_mono_scalar
      fp m n U R A V S B pA pB C X Xhat Rhat' Ru' PinvAbs' eta
      hU hV hA hB hpAmono hpAcard hRstrict hpBmono hpBcard hSstrict
      hdet hX hm hn hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

end NumStability
