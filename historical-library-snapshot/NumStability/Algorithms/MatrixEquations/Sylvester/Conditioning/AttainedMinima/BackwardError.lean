import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatrixEquations.Sylvester.BackwardError.LyapunovSpectral
import NumStability.Algorithms.MatrixEquations.Sylvester.BackwardError.SylvesterSVD
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.PracticalErrorBounds
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.Separation
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.SigmaMinBounds.SylvesterPerturbation
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.SigmaMinBounds.Vectorized
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Basic
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Lyapunov
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Rectangular
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Vectorization
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Algorithms.MatrixEquations.Sylvester.Conditioning.AttainedMinima.BackwardError

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/Sylvester/Higham16Minimizers.lean
--
-- Attained-minimum upgrades and the floating-point computed-residual model
-- for Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 16 "The Sylvester Equation".
--
-- This file closes three infimum-model gaps left open by `Higham16.lean` and
-- `SylvesterBackward.lean`:
--
-- 1. (16.26) `sep(A,B)`: the infimum of the Frobenius ratios
--    `||AX - XB||_F / ||X||_F` over nonzero `X` is attained by a unit
--    Frobenius-norm minimizer, so the infimum model `sylvesterSepInf` is a
--    minimum (`IsLeast`).
-- 2. (16.15) backward error `eta(Y)`: with positive weights and a nonempty
--    feasible set, the infimum model `sylvesterBackwardErrorInf` is itself a
--    feasible backward error, attained by an optimal perturbation triple.
-- 3. (16.29) the practical bound's computed-residual hypothesis: the residual
--    `R = C - (A*Xhat - Xhat*B)` evaluated with floating-point matrix products
--    and a rounded subtract/add pipeline admits an explicit `dR` with
--    `Rhat = R + dR` and an entrywise `gamma`-weighted budget, which plugs
--    directly into the diagonal practical error bound of `Higham16.lean`.
--
-- All statements are over the repository's legacy function-shaped matrices
-- `RMatFn m n = Fin m -> Fin n -> Real`, matching the Chapter 16 modules.





namespace NumStability

open scoped BigOperators

-- ============================================================
-- Topological helpers for the Frobenius objectives
-- ============================================================























































































-- ============================================================
-- Scaling identities for the sep(A,B) normalization
-- ============================================================



























-- ============================================================
-- (16.26): the sep(A,B) infimum is an attained minimum
-- ============================================================








































































































































-- ============================================================
-- (16.15): the backward-error infimum is an attained minimum
-- ============================================================



















































































































































































































































































































































/-- Higham, 2nd ed., Chapter 16, Section 16.2, equation (16.15):
    source-facing two-sided Sylvester eta/xi infimum bound from SVD data. -/
theorem sylvesterBackwardErrorInf_two_sided_sqrt_xiSq_of_svdOptimalPerturbations
    (n : Nat)
    (A B C Y U V : Fin n -> Fin n -> Real) (sigma : Fin n -> Real)
    (alpha beta gamma : Real)
    (hSVD : IsSVD n Y U V sigma)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hpos : forall i j : Fin n,
      0 < alpha ^ 2 * sigma j ^ 2 + beta ^ 2 * sigma i ^ 2 + gamma ^ 2) :
    Real.sqrt
        (xiSq n (svdResidual n U V (sylvesterResidual n A B C Y))
          sigma alpha beta gamma / 3) <=
      sylvesterBackwardErrorInf n A B C Y alpha beta gamma ∧
    sylvesterBackwardErrorInf n A B C Y alpha beta gamma <=
      Real.sqrt
        (xiSq n (svdResidual n U V (sylvesterResidual n A B C Y))
          sigma alpha beta gamma) := by
  constructor
  · exact
      sqrt_xiSq_div_three_le_sylvesterBackwardErrorInf_of_svd n
        A B C Y U V sigma alpha beta gamma hSVD halpha hbeta hgamma hpos
  · exact
      sylvesterBackwardErrorInf_le_sqrt_xiSq_of_svdOptimalPerturbations n
        A B C Y U V sigma alpha beta gamma hSVD hpos










































-- ============================================================
-- (16.21): the structured Lyapunov backward-error infimum is attained
-- ============================================================



















































































































































































































































































































/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
    Chapter 16, Section 16.2.1, equation (16.21): exact-arithmetic
    source-facing two-sided Lyapunov eta/xi infimum bound. This wrapper
    bundles the existing one-sided symmetric-spectral infimum bounds. -/
theorem lyapunovBackwardErrorInf_two_sided_sqrt_lyapunovXiSq_of_symmetric_spectral
    (n : Nat)
    (A C Y U : Fin n -> Fin n -> Real) (lam : Fin n -> Real)
    (alpha gamma : Real)
    (hY : Y = matMul n U (matMul n (diagMatrix lam) (matTranspose U)))
    (hU : IsOrthogonal n U)
    (hC : IsSymmetricFiniteMatrix C) (hYsym : IsSymmetricFiniteMatrix Y)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hpos : forall i j : Fin n,
      0 < 2 * alpha ^ 2 * (lam i ^ 2 + lam j ^ 2) + gamma ^ 2) :
    Real.sqrt
        (lyapunovXiSq n
          (lyapunovSpectralTransform n U (lyapunovResidual n A C Y))
          lam alpha gamma / 2) <=
      lyapunovBackwardErrorInf n A C Y alpha gamma ∧
    lyapunovBackwardErrorInf n A C Y alpha gamma <=
      Real.sqrt
        (lyapunovXiSq n
          (lyapunovSpectralTransform n U (lyapunovResidual n A C Y))
          lam alpha gamma) := by
  constructor
  · exact
      sqrt_lyapunovXiSq_div_two_le_lyapunovBackwardErrorInf_of_symmetric_spectral
        n A C Y U lam alpha gamma hY hU hC hYsym halpha hgamma hpos
  · exact
      lyapunovBackwardErrorInf_le_sqrt_lyapunovXiSq_of_symmetric_spectral
        n A C Y U lam alpha gamma hY hU hC hYsym hpos



























/-- Higham, 2nd ed., Chapter 16, Section 16.2.1, equation (16.21):
    Lyapunov eta infimum bounded by the mu-scaled relative residual. -/
theorem lyapunovBackwardErrorInf_le_mu_relative_residual_of_symmetric_spectral
    (n : Nat)
    (A C Y U : Fin n -> Fin n -> Real) (lam : Fin n -> Real)
    (alpha gamma lamStar : Real)
    (hY : Y = matMul n U (matMul n (diagMatrix lam) (matTranspose U)))
    (hU : IsOrthogonal n U)
    (hC : IsSymmetricFiniteMatrix C) (hYsym : IsSymmetricFiniteMatrix Y)
    (hpos : forall i j : Fin n,
      0 < 2 * alpha ^ 2 * (lam i ^ 2 + lam j ^ 2) + gamma ^ 2)
    (hLam : forall i : Fin n, lamStar ^ 2 <= lam i ^ 2)
    (hDenom : 0 < 4 * alpha ^ 2 * lamStar ^ 2 + gamma ^ 2)
    (hScale : 0 < 2 * alpha * frobNorm Y + gamma) :
    lyapunovBackwardErrorInf n A C Y alpha gamma <=
      lyapunovAmplificationMu alpha gamma (frobNorm Y) lamStar *
        (frobNorm (lyapunovResidual n A C Y) /
          (2 * alpha * frobNorm Y + gamma)) := by
  exact
    le_trans
      (lyapunovBackwardErrorInf_le_sqrt_lyapunovXiSq_of_symmetric_spectral
        n A C Y U lam alpha gamma hY hU hC hYsym hpos)
      (sqrt_lyapunovXiSq_le_mu_relative_residual n Y
        (lyapunovResidual n A C Y) U lam alpha gamma lamStar
        hU hLam hDenom hScale)























/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
    Chapter 16, Section 16.2.1, equation (16.21): exact-arithmetic
    source-facing Lyapunov residual-ratio lower bound. This wrapper uses the
    symmetric-spectral optimizer to discharge the feasible-set nonemptiness
    hypothesis; it is not a rounded solver or estimator. -/
theorem lyapunov_relative_residual_le_backwardErrorInf_of_symmetric_spectral
    (n : Nat)
    (A C Y U : Fin n -> Fin n -> Real) (lam : Fin n -> Real)
    (alpha gamma : Real)
    (hY : Y = matMul n U (matMul n (diagMatrix lam) (matTranspose U)))
    (hU : IsOrthogonal n U)
    (hC : IsSymmetricFiniteMatrix C) (hYsym : IsSymmetricFiniteMatrix Y)
    (hpos : forall i j : Fin n,
      0 < 2 * alpha ^ 2 * (lam i ^ 2 + lam j ^ 2) + gamma ^ 2)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma)
    (hscale : 0 < 2 * alpha * frobNorm Y + gamma) :
    frobNorm (lyapunovResidual n A C Y) /
        (2 * alpha * frobNorm Y + gamma) <=
      lyapunovBackwardErrorInf n A C Y alpha gamma := by
  exact
    lyapunov_relative_residual_le_backwardErrorInf n A C Y alpha gamma
      halpha hgamma hscale
      (lyapunovBackwardErrorValues_nonempty_of_symmetric_spectral n
        A C Y U lam alpha gamma hY hU hC hYsym hpos)






-- ============================================================
-- (16.29): floating-point computed-residual dR model
-- ============================================================

/-- Elementary gamma bound: `u ≤ γ₁`. -/
lemma u_le_gamma_one (fp : FPModel) (h1 : gammaValid fp 1) :
    fp.u ≤ gamma fp 1 := by
  have h1' : ((1 : ℕ) : ℝ) * fp.u < 1 := h1
  have hden : (0 : ℝ) < 1 - ((1 : ℕ) : ℝ) * fp.u := by linarith
  unfold gamma
  rw [le_div_iff₀ hden]
  push_cast
  nlinarith [fp.u_nonneg, sq_nonneg fp.u]

/-- Elementary gamma bound: `2u + u² ≤ γ₂`. -/
lemma two_u_add_u_sq_le_gamma_two (fp : FPModel) (h2 : gammaValid fp 2) :
    2 * fp.u + fp.u ^ 2 ≤ gamma fp 2 := by
  have h2' : ((2 : ℕ) : ℝ) * fp.u < 1 := h2
  have hden : (0 : ℝ) < 1 - ((2 : ℕ) : ℝ) * fp.u := by linarith
  unfold gamma
  rw [le_div_iff₀ hden]
  push_cast
  nlinarith [fp.u_nonneg, sq_nonneg fp.u]

/-- Gamma coefficient consolidation for the subtract-then-scale path of the
    computed Sylvester residual: `(2u + u²) + (1+u)² γₘ ≤ γₘ₊₂`. -/
lemma sub_then_scale_coeff_le_gamma (fp : FPModel) (m : ℕ)
    (hval : gammaValid fp (m + 2)) :
    (2 * fp.u + fp.u ^ 2) + (1 + fp.u) ^ 2 * gamma fp m ≤ gamma fp (m + 2) := by
  have h2 : gammaValid fp 2 := gammaValid_mono fp (by omega) hval
  have hm : gammaValid fp m := gammaValid_mono fp (by omega) hval
  have hγm : 0 ≤ gamma fp m := gamma_nonneg fp hm
  have hc2 : 2 * fp.u + fp.u ^ 2 ≤ gamma fp 2 :=
    two_u_add_u_sq_le_gamma_two fp h2
  have hexp : (1 + fp.u) ^ 2 = 1 + (2 * fp.u + fp.u ^ 2) := by ring
  have hsq : (1 + fp.u) ^ 2 ≤ 1 + gamma fp 2 := by
    rw [hexp]
    linarith
  have hmul : (1 + fp.u) ^ 2 * gamma fp m ≤ (1 + gamma fp 2) * gamma fp m :=
    mul_le_mul_of_nonneg_right hsq hγm
  have hsum : gamma fp m + gamma fp 2 + gamma fp m * gamma fp 2 ≤
      gamma fp (m + 2) :=
    gamma_sum_le fp m 2 hval
  have hprod : (1 + gamma fp 2) * gamma fp m =
      gamma fp m + gamma fp m * gamma fp 2 := by ring
  linarith

/-- Gamma coefficient consolidation for the add-then-scale path of the
    computed Sylvester residual: `u + (1+u) γₙ ≤ γₙ₊₁`. -/
lemma add_then_scale_coeff_le_gamma (fp : FPModel) (n : ℕ)
    (hval : gammaValid fp (n + 1)) :
    fp.u + (1 + fp.u) * gamma fp n ≤ gamma fp (n + 1) := by
  have h1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hval
  have hn : gammaValid fp n := gammaValid_mono fp (by omega) hval
  have hγn : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hc1 : fp.u ≤ gamma fp 1 := u_le_gamma_one fp h1
  have hmul : (1 + fp.u) * gamma fp n ≤ (1 + gamma fp 1) * gamma fp n :=
    mul_le_mul_of_nonneg_right (by linarith) hγn
  have hsum : gamma fp n + gamma fp 1 + gamma fp n * gamma fp 1 ≤
      gamma fp (n + 1) :=
    gamma_sum_le fp n 1 hval
  have hprod : (1 + gamma fp 1) * gamma fp n =
      gamma fp n + gamma fp n * gamma fp 1 := by ring
  linarith









/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29): the floating-point computed Sylvester residual
    `Rhat = fl(C - A*Xhat + Xhat*B)`.  The two matrix products are the
    repository's column-wise `fl_matMul`, and the combination is evaluated as
    `fl(fl(C - (A*Xhat)) + (Xhat*B))`, one rounded subtraction followed by one
    rounded addition per entry. -/
noncomputable def flSylvesterResidualRect (fp : FPModel) (m n : ℕ)
    (A : RMatFn m m) (B : RMatFn n n) (C Xhat : RMatFn m n) : RMatFn m n :=
  fun i j =>
    fp.fl_add (fp.fl_sub (C i j) (fl_matMul fp m m n A Xhat i j))
      (fl_matMul fp m n n Xhat B i j)

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29): the entrywise rounding budget `Ru` for the computed residual,
    the natural gamma-weighted combination of `|A||Xhat|`, `|Xhat||B|`, and
    `|C|` produced by the floating-point evaluation of
    `fl(fl(C - (A*Xhat)) + (Xhat*B))`. -/
noncomputable def flSylvesterResidualBudget (fp : FPModel) (m n : ℕ)
    (A : RMatFn m m) (B : RMatFn n n) (C Xhat : RMatFn m n) : RMatFn m n :=
  fun i j =>
    gamma fp (m + 2) * (∑ k : Fin m, |A i k| * |Xhat k j|) +
      gamma fp (n + 1) * (∑ k : Fin n, |Xhat i k| * |B k j|) +
      gamma fp 2 * |C i j|

/-- The computed-residual budget of eq (16.29) is entrywise nonnegative. -/
lemma flSylvesterResidualBudget_nonneg (fp : FPModel) (m n : ℕ)
    (A : RMatFn m m) (B : RMatFn n n) (C Xhat : RMatFn m n)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1)) :
    ∀ i j, 0 ≤ flSylvesterResidualBudget fp m n A B C Xhat i j := by
  intro i j
  have h2 : gammaValid fp 2 := gammaValid_mono fp (by omega) hm
  have hS1 : (0 : ℝ) ≤ ∑ k : Fin m, |A i k| * |Xhat k j| :=
    Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hS2 : (0 : ℝ) ≤ ∑ k : Fin n, |Xhat i k| * |B k j| :=
    Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  exact add_nonneg
    (add_nonneg (mul_nonneg (gamma_nonneg fp hm) hS1)
      (mul_nonneg (gamma_nonneg fp hn) hS2))
    (mul_nonneg (gamma_nonneg fp h2) (abs_nonneg _))


























































































































































































































































































































































































































































































































































/-- Higham, 2nd ed., Chapter 16, equation (16.29), Lyapunov specialization
    of the determinant practical computed-residual certificate. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru
      hdet hXSylv hBudget hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), scalar Lyapunov
    specialization of the determinant practical certificate. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) (eta : Real)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru eta
      hdet hXSylv hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), monotone Lyapunov
    specialization of the determinant practical certificate. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru'
      PinvAbs' hdet hXSylv hBudget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), monotone scalar Lyapunov
    specialization of the determinant practical certificate. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru'
      PinvAbs' eta hdet hXSylv hBudget hPinvAbs_le hRhat hRu_le
      heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), Lyapunov specialization
    of the determinant practical raw computed-residual budget endpoint. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru
      hdet hXSylv hRu hRhatSylv hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), scalar Lyapunov
    specialization of the determinant practical raw computed-residual budget
    endpoint. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) (eta : Real)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru eta
      hdet hXSylv hRu hRhatSylv heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), monotone Lyapunov
    specialization of the determinant practical raw computed-residual budget
    endpoint with supplied inverse and residual estimates. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_budget i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru'
      PinvAbs' hdet hXSylv hRu hRhatSylv hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), monotone scalar Lyapunov
    specialization of the determinant practical raw computed-residual budget
    endpoint with supplied inverse and residual estimates. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_budget i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru'
      PinvAbs' eta hdet hXSylv hRu hRhatSylv hPinvAbs_le hRhat hRu_le
      heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), Lyapunov specialization
    of the determinant practical explicit residual-error model endpoint. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru dR
      hdet hXSylv hRhatSylv hRu hdR hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), scalar Lyapunov
    specialization of the determinant practical explicit residual-error model
    endpoint. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n) (eta : Real)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru dR eta
      hdet hXSylv hRhatSylv hRu hdR heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), monotone Lyapunov
    specialization of the determinant practical explicit residual-error model
    endpoint with supplied inverse and residual estimates. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_eq i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru' dR
      PinvAbs' hdet hXSylv hPinvAbs_le hRhatSylv hRu hdR
      hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), monotone scalar Lyapunov
    specialization of the determinant practical explicit residual-error model
    endpoint with supplied inverse and residual estimates. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_eq i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru' dR
      PinvAbs' eta hdet hXSylv hPinvAbs_le hRhatSylv hRu hdR
      hRhat_le hRu_le heta hcomponent hXhat









































































/-- Higham, 2nd ed., Chapter 16, equation (16.29), Lyapunov practical
    computed-residual certificate from a supplied positive separation lower
    bound. -/
theorem lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_certificate
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A C X Xhat Rhat Ru hdet hX hBudget hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), scalar Lyapunov practical
    computed-residual certificate from a supplied positive separation lower
    bound. -/
theorem lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_certificate_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A C X Xhat Rhat Ru eta hdet hX hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), monotone Lyapunov
    practical computed-residual certificate from a supplied positive
    separation lower bound. -/
theorem lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_certificate_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A C X Xhat Rhat Rhat' Ru Ru' PinvAbs' hdet hX hBudget
      hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), monotone scalar Lyapunov
    practical computed-residual certificate from a supplied positive
    separation lower bound. -/
theorem lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta hdet hX hBudget
      hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

























/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov raw residual-budget endpoint from
    `SepLowerBound(A,-A^T)`: the separation certificate gives determinant
    nonsingularity, while the residual and residual-rounding budget stay in
    Lyapunov notation. -/
theorem lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_budget
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget
      n A C X Xhat Rhat Ru hdet hX hRu hRhat hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov raw residual-budget endpoint from
    `SepLowerBound(A,-A^T)`: the practical budget is capped by `eta`. -/
theorem lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_budget_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar
      n A C X Xhat Rhat Ru eta hdet hX hRu hRhat heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov raw residual-budget endpoint from
    `SepLowerBound(A,-A^T)`: enlarged inverse and residual budgets preserve the
    practical error bound. -/
theorem lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_budget_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
      n A C X Xhat Rhat Rhat' Ru Ru' PinvAbs' hdet hX hRu
      hRhat_budget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov raw residual-budget
    endpoint from `SepLowerBound(A,-A^T)`: an `eta` cap on the enlarged
    practical budget gives the source-shaped relative bound. -/
theorem lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_budget_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
      n A C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta hdet hX hRu
      hRhat_budget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov explicit residual-error-model endpoint
    from `SepLowerBound(A,-A^T)`: `Rhat = residual + dR` with a componentwise
    bound on `dR`. -/
theorem lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_error_model
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model
      n A C X Xhat Rhat Ru dR hdet hX hRhat hRu hdR hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov explicit residual-error-model
    endpoint from `SepLowerBound(A,-A^T)`. -/
theorem lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_error_model_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar
      n A C X Xhat Rhat Ru dR eta hdet hX hRhat hRu hdR heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov explicit residual-error-model
    endpoint from `SepLowerBound(A,-A^T)`. -/
theorem lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_error_model_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
      n A C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' hdet hX
      hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov explicit
    residual-error-model endpoint from `SepLowerBound(A,-A^T)`. -/
theorem lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
      n A C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' eta hdet hX
      hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le heta hcomponent hXhat

















































/-- Higham, 2nd ed., Chapter 16, equation (16.29), Lyapunov practical
    computed-residual certificate from a supplied operator sigma-min lower
    bound. -/
theorem lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_operator_sigmaMin
      n A sigma hsigma hSigmaMin
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A C X Xhat Rhat Ru hdet hX hBudget hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), scalar Lyapunov practical
    computed-residual certificate from a supplied operator sigma-min lower
    bound. -/
theorem lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_operator_sigmaMin
      n A sigma hsigma hSigmaMin
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A C X Xhat Rhat Ru eta hdet hX hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), monotone Lyapunov
    practical computed-residual certificate from a supplied operator sigma-min
    lower bound. -/
theorem lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_operator_sigmaMin
      n A sigma hsigma hSigmaMin
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A C X Xhat Rhat Rhat' Ru Ru' PinvAbs' hdet hX hBudget
      hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), monotone scalar Lyapunov
    practical computed-residual certificate from a supplied operator sigma-min
    lower bound. -/
theorem lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_operator_sigmaMin
      n A sigma hsigma hSigmaMin
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta hdet hX hBudget
      hPinvAbs_le hRhat hRu_le heta hcomponent hXhat
























































































































/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov raw residual-budget endpoint from a
    supplied operator sigma-min certificate. -/
theorem lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_budget
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_operator_sigmaMin
      n A sigma hsigma hSigmaMin
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget
      n A C X Xhat Rhat Ru hdet hX hRu hRhat hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov raw residual-budget endpoint from
    a supplied operator sigma-min certificate. -/
theorem lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_budget_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_operator_sigmaMin
      n A sigma hsigma hSigmaMin
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar
      n A C X Xhat Rhat Ru eta hdet hX hRu hRhat heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov raw residual-budget endpoint
    from a supplied operator sigma-min certificate. -/
theorem lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_budget_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_operator_sigmaMin
      n A sigma hsigma hSigmaMin
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
      n A C X Xhat Rhat Rhat' Ru Ru' PinvAbs' hdet hX hRu
      hRhat_budget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov raw residual-budget
    endpoint from a supplied operator sigma-min certificate. -/
theorem lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_budget_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_operator_sigmaMin
      n A sigma hsigma hSigmaMin
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
      n A C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta hdet hX hRu
      hRhat_budget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov explicit residual-error-model endpoint
    from a supplied operator sigma-min certificate. -/
theorem lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_operator_sigmaMin
      n A sigma hsigma hSigmaMin
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model
      n A C X Xhat Rhat Ru dR hdet hX hRhat hRu hdR hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov explicit residual-error-model
    endpoint from a supplied operator sigma-min certificate. -/
theorem lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_operator_sigmaMin
      n A sigma hsigma hSigmaMin
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar
      n A C X Xhat Rhat Ru dR eta hdet hX hRhat hRu hdR heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov explicit residual-error-model
    endpoint from a supplied operator sigma-min certificate. -/
theorem lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_operator_sigmaMin
      n A sigma hsigma hSigmaMin
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
      n A C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' hdet hX
      hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov explicit
    residual-error-model endpoint from a supplied operator sigma-min
    certificate. -/
theorem lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_operator_sigmaMin
      n A sigma hsigma hSigmaMin
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
      n A C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' eta hdet hX
      hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le heta hcomponent hXhat

















































/-- Higham, 2nd ed., Chapter 16, equation (16.29), Lyapunov practical
    computed-residual certificate from a positive lower bound on the exact
    separation infimum. -/
theorem lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
      (fun i j => -matTranspose A i j) sigma hsigma hle
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A C X Xhat Rhat Ru hdet hX hBudget hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), scalar Lyapunov practical
    computed-residual certificate from a positive lower bound on the exact
    separation infimum. -/
theorem lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
      (fun i j => -matTranspose A i j) sigma hsigma hle
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A C X Xhat Rhat Ru eta hdet hX hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), monotone Lyapunov
    practical computed-residual certificate from a positive lower bound on the
    exact separation infimum. -/
theorem lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
      (fun i j => -matTranspose A i j) sigma hsigma hle
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A C X Xhat Rhat Rhat' Ru Ru' PinvAbs' hdet hX hBudget
      hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), monotone scalar Lyapunov
    practical computed-residual certificate from a positive lower bound on the
    exact separation infimum. -/
theorem lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
      (fun i j => -matTranspose A i j) sigma hsigma hle
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta hdet hX hBudget
      hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov raw residual-budget endpoint from a
    positive lower bound on the exact `sylvesterSepInf` for `(A,-A^T)`. -/
theorem lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
      (fun i j => -matTranspose A i j) sigma hsigma hle
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget
      n A C X Xhat Rhat Ru hdet hX hRu hRhat hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov raw residual-budget endpoint from a
    positive exact-infimum certificate for `(A,-A^T)`. -/
theorem lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
      (fun i j => -matTranspose A i j) sigma hsigma hle
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar
      n A C X Xhat Rhat Ru eta hdet hX hRu hRhat heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov raw residual-budget endpoint from
    a positive exact-infimum certificate for `(A,-A^T)`. -/
theorem lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
      (fun i j => -matTranspose A i j) sigma hsigma hle
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
      n A C X Xhat Rhat Rhat' Ru Ru' PinvAbs' hdet hX hRu
      hRhat_budget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov raw residual-budget
    endpoint from a positive exact-infimum certificate for `(A,-A^T)`. -/
theorem lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
      (fun i j => -matTranspose A i j) sigma hsigma hle
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
      n A C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta hdet hX hRu
      hRhat_budget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov explicit residual-error-model endpoint
    from a positive exact-infimum certificate for `(A,-A^T)`. -/
theorem lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
      (fun i j => -matTranspose A i j) sigma hsigma hle
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model
      n A C X Xhat Rhat Ru dR hdet hX hRhat hRu hdR hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov explicit residual-error-model
    endpoint from a positive exact-infimum certificate for `(A,-A^T)`. -/
theorem lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
      (fun i j => -matTranspose A i j) sigma hsigma hle
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar
      n A C X Xhat Rhat Ru dR eta hdet hX hRhat hRu hdR heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov explicit residual-error-model
    endpoint from a positive exact-infimum certificate for `(A,-A^T)`. -/
theorem lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
      (fun i j => -matTranspose A i j) sigma hsigma hle
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
      n A C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' hdet hX
      hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov explicit
    residual-error-model endpoint from a positive exact-infimum certificate for
    `(A,-A^T)`. -/
theorem lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
      (fun i j => -matTranspose A i j) sigma hsigma hle
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
      n A C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' eta hdet hX
      hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le heta hcomponent hXhat









































































/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square
    arbitrary-coefficient endpoint: a concrete left-inverse finite-op-norm
    certificate gives determinant nonsingularity, which supplies the canonical
    exact inverse budget for a packaged computed-residual certificate. -/
theorem sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_certificate
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hX hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), scalar cap version of the
    concrete left-inverse finite-op-norm computed-residual certificate route. -/
theorem sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_certificate_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) (eta : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hX hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), monotone version of the
    concrete left-inverse finite-op-norm computed-residual certificate route. -/
theorem sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_certificate_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hX hBudget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), monotone scalar cap
    version of the concrete left-inverse finite-op-norm certificate route. -/
theorem sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real) {M : Real} (hM : 0 < M)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hX hBudget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square
    arbitrary-coefficient endpoint: a positive finite-Gram eigenvalue
    certificate gives determinant nonsingularity for a packaged
    computed-residual certificate. -/
theorem sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_certificate
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      hX hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), scalar cap version of the
    Gram-eigenvalue computed-residual certificate route. -/
theorem sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_certificate_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      hX hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), monotone version of the
    Gram-eigenvalue computed-residual certificate route. -/
theorem sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_certificate_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      hX hBudget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), monotone scalar cap
    version of the Gram-eigenvalue computed-residual certificate route. -/
theorem sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      hX hBudget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square
    arbitrary-coefficient endpoint: a positive sigma-min certificate gives
    determinant nonsingularity for a packaged computed-residual certificate. -/
theorem sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_certificate
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      hX hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), scalar cap version of the
    sigma-min computed-residual certificate route. -/
theorem sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_certificate_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      hX hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), monotone version of the
    sigma-min computed-residual certificate route. -/
theorem sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_certificate_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      hX hBudget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), monotone scalar cap
    version of the sigma-min computed-residual certificate route. -/
theorem sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      hX hBudget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat









































































/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square
    arbitrary-coefficient endpoint: an operator sigma-min lower-bound
    certificate discharges nonsingularity of the vec/Kronecker Sylvester
    coefficient for a packaged computed-residual certificate. -/
theorem sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
        n A B sigma hsigma hSigmaMin)
      hX hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), scalar cap endpoint:
    an operator sigma-min lower-bound certificate discharges nonsingularity
    of the vec/Kronecker Sylvester coefficient. -/
theorem sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
        n A B sigma hsigma hSigmaMin)
      hX hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), monotone endpoint:
    an operator sigma-min lower-bound certificate supplies the nonsingular
    inverse budget before componentwise estimator enlargement. -/
theorem sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
        n A B sigma hsigma hSigmaMin)
      hX hBudget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), monotone scalar endpoint:
    an operator sigma-min lower-bound certificate supplies the nonsingular
    inverse budget before estimator enlargement and a scalar component cap. -/
theorem sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
        n A B sigma hsigma hSigmaMin)
      hX hBudget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient residual-error-model
    endpoint: an operator sigma-min lower-bound certificate discharges
    determinant nonsingularity, and an explicit residual perturbation model
    supplies the computed-residual certificate.  Scope: this is a certificate
    transfer theorem, not a solve algorithm or estimator proof. -/
theorem sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model
      n A B C X Xhat Rhat Ru dR
      (sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
        n A B sigma hsigma hSigmaMin)
      hX hRhat hRu hdR hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), scalar residual-error-model endpoint: an operator
    sigma-min lower-bound certificate discharges determinant nonsingularity,
    and a scalar cap on the practical budget gives the source-shaped relative
    max-entry bound. -/
theorem sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar
      n A B C X Xhat Rhat Ru dR eta
      (sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
        n A B sigma hsigma hSigmaMin)
      hX hRhat hRu hdR heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), monotone residual-error-model endpoint: an operator
    sigma-min lower-bound certificate supplies determinant nonsingularity,
    while componentwise larger practical estimates preserve the bound. -/
theorem sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
        n A B sigma hsigma hSigmaMin)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), monotone scalar residual-error-model endpoint: after
    componentwise practical-budget enlargement, a scalar cap gives the
    source-shaped bound under an operator sigma-min lower-bound certificate. -/
theorem sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
        n A B sigma hsigma hSigmaMin)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget
    endpoint: a concrete finite-op-norm left-inverse certificate for the
    vec/Kronecker Sylvester coefficient supplies determinant nonsingularity,
    and the caller supplies the absolute computed-residual budget directly.
    Scope: square coefficients; this is a non-floating residual-budget adapter,
    not a solve algorithm or estimator proof. -/
theorem sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n)
    (Pinv :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hX hRu hRhat hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget
    endpoint: a positive finite-Gram eigenvalue certificate for the
    vec/Kronecker Sylvester coefficient supplies determinant nonsingularity,
    and the caller supplies the absolute computed-residual budget directly.
    Scope: square coefficients; this is a non-floating residual-budget adapter,
    not a solve algorithm or estimator proof. -/
theorem sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      hX hRu hRhat hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget
    endpoint: a positive sigma-min lower-bound certificate for the
    vec/Kronecker Sylvester coefficient supplies determinant nonsingularity,
    and the caller supplies the absolute computed-residual budget directly.
    Scope: square coefficients; this is a non-floating residual-budget adapter,
    not a solve algorithm or estimator proof. -/
theorem sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      hX hRu hRhat hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient residual-error-model
    endpoint: a concrete finite-op-norm left-inverse certificate supplies
    determinant nonsingularity, and an explicit residual perturbation model
    supplies the computed-residual certificate.  Scope: this is a certificate
    transfer theorem, not a solve algorithm or estimator proof. -/
theorem sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n)
    (Pinv :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model
      n A B C X Xhat Rhat Ru dR
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hX hRhat hRu hdR hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient residual-error-model
    endpoint: a positive finite-Gram eigenvalue certificate supplies
    determinant nonsingularity, and an explicit residual perturbation model
    supplies the computed-residual certificate.  Scope: this is a certificate
    transfer theorem, not a solve algorithm or estimator proof. -/
theorem sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model
      n A B C X Xhat Rhat Ru dR
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      hX hRhat hRu hdR hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient residual-error-model
    endpoint: a positive sigma-min lower-bound certificate supplies
    determinant nonsingularity, and an explicit residual perturbation model
    supplies the computed-residual certificate.  Scope: this is a certificate
    transfer theorem, not a solve algorithm or estimator proof. -/
theorem sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model
      n A B C X Xhat Rhat Ru dR
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      hX hRhat hRu hdR hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient residual-error-model
    scalar endpoint: a concrete finite-op-norm left-inverse certificate
    supplies determinant nonsingularity, and a scalar cap on the practical
    budget gives the source-shaped relative max-entry bound. -/
theorem sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n)
    (Pinv :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar
      n A B C X Xhat Rhat Ru dR eta
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hX hRhat hRu hdR heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient residual-error-model
    monotone endpoint: a concrete finite-op-norm left-inverse certificate
    supplies determinant nonsingularity, while componentwise larger practical
    estimates preserve the bound.  This is a certificate-transfer theorem, not
    an estimator correctness result. -/
theorem sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (Pinv PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient residual-error-model
    monotone scalar endpoint: after componentwise practical-budget
    enlargement, a scalar cap gives the source-shaped bound under a concrete
    finite-op-norm left-inverse certificate. -/
theorem sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (Pinv PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient residual-error-model
    scalar endpoint: a positive finite-Gram eigenvalue certificate supplies
    determinant nonsingularity, and a scalar cap on the practical budget gives
    the source-shaped relative max-entry bound. -/
theorem sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar
      n A B C X Xhat Rhat Ru dR eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      hX hRhat hRu hdR heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient residual-error-model
    monotone endpoint: a positive finite-Gram eigenvalue certificate supplies
    determinant nonsingularity, while componentwise larger practical estimates
    preserve the bound.  This is a certificate-transfer theorem, not an
    estimator correctness result. -/
theorem sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient residual-error-model
    monotone scalar endpoint: after componentwise practical-budget
    enlargement, a scalar cap gives the source-shaped bound under a positive
    finite-Gram eigenvalue certificate. -/
theorem sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient residual-error-model
    scalar endpoint: a positive sigma-min lower-bound certificate supplies
    determinant nonsingularity, and a scalar cap on the practical budget gives
    the source-shaped relative max-entry bound. -/
theorem sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar
      n A B C X Xhat Rhat Ru dR eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      hX hRhat hRu hdR heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient residual-error-model
    monotone endpoint: a positive sigma-min lower-bound certificate supplies
    determinant nonsingularity, while componentwise larger practical estimates
    preserve the bound.  This is a certificate-transfer theorem, not an
    estimator correctness result. -/
theorem sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient residual-error-model
    monotone scalar endpoint: after componentwise practical-budget
    enlargement, a scalar cap gives the source-shaped bound under a positive
    sigma-min lower-bound certificate. -/
theorem sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le heta hcomponent hXhat









































































/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget scalar
    endpoint: a concrete finite-op-norm left-inverse certificate supplies
    determinant nonsingularity, and a scalar cap on the practical budget gives
    the source-shaped relative max-entry bound. -/
theorem sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n)
    (Pinv :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hX hRu hRhat heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget
    monotone endpoint: a concrete finite-op-norm left-inverse certificate
    supplies determinant nonsingularity, while componentwise larger practical
    estimates preserve the bound. -/
theorem sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (Pinv PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hX hRu hRhat_budget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget
    monotone scalar endpoint: after componentwise estimator enlargement, a
    scalar cap on the enlarged practical budget gives the source-shaped bound
    under a concrete finite-op-norm left-inverse certificate. -/
theorem sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (Pinv PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hX hRu hRhat_budget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget
    endpoint: an operator sigma-min lower-bound certificate supplies
    determinant nonsingularity, and the caller supplies the absolute computed
    residual budget directly.  Scope: this is a non-floating residual-budget
    adapter, not a solve algorithm or estimator proof. -/
theorem sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_budget
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
        n A B sigma hsigma hSigmaMin)
      hX hRu hRhat hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget scalar
    endpoint: an operator sigma-min lower-bound certificate supplies
    determinant nonsingularity, and a scalar cap on the practical budget gives
    the source-shaped relative max-entry bound. -/
theorem sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_budget_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
        n A B sigma hsigma hSigmaMin)
      hX hRu hRhat heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equations (16.26), (16.28), and (16.29), square arbitrary-coefficient
    Frobenius endpoint: a supplied operator sigma-min lower bound and a raw
    computed-residual certificate give the clean relative Frobenius forward
    error bound once the componentwise residual budget has a Frobenius cap.
    Scope: this consumes a residual-budget certificate; it is not a proof that
    a solver or estimator produced the certificate. -/
theorem sylvester_relative_error_le_of_operator_sigmaMin_computed_residual_budget
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) (sigma eta : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  have hExact : forall i j, sylvesterOp n A B X i j = C i j := by
    intro i j
    simpa [IsSylvesterSolutionRect, sylvesterOpRect, sylvesterOp,
      matMulRect_square_eq_matMul] using hX i j
  have hRhat_square : forall i j,
      |sylvesterResidual n A B C Xhat i j - Rhat i j| <= Ru i j := by
    intro i j
    simpa [sylvesterResidualRect, sylvesterResidual, sylvesterOpRect,
      sylvesterOp, matMulRect_square_eq_matMul] using hRhat i j
  have hResidualEntry : forall i j,
      |sylvesterResidual n A B C Xhat i j| <=
        1 * |(|Rhat i j| + Ru i j)| := by
    intro i j
    have hnonneg : 0 <= |Rhat i j| + Ru i j :=
      add_nonneg (abs_nonneg _) (hRu i j)
    calc
      |sylvesterResidual n A B C Xhat i j|
          = |Rhat i j +
              (sylvesterResidual n A B C Xhat i j - Rhat i j)| := by
              congr 1
              ring
      _ <= |Rhat i j| +
            |sylvesterResidual n A B C Xhat i j - Rhat i j| :=
          abs_add_le _ _
      _ <= |Rhat i j| + Ru i j := by
          exact add_le_add (le_refl _) (hRhat_square i j)
      _ = 1 * |(|Rhat i j| + Ru i j)| := by
          rw [abs_of_nonneg hnonneg]
          ring
  have hResidualNorm :
      frobNorm (sylvesterResidual n A B C Xhat) <=
        frobNorm (fun i j => |Rhat i j| + Ru i j) := by
    have h :=
      frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
        (sylvesterResidual n A B C Xhat)
        (fun i j => |Rhat i j| + Ru i j)
        (c := 1) (by norm_num) hResidualEntry
    simpa using h
  exact
    sylvester_relative_error_le_of_sigmaMin_residual_budget n
      A B C X Xhat sigma eta hsigma hSigmaMin hExact hX_pos
      (hResidualNorm.trans hResidualCap)

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equations (16.26), (16.28), and (16.29), square arbitrary-coefficient
    Frobenius endpoint: a source `SepLowerBound` certificate discharges the
    operator sigma-min hypothesis of the clean raw residual-budget theorem. -/
theorem sylvester_relative_error_le_of_sepLowerBound_computed_residual_budget
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma eta : Real}
    (hSep : SepLowerBound n A B sigma)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  exact
    sylvester_relative_error_le_of_operator_sigmaMin_computed_residual_budget
      n A B C X Xhat Rhat Ru sigma eta hSep.1
      (sylvesterOp_sigmaMin_of_sepLowerBound n A B sigma hSep)
      hX hRu hRhat hX_pos hResidualCap

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equations (16.26), (16.28), and (16.29), square arbitrary-coefficient
    Frobenius endpoint: a positive exact lower bound on `sylvesterSepInf`
    supplies the `SepLowerBound` certificate, then the clean raw
    residual-budget conclusion follows. -/
theorem sylvester_relative_error_le_of_pos_le_sylvesterSepInf_computed_residual_budget
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma eta : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  exact
    sylvester_relative_error_le_of_sepLowerBound_computed_residual_budget
      n A B C X Xhat Rhat Ru
      (SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma hsigma hle)
      hX hRu hRhat hX_pos hResidualCap

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equations (16.27)-(16.29), Lyapunov Frobenius endpoint: a supplied
    Lyapunov operator sigma-min lower bound and raw computed-residual budget
    give the clean relative Frobenius forward-error bound. -/
theorem lyapunov_relative_error_le_of_operator_sigmaMin_computed_residual_budget
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) (sigma eta : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  have hSigmaMinSylv : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <=
        frobNorm (sylvesterOp n A (fun i j => -matTranspose A i j) Y) := by
    intro Y
    have h := hSigmaMin Y
    rwa [lyapunovOp_eq_sylvesterOp n A Y] at h
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_relative_error_le_of_operator_sigmaMin_computed_residual_budget
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru sigma eta
      hsigma hSigmaMinSylv hXSylv hRu hRhatSylv hX_pos hResidualCap

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equations (16.27)-(16.29), Lyapunov Frobenius endpoint:
    `SepLowerBound(A,-A^T)` discharges the operator lower-bound hypothesis of
    the clean raw residual-budget theorem. -/
theorem lyapunov_relative_error_le_of_sepLowerBound_computed_residual_budget
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) {sigma eta : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  exact
    lyapunov_relative_error_le_of_operator_sigmaMin_computed_residual_budget
      n A C X Xhat Rhat Ru sigma eta hSep.1
      (lyapunovOp_sigmaMin_of_sepLowerBound n A sigma hSep)
      hX hRu hRhat hX_pos hResidualCap

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equations (16.27)-(16.29), Lyapunov Frobenius endpoint: a positive
    lower bound on the exact `sep(A,-A^T)` infimum supplies the source
    separation certificate and hence the clean residual-budget bound. -/
theorem lyapunov_relative_error_le_of_pos_le_sylvesterSepInf_computed_residual_budget
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) {sigma eta : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  exact
    lyapunov_relative_error_le_of_sepLowerBound_computed_residual_budget
      n A C X Xhat Rhat Ru
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)
      hX hRu hRhat hX_pos hResidualCap






































































































































/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Sylvester Frobenius residual-error-model endpoint:
    an explicit `Rhat = residual + dR` model derives the raw residual-budget
    hypothesis under a source `SepLowerBound(A,B)` certificate. -/
theorem sylvester_relative_error_le_of_sepLowerBound_computed_residual_error_model
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n) {sigma eta : Real}
    (hSep : SepLowerBound n A B sigma)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  have hRhatBudget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j := by
    intro i j
    have hdiff :
        sylvesterResidualRect n n A B C Xhat i j - Rhat i j = -dR i j := by
      rw [hRhat i j]
      ring
    rw [hdiff, abs_neg]
    exact hdR i j
  exact
    sylvester_relative_error_le_of_sepLowerBound_computed_residual_budget
      n A B C X Xhat Rhat Ru hSep hX hRu hRhatBudget hX_pos hResidualCap























/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Sylvester Frobenius residual-error-model endpoint:
    a positive lower bound on `sylvesterSepInf` supplies the separation
    certificate for the explicit computed-residual model. -/
theorem sylvester_relative_error_le_of_pos_le_sylvesterSepInf_computed_residual_error_model
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n) {sigma eta : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  exact
    sylvester_relative_error_le_of_sepLowerBound_computed_residual_error_model
      n A B C X Xhat Rhat Ru dR
      (SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma hsigma hle)
      hX hRhat hRu hdR hX_pos hResidualCap
























/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov Frobenius residual-error-model endpoint:
    an explicit `Rhat = residual + dR` model derives the raw residual-budget
    hypothesis under a source `SepLowerBound(A,-A^T)` certificate. -/
theorem lyapunov_relative_error_le_of_sepLowerBound_computed_residual_error_model
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n) {sigma eta : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  have hRhatBudget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j := by
    intro i j
    have hdiff :
        lyapunovResidual n A C Xhat i j - Rhat i j = -dR i j := by
      rw [hRhat i j]
      ring
    rw [hdiff, abs_neg]
    exact hdR i j
  exact
    lyapunov_relative_error_le_of_sepLowerBound_computed_residual_budget
      n A C X Xhat Rhat Ru hSep hX hRu hRhatBudget hX_pos hResidualCap























/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov Frobenius residual-error-model endpoint:
    a positive lower bound on the exact `sep(A,-A^T)` infimum supplies the
    separation certificate for the explicit computed-residual model. -/
theorem lyapunov_relative_error_le_of_pos_le_sylvesterSepInf_computed_residual_error_model
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n) {sigma eta : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  exact
    lyapunov_relative_error_le_of_sepLowerBound_computed_residual_error_model
      n A C X Xhat Rhat Ru dR
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)
      hX hRhat hRu hdR hX_pos hResidualCap

























/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget
    monotone endpoint: an operator sigma-min lower-bound certificate supplies
    determinant nonsingularity, while componentwise larger practical estimates
    preserve the bound. -/
theorem sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_budget_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
        n A B sigma hsigma hSigmaMin)
      hX hRu hRhat_budget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget
    monotone scalar endpoint: after componentwise estimator enlargement, a
    scalar cap on the enlarged practical budget gives the source-shaped bound
    under an operator sigma-min lower-bound certificate. -/
theorem sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_budget_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
        n A B sigma hsigma hSigmaMin)
      hX hRu hRhat_budget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat









































































/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget scalar
    endpoint: a positive finite-Gram eigenvalue certificate supplies
    determinant nonsingularity, and a scalar cap on the practical budget gives
    the source-shaped relative max-entry bound. -/
theorem sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      hX hRu hRhat heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget
    monotone endpoint: a positive finite-Gram eigenvalue certificate supplies
    determinant nonsingularity, while componentwise larger practical estimates
    preserve the bound. -/
theorem sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      hX hRu hRhat_budget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget
    monotone scalar endpoint: after componentwise estimator enlargement, a
    scalar cap on the enlarged practical budget gives the source-shaped bound
    under a positive finite-Gram eigenvalue certificate. -/
theorem sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      hX hRu hRhat_budget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget scalar
    endpoint: a positive sigma-min lower-bound certificate supplies
    determinant nonsingularity, and a scalar cap on the practical budget gives
    the source-shaped relative max-entry bound. -/
theorem sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      hX hRu hRhat heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget
    monotone endpoint: a positive sigma-min lower-bound certificate supplies
    determinant nonsingularity, while componentwise larger practical estimates
    preserve the bound. -/
theorem sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      hX hRu hRhat_budget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget
    monotone scalar endpoint: after componentwise estimator enlargement, a
    scalar cap on the enlarged practical budget gives the source-shaped bound
    under a positive sigma-min lower-bound certificate. -/
theorem sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      hX hRu hRhat_budget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat





































































/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov-specialized raw residual-budget endpoint:
    a concrete finite-op-norm left inverse for the vec coefficient supplies the
    square practical relative max-entry forward-error bound. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n)
    (Pinv :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hLeft :
      Pinv * sylvesterVecCoeff n n A (fun i j => -matTranspose A i j) = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru Pinv hM
      hXSylv hLeft hPinv hRu hRhatSylv hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov specialization of the raw
    residual-budget endpoint under a concrete finite-op-norm left inverse. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n)
    (Pinv :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hLeft :
      Pinv * sylvesterVecCoeff n n A (fun i j => -matTranspose A i j) = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru Pinv hM eta
      hXSylv hLeft hPinv hRu hRhatSylv heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov raw residual-budget endpoint:
    a concrete finite-op-norm left inverse and larger practical estimates
    preserve the relative max-entry bound. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (Pinv PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hLeft :
      Pinv * sylvesterVecCoeff n n A (fun i j => -matTranspose A i j) = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_budget i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_mono
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru'
      Pinv PinvAbs' hM hXSylv hLeft hPinv hRu hRhatSylv hPinvAbs_le
      hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov raw residual-budget
    endpoint under a concrete finite-op-norm left-inverse certificate. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (Pinv PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hLeft :
      Pinv * sylvesterVecCoeff n n A (fun i j => -matTranspose A i j) = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_budget i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_mono_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru'
      Pinv PinvAbs' hM eta hXSylv hLeft hPinv hRu hRhatSylv hPinvAbs_le
      hRhat hRu_le heta hcomponent hXhat

























/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov-specialized raw residual-budget endpoint:
    positive eigenvalue certificates for the finite Gram matrix of the concrete
    vec coefficient give the practical relative max-entry bound. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))) p)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru
      hlam hEig hXSylv hRu hRhatSylv hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov specialization of the raw
    residual-budget endpoint from concrete Gram-eigenvalue certificates. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))) p)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru
      hlam hEig eta hXSylv hRu hRhatSylv heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov raw residual-budget endpoint from
    concrete Gram-eigenvalue certificates and enlarged practical estimates. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))) p)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_budget i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_mono
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru'
      hlam hEig PinvAbs' hXSylv hRu hRhatSylv hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov raw residual-budget
    endpoint from concrete Gram-eigenvalue certificates. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))) p)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_budget i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_mono_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru'
      hlam hEig PinvAbs' eta hXSylv hRu hRhatSylv hPinvAbs_le hRhat hRu_le
      heta hcomponent hXhat

























/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov-specialized raw residual-budget endpoint:
    a concrete sigma-min lower bound for the vec coefficient gives the
    practical relative max-entry forward-error bound. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2
          (Matrix.mulVec
            (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru
      hsigma hCoeff hXSylv hRu hRhatSylv hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov specialization of the raw
    residual-budget endpoint from a concrete sigma-min certificate. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2
          (Matrix.mulVec
            (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x))
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru
      hsigma hCoeff eta hXSylv hRu hRhatSylv heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov raw residual-budget endpoint from
    a concrete sigma-min certificate and enlarged practical estimates. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2
          (Matrix.mulVec
            (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_budget i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_mono
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru'
      hsigma hCoeff PinvAbs' hXSylv hRu hRhatSylv hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov raw residual-budget
    endpoint from a concrete sigma-min certificate. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2
          (Matrix.mulVec
            (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_budget i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_mono_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru'
      hsigma hCoeff PinvAbs' eta hXSylv hRu hRhatSylv hPinvAbs_le hRhat hRu_le
      heta hcomponent hXhat

























/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov-specialized residual-error-model
    endpoint: a concrete finite-op-norm left inverse for the vec coefficient
    gives the practical relative max-entry forward-error bound. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n)
    (Pinv :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hLeft :
      Pinv * sylvesterVecCoeff n n A (fun i j => -matTranspose A i j) = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru dR Pinv hM
      hXSylv hLeft hPinv hRhatSylv hRu hdR hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov residual-error-model endpoint
    under a concrete finite-op-norm left-inverse certificate. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n)
    (Pinv :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hLeft :
      Pinv * sylvesterVecCoeff n n A (fun i j => -matTranspose A i j) = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru dR Pinv hM eta
      hXSylv hLeft hPinv hRhatSylv hRu hdR heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov residual-error-model endpoint:
    a concrete finite-op-norm left inverse and larger practical estimates
    preserve the relative max-entry bound. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (Pinv PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hLeft :
      Pinv * sylvesterVecCoeff n n A (fun i j => -matTranspose A i j) = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_eq i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_mono
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru' dR
      Pinv PinvAbs' hM hXSylv hLeft hPinv hPinvAbs_le hRhatSylv hRu hdR
      hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov residual-error-model
    endpoint under a concrete finite-op-norm left-inverse certificate. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (Pinv PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hLeft :
      Pinv * sylvesterVecCoeff n n A (fun i j => -matTranspose A i j) = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_eq i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_mono_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru' dR
      Pinv PinvAbs' hM eta hXSylv hLeft hPinv hPinvAbs_le hRhatSylv hRu hdR
      hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov-specialized residual-error-model
    endpoint from concrete Gram-eigenvalue certificates for the vec
    coefficient. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))) p)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru dR
      hlam hEig hXSylv hRhatSylv hRu hdR hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov residual-error-model endpoint from
    concrete Gram-eigenvalue certificates. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))) p)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru dR
      hlam hEig eta hXSylv hRhatSylv hRu hdR heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov residual-error-model endpoint
    from concrete Gram-eigenvalue certificates and enlarged practical
    estimates. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))) p)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_eq i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_mono
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru' dR
      hlam hEig PinvAbs' hXSylv hPinvAbs_le hRhatSylv hRu hdR hRhat hRu_le
      hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov residual-error-model
    endpoint from concrete Gram-eigenvalue certificates. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))) p)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_eq i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_mono_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru' dR
      hlam hEig PinvAbs' eta hXSylv hPinvAbs_le hRhatSylv hRu hdR hRhat
      hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov-specialized residual-error-model
    endpoint from a concrete sigma-min lower bound for the vec coefficient. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2
          (Matrix.mulVec
            (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru dR
      hsigma hCoeff hXSylv hRhatSylv hRu hdR hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov residual-error-model endpoint from
    a concrete sigma-min certificate. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2
          (Matrix.mulVec
            (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x))
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru dR
      hsigma hCoeff eta hXSylv hRhatSylv hRu hdR heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov residual-error-model endpoint
    from a concrete sigma-min certificate and enlarged practical estimates. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2
          (Matrix.mulVec
            (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_eq i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_mono
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru' dR
      hsigma hCoeff PinvAbs' hXSylv hPinvAbs_le hRhatSylv hRu hdR hRhat
      hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov residual-error-model
    endpoint from a concrete sigma-min certificate. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2
          (Matrix.mulVec
            (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_eq i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_mono_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru' dR
      hsigma hCoeff PinvAbs' eta hXSylv hPinvAbs_le hRhatSylv hRu hdR hRhat
      hRu_le heta hcomponent hXhat






















































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































end NumStability
