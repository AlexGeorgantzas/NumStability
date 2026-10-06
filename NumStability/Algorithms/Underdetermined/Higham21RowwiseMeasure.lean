-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- The printed row-wise backward-error measure preceding Theorem 21.4.

import NumStability.Algorithms.Underdetermined.UnderdeterminedSolve

namespace NumStability

/-- Higham, 2nd ed., Chapter 21, Section 21.3: feasibility for the printed
    row-wise backward error `omega^R(y)`.

    Unlike `UndetRowwiseBackwardErrorFeasible`, the printed definition allows
    perturbations of both the matrix and the right-hand side.  Its display
    writes the bound index as `i = 1:n`; since `DeltaA` has `m` rows and
    `Deltab` has `m` entries, and Theorem 21.4 immediately uses `i = 1:m`, the
    bounds here range over `Fin m`. -/
structure Higham21RowwiseBackwardErrorFeasible (m n : Nat)
    (A DeltaA : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real)
    (y : Fin n -> Real) (eta : Real) : Prop where
  /-- The error radius is nonnegative. -/
  eta_nonneg : 0 <= eta
  /-- `y` is the minimum 2-norm solution of the perturbed system. -/
  min_norm :
    RectMinNormSolution m n
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i) y
  /-- Every matrix row obeys the source's relative Euclidean bound. -/
  row_bound :
    forall i : Fin m,
      rectRowNorm2 DeltaA i <= eta * rectRowNorm2 A i
  /-- Every right-hand-side entry obeys the source's relative bound. -/
  rhs_bound :
    forall i : Fin m, abs (Deltab i) <= eta * abs (b i)

/-- Feasible radii in Higham's printed row-wise backward-error definition. -/
def higham21RowwiseBackwardErrorValuesR {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (b : Fin m -> Real) (y : Fin n -> Real) : Set Real :=
  {eta | exists (DeltaA : Fin m -> Fin n -> Real) (Deltab : Fin m -> Real),
    Higham21RowwiseBackwardErrorFeasible
      m n A DeltaA b Deltab y eta}

/-- Infimum model of the source's minimum-style row-wise backward error
    `omega^R(y)`. -/
noncomputable def higham21RowwiseBackwardErrorOmegaR {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (b : Fin m -> Real) (y : Fin n -> Real) : Real :=
  sInf (higham21RowwiseBackwardErrorValuesR A b y)

/-- The feasible-radius set for `omega^R` is bounded below by zero. -/
theorem higham21RowwiseBackwardErrorValuesR.bddBelow {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (b : Fin m -> Real) (y : Fin n -> Real) :
    BddBelow (higham21RowwiseBackwardErrorValuesR A b y) := by
  refine ⟨0, ?_⟩
  intro eta heta
  rcases heta with ⟨DeltaA, Deltab, hfeas⟩
  exact hfeas.eta_nonneg

/-- The infimum model of the printed row-wise backward error is nonnegative. -/
theorem higham21RowwiseBackwardErrorOmegaR_nonneg {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (b : Fin m -> Real) (y : Fin n -> Real) :
    0 <= higham21RowwiseBackwardErrorOmegaR A b y := by
  unfold higham21RowwiseBackwardErrorOmegaR
  apply Real.sInf_nonneg
  intro eta heta
  rcases heta with ⟨DeltaA, Deltab, hfeas⟩
  exact hfeas.eta_nonneg

/-- Any printed row-wise feasible perturbation bounds `omega^R` from above. -/
theorem higham21RowwiseBackwardErrorOmegaR_le_of_feasible
    {m n : Nat}
    (A DeltaA : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real)
    (y : Fin n -> Real) (eta : Real)
    (hfeas : Higham21RowwiseBackwardErrorFeasible
      m n A DeltaA b Deltab y eta) :
    higham21RowwiseBackwardErrorOmegaR A b y <= eta := by
  unfold higham21RowwiseBackwardErrorOmegaR
  exact csInf_le
    (higham21RowwiseBackwardErrorValuesR.bddBelow A b y)
    ⟨DeltaA, Deltab, hfeas⟩

/-- The repository's existing row-wise witness is a witness for Higham's
    printed predicate after taking `Deltab = 0`. -/
theorem Higham21RowwiseBackwardErrorFeasible.of_fixed_b
    {m n : Nat}
    {A DeltaA : Fin m -> Fin n -> Real}
    {b : Fin m -> Real} {y : Fin n -> Real} {eta : Real}
    (hfeas : UndetRowwiseBackwardErrorFeasible m n A DeltaA b y eta) :
    Higham21RowwiseBackwardErrorFeasible
      m n A DeltaA b (0 : Fin m -> Real) y eta := by
  refine ⟨hfeas.eta_nonneg, ?_, hfeas.row_bound, ?_⟩
  · simpa using hfeas.min_norm
  · intro i
    simpa using mul_nonneg hfeas.eta_nonneg (abs_nonneg (b i))

/-- A stronger fixed-right-hand-side certificate supplies a feasible radius
    for the printed two-perturbation row-wise measure. -/
theorem higham21RowwiseBackwardErrorValuesR.mem_of_fixed_b_certificate
    {m n : Nat}
    {A : Fin m -> Fin n -> Real}
    {b : Fin m -> Real} {y : Fin n -> Real} {eta : Real}
    (hcert : UndetRowwiseBackwardErrorBounded m n A b y eta) :
    eta ∈ higham21RowwiseBackwardErrorValuesR A b y := by
  rcases hcert with ⟨DeltaA, hfeas⟩
  exact ⟨DeltaA, (0 : Fin m -> Real),
    Higham21RowwiseBackwardErrorFeasible.of_fixed_b hfeas⟩

/-- The existing fixed-`b` row-wise certificate implies the printed
    backward-error bound. -/
theorem higham21RowwiseBackwardErrorOmegaR_le_of_fixed_b_certificate
    {m n : Nat}
    {A : Fin m -> Fin n -> Real}
    {b : Fin m -> Real} {y : Fin n -> Real} {eta : Real}
    (hcert : UndetRowwiseBackwardErrorBounded m n A b y eta) :
    higham21RowwiseBackwardErrorOmegaR A b y <= eta := by
  unfold higham21RowwiseBackwardErrorOmegaR
  exact csInf_le
    (higham21RowwiseBackwardErrorValuesR.bddBelow A b y)
    (higham21RowwiseBackwardErrorValuesR.mem_of_fixed_b_certificate hcert)

/-- Higham, 2nd ed., Chapter 21, Theorem 21.4: the actual rounded Q-method
    output satisfies the printed `omega^R` bound.  The full-row-rank computed
    QR domain, gamma validity, and explicit condition-number smallness are
    exactly the hypotheses of the existing fixed-`b` certificate. -/
theorem higham21_theorem21_4_computed_qhat_omegaR_le_gamma
    {m k : Nat} (fp : FPModel)
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp (Higham21QMethodRoundedGammaIndex m k))
    (hCondSmall :
      gamma fp (Higham21QMethodRoundedGammaIndex m k) *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) < 1) :
    let Q_hat := fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
    let R_hat : Fin m -> Fin m -> Real := fun i j =>
      fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
        (Fin.castAdd k i) j
    let y1 := fl_forwardSub fp m (matTranspose R_hat) b
    let x_hat := matMulVec (m + k) Q_hat
      (Fin.append y1 (0 : Fin k -> Real))
    higham21RowwiseBackwardErrorOmegaR A b x_hat <=
      gamma fp (Higham21QMethodRoundedGammaIndex m k) := by
  dsimp only
  exact higham21RowwiseBackwardErrorOmegaR_le_of_fixed_b_certificate
    (higham21_theorem21_4_computed_qhat_rowwise_backward_stable_gamma
      fp A b hm hdomain hvalid hCondSmall)

end NumStability
