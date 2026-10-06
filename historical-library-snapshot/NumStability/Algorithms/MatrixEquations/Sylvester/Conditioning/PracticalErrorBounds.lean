import Mathlib.LinearAlgebra.Matrix.Vec
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Diagonal
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Rectangular
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Vectorization
import NumStability.Analysis.MatrixAlgebra

/-!
# Algorithms.MatrixEquations.Sylvester.Conditioning.PracticalErrorBounds

W05 semantic leaf. Declaration commands are copied byte-identically from the frozen C0004 owners.
-/

-- Algorithms/Sylvester/Higham16.lean
--
-- Source-facing Chapter 16 surfaces for Higham, Accuracy and Stability of
-- Numerical Algorithms, 2nd ed.  This file complements the older square
-- Frobenius-norm Sylvester infrastructure in `SylvesterSpec`,
-- `SylvesterBackward`, and `SylvesterPerturbation`.





namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- Rectangular source equations
-- ============================================================

























































-- ============================================================
-- Vec/Kronecker formulation from Chapter 16.1
-- ============================================================
































































































































































































































-- ============================================================
-- Practical max-entry error bounds from Chapter 16.4
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    the vector max norm on a vectorized rectangular matrix, using Mathlib's
    finite-function sup norm. -/
noncomputable def sylvesterVecMaxNorm (m n : Nat)
    (v : Prod (Fin n) (Fin m) -> Real) : Real :=
  norm v

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    `||X|| := max_{i,j} |x_ij|`, represented as the vector max norm of
    `vec(X)` in column-stacking order. -/
noncomputable def sylvesterMaxEntryNormRect (m n : Nat)
    (X : RMatFn m n) : Real :=
  sylvesterVecMaxNorm m n (Matrix.vec X)

lemma sylvesterVecMaxNorm_nonneg (m n : Nat)
    (v : Prod (Fin n) (Fin m) -> Real) :
    0 <= sylvesterVecMaxNorm m n v := by
  unfold sylvesterVecMaxNorm
  exact norm_nonneg v

lemma abs_le_sylvesterVecMaxNorm (m n : Nat)
    (v : Prod (Fin n) (Fin m) -> Real) (p : Prod (Fin n) (Fin m)) :
    |v p| <= sylvesterVecMaxNorm m n v := by
  unfold sylvesterVecMaxNorm
  simpa [Real.norm_eq_abs] using norm_le_pi_norm v p

lemma sylvesterVecMaxNorm_le_of_abs_le (m n : Nat)
    (v : Prod (Fin n) (Fin m) -> Real) {c : Real}
    (h : forall p : Prod (Fin n) (Fin m), |v p| <= c) (hc : 0 <= c) :
    sylvesterVecMaxNorm m n v <= c := by
  unfold sylvesterVecMaxNorm
  rw [pi_norm_le_iff_of_nonneg hc]
  intro p
  simpa [Real.norm_eq_abs] using h p

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    the practical componentwise budget vector
    `|P^{-1}| (|vec(Rhat)| + vec(Ru))`.  The matrix `PinvAbs` represents
    an entrywise nonnegative upper bound for `|P^{-1}|`, and `Ru` is the
    nonnegative residual-rounding budget. -/
noncomputable def sylvesterPracticalBudgetVec (m n : Nat)
    (PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (Rhat Ru : RMatFn m n) : Prod (Fin n) (Fin m) -> Real :=
  fun p =>
    Finset.sum Finset.univ fun q : Prod (Fin n) (Fin m) =>
      PinvAbs p q * (|Matrix.vec Rhat q| + Matrix.vec Ru q)

lemma sylvesterPracticalBudgetVec_nonneg (m n : Nat)
    (PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (Rhat Ru : RMatFn m n)
    (hPinvAbs : forall p q, 0 <= PinvAbs p q)
    (hRu : forall i j, 0 <= Ru i j) :
    forall p, 0 <= sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru p := by
  intro p
  unfold sylvesterPracticalBudgetVec
  exact Finset.sum_nonneg fun q _ =>
    mul_nonneg (hPinvAbs p q)
      (add_nonneg (abs_nonneg _)
        (by simpa [Matrix.vec] using hRu q.2 q.1))

/-- If one nonnegative vector budget dominates another componentwise, it also
    dominates it in the source max-entry norm used in equation (16.29). -/
lemma sylvesterVecMaxNorm_mono_of_nonneg (m n : Nat)
    {v w : Prod (Fin n) (Fin m) -> Real}
    (hv : forall p, 0 <= v p)
    (hle : forall p, v p <= w p) :
    sylvesterVecMaxNorm m n v <= sylvesterVecMaxNorm m n w := by
  unfold sylvesterVecMaxNorm
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg w)]
  intro p
  calc
    |v p| = v p := abs_of_nonneg (hv p)
    _ <= w p := hle p
    _ <= |w p| := le_abs_self (w p)
    _ <= norm w := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm w p

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    the practical budget is monotone in the inverse-entry bound, the
    absolute computed residual, and the residual-rounding budget.  This lets
    later estimator paths replace exact budgets by proved upper estimates. -/
lemma sylvesterPracticalBudgetVec_mono (m n : Nat)
    (PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (Rhat Rhat' Ru Ru' : RMatFn m n)
    (hPinvAbs' : forall p q, 0 <= PinvAbs' p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu : forall i j, 0 <= Ru i j)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    forall p,
      sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru p <=
        sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p := by
  intro p
  unfold sylvesterPracticalBudgetVec
  apply Finset.sum_le_sum
  intro q _
  have hterm :
      |Matrix.vec Rhat q| + Matrix.vec Ru q <=
        |Matrix.vec Rhat' q| + Matrix.vec Ru' q := by
    simpa [Matrix.vec] using
      add_le_add (hRhat q.2 q.1) (hRu_le q.2 q.1)
  have hterm_nonneg :
      0 <= |Matrix.vec Rhat q| + Matrix.vec Ru q := by
    exact add_nonneg (abs_nonneg _)
      (by simpa [Matrix.vec] using hRu q.2 q.1)
  exact mul_le_mul (hPinvAbs_le p q) hterm hterm_nonneg (hPinvAbs' p q)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    max-norm form of monotonicity for the practical budget vector. -/
lemma sylvesterPracticalBudgetVec_maxNorm_mono (m n : Nat)
    (PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (Rhat Rhat' Ru Ru' : RMatFn m n)
    (hPinvAbs : forall p q, 0 <= PinvAbs p q)
    (hPinvAbs' : forall p q, 0 <= PinvAbs' p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu : forall i j, 0 <= Ru i j)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') := by
  apply sylvesterVecMaxNorm_mono_of_nonneg
  · exact sylvesterPracticalBudgetVec_nonneg m n PinvAbs Rhat Ru hPinvAbs hRu
  · exact sylvesterPracticalBudgetVec_mono m n
      PinvAbs PinvAbs' Rhat Rhat' Ru Ru' hPinvAbs' hPinvAbs_le
      hRhat hRu hRu_le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    scalar cap form of the practical budget vector.  If every component of
    the practical `|P^{-1}| (|vec(Rhat)| + vec(Ru))` budget is bounded by
    `eta`, then its source max-entry norm is bounded by `eta`. -/
lemma sylvesterPracticalBudgetVec_maxNorm_le_of_componentwise_le (m n : Nat)
    (PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (Rhat Ru : RMatFn m n) {eta : Real}
    (hPinvAbs : forall p q, 0 <= PinvAbs p q)
    (hRu : forall i j, 0 <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru p <= eta) :
    sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) <= eta := by
  apply sylvesterVecMaxNorm_le_of_abs_le
  · intro p
    rw [abs_of_nonneg
      (sylvesterPracticalBudgetVec_nonneg m n PinvAbs Rhat Ru
        hPinvAbs hRu p)]
    exact hcomponent p
  · exact heta

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    the entrywise absolute-value matrix `|P^{-1}|` for the vec/Kronecker
    Sylvester coefficient `P = I_n kron A - B^T kron I_m`.  The inverse is
    Mathlib's nonsingular matrix inverse; source-facing theorems using this
    definition separately prove the required left-inverse hypothesis. -/
noncomputable def sylvesterVecCoeffNonsingInvAbs (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) :
    Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real :=
  fun p q => |((sylvesterVecCoeff m n A B)⁻¹) p q|

/-- The absolute-value matrix `sylvesterVecCoeffNonsingInvAbs` bounds the
    nonsingular inverse entries componentwise, exactly as required by the
    practical error-budget theorem. -/
lemma sylvesterVecCoeffNonsingInv_abs_le_invAbs (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) :
    forall p q,
      |((sylvesterVecCoeff m n A B)⁻¹) p q| <=
        sylvesterVecCoeffNonsingInvAbs m n A B p q := by
  intro p q
  rfl

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute max-entry
    bridge: a nonnegative componentwise budget for `X - Xhat` bounds the
    practical max-entry forward error before any relative normalization. -/
theorem sylvester_practical_abs_error_bound_of_componentwise_budget (m n : Nat)
    (X Xhat : RMatFn m n) (budget : Prod (Fin n) (Fin m) -> Real)
    (hbudget : forall p, 0 <= budget p)
    (hcert : forall i j, |X i j - Xhat i j| <= budget (j, i)) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm m n budget := by
  unfold sylvesterMaxEntryNormRect
  apply sylvesterVecMaxNorm_le_of_abs_le
  · intro p
    calc
      |Matrix.vec (fun i j => X i j - Xhat i j) p|
          = |X p.2 p.1 - Xhat p.2 p.1| := by
            simp [Matrix.vec]
      _ <= budget p := hcert p.2 p.1
      _ = |budget p| := (abs_of_nonneg (hbudget p)).symm
      _ <= sylvesterVecMaxNorm m n budget :=
        abs_le_sylvesterVecMaxNorm m n budget p
  · exact sylvesterVecMaxNorm_nonneg m n budget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), max-entry norm bridge:
    a nonnegative componentwise budget for `X - Xhat` bounds the relative
    max-entry forward error in the source norm `||X|| := max_{i,j} |x_ij|`. -/
theorem sylvester_practical_error_bound_of_componentwise_budget (m n : Nat)
    (X Xhat : RMatFn m n) (budget : Prod (Fin n) (Fin m) -> Real)
    (hbudget : forall p, 0 <= budget p)
    (hcert : forall i j, |X i j - Xhat i j| <= budget (j, i))
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n budget / sylvesterMaxEntryNormRect m n Xhat := by
  have hnorm :
      sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
        sylvesterVecMaxNorm m n budget := by
    exact
      sylvester_practical_abs_error_bound_of_componentwise_budget m n
        X Xhat budget hbudget hcert
  exact div_le_div_of_nonneg_right hnorm (le_of_lt hXhat)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute certificate
    form: if the vectorized error is `P^{-1} r`, the inverse entries are bounded
    componentwise by `PinvAbs`, and the residual vector satisfies
    `|r| <= |vec(Rhat)| + vec(Ru)`, then the practical budget bounds the
    unnormalized max-entry forward error. -/
theorem sylvester_practical_abs_error_bound_of_inverse_residual_budget (m n : Nat)
    (X Xhat Rhat Ru : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (r : Prod (Fin n) (Fin m) -> Real)
    (hErr : Matrix.vec (fun i j => X i j - Xhat i j) =
      Matrix.mulVec Pinv r)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hr : forall q, |r q| <= |Matrix.vec Rhat q| + Matrix.vec Ru q) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) := by
  have hPinvAbs_nonneg : forall p q, 0 <= PinvAbs p q := by
    intro p q
    exact (abs_nonneg (Pinv p q)).trans (hPinvAbs p q)
  apply sylvester_practical_abs_error_bound_of_componentwise_budget
  · exact sylvesterPracticalBudgetVec_nonneg m n PinvAbs Rhat Ru hPinvAbs_nonneg hRu
  · intro i j
    let p : Prod (Fin n) (Fin m) := (j, i)
    have hp := congrFun hErr p
    have herr :
        X i j - Xhat i j = Matrix.mulVec Pinv r p := by
      simpa [p, Matrix.vec] using hp
    rw [herr]
    calc
      |Matrix.mulVec Pinv r p|
          = |Finset.sum Finset.univ
              (fun q : Prod (Fin n) (Fin m) => Pinv p q * r q)| := by
            simp [Matrix.mulVec, dotProduct]
      _ <= Finset.sum Finset.univ
              (fun q : Prod (Fin n) (Fin m) => |Pinv p q * r q|) :=
            Finset.abs_sum_le_sum_abs _ _
      _ = Finset.sum Finset.univ
              (fun q : Prod (Fin n) (Fin m) => |Pinv p q| * |r q|) := by
            apply Finset.sum_congr rfl
            intro q _
            rw [abs_mul]
      _ <= Finset.sum Finset.univ
              (fun q : Prod (Fin n) (Fin m) =>
                PinvAbs p q * (|Matrix.vec Rhat q| + Matrix.vec Ru q)) := by
            apply Finset.sum_le_sum
            intro q _
            exact mul_le_mul (hPinvAbs p q) (hr q)
              (abs_nonneg (r q)) (hPinvAbs_nonneg p q)
      _ = sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru p := by
            rfl

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), certificate form:
    if the vectorized error is `P^{-1} r`, the inverse entries are bounded
    componentwise by `PinvAbs`, and the residual vector satisfies
    `|r| <= |vec(Rhat)| + vec(Ru)`, then the practical `|P^{-1}|` budget
    gives the relative max-entry forward-error bound. -/
theorem sylvester_practical_error_bound_of_inverse_residual_budget (m n : Nat)
    (X Xhat Rhat Ru : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (r : Prod (Fin n) (Fin m) -> Real)
    (hErr : Matrix.vec (fun i j => X i j - Xhat i j) =
      Matrix.mulVec Pinv r)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hr : forall q, |r q| <= |Matrix.vec Rhat q| + Matrix.vec Ru q)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  have hnorm :
      sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
        sylvesterVecMaxNorm m n
          (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) :=
    sylvester_practical_abs_error_bound_of_inverse_residual_budget m n
      X Xhat Rhat Ru Pinv PinvAbs r hErr hPinvAbs hRu hr
  exact div_le_div_of_nonneg_right hnorm (le_of_lt hXhat)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact residual identity:
    if `X` solves the Sylvester equation, then the exact residual of `Xhat`
    is the Sylvester operator applied to the forward error `X - Xhat`. -/
theorem sylvesterResidualRect_eq_sylvesterOpRect_error (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C X Xhat : RMatFn m n)
    (hX : IsSylvesterSolutionRect m n A B C X) :
    sylvesterResidualRect m n A B C Xhat =
      sylvesterOpRect m n A B (fun i j => X i j - Xhat i j) := by
  ext i j
  have h := hX i j
  unfold sylvesterResidualRect sylvesterOpRect matMulRect at h ⊢
  rw [← h]
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  ring







/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), inverse-residual bridge:
    if `Pinv` is a left inverse for the vec/Kronecker Sylvester coefficient,
    then the vectorized forward error is `Pinv` applied to the exact residual. -/
theorem sylvester_vec_error_eq_inverse_residual_of_left_inverse (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C X Xhat : RMatFn m n)
    (Pinv :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1) :
    Matrix.vec (fun i j => X i j - Xhat i j) =
      Matrix.mulVec Pinv (Matrix.vec (sylvesterResidualRect m n A B C Xhat)) := by
  let P := sylvesterVecCoeff m n A B
  let E : RMatFn m n := fun i j => X i j - Xhat i j
  change Matrix.vec E =
    Matrix.mulVec Pinv (Matrix.vec (sylvesterResidualRect m n A B C Xhat))
  have hLeftP : Pinv * P = 1 := by
    simpa [P] using hLeft
  have hres : Matrix.mulVec P (Matrix.vec E) =
      Matrix.vec (sylvesterResidualRect m n A B C Xhat) := by
    rw [show P = sylvesterVecCoeff m n A B by rfl]
    rw [sylvesterVecCoeff_mulVec_vec]
    rw [sylvesterResidualRect_eq_sylvesterOpRect_error m n A B C X Xhat hX]
  calc
    Matrix.vec E =
        Matrix.mulVec (1 :
          Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
          (Matrix.vec E) := by
            simp
    _ = Matrix.mulVec (Pinv * P) (Matrix.vec E) := by
          rw [hLeftP]
    _ = Matrix.mulVec Pinv (Matrix.mulVec P (Matrix.vec E)) := by
          rw [Matrix.mulVec_mulVec]
    _ = Matrix.mulVec Pinv (Matrix.vec (sylvesterResidualRect m n A B C Xhat)) := by
          rw [hres]






/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    if a computed residual `Rhat` differs from the exact residual `R` by
    the nonnegative componentwise budget `Ru`, then
    `|vec(R)| <= |vec(Rhat)| + vec(Ru)`. -/
theorem sylvester_exact_residual_vec_abs_le_computed_residual_budget (m n : Nat)
    (R Rhat Ru : RMatFn m n)
    (hRhat : forall i j, |R i j - Rhat i j| <= Ru i j) :
    forall q : Prod (Fin n) (Fin m),
      |Matrix.vec R q| <= |Matrix.vec Rhat q| + Matrix.vec Ru q := by
  intro q
  calc
    |Matrix.vec R q| = |R q.2 q.1| := by
        simp [Matrix.vec]
    _ = |Rhat q.2 q.1 + (R q.2 q.1 - Rhat q.2 q.1)| := by
        congr 1
        ring
    _ <= |Rhat q.2 q.1| + |R q.2 q.1 - Rhat q.2 q.1| :=
        abs_add_le _ _
    _ <= |Rhat q.2 q.1| + Ru q.2 q.1 := by
        exact add_le_add (le_refl |Rhat q.2 q.1|) (hRhat q.2 q.1)
    _ = |Matrix.vec Rhat q| + Matrix.vec Ru q := by
        simp [Matrix.vec]

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), computed-residual
    budget certificate: `Rhat` approximates the exact residual with
    nonnegative componentwise error budget `Ru`. -/
def IsSylvesterComputedResidualBudget (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C Xhat Rhat Ru : RMatFn m n) :
    Prop :=
  (forall i j, 0 <= Ru i j) /\
    forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    an explicit residual error matrix `dR` with
    `Rhat = R(Xhat) + dR` and `|dR| <= Ru` yields the computed-residual
    budget certificate used by the practical bound. -/
theorem sylvesterComputedResidualBudget_of_error_model (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C Xhat Rhat Ru dR : RMatFn m n)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j) :
    IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru := by
  constructor
  · exact hRu
  · intro i j
    rw [hRhat i j]
    have hsub :
        sylvesterResidualRect m n A B C Xhat i j -
            (sylvesterResidualRect m n A B C Xhat i j + dR i j) =
          -dR i j := by
      ring
    rw [hsub, abs_neg]
    exact hdR i j







/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    a Frobenius residual-arithmetic certificate `||dR||_F <= rho` supplies
    the componentwise computed-residual budget with the uniform budget
    `Ru i j = rho`. -/
theorem sylvesterComputedResidualBudget_of_frobenius_error_model (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C Xhat Rhat dR : RMatFn m n)
    (rho : Real)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho) :
    IsSylvesterComputedResidualBudget m n A B C Xhat Rhat (fun _ _ => rho) := by
  exact
    sylvesterComputedResidualBudget_of_error_model m n
      A B C Xhat Rhat (fun _ _ => rho) dR hRhat
      (fun _ _ => hrho)
      (fun i j => (abs_entry_le_frobNorm dR i j).trans hdR)







/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), computed-residual
    certificate form: a left inverse for the vec/Kronecker coefficient,
    an entrywise inverse bound, and a computed-residual budget instantiate
    the practical relative max-entry error bound. -/
theorem sylvester_practical_error_bound_of_computed_residual_budget (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C X Xhat Rhat Ru : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_inverse_residual_budget m n
      X Xhat Rhat Ru Pinv PinvAbs
      (Matrix.vec (sylvesterResidualRect m n A B C Xhat))
      (sylvester_vec_error_eq_inverse_residual_of_left_inverse
        m n A B C X Xhat Pinv hX hLeft)
      hPinvAbs hRu
      (sylvester_exact_residual_vec_abs_le_computed_residual_budget
        m n (sylvesterResidualRect m n A B C Xhat) Rhat Ru hRhat)
      hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), certificate-packaged
    form of the practical componentwise error bound. -/
theorem sylvester_practical_error_bound_of_computed_residual_certificate (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C X Xhat Rhat Ru : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_budget m n
      A B C X Xhat Rhat Ru Pinv PinvAbs hX hLeft hPinvAbs
      hBudget.1 hBudget.2 hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute
    computed-residual certificate endpoint: the same practical budget bounds
    the unnormalized max-entry forward error, so no positive `||Xhat||`
    denominator assumption is needed. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_certificate
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C X Xhat Rhat Ru : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) := by
  exact
    sylvester_practical_abs_error_bound_of_inverse_residual_budget m n
      X Xhat Rhat Ru Pinv PinvAbs
      (Matrix.vec (sylvesterResidualRect m n A B C Xhat))
      (sylvester_vec_error_eq_inverse_residual_of_left_inverse
        m n A B C X Xhat Pinv hX hLeft)
      hPinvAbs hBudget.1
      (sylvester_exact_residual_vec_abs_le_computed_residual_budget
        m n (sylvesterResidualRect m n A B C Xhat) Rhat Ru hBudget.2)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute scalar
    computed-residual certificate endpoint: a scalar cap on every practical
    budget component bounds the unnormalized max-entry forward error. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_certificate_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru p <= eta) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <= eta := by
  have hbase :
      sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
        sylvesterVecMaxNorm m n
          (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) :=
    sylvester_practical_abs_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru Pinv PinvAbs hX hLeft hPinvAbs hBudget
  have hPinvAbs_nonneg : forall p q, 0 <= PinvAbs p q := by
    intro p q
    exact (abs_nonneg (Pinv p q)).trans (hPinvAbs p q)
  have hnorm :
      sylvesterVecMaxNorm m n
          (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) <= eta :=
    sylvesterPracticalBudgetVec_maxNorm_le_of_componentwise_le m n
      PinvAbs Rhat Ru hPinvAbs_nonneg hBudget.1 heta hcomponent
  exact le_trans hbase hnorm

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute raw
    computed-residual budget endpoint: the residual budget hypotheses directly
    bound the unnormalized max-entry forward error. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_budget
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C X Xhat Rhat Ru : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru Pinv PinvAbs hX hLeft hPinvAbs
      (And.intro hRu hRhat)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute raw
    computed-residual budget endpoint with a scalar practical-budget cap. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_budget_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru p <= eta) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_scalar m n
      A B C X Xhat Rhat Ru Pinv PinvAbs eta hX hLeft hPinvAbs
      (And.intro hRu hRhat) heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute explicit
    residual error-model endpoint: an explicit residual perturbation model
    supplies the practical budget without requiring a positive denominator. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_error_model
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C X Xhat Rhat Ru dR : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru Pinv PinvAbs hX hLeft hPinvAbs
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute explicit
    residual error-model endpoint with a scalar practical-budget cap. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_error_model_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru dR : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru p <= eta) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_scalar m n
      A B C X Xhat Rhat Ru Pinv PinvAbs eta hX hLeft hPinvAbs
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute Frobenius
    residual-arithmetic endpoint: a Frobenius residual perturbation certificate
    supplies the componentwise residual budget with uniform radius `rho`,
    giving an unnormalized max-entry forward-error bound. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_frobenius_error_model
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat dR : RMatFn m n) (rho : Real)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs Rhat (fun _ _ => rho)) := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat (fun _ _ => rho) Pinv PinvAbs
      hX hLeft hPinvAbs
      (sylvesterComputedResidualBudget_of_frobenius_error_model m n
        A B C Xhat Rhat dR rho hRhat hrho hdR)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute Frobenius
    residual-arithmetic endpoint with a scalar practical-budget cap. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_frobenius_error_model_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat dR : RMatFn m n) (rho eta : Real)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs Rhat (fun _ _ => rho) p <= eta) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_scalar m n
      A B C X Xhat Rhat (fun _ _ => rho) Pinv PinvAbs eta
      hX hLeft hPinvAbs
      (sylvesterComputedResidualBudget_of_frobenius_error_model m n
        A B C Xhat Rhat dR rho hRhat hrho hdR)
      heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute
    estimator-ready form: once the exact practical certificate has been proved,
    any componentwise larger inverse/residual budget also gives a valid
    unnormalized max-entry forward-error bound. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_certificate_mono
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') := by
  have hbase :=
    sylvester_practical_abs_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru Pinv PinvAbs hX hLeft hPinvAbs hBudget
  have hPinvAbs_nonneg : forall p q, 0 <= PinvAbs p q := by
    intro p q
    exact (abs_nonneg (Pinv p q)).trans (hPinvAbs p q)
  have hPinvAbs'_nonneg : forall p q, 0 <= PinvAbs' p q := by
    intro p q
    exact (hPinvAbs_nonneg p q).trans (hPinvAbs_le p q)
  have hnorm :
      sylvesterVecMaxNorm m n
          (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) <=
        sylvesterVecMaxNorm m n
          (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') :=
    sylvesterPracticalBudgetVec_maxNorm_mono m n
      PinvAbs PinvAbs' Rhat Rhat' Ru Ru'
      hPinvAbs_nonneg hPinvAbs'_nonneg hPinvAbs_le hRhat hBudget.1 hRu_le
  exact hbase.trans hnorm

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute monotone
    scalar endpoint: after replacing the inverse and residual budgets by
    componentwise larger estimates, a scalar cap on the estimated practical
    budget bounds the unnormalized max-entry forward error. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_certificate_mono_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <= eta := by
  have hbase :
      sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
        sylvesterVecMaxNorm m n
          (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') :=
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_mono m n
      A B C X Xhat Rhat Rhat' Ru Ru' Pinv PinvAbs PinvAbs'
      hX hLeft hPinvAbs hPinvAbs_le hBudget hRhat hRu_le
  have hPinvAbs_nonneg : forall p q, 0 <= PinvAbs p q := by
    intro p q
    exact (abs_nonneg (Pinv p q)).trans (hPinvAbs p q)
  have hPinvAbs'_nonneg : forall p q, 0 <= PinvAbs' p q := by
    intro p q
    exact (hPinvAbs_nonneg p q).trans (hPinvAbs_le p q)
  have hRu'_nonneg : forall i j, 0 <= Ru' i j := by
    intro i j
    exact (hBudget.1 i j).trans (hRu_le i j)
  have hnorm :
      sylvesterVecMaxNorm m n
          (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') <= eta :=
    sylvesterPracticalBudgetVec_maxNorm_le_of_componentwise_le m n
      PinvAbs' Rhat' Ru' hPinvAbs'_nonneg hRu'_nonneg heta hcomponent
  exact le_trans hbase hnorm

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute raw
    computed-residual budget endpoint with monotone supplied inverse and
    residual estimates. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_budget_mono
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_mono m n
      A B C X Xhat Rhat Rhat' Ru Ru' Pinv PinvAbs PinvAbs'
      hX hLeft hPinvAbs hPinvAbs_le (And.intro hRu hRhat)
      hRhat_le hRu_le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute raw
    computed-residual budget endpoint with monotone supplied estimates and a
    scalar practical-budget cap. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_budget_mono_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_mono_scalar m n
      A B C X Xhat Rhat Rhat' Ru Ru' Pinv PinvAbs PinvAbs' eta
      hX hLeft hPinvAbs hPinvAbs_le (And.intro hRu hRhat)
      hRhat_le hRu_le heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute explicit
    residual error-model endpoint with monotone supplied inverse and residual
    estimates. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_error_model_mono
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_mono m n
      A B C X Xhat Rhat Rhat' Ru Ru' Pinv PinvAbs PinvAbs'
      hX hLeft hPinvAbs hPinvAbs_le
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      hRhat_le hRu_le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute explicit
    residual error-model endpoint with monotone supplied estimates and a
    scalar practical-budget cap. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_error_model_mono_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_mono_scalar m n
      A B C X Xhat Rhat Rhat' Ru Ru' Pinv PinvAbs PinvAbs' eta
      hX hLeft hPinvAbs hPinvAbs_le
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      hRhat_le hRu_le heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    practical residual bound from a Frobenius residual-arithmetic model.
    The bound `||dR||_F <= rho` derives the raw componentwise residual-budget
    hypothesis with `Ru i j = rho`, then feeds the existing practical
    computed-residual certificate endpoint. -/
theorem sylvester_practical_error_bound_of_computed_residual_frobenius_error_model
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat dR : RMatFn m n) (rho : Real)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs Rhat (fun _ _ => rho)) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat (fun _ _ => rho) Pinv PinvAbs
      hX hLeft hPinvAbs
      (sylvesterComputedResidualBudget_of_frobenius_error_model m n
        A B C Xhat Rhat dR rho hRhat hrho hdR)
      hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), estimator-ready form:
    once the exact practical certificate has been proved, any componentwise
    larger inverse/residual budget also gives a valid relative max-entry error
    bound.  This is a monotone wrapper for later LAPACK-style estimator
    instantiations; it does not prove the estimator itself. -/
theorem sylvester_practical_error_bound_of_computed_residual_certificate_mono
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  have hbase :=
    sylvester_practical_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru Pinv PinvAbs hX hLeft hPinvAbs hBudget hXhat
  have hPinvAbs_nonneg : forall p q, 0 <= PinvAbs p q := by
    intro p q
    exact (abs_nonneg (Pinv p q)).trans (hPinvAbs p q)
  have hPinvAbs'_nonneg : forall p q, 0 <= PinvAbs' p q := by
    intro p q
    exact (hPinvAbs_nonneg p q).trans (hPinvAbs_le p q)
  have hnorm :
      sylvesterVecMaxNorm m n
          (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) <=
        sylvesterVecMaxNorm m n
          (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') :=
    sylvesterPracticalBudgetVec_maxNorm_mono m n
      PinvAbs PinvAbs' Rhat Rhat' Ru Ru'
      hPinvAbs_nonneg hPinvAbs'_nonneg hPinvAbs_le hRhat hBudget.1 hRu_le
  exact hbase.trans
    (div_le_div_of_nonneg_right hnorm (le_of_lt hXhat))

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), scalar estimator-ready
    form: a scalar cap on every practical-budget component gives the same
    relative max-entry forward-error bound with right-hand side
    `eta / ||Xhat||`. -/
theorem sylvester_practical_error_bound_of_computed_residual_certificate_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  have hbase :=
    sylvester_practical_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru Pinv PinvAbs hX hLeft hPinvAbs hBudget hXhat
  have hPinvAbs_nonneg : forall p q, 0 <= PinvAbs p q := by
    intro p q
    exact (abs_nonneg (Pinv p q)).trans (hPinvAbs p q)
  have hnorm :
      sylvesterVecMaxNorm m n
          (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) <= eta :=
    sylvesterPracticalBudgetVec_maxNorm_le_of_componentwise_le m n
      PinvAbs Rhat Ru hPinvAbs_nonneg hBudget.1 heta hcomponent
  exact hbase.trans
    (div_le_div_of_nonneg_right hnorm (le_of_lt hXhat))

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), monotone scalar
    estimator-ready form: after replacing the inverse and residual budgets by
    componentwise larger estimated quantities, a scalar cap on the estimated
    practical budget gives the final relative max-entry error bound. -/
theorem sylvester_practical_error_bound_of_computed_residual_certificate_mono_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  have hbase :=
    sylvester_practical_error_bound_of_computed_residual_certificate_mono m n
      A B C X Xhat Rhat Rhat' Ru Ru' Pinv PinvAbs PinvAbs'
      hX hLeft hPinvAbs hPinvAbs_le hBudget hRhat hRu_le hXhat
  have hPinvAbs_nonneg : forall p q, 0 <= PinvAbs p q := by
    intro p q
    exact (abs_nonneg (Pinv p q)).trans (hPinvAbs p q)
  have hPinvAbs'_nonneg : forall p q, 0 <= PinvAbs' p q := by
    intro p q
    exact (hPinvAbs_nonneg p q).trans (hPinvAbs_le p q)
  have hRu'_nonneg : forall i j, 0 <= Ru' i j := by
    intro i j
    exact (hBudget.1 i j).trans (hRu_le i j)
  have hnorm :
      sylvesterVecMaxNorm m n
          (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') <= eta :=
    sylvesterPracticalBudgetVec_maxNorm_le_of_componentwise_le m n
      PinvAbs' Rhat' Ru' hPinvAbs'_nonneg hRu'_nonneg heta hcomponent
  exact hbase.trans
    (div_le_div_of_nonneg_right hnorm (le_of_lt hXhat))

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), raw computed-residual
    budget form with monotone supplied inverse and residual estimates. -/
theorem sylvester_practical_error_bound_of_computed_residual_budget_mono
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono m n
      A B C X Xhat Rhat Rhat' Ru Ru' Pinv PinvAbs PinvAbs'
      hX hLeft hPinvAbs hPinvAbs_le ⟨hRu, hRhat⟩
      hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), raw computed-residual
    budget form with a scalar cap on the practical budget. -/
theorem sylvester_practical_error_bound_of_computed_residual_budget_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_scalar m n
      A B C X Xhat Rhat Ru Pinv PinvAbs eta hX hLeft hPinvAbs
      ⟨hRu, hRhat⟩ heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), raw computed-residual
    budget form with monotone supplied estimates and a scalar cap. -/
theorem sylvester_practical_error_bound_of_computed_residual_budget_mono_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono_scalar m n
      A B C X Xhat Rhat Rhat' Ru Ru' Pinv PinvAbs PinvAbs' eta
      hX hLeft hPinvAbs hPinvAbs_le ⟨hRu, hRhat⟩
      hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), explicit residual
    error-model form of the practical componentwise error bound.  An explicit
    residual perturbation `dR` with `Rhat = R(Xhat) + dR` and `|dR| <= Ru`
    supplies the computed-residual certificate. -/
theorem sylvester_practical_error_bound_of_computed_residual_error_model (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C X Xhat Rhat Ru dR : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru Pinv PinvAbs hX hLeft hPinvAbs
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), explicit residual
    error-model form with monotone supplied inverse and residual estimates. -/
theorem sylvester_practical_error_bound_of_computed_residual_error_model_mono
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono m n
      A B C X Xhat Rhat Rhat' Ru Ru' Pinv PinvAbs PinvAbs'
      hX hLeft hPinvAbs hPinvAbs_le
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), explicit residual
    error-model form with a scalar cap on the practical budget. -/
theorem sylvester_practical_error_bound_of_computed_residual_error_model_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru dR : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_scalar m n
      A B C X Xhat Rhat Ru Pinv PinvAbs eta hX hLeft hPinvAbs
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), explicit residual
    error-model form with monotone supplied estimates and a scalar cap. -/
theorem sylvester_practical_error_bound_of_computed_residual_error_model_mono_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono_scalar m n
      A B C X Xhat Rhat Rhat' Ru Ru' Pinv PinvAbs PinvAbs' eta
      hX hLeft hPinvAbs hPinvAbs_le
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      hRhat_le hRu_le heta hcomponent hXhat




































































































































































































































































































































/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), rectangular determinant
    endpoint: nonsingularity of the rectangular vec/Kronecker Sylvester
    coefficient supplies the actual inverse and its absolute-value budget for
    the practical computed-residual certificate. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_rect
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hdet : Matrix.det (sylvesterVecCoeff m n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), rectangular determinant
    absolute endpoint: the determinant certificate supplies the actual inverse
    budget, giving an unnormalized practical error bound. -/
theorem sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_rect
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hdet : Matrix.det (sylvesterVecCoeff m n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hBudget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), rectangular determinant
    raw computed-residual budget endpoint. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_rect
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hdet : Matrix.det (sylvesterVecCoeff m n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_rect
      m n A B C X Xhat Rhat Ru hdet hX (And.intro hRu hRhat) hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), rectangular determinant
    explicit residual-error-model endpoint. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_rect
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru dR : RMatFn m n)
    (hdet : Matrix.det (sylvesterVecCoeff m n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_error_model m n
      A B C X Xhat Rhat Ru dR
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hRhat hRu hdR hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    endpoint: nonsingularity of the vec/Kronecker Sylvester coefficient
    supplies the actual inverse and its absolute-value budget for the exact
    computed-residual certificate.  This is a practical residual certificate,
    not an automatic estimator or rounded Schur-solve theorem. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
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
    sylvester_practical_error_bound_of_computed_residual_certificate n n
      A B C X Xhat Rhat Ru
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    absolute endpoint: nonsingularity of the vec/Kronecker coefficient supplies
    the actual inverse budget, giving an unnormalized practical error bound
    without a positive `||Xhat||` assumption. -/
theorem sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n)
    (hdet : Not (Matrix.det (sylvesterVecCoeff n n A B) = 0))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate n n
      A B C X Xhat Rhat Ru
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hBudget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    absolute scalar endpoint: nonsingularity of the vec/Kronecker coefficient
    supplies the actual inverse budget, and a scalar cap on that budget bounds
    the unnormalized max-entry error. -/
theorem sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) (eta : Real)
    (hdet : Not (Matrix.det (sylvesterVecCoeff n n A B) = 0))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_scalar n n
      A B C X Xhat Rhat Ru
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hBudget heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    absolute monotone endpoint: after determinant nonsingularity supplies the
    exact inverse budget, componentwise larger inverse and residual estimates
    preserve the unnormalized practical error bound. -/
theorem sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hdet : Not (Matrix.det (sylvesterVecCoeff n n A B) = 0))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_mono n n
      A B C X Xhat Rhat Rhat' Ru Ru'
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      PinvAbs' hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hPinvAbs_le hBudget hRhat hRu_le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    absolute monotone scalar endpoint. -/
theorem sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hdet : Not (Matrix.det (sylvesterVecCoeff n n A B) = 0))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_mono_scalar n n
      A B C X Xhat Rhat Rhat' Ru Ru'
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      PinvAbs' eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hPinvAbs_le hBudget hRhat hRu_le heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    absolute raw-budget monotone endpoint. -/
theorem sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hdet : Not (Matrix.det (sylvesterVecCoeff n n A B) = 0))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      hdet hX (And.intro hRu hRhat) hPinvAbs_le hRhat_le hRu_le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    absolute raw-budget monotone scalar endpoint. -/
theorem sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hdet : Not (Matrix.det (sylvesterVecCoeff n n A B) = 0))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      hdet hX (And.intro hRu hRhat) hPinvAbs_le hRhat_le hRu_le
      heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    absolute explicit-error-model monotone endpoint. -/
theorem sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hdet : Not (Matrix.det (sylvesterVecCoeff n n A B) = 0))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      hdet hX
      (sylvesterComputedResidualBudget_of_error_model n n A B C Xhat Rhat Ru dR
        hRhat_eq hRu hdR)
      hPinvAbs_le hRhat_le hRu_le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    absolute explicit-error-model monotone scalar endpoint. -/
theorem sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hdet : Not (Matrix.det (sylvesterVecCoeff n n A B) = 0))
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
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      hdet hX
      (sylvesterComputedResidualBudget_of_error_model n n A B C Xhat Rhat Ru dR
        hRhat_eq hRu hdR)
      hPinvAbs_le hRhat_le hRu_le heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    scalar endpoint: the nonsingular vec/Kronecker coefficient supplies the
    exact inverse budget, and a scalar cap on that practical budget gives the
    relative max-entry error bound. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) (eta : Real)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
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
    sylvester_practical_error_bound_of_computed_residual_certificate_scalar n n
      A B C X Xhat Rhat Ru
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    monotone endpoint: after the determinant proof supplies the exact inverse
    budget, componentwise larger inverse and residual inputs preserve the
    practical computed-residual bound.  This is estimator-ready infrastructure,
    not a proof of any particular estimator. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
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
    sylvester_practical_error_bound_of_computed_residual_certificate_mono n n
      A B C X Xhat Rhat Rhat' Ru Ru'
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      PinvAbs' hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hPinvAbs_le hBudget hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    monotone scalar endpoint: a scalar cap on a componentwise larger practical
    budget gives the same relative max-entry error bound after nonsingularity
    supplies the exact inverse certificate. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
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
    sylvester_practical_error_bound_of_computed_residual_certificate_mono_scalar n n
      A B C X Xhat Rhat Rhat' Ru Ru'
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      PinvAbs' eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hPinvAbs_le hBudget hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    raw computed-residual budget endpoint: a determinant-nonzero vec/Kronecker
    coefficient supplies the nonsingular inverse, while the caller supplies a
    direct absolute residual budget. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
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
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A B C X Xhat Rhat Ru hdet hX (And.intro hRu hRhat) hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    raw computed-residual budget endpoint with monotone supplied inverse and
    residual estimates.  The determinant certificate still provides the exact
    inverse; the primed inputs are any componentwise larger practical budget. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
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
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      hdet hX (And.intro hRu hRhat_budget)
      hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    raw computed-residual budget endpoint with a scalar cap on the practical
    budget induced by the nonsingular vec/Kronecker inverse. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) (eta : Real)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
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
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A B C X Xhat Rhat Ru eta hdet hX
      (And.intro hRu hRhat) heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    raw computed-residual budget endpoint with monotone supplied estimates and
    a scalar cap on the enlarged practical budget. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
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
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta hdet hX
      (And.intro hRu hRhat_budget)
      hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    explicit residual-error model endpoint.  An explicit residual perturbation
    supplies the computed-residual certificate; determinant nonsingularity
    supplies the exact inverse budget. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
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
    sylvester_practical_error_bound_of_computed_residual_error_model n n
      A B C X Xhat Rhat Ru dR
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hRhat hRu hdR hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    explicit residual-error model with a scalar cap on the practical budget. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n) (eta : Real)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
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
    sylvester_practical_error_bound_of_computed_residual_error_model_scalar n n
      A B C X Xhat Rhat Ru dR
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hRhat hRu hdR heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    explicit residual-error model with monotone supplied inverse and residual
    estimates.  The monotone inputs may be estimator outputs, but no estimator
    correctness is asserted here. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
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
    sylvester_practical_error_bound_of_computed_residual_error_model_mono n n
      A B C X Xhat Rhat Rhat' Ru Ru' dR
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      PinvAbs' hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    explicit residual-error model with monotone estimates and a scalar cap on
    the enlarged practical budget. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
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
    sylvester_practical_error_bound_of_computed_residual_error_model_mono_scalar n n
      A B C X Xhat Rhat Rhat' Ru Ru' dR
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      PinvAbs' eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    Frobenius residual-error endpoint.  A Frobenius residual-arithmetic
    certificate supplies the uniform residual budget `rho`; determinant
    nonsingularity supplies the nonsingular inverse budget. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_frobenius_error_model
    (n : Nat)
    (A B C X Xhat Rhat dR : RMatFn n n) (rho : Real)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat
          (fun _ _ => rho)) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A B C X Xhat Rhat (fun _ _ => rho) hdet hX
      (sylvesterComputedResidualBudget_of_frobenius_error_model n n
        A B C Xhat Rhat dR rho hRhat hrho hdR)
      hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    absolute Frobenius residual-error endpoint.  A Frobenius residual-arithmetic
    certificate supplies the uniform residual budget `rho`; determinant
    nonsingularity supplies the nonsingular inverse budget. -/
theorem sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_frobenius_error_model
    (n : Nat)
    (A B C X Xhat Rhat dR : RMatFn n n) (rho : Real)
    (hdet : Not (Matrix.det (sylvesterVecCoeff n n A B) = 0))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat
          (fun _ _ => rho)) := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A B C X Xhat Rhat (fun _ _ => rho) hdet hX
      (sylvesterComputedResidualBudget_of_frobenius_error_model n n
        A B C Xhat Rhat dR rho hRhat hrho hdR)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    absolute Frobenius residual-error scalar endpoint. -/
theorem sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_frobenius_error_model_scalar
    (n : Nat)
    (A B C X Xhat Rhat dR : RMatFn n n) (rho eta : Real)
    (hdet : Not (Matrix.det (sylvesterVecCoeff n n A B) = 0))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat
          (fun _ _ => rho) p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A B C X Xhat Rhat (fun _ _ => rho) eta hdet hX
      (sylvesterComputedResidualBudget_of_frobenius_error_model n n
        A B C Xhat Rhat dR rho hRhat hrho hdR)
      heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    absolute Frobenius residual-error monotone endpoint. -/
theorem sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_frobenius_error_model_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru' dR : RMatFn n n)
    (rho : Real)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hdet : Not (Matrix.det (sylvesterVecCoeff n n A B) = 0))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, rho <= Ru' i j) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A B C X Xhat Rhat Rhat' (fun _ _ => rho) Ru' PinvAbs'
      hdet hX
      (sylvesterComputedResidualBudget_of_frobenius_error_model n n
        A B C Xhat Rhat dR rho hRhat_eq hrho hdR)
      hPinvAbs_le hRhat_le hRu_le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    absolute Frobenius residual-error monotone scalar endpoint. -/
theorem sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_frobenius_error_model_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru' dR : RMatFn n n)
    (rho : Real)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hdet : Not (Matrix.det (sylvesterVecCoeff n n A B) = 0))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, rho <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A B C X Xhat Rhat Rhat' (fun _ _ => rho) Ru' PinvAbs' eta
      hdet hX
      (sylvesterComputedResidualBudget_of_frobenius_error_model n n
        A B C Xhat Rhat dR rho hRhat_eq hrho hdR)
      hPinvAbs_le hRhat_le hRu_le heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    Frobenius residual-error scalar endpoint.  The scalar cap is taken over
    the determinant-supplied inverse budget and the uniform residual budget
    `rho`. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_frobenius_error_model_scalar
    (n : Nat)
    (A B C X Xhat Rhat dR : RMatFn n n) (rho eta : Real)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat
          (fun _ _ => rho) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A B C X Xhat Rhat (fun _ _ => rho) eta hdet hX
      (sylvesterComputedResidualBudget_of_frobenius_error_model n n
        A B C Xhat Rhat dR rho hRhat hrho hdR)
      heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    Frobenius residual-error monotone endpoint.  Componentwise larger inverse
    and residual estimates may replace the determinant-supplied practical
    budget after the Frobenius certificate supplies `Ru i j = rho`. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_frobenius_error_model_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru' dR : RMatFn n n)
    (rho : Real)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, rho <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A B C X Xhat Rhat Rhat' (fun _ _ => rho) Ru' PinvAbs'
      hdet hX
      (sylvesterComputedResidualBudget_of_frobenius_error_model n n
        A B C Xhat Rhat dR rho hRhat_eq hrho hdR)
      hPinvAbs_le hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    Frobenius residual-error monotone scalar endpoint. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_frobenius_error_model_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru' dR : RMatFn n n)
    (rho : Real)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, rho <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A B C X Xhat Rhat Rhat' (fun _ _ => rho) Ru' PinvAbs' eta
      hdet hX
      (sylvesterComputedResidualBudget_of_frobenius_error_model n n
        A B C Xhat Rhat dR rho hRhat_eq hrho hdR)
      hPinvAbs_le hRhat_le hRu_le heta hcomponent hXhat
































































































































































































































































































































































































































































/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), diagonal case:
    the absolute-value matrix exactly bounds the explicit diagonal inverse
    componentwise. -/
lemma sylvesterDiagonalVecCoeffInv_abs_le_invAbs (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real) :
    forall p q,
      |sylvesterDiagonalVecCoeffInv m n a b p q| <=
        sylvesterDiagonalVecCoeffInvAbs m n a b p q := by
  intro p q
  rfl

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), diagonal separated case:
    with `A` and `B` diagonal and `a_i != b_j`, the practical componentwise
    error bound is instantiated with the explicit diagonal inverse of the
    vec/Kronecker Sylvester coefficient. -/
theorem sylvester_practical_error_bound_of_diagonal_computed_residual_certificate
    (m n : Nat) (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hBudget :
      IsSylvesterComputedResidualBudget m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterDiagonalVecCoeffInvAbs m n a b) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate m n
      (Matrix.diagonal a) (Matrix.diagonal b) C X Xhat Rhat Ru
      (sylvesterDiagonalVecCoeffInv m n a b)
      (sylvesterDiagonalVecCoeffInvAbs m n a b)
      hX
      (sylvesterDiagonalVecCoeffInv_mul_sylvesterVecCoeff_diagonal
        m n a b hsep)
      (sylvesterDiagonalVecCoeffInv_abs_le_invAbs m n a b)
      hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), diagonal separated case:
    after replacing the explicit diagonal inverse and computed-residual budget
    by componentwise larger supplied estimates, the enlarged practical budget
    gives the relative max-entry error bound.  This is an exact
    diagonal-inverse specialization; it does not prove any estimator such as a
    LAPACK condition estimator. -/
theorem sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_mono
    (m n : Nat) (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hBudget :
      IsSylvesterComputedResidualBudget m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterDiagonalVecCoeffInvAbs m n a b p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono
      m n (Matrix.diagonal a) (Matrix.diagonal b) C X Xhat Rhat Rhat' Ru Ru'
      (sylvesterDiagonalVecCoeffInv m n a b)
      (sylvesterDiagonalVecCoeffInvAbs m n a b)
      PinvAbs' hX
      (sylvesterDiagonalVecCoeffInv_mul_sylvesterVecCoeff_diagonal
        m n a b hsep)
      (sylvesterDiagonalVecCoeffInv_abs_le_invAbs m n a b)
      hPinvAbs_le hBudget hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), diagonal separated case:
    a scalar cap on the explicit diagonal-inverse practical budget gives the
    final practical relative max-entry error bound. -/
theorem sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_scalar
    (m n : Nat) (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hBudget :
      IsSylvesterComputedResidualBudget m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterDiagonalVecCoeffInvAbs m n a b) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_scalar m n
      (Matrix.diagonal a) (Matrix.diagonal b) C X Xhat Rhat Ru
      (sylvesterDiagonalVecCoeffInv m n a b)
      (sylvesterDiagonalVecCoeffInvAbs m n a b)
      eta hX
      (sylvesterDiagonalVecCoeffInv_mul_sylvesterVecCoeff_diagonal
        m n a b hsep)
      (sylvesterDiagonalVecCoeffInv_abs_le_invAbs m n a b)
      hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), diagonal separated case:
    after replacing the explicit diagonal inverse and computed-residual budget
    by componentwise larger supplied estimates, a scalar cap on the estimated
    practical budget gives the relative max-entry error bound.  This is an
    exact diagonal-inverse specialization; it does not prove any estimator such
    as a LAPACK condition estimator. -/
theorem sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_mono_scalar
    (m n : Nat) (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hBudget :
      IsSylvesterComputedResidualBudget m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterDiagonalVecCoeffInvAbs m n a b p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono_scalar
      m n (Matrix.diagonal a) (Matrix.diagonal b) C X Xhat Rhat Rhat' Ru Ru'
      (sylvesterDiagonalVecCoeffInv m n a b)
      (sylvesterDiagonalVecCoeffInvAbs m n a b)
      PinvAbs' eta hX
      (sylvesterDiagonalVecCoeffInv_mul_sylvesterVecCoeff_diagonal
        m n a b hsep)
      (sylvesterDiagonalVecCoeffInv_abs_le_invAbs m n a b)
      hPinvAbs_le hBudget hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), diagonal separated case:
    raw computed-residual budget form of the practical componentwise error
    bound using the explicit diagonal inverse of the vec/Kronecker Sylvester
    coefficient. -/
theorem sylvester_practical_error_bound_of_diagonal_computed_residual_budget
    (m n : Nat) (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat i j -
          Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterDiagonalVecCoeffInvAbs m n a b) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_diagonal_computed_residual_certificate
      m n a b C X Xhat Rhat Ru hsep hX
      (And.intro hRu hRhat) hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), diagonal separated case:
    raw computed-residual budget form with componentwise larger supplied
    inverse and residual estimates. -/
theorem sylvester_practical_error_bound_of_diagonal_computed_residual_budget_mono
    (m n : Nat) (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat i j -
          Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterDiagonalVecCoeffInvAbs m n a b p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_mono
      m n a b C X Xhat Rhat Rhat' Ru Ru' PinvAbs' hsep hX
      (And.intro hRu hRhat) hPinvAbs_le hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), diagonal separated case:
    raw computed-residual budget form with a scalar cap on the practical
    budget. -/
theorem sylvester_practical_error_bound_of_diagonal_computed_residual_budget_scalar
    (m n : Nat) (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat i j -
          Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterDiagonalVecCoeffInvAbs m n a b) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_scalar
      m n a b C X Xhat Rhat Ru eta hsep hX
      (And.intro hRu hRhat) heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), diagonal separated case:
    raw computed-residual budget form with monotone supplied estimates and a
    scalar cap on the estimated practical budget. -/
theorem sylvester_practical_error_bound_of_diagonal_computed_residual_budget_mono_scalar
    (m n : Nat) (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat i j -
          Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterDiagonalVecCoeffInvAbs m n a b p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_mono_scalar
      m n a b C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta hsep hX
      (And.intro hRu hRhat) hPinvAbs_le hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), diagonal separated case:
    if the computed residual has an explicit error model
    `Rhat = R(Xhat) + dR` with `|dR| <= Ru`, then the practical
    componentwise error bound follows using the explicit diagonal inverse of
    the vec/Kronecker Sylvester coefficient. -/
theorem sylvester_practical_error_bound_of_diagonal_computed_residual_error_model
    (m n : Nat) (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Ru dR : RMatFn m n)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hRhat : forall i j,
      Rhat i j =
        sylvesterResidualRect m n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat i j +
          dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterDiagonalVecCoeffInvAbs m n a b) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_diagonal_computed_residual_certificate
      m n a b C X Xhat Rhat Ru hsep hX
      (sylvesterComputedResidualBudget_of_error_model m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat Rhat Ru dR
        hRhat hRu hdR)
      hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), diagonal separated case
    with an explicit residual error model: after replacing the exact diagonal
    inverse and residual budget by componentwise larger supplied estimates, the
    enlarged practical budget gives the final relative max-entry error bound.
    This remains an exact diagonal-inverse wrapper, not a rounded residual or
    estimator proof. -/
theorem sylvester_practical_error_bound_of_diagonal_computed_residual_error_model_mono
    (m n : Nat) (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hRhat_model : forall i j,
      Rhat i j =
        sylvesterResidualRect m n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat i j +
          dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterDiagonalVecCoeffInvAbs m n a b p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_mono
      m n a b C X Xhat Rhat Rhat' Ru Ru' PinvAbs' hsep hX
      (sylvesterComputedResidualBudget_of_error_model m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat Rhat Ru dR
        hRhat_model hRu hdR)
      hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), diagonal separated case
    with an explicit residual error model and a scalar cap on the practical
    budget. -/
theorem sylvester_practical_error_bound_of_diagonal_computed_residual_error_model_scalar
    (m n : Nat) (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Ru dR : RMatFn m n) (eta : Real)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hRhat : forall i j,
      Rhat i j =
        sylvesterResidualRect m n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat i j +
          dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterDiagonalVecCoeffInvAbs m n a b) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_scalar
      m n a b C X Xhat Rhat Ru eta hsep hX
      (sylvesterComputedResidualBudget_of_error_model m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat Rhat Ru dR
        hRhat hRu hdR)
      heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), diagonal separated case
    with an explicit residual error model: after replacing the exact diagonal
    inverse and computed-residual budget by componentwise larger supplied
    estimates, a scalar cap on the estimated practical budget gives the final
    relative max-entry error bound.  This is an exact diagonal-inverse
    specialization; it does not prove any estimator such as a LAPACK condition
    estimator. -/
theorem sylvester_practical_error_bound_of_diagonal_computed_residual_error_model_mono_scalar
    (m n : Nat) (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hRhat_eq : forall i j,
      Rhat i j =
        sylvesterResidualRect m n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat i j +
          dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterDiagonalVecCoeffInvAbs m n a b p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_mono_scalar
      m n a b C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta hsep hX
      (sylvesterComputedResidualBudget_of_error_model m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat Rhat Ru dR
        hRhat_eq hRu hdR)
      hPinvAbs_le hRhat_le hRu_le heta hcomponent hXhat

-- ============================================================
-- Exact Schur-coordinate algebra from Chapter 16.1
-- ============================================================




















































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































-- ============================================================
-- Lyapunov specialization from Chapter 16.3
-- ============================================================











































































































-- ============================================================
-- Separation infimum from Chapter 16.4
-- ============================================================






































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































-- ============================================================
-- Equation (16.29) source-numbered practical endpoint aliases
-- ============================================================








































































































































































































































































































































































































-- ============================================================
-- Perturbation source wrappers from Chapter 16.3
-- ============================================================





























































































































































































































































































































































-- ============================================================
-- A posteriori source wrapper from Chapter 16.4
-- ============================================================


























































































































































































































































































































-- ============================================================
-- Generalized equations from Chapter 16.5
-- ============================================================




























































































































































































end NumStability
