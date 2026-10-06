-- Algorithms/LeastSquares/LSPerturbation.lean
--
-- Perturbation theory for the least squares problem (Higham §20.1).
--
-- Theorem 20.1 (Wedin): Normwise perturbation bounds for the LS solution.
--   ‖x−y‖/‖x‖ ≤ κ₂(A)ε/(1−κ₂(A)ε) · (2 + (κ₂(A)+1)‖r‖/(‖A‖‖x‖))
--   ‖r−s‖/‖b‖ ≤ (1+2κ₂(A))ε
--
-- Theorem 20.2: Componentwise perturbation via the augmented system
--   [I A; Aᵀ 0][r; x] = [b; 0].
--
-- The displayed Wedin bounds are formalized below at the repository
-- residual-definition and column-orthogonality API.  Further source-minimal
-- API cleanup may reduce hypotheses, but the core perturbation handoff now
-- goes through the proved Lemma 20.11 and Lemma 20.12 route.

import Mathlib.Data.Real.Basic
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Norms
import NumStability.Analysis.HighamChapter7

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §20.1  Theorem 20.1 (Wedin): Normwise LS perturbation
-- ============================================================

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.1):
    scalar right-hand side of Wedin's relative solution perturbation bound. -/
noncomputable def wedinTheorem20_1SolutionRelativeRHS
    (kappa eps A_norm x_norm r_norm : ℝ) : ℝ :=
  (kappa * eps) / (1 - kappa * eps) *
    (2 + (kappa + 1) * r_norm / (A_norm * x_norm))

/-- Conservative scalar right-hand side produced by the current one-sided
    Lemma 20.12 route toward Wedin's equation (20.1).

The second residual term keeps the extra `1 / (1 - κ ε)` factor that remains
until the full Lemma 20.12 equality/min surface is formalized. -/
noncomputable def wedinTheorem20_1SolutionRelativeRHSConservative
    (kappa eps A_norm x_norm r_norm : ℝ) : ℝ :=
  (kappa * eps) / (1 - kappa * eps) *
    (2 + r_norm / (A_norm * x_norm)) +
  (kappa ^ 2 * eps) / (1 - kappa * eps) ^ 2 *
    (r_norm / (A_norm * x_norm))

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.2):
    scalar right-hand side of Wedin's relative residual perturbation bound. -/
def wedinTheorem20_1ResidualRelativeRHS (kappa eps : ℝ) : ℝ :=
  (1 + 2 * kappa) * eps

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.2), conservative
    scalar right-hand side obtained from the currently formalized one-sided
    Lemma 20.12 route.

The extra denominator records that the proof uses the available
`||P_B(I-P_A)|| <= ||A-B|| ||Bplus||` estimate together with a Lemma 20.11
`Bplus` radius, rather than the still-open projection equality/min surface that
would replace `Bplus` by `Aplus` and recover the printed `(1+2κ)ε` RHS. -/
noncomputable def wedinTheorem20_1ResidualRelativeRHSConservative
    (kappa eps : ℝ) : ℝ :=
  (1 + kappa) * eps + (kappa * eps) / (1 - kappa * eps)

/-- The small-perturbation condition in Theorem 20.1 makes the denominator in
    equation (20.1) positive. -/
theorem wedinTheorem20_1_denominator_pos {kappa eps : ℝ}
    (hsmall : kappa * eps < 1) :
    0 < 1 - kappa * eps := by
  linarith

/-- The denominator in Wedin's equation (20.1) is nonzero under the printed
    small-perturbation hypothesis. -/
theorem wedinTheorem20_1_denominator_ne_zero {kappa eps : ℝ}
    (hsmall : kappa * eps < 1) :
    1 - kappa * eps ≠ 0 :=
  (wedinTheorem20_1_denominator_pos hsmall).ne'

/-- Under the natural norm-domain assumptions, Wedin's equation (20.1)
    right-hand side is a nonnegative scalar bound. -/
theorem wedinTheorem20_1_solutionRelativeRHS_nonneg {kappa eps A_norm x_norm r_norm : ℝ}
    (hkappa : 0 ≤ kappa) (heps : 0 ≤ eps) (hsmall : kappa * eps < 1)
    (hA : 0 < A_norm) (hx : 0 < x_norm) (hr : 0 ≤ r_norm) :
    0 ≤ wedinTheorem20_1SolutionRelativeRHS kappa eps A_norm x_norm r_norm := by
  unfold wedinTheorem20_1SolutionRelativeRHS
  have hnum : 0 ≤ kappa * eps := mul_nonneg hkappa heps
  have hden_pos : 0 < 1 - kappa * eps :=
    wedinTheorem20_1_denominator_pos hsmall
  have hfrac : 0 ≤ (kappa * eps) / (1 - kappa * eps) :=
    div_nonneg hnum (le_of_lt hden_pos)
  have hAx_pos : 0 < A_norm * x_norm := mul_pos hA hx
  have hkappa_one_nonneg : 0 ≤ kappa + 1 := by linarith
  have hterm : 0 ≤ (kappa + 1) * r_norm / (A_norm * x_norm) :=
    div_nonneg (mul_nonneg hkappa_one_nonneg hr) (le_of_lt hAx_pos)
  have hparen : 0 ≤ 2 + (kappa + 1) * r_norm / (A_norm * x_norm) := by
    linarith
  exact mul_nonneg hfrac hparen

/-- Under the natural condition-number and roundoff-domain assumptions,
    Wedin's equation (20.2) right-hand side is nonnegative. -/
theorem wedinTheorem20_1_residualRelativeRHS_nonneg {kappa eps : ℝ}
    (hkappa : 0 ≤ kappa) (heps : 0 ≤ eps) :
    0 ≤ wedinTheorem20_1ResidualRelativeRHS kappa eps := by
  unfold wedinTheorem20_1ResidualRelativeRHS
  have hfactor : 0 ≤ 1 + 2 * kappa := by nlinarith
  exact mul_nonneg hfactor heps

/-- With zero data perturbation budget, the scalar RHS of Wedin's equation
    (20.1) vanishes. -/
@[simp] theorem wedinTheorem20_1_solutionRelativeRHS_zero_eps
    (kappa A_norm x_norm r_norm : ℝ) :
    wedinTheorem20_1SolutionRelativeRHS kappa 0 A_norm x_norm r_norm = 0 := by
  simp [wedinTheorem20_1SolutionRelativeRHS]

/-- With zero data perturbation budget, the scalar RHS of Wedin's equation
    (20.2) vanishes. -/
@[simp] theorem wedinTheorem20_1_residualRelativeRHS_zero_eps (kappa : ℝ) :
    wedinTheorem20_1ResidualRelativeRHS kappa 0 = 0 := by
  simp [wedinTheorem20_1ResidualRelativeRHS]

/-- In the zero-residual case, Wedin's equation (20.1) loses the residual
    amplification term and reduces to the `2 κ ε / (1 - κ ε)` factor. -/
theorem wedinTheorem20_1_solutionRelativeRHS_of_zero_residual
    (kappa eps A_norm x_norm : ℝ) :
    wedinTheorem20_1SolutionRelativeRHS kappa eps A_norm x_norm 0 =
      2 * ((kappa * eps) / (1 - kappa * eps)) := by
  simp [wedinTheorem20_1SolutionRelativeRHS, mul_comm]

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1 / Problem 20.11:
    Wedin's displayed solution RHS is its first-order coefficient times `eps`
    plus an explicit quadratic remainder.  This is the scalar algebra behind
    the source's statement that (20.25) recovers (20.1) to first order in the
    unconstrained case. -/
theorem wedinTheorem20_1_solutionRelativeRHS_eq_first_order_add_quadratic_remainder
    {kappa eps A_norm x_norm r_norm : ℝ}
    (hden : 1 - kappa * eps ≠ 0) :
    wedinTheorem20_1SolutionRelativeRHS kappa eps A_norm x_norm r_norm =
      eps * kappa *
          (2 + (kappa + 1) * r_norm / (A_norm * x_norm)) +
        ((kappa * eps) ^ 2 / (1 - kappa * eps)) *
          (2 + (kappa + 1) * r_norm / (A_norm * x_norm)) := by
  let c : ℝ := 2 + (kappa + 1) * r_norm / (A_norm * x_norm)
  unfold wedinTheorem20_1SolutionRelativeRHS
  change (kappa * eps) / (1 - kappa * eps) * c =
    eps * kappa * c + ((kappa * eps) ^ 2 / (1 - kappa * eps)) * c
  field_simp [hden]
  ring

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1 / Problem 20.11:
    under the natural norm-domain assumptions, Wedin's full displayed
    solution RHS dominates its first-order coefficient times `eps`. -/
theorem wedinTheorem20_1_solutionRelativeRHS_first_order_le
    {kappa eps A_norm x_norm r_norm : ℝ}
    (hkappa : 0 ≤ kappa) (_heps : 0 ≤ eps) (hsmall : kappa * eps < 1)
    (hA : 0 < A_norm) (hx : 0 < x_norm) (hr : 0 ≤ r_norm) :
    eps * kappa *
        (2 + (kappa + 1) * r_norm / (A_norm * x_norm)) ≤
      wedinTheorem20_1SolutionRelativeRHS kappa eps A_norm x_norm r_norm := by
  have hden_ne : 1 - kappa * eps ≠ 0 :=
    wedinTheorem20_1_denominator_ne_zero hsmall
  rw [wedinTheorem20_1_solutionRelativeRHS_eq_first_order_add_quadratic_remainder
    hden_ne]
  apply le_add_of_nonneg_right
  have hden_pos : 0 < 1 - kappa * eps :=
    wedinTheorem20_1_denominator_pos hsmall
  have hfrac : 0 ≤ (kappa * eps) ^ 2 / (1 - kappa * eps) :=
    div_nonneg (sq_nonneg (kappa * eps)) (le_of_lt hden_pos)
  have hAx_pos : 0 < A_norm * x_norm := mul_pos hA hx
  have hkappa_one_nonneg : 0 ≤ kappa + 1 := by linarith
  have hterm : 0 ≤ (kappa + 1) * r_norm / (A_norm * x_norm) :=
    div_nonneg (mul_nonneg hkappa_one_nonneg hr) (le_of_lt hAx_pos)
  have hparen : 0 ≤ 2 + (kappa + 1) * r_norm / (A_norm * x_norm) := by
    linarith
  exact mul_nonneg hfrac hparen

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.1), scalar
    normalization for the currently proved one-sided Wedin vector route.

This theorem converts the vector estimate with forcing radii
`DeltaA_norm <= eps*A_norm` and
`Deltab_norm <= eps*(A_norm*x_norm + r_norm)` into the conservative relative
RHS above.  It deliberately does not collapse to the printed (20.1) RHS; that
requires the remaining full Lemma 20.12 equality/min step. -/
theorem wedinTheorem20_1_solutionRelativeRHSConservative_of_vector_bound
    {sol_norm Aplus_norm DeltaA_norm Deltab_norm kappa eps A_norm x_norm
      r_norm eta : ℝ}
    (hAplus_nonneg : 0 ≤ Aplus_norm)
    (hA_norm_pos : 0 < A_norm)
    (hx_norm_pos : 0 < x_norm)
    (hkappa : kappa = Aplus_norm * A_norm)
    (heta : eta = kappa * eps)
    (hsmall : kappa * eps < 1)
    (hDeltaA_norm : DeltaA_norm ≤ eps * A_norm)
    (hDeltab_norm : Deltab_norm ≤ eps * (A_norm * x_norm + r_norm))
    (hvec :
      sol_norm ≤
        (Aplus_norm / (1 - eta)) *
            (DeltaA_norm * x_norm + Deltab_norm) +
          (eta * Aplus_norm / (1 - eta) ^ 2) * r_norm) :
    sol_norm / x_norm ≤
      wedinTheorem20_1SolutionRelativeRHSConservative
        kappa eps A_norm x_norm r_norm := by
  have hden_eta_pos : 0 < 1 - eta := by
    rw [heta]
    exact wedinTheorem20_1_denominator_pos hsmall
  have hcoef_nonneg : 0 ≤ Aplus_norm / (1 - eta) :=
    div_nonneg hAplus_nonneg (le_of_lt hden_eta_pos)
  have hDeltaA_x :
      DeltaA_norm * x_norm ≤ (eps * A_norm) * x_norm :=
    mul_le_mul_of_nonneg_right hDeltaA_norm (le_of_lt hx_norm_pos)
  have hinside :
      DeltaA_norm * x_norm + Deltab_norm ≤
        (eps * A_norm) * x_norm + eps * (A_norm * x_norm + r_norm) :=
    add_le_add hDeltaA_x hDeltab_norm
  have hforcing :
      (Aplus_norm / (1 - eta)) *
          (DeltaA_norm * x_norm + Deltab_norm) ≤
        (Aplus_norm / (1 - eta)) *
          ((eps * A_norm) * x_norm + eps * (A_norm * x_norm + r_norm)) :=
    mul_le_mul_of_nonneg_left hinside hcoef_nonneg
  have hvec_scalar :
      sol_norm ≤
        (Aplus_norm / (1 - eta)) *
            ((eps * A_norm) * x_norm + eps * (A_norm * x_norm + r_norm)) +
          (eta * Aplus_norm / (1 - eta) ^ 2) * r_norm :=
    hvec.trans (add_le_add hforcing (le_refl _))
  calc
    sol_norm / x_norm
        ≤ ((Aplus_norm / (1 - eta)) *
            ((eps * A_norm) * x_norm + eps * (A_norm * x_norm + r_norm)) +
          (eta * Aplus_norm / (1 - eta) ^ 2) * r_norm) / x_norm :=
            div_le_div_of_nonneg_right hvec_scalar (le_of_lt hx_norm_pos)
    _ = wedinTheorem20_1SolutionRelativeRHSConservative
        kappa eps A_norm x_norm r_norm := by
          unfold wedinTheorem20_1SolutionRelativeRHSConservative
          rw [heta, hkappa]
          field_simp [ne_of_gt hA_norm_pos, ne_of_gt hx_norm_pos,
            ne_of_gt hden_eta_pos]
          ring

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.1), scalar
    normalization for the printed Wedin relative solution perturbation RHS.

This theorem isolates the final scalar arithmetic: a vector estimate whose
residual-transfer term has only the source-strength `1 / (1 - κ ε)`
denominator normalizes exactly to Higham's printed equation (20.1). -/
theorem wedinTheorem20_1_solutionRelativeRHS_of_vector_bound
    {sol_norm Aplus_norm DeltaA_norm Deltab_norm kappa eps A_norm x_norm
      r_norm eta : ℝ}
    (hAplus_nonneg : 0 ≤ Aplus_norm)
    (hA_norm_pos : 0 < A_norm)
    (hx_norm_pos : 0 < x_norm)
    (hkappa : kappa = Aplus_norm * A_norm)
    (heta : eta = kappa * eps)
    (hsmall : kappa * eps < 1)
    (hDeltaA_norm : DeltaA_norm ≤ eps * A_norm)
    (hDeltab_norm : Deltab_norm ≤ eps * (A_norm * x_norm + r_norm))
    (hvec :
      sol_norm ≤
        (Aplus_norm / (1 - eta)) *
            (DeltaA_norm * x_norm + Deltab_norm) +
          (eta * Aplus_norm / (1 - eta)) * r_norm) :
    sol_norm / x_norm ≤
      wedinTheorem20_1SolutionRelativeRHS kappa eps A_norm x_norm r_norm := by
  have hden_eta_pos : 0 < 1 - eta := by
    rw [heta]
    exact wedinTheorem20_1_denominator_pos hsmall
  have hcoef_nonneg : 0 ≤ Aplus_norm / (1 - eta) :=
    div_nonneg hAplus_nonneg (le_of_lt hden_eta_pos)
  have hDeltaA_x :
      DeltaA_norm * x_norm ≤ (eps * A_norm) * x_norm :=
    mul_le_mul_of_nonneg_right hDeltaA_norm (le_of_lt hx_norm_pos)
  have hinside :
      DeltaA_norm * x_norm + Deltab_norm ≤
        (eps * A_norm) * x_norm + eps * (A_norm * x_norm + r_norm) :=
    add_le_add hDeltaA_x hDeltab_norm
  have hforcing :
      (Aplus_norm / (1 - eta)) *
          (DeltaA_norm * x_norm + Deltab_norm) ≤
        (Aplus_norm / (1 - eta)) *
          ((eps * A_norm) * x_norm + eps * (A_norm * x_norm + r_norm)) :=
    mul_le_mul_of_nonneg_left hinside hcoef_nonneg
  have hvec_scalar :
      sol_norm ≤
        (Aplus_norm / (1 - eta)) *
            ((eps * A_norm) * x_norm + eps * (A_norm * x_norm + r_norm)) +
          (eta * Aplus_norm / (1 - eta)) * r_norm :=
    hvec.trans (add_le_add hforcing (le_refl _))
  have hden_kappa_pos : 0 < 1 - kappa * eps :=
    wedinTheorem20_1_denominator_pos hsmall
  have hden_rewrite_ne : 1 - Aplus_norm * A_norm * eps ≠ 0 := by
    rw [← hkappa]
    exact (ne_of_gt hden_kappa_pos)
  calc
    sol_norm / x_norm
        ≤ ((Aplus_norm / (1 - eta)) *
            ((eps * A_norm) * x_norm + eps * (A_norm * x_norm + r_norm)) +
          (eta * Aplus_norm / (1 - eta)) * r_norm) / x_norm :=
            div_le_div_of_nonneg_right hvec_scalar (le_of_lt hx_norm_pos)
    _ = wedinTheorem20_1SolutionRelativeRHS
        kappa eps A_norm x_norm r_norm := by
          unfold wedinTheorem20_1SolutionRelativeRHS
          rw [heta, hkappa]
          field_simp [ne_of_gt hA_norm_pos, ne_of_gt hx_norm_pos,
            hden_rewrite_ne]
          ring

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    the smallness hypothesis `η < 1` makes the reciprocal denominator positive. -/
theorem wedinLemma20_11_denominator_pos {eta : ℝ} (hsmall : eta < 1) :
    0 < 1 - eta := by
  linarith

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    column-side least singular value for a real rectangular matrix with
    nonempty column dimension, viewed through the repository's complexified
    singular-value API. -/
noncomputable def wedinLemma20_11_sigmaMinCol
    {m k : ℕ} (A : Fin m → Fin (k + 1) → ℝ) : ℝ :=
  complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k)

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    the column-side least singular value is nonnegative. -/
theorem wedinLemma20_11_sigmaMinCol_nonneg
    {m k : ℕ} (A : Fin m → Fin (k + 1) → ℝ) :
    0 ≤ wedinLemma20_11_sigmaMinCol A := by
  simpa [wedinLemma20_11_sigmaMinCol] using
    complexMatrixSingularValue_nonneg (realRectToCMatrix A) (Fin.last k)

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    the least singular value gives the lower vector-action radius for a real
    rectangular matrix with nonempty column dimension. -/
theorem wedinLemma20_11_sigmaMinCol_mul_vecNorm2_le_rectMatMulVec
    {m k : ℕ} (A : Fin m → Fin (k + 1) → ℝ)
    (x : Fin (k + 1) → ℝ) :
    wedinLemma20_11_sigmaMinCol A * vecNorm2 x ≤
      vecNorm2 (rectMatMulVec A x) := by
  have h :=
    complexMatrixSingularValue_last_mul_norm_le_norm_euclideanLin
      (realRectToCMatrix A) (realVecToEuclidean x)
  rw [realVecToEuclidean_norm] at h
  rw [realRectToCMatrix_euclideanLin_realVecToEuclidean_norm] at h
  simpa [wedinLemma20_11_sigmaMinCol] using h

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    injectivity of the real rectangular action makes the full-column
    `sigma_min` positive. -/
theorem wedinLemma20_11_sigmaMinCol_pos_of_rectMatMulVec_injective
    {m k : ℕ} (A : Fin m → Fin (k + 1) → ℝ)
    (hinj : Function.Injective (rectMatMulVec A)) :
    0 < wedinLemma20_11_sigmaMinCol A := by
  by_contra hnot
  have hsigma_zero : wedinLemma20_11_sigmaMinCol A = 0 :=
    le_antisymm (le_of_not_gt hnot) (wedinLemma20_11_sigmaMinCol_nonneg A)
  obtain ⟨x, hx_ne, hsq⟩ :=
    realRectToCMatrix_last_singularValue_exists_real_attaining_vector_sq A
  have hsing_zero :
      complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k) = 0 := by
    simpa [wedinLemma20_11_sigmaMinCol] using hsigma_zero
  have hx_action_zero : rectMatMulVec A x = 0 := by
    apply funext
    apply (vecNorm2_eq_zero_iff (rectMatMulVec A x)).1
    apply (sq_eq_zero_iff).1
    rw [vecNorm2_sq, hsq, hsing_zero]
    ring
  have hx_zero : x = 0 := by
    have h0 : rectMatMulVec A x = rectMatMulVec A (fun _j => 0) := by
      rw [hx_action_zero]
      ext i
      simp [rectMatMulVec]
    exact hinj h0
  exact hx_ne hx_zero

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    triangle-inequality core behind the singular-value perturbation step.

    If `A` has lower action radius `sigma` and the perturbation `Delta` has
    rectangular operator-2 radius `delta`, then `A + Delta` has lower action
    radius `sigma - delta`.  This is a proved local adapter toward the source
    line `sigma_r(B) >= sigma_r(A) - ||A-B||_2`; it does not by itself identify
    `sigma` with a singular value or prove rank preservation. -/
theorem wedinLemma20_11_lowerActionBound_of_rectOpNorm2Le
    {m n : ℕ} (A Delta : Fin m → Fin n → ℝ) {sigma delta : ℝ}
    (hlower : ∀ x : Fin n → ℝ,
      sigma * vecNorm2 x ≤ vecNorm2 (rectMatMulVec A x))
    (hDelta : rectOpNorm2Le Delta delta) :
    ∀ x : Fin n → ℝ,
      (sigma - delta) * vecNorm2 x ≤
        vecNorm2 (rectMatMulVec (fun i j => A i j + Delta i j) x) := by
  intro x
  have hsplit :
      rectMatMulVec (fun i j => A i j + Delta i j) x =
        fun i => rectMatMulVec A x i + rectMatMulVec Delta x i :=
    rectMatMulVec_mat_add A Delta x
  have hA_decomp :
      rectMatMulVec A x =
        fun i =>
          rectMatMulVec (fun i j => A i j + Delta i j) x i -
            rectMatMulVec Delta x i := by
    ext i
    rw [congrFun hsplit i]
    ring
  have htri :
      vecNorm2 (rectMatMulVec A x) ≤
        vecNorm2 (rectMatMulVec (fun i j => A i j + Delta i j) x) +
          vecNorm2 (rectMatMulVec Delta x) := by
    calc
      vecNorm2 (rectMatMulVec A x)
          = vecNorm2
              (fun i =>
                rectMatMulVec (fun i j => A i j + Delta i j) x i -
                  rectMatMulVec Delta x i) := by
            rw [hA_decomp]
      _ ≤ vecNorm2 (rectMatMulVec (fun i j => A i j + Delta i j) x) +
            vecNorm2 (fun i => -rectMatMulVec Delta x i) := by
            have h := vecNorm2_add_le
              (rectMatMulVec (fun i j => A i j + Delta i j) x)
              (fun i => -rectMatMulVec Delta x i)
            simpa [sub_eq_add_neg] using h
      _ = vecNorm2 (rectMatMulVec (fun i j => A i j + Delta i j) x) +
            vecNorm2 (rectMatMulVec Delta x) := by
            rw [vecNorm2_neg]
  have hlower_x := hlower x
  have hDelta_x := hDelta x
  have hleft :
      sigma * vecNorm2 x - delta * vecNorm2 x ≤
        vecNorm2 (rectMatMulVec A x) -
          vecNorm2 (rectMatMulVec Delta x) := by
    linarith
  have hright :
      vecNorm2 (rectMatMulVec A x) -
          vecNorm2 (rectMatMulVec Delta x) ≤
        vecNorm2 (rectMatMulVec (fun i j => A i j + Delta i j) x) := by
    linarith
  calc
    (sigma - delta) * vecNorm2 x =
        sigma * vecNorm2 x - delta * vecNorm2 x := by
          ring
    _ ≤ vecNorm2 (rectMatMulVec A x) -
          vecNorm2 (rectMatMulVec Delta x) := hleft
    _ ≤ vecNorm2 (rectMatMulVec (fun i j => A i j + Delta i j) x) := hright

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    source-shaped lower action perturbation with `B - A` as the perturbation.

    This is the same triangle-inequality step as
    `wedinLemma20_11_lowerActionBound_of_rectOpNorm2Le`, rewritten in the
    orientation used in the source proof of Lemma 20.11. -/
theorem wedinLemma20_11_lowerActionBound_of_sub_rectOpNorm2Le
    {m n : ℕ} (A B : Fin m → Fin n → ℝ) {sigma delta : ℝ}
    (hlower : ∀ x : Fin n → ℝ,
      sigma * vecNorm2 x ≤ vecNorm2 (rectMatMulVec A x))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta) :
    ∀ x : Fin n → ℝ,
      (sigma - delta) * vecNorm2 x ≤ vecNorm2 (rectMatMulVec B x) := by
  intro x
  have h :=
    wedinLemma20_11_lowerActionBound_of_rectOpNorm2Le
      A (fun i j => B i j - A i j) hlower hDelta x
  have hmat : (fun i j => A i j + (B i j - A i j)) = B := by
    ext i j
    ring
  simpa [hmat] using h

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    full-column singular-value perturbation line.

    For real rectangular matrices with nonempty column dimension, a rectangular
    operator-2 bound on `B - A` gives
    `sigma_min(A) - delta <= sigma_min(B)`.  This is the source line
    `sigma_r(B) >= sigma_r(A) - ||A-B||_2` specialized to the full-column-rank
    indexing surface used by least-squares applications. -/
theorem wedinLemma20_11_sigmaMinCol_sub_le_sigmaMinCol_of_sub_rectOpNorm2Le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ) {delta : ℝ}
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta) :
    wedinLemma20_11_sigmaMinCol A - delta ≤
      wedinLemma20_11_sigmaMinCol B := by
  by_cases hnonneg : 0 ≤ wedinLemma20_11_sigmaMinCol A - delta
  · obtain ⟨x, hx_ne, hsq⟩ :=
      realRectToCMatrix_last_singularValue_exists_real_attaining_vector_sq B
    have hx_norm_ne : vecNorm2 x ≠ 0 := by
      intro hx_norm
      apply hx_ne
      ext j
      exact (vecNorm2_eq_zero_iff x).mp hx_norm j
    have hx_norm_pos : 0 < vecNorm2 x :=
      lt_of_le_of_ne (vecNorm2_nonneg x) (Ne.symm hx_norm_ne)
    have hB_lower :=
      wedinLemma20_11_lowerActionBound_of_sub_rectOpNorm2Le
        A B (wedinLemma20_11_sigmaMinCol_mul_vecNorm2_le_rectMatMulVec A)
        hDelta x
    have hB_norm_eq :
        vecNorm2 (rectMatMulVec B x) =
          wedinLemma20_11_sigmaMinCol B * vecNorm2 x := by
      apply (sq_eq_sq₀
        (vecNorm2_nonneg (rectMatMulVec B x))
        (mul_nonneg (wedinLemma20_11_sigmaMinCol_nonneg B)
          (vecNorm2_nonneg x))).mp
      calc
        vecNorm2 (rectMatMulVec B x) ^ 2 =
            vecNorm2Sq (rectMatMulVec B x) := vecNorm2_sq _
        _ = (wedinLemma20_11_sigmaMinCol B) ^ 2 * vecNorm2Sq x := by
            simpa [wedinLemma20_11_sigmaMinCol] using hsq
        _ = (wedinLemma20_11_sigmaMinCol B) ^ 2 * vecNorm2 x ^ 2 := by
            rw [← vecNorm2_sq x]
        _ = (wedinLemma20_11_sigmaMinCol B * vecNorm2 x) ^ 2 := by
            ring
    have hmul :
        (wedinLemma20_11_sigmaMinCol A - delta) * vecNorm2 x ≤
          wedinLemma20_11_sigmaMinCol B * vecNorm2 x := by
      simpa [hB_norm_eq] using hB_lower
    nlinarith
  · have hB_nonneg := wedinLemma20_11_sigmaMinCol_nonneg B
    linarith

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    a strict full-column perturbation below `sigma_min(A)` makes
    `sigma_min(B)` positive. -/
theorem wedinLemma20_11_sigmaMinCol_pos_of_sub_rectOpNorm2Le_lt
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ) {delta : ℝ}
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hsmall : delta < wedinLemma20_11_sigmaMinCol A) :
    0 < wedinLemma20_11_sigmaMinCol B := by
  have hgap :=
    wedinLemma20_11_sigmaMinCol_sub_le_sigmaMinCol_of_sub_rectOpNorm2Le
      A B hDelta
  have hpos : 0 < wedinLemma20_11_sigmaMinCol A - delta := by
    linarith
  exact lt_of_lt_of_le hpos hgap

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    strict perturbations below a lower action radius preserve injectivity.

    This is a full-column-rank consequence of the source singular-value
    perturbation line.  It is not the general equal-rank pseudoinverse theorem,
    but it gives the rank-preservation bridge needed by full-rank LS uses of
    Wedin's theorem. -/
theorem wedinLemma20_11_rectMatMulVec_injective_of_sub_rectOpNorm2Le_lt
    {m n : ℕ} (A B : Fin m → Fin n → ℝ) {sigma delta : ℝ}
    (hlower : ∀ x : Fin n → ℝ,
      sigma * vecNorm2 x ≤ vecNorm2 (rectMatMulVec A x))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hsmall : delta < sigma) :
    Function.Injective (rectMatMulVec B) := by
  have h :=
    rectMatMulVec_injective_of_lower_bound_and_rectOpNorm2Le_lt
      (M := A) (Delta := fun i j => B i j - A i j)
      hlower hDelta hsmall
  have hmat : (fun i j => A i j + (B i j - A i j)) = B := by
    ext i j
    ring
  simpa [hmat] using h

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    scalar rearrangement step from the singular-value perturbation lower bound.

    The missing spectral input is the hypothesis `sigmaA - delta <= sigmaB`,
    where `delta = ||A - B||₂`, `sigmaA = ||A⁺||₂⁻¹`, and
    `sigmaB = ||B⁺||₂⁻¹`.  This theorem proves only the source's final
    reciprocal algebra, not the singular-value perturbation theorem itself. -/
theorem wedinLemma20_11_pinvNorm_le_of_singularValue_gap
    {Aplus_norm Bplus_norm delta eta sigmaA sigmaB : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hsigmaA : sigmaA = 1 / Aplus_norm)
    (hBplus : Bplus_norm = 1 / sigmaB)
    (hgap : sigmaA - delta ≤ sigmaB) :
    Bplus_norm ≤ Aplus_norm / (1 - eta) := by
  subst eta
  have hden_pos : 0 < 1 - Aplus_norm * delta :=
    wedinLemma20_11_denominator_pos hsmall
  have hdelta_lt : delta < 1 / Aplus_norm := by
    rw [lt_div_iff₀ hAplus_pos]
    simpa [mul_comm] using hsmall
  have hgap_pos : 0 < sigmaA - delta := by
    rw [hsigmaA]
    linarith
  have hrecip : 1 / sigmaB ≤ 1 / (sigmaA - delta) :=
    one_div_le_one_div_of_le hgap_pos hgap
  rw [hBplus]
  calc
    1 / sigmaB ≤ 1 / (sigmaA - delta) := hrecip
    _ = Aplus_norm / (1 - Aplus_norm * delta) := by
      rw [hsigmaA]
      field_simp [ne_of_gt hAplus_pos, ne_of_gt hden_pos]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    full-column specialization of the pseudoinverse norm bound.

    Compared with `wedinLemma20_11_pinvNorm_le_of_singularValue_gap`, this
    theorem proves the singular-value perturbation step locally for real
    rectangular matrices with nonempty column dimension.  The remaining
    assumptions are exactly the reciprocal identifications between the
    column-side `sigma_min` values and the displayed pseudoinverse norms. -/
theorem wedinLemma20_11_fullColumn_pinvNorm_le_of_sub_rectOpNorm2Le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    {Aplus_norm Bplus_norm delta eta : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hAplus_sigma :
      wedinLemma20_11_sigmaMinCol A = 1 / Aplus_norm)
    (hBplus_sigma :
      Bplus_norm = 1 / wedinLemma20_11_sigmaMinCol B) :
    Bplus_norm ≤ Aplus_norm / (1 - eta) :=
  wedinLemma20_11_pinvNorm_le_of_singularValue_gap
    (Aplus_norm := Aplus_norm) (Bplus_norm := Bplus_norm)
    (delta := delta) (eta := eta)
    (sigmaA := wedinLemma20_11_sigmaMinCol A)
    (sigmaB := wedinLemma20_11_sigmaMinCol B)
    hAplus_pos heta hsmall hAplus_sigma hBplus_sigma
    (wedinLemma20_11_sigmaMinCol_sub_le_sigmaMinCol_of_sub_rectOpNorm2Le
      A B hDelta)

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    full-column injectivity and the reciprocal identification make the
    displayed pseudoinverse norm positive. -/
theorem wedinLemma20_11_Aplus_norm_pos_of_injective_sigmaMinCol_recip
    {m k : ℕ} (A : Fin m → Fin (k + 1) → ℝ) {Aplus_norm : ℝ}
    (hAinj : Function.Injective (rectMatMulVec A))
    (hAplus_sigma :
      wedinLemma20_11_sigmaMinCol A = 1 / Aplus_norm) :
    0 < Aplus_norm := by
  apply one_div_pos.mp
  rw [← hAplus_sigma]
  exact wedinLemma20_11_sigmaMinCol_pos_of_rectMatMulVec_injective A hAinj

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    under the full-column reciprocal identification, `η = ||A⁺||₂ delta`
    and `η < 1` imply `delta < sigma_min(A)`. -/
theorem wedinLemma20_11_delta_lt_sigmaMinCol_of_injective_eta_lt_one
    {m k : ℕ} (A : Fin m → Fin (k + 1) → ℝ)
    {Aplus_norm delta eta : ℝ}
    (hAinj : Function.Injective (rectMatMulVec A))
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hAplus_sigma :
      wedinLemma20_11_sigmaMinCol A = 1 / Aplus_norm) :
    delta < wedinLemma20_11_sigmaMinCol A := by
  have hAplus_pos :
      0 < Aplus_norm :=
    wedinLemma20_11_Aplus_norm_pos_of_injective_sigmaMinCol_recip
      A hAinj hAplus_sigma
  have hdelta_lt : delta < 1 / Aplus_norm := by
    rw [lt_div_iff₀ hAplus_pos]
    rw [heta] at hsmall
    simpa [mul_comm] using hsmall
  simpa [hAplus_sigma] using hdelta_lt

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    the source smallness condition preserves positivity of the perturbed
    full-column lower singular value. -/
theorem wedinLemma20_11_sigmaMinCol_B_pos_of_injective_eta_lt_one
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    {Aplus_norm delta eta : ℝ}
    (hAinj : Function.Injective (rectMatMulVec A))
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hAplus_sigma :
      wedinLemma20_11_sigmaMinCol A = 1 / Aplus_norm) :
    0 < wedinLemma20_11_sigmaMinCol B :=
  wedinLemma20_11_sigmaMinCol_pos_of_sub_rectOpNorm2Le_lt A B hDelta
    (wedinLemma20_11_delta_lt_sigmaMinCol_of_injective_eta_lt_one
      A hAinj heta hsmall hAplus_sigma)

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    full-column source-shaped pseudoinverse norm perturbation wrapper.

    This version derives the pseudoinverse-norm positivity side condition from
    full-column injectivity of `A` and the reciprocal `sigma_min(A)` identity.
    The still-open pseudoinverse foundations remain explicit as the reciprocal
    norm/singular-value identifications for `A` and `B`. -/
theorem wedinLemma20_11_fullColumn_pinvNorm_le_of_injective_sub_rectOpNorm2Le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    {Aplus_norm Bplus_norm delta eta : ℝ}
    (hAinj : Function.Injective (rectMatMulVec A))
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hAplus_sigma :
      wedinLemma20_11_sigmaMinCol A = 1 / Aplus_norm)
    (hBplus_sigma :
      Bplus_norm = 1 / wedinLemma20_11_sigmaMinCol B) :
    Bplus_norm ≤ Aplus_norm / (1 - eta) :=
  wedinLemma20_11_fullColumn_pinvNorm_le_of_sub_rectOpNorm2Le
    A B
    (wedinLemma20_11_Aplus_norm_pos_of_injective_sigmaMinCol_recip
      A hAinj hAplus_sigma)
    heta hsmall hDelta hAplus_sigma hBplus_sigma

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    any proved full-column lower action radius is bounded above by the
    repository's column-side `sigma_min`. -/
theorem wedinLemma20_11_lowerActionBound_le_sigmaMinCol
    {m k : ℕ} (A : Fin m → Fin (k + 1) → ℝ) {sigma : ℝ}
    (hlower : ∀ x : Fin (k + 1) → ℝ,
      sigma * vecNorm2 x ≤ vecNorm2 (rectMatMulVec A x)) :
    sigma ≤ wedinLemma20_11_sigmaMinCol A := by
  by_cases hsigma_nonneg : 0 ≤ sigma
  · obtain ⟨x, hx_ne, hsq⟩ :=
      realRectToCMatrix_last_singularValue_exists_real_attaining_vector_sq A
    have hx_norm_ne : vecNorm2 x ≠ 0 := by
      intro hx_norm
      apply hx_ne
      ext j
      exact (vecNorm2_eq_zero_iff x).mp hx_norm j
    have hx_norm_pos : 0 < vecNorm2 x :=
      lt_of_le_of_ne (vecNorm2_nonneg x) (Ne.symm hx_norm_ne)
    have hA_norm_eq :
        vecNorm2 (rectMatMulVec A x) =
          wedinLemma20_11_sigmaMinCol A * vecNorm2 x := by
      apply (sq_eq_sq₀
        (vecNorm2_nonneg (rectMatMulVec A x))
        (mul_nonneg (wedinLemma20_11_sigmaMinCol_nonneg A)
          (vecNorm2_nonneg x))).mp
      calc
        vecNorm2 (rectMatMulVec A x) ^ 2 =
            vecNorm2Sq (rectMatMulVec A x) := vecNorm2_sq _
        _ = (wedinLemma20_11_sigmaMinCol A) ^ 2 * vecNorm2Sq x := by
            simpa [wedinLemma20_11_sigmaMinCol] using hsq
        _ = (wedinLemma20_11_sigmaMinCol A) ^ 2 * vecNorm2 x ^ 2 := by
            rw [← vecNorm2_sq x]
        _ = (wedinLemma20_11_sigmaMinCol A * vecNorm2 x) ^ 2 := by
            ring
    have hmul :
        sigma * vecNorm2 x ≤
          wedinLemma20_11_sigmaMinCol A * vecNorm2 x := by
      simpa [hA_norm_eq] using hlower x
    nlinarith
  · have hA_nonneg := wedinLemma20_11_sigmaMinCol_nonneg A
    linarith

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    an explicit left inverse `Aplus A = I` and an operator-norm bound on
    `Aplus` give the lower action radius `1 / Aplus_norm` for `A`. -/
theorem wedinLemma20_11_lowerActionBound_of_left_inverse_rectOpNorm2Le
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ)
    {Aplus_norm : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (hleft : rectMatMul Aplus A = idMatrix n)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm) :
    ∀ x : Fin n → ℝ,
      (1 / Aplus_norm) * vecNorm2 x ≤ vecNorm2 (rectMatMulVec A x) := by
  intro x
  have hleft_vec :
      rectMatMulVec Aplus (rectMatMulVec A x) = x := by
    rw [← rectMatMulVec_rectMatMul Aplus A x]
    rw [hleft]
    rw [rectMatMulVec_idMatrix]
  have hbound := hAplus (rectMatMulVec A x)
  have hx_bound :
      vecNorm2 x ≤ Aplus_norm * vecNorm2 (rectMatMulVec A x) := by
    simpa [hleft_vec] using hbound
  have hrec_nonneg : 0 ≤ 1 / Aplus_norm :=
    le_of_lt (one_div_pos.mpr hAplus_pos)
  calc
    (1 / Aplus_norm) * vecNorm2 x
        ≤ (1 / Aplus_norm) *
            (Aplus_norm * vecNorm2 (rectMatMulVec A x)) :=
          mul_le_mul_of_nonneg_left hx_bound hrec_nonneg
    _ = vecNorm2 (rectMatMulVec A x) := by
          field_simp [ne_of_gt hAplus_pos]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    source-shaped singular-value lower bound obtained from an explicit left
    inverse of `A` and a perturbation bound for `B - A`. -/
theorem wedinLemma20_11_recip_sub_le_sigmaMinCol_of_left_inverse_rectOpNorm2Le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus : Fin (k + 1) → Fin m → ℝ) {Aplus_norm delta : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (hleft : rectMatMul Aplus A = idMatrix (k + 1))
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta) :
    1 / Aplus_norm - delta ≤ wedinLemma20_11_sigmaMinCol B := by
  have hlowerA :
      ∀ x : Fin (k + 1) → ℝ,
        (1 / Aplus_norm) * vecNorm2 x ≤
          vecNorm2 (rectMatMulVec A x) :=
    wedinLemma20_11_lowerActionBound_of_left_inverse_rectOpNorm2Le
      A Aplus hAplus_pos hleft hAplus
  have hlowerB :
      ∀ x : Fin (k + 1) → ℝ,
        (1 / Aplus_norm - delta) * vecNorm2 x ≤
          vecNorm2 (rectMatMulVec B x) :=
    wedinLemma20_11_lowerActionBound_of_sub_rectOpNorm2Le
      A B hlowerA hDelta
  exact wedinLemma20_11_lowerActionBound_le_sigmaMinCol B hlowerB

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    full-column pseudoinverse norm perturbation from an explicit left inverse
    of `A` and an operator-norm bound on that left inverse.

    This removes the separate assumption
    `sigma_min(A) = 1 / ||Aplus||_2`; the remaining reciprocal identification
    is the perturbed-side norm identity for `Bplus`. -/
theorem wedinLemma20_11_fullColumn_pinvNorm_le_of_left_inverse_rectOpNorm2Le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus : Fin (k + 1) → Fin m → ℝ)
    {Aplus_norm Bplus_norm delta eta : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleft : rectMatMul Aplus A = idMatrix (k + 1))
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBplus_sigma :
      Bplus_norm = 1 / wedinLemma20_11_sigmaMinCol B) :
    Bplus_norm ≤ Aplus_norm / (1 - eta) :=
  wedinLemma20_11_pinvNorm_le_of_singularValue_gap
    (Aplus_norm := Aplus_norm) (Bplus_norm := Bplus_norm)
    (delta := delta) (eta := eta)
    (sigmaA := 1 / Aplus_norm)
    (sigmaB := wedinLemma20_11_sigmaMinCol B)
    hAplus_pos heta hsmall rfl hBplus_sigma
    (wedinLemma20_11_recip_sub_le_sigmaMinCol_of_left_inverse_rectOpNorm2Le
      A B Aplus hAplus_pos hleft hAplus hDelta)

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    a lower action radius for `B`, together with the Moore-Penrose range-side
    projection conditions, bounds the rectangular operator norm of `Bplus`.

    The hypotheses `Bplus B = I` and symmetry of `B Bplus` are exactly the
    full-column Penrose fields needed to make the range projection
    nonexpansive. -/
theorem wedinLemma20_11_rectOpNorm2Le_left_inverse_of_lowerActionBound
    {m n : ℕ} (B : Fin m → Fin n → ℝ) (Bplus : Fin n → Fin m → ℝ)
    {sigma : ℝ}
    (hsigma_pos : 0 < sigma)
    (hlower : ∀ x : Fin n → ℝ,
      sigma * vecNorm2 x ≤ vecNorm2 (rectMatMulVec B x))
    (hleft : rectMatMul Bplus B = idMatrix n)
    (hSym : IsSymmetricFiniteMatrix (rectMatMul B Bplus)) :
    rectOpNorm2Le Bplus (1 / sigma) := by
  intro y
  have hproj :=
    rectOpNorm2Le_rangeProjection_of_symmetric_left_inverse B Bplus
      hleft hSym y
  have hproj' :
      vecNorm2 (rectMatMulVec B (rectMatMulVec Bplus y)) ≤ vecNorm2 y := by
    simpa [rectMatMulVec_rectMatMul] using hproj
  have hlower_y := hlower (rectMatMulVec Bplus y)
  have hbound :
      sigma * vecNorm2 (rectMatMulVec Bplus y) ≤ vecNorm2 y :=
    le_trans hlower_y hproj'
  have hrec_nonneg : 0 ≤ 1 / sigma :=
    le_of_lt (one_div_pos.mpr hsigma_pos)
  calc
    vecNorm2 (rectMatMulVec Bplus y)
        = (1 / sigma) * (sigma * vecNorm2 (rectMatMulVec Bplus y)) := by
            field_simp [ne_of_gt hsigma_pos]
    _ ≤ (1 / sigma) * vecNorm2 y :=
            mul_le_mul_of_nonneg_left hbound hrec_nonneg

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    full-column predicate-form pseudoinverse norm perturbation bound.

    This is the source Lemma 20.11 route in the repository's
    `rectOpNorm2Le` API: an explicit left inverse for `A`, the perturbation
    bound for `B - A`, and the full-column Penrose range-projection fields for
    `Bplus` imply `||Bplus||₂ <= ||Aplus||₂ / (1 - eta)`. -/
theorem wedinLemma20_11_rectOpNorm2Le_Bplus_of_left_inverse_rectOpNorm2Le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {Aplus_norm delta eta : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus)) :
    rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)) := by
  subst eta
  have hden_pos : 0 < 1 - Aplus_norm * delta :=
    wedinLemma20_11_denominator_pos hsmall
  have hdelta_lt : delta < 1 / Aplus_norm := by
    rw [lt_div_iff₀ hAplus_pos]
    simpa [mul_comm] using hsmall
  have hmu_pos : 0 < 1 / Aplus_norm - delta := by
    linarith
  have hlowerA :
      ∀ x : Fin (k + 1) → ℝ,
        (1 / Aplus_norm) * vecNorm2 x ≤
          vecNorm2 (rectMatMulVec A x) :=
    wedinLemma20_11_lowerActionBound_of_left_inverse_rectOpNorm2Le
      A Aplus hAplus_pos hleftA hAplus
  have hlowerB :
      ∀ x : Fin (k + 1) → ℝ,
        (1 / Aplus_norm - delta) * vecNorm2 x ≤
          vecNorm2 (rectMatMulVec B x) :=
    wedinLemma20_11_lowerActionBound_of_sub_rectOpNorm2Le
      A B hlowerA hDelta
  have hBplus :
      rectOpNorm2Le Bplus (1 / (1 / Aplus_norm - delta)) :=
    wedinLemma20_11_rectOpNorm2Le_left_inverse_of_lowerActionBound
      B Bplus hmu_pos hlowerB hleftB hSymB
  have hcoeff :
      (Aplus_norm⁻¹ - delta)⁻¹ =
        Aplus_norm / (1 - Aplus_norm * delta) := by
    field_simp [ne_of_gt hAplus_pos, ne_of_gt hmu_pos, ne_of_gt hden_pos]
  simpa [one_div, hcoeff] using hBplus

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    full-column predicate-form pseudoinverse perturbation bound with the
    perturbed-side left inverse derived from the first Penrose equation.

    The Chapter 7 Moore-Penrose bridge turns `B Bplus B = B` plus injectivity
    of `x ↦ B*x` into `Bplus B = I`, leaving the same range-projection
    symmetry condition used by the direct operator-bound theorem above. -/
theorem wedinLemma20_11_rectOpNorm2Le_Bplus_of_penrose1_injective_rectOpNorm2Le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {Aplus_norm delta eta : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBpenrose1 : rectMatMul (rectMatMul B Bplus) B = B)
    (hBinj : Function.Injective (rectMatMulVec B))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus)) :
    rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)) := by
  have hleftB : rectMatMul Bplus B = idMatrix (k + 1) := by
    ext i j
    simpa [rectMatMul, idMatrix] using
      theorem7_5_rect_left_inverse_of_penrose1_rectMatMulVec_injective
        B Bplus hBpenrose1 hBinj i j
  exact
    wedinLemma20_11_rectOpNorm2Le_Bplus_of_left_inverse_rectOpNorm2Le
      A B Aplus Bplus hAplus_pos heta hsmall hleftA hAplus hDelta
      hleftB hSymB

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    full-column predicate-form pseudoinverse perturbation bound with the
    perturbed-side injectivity derived from the smallness condition.

    The A-side left inverse and operator bound supply the lower action radius
    `1 / Aplus_norm`; the source smallness condition `eta = Aplus_norm * delta
    < 1` makes the perturbation strict enough to preserve injectivity of `B`.
    The first Penrose equation for `Bplus` then supplies the remaining
    perturbed-side left-inverse field. -/
theorem wedinLemma20_11_rectOpNorm2Le_Bplus_of_penrose1_small_rectOpNorm2Le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {Aplus_norm delta eta : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBpenrose1 : rectMatMul (rectMatMul B Bplus) B = B)
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus)) :
    rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)) := by
  have hsmall_mul : Aplus_norm * delta < 1 := by
    simpa [heta] using hsmall
  have hdelta_lt : delta < 1 / Aplus_norm := by
    rw [lt_div_iff₀ hAplus_pos]
    simpa [mul_comm] using hsmall_mul
  have hlowerA :
      ∀ x : Fin (k + 1) → ℝ,
        (1 / Aplus_norm) * vecNorm2 x ≤
          vecNorm2 (rectMatMulVec A x) :=
    wedinLemma20_11_lowerActionBound_of_left_inverse_rectOpNorm2Le
      A Aplus hAplus_pos hleftA hAplus
  have hBinj : Function.Injective (rectMatMulVec B) :=
    wedinLemma20_11_rectMatMulVec_injective_of_sub_rectOpNorm2Le_lt
      A B hlowerA hDelta hdelta_lt
  exact
    wedinLemma20_11_rectOpNorm2Le_Bplus_of_penrose1_injective_rectOpNorm2Le
      A B Aplus Bplus hAplus_pos heta hsmall hleftA hAplus hDelta
      hBpenrose1 hBinj hSymB

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    full-column predicate-form pseudoinverse perturbation bound with both
    rectangular left-inverse fields derived from Penrose1 data.

    On the `A` side, Penrose1 plus injectivity gives `Aplus A = I`; the
    smallness condition then preserves injectivity for `B`, and Penrose1 plus
    the Chapter 7 bridge gives `Bplus B = I`. -/
theorem wedinLemma20_11_rectOpNorm2Le_Bplus_of_Apenrose1_Bpenrose1_small_rectOpNorm2Le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {Aplus_norm delta eta : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hApenrose1 : rectMatMul (rectMatMul A Aplus) A = A)
    (hAinj : Function.Injective (rectMatMulVec A))
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBpenrose1 : rectMatMul (rectMatMul B Bplus) B = B)
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus)) :
    rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)) := by
  have hleftA : rectMatMul Aplus A = idMatrix (k + 1) := by
    ext i j
    simpa [rectMatMul, idMatrix] using
      theorem7_5_rect_left_inverse_of_penrose1_rectMatMulVec_injective
        A Aplus hApenrose1 hAinj i j
  exact
    wedinLemma20_11_rectOpNorm2Le_Bplus_of_penrose1_small_rectOpNorm2Le
      A B Aplus Bplus hAplus_pos heta hsmall hleftA hAplus hDelta
      hBpenrose1 hSymB

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    matrix-rank source wrapper for the full-column predicate-form
    pseudoinverse perturbation bound.

    Full column rank of `A` is represented by `(Matrix.of A).rank = k + 1`;
    Chapter 7 turns that rank hypothesis and A-side Penrose1 into the explicit
    left inverse needed by the operator-bound route. -/
theorem wedinLemma20_11_rectOpNorm2Le_Bplus_of_Apenrose1_rank_Bpenrose1_small_rectOpNorm2Le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {Aplus_norm delta eta : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hApenrose1 : rectMatMul (rectMatMul A Aplus) A = A)
    (hArank : (Matrix.of A).rank = k + 1)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBpenrose1 : rectMatMul (rectMatMul B Bplus) B = B)
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus)) :
    rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)) :=
  wedinLemma20_11_rectOpNorm2Le_Bplus_of_Apenrose1_Bpenrose1_small_rectOpNorm2Le
    A B Aplus Bplus hAplus_pos heta hsmall hApenrose1
    (ch7_rectMatMulVec_injective_of_matrix_rank_eq_width A hArank)
    hAplus hDelta hBpenrose1 hSymB

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    applying the complement of a square projection is the vector residual
    `x - P*x`. -/
theorem wedinLemma20_12_rectMatMulVec_projectionComplement
    {m : ℕ} (P : Fin m → Fin m → ℝ) (x : Fin m → ℝ) :
    rectMatMulVec (fun i j => idMatrix m i j - P i j) x =
      fun i => x i - rectMatMulVec P x i := by
  ext i
  unfold rectMatMulVec
  calc
    (∑ j : Fin m, (idMatrix m i j - P i j) * x j)
        = (∑ j : Fin m, idMatrix m i j * x j) -
            ∑ j : Fin m, P i j * x j := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = x i - ∑ j : Fin m, P i j * x j := by
          have hid :
              (∑ j : Fin m, idMatrix m i j * x j) = x i := by
            simpa [rectMatMulVec] using
              congrFun (rectMatMulVec_idMatrix x) i
          rw [hid]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    a symmetric Moore-Penrose range projection has a nonexpansive complement
    `I - A Aplus`. -/
theorem wedinLemma20_12_rectOpNorm2Le_projectionComplement_of_symmetric_left_inverse
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ)
    (hleft : rectMatMul Aplus A = idMatrix n)
    (hSym : IsSymmetricFiniteMatrix (rectMatMul A Aplus)) :
    rectOpNorm2Le (fun i j => idMatrix m i j - rectMatMul A Aplus i j) 1 := by
  intro y
  have hbest :=
    rectMatMulVec_rangeProjection_residual_norm_le_range_residual_of_symmetric_left_inverse
      A Aplus hleft hSym y (fun _ : Fin n => 0)
  have hzero :
      (fun i : Fin m => y i - rectMatMulVec A (fun _ : Fin n => 0) i) = y := by
    ext i
    simp [rectMatMulVec]
  simpa [wedinLemma20_12_rectMatMulVec_projectionComplement, hzero] using hbest

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    reversing a matrix difference preserves a rectangular operator-2 bound. -/
theorem wedinLemma20_12_rectOpNorm2Le_sub_rev
    {m n : ℕ} (A B : Fin m → Fin n → ℝ) {delta : ℝ}
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta) :
    rectOpNorm2Le (fun i j => A i j - B i j) delta := by
  intro x
  have hmul :
      rectMatMulVec (fun i j => A i j - B i j) x =
        fun i => -rectMatMulVec (fun i j => B i j - A i j) x i := by
    ext i
    unfold rectMatMulVec
    calc
      (∑ j : Fin n, (A i j - B i j) * x j)
          = ∑ j : Fin n, -((B i j - A i j) * x j) := by
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = -(∑ j : Fin n, (B i j - A i j) * x j) := by
              rw [Finset.sum_neg_distrib]
  rw [hmul]
  simpa [vecNorm2_neg] using hDelta x

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12:
    one-sided projection perturbation bound from the source proof.

    This proves the elementary half
    `||(I - P_A) P_B||_2 <= ||A - B||_2 ||Bplus||_2` in the repository's
    predicate API.  The nontrivial CS-decomposition equality
    `||P_A(I-P_B)||_2 = ||P_B(I-P_A)||_2` is not claimed here. -/
theorem wedinLemma20_12_rectOpNorm2Le_complement_rangeProjection_mul_rangeProjection
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {delta Bplus_norm : ℝ}
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBplus : rectOpNorm2Le Bplus Bplus_norm) :
    rectOpNorm2Le
      (rectMatMul
        (fun i j => idMatrix m i j - rectMatMul A Aplus i j)
        (rectMatMul B Bplus))
      (delta * Bplus_norm) := by
  let IPA : Fin m → Fin m → ℝ :=
    fun i j => idMatrix m i j - rectMatMul A Aplus i j
  have hIPA :
      rectOpNorm2Le IPA 1 :=
    wedinLemma20_12_rectOpNorm2Le_projectionComplement_of_symmetric_left_inverse
      A Aplus hleftA hSymA
  have hIPA_A_zero : ∀ z : Fin (k + 1) → ℝ,
      rectMatMulVec IPA (rectMatMulVec A z) = 0 := by
    intro z
    have hfix :=
      rectMatMulVec_rangeProjection_apply_range_of_left_inverse A Aplus
        hleftA z
    rw [wedinLemma20_12_rectMatMulVec_projectionComplement]
    rw [hfix]
    ext i
    simp
  have hdelta_nonneg : 0 ≤ delta :=
    rectOpNorm2Le_radius_nonneg (M := fun i j => B i j - A i j) hDelta
  intro y
  let z : Fin (k + 1) → ℝ := rectMatMulVec Bplus y
  have hB_decomp :
      rectMatMulVec B z =
        fun i : Fin m =>
          rectMatMulVec (fun i j => B i j - A i j) z i +
            rectMatMulVec A z i := by
    ext i
    unfold rectMatMulVec
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hvec :
      rectMatMulVec
          (rectMatMul IPA (rectMatMul B Bplus)) y =
        rectMatMulVec IPA
          (rectMatMulVec (fun i j => B i j - A i j) z) := by
    calc
      rectMatMulVec (rectMatMul IPA (rectMatMul B Bplus)) y
          = rectMatMulVec IPA (rectMatMulVec (rectMatMul B Bplus) y) := by
              rw [rectMatMulVec_rectMatMul]
      _ = rectMatMulVec IPA (rectMatMulVec B z) := by
              rw [rectMatMulVec_rectMatMul]
      _ = rectMatMulVec IPA
            (fun i : Fin m =>
              rectMatMulVec (fun i j => B i j - A i j) z i +
                rectMatMulVec A z i) := by
              rw [hB_decomp]
      _ = fun i : Fin m =>
            rectMatMulVec IPA
                (rectMatMulVec (fun i j => B i j - A i j) z) i +
              rectMatMulVec IPA (rectMatMulVec A z) i := by
              rw [rectMatMulVec_add]
      _ = rectMatMulVec IPA
            (rectMatMulVec (fun i j => B i j - A i j) z) := by
              rw [hIPA_A_zero z]
              ext i
              simp
  have hproj :=
    hIPA (rectMatMulVec (fun i j => B i j - A i j) z)
  have hDelta_y := hDelta z
  have hBplus_y := hBplus y
  calc
    vecNorm2 (rectMatMulVec (rectMatMul IPA (rectMatMul B Bplus)) y)
        = vecNorm2
            (rectMatMulVec IPA
              (rectMatMulVec (fun i j => B i j - A i j) z)) := by
            rw [hvec]
    _ ≤ vecNorm2 (rectMatMulVec (fun i j => B i j - A i j) z) := by
            simpa using hproj
    _ ≤ delta * vecNorm2 z := hDelta_y
    _ ≤ delta * (Bplus_norm * vecNorm2 y) :=
            mul_le_mul_of_nonneg_left hBplus_y hdelta_nonneg
    _ = (delta * Bplus_norm) * vecNorm2 y := by ring

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12:
    swapped one-sided projection perturbation bound from the source proof.

    This is the companion elementary half
    `||(I - P_B) P_A||_2 <= ||A - B||_2 ||Aplus||_2` in the repository's
    predicate API.  As above, this does not claim the nontrivial equality of
    the two cross-projection operator norms. -/
theorem wedinLemma20_12_rectOpNorm2Le_complement_rangeProjection_mul_rangeProjection_swapped
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {delta Aplus_norm : ℝ}
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm) :
    rectOpNorm2Le
      (rectMatMul
        (fun i j => idMatrix m i j - rectMatMul B Bplus i j)
        (rectMatMul A Aplus))
      (delta * Aplus_norm) :=
  wedinLemma20_12_rectOpNorm2Le_complement_rangeProjection_mul_rangeProjection
    B A Bplus Aplus hleftB hSymB
    (wedinLemma20_12_rectOpNorm2Le_sub_rev A B hDelta)
    hAplus

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the complement of a symmetric projection is symmetric. -/
theorem wedinLemma20_12_projectionComplement_symmetric
    {m : ℕ} (P : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P) :
    IsSymmetricFiniteMatrix (fun i j => idMatrix m i j - P i j) := by
  intro i j
  by_cases hij : i = j
  · subst j
    simp [idMatrix]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [idMatrix, hij, hji, hP i j]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the complement of an algebraic projection is again an algebraic
    projection. -/
theorem wedinLemma20_12_projectionComplement_idempotent
    {m : ℕ} (P : Fin m → Fin m → ℝ)
    (hIdem : rectMatMul P P = P) :
    rectMatMul (fun i j => idMatrix m i j - P i j)
      (fun i j => idMatrix m i j - P i j) =
        fun i j => idMatrix m i j - P i j := by
  ext i j
  unfold rectMatMul idMatrix
  simp_rw [sub_mul, mul_sub]
  simp [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ]
  have hij := congrFun (congrFun hIdem i) j
  unfold rectMatMul at hij
  rw [hij]
  ring

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    a projection annihilates its complement on the right. -/
theorem wedinLemma20_12_rangeProjection_mul_projectionComplement_eq_zero
    {m : ℕ} (P : Fin m → Fin m → ℝ)
    (hIdem : rectMatMul P P = P) :
    rectMatMul P (fun i j => idMatrix m i j - P i j) =
      fun _ _ => 0 := by
  ext i j
  unfold rectMatMul idMatrix
  simp_rw [mul_sub]
  simp [Finset.sum_sub_distrib, Finset.mem_univ]
  have hij := congrFun (congrFun hIdem i) j
  unfold rectMatMul at hij
  rw [hij]
  ring

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    a projection complement annihilates the projection on the right. -/
theorem wedinLemma20_12_projectionComplement_mul_rangeProjection_eq_zero
    {m : ℕ} (P : Fin m → Fin m → ℝ)
    (hIdem : rectMatMul P P = P) :
    rectMatMul (fun i j => idMatrix m i j - P i j) P =
      fun _ _ => 0 := by
  ext i j
  unfold rectMatMul idMatrix
  simp_rw [sub_mul]
  simp [Finset.sum_sub_distrib, Finset.mem_univ]
  have hij := congrFun (congrFun hIdem i) j
  unfold rectMatMul at hij
  rw [hij]
  ring

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    a symmetric algebraic projection decomposes squared Euclidean norm into
    range and orthogonal-complement pieces. -/
theorem wedinLemma20_12_vecNorm2Sq_rangeProjection_add_complement
    {m : ℕ} (P : Fin m → Fin m → ℝ)
    (hSym : IsSymmetricFiniteMatrix P)
    (hIdem : rectMatMul P P = P)
    (x : Fin m → ℝ) :
    vecNorm2Sq (rectMatMulVec P x) +
        vecNorm2Sq (rectMatMulVec (fun i j => idMatrix m i j - P i j) x) =
      vecNorm2Sq x := by
  let IP : Fin m → Fin m → ℝ := fun i j => idMatrix m i j - P i j
  have hIdemFin : ∀ i j : Fin m, finiteMatMul P P i j = P i j := by
    intro i j
    simpa [finiteMatMul, rectMatMul] using congrFun (congrFun hIdem i) j
  have hIPx : rectMatMulVec IP x = fun i => x i - rectMatMulVec P x i := by
    simpa [IP] using wedinLemma20_12_rectMatMulVec_projectionComplement P x
  have horth_res :
      (∑ i : Fin m, (x i - rectMatMulVec P x i) * rectMatMulVec P x i) = 0 := by
    simpa [finiteMatVec, rectMatMulVec] using
      finiteVecInnerProduct_projection_residual_range_eq_zero
        P hSym hIdemFin x x
  have horth :
      (∑ i : Fin m, rectMatMulVec P x i * rectMatMulVec IP x i) = 0 := by
    calc
      (∑ i : Fin m, rectMatMulVec P x i * rectMatMulVec IP x i)
          = ∑ i : Fin m, (x i - rectMatMulVec P x i) * rectMatMulVec P x i := by
              rw [hIPx]
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = 0 := horth_res
  have hpyth :=
    finiteVecNorm2Sq_add_of_inner_eq_zero
      (rectMatMulVec P x) (rectMatMulVec IP x) horth
  have hdecomp :
      (fun i : Fin m => rectMatMulVec P x i + rectMatMulVec IP x i) = x := by
    rw [hIPx]
    ext i
    ring
  have hpyth' :
      vecNorm2Sq (fun i : Fin m => rectMatMulVec P x i + rectMatMulVec IP x i) =
        vecNorm2Sq (rectMatMulVec P x) + vecNorm2Sq (rectMatMulVec IP x) := by
    simpa [finiteVecNorm2Sq_fin] using hpyth
  rw [hdecomp] at hpyth'
  simpa [IP, add_comm] using hpyth'.symm

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    range/complement squared-norm decomposition after applying the complement
    of another projection.  This is a local CS-route building block for the
    cross terms `P_B(I-P_A)` and `(I-P_B)(I-P_A)`. -/
theorem wedinLemma20_12_vecNorm2Sq_rangeProjection_projectionComplement_add_complement
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hSymQ : IsSymmetricFiniteMatrix Q)
    (hIdemQ : rectMatMul Q Q = Q)
    (x : Fin m → ℝ) :
    vecNorm2Sq
        (rectMatMulVec
          (rectMatMul Q (fun i j => idMatrix m i j - P i j)) x) +
      vecNorm2Sq
        (rectMatMulVec
          (rectMatMul (fun i j => idMatrix m i j - Q i j)
            (fun i j => idMatrix m i j - P i j)) x) =
      vecNorm2Sq
        (rectMatMulVec (fun i j => idMatrix m i j - P i j) x) := by
  let IP : Fin m → Fin m → ℝ := fun i j => idMatrix m i j - P i j
  let IQ : Fin m → Fin m → ℝ := fun i j => idMatrix m i j - Q i j
  have hbase :
      vecNorm2Sq (rectMatMulVec Q (rectMatMulVec IP x)) +
          vecNorm2Sq (rectMatMulVec IQ (rectMatMulVec IP x)) =
        vecNorm2Sq (rectMatMulVec IP x) := by
    simpa [IQ] using
      wedinLemma20_12_vecNorm2Sq_rangeProjection_add_complement
        Q hSymQ hIdemQ (rectMatMulVec IP x)
  have hQIP :
      rectMatMulVec (rectMatMul Q IP) x =
        rectMatMulVec Q (rectMatMulVec IP x) := by
    rw [rectMatMulVec_rectMatMul]
  have hIQIP :
      rectMatMulVec (rectMatMul IQ IP) x =
        rectMatMulVec IQ (rectMatMulVec IP x) := by
    rw [rectMatMulVec_rectMatMul]
  simpa [IP, IQ, hQIP, hIQIP] using hbase

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    transposing a product of symmetric square matrices reverses the product
    order. -/
theorem wedinLemma20_12_finiteTranspose_rectMatMul_of_symmetric
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q) :
    finiteTranspose (rectMatMul P Q) = rectMatMul Q P := by
  ext i j
  unfold finiteTranspose rectMatMul
  apply Finset.sum_congr rfl
  intro l _
  rw [hP j l, hQ l i]
  ring

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    exact complexified operator-2 norms agree for a cross-projection product
    and its transpose.

This turns the repository's algebraic transpose identity for symmetric
projections into an exact `complexMatrixOp2` equality, which is needed by the
CS route toward the missing cross-projection norm equality. -/
theorem wedinLemma20_12_complexMatrixOp2_crossProjection_transpose_eq
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q) :
    complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul P (fun i j => idMatrix m i j - Q i j))) =
      complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul (fun i j => idMatrix m i j - Q i j) P)) := by
  let IQ : Fin m → Fin m → ℝ := fun i j => idMatrix m i j - Q i j
  have hIQ : IsSymmetricFiniteMatrix IQ :=
    wedinLemma20_12_projectionComplement_symmetric Q hQ
  have htranspose :
      finiteTranspose (rectMatMul IQ P) = rectMatMul P IQ :=
    wedinLemma20_12_finiteTranspose_rectMatMul_of_symmetric
      IQ P hIQ hP
  calc
    complexMatrixOp2 (realRectToCMatrix (rectMatMul P IQ))
        = complexMatrixOp2
            (realRectToCMatrix (finiteTranspose (rectMatMul IQ P))) := by
            rw [htranspose]
    _ = complexMatrixOp2 (realRectToCMatrix (rectMatMul IQ P)) := by
            rw [complexMatrixOp2_realRectToCMatrix_finiteTranspose_eq]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the squared exact operator-2 norm of the cross projection `P(I-Q)` is
    the exact operator-2 norm of the compressed Gram product
    `(I-Q)P(I-Q)`.

This is a CS-route reduction step.  It uses only symmetric-idempotent
projection algebra and the rectangular Gram bridge; it does not prove the
Stewart--Sun equality between the two different cross projections. -/
theorem wedinLemma20_12_complexMatrixOp2_compressedGram_eq_crossProjection_sq
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P) :
    complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul
            (rectMatMul (fun i j => idMatrix m i j - Q i j) P)
            (fun i j => idMatrix m i j - Q i j))) =
      complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul P (fun i j => idMatrix m i j - Q i j))) ^ 2 := by
  let IQ : Fin m → Fin m → ℝ := fun i j => idMatrix m i j - Q i j
  have hIQ : IsSymmetricFiniteMatrix IQ :=
    wedinLemma20_12_projectionComplement_symmetric Q hQ
  have hgram :=
    complexMatrixOp2_realRectToCMatrix_finiteTranspose_mul_self_eq_sq
      (rectMatMul P IQ)
  have htranspose :
      finiteTranspose (rectMatMul P IQ) = rectMatMul IQ P :=
    wedinLemma20_12_finiteTranspose_rectMatMul_of_symmetric P IQ hP hIQ
  have hcompressed :
      rectMatMul (finiteTranspose (rectMatMul P IQ)) (rectMatMul P IQ) =
        rectMatMul (rectMatMul IQ P) IQ := by
    rw [htranspose]
    calc
      rectMatMul (rectMatMul IQ P) (rectMatMul P IQ)
          = rectMatMul IQ (rectMatMul P (rectMatMul P IQ)) := by
              rw [rectMatMul_assoc]
      _ = rectMatMul IQ (rectMatMul (rectMatMul P P) IQ) := by
              rw [rectMatMul_assoc]
      _ = rectMatMul IQ (rectMatMul P IQ) := by
              rw [hIdemP]
      _ = rectMatMul (rectMatMul IQ P) IQ := by
              rw [← rectMatMul_assoc]
  calc
    complexMatrixOp2 (realRectToCMatrix (rectMatMul (rectMatMul IQ P) IQ))
        = complexMatrixOp2
            (realRectToCMatrix
              (rectMatMul (finiteTranspose (rectMatMul P IQ))
                (rectMatMul P IQ))) := by
            rw [hcompressed]
    _ = complexMatrixOp2 (realRectToCMatrix (rectMatMul P IQ)) ^ 2 := hgram

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the transposed self-product of `P(I-Q)` is the compressed Gram product
    `(I-Q)P(I-Q)`. -/
theorem wedinLemma20_12_crossProjection_transpose_mul_self_eq_compressedGram
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P) :
    rectMatMul
        (finiteTranspose
          (rectMatMul P (fun i j => idMatrix m i j - Q i j)))
        (rectMatMul P (fun i j => idMatrix m i j - Q i j)) =
      rectMatMul
        (rectMatMul (fun i j => idMatrix m i j - Q i j) P)
        (fun i j => idMatrix m i j - Q i j) := by
  let IQ : Fin m → Fin m → ℝ := fun i j => idMatrix m i j - Q i j
  have hIQ : IsSymmetricFiniteMatrix IQ :=
    wedinLemma20_12_projectionComplement_symmetric Q hQ
  have htranspose :
      finiteTranspose (rectMatMul P IQ) = rectMatMul IQ P :=
    wedinLemma20_12_finiteTranspose_rectMatMul_of_symmetric P IQ hP hIQ
  rw [htranspose]
  calc
    rectMatMul (rectMatMul IQ P) (rectMatMul P IQ)
        = rectMatMul IQ (rectMatMul P (rectMatMul P IQ)) := by
            rw [rectMatMul_assoc]
    _ = rectMatMul IQ (rectMatMul (rectMatMul P P) IQ) := by
            rw [rectMatMul_assoc]
    _ = rectMatMul IQ (rectMatMul P IQ) := by
            rw [hIdemP]
    _ = rectMatMul (rectMatMul IQ P) IQ := by
            rw [← rectMatMul_assoc]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the compressed Gram product `(I-Q)P(I-Q)` is symmetric. -/
theorem wedinLemma20_12_compressedGram_symmetric
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P) :
    IsSymmetricFiniteMatrix
      (rectMatMul
        (rectMatMul (fun i j => idMatrix m i j - Q i j) P)
        (fun i j => idMatrix m i j - Q i j)) := by
  have hEq :=
    wedinLemma20_12_crossProjection_transpose_mul_self_eq_compressedGram
      P Q hP hQ hIdemP
  exact
    IsSymmetricFiniteMatrix_of_eq_rectMatMul_transpose_self
      (rectMatMul P (fun i j => idMatrix m i j - Q i j))
      hEq.symm

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the compressed Gram product `(I-Q)P(I-Q)` is positive semidefinite. -/
theorem wedinLemma20_12_compressedGram_finitePSD
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P) :
    finitePSD
      (rectMatMul
        (rectMatMul (fun i j => idMatrix m i j - Q i j) P)
        (fun i j => idMatrix m i j - Q i j)) := by
  have hEq :=
    wedinLemma20_12_crossProjection_transpose_mul_self_eq_compressedGram
      P Q hP hQ hIdemP
  exact
    finitePSD_of_eq_rectMatMul_transpose_self
      (rectMatMul P (fun i j => idMatrix m i j - Q i j))
      hEq.symm

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    an equality between the compressed Gram projector products implies the
    desired equality between the original cross-projection exact operator-2
    norms.

The remaining mathematical work for the Stewart--Sun/CS route is therefore
isolated to proving the compressed-Gram equality under equal projection ranks. -/
theorem wedinLemma20_12_complexMatrixOp2_crossProjection_eq_of_compressedGram_eq
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (hEq :
      complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul
              (rectMatMul (fun i j => idMatrix m i j - Q i j) P)
              (fun i j => idMatrix m i j - Q i j))) =
        complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul
              (rectMatMul (fun i j => idMatrix m i j - P i j) Q)
              (fun i j => idMatrix m i j - P i j)))) :
    complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul P (fun i j => idMatrix m i j - Q i j))) =
      complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul Q (fun i j => idMatrix m i j - P i j))) := by
  let IP : Fin m → Fin m → ℝ := fun i j => idMatrix m i j - P i j
  let IQ : Fin m → Fin m → ℝ := fun i j => idMatrix m i j - Q i j
  have hP_sq :=
    wedinLemma20_12_complexMatrixOp2_compressedGram_eq_crossProjection_sq
      P Q hP hQ hIdemP
  have hQ_sq :=
    wedinLemma20_12_complexMatrixOp2_compressedGram_eq_crossProjection_sq
      Q P hQ hP hIdemQ
  have hsquares :
      complexMatrixOp2 (realRectToCMatrix (rectMatMul P IQ)) ^ 2 =
        complexMatrixOp2 (realRectToCMatrix (rectMatMul Q IP)) ^ 2 := by
    calc
      complexMatrixOp2 (realRectToCMatrix (rectMatMul P IQ)) ^ 2
          = complexMatrixOp2
              (realRectToCMatrix (rectMatMul (rectMatMul IQ P) IQ)) := by
              rw [hP_sq]
      _ = complexMatrixOp2
              (realRectToCMatrix (rectMatMul (rectMatMul IP Q) IP)) := by
              simpa [IP, IQ] using hEq
      _ = complexMatrixOp2 (realRectToCMatrix (rectMatMul Q IP)) ^ 2 := by
              rw [hQ_sq]
  exact (sq_eq_sq₀
    (complexMatrixOp2_nonneg (realRectToCMatrix (rectMatMul P IQ)))
    (complexMatrixOp2_nonneg (realRectToCMatrix (rectMatMul Q IP)))).mp
    hsquares

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    left multiplication by the complement `(I-Q)` agrees with multiplication
    by the projection difference `(P-Q)` after a right factor `P`. -/
theorem wedinLemma20_12_projectionComplement_mul_projection_eq_diff_mul_projection
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P) :
    rectMatMul (fun i j => idMatrix m i j - Q i j) P =
      rectMatMul (fun i j => P i j - Q i j) P := by
  ext i j
  unfold rectMatMul idMatrix
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp [Finset.sum_ite_eq, Finset.mem_univ]
  have hij := congrFun (congrFun hIdemP i) j
  unfold rectMatMul at hij
  rw [hij]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    right multiplication by the complement `(I-Q)` agrees with multiplication
    by the projection difference `(P-Q)` after a left factor `P`. -/
theorem wedinLemma20_12_projection_mul_projectionComplement_eq_projection_mul_diff
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P) :
    rectMatMul P (fun i j => idMatrix m i j - Q i j) =
      rectMatMul P (fun i j => P i j - Q i j) := by
  ext i j
  unfold rectMatMul idMatrix
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp [Finset.mem_univ]
  have hij := congrFun (congrFun hIdemP i) j
  unfold rectMatMul at hij
  rw [hij]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the compressed Gram product `(I-Q)P(I-Q)` can be written as
    `(P-Q)P(P-Q)`.

This is the projector-difference normal form used by spectral proofs of the
equal-rank cross-projection norm identity. -/
theorem wedinLemma20_12_compressedGram_eq_diff_projection_diff
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P) :
    rectMatMul
        (rectMatMul (fun i j => idMatrix m i j - Q i j) P)
        (fun i j => idMatrix m i j - Q i j) =
      rectMatMul
        (rectMatMul (fun i j => P i j - Q i j) P)
        (fun i j => P i j - Q i j) := by
  let IQ : Fin m → Fin m → ℝ := fun i j => idMatrix m i j - Q i j
  let D : Fin m → Fin m → ℝ := fun i j => P i j - Q i j
  have hleft : rectMatMul IQ P = rectMatMul D P := by
    simpa [IQ, D] using
      wedinLemma20_12_projectionComplement_mul_projection_eq_diff_mul_projection
        P Q hIdemP
  have hright : rectMatMul P IQ = rectMatMul P D := by
    simpa [IQ, D] using
      wedinLemma20_12_projection_mul_projectionComplement_eq_projection_mul_diff
        P Q hIdemP
  calc
    rectMatMul (rectMatMul IQ P) IQ
        = rectMatMul (rectMatMul D P) IQ := by
            rw [hleft]
    _ = rectMatMul D (rectMatMul P IQ) := by
            rw [rectMatMul_assoc]
    _ = rectMatMul D (rectMatMul P D) := by
            rw [hright]
    _ = rectMatMul (rectMatMul D P) D := by
            rw [← rectMatMul_assoc]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the range-side cross Gram product `P(I-Q)P` is the compression
    `P(P-Q)^2P` of the squared projection difference.

This is the algebraic shape used by principal-angle proofs of the
Stewart--Sun cross-projection norm equality. -/
theorem wedinLemma20_12_projection_projectionDiff_sq_projection_eq_crossGram
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    rectMatMul
        (rectMatMul P
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)))
        P =
      rectMatMul
        (rectMatMul P (fun i j => idMatrix m i j - Q i j))
        P := by
  let D : Fin m → Fin m → ℝ := fun i j => P i j - Q i j
  let IQ : Fin m → Fin m → ℝ := fun i j => idMatrix m i j - Q i j
  have hPD : rectMatMul P D = rectMatMul P IQ := by
    symm
    simpa [D, IQ] using
      wedinLemma20_12_projection_mul_projectionComplement_eq_projection_mul_diff
        P Q hIdemP
  have hDP : rectMatMul D P = rectMatMul IQ P := by
    symm
    simpa [D, IQ] using
      wedinLemma20_12_projectionComplement_mul_projection_eq_diff_mul_projection
        P Q hIdemP
  have hIQIdem : rectMatMul IQ IQ = IQ := by
    simpa [IQ] using
      wedinLemma20_12_projectionComplement_idempotent Q hIdemQ
  calc
    rectMatMul (rectMatMul P (rectMatMul D D)) P
        = rectMatMul (rectMatMul (rectMatMul P D) D) P := by
            rw [← rectMatMul_assoc]
    _ = rectMatMul (rectMatMul P D) (rectMatMul D P) := by
            rw [rectMatMul_assoc]
    _ = rectMatMul (rectMatMul P IQ) (rectMatMul IQ P) := by
            rw [hPD, hDP]
    _ = rectMatMul (rectMatMul (rectMatMul P IQ) IQ) P := by
            exact (rectMatMul_assoc (rectMatMul P IQ) IQ P).symm
    _ = rectMatMul (rectMatMul P (rectMatMul IQ IQ)) P := by
            exact congrArg (fun X => rectMatMul X P)
              (rectMatMul_assoc P IQ IQ)
    _ = rectMatMul (rectMatMul P IQ) P := by
            rw [hIQIdem]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    swapped range-side cross Gram product `Q(I-P)Q` as the compression
    `Q(P-Q)^2Q` of the same squared projection difference. -/
theorem wedinLemma20_12_projection_projectionDiff_sq_projection_eq_crossGram_swapped
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    rectMatMul
        (rectMatMul Q
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)))
        Q =
      rectMatMul
        (rectMatMul Q (fun i j => idMatrix m i j - P i j))
        Q := by
  have hbase :=
    wedinLemma20_12_projection_projectionDiff_sq_projection_eq_crossGram
      Q P hIdemQ hIdemP
  have hsq :
      rectMatMul (fun i j => Q i j - P i j)
          (fun i j => Q i j - P i j) =
        rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j) := by
    ext i j
    unfold rectMatMul
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsq] at hbase
  simpa using hbase

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    multiplying the projection difference `P-Q` by the complement `I-Q` on
    the right removes the `Q` part.

This is an invariant-subspace algebra step for the direct
Stewart--Sun/principal-angle route. -/
theorem wedinLemma20_12_projectionDiff_mul_projectionComplement_eq_projection_mul_projectionComplement
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemQ : rectMatMul Q Q = Q) :
    rectMatMul (fun i j => P i j - Q i j)
        (fun i j => idMatrix m i j - Q i j) =
      rectMatMul P (fun i j => idMatrix m i j - Q i j) := by
  let IQ : Fin m → Fin m → ℝ := fun i j => idMatrix m i j - Q i j
  have hQIQ : rectMatMul Q IQ = fun _ _ => 0 := by
    simpa [IQ] using
      wedinLemma20_12_rangeProjection_mul_projectionComplement_eq_zero
        Q hIdemQ
  calc
    rectMatMul (fun i j => P i j - Q i j) IQ
        = (fun i j => rectMatMul P IQ i j - rectMatMul Q IQ i j) := by
            rw [rectMatMul_sub_left]
    _ = rectMatMul P IQ := by
            rw [hQIQ]
            ext i j
            simp

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    multiplying the complement `I-Q` by the projection difference `P-Q` on
    the right removes the `Q` part. -/
theorem wedinLemma20_12_projectionComplement_mul_projectionDiff_eq_projectionComplement_mul_projection
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemQ : rectMatMul Q Q = Q) :
    rectMatMul (fun i j => idMatrix m i j - Q i j)
        (fun i j => P i j - Q i j) =
      rectMatMul (fun i j => idMatrix m i j - Q i j) P := by
  let IQ : Fin m → Fin m → ℝ := fun i j => idMatrix m i j - Q i j
  have hIQQ : rectMatMul IQ Q = fun _ _ => 0 := by
    simpa [IQ] using
      wedinLemma20_12_projectionComplement_mul_rangeProjection_eq_zero
        Q hIdemQ
  calc
    rectMatMul IQ (fun i j => P i j - Q i j)
        = (fun i j => rectMatMul IQ P i j - rectMatMul IQ Q i j) := by
            rw [rectMatMul_sub_right]
    _ = rectMatMul IQ P := by
            rw [hIQQ]
            ext i j
            simp

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the squared projection difference, applied on the right to `P`, is the
    range-side cross Gram product `P(I-Q)P`.

This exposes that `range(P)` is invariant under `(P-Q)^2`, a key structural
fact for the remaining principal-angle proof. -/
theorem wedinLemma20_12_projectionDiff_sq_mul_projection_eq_crossGram
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    rectMatMul
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j))
        P =
      rectMatMul
        (rectMatMul P (fun i j => idMatrix m i j - Q i j))
        P := by
  let D : Fin m → Fin m → ℝ := fun i j => P i j - Q i j
  let IQ : Fin m → Fin m → ℝ := fun i j => idMatrix m i j - Q i j
  have hDP : rectMatMul D P = rectMatMul IQ P := by
    symm
    simpa [D, IQ] using
      wedinLemma20_12_projectionComplement_mul_projection_eq_diff_mul_projection
        P Q hIdemP
  have hDIQ : rectMatMul D IQ = rectMatMul P IQ := by
    simpa [D, IQ] using
      wedinLemma20_12_projectionDiff_mul_projectionComplement_eq_projection_mul_projectionComplement
        P Q hIdemQ
  calc
    rectMatMul (rectMatMul D D) P
        = rectMatMul D (rectMatMul D P) := by
            rw [rectMatMul_assoc]
    _ = rectMatMul D (rectMatMul IQ P) := by
            rw [hDP]
    _ = rectMatMul (rectMatMul D IQ) P := by
            rw [← rectMatMul_assoc]
    _ = rectMatMul (rectMatMul P IQ) P := by
            rw [hDIQ]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the squared projection difference, applied on the left by `P`, is the same
    range-side cross Gram product `P(I-Q)P`. -/
theorem wedinLemma20_12_projection_mul_projectionDiff_sq_eq_crossGram
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    rectMatMul P
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)) =
      rectMatMul
        (rectMatMul P (fun i j => idMatrix m i j - Q i j))
        P := by
  let D : Fin m → Fin m → ℝ := fun i j => P i j - Q i j
  let IQ : Fin m → Fin m → ℝ := fun i j => idMatrix m i j - Q i j
  have hPD : rectMatMul P D = rectMatMul P IQ := by
    symm
    simpa [D, IQ] using
      wedinLemma20_12_projection_mul_projectionComplement_eq_projection_mul_diff
        P Q hIdemP
  have hIQD : rectMatMul IQ D = rectMatMul IQ P := by
    simpa [D, IQ] using
      wedinLemma20_12_projectionComplement_mul_projectionDiff_eq_projectionComplement_mul_projection
        P Q hIdemQ
  calc
    rectMatMul P (rectMatMul D D)
        = rectMatMul (rectMatMul P D) D := by
            rw [rectMatMul_assoc]
    _ = rectMatMul (rectMatMul P IQ) D := by
            rw [hPD]
    _ = rectMatMul P (rectMatMul IQ D) := by
            rw [rectMatMul_assoc]
    _ = rectMatMul P (rectMatMul IQ P) := by
            rw [hIQD]
    _ = rectMatMul (rectMatMul P IQ) P := by
            rw [← rectMatMul_assoc]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the squared projection difference `(P-Q)^2` commutes with `P`.

This is the finite-dimensional invariant-subspace bridge needed before the
remaining equality can be attacked by diagonalizing the restrictions of
`(P-Q)^2` to the two equal-dimensional projection ranges. -/
theorem wedinLemma20_12_projectionDiff_sq_commutes_projection
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    rectMatMul
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j))
        P =
      rectMatMul P
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)) := by
  calc
    rectMatMul
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j))
        P
        = rectMatMul
            (rectMatMul P (fun i j => idMatrix m i j - Q i j))
            P :=
            wedinLemma20_12_projectionDiff_sq_mul_projection_eq_crossGram
              P Q hIdemP hIdemQ
    _ = rectMatMul P
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)) := by
            exact
              (wedinLemma20_12_projection_mul_projectionDiff_sq_eq_crossGram
                P Q hIdemP hIdemQ).symm

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the same squared projection difference `(P-Q)^2` also commutes with `Q`. -/
theorem wedinLemma20_12_projectionDiff_sq_commutes_projection_swapped
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    rectMatMul
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j))
        Q =
      rectMatMul Q
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)) := by
  have hbase :=
    wedinLemma20_12_projectionDiff_sq_commutes_projection
      Q P hIdemQ hIdemP
  have hsq :
      rectMatMul (fun i j => Q i j - P i j)
          (fun i j => Q i j - P i j) =
        rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j) := by
    ext i j
    unfold rectMatMul
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsq] at hbase
  simpa using hbase

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    for the companion operator `S = P + Q - I`, `P*S = P*Q`. -/
theorem wedinLemma20_12_projection_mul_projectionSumSubId_eq_projection_mul_swapped
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P) :
    rectMatMul P (fun i j => P i j + Q i j - idMatrix m i j) =
      rectMatMul P Q := by
  calc
    rectMatMul P (fun i j => P i j + Q i j - idMatrix m i j)
        = (fun i j =>
            rectMatMul P (fun i j => P i j + Q i j) i j -
              rectMatMul P (idMatrix m) i j) := by
            rw [rectMatMul_sub_right]
    _ = (fun i j =>
            (rectMatMul P P i j + rectMatMul P Q i j) -
              rectMatMul P (idMatrix m) i j) := by
            rw [rectMatMul_add_right]
    _ = (fun i j => (P i j + rectMatMul P Q i j) - P i j) := by
            rw [hIdemP, rectMatMul_id_right]
    _ = rectMatMul P Q := by
            ext i j
            ring

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    for the companion operator `S = P + Q - I`, `Q*S = Q*P`. -/
theorem wedinLemma20_12_projection_swapped_mul_projectionSumSubId_eq_projection_swapped_mul_projection
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemQ : rectMatMul Q Q = Q) :
    rectMatMul Q (fun i j => P i j + Q i j - idMatrix m i j) =
      rectMatMul Q P := by
  calc
    rectMatMul Q (fun i j => P i j + Q i j - idMatrix m i j)
        = (fun i j =>
            rectMatMul Q (fun i j => P i j + Q i j) i j -
              rectMatMul Q (idMatrix m) i j) := by
            rw [rectMatMul_sub_right]
    _ = (fun i j =>
            (rectMatMul Q P i j + rectMatMul Q Q i j) -
              rectMatMul Q (idMatrix m) i j) := by
            rw [rectMatMul_add_right]
    _ = (fun i j => (rectMatMul Q P i j + Q i j) - Q i j) := by
            rw [hIdemQ, rectMatMul_id_right]
    _ = rectMatMul Q P := by
            ext i j
            ring

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    for the companion operator `S = P + Q - I`, `S*P = Q*P`. -/
theorem wedinLemma20_12_projectionSumSubId_mul_projection_eq_swapped_mul_projection
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P) :
    rectMatMul (fun i j => P i j + Q i j - idMatrix m i j) P =
      rectMatMul Q P := by
  calc
    rectMatMul (fun i j => P i j + Q i j - idMatrix m i j) P
        = (fun i j =>
            rectMatMul (fun i j => P i j + Q i j) P i j -
              rectMatMul (idMatrix m) P i j) := by
            rw [rectMatMul_sub_left]
    _ = (fun i j =>
            (rectMatMul P P i j + rectMatMul Q P i j) -
              rectMatMul (idMatrix m) P i j) := by
            rw [rectMatMul_add_left]
    _ = (fun i j => (P i j + rectMatMul Q P i j) - P i j) := by
            rw [hIdemP, rectMatMul_id_left]
    _ = rectMatMul Q P := by
            ext i j
            ring

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    for the companion operator `S = P + Q - I`, `S*Q = P*Q`. -/
theorem wedinLemma20_12_projectionSumSubId_mul_projection_swapped_eq_projection_mul_swapped
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemQ : rectMatMul Q Q = Q) :
    rectMatMul (fun i j => P i j + Q i j - idMatrix m i j) Q =
      rectMatMul P Q := by
  calc
    rectMatMul (fun i j => P i j + Q i j - idMatrix m i j) Q
        = (fun i j =>
            rectMatMul (fun i j => P i j + Q i j) Q i j -
              rectMatMul (idMatrix m) Q i j) := by
            rw [rectMatMul_sub_left]
    _ = (fun i j =>
            (rectMatMul P Q i j + rectMatMul Q Q i j) -
              rectMatMul (idMatrix m) Q i j) := by
            rw [rectMatMul_add_left]
    _ = (fun i j => (rectMatMul P Q i j + Q i j) - Q i j) := by
            rw [hIdemQ, rectMatMul_id_left]
    _ = rectMatMul P Q := by
            ext i j
            ring

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the companion operator `S = P + Q - I` maps the `P` range into the `Q`
    range in matrix form, `S*P = Q*S`. -/
theorem wedinLemma20_12_projectionSumSubId_intertwines_projection
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    rectMatMul (fun i j => P i j + Q i j - idMatrix m i j) P =
      rectMatMul Q (fun i j => P i j + Q i j - idMatrix m i j) := by
  calc
    rectMatMul (fun i j => P i j + Q i j - idMatrix m i j) P
        = rectMatMul Q P := by
            exact
              wedinLemma20_12_projectionSumSubId_mul_projection_eq_swapped_mul_projection
                P Q hIdemP
    _ = rectMatMul Q (fun i j => P i j + Q i j - idMatrix m i j) := by
            exact
              (wedinLemma20_12_projection_swapped_mul_projectionSumSubId_eq_projection_swapped_mul_projection
                P Q hIdemQ).symm

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the companion operator `S = P + Q - I` also maps the `Q` range into the
    `P` range in matrix form, `S*Q = P*S`. -/
theorem wedinLemma20_12_projectionSumSubId_intertwines_projection_swapped
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    rectMatMul (fun i j => P i j + Q i j - idMatrix m i j) Q =
      rectMatMul P (fun i j => P i j + Q i j - idMatrix m i j) := by
  calc
    rectMatMul (fun i j => P i j + Q i j - idMatrix m i j) Q
        = rectMatMul P Q := by
            exact
              wedinLemma20_12_projectionSumSubId_mul_projection_swapped_eq_projection_mul_swapped
                P Q hIdemQ
    _ = rectMatMul P (fun i j => P i j + Q i j - idMatrix m i j) := by
            exact
              (wedinLemma20_12_projection_mul_projectionSumSubId_eq_projection_mul_swapped
                P Q hIdemP).symm

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    `D = P-Q` anti-commutes with the companion operator `S = P+Q-I`.

This is the algebraic heart of the principal-angle route: it later implies
that `D^2` commutes with `S`, while `S` interchanges the two projection ranges. -/
theorem wedinLemma20_12_projectionDiff_mul_projectionSumSubId_eq_neg_projectionSumSubId_mul_projectionDiff
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    rectMatMul (fun i j => P i j - Q i j)
        (fun i j => P i j + Q i j - idMatrix m i j) =
      fun i j =>
        -rectMatMul (fun i j => P i j + Q i j - idMatrix m i j)
          (fun i j => P i j - Q i j) i j := by
  let D : Fin m → Fin m → ℝ := fun i j => P i j - Q i j
  let S : Fin m → Fin m → ℝ := fun i j => P i j + Q i j - idMatrix m i j
  calc
    rectMatMul D S
        = (fun i j => rectMatMul P S i j - rectMatMul Q S i j) := by
            rw [rectMatMul_sub_left]
    _ = (fun i j => rectMatMul P Q i j - rectMatMul Q P i j) := by
            rw [wedinLemma20_12_projection_mul_projectionSumSubId_eq_projection_mul_swapped
                P Q hIdemP,
              wedinLemma20_12_projection_swapped_mul_projectionSumSubId_eq_projection_swapped_mul_projection
                P Q hIdemQ]
    _ = (fun i j => -rectMatMul S D i j) := by
            have hSD :
                rectMatMul S D =
                  (fun i j => rectMatMul S P i j - rectMatMul S Q i j) := by
              rw [rectMatMul_sub_right]
            rw [hSD,
              wedinLemma20_12_projectionSumSubId_mul_projection_eq_swapped_mul_projection
                P Q hIdemP,
              wedinLemma20_12_projectionSumSubId_mul_projection_swapped_eq_projection_mul_swapped
                P Q hIdemQ]
            ext i j
            ring

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the squared projection difference `D^2` commutes with the companion
    operator `S = P+Q-I`. -/
theorem wedinLemma20_12_projectionDiff_sq_commutes_projectionSumSubId
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    rectMatMul
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j))
        (fun i j => P i j + Q i j - idMatrix m i j) =
      rectMatMul (fun i j => P i j + Q i j - idMatrix m i j)
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)) := by
  let D : Fin m → Fin m → ℝ := fun i j => P i j - Q i j
  let S : Fin m → Fin m → ℝ := fun i j => P i j + Q i j - idMatrix m i j
  have hanti :
      rectMatMul D S = fun i j => -rectMatMul S D i j := by
    simpa [D, S] using
      wedinLemma20_12_projectionDiff_mul_projectionSumSubId_eq_neg_projectionSumSubId_mul_projectionDiff
        P Q hIdemP hIdemQ
  calc
    rectMatMul (rectMatMul D D) S
        = rectMatMul D (rectMatMul D S) := by
            rw [rectMatMul_assoc]
    _ = rectMatMul D (fun i j => -rectMatMul S D i j) := by
            rw [hanti]
    _ = (fun i j => -rectMatMul D (rectMatMul S D) i j) := by
            rw [rectMatMul_neg_right]
    _ = (fun i j => -rectMatMul (rectMatMul D S) D i j) := by
            rw [← rectMatMul_assoc]
    _ = (fun i j =>
            -rectMatMul (fun i j => -rectMatMul S D i j) D i j) := by
            rw [hanti]
    _ = (fun i j => -(-rectMatMul (rectMatMul S D) D i j)) := by
            rw [rectMatMul_neg_left]
    _ = rectMatMul (rectMatMul S D) D := by
            ext i j
            ring
    _ = rectMatMul S (rectMatMul D D) := by
            rw [rectMatMul_assoc]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the companion operator `S = P+Q-I` satisfies
    `S^2 = I - (P-Q)^2`.

This is the algebraic identity that pairs the range-intertwining map `S` with
the squared projection-difference operator in the direct principal-angle route. -/
theorem wedinLemma20_12_projectionSumSubId_sq_eq_id_sub_projectionDiff_sq
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    rectMatMul
        (fun i j => P i j + Q i j - idMatrix m i j)
        (fun i j => P i j + Q i j - idMatrix m i j) =
      fun i j =>
        idMatrix m i j -
          rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j) i j := by
  let S : Fin m → Fin m → ℝ := fun i j => P i j + Q i j - idMatrix m i j
  let D : Fin m → Fin m → ℝ := fun i j => P i j - Q i j
  have hSS :
      rectMatMul S S =
        fun i j => (rectMatMul P Q i j + rectMatMul Q P i j) - S i j := by
    calc
      rectMatMul S S
          = (fun i j => rectMatMul (fun i j => P i j + Q i j) S i j -
              rectMatMul (idMatrix m) S i j) := by
              rw [show S = fun i j => (P i j + Q i j) - idMatrix m i j by rfl]
              rw [rectMatMul_sub_left]
      _ = (fun i j => (rectMatMul P S i j + rectMatMul Q S i j) - S i j) := by
              rw [rectMatMul_add_left, rectMatMul_id_left]
      _ = (fun i j => (rectMatMul P Q i j + rectMatMul Q P i j) - S i j) := by
              rw [wedinLemma20_12_projection_mul_projectionSumSubId_eq_projection_mul_swapped
                    P Q hIdemP,
                  wedinLemma20_12_projection_swapped_mul_projectionSumSubId_eq_projection_swapped_mul_projection
                    P Q hIdemQ]
  have hDD :
      rectMatMul D D =
        fun i j => (P i j - rectMatMul P Q i j) -
          (rectMatMul Q P i j - Q i j) := by
    calc
      rectMatMul D D
          = (fun i j => rectMatMul P D i j - rectMatMul Q D i j) := by
              rw [show D = fun i j => P i j - Q i j by rfl]
              rw [rectMatMul_sub_left]
      _ = (fun i j => (rectMatMul P P i j - rectMatMul P Q i j) -
              (rectMatMul Q P i j - rectMatMul Q Q i j)) := by
              rw [rectMatMul_sub_right, rectMatMul_sub_right]
      _ = (fun i j => (P i j - rectMatMul P Q i j) -
              (rectMatMul Q P i j - Q i j)) := by
              rw [hIdemP, hIdemQ]
  rw [show (fun i j => P i j + Q i j - idMatrix m i j) = S by rfl,
    show (fun i j => P i j - Q i j) = D by rfl]
  rw [hSS, hDD]
  ext i j
  ring

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    if a vector lies in the range of `P`, then applying the companion operator
    `S = P+Q-I` gives a vector in the range of `Q`. -/
theorem wedinLemma20_12_rectMatMulVec_projectionSumSubId_maps_projection_range
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (x : Fin m → ℝ)
    (hxP : rectMatMulVec P x = x) :
    rectMatMulVec Q
        (rectMatMulVec (fun i j => P i j + Q i j - idMatrix m i j) x) =
      rectMatMulVec (fun i j => P i j + Q i j - idMatrix m i j) x := by
  let S : Fin m → Fin m → ℝ := fun i j => P i j + Q i j - idMatrix m i j
  have hSP :
      rectMatMul S P = rectMatMul Q S := by
    simpa [S] using
      wedinLemma20_12_projectionSumSubId_intertwines_projection
        P Q hIdemP hIdemQ
  calc
    rectMatMulVec Q (rectMatMulVec S x)
        = rectMatMulVec (rectMatMul Q S) x := by
            rw [rectMatMulVec_rectMatMul]
    _ = rectMatMulVec (rectMatMul S P) x := by
            rw [← hSP]
    _ = rectMatMulVec S (rectMatMulVec P x) := by
            rw [rectMatMulVec_rectMatMul]
    _ = rectMatMulVec S x := by
            rw [hxP]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    swapped vector-range version of the companion intertwinement. -/
theorem wedinLemma20_12_rectMatMulVec_projectionSumSubId_maps_projection_range_swapped
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (x : Fin m → ℝ)
    (hxQ : rectMatMulVec Q x = x) :
    rectMatMulVec P
        (rectMatMulVec (fun i j => P i j + Q i j - idMatrix m i j) x) =
      rectMatMulVec (fun i j => P i j + Q i j - idMatrix m i j) x := by
  let S : Fin m → Fin m → ℝ := fun i j => P i j + Q i j - idMatrix m i j
  have hSQ :
      rectMatMul S Q = rectMatMul P S := by
    simpa [S] using
      wedinLemma20_12_projectionSumSubId_intertwines_projection_swapped
        P Q hIdemP hIdemQ
  calc
    rectMatMulVec P (rectMatMulVec S x)
        = rectMatMulVec (rectMatMul P S) x := by
            rw [rectMatMulVec_rectMatMul]
    _ = rectMatMulVec (rectMatMul S Q) x := by
            rw [← hSQ]
    _ = rectMatMulVec S (rectMatMulVec Q x) := by
            rw [rectMatMulVec_rectMatMul]
    _ = rectMatMulVec S x := by
            rw [hxQ]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    because `D^2` commutes with the companion operator `S`, applying `S` to a
    `D^2` eigenvector preserves the eigenvalue. -/
theorem wedinLemma20_12_rectMatMulVec_projectionSumSubId_preserves_projectionDiff_sq_eigenvector
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (lambda : ℝ) (x : Fin m → ℝ)
    (hxEig :
      rectMatMulVec
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)) x =
        fun i => lambda * x i) :
    rectMatMulVec
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j))
        (rectMatMulVec (fun i j => P i j + Q i j - idMatrix m i j) x) =
      fun i =>
        lambda *
          rectMatMulVec (fun i j => P i j + Q i j - idMatrix m i j) x i := by
  let D : Fin m → Fin m → ℝ := fun i j => P i j - Q i j
  let S : Fin m → Fin m → ℝ := fun i j => P i j + Q i j - idMatrix m i j
  have hcomm :
      rectMatMul (rectMatMul D D) S =
        rectMatMul S (rectMatMul D D) := by
    simpa [D, S] using
      wedinLemma20_12_projectionDiff_sq_commutes_projectionSumSubId
        P Q hIdemP hIdemQ
  calc
    rectMatMulVec (rectMatMul D D) (rectMatMulVec S x)
        = rectMatMulVec (rectMatMul (rectMatMul D D) S) x := by
            exact (rectMatMulVec_rectMatMul (rectMatMul D D) S x).symm
    _ = rectMatMulVec (rectMatMul S (rectMatMul D D)) x := by
            rw [hcomm]
    _ = rectMatMulVec S (rectMatMulVec (rectMatMul D D) x) := by
            rw [rectMatMulVec_rectMatMul]
    _ = rectMatMulVec S (fun i => lambda * x i) := by
            rw [hxEig]
    _ = fun i => lambda * rectMatMulVec S x i := by
            rw [rectMatMulVec_smul]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    on a `D^2` eigenvector, the companion square acts by the scalar
    `1 - lambda`. -/
theorem wedinLemma20_12_rectMatMulVec_projectionSumSubId_sq_apply_projectionDiff_sq_eigenvector
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (lambda : ℝ) (x : Fin m → ℝ)
    (hxEig :
      rectMatMulVec
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)) x =
        fun i => lambda * x i) :
    rectMatMulVec (fun i j => P i j + Q i j - idMatrix m i j)
        (rectMatMulVec (fun i j => P i j + Q i j - idMatrix m i j) x) =
      fun i => (1 - lambda) * x i := by
  let D : Fin m → Fin m → ℝ := fun i j => P i j - Q i j
  let S : Fin m → Fin m → ℝ := fun i j => P i j + Q i j - idMatrix m i j
  have hSsq :
      rectMatMul S S = fun i j => idMatrix m i j - rectMatMul D D i j := by
    simpa [D, S] using
      wedinLemma20_12_projectionSumSubId_sq_eq_id_sub_projectionDiff_sq
        P Q hIdemP hIdemQ
  calc
    rectMatMulVec S (rectMatMulVec S x)
        = rectMatMulVec (rectMatMul S S) x := by
            exact (rectMatMulVec_rectMatMul S S x).symm
    _ = rectMatMulVec (fun i j => idMatrix m i j - rectMatMul D D i j) x := by
            rw [hSsq]
    _ = fun i => x i - rectMatMulVec (rectMatMul D D) x i := by
            simpa [D] using
              wedinLemma20_12_rectMatMulVec_projectionComplement
                (rectMatMul D D) x
    _ = fun i => (1 - lambda) * x i := by
            rw [hxEig]
            ext i
            ring

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    if a nonzero `D^2` eigenvector has eigenvalue different from `1`, then
    its companion image is nonzero. -/
theorem wedinLemma20_12_rectMatMulVec_projectionSumSubId_ne_zero_of_projectionDiff_sq_eigenvalue_ne_one
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (lambda : ℝ) (x : Fin m → ℝ)
    (hxEig :
      rectMatMulVec
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)) x =
        fun i => lambda * x i)
    (hx_ne : x ≠ 0)
    (hlambda_ne : lambda ≠ 1) :
    rectMatMulVec (fun i j => P i j + Q i j - idMatrix m i j) x ≠ 0 := by
  let S : Fin m → Fin m → ℝ := fun i j => P i j + Q i j - idMatrix m i j
  intro hSx
  have hSSx_zero : rectMatMulVec S (rectMatMulVec S x) = 0 := by
    rw [hSx]
    ext i
    unfold rectMatMulVec
    simp
  have hSSx :=
    wedinLemma20_12_rectMatMulVec_projectionSumSubId_sq_apply_projectionDiff_sq_eigenvector
      P Q hIdemP hIdemQ lambda x hxEig
  have hscaled_zero : (fun i => (1 - lambda) * x i) = 0 := by
    rw [← hSSx, hSSx_zero]
  have hcoef_ne : 1 - lambda ≠ 0 := by
    intro hcoef
    apply hlambda_ne
    linarith
  apply hx_ne
  ext i
  have hi := congrFun hscaled_zero i
  exact (mul_eq_zero.mp hi).resolve_left hcoef_ne

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    a nonunit `D^2` eigenvector in the `P` range transfers through the companion
    operator to a nonzero `D^2` eigenvector in the `Q` range with the same
    eigenvalue. -/
theorem wedinLemma20_12_exists_projection_swapped_range_projectionDiff_sq_eigenvector_of_projection_range
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (lambda : ℝ) (x : Fin m → ℝ)
    (hxP : rectMatMulVec P x = x)
    (hxEig :
      rectMatMulVec
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)) x =
        fun i => lambda * x i)
    (hx_ne : x ≠ 0)
    (hlambda_ne : lambda ≠ 1) :
    ∃ y : Fin m → ℝ,
      y ≠ 0 ∧
      rectMatMulVec Q y = y ∧
      rectMatMulVec
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)) y =
        fun i => lambda * y i := by
  let S : Fin m → Fin m → ℝ := fun i j => P i j + Q i j - idMatrix m i j
  refine ⟨rectMatMulVec S x, ?_, ?_, ?_⟩
  · simpa [S] using
      wedinLemma20_12_rectMatMulVec_projectionSumSubId_ne_zero_of_projectionDiff_sq_eigenvalue_ne_one
        P Q hIdemP hIdemQ lambda x hxEig hx_ne hlambda_ne
  · simpa [S] using
      wedinLemma20_12_rectMatMulVec_projectionSumSubId_maps_projection_range
        P Q hIdemP hIdemQ x hxP
  · simpa [S] using
      wedinLemma20_12_rectMatMulVec_projectionSumSubId_preserves_projectionDiff_sq_eigenvector
        P Q hIdemP hIdemQ lambda x hxEig

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    symmetric nonunit transfer: a nonzero `D^2` eigenvector in the `Q` range
    maps through the same companion operator to a nonzero `D^2` eigenvector in
    the `P` range with the same eigenvalue. -/
theorem wedinLemma20_12_exists_projection_range_projectionDiff_sq_eigenvector_of_projection_swapped_range
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (lambda : ℝ) (x : Fin m → ℝ)
    (hxQ : rectMatMulVec Q x = x)
    (hxEig :
      rectMatMulVec
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)) x =
        fun i => lambda * x i)
    (hx_ne : x ≠ 0)
    (hlambda_ne : lambda ≠ 1) :
    ∃ y : Fin m → ℝ,
      y ≠ 0 ∧
      rectMatMulVec P y = y ∧
      rectMatMulVec
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)) y =
        fun i => lambda * y i := by
  let S : Fin m → Fin m → ℝ := fun i j => P i j + Q i j - idMatrix m i j
  refine ⟨rectMatMulVec S x, ?_, ?_, ?_⟩
  · simpa [S] using
      wedinLemma20_12_rectMatMulVec_projectionSumSubId_ne_zero_of_projectionDiff_sq_eigenvalue_ne_one
        P Q hIdemP hIdemQ lambda x hxEig hx_ne hlambda_ne
  · simpa [S] using
      wedinLemma20_12_rectMatMulVec_projectionSumSubId_maps_projection_range_swapped
        P Q hIdemP hIdemQ x hxQ
  · simpa [S] using
      wedinLemma20_12_rectMatMulVec_projectionSumSubId_preserves_projectionDiff_sq_eigenvector
        P Q hIdemP hIdemQ lambda x hxEig

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the companion square `S^2`, where `S = P+Q-I`, preserves the `P` range.

This follows from `S^2 = I - (P-Q)^2` and the already proved commutation of
`(P-Q)^2` with `P`. -/
theorem wedinLemma20_12_projectionSumSubId_sq_commutes_projection
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    rectMatMul
        (rectMatMul (fun i j => P i j + Q i j - idMatrix m i j)
          (fun i j => P i j + Q i j - idMatrix m i j))
        P =
      rectMatMul P
        (rectMatMul (fun i j => P i j + Q i j - idMatrix m i j)
          (fun i j => P i j + Q i j - idMatrix m i j)) := by
  let S : Fin m → Fin m → ℝ := fun i j => P i j + Q i j - idMatrix m i j
  let D : Fin m → Fin m → ℝ := fun i j => P i j - Q i j
  have hSsq :
      rectMatMul S S = fun i j => idMatrix m i j - rectMatMul D D i j := by
    simpa [S, D] using
      wedinLemma20_12_projectionSumSubId_sq_eq_id_sub_projectionDiff_sq
        P Q hIdemP hIdemQ
  have hDcomm :
      rectMatMul (rectMatMul D D) P =
        rectMatMul P (rectMatMul D D) := by
    simpa [D] using
      wedinLemma20_12_projectionDiff_sq_commutes_projection
        P Q hIdemP hIdemQ
  calc
    rectMatMul (rectMatMul S S) P
        = rectMatMul (fun i j => idMatrix m i j - rectMatMul D D i j) P := by
            rw [hSsq]
    _ = (fun i j =>
            rectMatMul (idMatrix m) P i j -
              rectMatMul (rectMatMul D D) P i j) := by
            rw [rectMatMul_sub_left]
    _ = (fun i j => P i j - rectMatMul (rectMatMul D D) P i j) := by
            rw [rectMatMul_id_left]
    _ = (fun i j => P i j - rectMatMul P (rectMatMul D D) i j) := by
            rw [hDcomm]
    _ = (fun i j =>
            rectMatMul P (idMatrix m) i j -
              rectMatMul P (rectMatMul D D) i j) := by
            rw [rectMatMul_id_right]
    _ = rectMatMul P (fun i j => idMatrix m i j - rectMatMul D D i j) := by
            rw [← rectMatMul_sub_right]
    _ = rectMatMul P (rectMatMul S S) := by
            rw [hSsq]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the companion square `S^2`, where `S = P+Q-I`, also preserves the `Q`
    range. -/
theorem wedinLemma20_12_projectionSumSubId_sq_commutes_projection_swapped
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    rectMatMul
        (rectMatMul (fun i j => P i j + Q i j - idMatrix m i j)
          (fun i j => P i j + Q i j - idMatrix m i j))
        Q =
      rectMatMul Q
        (rectMatMul (fun i j => P i j + Q i j - idMatrix m i j)
          (fun i j => P i j + Q i j - idMatrix m i j)) := by
  let S : Fin m → Fin m → ℝ := fun i j => P i j + Q i j - idMatrix m i j
  let D : Fin m → Fin m → ℝ := fun i j => P i j - Q i j
  have hSsq :
      rectMatMul S S = fun i j => idMatrix m i j - rectMatMul D D i j := by
    simpa [S, D] using
      wedinLemma20_12_projectionSumSubId_sq_eq_id_sub_projectionDiff_sq
        P Q hIdemP hIdemQ
  have hDcomm :
      rectMatMul (rectMatMul D D) Q =
        rectMatMul Q (rectMatMul D D) := by
    simpa [D] using
      wedinLemma20_12_projectionDiff_sq_commutes_projection_swapped
        P Q hIdemP hIdemQ
  calc
    rectMatMul (rectMatMul S S) Q
        = rectMatMul (fun i j => idMatrix m i j - rectMatMul D D i j) Q := by
            rw [hSsq]
    _ = (fun i j =>
            rectMatMul (idMatrix m) Q i j -
              rectMatMul (rectMatMul D D) Q i j) := by
            rw [rectMatMul_sub_left]
    _ = (fun i j => Q i j - rectMatMul (rectMatMul D D) Q i j) := by
            rw [rectMatMul_id_left]
    _ = (fun i j => Q i j - rectMatMul Q (rectMatMul D D) i j) := by
            rw [hDcomm]
    _ = (fun i j =>
            rectMatMul Q (idMatrix m) i j -
              rectMatMul Q (rectMatMul D D) i j) := by
            rw [rectMatMul_id_right]
    _ = rectMatMul Q (fun i j => idMatrix m i j - rectMatMul D D i j) := by
            rw [← rectMatMul_sub_right]
    _ = rectMatMul Q (rectMatMul S S) := by
            rw [hSsq]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    right-compressing the companion square `S^2` to the `P` range gives
    `P*Q*P`. -/
theorem wedinLemma20_12_projectionSumSubId_sq_mul_projection_eq_projection_mul_swapped_mul_projection
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    rectMatMul
        (rectMatMul (fun i j => P i j + Q i j - idMatrix m i j)
          (fun i j => P i j + Q i j - idMatrix m i j))
        P =
      rectMatMul (rectMatMul P Q) P := by
  let S : Fin m → Fin m → ℝ := fun i j => P i j + Q i j - idMatrix m i j
  calc
    rectMatMul (rectMatMul S S) P
        = rectMatMul S (rectMatMul S P) := by
            rw [rectMatMul_assoc]
    _ = rectMatMul S (rectMatMul Q P) := by
            rw [wedinLemma20_12_projectionSumSubId_mul_projection_eq_swapped_mul_projection
              P Q hIdemP]
    _ = rectMatMul (rectMatMul S Q) P := by
            rw [← rectMatMul_assoc]
    _ = rectMatMul (rectMatMul P Q) P := by
            rw [wedinLemma20_12_projectionSumSubId_mul_projection_swapped_eq_projection_mul_swapped
              P Q hIdemQ]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    left-compressing the companion square `S^2` to the `P` range gives
    `P*Q*P`. -/
theorem wedinLemma20_12_projection_mul_projectionSumSubId_sq_eq_projection_mul_swapped_mul_projection
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    rectMatMul P
        (rectMatMul (fun i j => P i j + Q i j - idMatrix m i j)
          (fun i j => P i j + Q i j - idMatrix m i j)) =
      rectMatMul (rectMatMul P Q) P := by
  let S : Fin m → Fin m → ℝ := fun i j => P i j + Q i j - idMatrix m i j
  calc
    rectMatMul P (rectMatMul S S)
        = rectMatMul (rectMatMul P S) S := by
            rw [← rectMatMul_assoc]
    _ = rectMatMul (rectMatMul P Q) S := by
            rw [wedinLemma20_12_projection_mul_projectionSumSubId_eq_projection_mul_swapped
              P Q hIdemP]
    _ = rectMatMul P (rectMatMul Q S) := by
            rw [rectMatMul_assoc]
    _ = rectMatMul P (rectMatMul Q P) := by
            rw [wedinLemma20_12_projection_swapped_mul_projectionSumSubId_eq_projection_swapped_mul_projection
              P Q hIdemQ]
    _ = rectMatMul (rectMatMul P Q) P := by
            rw [← rectMatMul_assoc]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    right-compressing the companion square `S^2` to the `Q` range gives
    `Q*P*Q`. -/
theorem wedinLemma20_12_projectionSumSubId_sq_mul_projection_swapped_eq_projection_swapped_mul_projection_mul_projection_swapped
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    rectMatMul
        (rectMatMul (fun i j => P i j + Q i j - idMatrix m i j)
          (fun i j => P i j + Q i j - idMatrix m i j))
        Q =
      rectMatMul (rectMatMul Q P) Q := by
  let S : Fin m → Fin m → ℝ := fun i j => P i j + Q i j - idMatrix m i j
  calc
    rectMatMul (rectMatMul S S) Q
        = rectMatMul S (rectMatMul S Q) := by
            rw [rectMatMul_assoc]
    _ = rectMatMul S (rectMatMul P Q) := by
            rw [wedinLemma20_12_projectionSumSubId_mul_projection_swapped_eq_projection_mul_swapped
              P Q hIdemQ]
    _ = rectMatMul (rectMatMul S P) Q := by
            rw [← rectMatMul_assoc]
    _ = rectMatMul (rectMatMul Q P) Q := by
            rw [wedinLemma20_12_projectionSumSubId_mul_projection_eq_swapped_mul_projection
              P Q hIdemP]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    if a `D^2` eigenvector in the `P` range has eigenvalue `1`, then the
    companion-square compression `PQP` kills it. -/
theorem wedinLemma20_12_rectMatMulVec_projection_mul_swapped_mul_projection_eq_zero_of_projectionDiff_sq_eigenvalue_one_projection_range
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (x : Fin m → ℝ)
    (hxP : rectMatMulVec P x = x)
    (hxEig :
      rectMatMulVec
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)) x = x) :
    rectMatMulVec (rectMatMul (rectMatMul P Q) P) x = 0 := by
  let S : Fin m → Fin m → ℝ := fun i j => P i j + Q i j - idMatrix m i j
  have hxEig_one :
      rectMatMulVec
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)) x =
        fun i => (1 : ℝ) * x i := by
    simpa using hxEig
  have hSsqP :
      rectMatMul (rectMatMul S S) P = rectMatMul (rectMatMul P Q) P := by
    simpa [S] using
      wedinLemma20_12_projectionSumSubId_sq_mul_projection_eq_projection_mul_swapped_mul_projection
        P Q hIdemP hIdemQ
  have hSsqx :
      rectMatMulVec S (rectMatMulVec S x) = 0 := by
    have h :=
      wedinLemma20_12_rectMatMulVec_projectionSumSubId_sq_apply_projectionDiff_sq_eigenvector
        P Q hIdemP hIdemQ (1 : ℝ) x hxEig_one
    simpa [S] using h
  calc
    rectMatMulVec (rectMatMul (rectMatMul P Q) P) x
        = rectMatMulVec (rectMatMul (rectMatMul S S) P) x := by
            rw [← hSsqP]
    _ = rectMatMulVec (rectMatMul S S) (rectMatMulVec P x) := by
            rw [rectMatMulVec_rectMatMul]
    _ = rectMatMulVec (rectMatMul S S) x := by
            rw [hxP]
    _ = rectMatMulVec S (rectMatMulVec S x) := by
            rw [rectMatMulVec_rectMatMul]
    _ = 0 := hSsqx

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    swapped version of the eigenvalue-`1` compression-kernel fact. -/
theorem wedinLemma20_12_rectMatMulVec_projection_swapped_mul_projection_mul_projection_swapped_eq_zero_of_projectionDiff_sq_eigenvalue_one_projection_swapped_range
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (x : Fin m → ℝ)
    (hxQ : rectMatMulVec Q x = x)
    (hxEig :
      rectMatMulVec
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)) x = x) :
    rectMatMulVec (rectMatMul (rectMatMul Q P) Q) x = 0 := by
  let S : Fin m → Fin m → ℝ := fun i j => P i j + Q i j - idMatrix m i j
  have hxEig_one :
      rectMatMulVec
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)) x =
        fun i => (1 : ℝ) * x i := by
    simpa using hxEig
  have hSsqQ :
      rectMatMul (rectMatMul S S) Q = rectMatMul (rectMatMul Q P) Q := by
    simpa [S] using
      wedinLemma20_12_projectionSumSubId_sq_mul_projection_swapped_eq_projection_swapped_mul_projection_mul_projection_swapped
        P Q hIdemP hIdemQ
  have hSsqx :
      rectMatMulVec S (rectMatMulVec S x) = 0 := by
    have h :=
      wedinLemma20_12_rectMatMulVec_projectionSumSubId_sq_apply_projectionDiff_sq_eigenvector
        P Q hIdemP hIdemQ (1 : ℝ) x hxEig_one
    simpa [S] using h
  calc
    rectMatMulVec (rectMatMul (rectMatMul Q P) Q) x
        = rectMatMulVec (rectMatMul (rectMatMul S S) Q) x := by
            rw [← hSsqQ]
    _ = rectMatMulVec (rectMatMul S S) (rectMatMulVec Q x) := by
            rw [rectMatMulVec_rectMatMul]
    _ = rectMatMulVec (rectMatMul S S) x := by
            rw [hxQ]
    _ = rectMatMulVec S (rectMatMulVec S x) := by
            rw [rectMatMulVec_rectMatMul]
    _ = 0 := hSsqx

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    if `x` lies in the range of `P` and `PQP` kills `x`, then the swapped
    projection `Q` kills `x`. -/
theorem wedinLemma20_12_rectMatMulVec_projection_swapped_eq_zero_of_projection_range_companion_compression_eq_zero
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemQ : rectMatMul Q Q = Q)
    (x : Fin m → ℝ)
    (hxP : rectMatMulVec P x = x)
    (hPQP :
      rectMatMulVec (rectMatMul (rectMatMul P Q) P) x = 0) :
    rectMatMulVec Q x = 0 := by
  have hxP_fin : finiteMatVec P x = x := by
    simpa [finiteMatVec, rectMatMulVec] using hxP
  have hPQP_fin :
      finiteMatVec (finiteMatMul (finiteMatMul P Q) P) x = 0 := by
    simpa [finiteMatVec, rectMatMulVec, finiteMatMul, rectMatMul] using hPQP
  have hP_Qx_zero : finiteMatVec P (finiteMatVec Q x) = 0 := by
    calc
      finiteMatVec P (finiteMatVec Q x)
          = finiteMatVec P (finiteMatVec Q (finiteMatVec P x)) := by
              rw [hxP_fin]
      _ = finiteMatVec (finiteMatMul P Q) (finiteMatVec P x) := by
              exact (finiteMatVec_finiteMatMul P Q (finiteMatVec P x)).symm
      _ = finiteMatVec (finiteMatMul (finiteMatMul P Q) P) x := by
              exact (finiteMatVec_finiteMatMul (finiteMatMul P Q) P x).symm
      _ = 0 := hPQP_fin
  have hquad_zero : finiteQuadraticForm Q x = 0 := by
    calc
      finiteQuadraticForm Q x
          = ∑ i : Fin m, x i * finiteMatVec Q x i := rfl
      _ = ∑ i : Fin m, finiteMatVec P x i * finiteMatVec Q x i := by
              rw [hxP_fin]
      _ = ∑ i : Fin m, x i * finiteMatVec P (finiteMatVec Q x) i := by
              exact
                (finiteVecInnerProduct_finiteMatVec_left_eq_right_of_symmetric
                  P hP x (finiteMatVec Q x)).symm
      _ = 0 := by
              rw [hP_Qx_zero]
              simp
  have hIdemQ_fin : ∀ i j : Fin m, finiteMatMul Q Q i j = Q i j := by
    intro i j
    simpa [finiteMatMul, rectMatMul] using congrFun (congrFun hIdemQ i) j
  have hnormsq_zero : finiteVecNorm2Sq (finiteMatVec Q x) = 0 := by
    calc
      finiteVecNorm2Sq (finiteMatVec Q x)
          = finiteQuadraticForm (finiteMatMul Q Q) x := by
              exact
                (finiteQuadraticForm_finiteMatMul_self_of_symmetric
                  Q hQ x).symm
      _ = finiteQuadraticForm Q x := by
              have hmat : finiteMatMul Q Q = Q := by
                funext i j
                exact hIdemQ_fin i j
              rw [hmat]
      _ = 0 := hquad_zero
  have hnorm_zero : vecNorm2 (rectMatMulVec Q x) = 0 := by
    have hsq : vecNorm2 (rectMatMulVec Q x) ^ 2 = 0 := by
      rw [vecNorm2_sq]
      simpa [finiteVecNorm2Sq_fin, finiteMatVec, rectMatMulVec] using hnormsq_zero
    exact sq_eq_zero_iff.mp hsq
  ext i
  exact (vecNorm2_eq_zero_iff (rectMatMulVec Q x)).mp hnorm_zero i

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    swapped version: if `x` lies in the range of `Q` and `QPQ` kills `x`,
    then `P` kills `x`. -/
theorem wedinLemma20_12_rectMatMulVec_projection_eq_zero_of_projection_swapped_range_companion_compression_eq_zero
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (x : Fin m → ℝ)
    (hxQ : rectMatMulVec Q x = x)
    (hQPQ :
      rectMatMulVec (rectMatMul (rectMatMul Q P) Q) x = 0) :
    rectMatMulVec P x = 0 := by
  simpa using
    wedinLemma20_12_rectMatMulVec_projection_swapped_eq_zero_of_projection_range_companion_compression_eq_zero
      Q P hQ hP hIdemP x hxQ hQPQ

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    a `D^2` eigenvector with eigenvalue `1` in the range of `P` is orthogonal
    to the swapped projection range, in vector-action form `Q*x = 0`. -/
theorem wedinLemma20_12_rectMatMulVec_projection_swapped_eq_zero_of_projectionDiff_sq_eigenvalue_one_projection_range
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (x : Fin m → ℝ)
    (hxP : rectMatMulVec P x = x)
    (hxEig :
      rectMatMulVec
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)) x = x) :
    rectMatMulVec Q x = 0 := by
  exact
    wedinLemma20_12_rectMatMulVec_projection_swapped_eq_zero_of_projection_range_companion_compression_eq_zero
      P Q hP hQ hIdemQ x hxP
      (wedinLemma20_12_rectMatMulVec_projection_mul_swapped_mul_projection_eq_zero_of_projectionDiff_sq_eigenvalue_one_projection_range
        P Q hIdemP hIdemQ x hxP hxEig)

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    swapped action-zero consequence for a `D^2` eigenvector with eigenvalue
    `1` in the range of `Q`. -/
theorem wedinLemma20_12_rectMatMulVec_projection_eq_zero_of_projectionDiff_sq_eigenvalue_one_projection_swapped_range
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (x : Fin m → ℝ)
    (hxQ : rectMatMulVec Q x = x)
    (hxEig :
      rectMatMulVec
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)) x = x) :
    rectMatMulVec P x = 0 := by
  exact
    wedinLemma20_12_rectMatMulVec_projection_eq_zero_of_projection_swapped_range_companion_compression_eq_zero
      P Q hP hQ hIdemP x hxQ
      (wedinLemma20_12_rectMatMulVec_projection_swapped_mul_projection_mul_projection_swapped_eq_zero_of_projectionDiff_sq_eigenvalue_one_projection_swapped_range
        P Q hIdemP hIdemQ x hxQ hxEig)

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    local matrix-linearity helper for applying a matrix difference to a vector. -/
theorem wedinLemma20_12_rectMatMulVec_mat_sub
    {m n : ℕ} (M E : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    rectMatMulVec (fun i j => M i j - E i j) x =
      fun i => rectMatMulVec M x i - rectMatMulVec E x i := by
  ext i
  unfold rectMatMulVec
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    if a vector is fixed by `P` and killed by `Q`, then the projection
    difference `D = P-Q` fixes it. -/
theorem wedinLemma20_12_rectMatMulVec_projectionDiff_eq_self_of_projection_range_projection_swapped_zero
    {m : ℕ} (P Q : Fin m → Fin m → ℝ) (x : Fin m → ℝ)
    (hxP : rectMatMulVec P x = x)
    (hxQ : rectMatMulVec Q x = 0) :
    rectMatMulVec (fun i j => P i j - Q i j) x = x := by
  rw [wedinLemma20_12_rectMatMulVec_mat_sub, hxP, hxQ]
  ext i
  simp

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    if a vector is fixed by `Q` and killed by `P`, then `D = P-Q` acts as
    negation. -/
theorem wedinLemma20_12_rectMatMulVec_projectionDiff_eq_neg_self_of_projection_swapped_range_projection_zero
    {m : ℕ} (P Q : Fin m → Fin m → ℝ) (x : Fin m → ℝ)
    (hxQ : rectMatMulVec Q x = x)
    (hxP : rectMatMulVec P x = 0) :
    rectMatMulVec (fun i j => P i j - Q i j) x = fun i => -x i := by
  rw [wedinLemma20_12_rectMatMulVec_mat_sub, hxP, hxQ]
  ext i
  simp

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the `P`-range/`Q`-kernel characterization gives a `D^2` eigenvector with
    eigenvalue `1`. -/
theorem wedinLemma20_12_rectMatMulVec_projectionDiff_sq_eq_self_of_projection_range_projection_swapped_zero
    {m : ℕ} (P Q : Fin m → Fin m → ℝ) (x : Fin m → ℝ)
    (hxP : rectMatMulVec P x = x)
    (hxQ : rectMatMulVec Q x = 0) :
    rectMatMulVec
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)) x = x := by
  let D : Fin m → Fin m → ℝ := fun i j => P i j - Q i j
  have hxD : rectMatMulVec D x = x := by
    simpa [D] using
      wedinLemma20_12_rectMatMulVec_projectionDiff_eq_self_of_projection_range_projection_swapped_zero
        P Q x hxP hxQ
  calc
    rectMatMulVec (rectMatMul D D) x
        = rectMatMulVec D (rectMatMulVec D x) := by
            rw [rectMatMulVec_rectMatMul]
    _ = rectMatMulVec D x := by
            exact congrArg (rectMatMulVec D) hxD
    _ = x := hxD

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the swapped range/kernel characterization also gives a `D^2` eigenvector
    with eigenvalue `1`. -/
theorem wedinLemma20_12_rectMatMulVec_projectionDiff_sq_eq_self_of_projection_swapped_range_projection_zero
    {m : ℕ} (P Q : Fin m → Fin m → ℝ) (x : Fin m → ℝ)
    (hxQ : rectMatMulVec Q x = x)
    (hxP : rectMatMulVec P x = 0) :
    rectMatMulVec
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)) x = x := by
  let D : Fin m → Fin m → ℝ := fun i j => P i j - Q i j
  have hxD : rectMatMulVec D x = fun i => -x i := by
    simpa [D] using
      wedinLemma20_12_rectMatMulVec_projectionDiff_eq_neg_self_of_projection_swapped_range_projection_zero
        P Q x hxQ hxP
  have hneg :
      rectMatMulVec D (fun i => -x i) =
        fun i => -rectMatMulVec D x i := by
    have hvec : (fun i => -x i) = fun i => (-1 : ℝ) * x i := by
      ext i
      ring
    rw [hvec, rectMatMulVec_smul]
    ext i
    ring
  calc
    rectMatMulVec (rectMatMul D D) x
        = rectMatMulVec D (rectMatMulVec D x) := by
            rw [rectMatMulVec_rectMatMul]
    _ = rectMatMulVec D (fun i => -x i) := by
            rw [hxD]
    _ = fun i => -rectMatMulVec D x i := hneg
    _ = fun i => -(-x i) := by
            rw [hxD]
    _ = x := by
            ext i
            ring

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    on the range of `P`, the eigenvalue-`1` vectors of `D^2`, `D = P-Q`,
    are exactly the vectors killed by the swapped projection `Q`. -/
theorem wedinLemma20_12_projection_range_projectionDiff_sq_eq_self_iff_projection_swapped_zero
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (x : Fin m → ℝ)
    (hxP : rectMatMulVec P x = x) :
    rectMatMulVec
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)) x = x ↔
      rectMatMulVec Q x = 0 := by
  constructor
  · intro hxEig
    exact
      wedinLemma20_12_rectMatMulVec_projection_swapped_eq_zero_of_projectionDiff_sq_eigenvalue_one_projection_range
        P Q hP hQ hIdemP hIdemQ x hxP hxEig
  · intro hxQ
    exact
      wedinLemma20_12_rectMatMulVec_projectionDiff_sq_eq_self_of_projection_range_projection_swapped_zero
        P Q x hxP hxQ

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    swapped version: on the range of `Q`, the eigenvalue-`1` vectors of
    `D^2`, `D = P-Q`, are exactly the vectors killed by `P`. -/
theorem wedinLemma20_12_projection_swapped_range_projectionDiff_sq_eq_self_iff_projection_zero
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (x : Fin m → ℝ)
    (hxQ : rectMatMulVec Q x = x) :
    rectMatMulVec
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)) x = x ↔
      rectMatMulVec P x = 0 := by
  constructor
  · intro hxEig
    exact
      wedinLemma20_12_rectMatMulVec_projection_eq_zero_of_projectionDiff_sq_eigenvalue_one_projection_swapped_range
        P Q hP hQ hIdemP hIdemQ x hxQ hxEig
  · intro hxP
    exact
      wedinLemma20_12_rectMatMulVec_projectionDiff_sq_eq_self_of_projection_swapped_range_projection_zero
        P Q x hxQ hxP

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    on the range of `P`, the compressed operator `P(P-Q)^2P` acts as
    `(P-Q)^2`. -/
theorem wedinLemma20_12_rectMatMulVec_projectionDiff_sq_compression_apply_projection_range
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (x : Fin m → ℝ)
    (hxP : rectMatMulVec P x = x) :
    rectMatMulVec
        (rectMatMul
          (rectMatMul P
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          P) x =
      rectMatMulVec
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)) x := by
  let D2 : Fin m → Fin m → ℝ :=
    rectMatMul (fun i j => P i j - Q i j)
      (fun i j => P i j - Q i j)
  have hcomm : rectMatMul D2 P = rectMatMul P D2 := by
    simpa [D2] using
      wedinLemma20_12_projectionDiff_sq_commutes_projection
        P Q hIdemP hIdemQ
  calc
    rectMatMulVec (rectMatMul (rectMatMul P D2) P) x
        = rectMatMulVec (rectMatMul P D2) (rectMatMulVec P x) := by
            rw [rectMatMulVec_rectMatMul]
    _ = rectMatMulVec (rectMatMul P D2) x := by
            rw [hxP]
    _ = rectMatMulVec (rectMatMul D2 P) x := by
            rw [← hcomm]
    _ = rectMatMulVec D2 (rectMatMulVec P x) := by
            rw [rectMatMulVec_rectMatMul]
    _ = rectMatMulVec D2 x := by
            rw [hxP]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    swapped version: on the range of `Q`, the compressed operator
    `Q(P-Q)^2Q` acts as `(P-Q)^2`. -/
theorem wedinLemma20_12_rectMatMulVec_projectionDiff_sq_compression_apply_projection_swapped_range
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (x : Fin m → ℝ)
    (hxQ : rectMatMulVec Q x = x) :
    rectMatMulVec
        (rectMatMul
          (rectMatMul Q
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          Q) x =
      rectMatMulVec
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)) x := by
  let D2 : Fin m → Fin m → ℝ :=
    rectMatMul (fun i j => P i j - Q i j)
      (fun i j => P i j - Q i j)
  have hcomm : rectMatMul D2 Q = rectMatMul Q D2 := by
    simpa [D2] using
      wedinLemma20_12_projectionDiff_sq_commutes_projection_swapped
        P Q hIdemP hIdemQ
  calc
    rectMatMulVec (rectMatMul (rectMatMul Q D2) Q) x
        = rectMatMulVec (rectMatMul Q D2) (rectMatMulVec Q x) := by
            rw [rectMatMulVec_rectMatMul]
    _ = rectMatMulVec (rectMatMul Q D2) x := by
            rw [hxQ]
    _ = rectMatMulVec (rectMatMul D2 Q) x := by
            rw [← hcomm]
    _ = rectMatMulVec D2 (rectMatMulVec Q x) := by
            rw [rectMatMulVec_rectMatMul]
    _ = rectMatMulVec D2 x := by
            rw [hxQ]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    on the range of `P`, the eigenvalue-`1` vectors of the compressed
    operator `P(P-Q)^2P` are exactly the vectors killed by `Q`. -/
theorem wedinLemma20_12_projection_range_projectionDiff_sq_compression_eq_self_iff_projection_swapped_zero
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (x : Fin m → ℝ)
    (hxP : rectMatMulVec P x = x) :
    rectMatMulVec
        (rectMatMul
          (rectMatMul P
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          P) x = x ↔
      rectMatMulVec Q x = 0 := by
  rw [
    wedinLemma20_12_rectMatMulVec_projectionDiff_sq_compression_apply_projection_range
      P Q hIdemP hIdemQ x hxP]
  exact
    wedinLemma20_12_projection_range_projectionDiff_sq_eq_self_iff_projection_swapped_zero
      P Q hP hQ hIdemP hIdemQ x hxP

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    swapped version: on the range of `Q`, the eigenvalue-`1` vectors of
    `Q(P-Q)^2Q` are exactly the vectors killed by `P`. -/
theorem wedinLemma20_12_projection_swapped_range_projectionDiff_sq_compression_eq_self_iff_projection_zero
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (x : Fin m → ℝ)
    (hxQ : rectMatMulVec Q x = x) :
    rectMatMulVec
        (rectMatMul
          (rectMatMul Q
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          Q) x = x ↔
      rectMatMulVec P x = 0 := by
  rw [
    wedinLemma20_12_rectMatMulVec_projectionDiff_sq_compression_apply_projection_swapped_range
      P Q hIdemP hIdemQ x hxQ]
  exact
    wedinLemma20_12_projection_swapped_range_projectionDiff_sq_eq_self_iff_projection_zero
      P Q hP hQ hIdemP hIdemQ x hxQ

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    a nonzero compressed `D^2` eigenvalue for `P(P-Q)^2P` forces the
    eigenvector to lie in the range of `P`. -/
theorem wedinLemma20_12_projection_range_of_projectionDiff_sq_compression_eigenvalue_ne_zero
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (lambda : ℝ) (x : Fin m → ℝ)
    (hxEig :
      rectMatMulVec
          (rectMatMul
            (rectMatMul P
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            P) x =
        fun i => lambda * x i)
    (hlambda_ne_zero : lambda ≠ 0) :
    rectMatMulVec P x = x := by
  let D2 : Fin m → Fin m → ℝ :=
    rectMatMul (fun i j => P i j - Q i j)
      (fun i j => P i j - Q i j)
  let MP : Fin m → Fin m → ℝ := rectMatMul (rectMatMul P D2) P
  have hleft : rectMatMul P MP = MP := by
    dsimp [MP]
    calc
      rectMatMul P (rectMatMul (rectMatMul P D2) P)
          = rectMatMul (rectMatMul P (rectMatMul P D2)) P := by
              rw [← rectMatMul_assoc]
      _ = rectMatMul (rectMatMul (rectMatMul P P) D2) P := by
              rw [← rectMatMul_assoc]
      _ = rectMatMul (rectMatMul P D2) P := by
              rw [hIdemP]
  have hxEig' : rectMatMulVec MP x = fun i => lambda * x i := by
    simpa [MP, D2] using hxEig
  have hscaled :
      (fun i => lambda * rectMatMulVec P x i) =
        fun i => lambda * x i := by
    calc
      (fun i => lambda * rectMatMulVec P x i)
          = rectMatMulVec P (fun i => lambda * x i) := by
              rw [rectMatMulVec_smul]
      _ = rectMatMulVec P (rectMatMulVec MP x) := by
              rw [hxEig']
      _ = rectMatMulVec (rectMatMul P MP) x := by
              exact (rectMatMulVec_rectMatMul P MP x).symm
      _ = rectMatMulVec MP x := by
              rw [hleft]
      _ = fun i => lambda * x i := hxEig'
  ext i
  exact mul_left_cancel₀ hlambda_ne_zero (congrFun hscaled i)

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    swapped version: a nonzero compressed `D^2` eigenvalue for `Q(P-Q)^2Q`
    forces the eigenvector to lie in the range of `Q`. -/
theorem wedinLemma20_12_projection_swapped_range_of_projectionDiff_sq_compression_eigenvalue_ne_zero
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemQ : rectMatMul Q Q = Q)
    (lambda : ℝ) (x : Fin m → ℝ)
    (hxEig :
      rectMatMulVec
          (rectMatMul
            (rectMatMul Q
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            Q) x =
        fun i => lambda * x i)
    (hlambda_ne_zero : lambda ≠ 0) :
    rectMatMulVec Q x = x := by
  let D2 : Fin m → Fin m → ℝ :=
    rectMatMul (fun i j => P i j - Q i j)
      (fun i j => P i j - Q i j)
  let MQ : Fin m → Fin m → ℝ := rectMatMul (rectMatMul Q D2) Q
  have hleft : rectMatMul Q MQ = MQ := by
    dsimp [MQ]
    calc
      rectMatMul Q (rectMatMul (rectMatMul Q D2) Q)
          = rectMatMul (rectMatMul Q (rectMatMul Q D2)) Q := by
              rw [← rectMatMul_assoc]
      _ = rectMatMul (rectMatMul (rectMatMul Q Q) D2) Q := by
              rw [← rectMatMul_assoc]
      _ = rectMatMul (rectMatMul Q D2) Q := by
              rw [hIdemQ]
  have hxEig' : rectMatMulVec MQ x = fun i => lambda * x i := by
    simpa [MQ, D2] using hxEig
  have hscaled :
      (fun i => lambda * rectMatMulVec Q x i) =
        fun i => lambda * x i := by
    calc
      (fun i => lambda * rectMatMulVec Q x i)
          = rectMatMulVec Q (fun i => lambda * x i) := by
              rw [rectMatMulVec_smul]
      _ = rectMatMulVec Q (rectMatMulVec MQ x) := by
              rw [hxEig']
      _ = rectMatMulVec (rectMatMul Q MQ) x := by
              exact (rectMatMulVec_rectMatMul Q MQ x).symm
      _ = rectMatMulVec MQ x := by
              rw [hleft]
      _ = fun i => lambda * x i := hxEig'
  ext i
  exact mul_left_cancel₀ hlambda_ne_zero (congrFun hscaled i)

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    a nonzero, nonunit compressed `D^2` eigenvector transfers from the `P`
    compression to the `Q` compression with the same eigenvalue. -/
theorem wedinLemma20_12_exists_projection_swapped_range_projectionDiff_sq_compression_eigenvector_of_projection_range
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (lambda : ℝ) (x : Fin m → ℝ)
    (hxEig :
      rectMatMulVec
          (rectMatMul
            (rectMatMul P
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            P) x =
        fun i => lambda * x i)
    (hx_ne : x ≠ 0)
    (hlambda_ne_zero : lambda ≠ 0)
    (hlambda_ne_one : lambda ≠ 1) :
    ∃ y : Fin m → ℝ,
      y ≠ 0 ∧
      rectMatMulVec Q y = y ∧
      rectMatMulVec
          (rectMatMul
            (rectMatMul Q
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            Q) y =
        fun i => lambda * y i := by
  have hxP :
      rectMatMulVec P x = x :=
    wedinLemma20_12_projection_range_of_projectionDiff_sq_compression_eigenvalue_ne_zero
      P Q hIdemP lambda x hxEig hlambda_ne_zero
  have hxRaw :
      rectMatMulVec
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)) x =
        fun i => lambda * x i := by
    rw [←
      wedinLemma20_12_rectMatMulVec_projectionDiff_sq_compression_apply_projection_range
        P Q hIdemP hIdemQ x hxP]
    exact hxEig
  obtain ⟨y, hy_ne, hyQ, hyRaw⟩ :=
    wedinLemma20_12_exists_projection_swapped_range_projectionDiff_sq_eigenvector_of_projection_range
      P Q hIdemP hIdemQ lambda x hxP hxRaw hx_ne hlambda_ne_one
  refine ⟨y, hy_ne, hyQ, ?_⟩
  rw [
    wedinLemma20_12_rectMatMulVec_projectionDiff_sq_compression_apply_projection_swapped_range
      P Q hIdemP hIdemQ y hyQ]
  exact hyRaw

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    symmetric transfer of a nonzero, nonunit compressed `D^2` eigenvector from
    the `Q` compression to the `P` compression. -/
theorem wedinLemma20_12_exists_projection_range_projectionDiff_sq_compression_eigenvector_of_projection_swapped_range
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (lambda : ℝ) (x : Fin m → ℝ)
    (hxEig :
      rectMatMulVec
          (rectMatMul
            (rectMatMul Q
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            Q) x =
        fun i => lambda * x i)
    (hx_ne : x ≠ 0)
    (hlambda_ne_zero : lambda ≠ 0)
    (hlambda_ne_one : lambda ≠ 1) :
    ∃ y : Fin m → ℝ,
      y ≠ 0 ∧
      rectMatMulVec P y = y ∧
      rectMatMulVec
          (rectMatMul
            (rectMatMul P
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            P) y =
        fun i => lambda * y i := by
  have hxQ :
      rectMatMulVec Q x = x :=
    wedinLemma20_12_projection_swapped_range_of_projectionDiff_sq_compression_eigenvalue_ne_zero
      P Q hIdemQ lambda x hxEig hlambda_ne_zero
  have hxRaw :
      rectMatMulVec
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)) x =
        fun i => lambda * x i := by
    rw [←
      wedinLemma20_12_rectMatMulVec_projectionDiff_sq_compression_apply_projection_swapped_range
        P Q hIdemP hIdemQ x hxQ]
    exact hxEig
  obtain ⟨y, hy_ne, hyP, hyRaw⟩ :=
    wedinLemma20_12_exists_projection_range_projectionDiff_sq_eigenvector_of_projection_swapped_range
      P Q hIdemP hIdemQ lambda x hxQ hxRaw hx_ne hlambda_ne_one
  refine ⟨y, hy_ne, hyP, ?_⟩
  rw [
    wedinLemma20_12_rectMatMulVec_projectionDiff_sq_compression_apply_projection_range
      P Q hIdemP hIdemQ y hyP]
  exact hyRaw

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    left-compressing the companion square `S^2` to the `Q` range gives
    `Q*P*Q`. -/
theorem wedinLemma20_12_projection_swapped_mul_projectionSumSubId_sq_eq_projection_swapped_mul_projection_mul_projection_swapped
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    rectMatMul Q
        (rectMatMul (fun i j => P i j + Q i j - idMatrix m i j)
          (fun i j => P i j + Q i j - idMatrix m i j)) =
      rectMatMul (rectMatMul Q P) Q := by
  let S : Fin m → Fin m → ℝ := fun i j => P i j + Q i j - idMatrix m i j
  calc
    rectMatMul Q (rectMatMul S S)
        = rectMatMul (rectMatMul Q S) S := by
            rw [← rectMatMul_assoc]
    _ = rectMatMul (rectMatMul Q P) S := by
            rw [wedinLemma20_12_projection_swapped_mul_projectionSumSubId_eq_projection_swapped_mul_projection
              P Q hIdemQ]
    _ = rectMatMul Q (rectMatMul P S) := by
            rw [rectMatMul_assoc]
    _ = rectMatMul Q (rectMatMul P Q) := by
            rw [wedinLemma20_12_projection_mul_projectionSumSubId_eq_projection_mul_swapped
              P Q hIdemP]
    _ = rectMatMul (rectMatMul Q P) Q := by
            rw [← rectMatMul_assoc]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the companion operator `S = P+Q-I` intertwines the `PQP` and `QPQ`
    companion-square compressions.

This is a direct principal-angle route identity: it relates the two restricted
operators before any spectral or operator-norm comparison is invoked. -/
theorem wedinLemma20_12_projectionSumSubId_intertwines_companion_sq_compression
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    rectMatMul (fun i j => P i j + Q i j - idMatrix m i j)
        (rectMatMul (rectMatMul P Q) P) =
      rectMatMul (rectMatMul (rectMatMul Q P) Q)
        (fun i j => P i j + Q i j - idMatrix m i j) := by
  let S : Fin m → Fin m → ℝ := fun i j => P i j + Q i j - idMatrix m i j
  let S2 : Fin m → Fin m → ℝ := rectMatMul S S
  have hSP : rectMatMul S P = rectMatMul Q S := by
    simpa [S] using
      wedinLemma20_12_projectionSumSubId_intertwines_projection
        P Q hIdemP hIdemQ
  have hS2P : rectMatMul S2 P = rectMatMul (rectMatMul P Q) P := by
    simpa [S, S2] using
      wedinLemma20_12_projectionSumSubId_sq_mul_projection_eq_projection_mul_swapped_mul_projection
        P Q hIdemP hIdemQ
  have hS2Q : rectMatMul S2 Q = rectMatMul (rectMatMul Q P) Q := by
    simpa [S, S2] using
      wedinLemma20_12_projectionSumSubId_sq_mul_projection_swapped_eq_projection_swapped_mul_projection_mul_projection_swapped
        P Q hIdemP hIdemQ
  have hS_S2 : rectMatMul S S2 = rectMatMul S2 S := by
    dsimp [S2]
    exact (rectMatMul_assoc S S S).symm
  change
    rectMatMul S (rectMatMul (rectMatMul P Q) P) =
      rectMatMul (rectMatMul (rectMatMul Q P) Q) S
  calc
    rectMatMul S (rectMatMul (rectMatMul P Q) P)
        = rectMatMul S (rectMatMul S2 P) := by
            rw [hS2P]
    _ = rectMatMul (rectMatMul S S2) P := by
            rw [← rectMatMul_assoc]
    _ = rectMatMul (rectMatMul S2 S) P := by
            rw [hS_S2]
    _ = rectMatMul S2 (rectMatMul S P) := by
            rw [rectMatMul_assoc]
    _ = rectMatMul S2 (rectMatMul Q S) := by
            rw [hSP]
    _ = rectMatMul (rectMatMul S2 Q) S := by
            rw [← rectMatMul_assoc]
    _ = rectMatMul (rectMatMul (rectMatMul Q P) Q) S := by
            rw [hS2Q]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the swapped companion intertwinement for the `QPQ` and `PQP`
    companion-square compressions. -/
theorem wedinLemma20_12_projectionSumSubId_intertwines_companion_sq_compression_swapped
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    rectMatMul (fun i j => P i j + Q i j - idMatrix m i j)
        (rectMatMul (rectMatMul Q P) Q) =
      rectMatMul (rectMatMul (rectMatMul P Q) P)
        (fun i j => P i j + Q i j - idMatrix m i j) := by
  let S : Fin m → Fin m → ℝ := fun i j => P i j + Q i j - idMatrix m i j
  let S2 : Fin m → Fin m → ℝ := rectMatMul S S
  have hSQ : rectMatMul S Q = rectMatMul P S := by
    simpa [S] using
      wedinLemma20_12_projectionSumSubId_intertwines_projection_swapped
        P Q hIdemP hIdemQ
  have hS2P : rectMatMul S2 P = rectMatMul (rectMatMul P Q) P := by
    simpa [S, S2] using
      wedinLemma20_12_projectionSumSubId_sq_mul_projection_eq_projection_mul_swapped_mul_projection
        P Q hIdemP hIdemQ
  have hS2Q : rectMatMul S2 Q = rectMatMul (rectMatMul Q P) Q := by
    simpa [S, S2] using
      wedinLemma20_12_projectionSumSubId_sq_mul_projection_swapped_eq_projection_swapped_mul_projection_mul_projection_swapped
        P Q hIdemP hIdemQ
  have hS_S2 : rectMatMul S S2 = rectMatMul S2 S := by
    dsimp [S2]
    exact (rectMatMul_assoc S S S).symm
  change
    rectMatMul S (rectMatMul (rectMatMul Q P) Q) =
      rectMatMul (rectMatMul (rectMatMul P Q) P) S
  calc
    rectMatMul S (rectMatMul (rectMatMul Q P) Q)
        = rectMatMul S (rectMatMul S2 Q) := by
            rw [hS2Q]
    _ = rectMatMul (rectMatMul S S2) Q := by
            rw [← rectMatMul_assoc]
    _ = rectMatMul (rectMatMul S2 S) Q := by
            rw [hS_S2]
    _ = rectMatMul S2 (rectMatMul S Q) := by
            rw [rectMatMul_assoc]
    _ = rectMatMul S2 (rectMatMul P S) := by
            rw [hSQ]
    _ = rectMatMul (rectMatMul S2 P) S := by
            rw [← rectMatMul_assoc]
    _ = rectMatMul (rectMatMul (rectMatMul P Q) P) S := by
            rw [hS2P]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    on the `P` range, the companion-square compression `PQP` and the
    cross-Gram product `P(I-Q)P` are complementary pieces of `P`. -/
theorem wedinLemma20_12_projection_mul_swapped_mul_projection_add_crossGram_eq_projection
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P) :
    (fun i j =>
      rectMatMul (rectMatMul P Q) P i j +
        rectMatMul (rectMatMul P (fun i j => idMatrix m i j - Q i j)) P i j) =
      P := by
  let IQ : Fin m → Fin m → ℝ := fun i j => idMatrix m i j - Q i j
  have hQI : (fun i j => Q i j + IQ i j) = idMatrix m := by
    ext i j
    simp [IQ]
  calc
    (fun i j =>
      rectMatMul (rectMatMul P Q) P i j +
        rectMatMul (rectMatMul P IQ) P i j)
        = rectMatMul
            (fun i j => rectMatMul P Q i j + rectMatMul P IQ i j) P := by
            rw [rectMatMul_add_left]
    _ = rectMatMul (rectMatMul P (fun i j => Q i j + IQ i j)) P := by
            rw [rectMatMul_add_right]
    _ = rectMatMul (rectMatMul P (idMatrix m)) P := by
            rw [hQI]
    _ = rectMatMul P P := by
            rw [rectMatMul_id_right]
    _ = P := hIdemP

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the symmetric `Q`-range version of the companion/cross-Gram complement
    identity. -/
theorem wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_add_crossGram_swapped_eq_projection_swapped
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemQ : rectMatMul Q Q = Q) :
    (fun i j =>
      rectMatMul (rectMatMul Q P) Q i j +
        rectMatMul (rectMatMul Q (fun i j => idMatrix m i j - P i j)) Q i j) =
      Q := by
  simpa [add_comm] using
    wedinLemma20_12_projection_mul_swapped_mul_projection_add_crossGram_eq_projection
      Q P hIdemQ

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the `P`-range compression of `D^2`, with `D = P-Q`, is the complement of
    the companion-square compression `PQP` inside the projection `P`. -/
theorem wedinLemma20_12_projectionDiff_sq_compression_add_companion_sq_eq_projection
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    (fun i j =>
      rectMatMul
          (rectMatMul P
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          P i j +
        rectMatMul (rectMatMul P Q) P i j) =
      P := by
  have hD :=
    wedinLemma20_12_projection_projectionDiff_sq_projection_eq_crossGram
      P Q hIdemP hIdemQ
  have hAdd :=
    wedinLemma20_12_projection_mul_swapped_mul_projection_add_crossGram_eq_projection
      P Q hIdemP
  ext i j
  have hDij := congrFun (congrFun hD i) j
  have hAddij := congrFun (congrFun hAdd i) j
  rw [hDij]
  simpa [add_comm] using hAddij

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the swapped `Q`-range compression of `D^2`, with `D = P-Q`, is the
    complement of the companion-square compression `QPQ` inside `Q`. -/
theorem wedinLemma20_12_projectionDiff_sq_compression_swapped_add_companion_sq_swapped_eq_projection_swapped
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    (fun i j =>
      rectMatMul
          (rectMatMul Q
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          Q i j +
        rectMatMul (rectMatMul Q P) Q i j) =
      Q := by
  have hD :=
    wedinLemma20_12_projection_projectionDiff_sq_projection_eq_crossGram_swapped
      P Q hIdemP hIdemQ
  have hAdd :=
    wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_add_crossGram_swapped_eq_projection_swapped
      P Q hIdemQ
  ext i j
  have hDij := congrFun (congrFun hD i) j
  have hAddij := congrFun (congrFun hAdd i) j
  rw [hDij]
  simpa [add_comm] using hAddij

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the `P`-range companion-square compression `PQP` is a rectangular
    Gram product. -/
theorem wedinLemma20_12_projection_mul_swapped_mul_projection_eq_transpose_self
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemQ : rectMatMul Q Q = Q) :
    rectMatMul (finiteTranspose (rectMatMul Q P)) (rectMatMul Q P) =
      rectMatMul (rectMatMul P Q) P := by
  have htranspose :
      finiteTranspose (rectMatMul Q P) = rectMatMul P Q :=
    wedinLemma20_12_finiteTranspose_rectMatMul_of_symmetric Q P hQ hP
  rw [htranspose]
  calc
    rectMatMul (rectMatMul P Q) (rectMatMul Q P)
        = rectMatMul P (rectMatMul Q (rectMatMul Q P)) := by
            rw [rectMatMul_assoc]
    _ = rectMatMul P (rectMatMul (rectMatMul Q Q) P) := by
            rw [rectMatMul_assoc]
    _ = rectMatMul P (rectMatMul Q P) := by
            rw [hIdemQ]
    _ = rectMatMul (rectMatMul P Q) P := by
            rw [← rectMatMul_assoc]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the companion-square compression `PQP` is symmetric. -/
theorem wedinLemma20_12_projection_mul_swapped_mul_projection_symmetric
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemQ : rectMatMul Q Q = Q) :
    IsSymmetricFiniteMatrix (rectMatMul (rectMatMul P Q) P) := by
  have hEq :=
    wedinLemma20_12_projection_mul_swapped_mul_projection_eq_transpose_self
      P Q hP hQ hIdemQ
  exact
    IsSymmetricFiniteMatrix_of_eq_rectMatMul_transpose_self
      (rectMatMul Q P) hEq.symm

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the companion-square compression `PQP` is positive semidefinite. -/
theorem wedinLemma20_12_projection_mul_swapped_mul_projection_finitePSD
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemQ : rectMatMul Q Q = Q) :
    finitePSD (rectMatMul (rectMatMul P Q) P) := by
  have hEq :=
    wedinLemma20_12_projection_mul_swapped_mul_projection_eq_transpose_self
      P Q hP hQ hIdemQ
  exact
    finitePSD_of_eq_rectMatMul_transpose_self
      (rectMatMul Q P) hEq.symm

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the swapped companion-square compression `QPQ` is symmetric. -/
theorem wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_symmetric
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P) :
    IsSymmetricFiniteMatrix (rectMatMul (rectMatMul Q P) Q) :=
  wedinLemma20_12_projection_mul_swapped_mul_projection_symmetric
    Q P hQ hP hIdemP

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the swapped companion-square compression `QPQ` is positive semidefinite. -/
theorem wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_finitePSD
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P) :
    finitePSD (rectMatMul (rectMatMul Q P) Q) :=
  wedinLemma20_12_projection_mul_swapped_mul_projection_finitePSD
    Q P hQ hP hIdemP

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the `P(I-Q)P` cross-Gram complement is a rectangular Gram product. -/
theorem wedinLemma20_12_projection_mul_projectionComplement_mul_projection_eq_transpose_self
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemQ : rectMatMul Q Q = Q) :
    rectMatMul
        (finiteTranspose
          (rectMatMul (fun i j => idMatrix m i j - Q i j) P))
        (rectMatMul (fun i j => idMatrix m i j - Q i j) P) =
      rectMatMul
        (rectMatMul P (fun i j => idMatrix m i j - Q i j)) P := by
  let IQ : Fin m → Fin m → ℝ := fun i j => idMatrix m i j - Q i j
  have hIQ : IsSymmetricFiniteMatrix IQ :=
    wedinLemma20_12_projectionComplement_symmetric Q hQ
  have hIQIdem : rectMatMul IQ IQ = IQ := by
    simpa [IQ] using
      wedinLemma20_12_projectionComplement_idempotent Q hIdemQ
  have htranspose :
      finiteTranspose (rectMatMul IQ P) = rectMatMul P IQ :=
    wedinLemma20_12_finiteTranspose_rectMatMul_of_symmetric IQ P hIQ hP
  rw [htranspose]
  calc
    rectMatMul (rectMatMul P IQ) (rectMatMul IQ P)
        = rectMatMul P (rectMatMul IQ (rectMatMul IQ P)) := by
            rw [rectMatMul_assoc]
    _ = rectMatMul P (rectMatMul (rectMatMul IQ IQ) P) := by
            rw [rectMatMul_assoc]
    _ = rectMatMul P (rectMatMul IQ P) := by
            rw [hIQIdem]
    _ = rectMatMul (rectMatMul P IQ) P := by
            rw [← rectMatMul_assoc]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the `P(I-Q)P` cross-Gram complement is positive semidefinite. -/
theorem wedinLemma20_12_projection_mul_projectionComplement_mul_projection_finitePSD
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemQ : rectMatMul Q Q = Q) :
    finitePSD
      (rectMatMul
        (rectMatMul P (fun i j => idMatrix m i j - Q i j)) P) := by
  have hEq :=
    wedinLemma20_12_projection_mul_projectionComplement_mul_projection_eq_transpose_self
      P Q hP hQ hIdemQ
  exact
    finitePSD_of_eq_rectMatMul_transpose_self
      (rectMatMul (fun i j => idMatrix m i j - Q i j) P) hEq.symm

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the companion-square compression `PQP` is Loewner-bounded above by `P`. -/
theorem wedinLemma20_12_projection_mul_swapped_mul_projection_loewnerLe_projection
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    finiteLoewnerLe (rectMatMul (rectMatMul P Q) P) P := by
  let IQ : Fin m → Fin m → ℝ := fun i j => idMatrix m i j - Q i j
  have hPSD :
      finitePSD (rectMatMul (rectMatMul P IQ) P) := by
    simpa [IQ] using
      wedinLemma20_12_projection_mul_projectionComplement_mul_projection_finitePSD
        P Q hP hQ hIdemQ
  have hdiff :
      (fun i j => P i j - rectMatMul (rectMatMul P Q) P i j) =
        rectMatMul (rectMatMul P IQ) P := by
    have hsum :=
      wedinLemma20_12_projection_mul_swapped_mul_projection_add_crossGram_eq_projection
        P Q hIdemP
    ext i j
    have hij := congrFun (congrFun hsum i) j
    dsimp [IQ] at hij ⊢
    linarith
  exact
    (finiteLoewnerLe_iff_sub_finitePSD
      (rectMatMul (rectMatMul P Q) P) P).mpr
      (by simpa [hdiff] using hPSD)

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the swapped companion-square compression `QPQ` is Loewner-bounded above
    by `Q`. -/
theorem wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_loewnerLe_projection_swapped
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    finiteLoewnerLe (rectMatMul (rectMatMul Q P) Q) Q :=
  wedinLemma20_12_projection_mul_swapped_mul_projection_loewnerLe_projection
    Q P hQ hP hIdemQ hIdemP

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the complement of a symmetric idempotent projection is positive
    semidefinite. -/
theorem wedinLemma20_12_projectionComplement_finitePSD
    {m : ℕ} (P : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hIdemP : rectMatMul P P = P) :
    finitePSD (fun i j => idMatrix m i j - P i j) := by
  have hPSD :
      finitePSD
        (rectMatMul
          (rectMatMul (idMatrix m)
            (fun i j => idMatrix m i j - P i j))
          (idMatrix m)) :=
    wedinLemma20_12_projection_mul_projectionComplement_mul_projection_finitePSD
      (idMatrix m) P (ch7_idMatrix_symmetric m) hP hIdemP
  simpa [rectMatMul_id_left, rectMatMul_id_right] using hPSD

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    a symmetric idempotent projection is Loewner-bounded by the identity. -/
theorem wedinLemma20_12_projection_loewnerLe_id
    {m : ℕ} (P : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hIdemP : rectMatMul P P = P) :
    finiteLoewnerLe P (fun i j : Fin m => finiteIdMatrix i j) := by
  have hPSD :
      finitePSD (fun i j => idMatrix m i j - P i j) :=
    wedinLemma20_12_projectionComplement_finitePSD P hP hIdemP
  have hLe : finiteLoewnerLe P (idMatrix m) :=
    (finiteLoewnerLe_iff_sub_finitePSD P (idMatrix m)).mpr hPSD
  simpa [idMatrix, finiteIdMatrix] using hLe

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the companion-square compression `PQP` is Loewner-bounded by the identity. -/
theorem wedinLemma20_12_projection_mul_swapped_mul_projection_loewnerLe_id
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    finiteLoewnerLe (rectMatMul (rectMatMul P Q) P)
      (fun i j : Fin m => finiteIdMatrix i j) :=
  finiteLoewnerLe_trans
    (wedinLemma20_12_projection_mul_swapped_mul_projection_loewnerLe_projection
      P Q hP hQ hIdemP hIdemQ)
    (wedinLemma20_12_projection_loewnerLe_id P hP hIdemP)

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the swapped companion-square compression `QPQ` is Loewner-bounded by the
    identity. -/
theorem wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_loewnerLe_id
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    finiteLoewnerLe (rectMatMul (rectMatMul Q P) Q)
      (fun i j : Fin m => finiteIdMatrix i j) :=
  finiteLoewnerLe_trans
    (wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_loewnerLe_projection_swapped
      P Q hP hQ hIdemP hIdemQ)
    (wedinLemma20_12_projection_loewnerLe_id Q hQ hIdemQ)

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    every finite Hermitian eigenvalue of the companion-square compression
    `PQP` is nonnegative. -/
theorem wedinLemma20_12_projection_mul_swapped_mul_projection_finiteHermitianEigenvalues_nonneg
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemQ : rectMatMul Q Q = Q)
    (a : Fin m) :
    0 ≤
      finiteHermitianEigenvalues (rectMatMul (rectMatMul P Q) P)
        (wedinLemma20_12_projection_mul_swapped_mul_projection_symmetric
          P Q hP hQ hIdemQ) a := by
  have hSym :=
    wedinLemma20_12_projection_mul_swapped_mul_projection_symmetric
      P Q hP hQ hIdemQ
  have hPSD :=
    wedinLemma20_12_projection_mul_swapped_mul_projection_finitePSD
      P Q hP hQ hIdemQ
  exact
    (finitePSD_iff_finiteHermitianEigenvalues_nonneg
      (rectMatMul (rectMatMul P Q) P) hSym).mp hPSD a

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    every finite Hermitian eigenvalue of the companion-square compression
    `PQP` is at most one. -/
theorem wedinLemma20_12_projection_mul_swapped_mul_projection_finiteHermitianEigenvalues_le_one
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (a : Fin m) :
    finiteHermitianEigenvalues (rectMatMul (rectMatMul P Q) P)
        (wedinLemma20_12_projection_mul_swapped_mul_projection_symmetric
          P Q hP hQ hIdemQ) a ≤ 1 := by
  have hSym :=
    wedinLemma20_12_projection_mul_swapped_mul_projection_symmetric
      P Q hP hQ hIdemQ
  have hLe :
      finiteLoewnerLe (rectMatMul (rectMatMul P Q) P)
        (fun i j : Fin m => (1 : ℝ) * finiteIdMatrix i j) := by
    simpa using
      wedinLemma20_12_projection_mul_swapped_mul_projection_loewnerLe_id
        P Q hP hQ hIdemP hIdemQ
  exact
    finiteHermitianEigenvalues_le_of_finiteLoewnerLe_smul_id
      (rectMatMul (rectMatMul P Q) P) hSym hLe a

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    every finite Hermitian eigenvalue of the companion-square compression
    `PQP` is bounded above by its exact complexified Euclidean operator norm.

This is the lower-bound side of the PSD norm/top-eigenvalue route for the
principal-angle proof. -/
theorem wedinLemma20_12_projection_mul_swapped_mul_projection_finiteHermitianEigenvalues_le_complexMatrixOp2
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemQ : rectMatMul Q Q = Q)
    (a : Fin m) :
    finiteHermitianEigenvalues (rectMatMul (rectMatMul P Q) P)
        (wedinLemma20_12_projection_mul_swapped_mul_projection_symmetric
          P Q hP hQ hIdemQ) a ≤
      complexMatrixOp2
        (realRectToCMatrix (rectMatMul (rectMatMul P Q) P)) := by
  have hSym :=
    wedinLemma20_12_projection_mul_swapped_mul_projection_symmetric
      P Q hP hQ hIdemQ
  have hNonneg :=
    wedinLemma20_12_projection_mul_swapped_mul_projection_finiteHermitianEigenvalues_nonneg
      P Q hP hQ hIdemQ a
  exact
    finiteHermitianEigenvalues_le_of_nonneg_of_finiteOpNorm2Le
      (rectMatMul (rectMatMul P Q) P) hSym
      (opNorm2Le_complexMatrixOp2_realRectToCMatrix
        (rectMatMul (rectMatMul P Q) P))
      a hNonneg

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    on a nonempty ambient dimension, the exact complexified Euclidean operator
    norm of the PSD companion-square compression `PQP` is one of its locally
    named top Hermitian eigenvalues. -/
theorem wedinLemma20_12_exists_topEigenvalue_complexMatrixOp2_projection_mul_swapped_mul_projection_eq
    {m : ℕ} (hm : 0 < m) (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemQ : rectMatMul Q Q = Q) :
    ∃ a₀ : Fin m,
      complexMatrixOp2
          (realRectToCMatrix (rectMatMul (rectMatMul P Q) P)) =
        finiteHermitianEigenvalues (rectMatMul (rectMatMul P Q) P)
          (wedinLemma20_12_projection_mul_swapped_mul_projection_symmetric
            P Q hP hQ hIdemQ) a₀ ∧
      ∀ a : Fin m,
        finiteHermitianEigenvalues (rectMatMul (rectMatMul P Q) P)
            (wedinLemma20_12_projection_mul_swapped_mul_projection_symmetric
              P Q hP hQ hIdemQ) a ≤
          finiteHermitianEigenvalues (rectMatMul (rectMatMul P Q) P)
            (wedinLemma20_12_projection_mul_swapped_mul_projection_symmetric
              P Q hP hQ hIdemQ) a₀ := by
  let MPQ : Fin m → Fin m → ℝ := rectMatMul (rectMatMul P Q) P
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hSym :=
    wedinLemma20_12_projection_mul_swapped_mul_projection_symmetric
      P Q hP hQ hIdemQ
  have hPSD :=
    wedinLemma20_12_projection_mul_swapped_mul_projection_finitePSD
      P Q hP hQ hIdemQ
  obtain ⟨a₀, hNonneg, hMax, hFiniteOp⟩ :=
    exists_top_finiteHermitianEigenvalue_finiteOpNorm2Le_of_finitePSD
      MPQ hSym hPSD
  have hUpper :
      complexMatrixOp2 (realRectToCMatrix MPQ) ≤
        finiteHermitianEigenvalues MPQ hSym a₀ :=
    complexMatrixOp2_realRectToCMatrix_le_of_opNorm2Le
      MPQ hNonneg (opNorm2Le_of_finiteOpNorm2Le MPQ hFiniteOp)
  have hLower :
      finiteHermitianEigenvalues MPQ hSym a₀ ≤
        complexMatrixOp2 (realRectToCMatrix MPQ) := by
    simpa [MPQ] using
      wedinLemma20_12_projection_mul_swapped_mul_projection_finiteHermitianEigenvalues_le_complexMatrixOp2
        P Q hP hQ hIdemQ a₀
  exact ⟨a₀, le_antisymm hUpper hLower, hMax⟩

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    every finite Hermitian eigenvalue of the swapped companion-square
    compression `QPQ` is nonnegative. -/
theorem wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_finiteHermitianEigenvalues_nonneg
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (a : Fin m) :
    0 ≤
      finiteHermitianEigenvalues (rectMatMul (rectMatMul Q P) Q)
        (wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_symmetric
          P Q hP hQ hIdemP) a := by
  have hSym :=
    wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_symmetric
      P Q hP hQ hIdemP
  have hPSD :=
    wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_finitePSD
      P Q hP hQ hIdemP
  exact
    (finitePSD_iff_finiteHermitianEigenvalues_nonneg
      (rectMatMul (rectMatMul Q P) Q) hSym).mp hPSD a

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    every finite Hermitian eigenvalue of the swapped companion-square
    compression `QPQ` is at most one. -/
theorem wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_finiteHermitianEigenvalues_le_one
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (a : Fin m) :
    finiteHermitianEigenvalues (rectMatMul (rectMatMul Q P) Q)
        (wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_symmetric
          P Q hP hQ hIdemP) a ≤ 1 := by
  have hSym :=
    wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_symmetric
      P Q hP hQ hIdemP
  have hLe :
      finiteLoewnerLe (rectMatMul (rectMatMul Q P) Q)
        (fun i j : Fin m => (1 : ℝ) * finiteIdMatrix i j) := by
    simpa using
      wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_loewnerLe_id
        P Q hP hQ hIdemP hIdemQ
  exact
    finiteHermitianEigenvalues_le_of_finiteLoewnerLe_smul_id
      (rectMatMul (rectMatMul Q P) Q) hSym hLe a

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    every finite Hermitian eigenvalue of the swapped companion-square
    compression `QPQ` is bounded above by its exact complexified Euclidean
    operator norm. -/
theorem wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_finiteHermitianEigenvalues_le_complexMatrixOp2
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (a : Fin m) :
    finiteHermitianEigenvalues (rectMatMul (rectMatMul Q P) Q)
        (wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_symmetric
          P Q hP hQ hIdemP) a ≤
      complexMatrixOp2
        (realRectToCMatrix (rectMatMul (rectMatMul Q P) Q)) := by
  have hSym :=
    wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_symmetric
      P Q hP hQ hIdemP
  have hNonneg :=
    wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_finiteHermitianEigenvalues_nonneg
      P Q hP hQ hIdemP a
  exact
    finiteHermitianEigenvalues_le_of_nonneg_of_finiteOpNorm2Le
      (rectMatMul (rectMatMul Q P) Q) hSym
      (opNorm2Le_complexMatrixOp2_realRectToCMatrix
        (rectMatMul (rectMatMul Q P) Q))
      a hNonneg

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    on a nonempty ambient dimension, the exact complexified Euclidean operator
    norm of the swapped PSD companion-square compression `QPQ` is one of its
    locally named top Hermitian eigenvalues. -/
theorem wedinLemma20_12_exists_topEigenvalue_complexMatrixOp2_projection_swapped_mul_projection_mul_projection_swapped_eq
    {m : ℕ} (hm : 0 < m) (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P) :
    ∃ a₀ : Fin m,
      complexMatrixOp2
          (realRectToCMatrix (rectMatMul (rectMatMul Q P) Q)) =
        finiteHermitianEigenvalues (rectMatMul (rectMatMul Q P) Q)
          (wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_symmetric
            P Q hP hQ hIdemP) a₀ ∧
      ∀ a : Fin m,
        finiteHermitianEigenvalues (rectMatMul (rectMatMul Q P) Q)
            (wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_symmetric
              P Q hP hQ hIdemP) a ≤
          finiteHermitianEigenvalues (rectMatMul (rectMatMul Q P) Q)
            (wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_symmetric
              P Q hP hQ hIdemP) a₀ := by
  let MQP : Fin m → Fin m → ℝ := rectMatMul (rectMatMul Q P) Q
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hSym :=
    wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_symmetric
      P Q hP hQ hIdemP
  have hPSD :=
    wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_finitePSD
      P Q hP hQ hIdemP
  obtain ⟨a₀, hNonneg, hMax, hFiniteOp⟩ :=
    exists_top_finiteHermitianEigenvalue_finiteOpNorm2Le_of_finitePSD
      MQP hSym hPSD
  have hUpper :
      complexMatrixOp2 (realRectToCMatrix MQP) ≤
        finiteHermitianEigenvalues MQP hSym a₀ :=
    complexMatrixOp2_realRectToCMatrix_le_of_opNorm2Le
      MQP hNonneg (opNorm2Le_of_finiteOpNorm2Le MQP hFiniteOp)
  have hLower :
      finiteHermitianEigenvalues MQP hSym a₀ ≤
        complexMatrixOp2 (realRectToCMatrix MQP) := by
    simpa [MQP] using
      wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_finiteHermitianEigenvalues_le_complexMatrixOp2
        P Q hP hQ hIdemP a₀
  exact ⟨a₀, le_antisymm hUpper hLower, hMax⟩

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the two companion-square compressions `PQP` and `QPQ` have the same
    finite trace. -/
theorem wedinLemma20_12_finiteTrace_projection_mul_swapped_mul_projection_eq_swapped
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    finiteTrace (rectMatMul (rectMatMul P Q) P) =
      finiteTrace (rectMatMul (rectMatMul Q P) Q) := by
  calc
    finiteTrace (rectMatMul (rectMatMul P Q) P)
        = finiteTrace (rectMatMul P (rectMatMul P Q)) :=
            finiteTrace_rectMatMul_comm (rectMatMul P Q) P
    _ = finiteTrace (rectMatMul (rectMatMul P P) Q) := by
            rw [rectMatMul_assoc]
    _ = finiteTrace (rectMatMul P Q) := by
            rw [hIdemP]
    _ = finiteTrace (rectMatMul Q P) :=
            finiteTrace_rectMatMul_comm P Q
    _ = finiteTrace (rectMatMul (rectMatMul Q Q) P) := by
            rw [hIdemQ]
    _ = finiteTrace (rectMatMul Q (rectMatMul Q P)) := by
            rw [rectMatMul_assoc]
    _ = finiteTrace (rectMatMul (rectMatMul Q P) Q) :=
            (finiteTrace_rectMatMul_comm (rectMatMul Q P) Q).symm

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the finite trace of the `P`-range `D^2` compression is the projection
    trace minus the companion-square trace. -/
theorem wedinLemma20_12_finiteTrace_projectionDiff_sq_compression_eq_projection_sub_companion
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    finiteTrace
        (rectMatMul
          (rectMatMul P
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          P) =
      finiteTrace P - finiteTrace (rectMatMul (rectMatMul P Q) P) := by
  let MP : Fin m → Fin m → ℝ :=
    rectMatMul
      (rectMatMul P
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)))
      P
  let CP : Fin m → Fin m → ℝ := rectMatMul (rectMatMul P Q) P
  have hAdd :
      (fun i j => MP i j + CP i j) = P := by
    simpa [MP, CP] using
      wedinLemma20_12_projectionDiff_sq_compression_add_companion_sq_eq_projection
        P Q hIdemP hIdemQ
  have hTraceAdd :
      finiteTrace MP + finiteTrace CP = finiteTrace P := by
    have h := congrArg finiteTrace hAdd
    simpa [finiteTrace_add] using h
  linarith

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    swapped finite-trace version for the `Q`-range `D^2` compression. -/
theorem wedinLemma20_12_finiteTrace_projectionDiff_sq_compression_swapped_eq_projection_sub_companion
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    finiteTrace
        (rectMatMul
          (rectMatMul Q
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          Q) =
      finiteTrace Q - finiteTrace (rectMatMul (rectMatMul Q P) Q) := by
  let MQ : Fin m → Fin m → ℝ :=
    rectMatMul
      (rectMatMul Q
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)))
      Q
  let CQ : Fin m → Fin m → ℝ := rectMatMul (rectMatMul Q P) Q
  have hAdd :
      (fun i j => MQ i j + CQ i j) = Q := by
    simpa [MQ, CQ] using
      wedinLemma20_12_projectionDiff_sq_compression_swapped_add_companion_sq_swapped_eq_projection_swapped
        P Q hIdemP hIdemQ
  have hTraceAdd :
      finiteTrace MQ + finiteTrace CQ = finiteTrace Q := by
    have h := congrArg finiteTrace hAdd
    simpa [finiteTrace_add] using h
  linarith

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    equal projection traces imply equal finite traces for the two `D^2`
    range-compressions `P(P-Q)^2P` and `Q(P-Q)^2Q`. -/
theorem wedinLemma20_12_finiteTrace_projectionDiff_sq_compression_eq_swapped_of_projection_trace_eq
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (hTrace : finiteTrace P = finiteTrace Q) :
    finiteTrace
        (rectMatMul
          (rectMatMul P
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          P) =
      finiteTrace
        (rectMatMul
          (rectMatMul Q
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          Q) := by
  have hPTrace :=
    wedinLemma20_12_finiteTrace_projectionDiff_sq_compression_eq_projection_sub_companion
      P Q hIdemP hIdemQ
  have hQTrace :=
    wedinLemma20_12_finiteTrace_projectionDiff_sq_compression_swapped_eq_projection_sub_companion
      P Q hIdemP hIdemQ
  have hComp :
      finiteTrace (rectMatMul (rectMatMul P Q) P) =
        finiteTrace (rectMatMul (rectMatMul Q P) Q) :=
    wedinLemma20_12_finiteTrace_projection_mul_swapped_mul_projection_eq_swapped
      P Q hIdemP hIdemQ
  linarith

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the two companion-square compressions `PQP` and `QPQ` have the same
    second trace moment. -/
theorem wedinLemma20_12_finiteTrace_projection_mul_swapped_mul_projection_sq_eq_swapped
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    finiteTrace
        (rectMatMul (rectMatMul (rectMatMul P Q) P)
          (rectMatMul (rectMatMul P Q) P)) =
      finiteTrace
        (rectMatMul (rectMatMul (rectMatMul Q P) Q)
          (rectMatMul (rectMatMul Q P) Q)) := by
  let A : Fin m → Fin m → ℝ := rectMatMul (rectMatMul P Q) P
  let B : Fin m → Fin m → ℝ := rectMatMul (rectMatMul Q P) Q
  have hPA : rectMatMul P A = A := by
    dsimp [A]
    calc
      rectMatMul P (rectMatMul (rectMatMul P Q) P)
          = rectMatMul (rectMatMul P (rectMatMul P Q)) P := by
              rw [← rectMatMul_assoc]
      _ = rectMatMul (rectMatMul (rectMatMul P P) Q) P := by
              rw [← rectMatMul_assoc]
      _ = rectMatMul (rectMatMul P Q) P := by
              rw [hIdemP]
  have hAP : rectMatMul A P = A := by
    dsimp [A]
    calc
      rectMatMul (rectMatMul (rectMatMul P Q) P) P
          = rectMatMul (rectMatMul P Q) (rectMatMul P P) := by
              rw [rectMatMul_assoc]
      _ = rectMatMul (rectMatMul P Q) P := by
              rw [hIdemP]
  have hQB : rectMatMul Q B = B := by
    dsimp [B]
    calc
      rectMatMul Q (rectMatMul (rectMatMul Q P) Q)
          = rectMatMul (rectMatMul Q (rectMatMul Q P)) Q := by
              rw [← rectMatMul_assoc]
      _ = rectMatMul (rectMatMul (rectMatMul Q Q) P) Q := by
              rw [← rectMatMul_assoc]
      _ = rectMatMul (rectMatMul Q P) Q := by
              rw [hIdemQ]
  have hBQ : rectMatMul B Q = B := by
    dsimp [B]
    calc
      rectMatMul (rectMatMul (rectMatMul Q P) Q) Q
          = rectMatMul (rectMatMul Q P) (rectMatMul Q Q) := by
              rw [rectMatMul_assoc]
      _ = rectMatMul (rectMatMul Q P) Q := by
              rw [hIdemQ]
  have hTraceA : finiteTrace (rectMatMul A A) =
      finiteTrace (rectMatMul A Q) := by
    calc
      finiteTrace (rectMatMul A A)
          = finiteTrace (rectMatMul (rectMatMul A (rectMatMul P Q)) P) := by
              dsimp [A]
              rw [← rectMatMul_assoc]
      _ = finiteTrace (rectMatMul P (rectMatMul A (rectMatMul P Q))) :=
              finiteTrace_rectMatMul_comm (rectMatMul A (rectMatMul P Q)) P
      _ = finiteTrace (rectMatMul (rectMatMul P A) (rectMatMul P Q)) := by
              rw [← rectMatMul_assoc]
      _ = finiteTrace (rectMatMul A (rectMatMul P Q)) := by
              rw [hPA]
      _ = finiteTrace (rectMatMul (rectMatMul A P) Q) := by
              rw [← rectMatMul_assoc]
      _ = finiteTrace (rectMatMul A Q) := by
              rw [hAP]
  have hTraceB : finiteTrace (rectMatMul B B) =
      finiteTrace (rectMatMul B P) := by
    calc
      finiteTrace (rectMatMul B B)
          = finiteTrace (rectMatMul (rectMatMul B (rectMatMul Q P)) Q) := by
              dsimp [B]
              rw [← rectMatMul_assoc]
      _ = finiteTrace (rectMatMul Q (rectMatMul B (rectMatMul Q P))) :=
              finiteTrace_rectMatMul_comm (rectMatMul B (rectMatMul Q P)) Q
      _ = finiteTrace (rectMatMul (rectMatMul Q B) (rectMatMul Q P)) := by
              rw [← rectMatMul_assoc]
      _ = finiteTrace (rectMatMul B (rectMatMul Q P)) := by
              rw [hQB]
      _ = finiteTrace (rectMatMul (rectMatMul B Q) P) := by
              rw [← rectMatMul_assoc]
      _ = finiteTrace (rectMatMul B P) := by
              rw [hBQ]
  have hQA : rectMatMul Q A = rectMatMul B P := by
    dsimp [A, B]
    calc
      rectMatMul Q (rectMatMul (rectMatMul P Q) P)
          = rectMatMul (rectMatMul Q (rectMatMul P Q)) P := by
              rw [← rectMatMul_assoc]
      _ = rectMatMul (rectMatMul (rectMatMul Q P) Q) P := by
              rw [← rectMatMul_assoc]
  calc
    finiteTrace (rectMatMul A A)
        = finiteTrace (rectMatMul A Q) := hTraceA
    _ = finiteTrace (rectMatMul Q A) :=
            finiteTrace_rectMatMul_comm A Q
    _ = finiteTrace (rectMatMul B P) := by
            rw [hQA]
    _ = finiteTrace (rectMatMul B B) := hTraceB.symm

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the locally named finite Hermitian eigenvalues of the two
    companion-square compressions have equal sums. -/
theorem wedinLemma20_12_sum_finiteHermitianEigenvalues_projection_mul_swapped_mul_projection_eq_swapped
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    (∑ a : Fin m,
      finiteHermitianEigenvalues (rectMatMul (rectMatMul P Q) P)
        (wedinLemma20_12_projection_mul_swapped_mul_projection_symmetric
          P Q hP hQ hIdemQ) a) =
      ∑ a : Fin m,
        finiteHermitianEigenvalues (rectMatMul (rectMatMul Q P) Q)
          (wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_symmetric
            P Q hP hQ hIdemP) a := by
  let MPQ : Fin m → Fin m → ℝ := rectMatMul (rectMatMul P Q) P
  let MQP : Fin m → Fin m → ℝ := rectMatMul (rectMatMul Q P) Q
  have hSymPQ :
      IsSymmetricFiniteMatrix MPQ := by
    simpa [MPQ] using
      wedinLemma20_12_projection_mul_swapped_mul_projection_symmetric
        P Q hP hQ hIdemQ
  have hSymQP :
      IsSymmetricFiniteMatrix MQP := by
    simpa [MQP] using
      wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_symmetric
        P Q hP hQ hIdemP
  have hTrace : finiteTrace MPQ = finiteTrace MQP := by
    simpa [MPQ, MQP] using
      wedinLemma20_12_finiteTrace_projection_mul_swapped_mul_projection_eq_swapped
        P Q hIdemP hIdemQ
  calc
    (∑ a : Fin m, finiteHermitianEigenvalues MPQ hSymPQ a)
        = finiteTrace MPQ :=
            (finiteTrace_eq_sum_finiteHermitianEigenvalues MPQ hSymPQ).symm
    _ = finiteTrace MQP := hTrace
    _ = ∑ a : Fin m, finiteHermitianEigenvalues MQP hSymQP a :=
            finiteTrace_eq_sum_finiteHermitianEigenvalues MQP hSymQP

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the locally named finite Hermitian eigenvalues of the two
    companion-square compressions have equal sums of squares. -/
theorem wedinLemma20_12_sum_sq_finiteHermitianEigenvalues_projection_mul_swapped_mul_projection_eq_swapped
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    (∑ a : Fin m,
      finiteHermitianEigenvalues (rectMatMul (rectMatMul P Q) P)
        (wedinLemma20_12_projection_mul_swapped_mul_projection_symmetric
          P Q hP hQ hIdemQ) a ^ 2) =
      ∑ a : Fin m,
        finiteHermitianEigenvalues (rectMatMul (rectMatMul Q P) Q)
          (wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_symmetric
            P Q hP hQ hIdemP) a ^ 2 := by
  let MPQ : Fin m → Fin m → ℝ := rectMatMul (rectMatMul P Q) P
  let MQP : Fin m → Fin m → ℝ := rectMatMul (rectMatMul Q P) Q
  have hSymPQ :
      IsSymmetricFiniteMatrix MPQ := by
    simpa [MPQ] using
      wedinLemma20_12_projection_mul_swapped_mul_projection_symmetric
        P Q hP hQ hIdemQ
  have hSymQP :
      IsSymmetricFiniteMatrix MQP := by
    simpa [MQP] using
      wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_symmetric
        P Q hP hQ hIdemP
  have hTraceSq : finiteTrace (rectMatMul MPQ MPQ) =
      finiteTrace (rectMatMul MQP MQP) := by
    simpa [MPQ, MQP] using
      wedinLemma20_12_finiteTrace_projection_mul_swapped_mul_projection_sq_eq_swapped
        P Q hIdemP hIdemQ
  calc
    (∑ a : Fin m, finiteHermitianEigenvalues MPQ hSymPQ a ^ 2)
        = finiteTrace (rectMatMul MPQ MPQ) :=
            (finiteTrace_rectMatMul_self_eq_sum_sq_finiteHermitianEigenvalues
              MPQ hSymPQ).symm
    _ = finiteTrace (rectMatMul MQP MQP) := hTraceSq
    _ = ∑ a : Fin m, finiteHermitianEigenvalues MQP hSymQP a ^ 2 :=
            finiteTrace_rectMatMul_self_eq_sum_sq_finiteHermitianEigenvalues
              MQP hSymQP

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the companion-square compressions `PQP` and `QPQ` have the same
    complexified spectral radius.

This is a direct spectral-radius bridge for the principal-angle route.  It uses
only projection idempotence and the finite-dimensional fact `rho(AB)=rho(BA)`;
it does not yet identify this radius with the exact operator-2 norm of the PSD
compressions. -/
theorem wedinLemma20_12_toLin_spectralRadius_projection_mul_swapped_mul_projection_eq_swapped
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    spectralRadius ℂ
        (Matrix.toLin'
          (show Matrix (Fin m) (Fin m) ℂ from
            realRectToCMatrix (rectMatMul (rectMatMul P Q) P))) =
      spectralRadius ℂ
        (Matrix.toLin'
          (show Matrix (Fin m) (Fin m) ℂ from
            realRectToCMatrix (rectMatMul (rectMatMul Q P) Q))) := by
  let Pc : Matrix (Fin m) (Fin m) ℂ := realRectToCMatrix P
  let Qc : Matrix (Fin m) (Fin m) ℂ := realRectToCMatrix Q
  have hPidemC : Pc * Pc = Pc := by
    have hbase :
        realRectToCMatrix (rectMatMul P P) =
          realRectToCMatrix P := by
      rw [hIdemP]
    simpa [Pc, realRectToCMatrix_rectMatMul] using hbase
  have hQidemC : Qc * Qc = Qc := by
    have hbase :
        realRectToCMatrix (rectMatMul Q Q) =
          realRectToCMatrix Q := by
      rw [hIdemQ]
    simpa [Qc, realRectToCMatrix_rectMatMul] using hbase
  have hPQP :
      (show Matrix (Fin m) (Fin m) ℂ from
        realRectToCMatrix (rectMatMul (rectMatMul P Q) P)) =
        (Pc * Qc) * Pc := by
    ext i j
    simp [Pc, Qc, realRectToCMatrix_rectMatMul, complexMatrixMul,
      Matrix.mul_apply]
  have hQPQ :
      (show Matrix (Fin m) (Fin m) ℂ from
        realRectToCMatrix (rectMatMul (rectMatMul Q P) Q)) =
        (Qc * Pc) * Qc := by
    ext i j
    simp [Pc, Qc, realRectToCMatrix_rectMatMul, complexMatrixMul,
      Matrix.mul_apply]
  calc
    spectralRadius ℂ
        (Matrix.toLin'
          (show Matrix (Fin m) (Fin m) ℂ from
            realRectToCMatrix (rectMatMul (rectMatMul P Q) P)))
        = spectralRadius ℂ (Matrix.toLin' (Pc * (Qc * Pc))) := by
            rw [hPQP, Matrix.mul_assoc]
    _ = spectralRadius ℂ (Matrix.toLin' ((Qc * Pc) * Pc)) :=
            ch7_toLin_spectralRadius_mul_comm_eq Pc (Qc * Pc)
    _ = spectralRadius ℂ (Matrix.toLin' (Qc * Pc)) := by
            rw [Matrix.mul_assoc, hPidemC]
    _ = spectralRadius ℂ (Matrix.toLin' (Pc * Qc)) :=
            ch7_toLin_spectralRadius_mul_comm_eq Qc Pc
    _ = spectralRadius ℂ (Matrix.toLin' ((Pc * Qc) * Qc)) := by
            rw [Matrix.mul_assoc, hQidemC]
    _ = spectralRadius ℂ (Matrix.toLin' (Qc * (Pc * Qc))) :=
            (ch7_toLin_spectralRadius_mul_comm_eq Qc (Pc * Qc)).symm
    _ = spectralRadius ℂ
        (Matrix.toLin'
          (show Matrix (Fin m) (Fin m) ℂ from
            realRectToCMatrix (rectMatMul (rectMatMul Q P) Q))) := by
            rw [hQPQ, Matrix.mul_assoc]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the companion-square compressions `PQP` and `QPQ` have the same real
    matrix spectrum.

This is the spectrum-level counterpart of the existing spectral-radius bridge.
It uses only projection idempotence and the finite-dimensional fact that
products `AB` and `BA` have the same spectrum. -/
theorem wedinLemma20_12_spectrum_projection_mul_swapped_mul_projection_iff_swapped
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (lam : ℝ) :
    lam ∈ spectrum ℝ
        (show Matrix (Fin m) (Fin m) ℝ from
          (rectMatMul (rectMatMul P Q) P : Fin m → Fin m → ℝ)) ↔
      lam ∈ spectrum ℝ
        (show Matrix (Fin m) (Fin m) ℝ from
          (rectMatMul (rectMatMul Q P) Q : Fin m → Fin m → ℝ)) := by
  let Pr : Matrix (Fin m) (Fin m) ℝ := P
  let Qr : Matrix (Fin m) (Fin m) ℝ := Q
  have hPidemR : Pr * Pr = Pr := by
    ext i j
    have hij := congrFun (congrFun hIdemP i) j
    simpa [Pr, rectMatMul, Matrix.mul_apply] using hij
  have hQidemR : Qr * Qr = Qr := by
    ext i j
    have hij := congrFun (congrFun hIdemQ i) j
    simpa [Qr, rectMatMul, Matrix.mul_apply] using hij
  have hPQP :
      (show Matrix (Fin m) (Fin m) ℝ from
        (rectMatMul (rectMatMul P Q) P : Fin m → Fin m → ℝ)) =
        (Pr * Qr) * Pr := by
    ext i j
    simp [Pr, Qr, rectMatMul, Matrix.mul_apply]
  have hQPQ :
      (show Matrix (Fin m) (Fin m) ℝ from
        (rectMatMul (rectMatMul Q P) Q : Fin m → Fin m → ℝ)) =
        (Qr * Pr) * Qr := by
    ext i j
    simp [Pr, Qr, rectMatMul, Matrix.mul_apply]
  rw [hPQP, hQPQ]
  calc
    lam ∈ spectrum ℝ ((Pr * Qr) * Pr)
        ↔ lam ∈ spectrum ℝ (Pr * (Qr * Pr)) := by
            rw [Matrix.mul_assoc]
    _ ↔ lam ∈ spectrum ℝ ((Qr * Pr) * Pr) :=
            real_matrix_spectrum_mul_comm_iff Pr (Qr * Pr) lam
    _ ↔ lam ∈ spectrum ℝ (Qr * Pr) := by
            rw [Matrix.mul_assoc, hPidemR]
    _ ↔ lam ∈ spectrum ℝ (Pr * Qr) :=
            real_matrix_spectrum_mul_comm_iff Qr Pr lam
    _ ↔ lam ∈ spectrum ℝ ((Pr * Qr) * Qr) := by
            rw [Matrix.mul_assoc, hQidemR]
    _ ↔ lam ∈ spectrum ℝ (Qr * (Pr * Qr)) :=
            (real_matrix_spectrum_mul_comm_iff Qr (Pr * Qr) lam).symm
    _ ↔ lam ∈ spectrum ℝ ((Qr * Pr) * Qr) := by
            rw [Matrix.mul_assoc]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    any top locally named Hermitian eigenvalue of `PQP` equals any top locally
    named Hermitian eigenvalue of `QPQ`. -/
theorem wedinLemma20_12_top_finiteHermitianEigenvalue_projection_mul_swapped_mul_projection_eq_swapped_of_top
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    {aP aQ : Fin m}
    (hTopP : ∀ a : Fin m,
      finiteHermitianEigenvalues (rectMatMul (rectMatMul P Q) P)
          (wedinLemma20_12_projection_mul_swapped_mul_projection_symmetric
            P Q hP hQ hIdemQ) a ≤
        finiteHermitianEigenvalues (rectMatMul (rectMatMul P Q) P)
          (wedinLemma20_12_projection_mul_swapped_mul_projection_symmetric
            P Q hP hQ hIdemQ) aP)
    (hTopQ : ∀ a : Fin m,
      finiteHermitianEigenvalues (rectMatMul (rectMatMul Q P) Q)
          (wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_symmetric
            P Q hP hQ hIdemP) a ≤
        finiteHermitianEigenvalues (rectMatMul (rectMatMul Q P) Q)
          (wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_symmetric
            P Q hP hQ hIdemP) aQ) :
    finiteHermitianEigenvalues (rectMatMul (rectMatMul P Q) P)
        (wedinLemma20_12_projection_mul_swapped_mul_projection_symmetric
          P Q hP hQ hIdemQ) aP =
      finiteHermitianEigenvalues (rectMatMul (rectMatMul Q P) Q)
        (wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_symmetric
          P Q hP hQ hIdemP) aQ := by
  let MPQ : Fin m → Fin m → ℝ := rectMatMul (rectMatMul P Q) P
  let MQP : Fin m → Fin m → ℝ := rectMatMul (rectMatMul Q P) Q
  have hSymPQ : IsSymmetricFiniteMatrix MPQ := by
    simpa [MPQ] using
      wedinLemma20_12_projection_mul_swapped_mul_projection_symmetric
        P Q hP hQ hIdemQ
  have hSymQP : IsSymmetricFiniteMatrix MQP := by
    simpa [MQP] using
      wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_symmetric
        P Q hP hQ hIdemP
  have hTopP' :
      ∀ a : Fin m,
        finiteHermitianEigenvalues MPQ hSymPQ a ≤
          finiteHermitianEigenvalues MPQ hSymPQ aP := by
    intro a
    simpa [MPQ] using hTopP a
  have hTopQ' :
      ∀ a : Fin m,
        finiteHermitianEigenvalues MQP hSymQP a ≤
          finiteHermitianEigenvalues MQP hSymQP aQ := by
    intro a
    simpa [MQP] using hTopQ a
  have hSpecP :
      finiteHermitianEigenvalues MPQ hSymPQ aP ∈
        spectrum ℝ (show Matrix (Fin m) (Fin m) ℝ from MPQ) := by
    simpa [MPQ] using
      finiteHermitianEigenvalues_mem_spectrum_real MPQ hSymPQ aP
  have hSpecP_as_Q :
      finiteHermitianEigenvalues MPQ hSymPQ aP ∈
        spectrum ℝ (show Matrix (Fin m) (Fin m) ℝ from MQP) := by
    have htransfer :=
      (wedinLemma20_12_spectrum_projection_mul_swapped_mul_projection_iff_swapped
        P Q hIdemP hIdemQ
        (finiteHermitianEigenvalues MPQ hSymPQ aP)).mp
    exact htransfer (by simpa [MPQ] using hSpecP)
  have hRangeQ :
      finiteHermitianEigenvalues MPQ hSymPQ aP ∈
        Set.range (fun a : Fin m => finiteHermitianEigenvalues MQP hSymQP a) := by
    have hspec := hSpecP_as_Q
    rw [(IsSymmetricFiniteMatrix.to_matrix_isHermitian MQP hSymQP).spectrum_real_eq_range_eigenvalues] at hspec
    simpa [finiteHermitianEigenvalues] using hspec
  rcases hRangeQ with ⟨bQ, hbQ⟩
  have hP_le_Q :
      finiteHermitianEigenvalues MPQ hSymPQ aP ≤
        finiteHermitianEigenvalues MQP hSymQP aQ := by
    rw [← hbQ]
    exact hTopQ' bQ
  have hSpecQ :
      finiteHermitianEigenvalues MQP hSymQP aQ ∈
        spectrum ℝ (show Matrix (Fin m) (Fin m) ℝ from MQP) := by
    simpa [MQP] using
      finiteHermitianEigenvalues_mem_spectrum_real MQP hSymQP aQ
  have hSpecQ_as_P :
      finiteHermitianEigenvalues MQP hSymQP aQ ∈
        spectrum ℝ (show Matrix (Fin m) (Fin m) ℝ from MPQ) := by
    have htransfer :=
      (wedinLemma20_12_spectrum_projection_mul_swapped_mul_projection_iff_swapped
        P Q hIdemP hIdemQ
        (finiteHermitianEigenvalues MQP hSymQP aQ)).mpr
    exact htransfer (by simpa [MQP] using hSpecQ)
  have hRangeP :
      finiteHermitianEigenvalues MQP hSymQP aQ ∈
        Set.range (fun a : Fin m => finiteHermitianEigenvalues MPQ hSymPQ a) := by
    have hspec := hSpecQ_as_P
    rw [(IsSymmetricFiniteMatrix.to_matrix_isHermitian MPQ hSymPQ).spectrum_real_eq_range_eigenvalues] at hspec
    simpa [finiteHermitianEigenvalues] using hspec
  rcases hRangeP with ⟨bP, hbP⟩
  have hQ_le_P :
      finiteHermitianEigenvalues MQP hSymQP aQ ≤
        finiteHermitianEigenvalues MPQ hSymPQ aP := by
    rw [← hbP]
    exact hTopP' bP
  simpa [MPQ, MQP] using le_antisymm hP_le_Q hQ_le_P

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the exact complexified Euclidean operator norms of the companion-square
    compressions `PQP` and `QPQ` are equal. -/
theorem wedinLemma20_12_complexMatrixOp2_projection_mul_swapped_mul_projection_eq_swapped
    {m : ℕ} (hm : 0 < m) (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    complexMatrixOp2
        (realRectToCMatrix (rectMatMul (rectMatMul P Q) P)) =
      complexMatrixOp2
        (realRectToCMatrix (rectMatMul (rectMatMul Q P) Q)) := by
  obtain ⟨aP, hOpP, hTopP⟩ :=
    wedinLemma20_12_exists_topEigenvalue_complexMatrixOp2_projection_mul_swapped_mul_projection_eq
      hm P Q hP hQ hIdemQ
  obtain ⟨aQ, hOpQ, hTopQ⟩ :=
    wedinLemma20_12_exists_topEigenvalue_complexMatrixOp2_projection_swapped_mul_projection_mul_projection_swapped_eq
      hm P Q hP hQ hIdemP
  have hTopEq :=
    wedinLemma20_12_top_finiteHermitianEigenvalue_projection_mul_swapped_mul_projection_eq_swapped_of_top
      P Q hP hQ hIdemP hIdemQ hTopP hTopQ
  calc
    complexMatrixOp2
        (realRectToCMatrix (rectMatMul (rectMatMul P Q) P))
        = finiteHermitianEigenvalues (rectMatMul (rectMatMul P Q) P)
            (wedinLemma20_12_projection_mul_swapped_mul_projection_symmetric
              P Q hP hQ hIdemQ) aP := hOpP
    _ = finiteHermitianEigenvalues (rectMatMul (rectMatMul Q P) Q)
            (wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_symmetric
              P Q hP hQ hIdemP) aQ := hTopEq
    _ = complexMatrixOp2
        (realRectToCMatrix (rectMatMul (rectMatMul Q P) Q)) := hOpQ.symm

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the exact squared operator-2 norm of `P(I-Q)` is the exact operator-2 norm
    of the range-side compression `P(P-Q)^2P`.

This complements the existing `(I-Q)P(I-Q)` compressed-Gram bridge and records
the second standard Gram form used in principal-angle proofs. -/
theorem wedinLemma20_12_complexMatrixOp2_projectionDiff_sq_compression_eq_crossProjection_sq
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul
            (rectMatMul P
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            P)) =
      complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul P (fun i j => idMatrix m i j - Q i j))) ^ 2 := by
  let IQ : Fin m → Fin m → ℝ := fun i j => idMatrix m i j - Q i j
  let D : Fin m → Fin m → ℝ := fun i j => P i j - Q i j
  have hIQ : IsSymmetricFiniteMatrix IQ :=
    wedinLemma20_12_projectionComplement_symmetric Q hQ
  have htranspose :
      finiteTranspose (rectMatMul P IQ) = rectMatMul IQ P :=
    wedinLemma20_12_finiteTranspose_rectMatMul_of_symmetric P IQ hP hIQ
  have hcrossGram :
      rectMatMul (rectMatMul P IQ) P =
        rectMatMul (rectMatMul P IQ) (finiteTranspose (rectMatMul P IQ)) := by
    rw [htranspose]
    symm
    calc
      rectMatMul (rectMatMul P IQ) (rectMatMul IQ P)
          = rectMatMul (rectMatMul (rectMatMul P IQ) IQ) P := by
              exact (rectMatMul_assoc (rectMatMul P IQ) IQ P).symm
      _ = rectMatMul (rectMatMul P (rectMatMul IQ IQ)) P := by
              exact congrArg (fun X => rectMatMul X P)
                (rectMatMul_assoc P IQ IQ)
      _ = rectMatMul (rectMatMul P IQ) P := by
              have hIQIdem : rectMatMul IQ IQ = IQ := by
                simpa [IQ] using
                  wedinLemma20_12_projectionComplement_idempotent Q hIdemQ
              rw [hIQIdem]
  have hcompress :
      rectMatMul (rectMatMul P (rectMatMul D D)) P =
        rectMatMul (rectMatMul P IQ) P := by
    simpa [D, IQ] using
      wedinLemma20_12_projection_projectionDiff_sq_projection_eq_crossGram
        P Q hIdemP hIdemQ
  calc
    complexMatrixOp2
        (realRectToCMatrix (rectMatMul (rectMatMul P (rectMatMul D D)) P))
        = complexMatrixOp2
            (realRectToCMatrix (rectMatMul (rectMatMul P IQ) P)) := by
            rw [hcompress]
    _ = complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul (rectMatMul P IQ)
              (finiteTranspose (rectMatMul P IQ)))) := by
            rw [hcrossGram]
    _ = complexMatrixOp2 (realRectToCMatrix (rectMatMul P IQ)) ^ 2 :=
            complexMatrixOp2_realRectToCMatrix_mul_finiteTranspose_self_eq_sq
              (rectMatMul P IQ)

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    swapped version of the squared-norm compression bridge, using the same
    squared projection difference `(P-Q)^2`. -/
theorem wedinLemma20_12_complexMatrixOp2_projectionDiff_sq_compression_eq_crossProjection_sq_swapped
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul
            (rectMatMul Q
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            Q)) =
      complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul Q (fun i j => idMatrix m i j - P i j))) ^ 2 := by
  have hbase :=
    wedinLemma20_12_complexMatrixOp2_projectionDiff_sq_compression_eq_crossProjection_sq
      Q P hQ hP hIdemQ hIdemP
  have hsq :
      rectMatMul (fun i j => Q i j - P i j)
          (fun i j => Q i j - P i j) =
        rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j) := by
    ext i j
    unfold rectMatMul
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsq] at hbase
  simpa using hbase

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the `P`-range compression `P(P-Q)^2P` is symmetric. -/
theorem wedinLemma20_12_projectionDiff_sq_compression_symmetric
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    IsSymmetricFiniteMatrix
      (rectMatMul
        (rectMatMul P
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)))
        P) := by
  let IQ : Fin m → Fin m → ℝ := fun i j => idMatrix m i j - Q i j
  let D : Fin m → Fin m → ℝ := fun i j => P i j - Q i j
  have hIQ : IsSymmetricFiniteMatrix IQ :=
    wedinLemma20_12_projectionComplement_symmetric Q hQ
  have hCrossSym :
      IsSymmetricFiniteMatrix (rectMatMul (rectMatMul P IQ) P) := by
    have hEq :=
      wedinLemma20_12_projection_mul_projectionComplement_mul_projection_eq_transpose_self
        P Q hP hQ hIdemQ
    exact
      IsSymmetricFiniteMatrix_of_eq_rectMatMul_transpose_self
        (rectMatMul IQ P) hEq.symm
  have hCompress :
      rectMatMul (rectMatMul P (rectMatMul D D)) P =
        rectMatMul (rectMatMul P IQ) P := by
    simpa [D, IQ] using
      wedinLemma20_12_projection_projectionDiff_sq_projection_eq_crossGram
        P Q hIdemP hIdemQ
  simpa [D] using hCompress.symm ▸ hCrossSym

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the `P`-range compression `P(P-Q)^2P` is positive semidefinite. -/
theorem wedinLemma20_12_projectionDiff_sq_compression_finitePSD
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    finitePSD
      (rectMatMul
        (rectMatMul P
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)))
        P) := by
  let IQ : Fin m → Fin m → ℝ := fun i j => idMatrix m i j - Q i j
  let D : Fin m → Fin m → ℝ := fun i j => P i j - Q i j
  have hCrossPSD :
      finitePSD (rectMatMul (rectMatMul P IQ) P) := by
    simpa [IQ] using
      wedinLemma20_12_projection_mul_projectionComplement_mul_projection_finitePSD
        P Q hP hQ hIdemQ
  have hCompress :
      rectMatMul (rectMatMul P (rectMatMul D D)) P =
        rectMatMul (rectMatMul P IQ) P := by
    simpa [D, IQ] using
      wedinLemma20_12_projection_projectionDiff_sq_projection_eq_crossGram
        P Q hIdemP hIdemQ
  simpa [D] using hCompress.symm ▸ hCrossPSD

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the swapped `Q`-range compression `Q(P-Q)^2Q` is symmetric. -/
theorem wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    IsSymmetricFiniteMatrix
      (rectMatMul
        (rectMatMul Q
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)))
        Q) := by
  have hbase :=
    wedinLemma20_12_projectionDiff_sq_compression_symmetric
      Q P hQ hP hIdemQ hIdemP
  have hsq :
      rectMatMul (fun i j => Q i j - P i j)
          (fun i j => Q i j - P i j) =
        rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j) := by
    ext i j
    unfold rectMatMul
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsq] at hbase
  simpa using hbase

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the swapped `Q`-range compression `Q(P-Q)^2Q` is positive semidefinite. -/
theorem wedinLemma20_12_projectionDiff_sq_compression_swapped_finitePSD
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    finitePSD
      (rectMatMul
        (rectMatMul Q
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)))
        Q) := by
  have hbase :=
    wedinLemma20_12_projectionDiff_sq_compression_finitePSD
      Q P hQ hP hIdemQ hIdemP
  have hsq :
      rectMatMul (fun i j => Q i j - P i j)
          (fun i j => Q i j - P i j) =
        rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j) := by
    ext i j
    unfold rectMatMul
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsq] at hbase
  simpa using hbase

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the `P`-range `D^2` compression is Loewner-bounded above by the projection
    `P`. -/
theorem wedinLemma20_12_projectionDiff_sq_compression_loewnerLe_projection
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    finiteLoewnerLe
      (rectMatMul
        (rectMatMul P
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)))
        P) P := by
  let MP : Fin m → Fin m → ℝ :=
    rectMatMul
      (rectMatMul P
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)))
      P
  let CP : Fin m → Fin m → ℝ := rectMatMul (rectMatMul P Q) P
  have hPSDcomp : finitePSD CP := by
    simpa [CP] using
      wedinLemma20_12_projection_mul_swapped_mul_projection_finitePSD
        P Q hP hQ hIdemQ
  have hdiff :
      (fun i j => P i j - MP i j) = CP := by
    have hsum :=
      wedinLemma20_12_projectionDiff_sq_compression_add_companion_sq_eq_projection
        P Q hIdemP hIdemQ
    ext i j
    have hij := congrFun (congrFun hsum i) j
    dsimp [MP, CP] at hij ⊢
    linarith
  have hPSDdiff : finitePSD (fun i j => P i j - MP i j) := by
    rw [hdiff]
    exact hPSDcomp
  exact
    (finiteLoewnerLe_iff_sub_finitePSD MP P).mpr hPSDdiff

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    swapped Loewner upper bound for the `Q`-range `D^2` compression. -/
theorem wedinLemma20_12_projectionDiff_sq_compression_swapped_loewnerLe_projection_swapped
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    finiteLoewnerLe
      (rectMatMul
        (rectMatMul Q
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)))
        Q) Q := by
  have hbase :=
    wedinLemma20_12_projectionDiff_sq_compression_loewnerLe_projection
      Q P hQ hP hIdemQ hIdemP
  have hsq :
      rectMatMul (fun i j => Q i j - P i j)
          (fun i j => Q i j - P i j) =
        rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j) := by
    ext i j
    unfold rectMatMul
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsq] at hbase
  simpa using hbase

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the `P`-range `D^2` compression is Loewner-bounded above by the identity. -/
theorem wedinLemma20_12_projectionDiff_sq_compression_loewnerLe_id
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    finiteLoewnerLe
      (rectMatMul
        (rectMatMul P
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)))
        P)
      (fun i j : Fin m => finiteIdMatrix i j) :=
  finiteLoewnerLe_trans
    (wedinLemma20_12_projectionDiff_sq_compression_loewnerLe_projection
      P Q hP hQ hIdemP hIdemQ)
    (wedinLemma20_12_projection_loewnerLe_id P hP hIdemP)

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    swapped identity upper bound for the `Q`-range `D^2` compression. -/
theorem wedinLemma20_12_projectionDiff_sq_compression_swapped_loewnerLe_id
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    finiteLoewnerLe
      (rectMatMul
        (rectMatMul Q
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)))
        Q)
      (fun i j : Fin m => finiteIdMatrix i j) :=
  finiteLoewnerLe_trans
    (wedinLemma20_12_projectionDiff_sq_compression_swapped_loewnerLe_projection_swapped
      P Q hP hQ hIdemP hIdemQ)
    (wedinLemma20_12_projection_loewnerLe_id Q hQ hIdemQ)

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    every finite Hermitian eigenvalue of `P(P-Q)^2P` is nonnegative. -/
theorem wedinLemma20_12_projectionDiff_sq_compression_finiteHermitianEigenvalues_nonneg
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (a : Fin m) :
    0 ≤
      finiteHermitianEigenvalues
        (rectMatMul
          (rectMatMul P
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          P)
        (wedinLemma20_12_projectionDiff_sq_compression_symmetric
          P Q hP hQ hIdemP hIdemQ) a := by
  have hSym :=
    wedinLemma20_12_projectionDiff_sq_compression_symmetric
      P Q hP hQ hIdemP hIdemQ
  have hPSD :=
    wedinLemma20_12_projectionDiff_sq_compression_finitePSD
      P Q hP hQ hIdemP hIdemQ
  exact
    (finitePSD_iff_finiteHermitianEigenvalues_nonneg
      (rectMatMul
        (rectMatMul P
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)))
        P) hSym).mp hPSD a

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    every finite Hermitian eigenvalue of `P(P-Q)^2P` is at most one. -/
theorem wedinLemma20_12_projectionDiff_sq_compression_finiteHermitianEigenvalues_le_one
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (a : Fin m) :
    finiteHermitianEigenvalues
        (rectMatMul
          (rectMatMul P
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          P)
        (wedinLemma20_12_projectionDiff_sq_compression_symmetric
          P Q hP hQ hIdemP hIdemQ) a ≤ 1 := by
  let MP : Fin m → Fin m → ℝ :=
    rectMatMul
      (rectMatMul P
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)))
      P
  have hSym : IsSymmetricFiniteMatrix MP := by
    simpa [MP] using
      wedinLemma20_12_projectionDiff_sq_compression_symmetric
        P Q hP hQ hIdemP hIdemQ
  have hLe :
      finiteLoewnerLe MP
        (fun i j : Fin m => (1 : ℝ) * finiteIdMatrix i j) := by
    simpa [MP] using
      wedinLemma20_12_projectionDiff_sq_compression_loewnerLe_id
        P Q hP hQ hIdemP hIdemQ
  simpa [MP] using
    finiteHermitianEigenvalues_le_of_finiteLoewnerLe_smul_id
      MP hSym hLe a

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    every finite Hermitian eigenvalue of `P(P-Q)^2P` is bounded above by its
    exact complexified Euclidean operator norm. -/
theorem wedinLemma20_12_projectionDiff_sq_compression_finiteHermitianEigenvalues_le_complexMatrixOp2
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (a : Fin m) :
    finiteHermitianEigenvalues
        (rectMatMul
          (rectMatMul P
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          P)
        (wedinLemma20_12_projectionDiff_sq_compression_symmetric
          P Q hP hQ hIdemP hIdemQ) a ≤
      complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul
            (rectMatMul P
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            P)) := by
  have hSym :=
    wedinLemma20_12_projectionDiff_sq_compression_symmetric
      P Q hP hQ hIdemP hIdemQ
  have hNonneg :=
    wedinLemma20_12_projectionDiff_sq_compression_finiteHermitianEigenvalues_nonneg
      P Q hP hQ hIdemP hIdemQ a
  exact
    finiteHermitianEigenvalues_le_of_nonneg_of_finiteOpNorm2Le
      (rectMatMul
        (rectMatMul P
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)))
        P) hSym
      (opNorm2Le_complexMatrixOp2_realRectToCMatrix
        (rectMatMul
          (rectMatMul P
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          P))
      a hNonneg

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    on a nonempty ambient dimension, the exact complexified Euclidean operator
    norm of `P(P-Q)^2P` is one of its locally named top Hermitian eigenvalues. -/
theorem wedinLemma20_12_exists_topEigenvalue_complexMatrixOp2_projectionDiff_sq_compression_eq
    {m : ℕ} (hm : 0 < m) (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    ∃ a₀ : Fin m,
      complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul
              (rectMatMul P
                (rectMatMul (fun i j => P i j - Q i j)
                  (fun i j => P i j - Q i j)))
              P)) =
        finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul P
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            P)
          (wedinLemma20_12_projectionDiff_sq_compression_symmetric
            P Q hP hQ hIdemP hIdemQ) a₀ ∧
      ∀ a : Fin m,
        finiteHermitianEigenvalues
            (rectMatMul
              (rectMatMul P
                (rectMatMul (fun i j => P i j - Q i j)
                  (fun i j => P i j - Q i j)))
              P)
            (wedinLemma20_12_projectionDiff_sq_compression_symmetric
              P Q hP hQ hIdemP hIdemQ) a ≤
          finiteHermitianEigenvalues
            (rectMatMul
              (rectMatMul P
                (rectMatMul (fun i j => P i j - Q i j)
                  (fun i j => P i j - Q i j)))
              P)
            (wedinLemma20_12_projectionDiff_sq_compression_symmetric
              P Q hP hQ hIdemP hIdemQ) a₀ := by
  let MP : Fin m → Fin m → ℝ :=
    rectMatMul
      (rectMatMul P
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)))
      P
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hSym :=
    wedinLemma20_12_projectionDiff_sq_compression_symmetric
      P Q hP hQ hIdemP hIdemQ
  have hPSD :=
    wedinLemma20_12_projectionDiff_sq_compression_finitePSD
      P Q hP hQ hIdemP hIdemQ
  obtain ⟨a₀, hNonneg, hMax, hFiniteOp⟩ :=
    exists_top_finiteHermitianEigenvalue_finiteOpNorm2Le_of_finitePSD
      MP hSym hPSD
  have hUpper :
      complexMatrixOp2 (realRectToCMatrix MP) ≤
        finiteHermitianEigenvalues MP hSym a₀ :=
    complexMatrixOp2_realRectToCMatrix_le_of_opNorm2Le
      MP hNonneg (opNorm2Le_of_finiteOpNorm2Le MP hFiniteOp)
  have hLower :
      finiteHermitianEigenvalues MP hSym a₀ ≤
        complexMatrixOp2 (realRectToCMatrix MP) := by
    simpa [MP] using
      wedinLemma20_12_projectionDiff_sq_compression_finiteHermitianEigenvalues_le_complexMatrixOp2
        P Q hP hQ hIdemP hIdemQ a₀
  exact ⟨a₀, le_antisymm hUpper hLower, hMax⟩

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    every finite Hermitian eigenvalue of `Q(P-Q)^2Q` is nonnegative. -/
theorem wedinLemma20_12_projectionDiff_sq_compression_swapped_finiteHermitianEigenvalues_nonneg
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (a : Fin m) :
    0 ≤
      finiteHermitianEigenvalues
        (rectMatMul
          (rectMatMul Q
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          Q)
        (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
          P Q hP hQ hIdemP hIdemQ) a := by
  have hSym :=
    wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
      P Q hP hQ hIdemP hIdemQ
  have hPSD :=
    wedinLemma20_12_projectionDiff_sq_compression_swapped_finitePSD
      P Q hP hQ hIdemP hIdemQ
  exact
    (finitePSD_iff_finiteHermitianEigenvalues_nonneg
      (rectMatMul
        (rectMatMul Q
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)))
        Q) hSym).mp hPSD a

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    every finite Hermitian eigenvalue of `Q(P-Q)^2Q` is at most one. -/
theorem wedinLemma20_12_projectionDiff_sq_compression_swapped_finiteHermitianEigenvalues_le_one
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (a : Fin m) :
    finiteHermitianEigenvalues
        (rectMatMul
          (rectMatMul Q
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          Q)
        (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
          P Q hP hQ hIdemP hIdemQ) a ≤ 1 := by
  let MQ : Fin m → Fin m → ℝ :=
    rectMatMul
      (rectMatMul Q
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)))
      Q
  have hSym : IsSymmetricFiniteMatrix MQ := by
    simpa [MQ] using
      wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
        P Q hP hQ hIdemP hIdemQ
  have hLe :
      finiteLoewnerLe MQ
        (fun i j : Fin m => (1 : ℝ) * finiteIdMatrix i j) := by
    simpa [MQ] using
      wedinLemma20_12_projectionDiff_sq_compression_swapped_loewnerLe_id
        P Q hP hQ hIdemP hIdemQ
  simpa [MQ] using
    finiteHermitianEigenvalues_le_of_finiteLoewnerLe_smul_id
      MQ hSym hLe a

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    every finite Hermitian eigenvalue of `Q(P-Q)^2Q` is bounded above by its
    exact complexified Euclidean operator norm. -/
theorem wedinLemma20_12_projectionDiff_sq_compression_swapped_finiteHermitianEigenvalues_le_complexMatrixOp2
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (a : Fin m) :
    finiteHermitianEigenvalues
        (rectMatMul
          (rectMatMul Q
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          Q)
        (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
          P Q hP hQ hIdemP hIdemQ) a ≤
      complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul
            (rectMatMul Q
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            Q)) := by
  have hSym :=
    wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
      P Q hP hQ hIdemP hIdemQ
  have hNonneg :=
    wedinLemma20_12_projectionDiff_sq_compression_swapped_finiteHermitianEigenvalues_nonneg
      P Q hP hQ hIdemP hIdemQ a
  exact
    finiteHermitianEigenvalues_le_of_nonneg_of_finiteOpNorm2Le
      (rectMatMul
        (rectMatMul Q
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)))
        Q) hSym
      (opNorm2Le_complexMatrixOp2_realRectToCMatrix
        (rectMatMul
          (rectMatMul Q
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          Q))
      a hNonneg

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    on a nonempty ambient dimension, the exact complexified Euclidean operator
    norm of `Q(P-Q)^2Q` is one of its locally named top Hermitian eigenvalues. -/
theorem wedinLemma20_12_exists_topEigenvalue_complexMatrixOp2_projectionDiff_sq_compression_swapped_eq
    {m : ℕ} (hm : 0 < m) (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    ∃ a₀ : Fin m,
      complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul
              (rectMatMul Q
                (rectMatMul (fun i j => P i j - Q i j)
                  (fun i j => P i j - Q i j)))
              Q)) =
        finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul Q
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            Q)
          (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
            P Q hP hQ hIdemP hIdemQ) a₀ ∧
      ∀ a : Fin m,
        finiteHermitianEigenvalues
            (rectMatMul
              (rectMatMul Q
                (rectMatMul (fun i j => P i j - Q i j)
                  (fun i j => P i j - Q i j)))
              Q)
            (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
              P Q hP hQ hIdemP hIdemQ) a ≤
          finiteHermitianEigenvalues
            (rectMatMul
              (rectMatMul Q
                (rectMatMul (fun i j => P i j - Q i j)
                  (fun i j => P i j - Q i j)))
              Q)
            (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
              P Q hP hQ hIdemP hIdemQ) a₀ := by
  let MQ : Fin m → Fin m → ℝ :=
    rectMatMul
      (rectMatMul Q
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)))
      Q
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hSym :=
    wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
      P Q hP hQ hIdemP hIdemQ
  have hPSD :=
    wedinLemma20_12_projectionDiff_sq_compression_swapped_finitePSD
      P Q hP hQ hIdemP hIdemQ
  obtain ⟨a₀, hNonneg, hMax, hFiniteOp⟩ :=
    exists_top_finiteHermitianEigenvalue_finiteOpNorm2Le_of_finitePSD
      MQ hSym hPSD
  have hUpper :
      complexMatrixOp2 (realRectToCMatrix MQ) ≤
        finiteHermitianEigenvalues MQ hSym a₀ :=
    complexMatrixOp2_realRectToCMatrix_le_of_opNorm2Le
      MQ hNonneg (opNorm2Le_of_finiteOpNorm2Le MQ hFiniteOp)
  have hLower :
      finiteHermitianEigenvalues MQ hSym a₀ ≤
        complexMatrixOp2 (realRectToCMatrix MQ) := by
    simpa [MQ] using
      wedinLemma20_12_projectionDiff_sq_compression_swapped_finiteHermitianEigenvalues_le_complexMatrixOp2
        P Q hP hQ hIdemP hIdemQ a₀
  exact ⟨a₀, le_antisymm hUpper hLower, hMax⟩

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    endpoint characterization for the selected top eigenvalue of
    `P(P-Q)^2P`.  Under a top-index certificate, that top value is `1`
    exactly when the exceptional range/kernel subspace
    `ran(P) ∩ ker(Q)` contains a nonzero vector.

This packages the `lambda = 1` endpoint into a finite-dimensional
range/kernel problem; it does not compare the two endpoint multiplicities. -/
theorem wedinLemma20_12_top_finiteHermitianEigenvalue_projectionDiff_sq_compression_eq_one_iff_exists_projection_range_projection_swapped_zero
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    {aP : Fin m}
    (hTopP : ∀ a : Fin m,
      finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul P
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            P)
          (wedinLemma20_12_projectionDiff_sq_compression_symmetric
            P Q hP hQ hIdemP hIdemQ) a ≤
        finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul P
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            P)
          (wedinLemma20_12_projectionDiff_sq_compression_symmetric
            P Q hP hQ hIdemP hIdemQ) aP) :
    finiteHermitianEigenvalues
        (rectMatMul
          (rectMatMul P
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          P)
        (wedinLemma20_12_projectionDiff_sq_compression_symmetric
          P Q hP hQ hIdemP hIdemQ) aP = 1 ↔
      ∃ x : Fin m → ℝ,
        x ≠ 0 ∧
        rectMatMulVec P x = x ∧
        rectMatMulVec Q x = 0 := by
  let MP : Fin m → Fin m → ℝ :=
    rectMatMul
      (rectMatMul P
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)))
      P
  have hSymP : IsSymmetricFiniteMatrix MP := by
    simpa [MP] using
      wedinLemma20_12_projectionDiff_sq_compression_symmetric
        P Q hP hQ hIdemP hIdemQ
  let lambdaP : ℝ := finiteHermitianEigenvalues MP hSymP aP
  have hTopP' :
      ∀ a : Fin m, finiteHermitianEigenvalues MP hSymP a ≤ lambdaP := by
    intro a
    simpa [MP, lambdaP] using hTopP a
  constructor
  · intro hTop_eq_one
    have hLambda_eq_one : lambdaP = 1 := by
      simpa [MP, lambdaP] using hTop_eq_one
    let xP : Fin m → ℝ :=
      ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian MP hSymP).eigenvectorBasis aP)
    have hxP_ne : xP ≠ 0 := by
      intro hx0
      have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one MP hSymP aP
      change finiteVecNorm2Sq xP = 1 at hnorm
      rw [hx0] at hnorm
      simp [finiteVecNorm2Sq] at hnorm
    have hxP_eig :
        rectMatMulVec MP xP = fun i => lambdaP * xP i := by
      have h := finiteMatVec_finiteHermitianEigenvector_eq MP hSymP aP
      simpa [finiteMatVec, rectMatMulVec, MP, xP, lambdaP] using h
    have hLambda_ne_zero : lambdaP ≠ 0 := by
      simp [hLambda_eq_one]
    have hxP_range :
        rectMatMulVec P xP = xP :=
      wedinLemma20_12_projection_range_of_projectionDiff_sq_compression_eigenvalue_ne_zero
        P Q hIdemP lambdaP xP
        (by simpa [MP] using hxP_eig) hLambda_ne_zero
    have hxP_compress_self : rectMatMulVec MP xP = xP := by
      calc
        rectMatMulVec MP xP = fun i => lambdaP * xP i := hxP_eig
        _ = xP := by
              ext i
              simp [hLambda_eq_one]
    have hxQ_zero : rectMatMulVec Q xP = 0 :=
      (wedinLemma20_12_projection_range_projectionDiff_sq_compression_eq_self_iff_projection_swapped_zero
        P Q hP hQ hIdemP hIdemQ xP hxP_range).mp
        (by simpa [MP] using hxP_compress_self)
    exact ⟨xP, hxP_ne, hxP_range, hxQ_zero⟩
  · rintro ⟨x, hx_ne, hxP_range, hxQ_zero⟩
    have hxP_compress_self :
        rectMatMulVec MP x = x := by
      simpa [MP] using
        (wedinLemma20_12_projection_range_projectionDiff_sq_compression_eq_self_iff_projection_swapped_zero
          P Q hP hQ hIdemP hIdemQ x hxP_range).mpr hxQ_zero
    have hxP_eig :
        finiteMatVec MP x = fun i => (1 : ℝ) * x i := by
      calc
        finiteMatVec MP x = rectMatMulVec MP x := by
            rfl
        _ = x := hxP_compress_self
        _ = fun i => (1 : ℝ) * x i := by
            ext i
            simp
    have hOne_mem :
        (1 : ℝ) ∈ Set.range (finiteHermitianEigenvalues MP hSymP) :=
      finiteHermitianEigenvalues_mem_range_of_finiteMatVec_eigenvector
        MP hSymP hx_ne hxP_eig
    rcases hOne_mem with ⟨bP, hbP⟩
    have hOne_le : (1 : ℝ) ≤ lambdaP := by
      rw [← hbP]
      exact hTopP' bP
    have hTop_le_one : lambdaP ≤ 1 := by
      simpa [MP, lambdaP] using
        wedinLemma20_12_projectionDiff_sq_compression_finiteHermitianEigenvalues_le_one
          P Q hP hQ hIdemP hIdemQ aP
    simpa [MP, lambdaP] using le_antisymm hTop_le_one hOne_le

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    swapped endpoint characterization for the selected top eigenvalue of
    `Q(P-Q)^2Q`.  Under a top-index certificate, that top value is `1`
    exactly when `ran(Q) ∩ ker(P)` contains a nonzero vector. -/
theorem wedinLemma20_12_top_finiteHermitianEigenvalue_projectionDiff_sq_compression_swapped_eq_one_iff_exists_projection_swapped_range_projection_zero
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    {aQ : Fin m}
    (hTopQ : ∀ a : Fin m,
      finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul Q
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            Q)
          (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
            P Q hP hQ hIdemP hIdemQ) a ≤
        finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul Q
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            Q)
          (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
            P Q hP hQ hIdemP hIdemQ) aQ) :
    finiteHermitianEigenvalues
        (rectMatMul
          (rectMatMul Q
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          Q)
        (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
          P Q hP hQ hIdemP hIdemQ) aQ = 1 ↔
      ∃ x : Fin m → ℝ,
        x ≠ 0 ∧
        rectMatMulVec Q x = x ∧
        rectMatMulVec P x = 0 := by
  let MQ : Fin m → Fin m → ℝ :=
    rectMatMul
      (rectMatMul Q
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)))
      Q
  have hSymQ : IsSymmetricFiniteMatrix MQ := by
    simpa [MQ] using
      wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
        P Q hP hQ hIdemP hIdemQ
  let lambdaQ : ℝ := finiteHermitianEigenvalues MQ hSymQ aQ
  have hTopQ' :
      ∀ a : Fin m, finiteHermitianEigenvalues MQ hSymQ a ≤ lambdaQ := by
    intro a
    simpa [MQ, lambdaQ] using hTopQ a
  constructor
  · intro hTop_eq_one
    have hLambda_eq_one : lambdaQ = 1 := by
      simpa [MQ, lambdaQ] using hTop_eq_one
    let xQ : Fin m → ℝ :=
      ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian MQ hSymQ).eigenvectorBasis aQ)
    have hxQ_ne : xQ ≠ 0 := by
      intro hx0
      have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one MQ hSymQ aQ
      change finiteVecNorm2Sq xQ = 1 at hnorm
      rw [hx0] at hnorm
      simp [finiteVecNorm2Sq] at hnorm
    have hxQ_eig :
        rectMatMulVec MQ xQ = fun i => lambdaQ * xQ i := by
      have h := finiteMatVec_finiteHermitianEigenvector_eq MQ hSymQ aQ
      simpa [finiteMatVec, rectMatMulVec, MQ, xQ, lambdaQ] using h
    have hLambda_ne_zero : lambdaQ ≠ 0 := by
      simp [hLambda_eq_one]
    have hxQ_range :
        rectMatMulVec Q xQ = xQ :=
      wedinLemma20_12_projection_swapped_range_of_projectionDiff_sq_compression_eigenvalue_ne_zero
        P Q hIdemQ lambdaQ xQ
        (by simpa [MQ] using hxQ_eig) hLambda_ne_zero
    have hxQ_compress_self : rectMatMulVec MQ xQ = xQ := by
      calc
        rectMatMulVec MQ xQ = fun i => lambdaQ * xQ i := hxQ_eig
        _ = xQ := by
              ext i
              simp [hLambda_eq_one]
    have hxP_zero : rectMatMulVec P xQ = 0 :=
      (wedinLemma20_12_projection_swapped_range_projectionDiff_sq_compression_eq_self_iff_projection_zero
        P Q hP hQ hIdemP hIdemQ xQ hxQ_range).mp
        (by simpa [MQ] using hxQ_compress_self)
    exact ⟨xQ, hxQ_ne, hxQ_range, hxP_zero⟩
  · rintro ⟨x, hx_ne, hxQ_range, hxP_zero⟩
    have hxQ_compress_self :
        rectMatMulVec MQ x = x := by
      simpa [MQ] using
        (wedinLemma20_12_projection_swapped_range_projectionDiff_sq_compression_eq_self_iff_projection_zero
          P Q hP hQ hIdemP hIdemQ x hxQ_range).mpr hxP_zero
    have hxQ_eig :
        finiteMatVec MQ x = fun i => (1 : ℝ) * x i := by
      calc
        finiteMatVec MQ x = rectMatMulVec MQ x := by
            rfl
        _ = x := hxQ_compress_self
        _ = fun i => (1 : ℝ) * x i := by
            ext i
            simp
    have hOne_mem :
        (1 : ℝ) ∈ Set.range (finiteHermitianEigenvalues MQ hSymQ) :=
      finiteHermitianEigenvalues_mem_range_of_finiteMatVec_eigenvector
        MQ hSymQ hx_ne hxQ_eig
    rcases hOne_mem with ⟨bQ, hbQ⟩
    have hOne_le : (1 : ℝ) ≤ lambdaQ := by
      rw [← hbQ]
      exact hTopQ' bQ
    have hTop_le_one : lambdaQ ≤ 1 := by
      simpa [MQ, lambdaQ] using
        wedinLemma20_12_projectionDiff_sq_compression_swapped_finiteHermitianEigenvalues_le_one
          P Q hP hQ hIdemP hIdemQ aQ
    simpa [MQ, lambdaQ] using le_antisymm hTop_le_one hOne_le

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    source range-finrank bridge for a range projection.  If `Aplus*A = I`,
    then the range of the square projection `A*Aplus` has finite dimension
    equal to the column dimension of `A`.

This connects the source full-column/left-inverse hypotheses to the equal
projection-range dimension needed by the endpoint rank-nullity route. -/
theorem wedinLemma20_12_rangeProjection_range_finrank_eq_width_of_left_inverse
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ)
    (hleft : rectMatMul Aplus A = idMatrix n) :
    Module.finrank ℝ
        (LinearMap.range
          ((Matrix.of (rectMatMul A Aplus) : Matrix (Fin m) (Fin m) ℝ).mulVecLin)) = n := by
  let AM : Matrix (Fin m) (Fin n) ℝ := Matrix.of A
  let AplusM : Matrix (Fin n) (Fin m) ℝ := Matrix.of Aplus
  let PM : Matrix (Fin m) (Fin m) ℝ := Matrix.of (rectMatMul A Aplus)
  let TA : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ) := AM.mulVecLin
  let TAplus : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ) := AplusM.mulVecLin
  let TP : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) := PM.mulVecLin
  have hTA_rect (x : Fin n → ℝ) : TA x = rectMatMulVec A x := by
    ext i
    simp [TA, AM, Matrix.mulVec, dotProduct, rectMatMulVec]
  have hTAplus_rect (x : Fin m → ℝ) : TAplus x = rectMatMulVec Aplus x := by
    ext i
    simp [TAplus, AplusM, Matrix.mulVec, dotProduct, rectMatMulVec]
  have hTP_rect (x : Fin m → ℝ) :
      TP x = rectMatMulVec (rectMatMul A Aplus) x := by
    ext i
    simp [TP, PM, Matrix.mulVec, dotProduct, rectMatMulVec, rectMatMul]
  have hRange : LinearMap.range TP = LinearMap.range TA := by
    apply le_antisymm
    · intro y hy
      rcases hy with ⟨x, rfl⟩
      refine ⟨TAplus x, ?_⟩
      ext i
      rw [hTA_rect, hTAplus_rect, hTP_rect]
      exact congrFun (rectMatMulVec_rectMatMul A Aplus x).symm i
    · intro y hy
      rcases hy with ⟨z, rfl⟩
      refine ⟨TA z, ?_⟩
      rw [hTP_rect, hTA_rect]
      exact rectMatMulVec_rangeProjection_apply_range_of_left_inverse A Aplus hleft z
  have hleft_apply (z : Fin n → ℝ) : TAplus (TA z) = z := by
    ext i
    rw [hTA_rect, hTAplus_rect]
    calc
      rectMatMulVec Aplus (rectMatMulVec A z) i =
          rectMatMulVec (rectMatMul Aplus A) z i := by
            exact congrFun (rectMatMulVec_rectMatMul Aplus A z).symm i
      _ = rectMatMulVec (idMatrix n) z i := by rw [hleft]
      _ = z i := by
            simpa [rectMatMulVec] using congrFun (rectMatMulVec_idMatrix z) i
  have hTA_inj : Function.Injective TA := by
    intro x y hxy
    have hxy' := congrArg TAplus hxy
    rw [hleft_apply x, hleft_apply y] at hxy'
    exact hxy'
  calc
    Module.finrank ℝ (LinearMap.range TP) =
        Module.finrank ℝ (LinearMap.range TA) := by rw [hRange]
    _ = Module.finrank ℝ (Fin n → ℝ) :=
        LinearMap.finrank_range_of_inj hTA_inj
    _ = n := by simp

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    two source range projections with left inverses and the same column
    dimension have equal projection-range finrank. -/
theorem wedinLemma20_12_rangeProjection_range_finrank_eq_of_left_inverses
    {m n : ℕ} (A B : Fin m → Fin n → ℝ)
    (Aplus Bplus : Fin n → Fin m → ℝ)
    (hleftA : rectMatMul Aplus A = idMatrix n)
    (hleftB : rectMatMul Bplus B = idMatrix n) :
    Module.finrank ℝ
        (LinearMap.range
          ((Matrix.of (rectMatMul A Aplus) : Matrix (Fin m) (Fin m) ℝ).mulVecLin)) =
      Module.finrank ℝ
        (LinearMap.range
          ((Matrix.of (rectMatMul B Bplus) : Matrix (Fin m) (Fin m) ℝ).mulVecLin)) := by
  rw [wedinLemma20_12_rangeProjection_range_finrank_eq_width_of_left_inverse
        A Aplus hleftA,
      wedinLemma20_12_rangeProjection_range_finrank_eq_width_of_left_inverse
        B Bplus hleftB]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    finite-dimensional endpoint-rank bridge for equal-rank symmetric
    projections.  If the ranges of `P` and `Q` have the same dimension, then
    the kernels of the restricted maps `Q : ran(P) -> ℝ^m` and
    `P : ran(Q) -> ℝ^m` have the same dimension.

This is the rank-nullity half of the `lambda = 1` principal-angle endpoint:
it compares the dimensions of `ran(P) ∩ ker(Q)` and `ran(Q) ∩ ker(P)` once
those intersections are represented as restricted-map kernels. -/
theorem wedinLemma20_12_projection_range_kernel_finrank_eq_of_range_finrank_eq
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hRangeFinrank :
      Module.finrank ℝ
          (LinearMap.range ((Matrix.of P : Matrix (Fin m) (Fin m) ℝ).mulVecLin)) =
        Module.finrank ℝ
          (LinearMap.range ((Matrix.of Q : Matrix (Fin m) (Fin m) ℝ).mulVecLin))) :
    Module.finrank ℝ
        (LinearMap.ker
          (((Matrix.of Q : Matrix (Fin m) (Fin m) ℝ).mulVecLin).comp
            ((LinearMap.range
              ((Matrix.of P : Matrix (Fin m) (Fin m) ℝ).mulVecLin)).subtype))) =
      Module.finrank ℝ
        (LinearMap.ker
          (((Matrix.of P : Matrix (Fin m) (Fin m) ℝ).mulVecLin).comp
            ((LinearMap.range
              ((Matrix.of Q : Matrix (Fin m) (Fin m) ℝ).mulVecLin)).subtype))) := by
  let PM : Matrix (Fin m) (Fin m) ℝ := Matrix.of P
  let QM : Matrix (Fin m) (Fin m) ℝ := Matrix.of Q
  let TP : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) := PM.mulVecLin
  let TQ : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) := QM.mulVecLin
  let UP : Submodule ℝ (Fin m → ℝ) := LinearMap.range TP
  let UQ : Submodule ℝ (Fin m → ℝ) := LinearMap.range TQ
  let qOnP : UP →ₗ[ℝ] (Fin m → ℝ) := TQ.comp UP.subtype
  let pOnQ : UQ →ₗ[ℝ] (Fin m → ℝ) := TP.comp UQ.subtype
  have hRangeFinrank' : Module.finrank ℝ UP = Module.finrank ℝ UQ := by
    simpa [PM, QM, TP, TQ, UP, UQ] using hRangeFinrank
  have hq_range : LinearMap.range qOnP = LinearMap.range (TQ.comp TP) := by
    simp [qOnP, UP, LinearMap.range_comp, Submodule.range_subtype]
  have hp_range : LinearMap.range pOnQ = LinearMap.range (TP.comp TQ) := by
    simp [pOnQ, UQ, LinearMap.range_comp, Submodule.range_subtype]
  have hPM_transpose : PM.transpose = PM := by
    ext i j
    simp [PM, Matrix.transpose_apply, hP j i]
  have hQM_transpose : QM.transpose = QM := by
    ext i j
    simp [QM, Matrix.transpose_apply, hQ j i]
  have htranspose_QP : (QM * PM).transpose = PM * QM := by
    rw [Matrix.transpose_mul, hPM_transpose, hQM_transpose]
  have hmat_rank : (QM * PM).rank = (PM * QM).rank := by
    calc
      (QM * PM).rank = (QM * PM).transpose.rank := (Matrix.rank_transpose (QM * PM)).symm
      _ = (PM * QM).rank := by rw [htranspose_QP]
  have hq_rank : Module.finrank ℝ (LinearMap.range qOnP) = (QM * PM).rank := by
    calc
      Module.finrank ℝ (LinearMap.range qOnP) =
          Module.finrank ℝ (LinearMap.range (TQ.comp TP)) := by
            rw [hq_range]
      _ = (QM * PM).rank := by
            have hmul := congrArg
              (fun f : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) =>
                Module.finrank ℝ (LinearMap.range f))
              (Matrix.mulVecLin_mul QM PM)
            simpa [Matrix.rank, PM, QM, TP, TQ] using hmul.symm
  have hp_rank : Module.finrank ℝ (LinearMap.range pOnQ) = (PM * QM).rank := by
    calc
      Module.finrank ℝ (LinearMap.range pOnQ) =
          Module.finrank ℝ (LinearMap.range (TP.comp TQ)) := by
            rw [hp_range]
      _ = (PM * QM).rank := by
            have hmul := congrArg
              (fun f : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) =>
                Module.finrank ℝ (LinearMap.range f))
              (Matrix.mulVecLin_mul PM QM)
            simpa [Matrix.rank, PM, QM, TP, TQ] using hmul.symm
  have hRankRanges :
      Module.finrank ℝ (LinearMap.range qOnP) =
        Module.finrank ℝ (LinearMap.range pOnQ) := by
    rw [hq_rank, hp_rank, hmat_rank]
  have hRNq :
      Module.finrank ℝ (LinearMap.range qOnP) +
          Module.finrank ℝ (LinearMap.ker qOnP) =
        Module.finrank ℝ UP :=
    LinearMap.finrank_range_add_finrank_ker qOnP
  have hRNp :
      Module.finrank ℝ (LinearMap.range pOnQ) +
          Module.finrank ℝ (LinearMap.ker pOnQ) =
        Module.finrank ℝ UQ :=
    LinearMap.finrank_range_add_finrank_ker pOnQ
  have hker_eq :
      Module.finrank ℝ (LinearMap.ker qOnP) =
        Module.finrank ℝ (LinearMap.ker pOnQ) := by
    omega
  simpa [PM, QM, TP, TQ, UP, UQ, qOnP, pOnQ] using hker_eq

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    a nonzero vector in `ran(P) ∩ ker(Q)` is the same data as a nonzero
    element of the restricted kernel `ker(Q|ran(P))`.

This is a reusable endpoint-subspace wrapper.  It only needs idempotence of
the first projection to identify `ran(P)` with the fixed-point equation
`P*x = x`. -/
theorem wedinLemma20_12_exists_projection_range_projection_swapped_zero_iff_restricted_kernel_ne_bot
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P) :
    (∃ x : Fin m → ℝ,
        x ≠ 0 ∧ rectMatMulVec P x = x ∧ rectMatMulVec Q x = 0) ↔
      LinearMap.ker
          (((Matrix.of Q : Matrix (Fin m) (Fin m) ℝ).mulVecLin).comp
            ((LinearMap.range
              ((Matrix.of P : Matrix (Fin m) (Fin m) ℝ).mulVecLin)).subtype)) ≠ ⊥ := by
  let PM : Matrix (Fin m) (Fin m) ℝ := Matrix.of P
  let QM : Matrix (Fin m) (Fin m) ℝ := Matrix.of Q
  let TP : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) := PM.mulVecLin
  let TQ : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) := QM.mulVecLin
  let UP : Submodule ℝ (Fin m → ℝ) := LinearMap.range TP
  let qOnP : UP →ₗ[ℝ] (Fin m → ℝ) := TQ.comp UP.subtype
  have hTP_rect (x : Fin m → ℝ) : TP x = rectMatMulVec P x := by
    ext i
    simp [TP, PM, Matrix.mulVec, dotProduct, rectMatMulVec]
  have hTQ_rect (x : Fin m → ℝ) : TQ x = rectMatMulVec Q x := by
    ext i
    simp [TQ, QM, Matrix.mulVec, dotProduct, rectMatMulVec]
  constructor
  · rintro ⟨x, hx_ne, hxP, hxQ⟩
    let u : UP := ⟨x, by
      rw [LinearMap.mem_range]
      exact ⟨x, by rw [hTP_rect, hxP]⟩⟩
    have hu_mem : u ∈ LinearMap.ker qOnP := by
      rw [LinearMap.mem_ker]
      change TQ x = 0
      rw [hTQ_rect, hxQ]
    have hu_ne : u ≠ 0 := by
      intro hu
      apply hx_ne
      simpa [u] using congrArg (fun y : UP => (y : Fin m → ℝ)) hu
    have hne : LinearMap.ker qOnP ≠ ⊥ :=
      (Submodule.ne_bot_iff (LinearMap.ker qOnP)).mpr ⟨u, hu_mem, hu_ne⟩
    simpa [PM, QM, TP, TQ, UP, qOnP] using hne
  · intro hne_raw
    have hne : LinearMap.ker qOnP ≠ ⊥ := by
      simpa [PM, QM, TP, TQ, UP, qOnP] using hne_raw
    rcases (Submodule.ne_bot_iff (LinearMap.ker qOnP)).mp hne with ⟨u, hu_mem, hu_ne⟩
    let x : Fin m → ℝ := u
    have hx_ne : x ≠ 0 := by
      intro hx
      apply hu_ne
      apply Subtype.ext
      exact hx
    have hxQ : rectMatMulVec Q x = 0 := by
      have hker : qOnP u = 0 := by
        simpa [LinearMap.mem_ker] using hu_mem
      change TQ x = 0 at hker
      rw [hTQ_rect] at hker
      exact hker
    have hxP : rectMatMulVec P x = x := by
      rcases u.property with ⟨z, hz⟩
      have hz_rect : rectMatMulVec P z = x := by
        change TP z = x at hz
        rw [hTP_rect] at hz
        exact hz
      calc
        rectMatMulVec P x = rectMatMulVec P (rectMatMulVec P z) := by rw [hz_rect]
        _ = rectMatMulVec (rectMatMul P P) z := by
              rw [rectMatMulVec_rectMatMul]
        _ = rectMatMulVec P z := by rw [hIdemP]
        _ = x := hz_rect
    exact ⟨x, hx_ne, hxP, hxQ⟩

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    endpoint nonzero-transfer under equal projection range dimensions.
    For symmetric idempotent projections with equal range dimension,
    `ran(P) ∩ ker(Q)` contains a nonzero vector iff
    `ran(Q) ∩ ker(P)` contains a nonzero vector.

Together with the selected-top endpoint characterizations, this packages the
finite-dimensional `lambda = 1` exceptional case into a source-facing transfer
between the two projection ranges. -/
theorem wedinLemma20_12_exists_projection_range_projection_swapped_zero_iff_exists_projection_swapped_range_projection_zero_of_range_finrank_eq
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (hRangeFinrank :
      Module.finrank ℝ
          (LinearMap.range ((Matrix.of P : Matrix (Fin m) (Fin m) ℝ).mulVecLin)) =
        Module.finrank ℝ
          (LinearMap.range ((Matrix.of Q : Matrix (Fin m) (Fin m) ℝ).mulVecLin))) :
    (∃ x : Fin m → ℝ,
        x ≠ 0 ∧ rectMatMulVec P x = x ∧ rectMatMulVec Q x = 0) ↔
      ∃ x : Fin m → ℝ,
        x ≠ 0 ∧ rectMatMulVec Q x = x ∧ rectMatMulVec P x = 0 := by
  let PM : Matrix (Fin m) (Fin m) ℝ := Matrix.of P
  let QM : Matrix (Fin m) (Fin m) ℝ := Matrix.of Q
  let TP : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) := PM.mulVecLin
  let TQ : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) := QM.mulVecLin
  let UP : Submodule ℝ (Fin m → ℝ) := LinearMap.range TP
  let UQ : Submodule ℝ (Fin m → ℝ) := LinearMap.range TQ
  let KP : Submodule ℝ UP := LinearMap.ker (TQ.comp UP.subtype)
  let KQ : Submodule ℝ UQ := LinearMap.ker (TP.comp UQ.subtype)
  have hKernelFinrank : Module.finrank ℝ KP = Module.finrank ℝ KQ := by
    simpa [PM, QM, TP, TQ, UP, UQ, KP, KQ] using
      wedinLemma20_12_projection_range_kernel_finrank_eq_of_range_finrank_eq
        P Q hP hQ hRangeFinrank
  have hKernelNontrivial : KP ≠ ⊥ ↔ KQ ≠ ⊥ := by
    constructor
    · intro hKP
      have hKP_fin_ne : Module.finrank ℝ KP ≠ 0 := by
        intro hzero
        exact hKP ((Submodule.finrank_eq_zero (R := ℝ)).mp hzero)
      have hKQ_fin_ne : Module.finrank ℝ KQ ≠ 0 := by
        intro hzero
        apply hKP_fin_ne
        rw [hKernelFinrank]
        exact hzero
      intro hKQ_bot
      exact hKQ_fin_ne ((Submodule.finrank_eq_zero (R := ℝ)).mpr hKQ_bot)
    · intro hKQ
      have hKQ_fin_ne : Module.finrank ℝ KQ ≠ 0 := by
        intro hzero
        exact hKQ ((Submodule.finrank_eq_zero (R := ℝ)).mp hzero)
      have hKP_fin_ne : Module.finrank ℝ KP ≠ 0 := by
        intro hzero
        apply hKQ_fin_ne
        rw [← hKernelFinrank]
        exact hzero
      intro hKP_bot
      exact hKP_fin_ne ((Submodule.finrank_eq_zero (R := ℝ)).mpr hKP_bot)
  constructor
  · intro hleft
    have hKP_nontriv : KP ≠ ⊥ := by
      have hraw :=
        (wedinLemma20_12_exists_projection_range_projection_swapped_zero_iff_restricted_kernel_ne_bot
          P Q hIdemP).mp hleft
      simpa [PM, QM, TP, TQ, UP, KP] using hraw
    have hKQ_nontriv : KQ ≠ ⊥ := hKernelNontrivial.mp hKP_nontriv
    have hraw :
        LinearMap.ker
          (((Matrix.of P : Matrix (Fin m) (Fin m) ℝ).mulVecLin).comp
            ((LinearMap.range
              ((Matrix.of Q : Matrix (Fin m) (Fin m) ℝ).mulVecLin)).subtype)) ≠ ⊥ := by
      simpa [PM, QM, TP, TQ, UQ, KQ] using hKQ_nontriv
    exact
      (wedinLemma20_12_exists_projection_range_projection_swapped_zero_iff_restricted_kernel_ne_bot
        Q P hIdemQ).mpr hraw
  · intro hright
    have hKQ_nontriv : KQ ≠ ⊥ := by
      have hraw :=
        (wedinLemma20_12_exists_projection_range_projection_swapped_zero_iff_restricted_kernel_ne_bot
          Q P hIdemQ).mp hright
      simpa [PM, QM, TP, TQ, UQ, KQ] using hraw
    have hKP_nontriv : KP ≠ ⊥ := hKernelNontrivial.mpr hKQ_nontriv
    have hraw :
        LinearMap.ker
          (((Matrix.of Q : Matrix (Fin m) (Fin m) ℝ).mulVecLin).comp
            ((LinearMap.range
              ((Matrix.of P : Matrix (Fin m) (Fin m) ℝ).mulVecLin)).subtype)) ≠ ⊥ := by
      simpa [PM, QM, TP, TQ, UP, KP] using hKP_nontriv
    exact
      (wedinLemma20_12_exists_projection_range_projection_swapped_zero_iff_restricted_kernel_ne_bot
        P Q hIdemP).mpr hraw

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    endpoint selected-top transfer for the `lambda = 1` case.  Under equal
    projection range dimension, the selected top eigenvalue of `P(P-Q)^2P` is
    `1` iff the selected top eigenvalue of `Q(P-Q)^2Q` is `1`.

This combines the endpoint range/kernel characterizations with the
rank-nullity nonzero-transfer bridge. -/
theorem wedinLemma20_12_top_finiteHermitianEigenvalue_projectionDiff_sq_compression_eq_one_iff_swapped_eq_one_of_range_finrank_eq
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    {aP aQ : Fin m}
    (hTopP : ∀ a : Fin m,
      finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul P
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            P)
          (wedinLemma20_12_projectionDiff_sq_compression_symmetric
            P Q hP hQ hIdemP hIdemQ) a ≤
        finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul P
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            P)
          (wedinLemma20_12_projectionDiff_sq_compression_symmetric
            P Q hP hQ hIdemP hIdemQ) aP)
    (hTopQ : ∀ a : Fin m,
      finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul Q
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            Q)
          (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
            P Q hP hQ hIdemP hIdemQ) a ≤
        finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul Q
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            Q)
          (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
            P Q hP hQ hIdemP hIdemQ) aQ)
    (hRangeFinrank :
      Module.finrank ℝ
          (LinearMap.range ((Matrix.of P : Matrix (Fin m) (Fin m) ℝ).mulVecLin)) =
        Module.finrank ℝ
          (LinearMap.range ((Matrix.of Q : Matrix (Fin m) (Fin m) ℝ).mulVecLin))) :
    finiteHermitianEigenvalues
        (rectMatMul
          (rectMatMul P
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          P)
        (wedinLemma20_12_projectionDiff_sq_compression_symmetric
          P Q hP hQ hIdemP hIdemQ) aP = 1 ↔
      finiteHermitianEigenvalues
        (rectMatMul
          (rectMatMul Q
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          Q)
        (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
          P Q hP hQ hIdemP hIdemQ) aQ = 1 := by
  have hEndpointP :=
    wedinLemma20_12_top_finiteHermitianEigenvalue_projectionDiff_sq_compression_eq_one_iff_exists_projection_range_projection_swapped_zero
      P Q hP hQ hIdemP hIdemQ hTopP
  have hEndpointQ :=
    wedinLemma20_12_top_finiteHermitianEigenvalue_projectionDiff_sq_compression_swapped_eq_one_iff_exists_projection_swapped_range_projection_zero
      P Q hP hQ hIdemP hIdemQ hTopQ
  have hTransfer :=
    wedinLemma20_12_exists_projection_range_projection_swapped_zero_iff_exists_projection_swapped_range_projection_zero_of_range_finrank_eq
      P Q hP hQ hIdemP hIdemQ hRangeFinrank
  constructor
  · intro hP_one
    exact hEndpointQ.mpr (hTransfer.mp (hEndpointP.mp hP_one))
  · intro hQ_one
    exact hEndpointP.mpr (hTransfer.mpr (hEndpointQ.mp hQ_one))

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    source range-projection endpoint transfer for the `lambda = 1` case.
    For the projections `A*Aplus` and `B*Bplus`, the equal range-dimension
    hypothesis required by the abstract endpoint theorem follows from the two
    left inverses `Aplus*A = I` and `Bplus*B = I`. -/
theorem wedinLemma20_12_top_finiteHermitianEigenvalue_rangeProjection_projectionDiff_sq_compression_eq_one_iff_swapped_eq_one
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    {aA aB : Fin m}
    (hTopA : ∀ a : Fin m,
      finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul (rectMatMul A Aplus)
              (rectMatMul
                (fun i j => rectMatMul A Aplus i j - rectMatMul B Bplus i j)
                (fun i j => rectMatMul A Aplus i j - rectMatMul B Bplus i j)))
            (rectMatMul A Aplus))
          (wedinLemma20_12_projectionDiff_sq_compression_symmetric
            (rectMatMul A Aplus) (rectMatMul B Bplus) hSymA hSymB
            (rectMatMul_rangeProjection_idempotent_of_left_inverse A Aplus hleftA)
            (rectMatMul_rangeProjection_idempotent_of_left_inverse B Bplus hleftB)) a ≤
        finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul (rectMatMul A Aplus)
              (rectMatMul
                (fun i j => rectMatMul A Aplus i j - rectMatMul B Bplus i j)
                (fun i j => rectMatMul A Aplus i j - rectMatMul B Bplus i j)))
            (rectMatMul A Aplus))
          (wedinLemma20_12_projectionDiff_sq_compression_symmetric
            (rectMatMul A Aplus) (rectMatMul B Bplus) hSymA hSymB
            (rectMatMul_rangeProjection_idempotent_of_left_inverse A Aplus hleftA)
            (rectMatMul_rangeProjection_idempotent_of_left_inverse B Bplus hleftB)) aA)
    (hTopB : ∀ a : Fin m,
      finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul (rectMatMul B Bplus)
              (rectMatMul
                (fun i j => rectMatMul A Aplus i j - rectMatMul B Bplus i j)
                (fun i j => rectMatMul A Aplus i j - rectMatMul B Bplus i j)))
            (rectMatMul B Bplus))
          (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
            (rectMatMul A Aplus) (rectMatMul B Bplus) hSymA hSymB
            (rectMatMul_rangeProjection_idempotent_of_left_inverse A Aplus hleftA)
            (rectMatMul_rangeProjection_idempotent_of_left_inverse B Bplus hleftB)) a ≤
        finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul (rectMatMul B Bplus)
              (rectMatMul
                (fun i j => rectMatMul A Aplus i j - rectMatMul B Bplus i j)
                (fun i j => rectMatMul A Aplus i j - rectMatMul B Bplus i j)))
            (rectMatMul B Bplus))
          (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
            (rectMatMul A Aplus) (rectMatMul B Bplus) hSymA hSymB
            (rectMatMul_rangeProjection_idempotent_of_left_inverse A Aplus hleftA)
            (rectMatMul_rangeProjection_idempotent_of_left_inverse B Bplus hleftB)) aB) :
    finiteHermitianEigenvalues
        (rectMatMul
          (rectMatMul (rectMatMul A Aplus)
            (rectMatMul
              (fun i j => rectMatMul A Aplus i j - rectMatMul B Bplus i j)
              (fun i j => rectMatMul A Aplus i j - rectMatMul B Bplus i j)))
          (rectMatMul A Aplus))
        (wedinLemma20_12_projectionDiff_sq_compression_symmetric
          (rectMatMul A Aplus) (rectMatMul B Bplus) hSymA hSymB
          (rectMatMul_rangeProjection_idempotent_of_left_inverse A Aplus hleftA)
          (rectMatMul_rangeProjection_idempotent_of_left_inverse B Bplus hleftB)) aA = 1 ↔
      finiteHermitianEigenvalues
        (rectMatMul
          (rectMatMul (rectMatMul B Bplus)
            (rectMatMul
              (fun i j => rectMatMul A Aplus i j - rectMatMul B Bplus i j)
              (fun i j => rectMatMul A Aplus i j - rectMatMul B Bplus i j)))
          (rectMatMul B Bplus))
        (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
          (rectMatMul A Aplus) (rectMatMul B Bplus) hSymA hSymB
          (rectMatMul_rangeProjection_idempotent_of_left_inverse A Aplus hleftA)
          (rectMatMul_rangeProjection_idempotent_of_left_inverse B Bplus hleftB)) aB = 1 := by
  let PA : Fin m → Fin m → ℝ := rectMatMul A Aplus
  let PB : Fin m → Fin m → ℝ := rectMatMul B Bplus
  have hIdemA : rectMatMul PA PA = PA := by
    simpa [PA] using
      rectMatMul_rangeProjection_idempotent_of_left_inverse A Aplus hleftA
  have hIdemB : rectMatMul PB PB = PB := by
    simpa [PB] using
      rectMatMul_rangeProjection_idempotent_of_left_inverse B Bplus hleftB
  have hRangeFinrank :
      Module.finrank ℝ
          (LinearMap.range ((Matrix.of PA : Matrix (Fin m) (Fin m) ℝ).mulVecLin)) =
        Module.finrank ℝ
          (LinearMap.range ((Matrix.of PB : Matrix (Fin m) (Fin m) ℝ).mulVecLin)) := by
    simpa [PA, PB] using
      wedinLemma20_12_rangeProjection_range_finrank_eq_of_left_inverses
        A B Aplus Bplus hleftA hleftB
  simpa [PA, PB, hIdemA, hIdemB] using
    wedinLemma20_12_top_finiteHermitianEigenvalue_projectionDiff_sq_compression_eq_one_iff_swapped_eq_one_of_range_finrank_eq
      PA PB (by simpa [PA] using hSymA) (by simpa [PB] using hSymB)
      hIdemA hIdemB hTopA hTopB hRangeFinrank

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    if the selected top Hermitian eigenvalues of the two `D^2` compressions
    are away from the endpoint cases `0` and `1`, then the top eigenvalues
    are equal.

The remaining principal-angle work is therefore concentrated on the endpoint
cases, especially the `lambda = 1` eigenspace multiplicity/rank comparison. -/
theorem wedinLemma20_12_top_finiteHermitianEigenvalue_projectionDiff_sq_compression_eq_swapped_of_top_of_nonzero_nonunit
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    {aP aQ : Fin m}
    (hTopP : ∀ a : Fin m,
      finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul P
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            P)
          (wedinLemma20_12_projectionDiff_sq_compression_symmetric
            P Q hP hQ hIdemP hIdemQ) a ≤
        finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul P
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            P)
          (wedinLemma20_12_projectionDiff_sq_compression_symmetric
            P Q hP hQ hIdemP hIdemQ) aP)
    (hTopQ : ∀ a : Fin m,
      finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul Q
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            Q)
          (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
            P Q hP hQ hIdemP hIdemQ) a ≤
        finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul Q
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            Q)
          (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
            P Q hP hQ hIdemP hIdemQ) aQ)
    (hTopP_ne_zero :
      finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul P
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            P)
          (wedinLemma20_12_projectionDiff_sq_compression_symmetric
            P Q hP hQ hIdemP hIdemQ) aP ≠ 0)
    (hTopP_ne_one :
      finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul P
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            P)
          (wedinLemma20_12_projectionDiff_sq_compression_symmetric
            P Q hP hQ hIdemP hIdemQ) aP ≠ 1)
    (hTopQ_ne_zero :
      finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul Q
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            Q)
          (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
            P Q hP hQ hIdemP hIdemQ) aQ ≠ 0)
    (hTopQ_ne_one :
      finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul Q
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            Q)
          (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
            P Q hP hQ hIdemP hIdemQ) aQ ≠ 1) :
    finiteHermitianEigenvalues
        (rectMatMul
          (rectMatMul P
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          P)
        (wedinLemma20_12_projectionDiff_sq_compression_symmetric
          P Q hP hQ hIdemP hIdemQ) aP =
      finiteHermitianEigenvalues
        (rectMatMul
          (rectMatMul Q
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          Q)
        (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
          P Q hP hQ hIdemP hIdemQ) aQ := by
  let MP : Fin m → Fin m → ℝ :=
    rectMatMul
      (rectMatMul P
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)))
      P
  let MQ : Fin m → Fin m → ℝ :=
    rectMatMul
      (rectMatMul Q
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)))
      Q
  have hSymP : IsSymmetricFiniteMatrix MP := by
    simpa [MP] using
      wedinLemma20_12_projectionDiff_sq_compression_symmetric
        P Q hP hQ hIdemP hIdemQ
  have hSymQ : IsSymmetricFiniteMatrix MQ := by
    simpa [MQ] using
      wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
        P Q hP hQ hIdemP hIdemQ
  let lambdaP : ℝ := finiteHermitianEigenvalues MP hSymP aP
  let lambdaQ : ℝ := finiteHermitianEigenvalues MQ hSymQ aQ
  have hTopP' :
      ∀ a : Fin m, finiteHermitianEigenvalues MP hSymP a ≤ lambdaP := by
    intro a
    simpa [MP, lambdaP] using hTopP a
  have hTopQ' :
      ∀ a : Fin m, finiteHermitianEigenvalues MQ hSymQ a ≤ lambdaQ := by
    intro a
    simpa [MQ, lambdaQ] using hTopQ a
  have hTopP_ne_zero' : lambdaP ≠ 0 := by
    simpa [MP, lambdaP] using hTopP_ne_zero
  have hTopP_ne_one' : lambdaP ≠ 1 := by
    simpa [MP, lambdaP] using hTopP_ne_one
  have hTopQ_ne_zero' : lambdaQ ≠ 0 := by
    simpa [MQ, lambdaQ] using hTopQ_ne_zero
  have hTopQ_ne_one' : lambdaQ ≠ 1 := by
    simpa [MQ, lambdaQ] using hTopQ_ne_one
  let xP : Fin m → ℝ :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian MP hSymP).eigenvectorBasis aP)
  have hxP_ne : xP ≠ 0 := by
    intro hx0
    have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one MP hSymP aP
    change finiteVecNorm2Sq xP = 1 at hnorm
    rw [hx0] at hnorm
    simp [finiteVecNorm2Sq] at hnorm
  have hxP_eig : rectMatMulVec MP xP = fun i => lambdaP * xP i := by
    have h := finiteMatVec_finiteHermitianEigenvector_eq MP hSymP aP
    simpa [finiteMatVec, rectMatMulVec, MP, xP, lambdaP] using h
  obtain ⟨yQ, hyQ_ne, _hyQ_range, hyQ_eig⟩ :=
    wedinLemma20_12_exists_projection_swapped_range_projectionDiff_sq_compression_eigenvector_of_projection_range
      P Q hIdemP hIdemQ lambdaP xP
      (by simpa [MP] using hxP_eig) hxP_ne hTopP_ne_zero' hTopP_ne_one'
  have hyQ_eig_finite :
      finiteMatVec MQ yQ = fun i => lambdaP * yQ i := by
    simpa [finiteMatVec, rectMatMulVec, MQ] using hyQ_eig
  have hRangeQ :
      lambdaP ∈ Set.range (finiteHermitianEigenvalues MQ hSymQ) :=
    finiteHermitianEigenvalues_mem_range_of_finiteMatVec_eigenvector
      MQ hSymQ hyQ_ne hyQ_eig_finite
  rcases hRangeQ with ⟨bQ, hbQ⟩
  have hP_le_Q : lambdaP ≤ lambdaQ := by
    rw [← hbQ]
    exact hTopQ' bQ
  let xQ : Fin m → ℝ :=
    ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian MQ hSymQ).eigenvectorBasis aQ)
  have hxQ_ne : xQ ≠ 0 := by
    intro hx0
    have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one MQ hSymQ aQ
    change finiteVecNorm2Sq xQ = 1 at hnorm
    rw [hx0] at hnorm
    simp [finiteVecNorm2Sq] at hnorm
  have hxQ_eig : rectMatMulVec MQ xQ = fun i => lambdaQ * xQ i := by
    have h := finiteMatVec_finiteHermitianEigenvector_eq MQ hSymQ aQ
    simpa [finiteMatVec, rectMatMulVec, MQ, xQ, lambdaQ] using h
  obtain ⟨yP, hyP_ne, _hyP_range, hyP_eig⟩ :=
    wedinLemma20_12_exists_projection_range_projectionDiff_sq_compression_eigenvector_of_projection_swapped_range
      P Q hIdemP hIdemQ lambdaQ xQ
      (by simpa [MQ] using hxQ_eig) hxQ_ne hTopQ_ne_zero' hTopQ_ne_one'
  have hyP_eig_finite :
      finiteMatVec MP yP = fun i => lambdaQ * yP i := by
    simpa [finiteMatVec, rectMatMulVec, MP] using hyP_eig
  have hRangeP :
      lambdaQ ∈ Set.range (finiteHermitianEigenvalues MP hSymP) :=
    finiteHermitianEigenvalues_mem_range_of_finiteMatVec_eigenvector
      MP hSymP hyP_ne hyP_eig_finite
  rcases hRangeP with ⟨bP, hbP⟩
  have hQ_le_P : lambdaQ ≤ lambdaP := by
    rw [← hbP]
    exact hTopP' bP
  simpa [MP, MQ, lambdaP, lambdaQ] using le_antisymm hP_le_Q hQ_le_P

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    unconditional selected-top equality for the two `D^2` projection
    compressions under equal projection-range dimension.

The proof splits the selected top value into the three spectral cases allowed
by `0 <= lambda <= 1`: zero is handled by nonnegativity, one by the endpoint
range/kernel transfer, and the open interval by the compressed eigenvector
transfer to the opposite range. -/
theorem wedinLemma20_12_top_finiteHermitianEigenvalue_projectionDiff_sq_compression_eq_swapped_of_top_of_range_finrank_eq
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    {aP aQ : Fin m}
    (hTopP : ∀ a : Fin m,
      finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul P
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            P)
          (wedinLemma20_12_projectionDiff_sq_compression_symmetric
            P Q hP hQ hIdemP hIdemQ) a ≤
        finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul P
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            P)
          (wedinLemma20_12_projectionDiff_sq_compression_symmetric
            P Q hP hQ hIdemP hIdemQ) aP)
    (hTopQ : ∀ a : Fin m,
      finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul Q
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            Q)
          (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
            P Q hP hQ hIdemP hIdemQ) a ≤
        finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul Q
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            Q)
          (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
            P Q hP hQ hIdemP hIdemQ) aQ)
    (hRangeFinrank :
      Module.finrank ℝ
          (LinearMap.range ((Matrix.of P : Matrix (Fin m) (Fin m) ℝ).mulVecLin)) =
        Module.finrank ℝ
          (LinearMap.range ((Matrix.of Q : Matrix (Fin m) (Fin m) ℝ).mulVecLin))) :
    finiteHermitianEigenvalues
        (rectMatMul
          (rectMatMul P
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          P)
        (wedinLemma20_12_projectionDiff_sq_compression_symmetric
          P Q hP hQ hIdemP hIdemQ) aP =
      finiteHermitianEigenvalues
        (rectMatMul
          (rectMatMul Q
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          Q)
        (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
          P Q hP hQ hIdemP hIdemQ) aQ := by
  let MP : Fin m → Fin m → ℝ :=
    rectMatMul
      (rectMatMul P
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)))
      P
  let MQ : Fin m → Fin m → ℝ :=
    rectMatMul
      (rectMatMul Q
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)))
      Q
  have hSymP : IsSymmetricFiniteMatrix MP := by
    simpa [MP] using
      wedinLemma20_12_projectionDiff_sq_compression_symmetric
        P Q hP hQ hIdemP hIdemQ
  have hSymQ : IsSymmetricFiniteMatrix MQ := by
    simpa [MQ] using
      wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
        P Q hP hQ hIdemP hIdemQ
  let lambdaP : ℝ := finiteHermitianEigenvalues MP hSymP aP
  let lambdaQ : ℝ := finiteHermitianEigenvalues MQ hSymQ aQ
  have hTopP' :
      ∀ a : Fin m, finiteHermitianEigenvalues MP hSymP a ≤ lambdaP := by
    intro a
    simpa [MP, lambdaP] using hTopP a
  have hTopQ' :
      ∀ a : Fin m, finiteHermitianEigenvalues MQ hSymQ a ≤ lambdaQ := by
    intro a
    simpa [MQ, lambdaQ] using hTopQ a
  have hEndpoint :
      lambdaP = 1 ↔ lambdaQ = 1 := by
    simpa [MP, MQ, lambdaP, lambdaQ] using
      wedinLemma20_12_top_finiteHermitianEigenvalue_projectionDiff_sq_compression_eq_one_iff_swapped_eq_one_of_range_finrank_eq
        P Q hP hQ hIdemP hIdemQ hTopP hTopQ hRangeFinrank
  have hQ_nonneg : 0 ≤ lambdaQ := by
    simpa [MQ, lambdaQ] using
      wedinLemma20_12_projectionDiff_sq_compression_swapped_finiteHermitianEigenvalues_nonneg
        P Q hP hQ hIdemP hIdemQ aQ
  have hP_nonneg : 0 ≤ lambdaP := by
    simpa [MP, lambdaP] using
      wedinLemma20_12_projectionDiff_sq_compression_finiteHermitianEigenvalues_nonneg
        P Q hP hQ hIdemP hIdemQ aP
  have hP_le_Q : lambdaP ≤ lambdaQ := by
    by_cases hP_zero : lambdaP = 0
    · simpa [hP_zero] using hQ_nonneg
    · by_cases hP_one : lambdaP = 1
      · have hQ_one : lambdaQ = 1 := hEndpoint.mp hP_one
        rw [hP_one, hQ_one]
      · let xP : Fin m → ℝ :=
          ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian MP hSymP).eigenvectorBasis aP)
        have hxP_ne : xP ≠ 0 := by
          intro hx0
          have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one MP hSymP aP
          change finiteVecNorm2Sq xP = 1 at hnorm
          rw [hx0] at hnorm
          simp [finiteVecNorm2Sq] at hnorm
        have hxP_eig : rectMatMulVec MP xP = fun i => lambdaP * xP i := by
          have h := finiteMatVec_finiteHermitianEigenvector_eq MP hSymP aP
          simpa [finiteMatVec, rectMatMulVec, MP, xP, lambdaP] using h
        obtain ⟨yQ, hyQ_ne, _hyQ_range, hyQ_eig⟩ :=
          wedinLemma20_12_exists_projection_swapped_range_projectionDiff_sq_compression_eigenvector_of_projection_range
            P Q hIdemP hIdemQ lambdaP xP
            (by simpa [MP] using hxP_eig) hxP_ne hP_zero hP_one
        have hyQ_eig_finite :
            finiteMatVec MQ yQ = fun i => lambdaP * yQ i := by
          simpa [finiteMatVec, rectMatMulVec, MQ] using hyQ_eig
        have hRangeQ :
            lambdaP ∈ Set.range (finiteHermitianEigenvalues MQ hSymQ) :=
          finiteHermitianEigenvalues_mem_range_of_finiteMatVec_eigenvector
            MQ hSymQ hyQ_ne hyQ_eig_finite
        rcases hRangeQ with ⟨bQ, hbQ⟩
        rw [← hbQ]
        exact hTopQ' bQ
  have hQ_le_P : lambdaQ ≤ lambdaP := by
    by_cases hQ_zero : lambdaQ = 0
    · simpa [hQ_zero] using hP_nonneg
    · by_cases hQ_one : lambdaQ = 1
      · have hP_one : lambdaP = 1 := hEndpoint.mpr hQ_one
        rw [hQ_one, hP_one]
      · let xQ : Fin m → ℝ :=
          ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian MQ hSymQ).eigenvectorBasis aQ)
        have hxQ_ne : xQ ≠ 0 := by
          intro hx0
          have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one MQ hSymQ aQ
          change finiteVecNorm2Sq xQ = 1 at hnorm
          rw [hx0] at hnorm
          simp [finiteVecNorm2Sq] at hnorm
        have hxQ_eig : rectMatMulVec MQ xQ = fun i => lambdaQ * xQ i := by
          have h := finiteMatVec_finiteHermitianEigenvector_eq MQ hSymQ aQ
          simpa [finiteMatVec, rectMatMulVec, MQ, xQ, lambdaQ] using h
        obtain ⟨yP, hyP_ne, _hyP_range, hyP_eig⟩ :=
          wedinLemma20_12_exists_projection_range_projectionDiff_sq_compression_eigenvector_of_projection_swapped_range
            P Q hIdemP hIdemQ lambdaQ xQ
            (by simpa [MQ] using hxQ_eig) hxQ_ne hQ_zero hQ_one
        have hyP_eig_finite :
            finiteMatVec MP yP = fun i => lambdaQ * yP i := by
          simpa [finiteMatVec, rectMatMulVec, MP] using hyP_eig
        have hRangeP :
            lambdaQ ∈ Set.range (finiteHermitianEigenvalues MP hSymP) :=
          finiteHermitianEigenvalues_mem_range_of_finiteMatVec_eigenvector
            MP hSymP hyP_ne hyP_eig_finite
        rcases hRangeP with ⟨bP, hbP⟩
        rw [← hbP]
        exact hTopP' bP
  simpa [MP, MQ, lambdaP, lambdaQ] using le_antisymm hP_le_Q hQ_le_P

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    equality of the exact complexified Euclidean operator norms of the two
    `D^2` projection compressions.

This packages the selected-top eigenvalue equality through the existing PSD
top-eigenvalue/operator-norm wrappers for `P(P-Q)^2P` and `Q(P-Q)^2Q`. -/
theorem wedinLemma20_12_complexMatrixOp2_projectionDiff_sq_compression_eq_swapped_of_range_finrank_eq
    {m : ℕ} (hm : 0 < m) (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (hRangeFinrank :
      Module.finrank ℝ
          (LinearMap.range ((Matrix.of P : Matrix (Fin m) (Fin m) ℝ).mulVecLin)) =
        Module.finrank ℝ
          (LinearMap.range ((Matrix.of Q : Matrix (Fin m) (Fin m) ℝ).mulVecLin))) :
    complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul
            (rectMatMul P
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            P)) =
      complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul
            (rectMatMul Q
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            Q)) := by
  obtain ⟨aP, hOpP, hTopP⟩ :=
    wedinLemma20_12_exists_topEigenvalue_complexMatrixOp2_projectionDiff_sq_compression_eq
      hm P Q hP hQ hIdemP hIdemQ
  obtain ⟨aQ, hOpQ, hTopQ⟩ :=
    wedinLemma20_12_exists_topEigenvalue_complexMatrixOp2_projectionDiff_sq_compression_swapped_eq
      hm P Q hP hQ hIdemP hIdemQ
  have hEigEq :=
    wedinLemma20_12_top_finiteHermitianEigenvalue_projectionDiff_sq_compression_eq_swapped_of_top_of_range_finrank_eq
      P Q hP hQ hIdemP hIdemQ hTopP hTopQ hRangeFinrank
  calc
    complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul
            (rectMatMul P
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            P))
        = finiteHermitianEigenvalues
            (rectMatMul
              (rectMatMul P
                (rectMatMul (fun i j => P i j - Q i j)
                  (fun i j => P i j - Q i j)))
              P)
            (wedinLemma20_12_projectionDiff_sq_compression_symmetric
              P Q hP hQ hIdemP hIdemQ) aP := hOpP
    _ = finiteHermitianEigenvalues
            (rectMatMul
              (rectMatMul Q
                (rectMatMul (fun i j => P i j - Q i j)
                  (fun i j => P i j - Q i j)))
              Q)
            (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
              P Q hP hQ hIdemP hIdemQ) aQ := hEigEq
    _ = complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul
            (rectMatMul Q
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            Q)) := hOpQ.symm

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    equality of the two `D^2` range-compression operator norms implies the
    missing Stewart--Sun cross-projection norm equality.

The remaining principal-angle proof can therefore target the symmetric
compression equality
`||P(P-Q)^2P||_2 = ||Q(P-Q)^2Q||_2`, instead of working directly with
rectangular cross projections. -/
theorem wedinLemma20_12_complexMatrixOp2_crossProjection_eq_of_projectionDiff_sq_compression_eq
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (hEq :
      complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul
              (rectMatMul P
                (rectMatMul (fun i j => P i j - Q i j)
                  (fun i j => P i j - Q i j)))
              P)) =
        complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul
              (rectMatMul Q
                (rectMatMul (fun i j => P i j - Q i j)
                  (fun i j => P i j - Q i j)))
              Q))) :
    complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul P (fun i j => idMatrix m i j - Q i j))) =
      complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul Q (fun i j => idMatrix m i j - P i j))) := by
  let IP : Fin m → Fin m → ℝ := fun i j => idMatrix m i j - P i j
  let IQ : Fin m → Fin m → ℝ := fun i j => idMatrix m i j - Q i j
  let D : Fin m → Fin m → ℝ := fun i j => P i j - Q i j
  have hP_sq :=
    wedinLemma20_12_complexMatrixOp2_projectionDiff_sq_compression_eq_crossProjection_sq
      P Q hP hQ hIdemP hIdemQ
  have hQ_sq :=
    wedinLemma20_12_complexMatrixOp2_projectionDiff_sq_compression_eq_crossProjection_sq_swapped
      P Q hP hQ hIdemP hIdemQ
  have hsquares :
      complexMatrixOp2 (realRectToCMatrix (rectMatMul P IQ)) ^ 2 =
        complexMatrixOp2 (realRectToCMatrix (rectMatMul Q IP)) ^ 2 := by
    calc
      complexMatrixOp2 (realRectToCMatrix (rectMatMul P IQ)) ^ 2
          = complexMatrixOp2
              (realRectToCMatrix (rectMatMul (rectMatMul P (rectMatMul D D)) P)) :=
              hP_sq.symm
      _ = complexMatrixOp2
              (realRectToCMatrix (rectMatMul (rectMatMul Q (rectMatMul D D)) Q)) := by
              simpa [D] using hEq
      _ = complexMatrixOp2 (realRectToCMatrix (rectMatMul Q IP)) ^ 2 := by
              simpa [IP, D] using hQ_sq
  exact (sq_eq_sq₀
    (complexMatrixOp2_nonneg (realRectToCMatrix (rectMatMul P IQ)))
    (complexMatrixOp2_nonneg (realRectToCMatrix (rectMatMul Q IP)))).mp
    hsquares

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12:
    Stewart--Sun cross-projection norm equality for finite symmetric
    idempotent projections with equal projection-range dimension.

This is the abstract principal-angle equality used to remove the conditional
`complexMatrixOp2` hypothesis from the source Lemma 20.12 `min` bound. -/
theorem wedinLemma20_12_complexMatrixOp2_crossProjection_eq_of_range_finrank_eq
    {m : ℕ} (hm : 0 < m) (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (hRangeFinrank :
      Module.finrank ℝ
          (LinearMap.range ((Matrix.of P : Matrix (Fin m) (Fin m) ℝ).mulVecLin)) =
        Module.finrank ℝ
          (LinearMap.range ((Matrix.of Q : Matrix (Fin m) (Fin m) ℝ).mulVecLin))) :
    complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul P (fun i j => idMatrix m i j - Q i j))) =
      complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul Q (fun i j => idMatrix m i j - P i j))) := by
  have hEq :
      complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul
              (rectMatMul P
                (rectMatMul (fun i j => P i j - Q i j)
                  (fun i j => P i j - Q i j)))
              P)) =
        complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul
              (rectMatMul Q
                (rectMatMul (fun i j => P i j - Q i j)
                  (fun i j => P i j - Q i j)))
              Q)) :=
    wedinLemma20_12_complexMatrixOp2_projectionDiff_sq_compression_eq_swapped_of_range_finrank_eq
      hm P Q hP hQ hIdemP hIdemQ hRangeFinrank
  exact
    wedinLemma20_12_complexMatrixOp2_crossProjection_eq_of_projectionDiff_sq_compression_eq
      P Q hP hQ hIdemP hIdemQ hEq

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the difference of two symmetric projections is symmetric. -/
theorem wedinLemma20_12_projectionDiff_symmetric
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q) :
    IsSymmetricFiniteMatrix (fun i j => P i j - Q i j) := by
  intro i j
  dsimp
  rw [hP i j, hQ i j]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the normal-form product `(P-Q)P(P-Q)` is symmetric. -/
theorem wedinLemma20_12_diff_projection_diff_symmetric
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P) :
    IsSymmetricFiniteMatrix
      (rectMatMul
        (rectMatMul (fun i j => P i j - Q i j) P)
        (fun i j => P i j - Q i j)) := by
  have hEq :=
    wedinLemma20_12_compressedGram_eq_diff_projection_diff P Q hIdemP
  rw [← hEq]
  exact wedinLemma20_12_compressedGram_symmetric P Q hP hQ hIdemP

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the normal-form product `(P-Q)P(P-Q)` is positive semidefinite. -/
theorem wedinLemma20_12_diff_projection_diff_finitePSD
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P) :
    finitePSD
      (rectMatMul
        (rectMatMul (fun i j => P i j - Q i j) P)
        (fun i j => P i j - Q i j)) := by
  have hEq :=
    wedinLemma20_12_compressedGram_eq_diff_projection_diff P Q hIdemP
  rw [← hEq]
  exact wedinLemma20_12_compressedGram_finitePSD P Q hP hQ hIdemP

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the swapped compressed Gram product `(I-P)Q(I-P)` can be written in the
    same projector-difference orientation as `(P-Q)Q(P-Q)`. -/
theorem wedinLemma20_12_swapped_compressedGram_eq_diff_projection_diff
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemQ : rectMatMul Q Q = Q) :
    rectMatMul
        (rectMatMul (fun i j => idMatrix m i j - P i j) Q)
        (fun i j => idMatrix m i j - P i j) =
      rectMatMul
        (rectMatMul (fun i j => P i j - Q i j) Q)
        (fun i j => P i j - Q i j) := by
  have hbase :=
    wedinLemma20_12_compressedGram_eq_diff_projection_diff Q P hIdemQ
  rw [hbase]
  ext i j
  unfold rectMatMul
  calc
    (∑ a : Fin m, (∑ b : Fin m, (Q i b - P i b) * Q b a) *
        (Q a j - P a j))
        = ∑ a : Fin m, (-(∑ b : Fin m, (P i b - Q i b) * Q b a)) *
            (-(P a j - Q a j)) := by
            apply Finset.sum_congr rfl
            intro a _
            have hinner :
                (∑ b : Fin m, (Q i b - P i b) * Q b a) =
                  -(∑ b : Fin m, (P i b - Q i b) * Q b a) := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro b _
              ring
            rw [hinner]
            ring
    _ = ∑ a : Fin m, (∑ b : Fin m, (P i b - Q i b) * Q b a) *
          (P a j - Q a j) := by
            apply Finset.sum_congr rfl
            intro a _
            ring

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the difference between the two projector-difference normal forms is the
    cube of the projection difference `D = P-Q`. -/
theorem wedinLemma20_12_diff_projection_diff_sub_swapped_eq_projectionDiff_cube
    {m : ℕ} (P Q : Fin m → Fin m → ℝ) :
    (fun i j =>
      rectMatMul
          (rectMatMul (fun i j => P i j - Q i j) P)
          (fun i j => P i j - Q i j) i j -
        rectMatMul
          (rectMatMul (fun i j => P i j - Q i j) Q)
          (fun i j => P i j - Q i j) i j) =
      rectMatMul
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j))
        (fun i j => P i j - Q i j) := by
  ext i j
  unfold rectMatMul
  calc
    (∑ a : Fin m, (∑ b : Fin m, (P i b - Q i b) * P b a) *
        (P a j - Q a j)) -
      (∑ a : Fin m, (∑ b : Fin m, (P i b - Q i b) * Q b a) *
        (P a j - Q a j))
        = ∑ a : Fin m,
            ((∑ b : Fin m, (P i b - Q i b) * P b a) -
              (∑ b : Fin m, (P i b - Q i b) * Q b a)) *
              (P a j - Q a j) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro a _
            ring
    _ = ∑ a : Fin m,
          (∑ b : Fin m, (P i b - Q i b) * (P b a - Q b a)) *
            (P a j - Q a j) := by
            apply Finset.sum_congr rfl
            intro a _
            have hinner :
                (∑ b : Fin m, (P i b - Q i b) * P b a) -
                  (∑ b : Fin m, (P i b - Q i b) * Q b a) =
                ∑ b : Fin m, (P i b - Q i b) * (P b a - Q b a) := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro b _
              ring
            rw [hinner]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    in original compressed-Gram orientation, the difference of the two
    compressed Gram products is the cube of the projection difference. -/
theorem wedinLemma20_12_compressedGram_sub_swapped_compressedGram_eq_projectionDiff_cube
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    (fun i j =>
      rectMatMul
          (rectMatMul (fun i j => idMatrix m i j - Q i j) P)
          (fun i j => idMatrix m i j - Q i j) i j -
        rectMatMul
          (rectMatMul (fun i j => idMatrix m i j - P i j) Q)
          (fun i j => idMatrix m i j - P i j) i j) =
      rectMatMul
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j))
        (fun i j => P i j - Q i j) := by
  have hP :=
    wedinLemma20_12_compressedGram_eq_diff_projection_diff P Q hIdemP
  have hQ :=
    wedinLemma20_12_swapped_compressedGram_eq_diff_projection_diff P Q hIdemQ
  rw [hP, hQ]
  exact
    wedinLemma20_12_diff_projection_diff_sub_swapped_eq_projectionDiff_cube P Q

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    trace form of the projector-difference cube identity. -/
theorem wedinLemma20_12_finiteTrace_diff_projection_diff_sub_swapped_eq_projectionDiff_cube
    {m : ℕ} (P Q : Fin m → Fin m → ℝ) :
    finiteTrace
        (rectMatMul
          (rectMatMul (fun i j => P i j - Q i j) P)
          (fun i j => P i j - Q i j)) -
      finiteTrace
        (rectMatMul
          (rectMatMul (fun i j => P i j - Q i j) Q)
          (fun i j => P i j - Q i j)) =
      finiteTrace
        (rectMatMul
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j))
          (fun i j => P i j - Q i j)) := by
  rw [← finiteTrace_sub]
  exact congrArg finiteTrace
    (wedinLemma20_12_diff_projection_diff_sub_swapped_eq_projectionDiff_cube P Q)

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    trace form of the compressed-Gram cube identity in the original
    `(I-Q)P(I-Q)` and `(I-P)Q(I-P)` orientations. -/
theorem wedinLemma20_12_finiteTrace_compressedGram_sub_swapped_eq_projectionDiff_cube
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    finiteTrace
        (rectMatMul
          (rectMatMul (fun i j => idMatrix m i j - Q i j) P)
          (fun i j => idMatrix m i j - Q i j)) -
      finiteTrace
        (rectMatMul
          (rectMatMul (fun i j => idMatrix m i j - P i j) Q)
          (fun i j => idMatrix m i j - P i j)) =
      finiteTrace
        (rectMatMul
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j))
          (fun i j => P i j - Q i j)) := by
  rw [← finiteTrace_sub]
  exact congrArg finiteTrace
    (wedinLemma20_12_compressedGram_sub_swapped_compressedGram_eq_projectionDiff_cube
      P Q hIdemP hIdemQ)

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the trace of `(I-Q)P(I-Q)` is `tr(P) - tr(PQ)` for an algebraic
    projection `Q`. -/
theorem wedinLemma20_12_finiteTrace_compressedGram_eq_projection_trace_sub
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemQ : rectMatMul Q Q = Q) :
    finiteTrace
        (rectMatMul
          (rectMatMul (fun i j => idMatrix m i j - Q i j) P)
          (fun i j => idMatrix m i j - Q i j)) =
      finiteTrace P - finiteTrace (rectMatMul P Q) := by
  let IQ : Fin m → Fin m → ℝ := fun i j => idMatrix m i j - Q i j
  have hIQIdem : rectMatMul IQ IQ = IQ := by
    simpa [IQ] using
      wedinLemma20_12_projectionComplement_idempotent Q hIdemQ
  have hcycle₁ :
      finiteTrace (rectMatMul (rectMatMul IQ P) IQ) =
        finiteTrace (rectMatMul IQ (rectMatMul IQ P)) := by
    simpa [finiteMatMul, rectMatMul] using
      finiteTrace_finiteMatMul_comm (rectMatMul IQ P) IQ
  have hcycle₂ :
      finiteTrace (rectMatMul IQ P) =
        finiteTrace (rectMatMul P IQ) := by
    simpa [finiteMatMul, rectMatMul] using
      finiteTrace_finiteMatMul_comm IQ P
  have hright :
      finiteTrace (rectMatMul P IQ) =
        finiteTrace P - finiteTrace (rectMatMul P Q) := by
    have hmul := rectMatMul_sub_right P (idMatrix m) Q
    calc
      finiteTrace (rectMatMul P IQ)
          = finiteTrace
              (fun i j =>
                rectMatMul P (idMatrix m) i j - rectMatMul P Q i j) := by
              simpa [IQ] using congrArg finiteTrace hmul
      _ = finiteTrace (rectMatMul P (idMatrix m)) -
            finiteTrace (rectMatMul P Q) := by
              rw [finiteTrace_sub]
      _ = finiteTrace P - finiteTrace (rectMatMul P Q) := by
              rw [rectMatMul_id_right]
  calc
    finiteTrace (rectMatMul (rectMatMul IQ P) IQ)
        = finiteTrace (rectMatMul IQ (rectMatMul IQ P)) := hcycle₁
    _ = finiteTrace (rectMatMul (rectMatMul IQ IQ) P) := by
            rw [← rectMatMul_assoc]
    _ = finiteTrace (rectMatMul IQ P) := by
            rw [hIQIdem]
    _ = finiteTrace (rectMatMul P IQ) := hcycle₂
    _ = finiteTrace P - finiteTrace (rectMatMul P Q) := hright

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    subtracting the two compressed-Gram traces leaves only the difference of
    the projection traces. -/
theorem wedinLemma20_12_finiteTrace_compressedGram_sub_swapped_eq_projection_trace_sub
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    finiteTrace
        (rectMatMul
          (rectMatMul (fun i j => idMatrix m i j - Q i j) P)
          (fun i j => idMatrix m i j - Q i j)) -
      finiteTrace
        (rectMatMul
          (rectMatMul (fun i j => idMatrix m i j - P i j) Q)
          (fun i j => idMatrix m i j - P i j)) =
      finiteTrace P - finiteTrace Q := by
  have hP :=
    wedinLemma20_12_finiteTrace_compressedGram_eq_projection_trace_sub
      P Q hIdemQ
  have hQ :=
    wedinLemma20_12_finiteTrace_compressedGram_eq_projection_trace_sub
      Q P hIdemP
  have hQP :
      finiteTrace (rectMatMul Q P) = finiteTrace (rectMatMul P Q) := by
    simpa [finiteMatMul, rectMatMul] using
      finiteTrace_finiteMatMul_comm Q P
  rw [hP, hQ, hQP]
  ring

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    for algebraic projections, the trace of `(P-Q)^3` is the trace of
    `P-Q`. -/
theorem wedinLemma20_12_finiteTrace_projectionDiff_cube_eq_projectionDiff
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    finiteTrace
        (rectMatMul
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j))
          (fun i j => P i j - Q i j)) =
      finiteTrace (fun i j => P i j - Q i j) := by
  have hcube :=
    wedinLemma20_12_finiteTrace_compressedGram_sub_swapped_eq_projectionDiff_cube
      P Q hIdemP hIdemQ
  have hdiff :=
    wedinLemma20_12_finiteTrace_compressedGram_sub_swapped_eq_projection_trace_sub
      P Q hIdemP hIdemQ
  calc
    finiteTrace
        (rectMatMul
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j))
          (fun i j => P i j - Q i j))
        = finiteTrace
            (rectMatMul
              (rectMatMul (fun i j => idMatrix m i j - Q i j) P)
              (fun i j => idMatrix m i j - Q i j)) -
          finiteTrace
            (rectMatMul
              (rectMatMul (fun i j => idMatrix m i j - P i j) Q)
              (fun i j => idMatrix m i j - P i j)) := by
            exact hcube.symm
    _ = finiteTrace P - finiteTrace Q := hdiff
    _ = finiteTrace (fun i j => P i j - Q i j) := by
            rw [finiteTrace_sub]

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    equal projection traces imply equality of the two compressed-Gram traces. -/
theorem wedinLemma20_12_finiteTrace_compressedGram_eq_swapped_of_projection_trace_eq
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (hTrace : finiteTrace P = finiteTrace Q) :
    finiteTrace
        (rectMatMul
          (rectMatMul (fun i j => idMatrix m i j - Q i j) P)
          (fun i j => idMatrix m i j - Q i j)) =
      finiteTrace
        (rectMatMul
          (rectMatMul (fun i j => idMatrix m i j - P i j) Q)
          (fun i j => idMatrix m i j - P i j)) := by
  have hdiff :=
    wedinLemma20_12_finiteTrace_compressedGram_sub_swapped_eq_projection_trace_sub
      P Q hIdemP hIdemQ
  rw [hTrace] at hdiff
  linarith

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    a compressed-Gram Loewner comparison plus equal projection traces supplies
    the exact cross-projection operator-2 equality needed by the conditional
    `min` packaging route.

This theorem does not prove the missing principal-angle/Stewart--Sun comparison;
it isolates that remaining foundation as the explicit Loewner hypothesis. -/
theorem wedinLemma20_12_complexMatrixOp2_crossProjection_eq_of_compressedGram_loewnerLe_trace_eq
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (hTrace : finiteTrace P = finiteTrace Q)
    (hLoewner :
      finiteLoewnerLe
        (rectMatMul
          (rectMatMul (fun i j => idMatrix m i j - Q i j) P)
          (fun i j => idMatrix m i j - Q i j))
        (rectMatMul
          (rectMatMul (fun i j => idMatrix m i j - P i j) Q)
          (fun i j => idMatrix m i j - P i j))) :
    complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul P (fun i j => idMatrix m i j - Q i j))) =
      complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul Q (fun i j => idMatrix m i j - P i j))) := by
  let GP : Fin m → Fin m → ℝ :=
    rectMatMul
      (rectMatMul (fun i j => idMatrix m i j - Q i j) P)
      (fun i j => idMatrix m i j - Q i j)
  let GQ : Fin m → Fin m → ℝ :=
    rectMatMul
      (rectMatMul (fun i j => idMatrix m i j - P i j) Q)
      (fun i j => idMatrix m i j - P i j)
  have hGPsym : IsSymmetricFiniteMatrix GP := by
    simpa [GP] using
      wedinLemma20_12_compressedGram_symmetric P Q hP hQ hIdemP
  have hGQsym : IsSymmetricFiniteMatrix GQ := by
    simpa [GQ] using
      wedinLemma20_12_compressedGram_symmetric Q P hQ hP hIdemQ
  have hTraceGram : finiteTrace GP = finiteTrace GQ := by
    simpa [GP, GQ] using
      wedinLemma20_12_finiteTrace_compressedGram_eq_swapped_of_projection_trace_eq
        P Q hIdemP hIdemQ hTrace
  have hGramEq : GP = GQ :=
    finiteLoewnerLe_eq_of_finiteTrace_eq hGPsym hGQsym
      (by simpa [GP, GQ] using hLoewner) hTraceGram
  have hOpEq :
      complexMatrixOp2 (realRectToCMatrix GP) =
        complexMatrixOp2 (realRectToCMatrix GQ) := by
    rw [hGramEq]
  exact
    wedinLemma20_12_complexMatrixOp2_crossProjection_eq_of_compressedGram_eq
      P Q hP hQ hIdemP hIdemQ (by simpa [GP, GQ] using hOpEq)

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12:
    source-oriented projection perturbation bound.

    This transposes the swapped one-sided half into the printed orientation
    `P_A (I - P_B)`, giving
    `||P_A(I-P_B)||_2 <= ||A-B||_2 ||Aplus||_2` in the repository predicate
    API.  The equality with the opposite cross-projection norm is still not
    claimed. -/
theorem wedinLemma20_12_rectOpNorm2Le_rangeProjection_mul_projectionComplement
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {delta Aplus_norm : ℝ}
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hAplus_norm_nonneg : 0 ≤ Aplus_norm)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm) :
    rectOpNorm2Le
      (rectMatMul
        (rectMatMul A Aplus)
        (fun i j => idMatrix m i j - rectMatMul B Bplus i j))
      (delta * Aplus_norm) := by
  let PA : Fin m → Fin m → ℝ := rectMatMul A Aplus
  let IPB : Fin m → Fin m → ℝ :=
    fun i j => idMatrix m i j - rectMatMul B Bplus i j
  have hIPB_sym : IsSymmetricFiniteMatrix IPB :=
    wedinLemma20_12_projectionComplement_symmetric
      (rectMatMul B Bplus) hSymB
  have hhalf :
      rectOpNorm2Le (rectMatMul IPB PA) (delta * Aplus_norm) := by
    simpa [PA, IPB] using
      wedinLemma20_12_rectOpNorm2Le_complement_rangeProjection_mul_rangeProjection_swapped
        A B Aplus Bplus hleftB hSymB hDelta hAplus
  have hdelta_nonneg : 0 ≤ delta :=
    rectOpNorm2Le_radius_nonneg (M := fun i j => B i j - A i j) hDelta
  have htrans :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
      (rectMatMul IPB PA)
      (mul_nonneg hdelta_nonneg hAplus_norm_nonneg)
      hhalf
  have htranspose :
      finiteTranspose (rectMatMul IPB PA) = rectMatMul PA IPB :=
    wedinLemma20_12_finiteTranspose_rectMatMul_of_symmetric
      IPB PA hIPB_sym (by simpa [PA] using hSymA)
  rw [htranspose] at htrans
  simpa [PA, IPB] using htrans

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12:
    source-oriented swapped projection perturbation bound.

    This transposes the direct one-sided half into the printed orientation
    `P_B (I - P_A)`, giving
    `||P_B(I-P_A)||_2 <= ||A-B||_2 ||Bplus||_2` in the repository predicate
    API. -/
theorem wedinLemma20_12_rectOpNorm2Le_rangeProjection_mul_projectionComplement_swapped
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {delta Bplus_norm : ℝ}
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBplus_norm_nonneg : 0 ≤ Bplus_norm)
    (hBplus : rectOpNorm2Le Bplus Bplus_norm) :
    rectOpNorm2Le
      (rectMatMul
        (rectMatMul B Bplus)
        (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
      (delta * Bplus_norm) := by
  let PB : Fin m → Fin m → ℝ := rectMatMul B Bplus
  let IPA : Fin m → Fin m → ℝ :=
    fun i j => idMatrix m i j - rectMatMul A Aplus i j
  have hIPA_sym : IsSymmetricFiniteMatrix IPA :=
    wedinLemma20_12_projectionComplement_symmetric
      (rectMatMul A Aplus) hSymA
  have hhalf :
      rectOpNorm2Le (rectMatMul IPA PB) (delta * Bplus_norm) := by
    simpa [PB, IPA] using
      wedinLemma20_12_rectOpNorm2Le_complement_rangeProjection_mul_rangeProjection
        A B Aplus Bplus hleftA hSymA hDelta hBplus
  have hdelta_nonneg : 0 ≤ delta :=
    rectOpNorm2Le_radius_nonneg (M := fun i j => B i j - A i j) hDelta
  have htrans :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
      (rectMatMul IPA PB)
      (mul_nonneg hdelta_nonneg hBplus_norm_nonneg)
      hhalf
  have htranspose :
      finiteTranspose (rectMatMul IPA PB) = rectMatMul PB IPA :=
    wedinLemma20_12_finiteTranspose_rectMatMul_of_symmetric
      IPA PB hIPA_sym (by simpa [PB] using hSymB)
  rw [htranspose] at htrans
  simpa [PB, IPA] using htrans

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    conditional transfer of the source-oriented `Aplus` projector bound to
    the opposite cross projection from an exact complexified operator-norm
    equality.

The hypothesis is the still-open Stewart--Sun/CS equality route, expressed in
the exact `complexMatrixOp2` API.  This theorem only packages the consequence;
it does not prove the equality. -/
theorem wedinLemma20_12_rectOpNorm2Le_rangeProjection_mul_projectionComplement_swapped_of_complexMatrixOp2_eq
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {delta Aplus_norm : ℝ}
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hAplus_norm_nonneg : 0 ≤ Aplus_norm)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hEq :
      complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul
              (rectMatMul B Bplus)
              (fun i j => idMatrix m i j - rectMatMul A Aplus i j))) =
        complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul
              (rectMatMul A Aplus)
              (fun i j => idMatrix m i j - rectMatMul B Bplus i j)))) :
    rectOpNorm2Le
      (rectMatMul
        (rectMatMul B Bplus)
        (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
      (delta * Aplus_norm) := by
  let PA : Fin m → Fin m → ℝ := rectMatMul A Aplus
  let PB : Fin m → Fin m → ℝ := rectMatMul B Bplus
  let IPA : Fin m → Fin m → ℝ :=
    fun i j => idMatrix m i j - PA i j
  let IPB : Fin m → Fin m → ℝ :=
    fun i j => idMatrix m i j - PB i j
  have hdelta_nonneg : 0 ≤ delta :=
    rectOpNorm2Le_radius_nonneg (M := fun i j => B i j - A i j) hDelta
  have hPAIPB :
      rectOpNorm2Le (rectMatMul PA IPB) (delta * Aplus_norm) := by
    simpa [PA, IPB] using
      wedinLemma20_12_rectOpNorm2Le_rangeProjection_mul_projectionComplement
        A B Aplus Bplus hleftB hSymA hSymB hDelta
        hAplus_norm_nonneg hAplus
  exact
    rectOpNorm2Le_of_complexMatrixOp2_eq_of_rectOpNorm2Le
      (rectMatMul PB IPA) (rectMatMul PA IPB)
      (mul_nonneg hdelta_nonneg hAplus_norm_nonneg)
      (by simpa [PA, PB, IPA, IPB] using hEq)
      hPAIPB

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    conditional `min` packaging for the source-oriented `P_B(I-P_A)` projector
    estimate.

Once the still-open Stewart--Sun/CS equality is supplied in exact
`complexMatrixOp2` form, the two one-sided estimates combine to the source
radius `delta * min Aplus_norm Bplus_norm`. -/
theorem wedinLemma20_12_rectOpNorm2Le_rangeProjection_mul_projectionComplement_swapped_min_of_complexMatrixOp2_eq
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {delta Aplus_norm Bplus_norm : ℝ}
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hAplus_norm_nonneg : 0 ≤ Aplus_norm)
    (hBplus_norm_nonneg : 0 ≤ Bplus_norm)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hBplus : rectOpNorm2Le Bplus Bplus_norm)
    (hEq :
      complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul
              (rectMatMul B Bplus)
              (fun i j => idMatrix m i j - rectMatMul A Aplus i j))) =
        complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul
              (rectMatMul A Aplus)
              (fun i j => idMatrix m i j - rectMatMul B Bplus i j)))) :
    rectOpNorm2Le
      (rectMatMul
        (rectMatMul B Bplus)
        (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
      (delta * min Aplus_norm Bplus_norm) := by
  have hA_bound :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * Aplus_norm) :=
    wedinLemma20_12_rectOpNorm2Le_rangeProjection_mul_projectionComplement_swapped_of_complexMatrixOp2_eq
      A B Aplus Bplus hleftB hSymA hSymB hDelta
      hAplus_norm_nonneg hAplus hEq
  have hB_bound :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * Bplus_norm) :=
    wedinLemma20_12_rectOpNorm2Le_rangeProjection_mul_projectionComplement_swapped
      A B Aplus Bplus hleftA hSymA hSymB hDelta
      hBplus_norm_nonneg hBplus
  intro x
  by_cases hAB : Aplus_norm ≤ Bplus_norm
  · simpa [min_eq_left hAB] using hA_bound x
  · have hBA : Bplus_norm ≤ Aplus_norm :=
      le_of_lt (lt_of_not_ge hAB)
    simpa [min_eq_right hBA] using hB_bound x

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    source range-projection Stewart--Sun equality.  For the projections
    `A*Aplus` and `B*Bplus`, the equal range-dimension hypothesis follows from
    the two source left inverses. -/
theorem wedinLemma20_12_complexMatrixOp2_rangeProjection_crossProjection_eq_of_left_inverses
    {m k : ℕ} (hm : 0 < m) (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus)) :
    complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul
            (rectMatMul B Bplus)
            (fun i j => idMatrix m i j - rectMatMul A Aplus i j))) =
      complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul
            (rectMatMul A Aplus)
            (fun i j => idMatrix m i j - rectMatMul B Bplus i j))) := by
  let PA : Fin m → Fin m → ℝ := rectMatMul A Aplus
  let PB : Fin m → Fin m → ℝ := rectMatMul B Bplus
  have hIdemA : rectMatMul PA PA = PA := by
    simpa [PA] using
      rectMatMul_rangeProjection_idempotent_of_left_inverse A Aplus hleftA
  have hIdemB : rectMatMul PB PB = PB := by
    simpa [PB] using
      rectMatMul_rangeProjection_idempotent_of_left_inverse B Bplus hleftB
  have hRangeFinrank :
      Module.finrank ℝ
          (LinearMap.range ((Matrix.of PB : Matrix (Fin m) (Fin m) ℝ).mulVecLin)) =
        Module.finrank ℝ
          (LinearMap.range ((Matrix.of PA : Matrix (Fin m) (Fin m) ℝ).mulVecLin)) := by
    simpa [PA, PB] using
      wedinLemma20_12_rangeProjection_range_finrank_eq_of_left_inverses
        B A Bplus Aplus hleftB hleftA
  simpa [PA, PB] using
    wedinLemma20_12_complexMatrixOp2_crossProjection_eq_of_range_finrank_eq
      hm PB PA (by simpa [PB] using hSymB) (by simpa [PA] using hSymA)
      hIdemB hIdemA hRangeFinrank

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12:
    source `min` projector bound with the Stewart--Sun/principal-angle equality
    discharged.

This is the source-facing Lemma 20.12 surface in the repository's
`rectOpNorm2Le` API:
`||P_B(I-P_A)||₂ <= ||A-B||₂ * min(||Aplus||₂, ||Bplus||₂)`. -/
theorem wedinLemma20_12_rectOpNorm2Le_rangeProjection_mul_projectionComplement_swapped_min
    {m k : ℕ} (hm : 0 < m) (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {delta Aplus_norm Bplus_norm : ℝ}
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hAplus_norm_nonneg : 0 ≤ Aplus_norm)
    (hBplus_norm_nonneg : 0 ≤ Bplus_norm)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hBplus : rectOpNorm2Le Bplus Bplus_norm) :
    rectOpNorm2Le
      (rectMatMul
        (rectMatMul B Bplus)
        (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
      (delta * min Aplus_norm Bplus_norm) := by
  have hEq :
      complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul
              (rectMatMul B Bplus)
              (fun i j => idMatrix m i j - rectMatMul A Aplus i j))) =
        complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul
              (rectMatMul A Aplus)
              (fun i j => idMatrix m i j - rectMatMul B Bplus i j))) :=
    wedinLemma20_12_complexMatrixOp2_rangeProjection_crossProjection_eq_of_left_inverses
      hm A B Aplus Bplus hleftA hleftB hSymA hSymB
  exact
    wedinLemma20_12_rectOpNorm2Le_rangeProjection_mul_projectionComplement_swapped_min_of_complexMatrixOp2_eq
      A B Aplus Bplus hleftA hleftB hSymA hSymB hDelta
      hAplus_norm_nonneg hBplus_norm_nonneg hAplus hBplus hEq

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    conditional Loewner-to-`min` packaging for the source-oriented
    `P_B(I-P_A)` projector estimate.

This closes the `delta * min Aplus_norm Bplus_norm` projector bound once the
compressed-Gram Loewner comparison and equal projection traces are supplied.
It still leaves the Stewart--Sun/principal-angle comparison as the explicit
`hLoewner` hypothesis. -/
theorem wedinLemma20_12_rectOpNorm2Le_rangeProjection_mul_projectionComplement_swapped_min_of_compressedGram_loewnerLe_trace_eq
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {delta Aplus_norm Bplus_norm : ℝ}
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hTrace :
      finiteTrace (rectMatMul B Bplus) =
        finiteTrace (rectMatMul A Aplus))
    (hLoewner :
      finiteLoewnerLe
        (rectMatMul
          (rectMatMul
            (fun i j => idMatrix m i j - rectMatMul A Aplus i j)
            (rectMatMul B Bplus))
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (rectMatMul
          (rectMatMul
            (fun i j => idMatrix m i j - rectMatMul B Bplus i j)
            (rectMatMul A Aplus))
          (fun i j => idMatrix m i j - rectMatMul B Bplus i j)))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hAplus_norm_nonneg : 0 ≤ Aplus_norm)
    (hBplus_norm_nonneg : 0 ≤ Bplus_norm)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hBplus : rectOpNorm2Le Bplus Bplus_norm) :
    rectOpNorm2Le
      (rectMatMul
        (rectMatMul B Bplus)
        (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
      (delta * min Aplus_norm Bplus_norm) := by
  let PA : Fin m → Fin m → ℝ := rectMatMul A Aplus
  let PB : Fin m → Fin m → ℝ := rectMatMul B Bplus
  have hPAidem : rectMatMul PA PA = PA := by
    simpa [PA] using
      rectMatMul_rangeProjection_idempotent_of_left_inverse A Aplus hleftA
  have hPBidem : rectMatMul PB PB = PB := by
    simpa [PB] using
      rectMatMul_rangeProjection_idempotent_of_left_inverse B Bplus hleftB
  have hEq :
      complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul PB (fun i j => idMatrix m i j - PA i j))) =
        complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul PA (fun i j => idMatrix m i j - PB i j))) := by
    simpa [PA, PB] using
      wedinLemma20_12_complexMatrixOp2_crossProjection_eq_of_compressedGram_loewnerLe_trace_eq
        PB PA hSymB hSymA hPBidem hPAidem hTrace hLoewner
  exact
    wedinLemma20_12_rectOpNorm2Le_rangeProjection_mul_projectionComplement_swapped_min_of_complexMatrixOp2_eq
      A B Aplus Bplus hleftA hleftB hSymA hSymB hDelta
      hAplus_norm_nonneg hBplus_norm_nonneg hAplus hBplus hEq

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    conditional Loewner-to-`min` packaging with the equal projection trace
    discharged from the two full-column left inverses.

This keeps the missing Stewart--Sun/principal-angle comparison explicit as
`hLoewner`, but no longer requires callers to provide the equal-trace fact
separately. -/
theorem wedinLemma20_12_rectOpNorm2Le_rangeProjection_mul_projectionComplement_swapped_min_of_compressedGram_loewnerLe
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {delta Aplus_norm Bplus_norm : ℝ}
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hLoewner :
      finiteLoewnerLe
        (rectMatMul
          (rectMatMul
            (fun i j => idMatrix m i j - rectMatMul A Aplus i j)
            (rectMatMul B Bplus))
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (rectMatMul
          (rectMatMul
            (fun i j => idMatrix m i j - rectMatMul B Bplus i j)
            (rectMatMul A Aplus))
          (fun i j => idMatrix m i j - rectMatMul B Bplus i j)))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hAplus_norm_nonneg : 0 ≤ Aplus_norm)
    (hBplus_norm_nonneg : 0 ≤ Bplus_norm)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hBplus : rectOpNorm2Le Bplus Bplus_norm) :
    rectOpNorm2Le
      (rectMatMul
        (rectMatMul B Bplus)
        (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
      (delta * min Aplus_norm Bplus_norm) := by
  have hTrace :
      finiteTrace (rectMatMul B Bplus) =
        finiteTrace (rectMatMul A Aplus) := by
    simpa using
      (finiteTrace_rangeProjection_eq_of_left_inverses
        B A Bplus Aplus hleftB hleftA)
  exact
    wedinLemma20_12_rectOpNorm2Le_rangeProjection_mul_projectionComplement_swapped_min_of_compressedGram_loewnerLe_trace_eq
      A B Aplus Bplus hleftA hleftB hSymA hSymB hTrace hLoewner
      hDelta hAplus_norm_nonneg hBplus_norm_nonneg hAplus hBplus

/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 route audit:
    the compressed-Gram Loewner comparison is not a valid general replacement
    for the missing Stewart--Sun/principal-angle equality.  Two rank-one
    orthogonal projections in `ℝ^2` can have equal trace while the Loewner
    comparison required by the conditional route fails.

This is a bottleneck-audit result, not a source theorem.  It rules out closing
Lemma 20.12 by trying to prove the displayed Loewner comparison from the
ordinary equal-rank projection hypotheses alone. -/
theorem wedinLemma20_12_compressedGram_loewnerLe_counterexample :
    ∃ P Q : Fin 2 → Fin 2 → ℝ,
      IsSymmetricFiniteMatrix P ∧
      IsSymmetricFiniteMatrix Q ∧
      rectMatMul P P = P ∧
      rectMatMul Q Q = Q ∧
      finiteTrace P = finiteTrace Q ∧
      ¬ finiteLoewnerLe
        (rectMatMul
          (rectMatMul (fun i j => idMatrix 2 i j - Q i j) P)
          (fun i j => idMatrix 2 i j - Q i j))
        (rectMatMul
          (rectMatMul (fun i j => idMatrix 2 i j - P i j) Q)
          (fun i j => idMatrix 2 i j - P i j)) := by
  let P : Fin 2 → Fin 2 → ℝ :=
    fun i j => if i = (0 : Fin 2) ∧ j = (0 : Fin 2) then 1 else 0
  let Q : Fin 2 → Fin 2 → ℝ := fun _ _ => (1 / 2 : ℝ)
  refine ⟨P, Q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [P]
  · intro i j
    norm_num [Q]
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [P, rectMatMul]
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Q, rectMatMul]
  · norm_num [P, Q, finiteTrace]
    rfl
  · intro hLoewner
    let GP : Fin 2 → Fin 2 → ℝ :=
      rectMatMul
        (rectMatMul (fun i j => idMatrix 2 i j - Q i j) P)
        (fun i j => idMatrix 2 i j - Q i j)
    let GQ : Fin 2 → Fin 2 → ℝ :=
      rectMatMul
        (rectMatMul (fun i j => idMatrix 2 i j - P i j) Q)
        (fun i j => idMatrix 2 i j - P i j)
    let e0 : Fin 2 → ℝ := finiteBasisVec (0 : Fin 2)
    have hquad := hLoewner e0
    have hGP :
        finiteQuadraticForm GP e0 = (1 / 4 : ℝ) := by
      norm_num [GP, P, Q, e0, finiteQuadraticForm, finiteMatVec,
        rectMatMul, finiteBasisVec, idMatrix]
    have hGQ :
        finiteQuadraticForm GQ e0 = 0 := by
      norm_num [GQ, P, Q, e0, finiteQuadraticForm, finiteMatVec,
        rectMatMul, finiteBasisVec, idMatrix]
    have hbad : (1 / 4 : ℝ) ≤ 0 := by
      simpa [GP, GQ, e0, hGP, hGQ] using hquad
    norm_num at hbad

/-- Higham, 2nd ed., Chapter 20, Wedin proof line toward (20.33):
    the source-oriented Lemma 20.12 projector estimate controls `Bplus*r`
    whenever `r` is orthogonal to the range of `A`.

This is the local algebra behind `B⁺r = B⁺P_B(I-P_A)r`.  It deliberately
keeps the one-sided projector radius already proved above and does not claim
the missing CS-decomposition equality from the printed Lemma 20.12. -/
theorem wedinTheorem20_1_vecNorm2_Bplus_residual_le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {delta Bplus_norm : ℝ} (r : Fin m → ℝ)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBplus_norm_nonneg : 0 ≤ Bplus_norm)
    (hBplus : rectOpNorm2Le Bplus Bplus_norm)
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0) :
    vecNorm2 (rectMatMulVec Bplus r) ≤
      (delta * Bplus_norm * Bplus_norm) * vecNorm2 r := by
  let PA : Fin m → Fin m → ℝ := rectMatMul A Aplus
  let PB : Fin m → Fin m → ℝ := rectMatMul B Bplus
  let IPA : Fin m → Fin m → ℝ :=
    fun i j => idMatrix m i j - PA i j
  have hBplusPB : rectMatMul Bplus PB = Bplus := by
    calc
      rectMatMul Bplus PB = rectMatMul Bplus (rectMatMul B Bplus) := by
        rfl
      _ = rectMatMul (rectMatMul Bplus B) Bplus := by
        rw [rectMatMul_assoc]
      _ = rectMatMul (idMatrix (k + 1)) Bplus := by
        rw [hleftB]
      _ = Bplus := rectMatMul_id_left Bplus
  have hIPA_r : rectMatMulVec IPA r = r := by
    rw [show IPA = (fun i j => idMatrix m i j - rectMatMul A Aplus i j) by
      ext i j
      rfl]
    rw [wedinLemma20_12_rectMatMulVec_projectionComplement]
    rw [hrangeA_residual]
    ext i
    simp
  have hfactor :
      rectMatMulVec Bplus r =
        rectMatMulVec Bplus (rectMatMulVec (rectMatMul PB IPA) r) := by
    symm
    calc
      rectMatMulVec Bplus (rectMatMulVec (rectMatMul PB IPA) r)
          = rectMatMulVec Bplus
              (rectMatMulVec PB (rectMatMulVec IPA r)) := by
              rw [rectMatMulVec_rectMatMul]
      _ = rectMatMulVec Bplus (rectMatMulVec PB r) := by
              rw [hIPA_r]
      _ = rectMatMulVec (rectMatMul Bplus PB) r := by
              rw [← rectMatMulVec_rectMatMul]
      _ = rectMatMulVec Bplus r := by
              rw [hBplusPB]
  have hPBIPA :
      rectOpNorm2Le (rectMatMul PB IPA) (delta * Bplus_norm) := by
    simpa [PA, PB, IPA] using
      wedinLemma20_12_rectOpNorm2Le_rangeProjection_mul_projectionComplement_swapped
        A B Aplus Bplus hleftA hSymA hSymB hDelta
        hBplus_norm_nonneg hBplus
  have hBplus_y := hBplus (rectMatMulVec (rectMatMul PB IPA) r)
  have hPBIPA_r := hPBIPA r
  calc
    vecNorm2 (rectMatMulVec Bplus r)
        = vecNorm2
            (rectMatMulVec Bplus (rectMatMulVec (rectMatMul PB IPA) r)) := by
            rw [hfactor]
    _ ≤ Bplus_norm * vecNorm2 (rectMatMulVec (rectMatMul PB IPA) r) :=
            hBplus_y
    _ ≤ Bplus_norm * ((delta * Bplus_norm) * vecNorm2 r) :=
            mul_le_mul_of_nonneg_left hPBIPA_r hBplus_norm_nonneg
    _ = (delta * Bplus_norm * Bplus_norm) * vecNorm2 r := by ring

/-- Higham, 2nd ed., Chapter 20, Wedin proof line toward (20.33):
    `η`-scaled form of the `Bplus*r` residual bound.

When Lemma 20.11 has supplied
`||Bplus||₂ <= ||Aplus||₂ / (1 - η)` and `η = ||Aplus||₂ * delta`, the
one-sided Lemma 20.12 route gives the displayed residual-transfer scale
`η ||Aplus||₂ / (1 - η)^2`. -/
theorem wedinTheorem20_1_vecNorm2_Bplus_residual_le_eta
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {Aplus_norm delta eta : ℝ} (r : Fin m → ℝ)
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBplus :
      rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)))
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0) :
    vecNorm2 (rectMatMulVec Bplus r) ≤
      (eta * Aplus_norm / (1 - eta) ^ 2) * vecNorm2 r := by
  have hden_pos : 0 < 1 - eta :=
    wedinLemma20_11_denominator_pos hsmall
  have hBplus_radius_nonneg : 0 ≤ Aplus_norm / (1 - eta) :=
    div_nonneg (le_of_lt hAplus_pos) (le_of_lt hden_pos)
  have hbound :=
    wedinTheorem20_1_vecNorm2_Bplus_residual_le
      A B Aplus Bplus r hleftA hleftB hSymA hSymB hDelta
      hBplus_radius_nonneg hBplus hrangeA_residual
  have hcoeff :
      delta * (Aplus_norm / (1 - eta)) *
          (Aplus_norm / (1 - eta)) =
        eta * Aplus_norm / (1 - eta) ^ 2 := by
    rw [heta]
    field_simp [ne_of_gt hden_pos]
  simpa [hcoeff] using hbound

/-- Higham, 2nd ed., Chapter 20, Wedin proof line toward (20.33):
    direct forcing-term estimate for `Bplus*(-DeltaA*x + Deltab)`.

This is the elementary norm part of the Wedin transfer: a pseudoinverse
operator-radius for `Bplus`, an operator-radius for `DeltaA`, and a vector
radius for `Deltab` bound the forcing contribution before it is combined with
the residual-transfer term. -/
theorem wedinTheorem20_1_vecNorm2_Bplus_forcing_le
    {m k : ℕ} (Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (Deltab : Fin m → ℝ)
    (x : Fin (k + 1) → ℝ)
    {Bplus_norm DeltaA_norm Deltab_norm : ℝ}
    (hBplus_norm_nonneg : 0 ≤ Bplus_norm)
    (hBplus : rectOpNorm2Le Bplus Bplus_norm)
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm) :
    vecNorm2
        (rectMatMulVec Bplus
          (fun i => -rectMatMulVec DeltaA x i + Deltab i)) ≤
      Bplus_norm * (DeltaA_norm * vecNorm2 x + Deltab_norm) := by
  let forcing : Fin m → ℝ :=
    fun i => -rectMatMulVec DeltaA x i + Deltab i
  have hforcing :
      vecNorm2 forcing ≤ DeltaA_norm * vecNorm2 x + Deltab_norm := by
    calc
      vecNorm2 forcing
          ≤ vecNorm2 (fun i : Fin m => -rectMatMulVec DeltaA x i) +
              vecNorm2 Deltab := by
              simpa [forcing] using
                vecNorm2_add_le (fun i : Fin m => -rectMatMulVec DeltaA x i)
                  Deltab
      _ = vecNorm2 (rectMatMulVec DeltaA x) + vecNorm2 Deltab := by
              rw [vecNorm2_neg]
      _ ≤ DeltaA_norm * vecNorm2 x + Deltab_norm :=
              add_le_add (hDeltaA x) hDeltab
  calc
    vecNorm2 (rectMatMulVec Bplus forcing)
        ≤ Bplus_norm * vecNorm2 forcing := hBplus forcing
    _ ≤ Bplus_norm * (DeltaA_norm * vecNorm2 x + Deltab_norm) :=
        mul_le_mul_of_nonneg_left hforcing hBplus_norm_nonneg

/-- Higham, 2nd ed., Chapter 20, Wedin proof line toward (20.33):
    assembled bound for the forcing contribution plus the residual-transfer
    contribution, before the final source scalar normalization. -/
theorem wedinTheorem20_1_vecNorm2_Bplus_forcing_add_residual_le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (Deltab r : Fin m → ℝ)
    (x : Fin (k + 1) → ℝ)
    {Aplus_norm delta eta DeltaA_norm Deltab_norm : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBplus :
      rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)))
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0) :
    vecNorm2
        (fun j =>
          rectMatMulVec Bplus
              (fun i => -rectMatMulVec DeltaA x i + Deltab i) j +
            rectMatMulVec Bplus r j) ≤
      (Aplus_norm / (1 - eta)) *
          (DeltaA_norm * vecNorm2 x + Deltab_norm) +
        (eta * Aplus_norm / (1 - eta) ^ 2) * vecNorm2 r := by
  have hden_pos : 0 < 1 - eta :=
    wedinLemma20_11_denominator_pos hsmall
  have hBplus_radius_nonneg : 0 ≤ Aplus_norm / (1 - eta) :=
    div_nonneg (le_of_lt hAplus_pos) (le_of_lt hden_pos)
  have hforcing :
      vecNorm2
          (rectMatMulVec Bplus
            (fun i => -rectMatMulVec DeltaA x i + Deltab i)) ≤
        (Aplus_norm / (1 - eta)) *
          (DeltaA_norm * vecNorm2 x + Deltab_norm) :=
    wedinTheorem20_1_vecNorm2_Bplus_forcing_le
      Bplus DeltaA Deltab x hBplus_radius_nonneg hBplus hDeltaA hDeltab
  have hresidual :
      vecNorm2 (rectMatMulVec Bplus r) ≤
        (eta * Aplus_norm / (1 - eta) ^ 2) * vecNorm2 r :=
    wedinTheorem20_1_vecNorm2_Bplus_residual_le_eta
      A B Aplus Bplus r hAplus_pos heta hsmall hleftA hleftB
      hSymA hSymB hDelta hBplus hrangeA_residual
  calc
    vecNorm2
        (fun j =>
          rectMatMulVec Bplus
              (fun i => -rectMatMulVec DeltaA x i + Deltab i) j +
            rectMatMulVec Bplus r j)
        ≤ vecNorm2
            (rectMatMulVec Bplus
              (fun i => -rectMatMulVec DeltaA x i + Deltab i)) +
          vecNorm2 (rectMatMulVec Bplus r) := by
            exact vecNorm2_add_le
              (rectMatMulVec Bplus
                (fun i => -rectMatMulVec DeltaA x i + Deltab i))
              (rectMatMulVec Bplus r)
    _ ≤ (Aplus_norm / (1 - eta)) *
            (DeltaA_norm * vecNorm2 x + Deltab_norm) +
          (eta * Aplus_norm / (1 - eta) ^ 2) * vecNorm2 r :=
            add_le_add hforcing hresidual

/-- Higham, 2nd ed., Chapter 20, Wedin proof line toward (20.33):
    assembled bound with the combined source vector
    `-DeltaA*x + Deltab + r` inside the single `Bplus` action. -/
theorem wedinTheorem20_1_vecNorm2_Bplus_combined_forcing_residual_le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (Deltab r : Fin m → ℝ)
    (x : Fin (k + 1) → ℝ)
    {Aplus_norm delta eta DeltaA_norm Deltab_norm : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBplus :
      rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)))
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0) :
    vecNorm2
        (rectMatMulVec Bplus
          (fun i => (-rectMatMulVec DeltaA x i + Deltab i) + r i)) ≤
      (Aplus_norm / (1 - eta)) *
          (DeltaA_norm * vecNorm2 x + Deltab_norm) +
        (eta * Aplus_norm / (1 - eta) ^ 2) * vecNorm2 r := by
  have hsum :=
    wedinTheorem20_1_vecNorm2_Bplus_forcing_add_residual_le
      A B Aplus Bplus DeltaA Deltab r x hAplus_pos heta hsmall
      hleftA hleftB hSymA hSymB hDelta hBplus hDeltaA hDeltab
      hrangeA_residual
  have hsplit :
      rectMatMulVec Bplus
          (fun i => (-rectMatMulVec DeltaA x i + Deltab i) + r i) =
        fun j =>
          rectMatMulVec Bplus
              (fun i => -rectMatMulVec DeltaA x i + Deltab i) j +
            rectMatMulVec Bplus r j := by
    simpa using
      rectMatMulVec_add Bplus
        (fun i : Fin m => -rectMatMulVec DeltaA x i + Deltab i) r
  simpa [hsplit] using hsum

/-- Higham, 2nd ed., Chapter 20, Wedin proof line toward (20.33):
    if the perturbation algebra has produced the source equation for
    `B*(y-x)`, then the left inverse `Bplus*B = I` identifies the solution
    difference with the combined `Bplus` vector. -/
theorem wedinTheorem20_1_solution_difference_eq_Bplus_combined_of_B_mul
    {m k : ℕ} (B : Fin m → Fin (k + 1) → ℝ)
    (Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (Deltab r : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hBdiff :
      rectMatMulVec B (fun j => y j - x j) =
        fun i => (-rectMatMulVec DeltaA x i + Deltab i) + r i) :
    (fun j => y j - x j) =
      rectMatMulVec Bplus
        (fun i => (-rectMatMulVec DeltaA x i + Deltab i) + r i) := by
  calc
    (fun j => y j - x j)
        = rectMatMulVec (idMatrix (k + 1)) (fun j => y j - x j) := by
            symm
            exact rectMatMulVec_idMatrix (fun j => y j - x j)
    _ = rectMatMulVec (rectMatMul Bplus B) (fun j => y j - x j) := by
            rw [hleftB]
    _ = rectMatMulVec Bplus
          (rectMatMulVec B (fun j => y j - x j)) := by
            rw [rectMatMulVec_rectMatMul]
    _ = rectMatMulVec Bplus
          (fun i => (-rectMatMulVec DeltaA x i + Deltab i) + r i) := by
            rw [hBdiff]

/-- Higham, 2nd ed., Chapter 20, Wedin proof line toward (20.33):
    solution-difference norm bound after the source equation for `B*(y-x)`
    has been exposed.  This is still prior to the printed relative scalar
    normalization in (20.1). -/
theorem wedinTheorem20_1_vecNorm2_solution_difference_le_of_B_mul
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (Deltab r : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {Aplus_norm delta eta DeltaA_norm Deltab_norm : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBplus :
      rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)))
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hBdiff :
      rectMatMulVec B (fun j => y j - x j) =
        fun i => (-rectMatMulVec DeltaA x i + Deltab i) + r i) :
    vecNorm2 (fun j => y j - x j) ≤
      (Aplus_norm / (1 - eta)) *
          (DeltaA_norm * vecNorm2 x + Deltab_norm) +
        (eta * Aplus_norm / (1 - eta) ^ 2) * vecNorm2 r := by
  have hdiff_eq :
      (fun j => y j - x j) =
        rectMatMulVec Bplus
          (fun i => (-rectMatMulVec DeltaA x i + Deltab i) + r i) :=
    wedinTheorem20_1_solution_difference_eq_Bplus_combined_of_B_mul
      B Bplus DeltaA Deltab r x y hleftB hBdiff
  rw [hdiff_eq]
  exact
    wedinTheorem20_1_vecNorm2_Bplus_combined_forcing_residual_le
      A B Aplus Bplus DeltaA Deltab r x hAplus_pos heta hsmall
      hleftA hleftB hSymA hSymB hDelta hBplus hDeltaA hDeltab
      hrangeA_residual

/-- Higham, 2nd ed., Chapter 20, Wedin proof line toward (20.33):
    a perturbed residual annihilated by the `B` range projector is killed by
    `Bplus`. -/
theorem wedinTheorem20_1_Bplus_perturbed_residual_eq_zero
    {m k : ℕ} (B : Fin m → Fin (k + 1) → ℝ)
    (Bplus : Fin (k + 1) → Fin m → ℝ) (s : Fin m → ℝ)
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hproj_s : rectMatMulVec (rectMatMul B Bplus) s = 0) :
    rectMatMulVec Bplus s = 0 := by
  have hBplusPB : rectMatMul Bplus (rectMatMul B Bplus) = Bplus := by
    calc
      rectMatMul Bplus (rectMatMul B Bplus)
          = rectMatMul (rectMatMul Bplus B) Bplus := by
              rw [rectMatMul_assoc]
      _ = rectMatMul (idMatrix (k + 1)) Bplus := by
              rw [hleftB]
      _ = Bplus := rectMatMul_id_left Bplus
  calc
    rectMatMulVec Bplus s
        = rectMatMulVec (rectMatMul Bplus (rectMatMul B Bplus)) s := by
            rw [hBplusPB]
    _ = rectMatMulVec Bplus (rectMatMulVec (rectMatMul B Bplus) s) := by
            rw [rectMatMulVec_rectMatMul]
    _ = 0 := by
            rw [hproj_s]
            ext j
            unfold rectMatMulVec
            simp

/-- Higham, 2nd ed., Chapter 20, Wedin proof line toward (20.33):
    source-faithful solution-difference identity with the perturbed residual
    `s` present in the `B*(y-x)` equation and removed only through the
    `B` range-projector condition. -/
theorem wedinTheorem20_1_solution_difference_eq_Bplus_combined_of_B_mul_sub_residual
    {m k : ℕ} (B : Fin m → Fin (k + 1) → ℝ)
    (Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hBdiff :
      rectMatMulVec B (fun j => y j - x j) =
        fun i => ((-rectMatMulVec DeltaA x i + Deltab i) + r i) - s i)
    (hproj_s : rectMatMulVec (rectMatMul B Bplus) s = 0) :
    (fun j => y j - x j) =
      rectMatMulVec Bplus
        (fun i => (-rectMatMulVec DeltaA x i + Deltab i) + r i) := by
  let combined : Fin m → ℝ :=
    fun i => (-rectMatMulVec DeltaA x i + Deltab i) + r i
  have hBplus_s : rectMatMulVec Bplus s = 0 :=
    wedinTheorem20_1_Bplus_perturbed_residual_eq_zero
      B Bplus s hleftB hproj_s
  have hsub :
      rectMatMulVec Bplus (fun i => combined i - s i) =
        rectMatMulVec Bplus combined := by
    calc
      rectMatMulVec Bplus (fun i => combined i - s i)
          = fun j => rectMatMulVec Bplus combined j - rectMatMulVec Bplus s j := by
              rw [rectMatMulVec_sub]
      _ = rectMatMulVec Bplus combined := by
              rw [hBplus_s]
              ext j
              simp
  calc
    (fun j => y j - x j)
        = rectMatMulVec (idMatrix (k + 1)) (fun j => y j - x j) := by
            symm
            exact rectMatMulVec_idMatrix (fun j => y j - x j)
    _ = rectMatMulVec (rectMatMul Bplus B) (fun j => y j - x j) := by
            rw [hleftB]
    _ = rectMatMulVec Bplus
          (rectMatMulVec B (fun j => y j - x j)) := by
            rw [rectMatMulVec_rectMatMul]
    _ = rectMatMulVec Bplus (fun i => combined i - s i) := by
            rw [hBdiff]
    _ = rectMatMulVec Bplus combined := hsub

/-- Higham, 2nd ed., Chapter 20, Wedin proof line toward (20.33):
    source-faithful solution-difference norm bound with a perturbed residual
    `s` that is annihilated by the `B` range projector. -/
theorem wedinTheorem20_1_vecNorm2_solution_difference_le_of_B_mul_sub_residual
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {Aplus_norm delta eta DeltaA_norm Deltab_norm : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBplus :
      rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)))
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hBdiff :
      rectMatMulVec B (fun j => y j - x j) =
        fun i => ((-rectMatMulVec DeltaA x i + Deltab i) + r i) - s i)
    (hproj_s : rectMatMulVec (rectMatMul B Bplus) s = 0) :
    vecNorm2 (fun j => y j - x j) ≤
      (Aplus_norm / (1 - eta)) *
          (DeltaA_norm * vecNorm2 x + Deltab_norm) +
        (eta * Aplus_norm / (1 - eta) ^ 2) * vecNorm2 r := by
  have hdiff_eq :
      (fun j => y j - x j) =
        rectMatMulVec Bplus
          (fun i => (-rectMatMulVec DeltaA x i + Deltab i) + r i) :=
    wedinTheorem20_1_solution_difference_eq_Bplus_combined_of_B_mul_sub_residual
      B Bplus DeltaA Deltab r s x y hleftB hBdiff hproj_s
  rw [hdiff_eq]
  exact
    wedinTheorem20_1_vecNorm2_Bplus_combined_forcing_residual_le
      A B Aplus Bplus DeltaA Deltab r x hAplus_pos heta hsmall
      hleftA hleftB hSymA hSymB hDelta hBplus hDeltaA hDeltab
      hrangeA_residual

/-- Higham, 2nd ed., Chapter 20, Wedin proof algebra:
    the residual definitions `r = b - A*x`, `s = b + Δb - B*y`, and
    `B = A + ΔA` imply the source equation
    `B*(y-x) = -ΔA*x + Δb + r - s`. -/
theorem wedinTheorem20_1_B_mul_solution_difference_eq_forcing_residual_sub_of_residuals
    {m k : ℕ} (A B DeltaA : Fin m → Fin (k + 1) → ℝ)
    (b Deltab r s : Fin m → ℝ) (x y : Fin (k + 1) → ℝ)
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i) :
    rectMatMulVec B (fun j => y j - x j) =
      fun i => ((-rectMatMulVec DeltaA x i + Deltab i) + r i) - s i := by
  ext i
  have hdiff := congrFun (rectMatMulVec_sub B y x) i
  have hBx :
      rectMatMulVec B x i =
        rectMatMulVec A x i + rectMatMulVec DeltaA x i := by
    rw [hB]
    exact congrFun (rectMatMulVec_mat_add A DeltaA x) i
  have hri : r i = b i - rectMatMulVec A x i := by
    simpa using congrFun hr i
  have hsi : s i = (b i + Deltab i) - rectMatMulVec B y i := by
    simpa using congrFun hs i
  rw [hdiff, hBx, hri, hsi]
  ring

/-- Higham, 2nd ed., Chapter 20, Wedin proof line toward (20.33):
    solution-difference norm bound after deriving the source
    `B*(y-x) = -ΔA*x + Δb + r - s` equation from the residual definitions.

The remaining visible `P_B s = 0` hypothesis is the perturbed least-squares
orthogonality condition and is not hidden inside the residual algebra. -/
theorem wedinTheorem20_1_vecNorm2_solution_difference_le_of_residual_definitions
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (b Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {Aplus_norm delta eta DeltaA_norm Deltab_norm : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBplus :
      rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)))
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (hproj_s : rectMatMulVec (rectMatMul B Bplus) s = 0) :
    vecNorm2 (fun j => y j - x j) ≤
      (Aplus_norm / (1 - eta)) *
          (DeltaA_norm * vecNorm2 x + Deltab_norm) +
        (eta * Aplus_norm / (1 - eta) ^ 2) * vecNorm2 r := by
  have hBdiff :
      rectMatMulVec B (fun j => y j - x j) =
        fun i => ((-rectMatMulVec DeltaA x i + Deltab i) + r i) - s i :=
    wedinTheorem20_1_B_mul_solution_difference_eq_forcing_residual_sub_of_residuals
      A B DeltaA b Deltab r s x y hB hr hs
  exact
    wedinTheorem20_1_vecNorm2_solution_difference_le_of_B_mul_sub_residual
      A B Aplus Bplus DeltaA Deltab r s x y hAplus_pos heta hsmall
      hleftA hleftB hSymA hSymB hDelta hBplus hDeltaA hDeltab
      hrangeA_residual hBdiff hproj_s

/-- Higham, 2nd ed., Chapter 20, Wedin proof algebra:
    if the perturbed residual is orthogonal to every column of `B`, then the
    symmetric range projector `P_B = B*Bplus` annihilates it.

This is the normal-equation/least-squares optimality bridge for the explicit
projector condition used by the source-faithful `s`-residual Wedin route. -/
theorem wedinTheorem20_1_rangeProjection_perturbed_residual_eq_zero_of_column_orthogonal
    {m k : ℕ} (B : Fin m → Fin (k + 1) → ℝ)
    (Bplus : Fin (k + 1) → Fin m → ℝ) (s : Fin m → ℝ)
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (horth_s : ∀ j : Fin (k + 1), ∑ i : Fin m, B i j * s i = 0) :
    rectMatMulVec (rectMatMul B Bplus) s = 0 := by
  ext i
  unfold rectMatMulVec rectMatMul
  calc
    (∑ l : Fin m, (∑ j : Fin (k + 1), B i j * Bplus j l) * s l)
        = ∑ l : Fin m, (∑ j : Fin (k + 1), B l j * Bplus j i) * s l := by
            apply Finset.sum_congr rfl
            intro l _
            have hentry :
                (∑ j : Fin (k + 1), B i j * Bplus j l) =
                  ∑ j : Fin (k + 1), B l j * Bplus j i := by
              simpa [rectMatMul] using hSymB i l
            rw [hentry]
    _ = ∑ l : Fin m, ∑ j : Fin (k + 1),
          (B l j * Bplus j i) * s l := by
            apply Finset.sum_congr rfl
            intro l _
            rw [Finset.sum_mul]
    _ = ∑ j : Fin (k + 1), ∑ l : Fin m,
          (B l j * Bplus j i) * s l := by
            rw [Finset.sum_comm]
    _ = ∑ j : Fin (k + 1), Bplus j i * (∑ l : Fin m, B l j * s l) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro l _
            ring
    _ = 0 := by
            apply Finset.sum_eq_zero
            intro j _
            rw [horth_s j]
            ring

/-- Higham, 2nd ed., Chapter 20, Wedin proof line toward (20.33):
    solution-difference norm bound using the residual definitions and the
    normal-equation column-orthogonality form of perturbed least-squares
    optimality.

This removes the raw `P_B s = 0` hypothesis from the caller-facing vector
route; the remaining scalar work is the printed relative normalization. -/
theorem wedinTheorem20_1_vecNorm2_solution_difference_le_of_residual_definitions_column_orthogonal
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (b Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {Aplus_norm delta eta DeltaA_norm Deltab_norm : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBplus :
      rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)))
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (horth_s : ∀ j : Fin (k + 1), ∑ i : Fin m, B i j * s i = 0) :
    vecNorm2 (fun j => y j - x j) ≤
      (Aplus_norm / (1 - eta)) *
          (DeltaA_norm * vecNorm2 x + Deltab_norm) +
        (eta * Aplus_norm / (1 - eta) ^ 2) * vecNorm2 r := by
  have hproj_s : rectMatMulVec (rectMatMul B Bplus) s = 0 :=
    wedinTheorem20_1_rangeProjection_perturbed_residual_eq_zero_of_column_orthogonal
      B Bplus s hSymB horth_s
  exact
    wedinTheorem20_1_vecNorm2_solution_difference_le_of_residual_definitions
      A B Aplus Bplus DeltaA b Deltab r s x y hAplus_pos heta hsmall
      hleftA hleftB hSymA hSymB hDelta hBplus hDeltaA hDeltab
      hrangeA_residual hB hr hs hproj_s

/-- Higham, 2nd ed., Chapter 20, proof of Theorem 20.1:
    source-strength residual-transfer estimate for the solution side.

If the full Lemma 20.12 projector route has supplied
`||P_B(I-P_A)||₂ <= delta * ||Aplus||₂`, then the source algebra
`Bplus*r = Bplus*P_B*(I-P_A)*r` controls `Bplus*r` with only one later
`Bplus` radius.  This is the vector step needed to remove the conservative
extra denominator from the solution bound. -/
theorem wedinTheorem20_1_vecNorm2_Bplus_residual_le_projector_bound
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {delta Aplus_norm Bplus_norm : ℝ} (r : Fin m → ℝ)
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hPBIPA :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * Aplus_norm))
    (hBplus_norm_nonneg : 0 ≤ Bplus_norm)
    (hBplus : rectOpNorm2Le Bplus Bplus_norm)
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0) :
    vecNorm2 (rectMatMulVec Bplus r) ≤
      Bplus_norm * ((delta * Aplus_norm) * vecNorm2 r) := by
  let PA : Fin m → Fin m → ℝ := rectMatMul A Aplus
  let PB : Fin m → Fin m → ℝ := rectMatMul B Bplus
  let IPA : Fin m → Fin m → ℝ :=
    fun i j => idMatrix m i j - PA i j
  have hBplusPB : rectMatMul Bplus PB = Bplus := by
    calc
      rectMatMul Bplus PB = rectMatMul Bplus (rectMatMul B Bplus) := by
        rfl
      _ = rectMatMul (rectMatMul Bplus B) Bplus := by
        rw [rectMatMul_assoc]
      _ = rectMatMul (idMatrix (k + 1)) Bplus := by
        rw [hleftB]
      _ = Bplus := rectMatMul_id_left Bplus
  have hIPA_r : rectMatMulVec IPA r = r := by
    rw [show IPA = (fun i j => idMatrix m i j - rectMatMul A Aplus i j) by
      ext i j
      rfl]
    rw [wedinLemma20_12_rectMatMulVec_projectionComplement]
    rw [hrangeA_residual]
    ext i
    simp
  have hfactor :
      rectMatMulVec Bplus r =
        rectMatMulVec Bplus (rectMatMulVec (rectMatMul PB IPA) r) := by
    symm
    calc
      rectMatMulVec Bplus (rectMatMulVec (rectMatMul PB IPA) r)
          = rectMatMulVec Bplus
              (rectMatMulVec PB (rectMatMulVec IPA r)) := by
              rw [rectMatMulVec_rectMatMul]
      _ = rectMatMulVec Bplus (rectMatMulVec PB r) := by
              rw [hIPA_r]
      _ = rectMatMulVec (rectMatMul Bplus PB) r := by
              rw [← rectMatMulVec_rectMatMul]
      _ = rectMatMulVec Bplus r := by
              rw [hBplusPB]
  have hPBIPA_r :
      vecNorm2 (rectMatMulVec (rectMatMul PB IPA) r) ≤
        (delta * Aplus_norm) * vecNorm2 r := by
    simpa [PA, PB, IPA] using hPBIPA r
  have hBplus_y := hBplus (rectMatMulVec (rectMatMul PB IPA) r)
  calc
    vecNorm2 (rectMatMulVec Bplus r)
        = vecNorm2
            (rectMatMulVec Bplus (rectMatMulVec (rectMatMul PB IPA) r)) := by
            rw [hfactor]
    _ ≤ Bplus_norm * vecNorm2 (rectMatMulVec (rectMatMul PB IPA) r) :=
            hBplus_y
    _ ≤ Bplus_norm * ((delta * Aplus_norm) * vecNorm2 r) :=
            mul_le_mul_of_nonneg_left hPBIPA_r hBplus_norm_nonneg

/-- Higham, 2nd ed., Chapter 20, proof of Theorem 20.1:
    `η`-scaled source-strength residual-transfer estimate for the solution
    side.  Compared with the conservative one-sided route, the residual term
    has a single `1 - η` denominator. -/
theorem wedinTheorem20_1_vecNorm2_Bplus_residual_le_projector_bound_eta
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {Aplus_norm delta eta : ℝ} (r : Fin m → ℝ)
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hPBIPA :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * Aplus_norm))
    (hBplus :
      rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)))
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0) :
    vecNorm2 (rectMatMulVec Bplus r) ≤
      (eta * Aplus_norm / (1 - eta)) * vecNorm2 r := by
  have hden_pos : 0 < 1 - eta :=
    wedinLemma20_11_denominator_pos hsmall
  have hBplus_radius_nonneg : 0 ≤ Aplus_norm / (1 - eta) :=
    div_nonneg (le_of_lt hAplus_pos) (le_of_lt hden_pos)
  have hbound :=
    wedinTheorem20_1_vecNorm2_Bplus_residual_le_projector_bound
      A B Aplus Bplus r hleftB hPBIPA hBplus_radius_nonneg hBplus
      hrangeA_residual
  have hden_rewrite_ne : 1 - Aplus_norm * delta ≠ 0 := by
    rw [← heta]
    exact (ne_of_gt hden_pos)
  have hcoeff :
      (Aplus_norm / (1 - eta)) *
          ((delta * Aplus_norm) * vecNorm2 r) =
        (eta * Aplus_norm / (1 - eta)) * vecNorm2 r := by
    rw [heta]
    field_simp [hden_rewrite_ne]
  simpa [hcoeff] using hbound

/-- Higham, 2nd ed., Chapter 20, proof of Theorem 20.1:
    source-strength vector assembly for the Wedin solution perturbation
    estimate.  The supplied projector estimate is the remaining full
    Lemma 20.12 dependency. -/
theorem wedinTheorem20_1_vecNorm2_Bplus_forcing_add_residual_le_projector_bound
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (Deltab r : Fin m → ℝ)
    (x : Fin (k + 1) → ℝ)
    {Aplus_norm delta eta DeltaA_norm Deltab_norm : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hPBIPA :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * Aplus_norm))
    (hBplus :
      rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)))
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0) :
    vecNorm2
        (fun j =>
          rectMatMulVec Bplus
              (fun i => -rectMatMulVec DeltaA x i + Deltab i) j +
            rectMatMulVec Bplus r j) ≤
      (Aplus_norm / (1 - eta)) *
          (DeltaA_norm * vecNorm2 x + Deltab_norm) +
        (eta * Aplus_norm / (1 - eta)) * vecNorm2 r := by
  have hden_pos : 0 < 1 - eta :=
    wedinLemma20_11_denominator_pos hsmall
  have hBplus_radius_nonneg : 0 ≤ Aplus_norm / (1 - eta) :=
    div_nonneg (le_of_lt hAplus_pos) (le_of_lt hden_pos)
  have hforcing :
      vecNorm2
          (rectMatMulVec Bplus
            (fun i => -rectMatMulVec DeltaA x i + Deltab i)) ≤
        (Aplus_norm / (1 - eta)) *
          (DeltaA_norm * vecNorm2 x + Deltab_norm) :=
    wedinTheorem20_1_vecNorm2_Bplus_forcing_le
      Bplus DeltaA Deltab x hBplus_radius_nonneg hBplus hDeltaA hDeltab
  have hresidual :
      vecNorm2 (rectMatMulVec Bplus r) ≤
        (eta * Aplus_norm / (1 - eta)) * vecNorm2 r :=
    wedinTheorem20_1_vecNorm2_Bplus_residual_le_projector_bound_eta
      A B Aplus Bplus r hAplus_pos heta hsmall hleftB hPBIPA hBplus
      hrangeA_residual
  calc
    vecNorm2
        (fun j =>
          rectMatMulVec Bplus
              (fun i => -rectMatMulVec DeltaA x i + Deltab i) j +
            rectMatMulVec Bplus r j)
        ≤ vecNorm2
            (rectMatMulVec Bplus
              (fun i => -rectMatMulVec DeltaA x i + Deltab i)) +
          vecNorm2 (rectMatMulVec Bplus r) := by
            exact vecNorm2_add_le
              (rectMatMulVec Bplus
                (fun i => -rectMatMulVec DeltaA x i + Deltab i))
              (rectMatMulVec Bplus r)
    _ ≤ (Aplus_norm / (1 - eta)) *
            (DeltaA_norm * vecNorm2 x + Deltab_norm) +
          (eta * Aplus_norm / (1 - eta)) * vecNorm2 r :=
            add_le_add hforcing hresidual

/-- Higham, 2nd ed., Chapter 20, proof of Theorem 20.1:
    source-strength assembled bound with the combined vector
    `-DeltaA*x + Deltab + r` inside the single `Bplus` action. -/
theorem wedinTheorem20_1_vecNorm2_Bplus_combined_forcing_residual_le_projector_bound
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (Deltab r : Fin m → ℝ)
    (x : Fin (k + 1) → ℝ)
    {Aplus_norm delta eta DeltaA_norm Deltab_norm : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hPBIPA :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * Aplus_norm))
    (hBplus :
      rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)))
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0) :
    vecNorm2
        (rectMatMulVec Bplus
          (fun i => (-rectMatMulVec DeltaA x i + Deltab i) + r i)) ≤
      (Aplus_norm / (1 - eta)) *
          (DeltaA_norm * vecNorm2 x + Deltab_norm) +
        (eta * Aplus_norm / (1 - eta)) * vecNorm2 r := by
  have hsum :=
    wedinTheorem20_1_vecNorm2_Bplus_forcing_add_residual_le_projector_bound
      A B Aplus Bplus DeltaA Deltab r x hAplus_pos heta hsmall
      hleftB hPBIPA hBplus hDeltaA hDeltab hrangeA_residual
  have hsplit :
      rectMatMulVec Bplus
          (fun i => (-rectMatMulVec DeltaA x i + Deltab i) + r i) =
        fun j =>
          rectMatMulVec Bplus
              (fun i => -rectMatMulVec DeltaA x i + Deltab i) j +
            rectMatMulVec Bplus r j := by
    simpa using
      rectMatMulVec_add Bplus
        (fun i : Fin m => -rectMatMulVec DeltaA x i + Deltab i) r
  simpa [hsplit] using hsum

/-- Higham, 2nd ed., Chapter 20, proof of Theorem 20.1:
    source-strength solution-difference vector bound using residual
    definitions and perturbed normal-equation orthogonality. -/
theorem wedinTheorem20_1_vecNorm2_solution_difference_le_of_residual_definitions_projector_bound_column_orthogonal
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (b Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {Aplus_norm delta eta DeltaA_norm Deltab_norm : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hPBIPA :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * Aplus_norm))
    (hBplus :
      rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)))
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (horth_s : ∀ j : Fin (k + 1), ∑ i : Fin m, B i j * s i = 0) :
    vecNorm2 (fun j => y j - x j) ≤
      (Aplus_norm / (1 - eta)) *
          (DeltaA_norm * vecNorm2 x + Deltab_norm) +
        (eta * Aplus_norm / (1 - eta)) * vecNorm2 r := by
  have hproj_s : rectMatMulVec (rectMatMul B Bplus) s = 0 :=
    wedinTheorem20_1_rangeProjection_perturbed_residual_eq_zero_of_column_orthogonal
      B Bplus s hSymB horth_s
  have hBdiff :
      rectMatMulVec B (fun j => y j - x j) =
        fun i => ((-rectMatMulVec DeltaA x i + Deltab i) + r i) - s i :=
    wedinTheorem20_1_B_mul_solution_difference_eq_forcing_residual_sub_of_residuals
      A B DeltaA b Deltab r s x y hB hr hs
  have hdiff_eq :
      (fun j => y j - x j) =
        rectMatMulVec Bplus
          (fun i => (-rectMatMulVec DeltaA x i + Deltab i) + r i) :=
    wedinTheorem20_1_solution_difference_eq_Bplus_combined_of_B_mul_sub_residual
      B Bplus DeltaA Deltab r s x y hleftB hBdiff hproj_s
  rw [hdiff_eq]
  exact
    wedinTheorem20_1_vecNorm2_Bplus_combined_forcing_residual_le_projector_bound
      A B Aplus Bplus DeltaA Deltab r x hAplus_pos heta hsmall
      hleftB hPBIPA hBplus hDeltaA hDeltab hrangeA_residual

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.1):
    printed relative solution perturbation bound, conditional on the
    source-strength Lemma 20.12 projector estimate.

This theorem removes the conservative extra denominator from the solution
RHS once `||P_B(I-P_A)||₂ <= delta * ||Aplus||₂` is supplied.  The remaining
chapter-level work is to prove that projector estimate from the full
Lemma 20.12 equality/min surface. -/
theorem wedinTheorem20_1_solutionRelativeRHS_le_of_residual_definitions_projector_bound_column_orthogonal
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (b Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {Aplus_norm delta eta DeltaA_norm Deltab_norm kappa eps A_norm : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (hA_norm_pos : 0 < A_norm)
    (hx_norm_pos : 0 < vecNorm2 x)
    (hkappa : kappa = Aplus_norm * A_norm)
    (hdelta : delta = eps * A_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hPBIPA :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * Aplus_norm))
    (hBplus :
      rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)))
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hDeltaA_norm_budget : DeltaA_norm ≤ eps * A_norm)
    (hDeltab_norm_budget :
      Deltab_norm ≤ eps * (A_norm * vecNorm2 x + vecNorm2 r))
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (horth_s : ∀ j : Fin (k + 1), ∑ i : Fin m, B i j * s i = 0) :
    vecNorm2 (fun j => y j - x j) / vecNorm2 x ≤
      wedinTheorem20_1SolutionRelativeRHS
        kappa eps A_norm (vecNorm2 x) (vecNorm2 r) := by
  have hvec :
      vecNorm2 (fun j => y j - x j) ≤
        (Aplus_norm / (1 - eta)) *
            (DeltaA_norm * vecNorm2 x + Deltab_norm) +
          (eta * Aplus_norm / (1 - eta)) * vecNorm2 r :=
    wedinTheorem20_1_vecNorm2_solution_difference_le_of_residual_definitions_projector_bound_column_orthogonal
      A B Aplus Bplus DeltaA b Deltab r s x y hAplus_pos heta hsmall
      hleftB hSymB hPBIPA hBplus hDeltaA hDeltab hrangeA_residual
      hB hr hs horth_s
  have heta_scalar : eta = kappa * eps := by
    rw [heta, hdelta, hkappa]
    ring
  have hsmall_scalar : kappa * eps < 1 := by
    rw [← heta_scalar]
    exact hsmall
  exact
    wedinTheorem20_1_solutionRelativeRHS_of_vector_bound
      (hAplus_nonneg := le_of_lt hAplus_pos)
      (hA_norm_pos := hA_norm_pos)
      (hx_norm_pos := hx_norm_pos)
      (hkappa := hkappa)
      (heta := heta_scalar)
      (hsmall := hsmall_scalar)
      (hDeltaA_norm := hDeltaA_norm_budget)
      (hDeltab_norm := hDeltab_norm_budget)
      (hvec := hvec)

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.1):
    printed relative solution perturbation bound, conditional only on the
    exact cross-projection norm equality from the open Stewart--Sun/CS route.

This wrapper derives the source-strength `P_B(I-P_A)` projector estimate from
the exact `complexMatrixOp2` equality and then calls the already formalized
Wedin solution algebra.  It does not prove the equality itself. -/
theorem wedinTheorem20_1_solutionRelativeRHS_le_of_residual_definitions_crossProjection_eq_column_orthogonal
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (b Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {Aplus_norm delta eta DeltaA_norm Deltab_norm kappa eps A_norm : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (hA_norm_pos : 0 < A_norm)
    (hx_norm_pos : 0 < vecNorm2 x)
    (hkappa : kappa = Aplus_norm * A_norm)
    (hdelta : delta = eps * A_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hBplus :
      rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)))
    (hEq :
      complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul
              (rectMatMul B Bplus)
              (fun i j => idMatrix m i j - rectMatMul A Aplus i j))) =
        complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul
              (rectMatMul A Aplus)
              (fun i j => idMatrix m i j - rectMatMul B Bplus i j))))
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hDeltaA_norm_budget : DeltaA_norm ≤ eps * A_norm)
    (hDeltab_norm_budget :
      Deltab_norm ≤ eps * (A_norm * vecNorm2 x + vecNorm2 r))
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (horth_s : ∀ j : Fin (k + 1), ∑ i : Fin m, B i j * s i = 0) :
    vecNorm2 (fun j => y j - x j) / vecNorm2 x ≤
      wedinTheorem20_1SolutionRelativeRHS
        kappa eps A_norm (vecNorm2 x) (vecNorm2 r) := by
  have hPBIPA :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * Aplus_norm) :=
    wedinLemma20_12_rectOpNorm2Le_rangeProjection_mul_projectionComplement_swapped_of_complexMatrixOp2_eq
      A B Aplus Bplus hleftB hSymA hSymB hDelta (le_of_lt hAplus_pos)
      hAplus hEq
  exact
    wedinTheorem20_1_solutionRelativeRHS_le_of_residual_definitions_projector_bound_column_orthogonal
      A B Aplus Bplus DeltaA b Deltab r s x y hAplus_pos hA_norm_pos
      hx_norm_pos hkappa hdelta heta hsmall hleftB hSymB hPBIPA hBplus
      hDeltaA hDeltab hDeltaA_norm_budget hDeltab_norm_budget
      hrangeA_residual hB hr hs horth_s

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.1):
    printed relative solution perturbation bound using the source-facing
    Lemma 20.12 `min` projector surface.

This removes the old caller-facing cross-projection equality hypothesis by
combining Lemma 20.11's `Bplus` radius with the proved Lemma 20.12 bound
`||P_B(I-P_A)||₂ <= delta * min(||Aplus||₂, ||Bplus||₂)`. -/
theorem wedinTheorem20_1_solutionRelativeRHS_le_of_residual_definitions_min_surface_column_orthogonal
    {m k : ℕ} (hm : 0 < m) (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (b Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {Aplus_norm delta eta DeltaA_norm Deltab_norm kappa eps A_norm : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (hA_norm_pos : 0 < A_norm)
    (hx_norm_pos : 0 < vecNorm2 x)
    (hkappa : kappa = Aplus_norm * A_norm)
    (hdelta : delta = eps * A_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hDeltaA_norm_budget : DeltaA_norm ≤ eps * A_norm)
    (hDeltab_norm_budget :
      Deltab_norm ≤ eps * (A_norm * vecNorm2 x + vecNorm2 r))
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (horth_s : ∀ j : Fin (k + 1), ∑ i : Fin m, B i j * s i = 0) :
    vecNorm2 (fun j => y j - x j) / vecNorm2 x ≤
      wedinTheorem20_1SolutionRelativeRHS
        kappa eps A_norm (vecNorm2 x) (vecNorm2 r) := by
  have hBplus :
      rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)) :=
    wedinLemma20_11_rectOpNorm2Le_Bplus_of_left_inverse_rectOpNorm2Le
      A B Aplus Bplus hAplus_pos heta hsmall hleftA hAplus hDelta
      hleftB hSymB
  have hden_pos : 0 < 1 - eta :=
    wedinLemma20_11_denominator_pos hsmall
  have hBplus_radius_nonneg : 0 ≤ Aplus_norm / (1 - eta) :=
    div_nonneg (le_of_lt hAplus_pos) (le_of_lt hden_pos)
  have hPBIPA_min :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * min Aplus_norm (Aplus_norm / (1 - eta))) :=
    wedinLemma20_12_rectOpNorm2Le_rangeProjection_mul_projectionComplement_swapped_min
      hm A B Aplus Bplus hleftA hleftB hSymA hSymB hDelta
      (le_of_lt hAplus_pos) hBplus_radius_nonneg hAplus hBplus
  have hdelta_nonneg : 0 ≤ delta :=
    rectOpNorm2Le_radius_nonneg (M := fun i j => B i j - A i j) hDelta
  have hPBIPA :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * Aplus_norm) :=
    rectOpNorm2Le_mono
      (mul_le_mul_of_nonneg_left
        (min_le_left Aplus_norm (Aplus_norm / (1 - eta))) hdelta_nonneg)
      hPBIPA_min
  exact
    wedinTheorem20_1_solutionRelativeRHS_le_of_residual_definitions_projector_bound_column_orthogonal
      A B Aplus Bplus DeltaA b Deltab r s x y hAplus_pos hA_norm_pos
      hx_norm_pos hkappa hdelta heta hsmall hleftB hSymB hPBIPA hBplus
      hDeltaA hDeltab hDeltaA_norm_budget hDeltab_norm_budget
      hrangeA_residual hB hr hs horth_s

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.1), conservative
    relative solution perturbation bound assembled from the currently proved
    Wedin vector route.

The result uses residual definitions, normal-equation column orthogonality for
the perturbed residual, relative perturbation budgets, and `kappa =
Aplus_norm*A_norm`.  The conclusion is the conservative scalar RHS rather than
the printed (20.1) RHS because the residual-transfer path still carries the
extra one-sided Lemma 20.12 denominator. -/
theorem wedinTheorem20_1_solutionRelativeRHSConservative_le_of_residual_definitions_column_orthogonal
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (b Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {Aplus_norm delta eta DeltaA_norm Deltab_norm kappa eps A_norm : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (hA_norm_pos : 0 < A_norm)
    (hx_norm_pos : 0 < vecNorm2 x)
    (hkappa : kappa = Aplus_norm * A_norm)
    (hdelta : delta = eps * A_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBplus :
      rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)))
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hDeltaA_norm_budget : DeltaA_norm ≤ eps * A_norm)
    (hDeltab_norm_budget :
      Deltab_norm ≤ eps * (A_norm * vecNorm2 x + vecNorm2 r))
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (horth_s : ∀ j : Fin (k + 1), ∑ i : Fin m, B i j * s i = 0) :
    vecNorm2 (fun j => y j - x j) / vecNorm2 x ≤
      wedinTheorem20_1SolutionRelativeRHSConservative
        kappa eps A_norm (vecNorm2 x) (vecNorm2 r) := by
  have hvec :
      vecNorm2 (fun j => y j - x j) ≤
        (Aplus_norm / (1 - eta)) *
            (DeltaA_norm * vecNorm2 x + Deltab_norm) +
          (eta * Aplus_norm / (1 - eta) ^ 2) * vecNorm2 r :=
    wedinTheorem20_1_vecNorm2_solution_difference_le_of_residual_definitions_column_orthogonal
      A B Aplus Bplus DeltaA b Deltab r s x y hAplus_pos heta hsmall
      hleftA hleftB hSymA hSymB hDelta hBplus hDeltaA hDeltab
      hrangeA_residual hB hr hs horth_s
  have heta_scalar : eta = kappa * eps := by
    rw [heta, hdelta, hkappa]
    ring
  have hsmall_scalar : kappa * eps < 1 := by
    rw [← heta_scalar]
    exact hsmall
  exact
    wedinTheorem20_1_solutionRelativeRHSConservative_of_vector_bound
      (hAplus_nonneg := le_of_lt hAplus_pos)
      (hA_norm_pos := hA_norm_pos)
      (hx_norm_pos := hx_norm_pos)
      (hkappa := hkappa)
      (heta := heta_scalar)
      (hsmall := hsmall_scalar)
      (hDeltaA_norm := hDeltaA_norm_budget)
      (hDeltab_norm := hDeltab_norm_budget)
      (hvec := hvec)

/-- Higham, 2nd ed., Chapter 20, proof of Theorem 20.1, residual side:
    residual algebra after substituting the Wedin solution-difference identity.

This is the formal version of
`s - r = (I - B Bplus) (Delta b - Delta A*x) - B Bplus*r`. -/
theorem wedinTheorem20_1_residual_difference_eq_projection_decomp
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (b Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (hproj_s : rectMatMulVec (rectMatMul B Bplus) s = 0) :
    (fun i => s i - r i) =
      fun i =>
        rectMatMulVec
            (fun i j => idMatrix m i j - rectMatMul B Bplus i j)
            (fun i => Deltab i - rectMatMulVec DeltaA x i) i -
          rectMatMulVec (rectMatMul B Bplus) r i := by
  let PB : Fin m → Fin m → ℝ := rectMatMul B Bplus
  let IPB : Fin m → Fin m → ℝ :=
    fun i j => idMatrix m i j - PB i j
  let q : Fin m → ℝ := fun i => Deltab i - rectMatMulVec DeltaA x i
  let combined : Fin m → ℝ :=
    fun i => (-rectMatMulVec DeltaA x i + Deltab i) + r i
  have hBdiff :
      rectMatMulVec B (fun j => y j - x j) =
        fun i => ((-rectMatMulVec DeltaA x i + Deltab i) + r i) - s i :=
    wedinTheorem20_1_B_mul_solution_difference_eq_forcing_residual_sub_of_residuals
      A B DeltaA b Deltab r s x y hB hr hs
  have hdiff :
      (fun j => y j - x j) =
        rectMatMulVec Bplus combined :=
    wedinTheorem20_1_solution_difference_eq_Bplus_combined_of_B_mul_sub_residual
      B Bplus DeltaA Deltab r s x y hleftB hBdiff hproj_s
  have hB_yx :
      rectMatMulVec B (fun j => y j - x j) =
        rectMatMulVec PB combined := by
    calc
      rectMatMulVec B (fun j => y j - x j)
          = rectMatMulVec B (rectMatMulVec Bplus combined) := by
              rw [hdiff]
      _ = rectMatMulVec PB combined := by
              rw [rectMatMulVec_rectMatMul]
  have hcombined :
      combined = fun i => q i + r i := by
    ext i
    simp [combined, q]
    ring
  have hPB_combined :
      rectMatMulVec PB combined =
        fun i => rectMatMulVec PB q i + rectMatMulVec PB r i := by
    rw [hcombined]
    exact rectMatMulVec_add PB q r
  have hIPB_q :
      rectMatMulVec IPB q =
        fun i => q i - rectMatMulVec PB q i := by
    simpa [IPB, PB, q] using
      wedinLemma20_12_rectMatMulVec_projectionComplement PB q
  ext i
  have hsubB := congrFun (rectMatMulVec_sub B y x) i
  have hBx :
      rectMatMulVec B x i =
        rectMatMulVec A x i + rectMatMulVec DeltaA x i := by
    rw [hB]
    exact congrFun (rectMatMulVec_mat_add A DeltaA x) i
  have hri : r i = b i - rectMatMulVec A x i := by
    simpa using congrFun hr i
  have hsi : s i = (b i + Deltab i) - rectMatMulVec B y i := by
    simpa using congrFun hs i
  have hres :
      s i - r i =
        Deltab i - rectMatMulVec B (fun j => y j - x j) i -
          rectMatMulVec DeltaA x i := by
    have hBy :
        rectMatMulVec B y i =
          rectMatMulVec B (fun j => y j - x j) i + rectMatMulVec B x i := by
      linarith [hsubB]
    rw [hsi, hri, hBy, hBx]
    ring
  have hPB_combined_i :
      rectMatMulVec PB combined i =
        rectMatMulVec PB q i + rectMatMulVec PB r i := by
    exact congrFun hPB_combined i
  have hIPB_q_i :
      rectMatMulVec IPB q i = q i - rectMatMulVec PB q i := by
    exact congrFun hIPB_q i
  rw [hres, congrFun hB_yx i, hPB_combined_i, hIPB_q_i]
  simp [PB, q]
  ring

/-- Higham, 2nd ed., Chapter 20, proof of Theorem 20.1, residual side:
    vector residual-difference estimate once the source-strength projector
    estimate `||P_B(I-P_A)||₂ <= ||Delta A||₂ ||Aplus||₂` is supplied.

The supplied projector estimate is exactly the still-open full Lemma 20.12
equality/min dependency; this theorem closes the remaining residual algebra
without hiding that dependency. -/
theorem wedinTheorem20_1_vecNorm2_residual_difference_le_of_residual_definitions_projector_bound
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (b Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {delta Aplus_norm DeltaA_norm Deltab_norm : ℝ}
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hPBIPA :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * Aplus_norm))
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (hproj_s : rectMatMulVec (rectMatMul B Bplus) s = 0) :
    vecNorm2 (fun i => r i - s i) ≤
      Deltab_norm + DeltaA_norm * vecNorm2 x +
        (delta * Aplus_norm) * vecNorm2 r := by
  let PB : Fin m → Fin m → ℝ := rectMatMul B Bplus
  let IPB : Fin m → Fin m → ℝ :=
    fun i j => idMatrix m i j - PB i j
  let IPA : Fin m → Fin m → ℝ :=
    fun i j => idMatrix m i j - rectMatMul A Aplus i j
  let q : Fin m → ℝ := fun i => Deltab i - rectMatMulVec DeltaA x i
  have hdecomp :
      (fun i => s i - r i) =
        fun i => rectMatMulVec IPB q i - rectMatMulVec PB r i := by
    simpa [PB, IPB, q] using
      wedinTheorem20_1_residual_difference_eq_projection_decomp
        A B Bplus DeltaA b Deltab r s x y hleftB hB hr hs hproj_s
  have hneg :
      (fun i => r i - s i) = fun i => -(s i - r i) := by
    ext i
    ring
  have hq_norm :
      vecNorm2 q ≤ Deltab_norm + DeltaA_norm * vecNorm2 x := by
    calc
      vecNorm2 q
          ≤ vecNorm2 Deltab +
              vecNorm2 (fun i : Fin m => -rectMatMulVec DeltaA x i) := by
              simpa [q, sub_eq_add_neg] using
                vecNorm2_add_le Deltab
                  (fun i : Fin m => -rectMatMulVec DeltaA x i)
      _ = vecNorm2 Deltab + vecNorm2 (rectMatMulVec DeltaA x) := by
              rw [vecNorm2_neg]
      _ ≤ Deltab_norm + DeltaA_norm * vecNorm2 x :=
              add_le_add hDeltab (hDeltaA x)
  have hIPB :
      rectOpNorm2Le IPB 1 := by
    simpa [IPB, PB] using
      wedinLemma20_12_rectOpNorm2Le_projectionComplement_of_symmetric_left_inverse
        B Bplus hleftB hSymB
  have hIPB_q :
      vecNorm2 (rectMatMulVec IPB q) ≤
        Deltab_norm + DeltaA_norm * vecNorm2 x := by
    have h := hIPB q
    have h' : vecNorm2 (rectMatMulVec IPB q) ≤ vecNorm2 q := by
      simpa using h
    exact h'.trans hq_norm
  have hIPA_r : rectMatMulVec IPA r = r := by
    rw [show IPA = (fun i j => idMatrix m i j - rectMatMul A Aplus i j) by
      ext i j
      rfl]
    rw [wedinLemma20_12_rectMatMulVec_projectionComplement]
    rw [hrangeA_residual]
    ext i
    simp
  have hPB_r :
      vecNorm2 (rectMatMulVec PB r) ≤
        (delta * Aplus_norm) * vecNorm2 r := by
    have h := hPBIPA r
    have hPBIPA_r :
        rectMatMulVec
            (rectMatMul
              (rectMatMul B Bplus)
              (fun i j => idMatrix m i j - rectMatMul A Aplus i j)) r =
          rectMatMulVec PB r := by
      calc
        rectMatMulVec
            (rectMatMul
              (rectMatMul B Bplus)
              (fun i j => idMatrix m i j - rectMatMul A Aplus i j)) r
            = rectMatMulVec PB (rectMatMulVec IPA r) := by
                rw [rectMatMulVec_rectMatMul]
        _ = rectMatMulVec PB r := by
                rw [hIPA_r]
    simpa [hPBIPA_r] using h
  calc
    vecNorm2 (fun i => r i - s i)
        = vecNorm2 (fun i => s i - r i) := by
            rw [hneg]
            rw [vecNorm2_neg]
    _ = vecNorm2 (fun i => rectMatMulVec IPB q i - rectMatMulVec PB r i) := by
            rw [hdecomp]
    _ ≤ vecNorm2 (rectMatMulVec IPB q) +
          vecNorm2 (fun i : Fin m => -rectMatMulVec PB r i) := by
            simpa [sub_eq_add_neg] using
              vecNorm2_add_le (rectMatMulVec IPB q)
                (fun i : Fin m => -rectMatMulVec PB r i)
    _ = vecNorm2 (rectMatMulVec IPB q) +
          vecNorm2 (rectMatMulVec PB r) := by
            rw [vecNorm2_neg]
    _ ≤ (Deltab_norm + DeltaA_norm * vecNorm2 x) +
          (delta * Aplus_norm) * vecNorm2 r :=
            add_le_add hIPB_q hPB_r
    _ = Deltab_norm + DeltaA_norm * vecNorm2 x +
          (delta * Aplus_norm) * vecNorm2 r := by ring

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.2):
    scalar normalization of the residual perturbation bound from the vector
    residual estimate.

The assumptions `A_norm * ||x|| <= kappa * b_norm` and `||r|| <= b_norm`
are the LS-geometry bounds used in the source proof; the projector estimate is
kept in the vector theorem that supplies `hvec`. -/
theorem wedinTheorem20_1_residualRelativeRHS_of_vector_bound
    {res_norm DeltaA_norm Deltab_norm delta Aplus_norm kappa eps A_norm
      b_norm x_norm r_norm : ℝ}
    (hb_norm_pos : 0 < b_norm)
    (hx_norm_nonneg : 0 ≤ x_norm)
    (heps_nonneg : 0 ≤ eps)
    (hkappa_nonneg : 0 ≤ kappa)
    (hkappa : kappa = Aplus_norm * A_norm)
    (hdelta : delta = eps * A_norm)
    (hDeltaA_norm_budget : DeltaA_norm ≤ eps * A_norm)
    (hDeltab_norm_budget : Deltab_norm ≤ eps * b_norm)
    (hx_budget : A_norm * x_norm ≤ kappa * b_norm)
    (hr_budget : r_norm ≤ b_norm)
    (hvec :
      res_norm ≤ Deltab_norm + DeltaA_norm * x_norm +
        (delta * Aplus_norm) * r_norm) :
    res_norm / b_norm ≤
      wedinTheorem20_1ResidualRelativeRHS kappa eps := by
  have hDeltaA_x :
      DeltaA_norm * x_norm ≤ eps * kappa * b_norm := by
    have h1 : DeltaA_norm * x_norm ≤ (eps * A_norm) * x_norm :=
      mul_le_mul_of_nonneg_right hDeltaA_norm_budget hx_norm_nonneg
    have h2 : (eps * A_norm) * x_norm ≤ eps * (kappa * b_norm) := by
      calc
        (eps * A_norm) * x_norm = eps * (A_norm * x_norm) := by ring
        _ ≤ eps * (kappa * b_norm) :=
            mul_le_mul_of_nonneg_left hx_budget heps_nonneg
    exact h1.trans (by simpa [mul_assoc] using h2)
  have hproj_coeff : delta * Aplus_norm = eps * kappa := by
    rw [hdelta, hkappa]
    ring
  have hproj :
      (delta * Aplus_norm) * r_norm ≤ eps * kappa * b_norm := by
    rw [hproj_coeff]
    have hcoeff_nonneg : 0 ≤ eps * kappa :=
      mul_nonneg heps_nonneg hkappa_nonneg
    exact mul_le_mul_of_nonneg_left hr_budget hcoeff_nonneg
  have hscalar :
      res_norm ≤
        eps * b_norm + eps * kappa * b_norm + eps * kappa * b_norm := by
    calc
      res_norm
          ≤ Deltab_norm + DeltaA_norm * x_norm +
              (delta * Aplus_norm) * r_norm := hvec
      _ ≤ eps * b_norm + eps * kappa * b_norm +
              eps * kappa * b_norm := by
            exact add_le_add (add_le_add hDeltab_norm_budget hDeltaA_x) hproj
  calc
    res_norm / b_norm
        ≤ (eps * b_norm + eps * kappa * b_norm + eps * kappa * b_norm) /
            b_norm := div_le_div_of_nonneg_right hscalar (le_of_lt hb_norm_pos)
    _ = wedinTheorem20_1ResidualRelativeRHS kappa eps := by
          unfold wedinTheorem20_1ResidualRelativeRHS
          field_simp [ne_of_gt hb_norm_pos]
          ring

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.2), conservative
    scalar normalization for the currently proved one-sided Lemma 20.12 route.

This is the residual-side analogue of
`wedinTheorem20_1_solutionRelativeRHSConservative_of_vector_bound`: the vector
bound uses the projector coefficient `delta * Aplus_norm / (1 - eta)`, so the
normalized RHS is `(1 + kappa) * eps + (kappa * eps)/(1 - kappa*eps)` rather
than the printed `(1 + 2*kappa) * eps`. -/
theorem wedinTheorem20_1_residualRelativeRHSConservative_of_vector_bound
    {res_norm b_norm Aplus_norm DeltaA_norm Deltab_norm kappa eps A_norm
      x_norm r_norm delta eta : ℝ}
    (hb_norm_pos : 0 < b_norm)
    (hx_norm_nonneg : 0 ≤ x_norm)
    (heps_nonneg : 0 ≤ eps)
    (hkappa_nonneg : 0 ≤ kappa)
    (hkappa : kappa = Aplus_norm * A_norm)
    (hdelta : delta = eps * A_norm)
    (heta : eta = kappa * eps)
    (hsmall : kappa * eps < 1)
    (hDeltaA_norm_budget : DeltaA_norm ≤ eps * A_norm)
    (hDeltab_norm_budget : Deltab_norm ≤ eps * b_norm)
    (hx_budget : A_norm * x_norm ≤ kappa * b_norm)
    (hr_budget : r_norm ≤ b_norm)
    (hvec :
      res_norm ≤ Deltab_norm + DeltaA_norm * x_norm +
        (delta * (Aplus_norm / (1 - eta))) * r_norm) :
    res_norm / b_norm ≤
      wedinTheorem20_1ResidualRelativeRHSConservative kappa eps := by
  have hden_pos : 0 < 1 - kappa * eps :=
    wedinTheorem20_1_denominator_pos hsmall
  have heta_den : 1 - eta = 1 - kappa * eps := by rw [heta]
  have hDeltaA_x :
      DeltaA_norm * x_norm ≤ eps * kappa * b_norm := by
    have h1 : DeltaA_norm * x_norm ≤ (eps * A_norm) * x_norm :=
      mul_le_mul_of_nonneg_right hDeltaA_norm_budget hx_norm_nonneg
    have h2 : (eps * A_norm) * x_norm ≤ eps * (kappa * b_norm) := by
      calc
        (eps * A_norm) * x_norm = eps * (A_norm * x_norm) := by ring
        _ ≤ eps * (kappa * b_norm) :=
            mul_le_mul_of_nonneg_left hx_budget heps_nonneg
    exact h1.trans (by simpa [mul_assoc] using h2)
  have hproj_coeff :
      delta * (Aplus_norm / (1 - eta)) =
        (kappa * eps) / (1 - kappa * eps) := by
    rw [hdelta, heta_den]
    calc
      eps * A_norm * (Aplus_norm / (1 - kappa * eps))
          = (eps * A_norm * Aplus_norm) / (1 - kappa * eps) := by ring
      _ = (kappa * eps) / (1 - kappa * eps) := by
          have hnum : eps * A_norm * Aplus_norm = kappa * eps := by
            rw [hkappa]
            ring
          rw [hnum]
  have hproj :
      (delta * (Aplus_norm / (1 - eta))) * r_norm ≤
        ((kappa * eps) / (1 - kappa * eps)) * b_norm := by
    rw [hproj_coeff]
    have hcoeff_nonneg : 0 ≤ (kappa * eps) / (1 - kappa * eps) :=
      div_nonneg (mul_nonneg hkappa_nonneg heps_nonneg) (le_of_lt hden_pos)
    exact mul_le_mul_of_nonneg_left hr_budget hcoeff_nonneg
  have hscalar :
      res_norm ≤
        eps * b_norm + eps * kappa * b_norm +
          ((kappa * eps) / (1 - kappa * eps)) * b_norm := by
    calc
      res_norm
          ≤ Deltab_norm + DeltaA_norm * x_norm +
              (delta * (Aplus_norm / (1 - eta))) * r_norm := hvec
      _ ≤ eps * b_norm + eps * kappa * b_norm +
              ((kappa * eps) / (1 - kappa * eps)) * b_norm := by
            exact add_le_add (add_le_add hDeltab_norm_budget hDeltaA_x) hproj
  calc
    res_norm / b_norm
        ≤ (eps * b_norm + eps * kappa * b_norm +
            ((kappa * eps) / (1 - kappa * eps)) * b_norm) / b_norm :=
          div_le_div_of_nonneg_right hscalar (le_of_lt hb_norm_pos)
    _ = wedinTheorem20_1ResidualRelativeRHSConservative kappa eps := by
          unfold wedinTheorem20_1ResidualRelativeRHSConservative
          field_simp [ne_of_gt hb_norm_pos, ne_of_gt hden_pos]

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.2):
    residual perturbation bound assembled from residual definitions and the
    source-strength projector estimate used in the proof of Wedin's theorem.

This closes the residual side modulo the same full Lemma 20.12
`P_B(I-P_A)` estimate needed by the printed solution bound. -/
theorem wedinTheorem20_1_residualRelativeRHS_le_of_residual_definitions_projector_bound
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (b Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {delta Aplus_norm DeltaA_norm Deltab_norm kappa eps A_norm : ℝ}
    (hb_norm_pos : 0 < vecNorm2 b)
    (heps_nonneg : 0 ≤ eps)
    (hkappa_nonneg : 0 ≤ kappa)
    (hkappa : kappa = Aplus_norm * A_norm)
    (hdelta : delta = eps * A_norm)
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hDeltaA_norm_budget : DeltaA_norm ≤ eps * A_norm)
    (hDeltab_norm_budget : Deltab_norm ≤ eps * vecNorm2 b)
    (hx_budget : A_norm * vecNorm2 x ≤ kappa * vecNorm2 b)
    (hr_budget : vecNorm2 r ≤ vecNorm2 b)
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hPBIPA :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * Aplus_norm))
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (hproj_s : rectMatMulVec (rectMatMul B Bplus) s = 0) :
    vecNorm2 (fun i => r i - s i) / vecNorm2 b ≤
      wedinTheorem20_1ResidualRelativeRHS kappa eps := by
  have hvec :
      vecNorm2 (fun i => r i - s i) ≤
        Deltab_norm + DeltaA_norm * vecNorm2 x +
          (delta * Aplus_norm) * vecNorm2 r :=
    wedinTheorem20_1_vecNorm2_residual_difference_le_of_residual_definitions_projector_bound
      A B Aplus Bplus DeltaA b Deltab r s x y hleftB hSymB
      hDeltaA hDeltab hrangeA_residual hPBIPA hB hr hs hproj_s
  exact
    wedinTheorem20_1_residualRelativeRHS_of_vector_bound
      (hb_norm_pos := hb_norm_pos)
      (hx_norm_nonneg := vecNorm2_nonneg x)
      (heps_nonneg := heps_nonneg)
      (hkappa_nonneg := hkappa_nonneg)
      (hkappa := hkappa)
      (hdelta := hdelta)
      (hDeltaA_norm_budget := hDeltaA_norm_budget)
      (hDeltab_norm_budget := hDeltab_norm_budget)
      (hx_budget := hx_budget)
      (hr_budget := hr_budget)
      (hvec := hvec)

/-- Higham, 2nd ed., Chapter 20, proof of Theorem 20.1:
    the exact least-squares residual orthogonality and residual definition
    identify the solution as `Aplus*b`. -/
theorem wedinTheorem20_1_solution_eq_Aplus_b_of_residual_definition
    {m k : ℕ} (A : Fin m → Fin (k + 1) → ℝ)
    (Aplus : Fin (k + 1) → Fin m → ℝ)
    (b r : Fin m → ℝ) (x : Fin (k + 1) → ℝ)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hr : r = fun i => b i - rectMatMulVec A x i) :
    x = rectMatMulVec Aplus b := by
  have hAplusPA : rectMatMul Aplus (rectMatMul A Aplus) = Aplus := by
    calc
      rectMatMul Aplus (rectMatMul A Aplus)
          = rectMatMul (rectMatMul Aplus A) Aplus := by
              rw [rectMatMul_assoc]
      _ = rectMatMul (idMatrix (k + 1)) Aplus := by
              rw [hleftA]
      _ = Aplus := rectMatMul_id_left Aplus
  have hAplus_r : rectMatMulVec Aplus r = 0 := by
    calc
      rectMatMulVec Aplus r
          = rectMatMulVec (rectMatMul Aplus (rectMatMul A Aplus)) r := by
              rw [hAplusPA]
      _ = rectMatMulVec Aplus (rectMatMulVec (rectMatMul A Aplus) r) := by
              rw [rectMatMulVec_rectMatMul]
      _ = 0 := by
              rw [hrangeA_residual]
              ext j
              simp [rectMatMulVec]
  have hb_decomp : b = fun i => rectMatMulVec A x i + r i := by
    ext i
    have hri : r i = b i - rectMatMulVec A x i := by
      simpa using congrFun hr i
    linarith
  symm
  calc
    rectMatMulVec Aplus b
        = rectMatMulVec Aplus
            (fun i => rectMatMulVec A x i + r i) := by
            rw [hb_decomp]
    _ = fun j =>
          rectMatMulVec Aplus (rectMatMulVec A x) j +
            rectMatMulVec Aplus r j := by
            rw [rectMatMulVec_add]
    _ = rectMatMulVec Aplus (rectMatMulVec A x) := by
            rw [hAplus_r]
            ext j
            simp
    _ = rectMatMulVec (rectMatMul Aplus A) x := by
            rw [rectMatMulVec_rectMatMul]
    _ = rectMatMulVec (idMatrix (k + 1)) x := by
            rw [hleftA]
    _ = x := rectMatMulVec_idMatrix x

/-- Higham, 2nd ed., Chapter 20, proof of Theorem 20.1:
    exact least-squares residuals are no larger than the right-hand side in
    Euclidean norm. -/
theorem wedinTheorem20_1_vecNorm2_residual_le_b_of_residual_definition
    {m k : ℕ} (A : Fin m → Fin (k + 1) → ℝ)
    (Aplus : Fin (k + 1) → Fin m → ℝ)
    (b r : Fin m → ℝ) (x : Fin (k + 1) → ℝ)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hr : r = fun i => b i - rectMatMulVec A x i) :
    vecNorm2 r ≤ vecNorm2 b := by
  let PA : Fin m → Fin m → ℝ := rectMatMul A Aplus
  have hb_decomp : b = fun i => rectMatMulVec A x i + r i := by
    ext i
    have hri : r i = b i - rectMatMulVec A x i := by
      simpa using congrFun hr i
    linarith
  have hPA_Ax :
      rectMatMulVec PA (rectMatMulVec A x) = rectMatMulVec A x := by
    simpa [PA] using
      rectMatMulVec_rangeProjection_apply_range_of_left_inverse A Aplus
        hleftA x
  have hPA_b : rectMatMulVec PA b = rectMatMulVec A x := by
    calc
      rectMatMulVec PA b
          = rectMatMulVec PA
              (fun i => rectMatMulVec A x i + r i) := by
              rw [hb_decomp]
      _ = fun i =>
            rectMatMulVec PA (rectMatMulVec A x) i +
              rectMatMulVec PA r i := by
              rw [rectMatMulVec_add]
      _ = rectMatMulVec A x := by
              rw [hPA_Ax, show rectMatMulVec PA r = 0 by
                simpa [PA] using hrangeA_residual]
              ext i
              simp
  have hresid_eq :
      (fun i => b i - rectMatMulVec PA b i) = r := by
    ext i
    have hri : r i = b i - rectMatMulVec A x i := by
      simpa using congrFun hr i
    have hPAi : rectMatMulVec PA b i = rectMatMulVec A x i := by
      exact congrFun hPA_b i
    rw [hPAi]
    exact hri.symm
  have hzero :
      (fun i : Fin m => b i - rectMatMulVec A (fun _ : Fin (k + 1) => 0) i) =
        b := by
    ext i
    simp [rectMatMulVec]
  have hbest :=
    rectMatMulVec_rangeProjection_residual_norm_le_range_residual_of_symmetric_left_inverse
      A Aplus hleftA hSymA b (fun _ : Fin (k + 1) => 0)
  simpa [PA, hresid_eq, hzero] using hbest

/-- Higham, 2nd ed., Chapter 20, proof of Theorem 20.1:
    the source `||A|| ||x|| <= kappa ||b||` geometry bound follows from
    `x = Aplus*b` and `kappa = ||Aplus|| ||A||`. -/
theorem wedinTheorem20_1_A_norm_mul_solution_norm_le_kappa_b_of_residual_definition
    {m k : ℕ} (A : Fin m → Fin (k + 1) → ℝ)
    (Aplus : Fin (k + 1) → Fin m → ℝ)
    (b r : Fin m → ℝ) (x : Fin (k + 1) → ℝ)
    {Aplus_norm A_norm kappa : ℝ}
    (hA_norm_nonneg : 0 ≤ A_norm)
    (hkappa : kappa = Aplus_norm * A_norm)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hr : r = fun i => b i - rectMatMulVec A x i) :
    A_norm * vecNorm2 x ≤ kappa * vecNorm2 b := by
  have hx_eq :
      x = rectMatMulVec Aplus b :=
    wedinTheorem20_1_solution_eq_Aplus_b_of_residual_definition
      A Aplus b r x hleftA hrangeA_residual hr
  have hx_norm :
      vecNorm2 x ≤ Aplus_norm * vecNorm2 b := by
    rw [hx_eq]
    exact hAplus b
  calc
    A_norm * vecNorm2 x
        ≤ A_norm * (Aplus_norm * vecNorm2 b) :=
            mul_le_mul_of_nonneg_left hx_norm hA_norm_nonneg
    _ = kappa * vecNorm2 b := by
            rw [hkappa]
            ring

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.2):
    residual perturbation bound with the standard LS geometry bounds derived
    from the residual definition and exact-residual projection orthogonality.

The remaining explicit blocker is the source-strength projector estimate
`||P_B(I-P_A)|| <= ||Delta A|| ||Aplus||`, i.e. the full Lemma 20.12
equality/min surface. -/
theorem wedinTheorem20_1_residualRelativeRHS_le_of_residual_definitions_projector_bound_geometry
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (b Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {delta Aplus_norm DeltaA_norm Deltab_norm kappa eps A_norm : ℝ}
    (hb_norm_pos : 0 < vecNorm2 b)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (heps_nonneg : 0 ≤ eps)
    (hkappa : kappa = Aplus_norm * A_norm)
    (hdelta : delta = eps * A_norm)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hDeltaA_norm_budget : DeltaA_norm ≤ eps * A_norm)
    (hDeltab_norm_budget : Deltab_norm ≤ eps * vecNorm2 b)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hPBIPA :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * Aplus_norm))
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (hproj_s : rectMatMulVec (rectMatMul B Bplus) s = 0) :
    vecNorm2 (fun i => r i - s i) / vecNorm2 b ≤
      wedinTheorem20_1ResidualRelativeRHS kappa eps := by
  have hAplus_norm_nonneg : 0 ≤ Aplus_norm :=
    by
      have hright_nonneg :
          0 ≤ Aplus_norm * vecNorm2 b :=
        le_trans (vecNorm2_nonneg (rectMatMulVec Aplus b)) (hAplus b)
      nlinarith [hb_norm_pos]
  have hkappa_nonneg : 0 ≤ kappa := by
    rw [hkappa]
    exact mul_nonneg hAplus_norm_nonneg hA_norm_nonneg
  have hx_budget :
      A_norm * vecNorm2 x ≤ kappa * vecNorm2 b :=
    wedinTheorem20_1_A_norm_mul_solution_norm_le_kappa_b_of_residual_definition
      A Aplus b r x hA_norm_nonneg hkappa hAplus hleftA
      hrangeA_residual hr
  have hr_budget : vecNorm2 r ≤ vecNorm2 b :=
    wedinTheorem20_1_vecNorm2_residual_le_b_of_residual_definition
      A Aplus b r x hleftA hSymA hrangeA_residual hr
  exact
    wedinTheorem20_1_residualRelativeRHS_le_of_residual_definitions_projector_bound
      A B Aplus Bplus DeltaA b Deltab r s x y hb_norm_pos heps_nonneg
      hkappa_nonneg hkappa hdelta hDeltaA hDeltab hDeltaA_norm_budget
      hDeltab_norm_budget hx_budget hr_budget hleftB hSymB
      hrangeA_residual hPBIPA hB hr hs hproj_s

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.2):
    residual perturbation bound with the perturbed residual optimality
    hypothesis stated as column orthogonality.

This is the source-facing version of the residual-side Wedin wrapper above:
`B^T s = 0` is converted to `P_B s = 0` by the symmetric range-projector
lemma, so callers no longer have to expose the raw projector annihilation
condition.  The remaining explicit blocker is still the full Lemma 20.12
source-strength estimate `||P_B(I-P_A)|| <= ||Delta A|| ||Aplus||`. -/
theorem wedinTheorem20_1_residualRelativeRHS_le_of_residual_definitions_projector_bound_geometry_column_orthogonal
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (b Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {delta Aplus_norm DeltaA_norm Deltab_norm kappa eps A_norm : ℝ}
    (hb_norm_pos : 0 < vecNorm2 b)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (heps_nonneg : 0 ≤ eps)
    (hkappa : kappa = Aplus_norm * A_norm)
    (hdelta : delta = eps * A_norm)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hDeltaA_norm_budget : DeltaA_norm ≤ eps * A_norm)
    (hDeltab_norm_budget : Deltab_norm ≤ eps * vecNorm2 b)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hPBIPA :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * Aplus_norm))
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (horth_s : ∀ j : Fin (k + 1), ∑ i : Fin m, B i j * s i = 0) :
    vecNorm2 (fun i => r i - s i) / vecNorm2 b ≤
      wedinTheorem20_1ResidualRelativeRHS kappa eps := by
  have hproj_s : rectMatMulVec (rectMatMul B Bplus) s = 0 :=
    wedinTheorem20_1_rangeProjection_perturbed_residual_eq_zero_of_column_orthogonal
      B Bplus s hSymB horth_s
  exact
    wedinTheorem20_1_residualRelativeRHS_le_of_residual_definitions_projector_bound_geometry
      A B Aplus Bplus DeltaA b Deltab r s x y hb_norm_pos hA_norm_nonneg
      heps_nonneg hkappa hdelta hAplus hDeltaA hDeltab hDeltaA_norm_budget
      hDeltab_norm_budget hleftA hleftB hSymA hSymB hrangeA_residual
      hPBIPA hB hr hs hproj_s

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.2):
    printed relative residual perturbation bound, conditional only on the
    exact cross-projection norm equality from the open Stewart--Sun/CS route.

The exact equality supplies the source-strength `P_B(I-P_A)` projector
estimate.  The remaining residual-definition and least-squares geometry are
then handled by the existing printed-RHS wrapper. -/
theorem wedinTheorem20_1_residualRelativeRHS_le_of_residual_definitions_crossProjection_eq_geometry_column_orthogonal
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (b Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {delta Aplus_norm DeltaA_norm Deltab_norm kappa eps A_norm : ℝ}
    (hb_norm_pos : 0 < vecNorm2 b)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (heps_nonneg : 0 ≤ eps)
    (hkappa : kappa = Aplus_norm * A_norm)
    (hdelta : delta = eps * A_norm)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hDeltaA_norm_budget : DeltaA_norm ≤ eps * A_norm)
    (hDeltab_norm_budget : Deltab_norm ≤ eps * vecNorm2 b)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hEq :
      complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul
              (rectMatMul B Bplus)
              (fun i j => idMatrix m i j - rectMatMul A Aplus i j))) =
        complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul
              (rectMatMul A Aplus)
              (fun i j => idMatrix m i j - rectMatMul B Bplus i j))))
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (horth_s : ∀ j : Fin (k + 1), ∑ i : Fin m, B i j * s i = 0) :
    vecNorm2 (fun i => r i - s i) / vecNorm2 b ≤
      wedinTheorem20_1ResidualRelativeRHS kappa eps := by
  have hAplus_norm_nonneg : 0 ≤ Aplus_norm := by
    have hright_nonneg :
        0 ≤ Aplus_norm * vecNorm2 b :=
      le_trans (vecNorm2_nonneg (rectMatMulVec Aplus b)) (hAplus b)
    nlinarith [hb_norm_pos]
  have hPBIPA :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * Aplus_norm) :=
    wedinLemma20_12_rectOpNorm2Le_rangeProjection_mul_projectionComplement_swapped_of_complexMatrixOp2_eq
      A B Aplus Bplus hleftB hSymA hSymB hDelta hAplus_norm_nonneg
      hAplus hEq
  exact
    wedinTheorem20_1_residualRelativeRHS_le_of_residual_definitions_projector_bound_geometry_column_orthogonal
      A B Aplus Bplus DeltaA b Deltab r s x y hb_norm_pos hA_norm_nonneg
      heps_nonneg hkappa hdelta hAplus hDeltaA hDeltab hDeltaA_norm_budget
      hDeltab_norm_budget hleftA hleftB hSymA hSymB hrangeA_residual
      hPBIPA hB hr hs horth_s

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.2):
    printed relative residual perturbation bound using the source-facing
    Lemma 20.12 `min` projector surface.

This wrapper removes both the raw `P_B(I-P_A)` projector-bound hypothesis and
the earlier exact cross-projection equality hypothesis.  Lemma 20.11 supplies
the `Bplus` radius used by the Lemma 20.12 `min` surface, and monotonicity of
`rectOpNorm2Le` weakens `delta * min(...)` to the printed `delta*||Aplus||₂`
radius consumed by the residual perturbation algebra. -/
theorem wedinTheorem20_1_residualRelativeRHS_le_of_residual_definitions_min_surface_geometry_column_orthogonal
    {m k : ℕ} (hm : 0 < m) (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (b Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {delta Aplus_norm DeltaA_norm Deltab_norm kappa eps A_norm : ℝ}
    (hb_norm_pos : 0 < vecNorm2 b)
    (hAplus_pos : 0 < Aplus_norm)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (heps_nonneg : 0 ≤ eps)
    (hkappa : kappa = Aplus_norm * A_norm)
    (hdelta : delta = eps * A_norm)
    (hsmall : kappa * eps < 1)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hDeltaA_norm_budget : DeltaA_norm ≤ eps * A_norm)
    (hDeltab_norm_budget : Deltab_norm ≤ eps * vecNorm2 b)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (horth_s : ∀ j : Fin (k + 1), ∑ i : Fin m, B i j * s i = 0) :
    vecNorm2 (fun i => r i - s i) / vecNorm2 b ≤
      wedinTheorem20_1ResidualRelativeRHS kappa eps := by
  have heta : kappa * eps = Aplus_norm * delta := by
    rw [hkappa, hdelta]
    ring
  have hBplus :
      rectOpNorm2Le Bplus (Aplus_norm / (1 - kappa * eps)) :=
    wedinLemma20_11_rectOpNorm2Le_Bplus_of_left_inverse_rectOpNorm2Le
      A B Aplus Bplus hAplus_pos heta hsmall hleftA hAplus hDelta
      hleftB hSymB
  have hden_pos : 0 < 1 - kappa * eps :=
    wedinTheorem20_1_denominator_pos hsmall
  have hBplus_radius_nonneg : 0 ≤ Aplus_norm / (1 - kappa * eps) :=
    div_nonneg (le_of_lt hAplus_pos) (le_of_lt hden_pos)
  have hPBIPA_min :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * min Aplus_norm (Aplus_norm / (1 - kappa * eps))) :=
    wedinLemma20_12_rectOpNorm2Le_rangeProjection_mul_projectionComplement_swapped_min
      hm A B Aplus Bplus hleftA hleftB hSymA hSymB hDelta
      (le_of_lt hAplus_pos) hBplus_radius_nonneg hAplus hBplus
  have hdelta_nonneg : 0 ≤ delta :=
    rectOpNorm2Le_radius_nonneg (M := fun i j => B i j - A i j) hDelta
  have hPBIPA :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * Aplus_norm) :=
    rectOpNorm2Le_mono
      (mul_le_mul_of_nonneg_left
        (min_le_left Aplus_norm (Aplus_norm / (1 - kappa * eps)))
        hdelta_nonneg)
      hPBIPA_min
  exact
    wedinTheorem20_1_residualRelativeRHS_le_of_residual_definitions_projector_bound_geometry_column_orthogonal
      A B Aplus Bplus DeltaA b Deltab r s x y hb_norm_pos hA_norm_nonneg
      heps_nonneg hkappa hdelta hAplus hDeltaA hDeltab hDeltaA_norm_budget
      hDeltab_norm_budget hleftA hleftB hSymA hSymB hrangeA_residual
      hPBIPA hB hr hs horth_s

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equations (20.1)-(20.2):
    combined source-facing Wedin perturbation surface at the repository
    residual-definition and column-orthogonality API.

This packages the separately proved solution and residual displayed bounds
after Lemmas 20.11 and 20.12 have discharged the `Bplus` and projector
hypotheses.  The two right-hand-side perturbation budgets are kept separate
because the printed solution and residual estimates use different normalizers. -/
theorem wedinTheorem20_1_solution_and_residualRelativeRHS_le_of_residual_definitions_min_surface_geometry_column_orthogonal
    {m k : ℕ} (hm : 0 < m) (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (b Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {Aplus_norm delta eta DeltaA_norm Deltab_norm kappa eps A_norm : ℝ}
    (hb_norm_pos : 0 < vecNorm2 b)
    (hAplus_pos : 0 < Aplus_norm)
    (hA_norm_pos : 0 < A_norm)
    (heps_nonneg : 0 ≤ eps)
    (hx_norm_pos : 0 < vecNorm2 x)
    (hkappa : kappa = Aplus_norm * A_norm)
    (hdelta : delta = eps * A_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall_eta : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hDeltaA_norm_budget : DeltaA_norm ≤ eps * A_norm)
    (hDeltab_norm_budget_solution :
      Deltab_norm ≤ eps * (A_norm * vecNorm2 x + vecNorm2 r))
    (hDeltab_norm_budget_residual : Deltab_norm ≤ eps * vecNorm2 b)
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (horth_s : ∀ j : Fin (k + 1), ∑ i : Fin m, B i j * s i = 0) :
    (vecNorm2 (fun j => y j - x j) / vecNorm2 x ≤
        wedinTheorem20_1SolutionRelativeRHS
          kappa eps A_norm (vecNorm2 x) (vecNorm2 r)) ∧
      (vecNorm2 (fun i => r i - s i) / vecNorm2 b ≤
        wedinTheorem20_1ResidualRelativeRHS kappa eps) := by
  have hsmall_kappa : kappa * eps < 1 := by
    have h : kappa * eps = eta := by
      rw [hkappa, heta, hdelta]
      ring
    rw [h]
    exact hsmall_eta
  constructor
  · exact
      wedinTheorem20_1_solutionRelativeRHS_le_of_residual_definitions_min_surface_column_orthogonal
        hm A B Aplus Bplus DeltaA b Deltab r s x y hAplus_pos hA_norm_pos
        hx_norm_pos hkappa hdelta heta hsmall_eta hleftA hleftB hSymA hSymB
        hDelta hAplus hDeltaA hDeltab hDeltaA_norm_budget
        hDeltab_norm_budget_solution hrangeA_residual hB hr hs horth_s
  · exact
      wedinTheorem20_1_residualRelativeRHS_le_of_residual_definitions_min_surface_geometry_column_orthogonal
        hm A B Aplus Bplus DeltaA b Deltab r s x y hb_norm_pos hAplus_pos
        (le_of_lt hA_norm_pos) heps_nonneg hkappa hdelta hsmall_kappa hAplus
        hDelta hDeltaA hDeltab hDeltaA_norm_budget
        hDeltab_norm_budget_residual hleftA hleftB hSymA hSymB
        hrangeA_residual hB hr hs horth_s

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.2), conservative
    residual perturbation bound from the currently proved one-sided
    Lemma 20.12 route.

This discharges the explicit projector hypothesis of the printed-RHS wrapper by
using the available source-oriented bound
`||P_B(I-P_A)|| <= ||A-B|| ||Bplus||` and a Lemma 20.11-style radius for
`Bplus`.  The conclusion is deliberately the conservative RHS with the extra
`1/(1-kappa*eps)` denominator; the printed (20.2) bound still needs the full
projection equality/min surface of Lemma 20.12. -/
theorem wedinTheorem20_1_residualRelativeRHSConservative_le_of_residual_definitions_Bplus_bound_geometry_column_orthogonal
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (b Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {delta Aplus_norm DeltaA_norm Deltab_norm kappa eps A_norm eta : ℝ}
    (hb_norm_pos : 0 < vecNorm2 b)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (heps_nonneg : 0 ≤ eps)
    (hkappa : kappa = Aplus_norm * A_norm)
    (hdelta : delta = eps * A_norm)
    (heta : eta = kappa * eps)
    (hsmall : kappa * eps < 1)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hBplus : rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hDeltaA_norm_budget : DeltaA_norm ≤ eps * A_norm)
    (hDeltab_norm_budget : Deltab_norm ≤ eps * vecNorm2 b)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (horth_s : ∀ j : Fin (k + 1), ∑ i : Fin m, B i j * s i = 0) :
    vecNorm2 (fun i => r i - s i) / vecNorm2 b ≤
      wedinTheorem20_1ResidualRelativeRHSConservative kappa eps := by
  have hAplus_norm_nonneg : 0 ≤ Aplus_norm := by
    have hright_nonneg :
        0 ≤ Aplus_norm * vecNorm2 b :=
      le_trans (vecNorm2_nonneg (rectMatMulVec Aplus b)) (hAplus b)
    nlinarith [hb_norm_pos]
  have hkappa_nonneg : 0 ≤ kappa := by
    rw [hkappa]
    exact mul_nonneg hAplus_norm_nonneg hA_norm_nonneg
  have hsmall_eta : eta < 1 := by
    rw [heta]
    exact hsmall
  have hden_pos : 0 < 1 - eta :=
    wedinLemma20_11_denominator_pos hsmall_eta
  have hBplus_radius_nonneg : 0 ≤ Aplus_norm / (1 - eta) :=
    div_nonneg hAplus_norm_nonneg (le_of_lt hden_pos)
  have hPBIPA :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * (Aplus_norm / (1 - eta))) :=
    wedinLemma20_12_rectOpNorm2Le_rangeProjection_mul_projectionComplement_swapped
      A B Aplus Bplus hleftA hSymA hSymB hDelta
      hBplus_radius_nonneg hBplus
  have hproj_s : rectMatMulVec (rectMatMul B Bplus) s = 0 :=
    wedinTheorem20_1_rangeProjection_perturbed_residual_eq_zero_of_column_orthogonal
      B Bplus s hSymB horth_s
  have hvec :
      vecNorm2 (fun i => r i - s i) ≤
        Deltab_norm + DeltaA_norm * vecNorm2 x +
          (delta * (Aplus_norm / (1 - eta))) * vecNorm2 r :=
    wedinTheorem20_1_vecNorm2_residual_difference_le_of_residual_definitions_projector_bound
      (A := A) (B := B) (Aplus := Aplus) (Bplus := Bplus)
      (DeltaA := DeltaA) (b := b) (Deltab := Deltab)
      (r := r) (s := s) (x := x) (y := y)
      (delta := delta) (Aplus_norm := Aplus_norm / (1 - eta))
      (DeltaA_norm := DeltaA_norm) (Deltab_norm := Deltab_norm)
      hleftB hSymB hDeltaA hDeltab hrangeA_residual hPBIPA hB hr hs hproj_s
  have hx_budget :
      A_norm * vecNorm2 x ≤ kappa * vecNorm2 b :=
    wedinTheorem20_1_A_norm_mul_solution_norm_le_kappa_b_of_residual_definition
      A Aplus b r x hA_norm_nonneg hkappa hAplus hleftA
      hrangeA_residual hr
  have hr_budget : vecNorm2 r ≤ vecNorm2 b :=
    wedinTheorem20_1_vecNorm2_residual_le_b_of_residual_definition
      A Aplus b r x hleftA hSymA hrangeA_residual hr
  exact
    wedinTheorem20_1_residualRelativeRHSConservative_of_vector_bound
      (hb_norm_pos := hb_norm_pos)
      (hx_norm_nonneg := vecNorm2_nonneg x)
      (heps_nonneg := heps_nonneg)
      (hkappa_nonneg := hkappa_nonneg)
      (hkappa := hkappa)
      (hdelta := hdelta)
      (heta := heta)
      (hsmall := hsmall)
      (hDeltaA_norm_budget := hDeltaA_norm_budget)
      (hDeltab_norm_budget := hDeltab_norm_budget)
      (hx_budget := hx_budget)
      (hr_budget := hr_budget)
      (hvec := hvec)

/-- **Theorem 20.1 (Wedin)**: Normwise perturbation of the LS solution.

    Let A ∈ ℝ^{m×n} (m ≥ n) and A + ΔA both be of full rank, with
    ‖ΔA‖₂ ≤ ε‖A‖₂ and ‖Δb‖₂ ≤ ε‖b‖₂. Then:

    ‖x−y‖₂/‖x‖₂ ≤ κ₂(A)·ε/(1−κ₂(A)·ε) · (2 + (κ₂(A)+1)·‖r‖₂/(‖A‖₂·‖x‖₂))
    ‖r−s‖₂/‖b‖₂ ≤ (1 + 2κ₂(A))·ε

    where r = b − Ax, s = b + Δb − (A+ΔA)y.

    The bound shows sensitivity is κ₂(A) when the residual is small
    (nearly consistent system) and κ₂(A)² when the residual is large.

    Legacy contract package only: the source-exact Wedin theorem still remains
    open until the SVD, pseudoinverse, and projector perturbation foundations
    are closed. -/
structure WedinPerturbationBound (n : ℕ)
    (x y : Fin n → ℝ) (kappa eps : ℝ)
    (sol_bound res_bound : ℝ) : Prop where
  /-- κ₂(A) > 0. -/
  kappa_pos : 0 < kappa
  /-- The perturbation is small enough: κ₂(A)·ε < 1. -/
  small_pert : kappa * eps < 1
  /-- Solution perturbation bound (eq 20.1):
      ‖x−y‖ ≤ sol_bound where sol_bound depends on κ₂(A), ε, ‖r‖, ‖A‖, ‖x‖. -/
  solution : ∀ i, |y i - x i| ≤ sol_bound
  /-- Residual perturbation bound (eq 20.2):
      ‖r−s‖ ≤ res_bound where res_bound ≤ (1+2κ₂(A))·ε·‖b‖. -/
  residual_bound_val : res_bound ≤ (1 + 2 * kappa) * eps

-- ============================================================
-- §20.1  Theorem 20.2: Componentwise LS perturbation
-- ============================================================

/-- **Augmented system for the LS problem** (Higham eq 20.3).

    The LS solution x and residual r = b − Ax satisfy the
    (m+n)×(m+n) augmented system:

    [I  A ][r]   [b]
    [Aᵀ 0 ][x] = [0]

    This is equivalent to the normal equations AᵀAx = Aᵀb.

    The inverse of the augmented system matrix has blocks
    involving A⁺ and (AᵀA)⁻¹ (eq 19.6), enabling componentwise
    perturbation analysis.

    We capture the componentwise perturbation result (Theorem 20.2)
    in terms of the n×n Gram inverse (AᵀA)⁻¹, which is representable
    in the library's square-matrix framework. -/
structure LSAugmentedPerturbation (n : ℕ)
    (ATA ATA_inv : Fin n → Fin n → ℝ)
    (x y : Fin n → ℝ) (eps : ℝ)
    (bound_vec : Fin n → ℝ) : Prop where
  /-- (AᵀA)⁻¹ is the inverse of the Gram matrix. -/
  gram_inv : IsInverse n ATA ATA_inv
  /-- The perturbation ε is nonneg. -/
  eps_nonneg : 0 ≤ eps
  /-- Componentwise bound on the solution perturbation (eq 19.8):
      |y_i − x_i| ≤ ε · bound_vec_i
      where bound_vec captures the |(AᵀA)⁻¹|-weighted perturbation. -/
  solution_bound : ∀ i, |y i - x i| ≤ eps * bound_vec i

end NumStability
