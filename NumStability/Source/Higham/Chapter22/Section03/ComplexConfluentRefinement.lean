/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter12.IterativeRefinement
import NumStability.Algorithms.Horner
import NumStability.Source.Higham.Chapter22.VandermondeSystems
import NumStability.Analysis.ComplexArithmetic

/-! # Complex confluent Vandermonde residual/refinement bridge

This module closes the full complex-scalar finite residual/refinement path of
Higham §22.3. It builds
an actual rounded all-order differentiated-Horner executor from the repository's
rounded complex add, subtract, and multiply primitives, proves its generated
forward budget, identifies every derivative order with the corresponding row
of the existing confluent Vandermonde matrix, includes the rounded final
residual subtraction, and transports that per-row (12.8) certificate through
the complex-norm form of Theorem 12.3 to the exact finite (12.10) bound.

The executor follows Algorithm 5.2's Taylor-state recurrence and final
factorial scaling; no derivative-error or target conclusion is assumed.

The companion real bridge contains a compiled `SOURCE-DISCREPANCY`
counterexample to p. 428 read with (12.9)'s literal conventional-dot-product
constant `γ_(n+1)/u`.  Accordingly, this module proves the corrected (12.8)
certificate: its exact generated budget is divided by positive unit roundoff
to provide `t` directly, and no false `γ_(n+1)` domination is asserted.
-/

namespace NumStability.Ch22B

open scoped BigOperators
lemma ch22b_iter_deriv_add (p q : Polynomial ℂ) : ∀ s : ℕ,
    (Polynomial.derivative^[s]) (p + q) =
      (Polynomial.derivative^[s]) p + (Polynomial.derivative^[s]) q := by
  intro s
  induction s generalizing p q with
  | zero => rfl
  | succ s ih =>
      rw [Function.iterate_succ_apply, Polynomial.derivative_add, ih]
      rw [show s + 1 = s.succ by omega]
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]

lemma ch22b_iter_deriv_derivative (p : Polynomial ℂ) (s : ℕ) :
    (Polynomial.derivative^[s]) (Polynomial.derivative p) =
      (Polynomial.derivative^[s + 1]) p := by
  rw [show s + 1 = s.succ by omega, Function.iterate_succ_apply]

lemma ch22b_iter_deriv_mul_X_eval_succ (p : Polynomial ℂ) (alpha : ℂ) :
    ∀ s : ℕ,
      ((Polynomial.derivative^[s + 1]) (p * Polynomial.X)).eval alpha =
        ((Polynomial.derivative^[s + 1]) p).eval alpha * alpha +
          (s + 1 : ℂ) * ((Polynomial.derivative^[s]) p).eval alpha := by
  intro s
  induction s generalizing p with
  | zero =>
      rw [Function.iterate_succ_apply]
      simp [Polynomial.derivative_mul]
  | succ s ih =>
      rw [show s + 1 + 1 = (s + 1).succ by omega,
        Function.iterate_succ_apply]
      simp only [Polynomial.derivative_mul, Polynomial.derivative_X, mul_one]
      rw [ch22b_iter_deriv_add]
      simp only [Polynomial.eval_add]
      rw [ih (Polynomial.derivative p)]
      rw [ch22b_iter_deriv_derivative, ch22b_iter_deriv_derivative]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

lemma ch22b_horner_poly_step_eval (q : Polynomial ℂ) (a alpha : ℂ) :
    ∀ r : ℕ,
      ((Polynomial.derivative^[r]) (q * Polynomial.X + Polynomial.C a)).eval alpha =
        match r with
        | 0 => q.eval alpha * alpha + a
        | s + 1 =>
            ((Polynomial.derivative^[s + 1]) q).eval alpha * alpha +
              (s + 1 : ℂ) * ((Polynomial.derivative^[s]) q).eval alpha := by
  intro r
  cases r with
  | zero => simp
  | succ s =>
      rw [Function.iterate_succ_apply]
      simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
        Polynomial.derivative_X, Polynomial.derivative_C, mul_one, add_zero]
      rw [ch22b_iter_deriv_add]
      simp only [Polynomial.eval_add]
      rw [show (Polynomial.derivative^[s])
              (Polynomial.derivative q * Polynomial.X) =
            (Polynomial.derivative^[s + 1]) (q * Polynomial.X) -
              (Polynomial.derivative^[s]) q by
            rw [show s + 1 = s.succ by omega, Function.iterate_succ_apply]
            simp only [Polynomial.derivative_mul, Polynomial.derivative_X,
              mul_one]
            rw [ch22b_iter_deriv_add]
            ring]
      simp only [Polynomial.eval_sub]
      rw [ch22b_iter_deriv_mul_X_eval_succ]
      ring

noncomputable def ch22bComplexPolyDesc : List ℂ → Polynomial ℂ
  | [] => 0
  | a :: rest =>
      rest.foldl (fun q b => q * Polynomial.X + Polynomial.C b)
        (Polynomial.C a)

lemma ch22bComplexPolyDesc_append_singleton (l : List ℂ) (a : ℂ) :
    ch22bComplexPolyDesc (l ++ [a]) =
      ch22bComplexPolyDesc l * Polynomial.X + Polynomial.C a := by
  cases l with
  | nil => simp [ch22bComplexPolyDesc]
  | cons b rest =>
      simp [ch22bComplexPolyDesc, List.foldl_append]

theorem ch22bComplexPolyDesc_reverse_ofFn_eq_sum {n : ℕ}
    (a : Fin n → ℂ) :
    ch22bComplexPolyDesc (List.ofFn a).reverse =
      ∑ j : Fin n, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ) := by
  induction n with
  | zero => simp [ch22bComplexPolyDesc]
  | succ n ih =>
      rw [List.ofFn_succ, List.reverse_cons,
        ch22bComplexPolyDesc_append_singleton, ih, Fin.sum_univ_succ]
      simp only [Finset.sum_mul, mul_assoc, ← pow_succ]
      simp
      ring

theorem ch22bComplexPolyDesc_reverse_ofFn_eq_higham {n : ℕ}
    (a : Fin n → ℂ) :
    ch22bComplexPolyDesc (List.ofFn a).reverse =
      NumStability.higham22CoefficientPolynomial a := by
  rw [ch22bComplexPolyDesc_reverse_ofFn_eq_sum]
  unfold NumStability.higham22CoefficientPolynomial Polynomial.degreeLTEquiv
  change (∑ j : Fin n, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)) =
    ∑ j : Fin n, Polynomial.monomial (j : ℕ) (a j)
  simp_rw [← Polynomial.C_mul_X_pow_eq_monomial]

noncomputable def ch22bComplexFormalStep
    (alpha a : ℂ) (deriv : ℕ → ℂ) : ℕ → ℂ
  | 0 => alpha * deriv 0 + a
  | i + 1 => alpha * deriv (i + 1) + (i + 1 : ℂ) * deriv i

noncomputable def ch22bComplexFormalDesc
    (alpha : ℂ) : List ℂ → ℕ → ℂ
  | [] => fun _ => 0
  | a :: rest =>
      rest.foldl (fun d b => ch22bComplexFormalStep alpha b d)
        (fun | 0 => a | _ + 1 => 0)

lemma ch22bComplexFormalStep_eq_iterateDerivative_eval
    (q : Polynomial ℂ) (alpha a : ℂ) :
    ch22bComplexFormalStep alpha a
        (fun r => ((Polynomial.derivative^[r]) q).eval alpha) =
      fun r => ((Polynomial.derivative^[r])
        (q * Polynomial.X + Polynomial.C a)).eval alpha := by
  funext r
  cases r with
  | zero =>
      rw [ch22b_horner_poly_step_eval]
      simp [ch22bComplexFormalStep]
      ring
  | succ s =>
      rw [ch22b_horner_poly_step_eval]
      simp [ch22bComplexFormalStep]
      ring

lemma ch22bComplexFormalFold_eq_iterateDerivative_eval (alpha : ℂ) :
    ∀ (rest : List ℂ) (q : Polynomial ℂ) (r : ℕ),
      rest.foldl (fun d b => ch22bComplexFormalStep alpha b d)
          (fun j => ((Polynomial.derivative^[j]) q).eval alpha) r =
        ((Polynomial.derivative^[r])
          (rest.foldl
            (fun p b => p * Polynomial.X + Polynomial.C b) q)).eval alpha := by
  intro rest
  induction rest with
  | nil => intro q r; rfl
  | cons a rest ih =>
      intro q r
      simp only [List.foldl]
      rw [ch22bComplexFormalStep_eq_iterateDerivative_eval]
      exact ih (q * Polynomial.X + Polynomial.C a) r

theorem ch22bComplexFormalDesc_eq_iterateDerivative_eval
    (alpha : ℂ) (coeffsDesc : List ℂ) (r : ℕ) :
    ch22bComplexFormalDesc alpha coeffsDesc r =
      ((Polynomial.derivative^[r])
        (ch22bComplexPolyDesc coeffsDesc)).eval alpha := by
  cases coeffsDesc with
  | nil => simp [ch22bComplexFormalDesc, ch22bComplexPolyDesc]
  | cons a rest =>
      have hinit : (fun j =>
          ((Polynomial.derivative^[j]) (Polynomial.C a)).eval alpha) =
          (fun | 0 => a | _ + 1 => 0) := by
        funext j
        cases j with
        | zero => simp
        | succ j =>
            rw [Function.iterate_succ_apply]
            simp
      rw [ch22bComplexFormalDesc, ← hinit]
      exact ch22bComplexFormalFold_eq_iterateDerivative_eval alpha rest
        (Polynomial.C a) r

noncomputable def ch22bComplexTaylorStep
    (alpha a : ℂ) (coeff : ℕ → ℂ) : ℕ → ℂ
  | 0 => alpha * coeff 0 + a
  | i + 1 => alpha * coeff (i + 1) + coeff i

noncomputable def ch22bComplexTaylorDesc
    (alpha : ℂ) : List ℂ → ℕ → ℂ
  | [] => fun _ => 0
  | a :: rest =>
      rest.foldl (fun c b => ch22bComplexTaylorStep alpha b c)
        (fun | 0 => a | _ + 1 => 0)

lemma ch22bComplexFormalStep_factorial_taylor
    (alpha a : ℂ) (coeff : ℕ → ℂ) (r : ℕ) :
    ch22bComplexFormalStep alpha a
        (fun j => (Nat.factorial j : ℂ) * coeff j) r =
      (Nat.factorial r : ℂ) * ch22bComplexTaylorStep alpha a coeff r := by
  cases r with
  | zero => simp [ch22bComplexFormalStep, ch22bComplexTaylorStep]
  | succ r =>
      simp only [ch22bComplexFormalStep, ch22bComplexTaylorStep,
        Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring

lemma ch22bComplexFormalFold_factorial_taylor (alpha : ℂ) :
    ∀ (rest : List ℂ) (coeff : ℕ → ℂ) (r : ℕ),
      rest.foldl (fun d b => ch22bComplexFormalStep alpha b d)
          (fun j => (Nat.factorial j : ℂ) * coeff j) r =
        (Nat.factorial r : ℂ) *
          (rest.foldl (fun c b => ch22bComplexTaylorStep alpha b c) coeff) r := by
  intro rest
  induction rest with
  | nil => intro coeff r; rfl
  | cons a rest ih =>
      intro coeff r
      simp only [List.foldl]
      rw [show ch22bComplexFormalStep alpha a
          (fun j => (Nat.factorial j : ℂ) * coeff j) =
        fun j => (Nat.factorial j : ℂ) *
          ch22bComplexTaylorStep alpha a coeff j by
            funext j
            exact ch22bComplexFormalStep_factorial_taylor alpha a coeff j]
      exact ih (ch22bComplexTaylorStep alpha a coeff) r

theorem ch22bComplexFormalDesc_eq_factorial_taylor
    (alpha : ℂ) (coeffsDesc : List ℂ) (r : ℕ) :
    ch22bComplexFormalDesc alpha coeffsDesc r =
      (Nat.factorial r : ℂ) * ch22bComplexTaylorDesc alpha coeffsDesc r := by
  cases coeffsDesc with
  | nil => simp [ch22bComplexFormalDesc, ch22bComplexTaylorDesc]
  | cons a rest =>
      let coeff : ℕ → ℂ := fun | 0 => a | _ + 1 => 0
      have h := ch22bComplexFormalFold_factorial_taylor alpha rest coeff r
      have hinit : (fun j => (Nat.factorial j : ℂ) * coeff j) = coeff := by
        funext j
        cases j <;> simp [coeff]
      rw [hinit] at h
      simpa [ch22bComplexFormalDesc, ch22bComplexTaylorDesc, coeff] using h

noncomputable def ch22bFlComplexTaylorStep
    (fp : NumStability.FPModel) (alpha a : ℂ)
    (coeff : ℕ → ℂ) : ℕ → ℂ
  | 0 => NumStability.fl_complexAdd fp
      (NumStability.fl_complexMul fp alpha (coeff 0)) a
  | i + 1 => NumStability.fl_complexAdd fp
      (NumStability.fl_complexMul fp alpha (coeff (i + 1))) (coeff i)

noncomputable def ch22bFlComplexTaylorStepBudget
    (fp : NumStability.FPModel) (alpha a : ℂ)
    (coeff : ℕ → ℂ) (budget : ℕ → ℝ) : ℕ → ℝ
  | 0 =>
      fp.u * ‖NumStability.fl_complexMul fp alpha (coeff 0) + a‖ +
        (Real.sqrt 2 * NumStability.gamma fp 2) * ‖alpha * coeff 0‖ +
        ‖alpha‖ * budget 0
  | i + 1 =>
      fp.u * ‖NumStability.fl_complexMul fp alpha (coeff (i + 1)) + coeff i‖ +
        (Real.sqrt 2 * NumStability.gamma fp 2) *
          ‖alpha * coeff (i + 1)‖ +
        ‖alpha‖ * budget (i + 1) + budget i

lemma ch22bFlComplexTaylorStep_error_bound
    (fp : NumStability.FPModel) (hgamma2 : NumStability.gammaValid fp 2)
    (alpha a : ℂ) (coeffHat coeff : ℕ → ℂ) (budget : ℕ → ℝ)
    (hbound : ∀ i, ‖coeffHat i - coeff i‖ ≤ budget i) (r : ℕ) :
    ‖ch22bFlComplexTaylorStep fp alpha a coeffHat r -
        ch22bComplexTaylorStep alpha a coeff r‖ ≤
      ch22bFlComplexTaylorStepBudget fp alpha a coeffHat budget r := by
  let rho := Real.sqrt 2 * NumStability.gamma fp 2
  cases r with
  | zero =>
      let mHat := NumStability.fl_complexMul fp alpha (coeffHat 0)
      have hadd :
          ‖NumStability.fl_complexAdd fp mHat a - (mHat + a)‖ ≤
            fp.u * ‖mHat + a‖ :=
        NumStability.fl_complexAdd_error_bound fp mHat a
      have hmul : ‖mHat - alpha * coeffHat 0‖ ≤
          rho * ‖alpha * coeffHat 0‖ := by
        simpa [mHat, rho] using
          NumStability.fl_complexMul_error_bound fp hgamma2 alpha (coeffHat 0)
      have hstate : ‖alpha * (coeffHat 0 - coeff 0)‖ ≤
          ‖alpha‖ * budget 0 := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hbound 0) (norm_nonneg _)
      change ‖NumStability.fl_complexAdd fp mHat a -
          (alpha * coeff 0 + a)‖ ≤ _
      have hid : NumStability.fl_complexAdd fp mHat a -
          (alpha * coeff 0 + a) =
          (NumStability.fl_complexAdd fp mHat a - (mHat + a)) +
            ((mHat - alpha * coeffHat 0) +
              alpha * (coeffHat 0 - coeff 0)) := by ring
      rw [hid]
      calc
        ‖(NumStability.fl_complexAdd fp mHat a - (mHat + a)) +
            ((mHat - alpha * coeffHat 0) +
              alpha * (coeffHat 0 - coeff 0))‖ ≤
            ‖NumStability.fl_complexAdd fp mHat a - (mHat + a)‖ +
              (‖mHat - alpha * coeffHat 0‖ +
                ‖alpha * (coeffHat 0 - coeff 0)‖) := by
          exact (norm_add_le _ _).trans
            (add_le_add (le_refl _) (norm_add_le _ _))
        _ ≤ fp.u * ‖mHat + a‖ +
            (rho * ‖alpha * coeffHat 0‖ + ‖alpha‖ * budget 0) :=
          add_le_add hadd (add_le_add hmul hstate)
        _ = ch22bFlComplexTaylorStepBudget fp alpha a coeffHat budget 0 := by
          simp [ch22bFlComplexTaylorStepBudget, mHat, rho]
          ring
  | succ i =>
      let mHat := NumStability.fl_complexMul fp alpha (coeffHat (i + 1))
      have hadd :
          ‖NumStability.fl_complexAdd fp mHat (coeffHat i) -
              (mHat + coeffHat i)‖ ≤
            fp.u * ‖mHat + coeffHat i‖ :=
        NumStability.fl_complexAdd_error_bound fp mHat (coeffHat i)
      have hmul : ‖mHat - alpha * coeffHat (i + 1)‖ ≤
          rho * ‖alpha * coeffHat (i + 1)‖ := by
        simpa [mHat, rho] using
          NumStability.fl_complexMul_error_bound fp hgamma2 alpha
            (coeffHat (i + 1))
      have hstateSucc : ‖alpha * (coeffHat (i + 1) - coeff (i + 1))‖ ≤
          ‖alpha‖ * budget (i + 1) := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hbound (i + 1)) (norm_nonneg _)
      change ‖NumStability.fl_complexAdd fp mHat (coeffHat i) -
          (alpha * coeff (i + 1) + coeff i)‖ ≤ _
      have hid : NumStability.fl_complexAdd fp mHat (coeffHat i) -
          (alpha * coeff (i + 1) + coeff i) =
          (NumStability.fl_complexAdd fp mHat (coeffHat i) -
              (mHat + coeffHat i)) +
            ((mHat - alpha * coeffHat (i + 1)) +
              (alpha * (coeffHat (i + 1) - coeff (i + 1)) +
                (coeffHat i - coeff i))) := by ring
      rw [hid]
      calc
        ‖(NumStability.fl_complexAdd fp mHat (coeffHat i) -
              (mHat + coeffHat i)) +
            ((mHat - alpha * coeffHat (i + 1)) +
              (alpha * (coeffHat (i + 1) - coeff (i + 1)) +
                (coeffHat i - coeff i)))‖ ≤
            ‖NumStability.fl_complexAdd fp mHat (coeffHat i) -
              (mHat + coeffHat i)‖ +
              (‖mHat - alpha * coeffHat (i + 1)‖ +
                (‖alpha * (coeffHat (i + 1) - coeff (i + 1))‖ +
                  ‖coeffHat i - coeff i‖)) := by
          exact (norm_add_le _ _).trans
            (add_le_add (le_refl _)
              ((norm_add_le _ _).trans
                (add_le_add (le_refl _) (norm_add_le _ _))))
        _ ≤ fp.u * ‖mHat + coeffHat i‖ +
            (rho * ‖alpha * coeffHat (i + 1)‖ +
              (‖alpha‖ * budget (i + 1) + budget i)) :=
          add_le_add hadd
            (add_le_add hmul (add_le_add hstateSucc (hbound i)))
        _ = ch22bFlComplexTaylorStepBudget fp alpha a coeffHat budget (i + 1) := by
          simp [ch22bFlComplexTaylorStepBudget, mHat, rho]
          ring

noncomputable def ch22bFlComplexTaylorStateStep
    (fp : NumStability.FPModel) (alpha a : ℂ)
    (state : (ℕ → ℂ) × (ℕ → ℝ)) : (ℕ → ℂ) × (ℕ → ℝ) :=
  (ch22bFlComplexTaylorStep fp alpha a state.1,
    ch22bFlComplexTaylorStepBudget fp alpha a state.1 state.2)

noncomputable def ch22bFlComplexTaylorStateDesc
    (fp : NumStability.FPModel) (alpha : ℂ) :
    List ℂ → (ℕ → ℂ) × (ℕ → ℝ)
  | [] => (fun _ => 0, fun _ => 0)
  | a :: rest =>
      rest.foldl (fun state b => ch22bFlComplexTaylorStateStep fp alpha b state)
        (fun | 0 => a | _ + 1 => 0, fun _ => 0)

noncomputable def ch22bFlComplexTaylorDesc
    (fp : NumStability.FPModel) (alpha : ℂ)
    (coeffsDesc : List ℂ) (r : ℕ) : ℂ :=
  (ch22bFlComplexTaylorStateDesc fp alpha coeffsDesc).1 r

noncomputable def ch22bFlComplexTaylorForwardBudgetDesc
    (fp : NumStability.FPModel) (alpha : ℂ)
    (coeffsDesc : List ℂ) (r : ℕ) : ℝ :=
  (ch22bFlComplexTaylorStateDesc fp alpha coeffsDesc).2 r

lemma ch22bFlComplexTaylorStateFold_error_bound
    (fp : NumStability.FPModel)
    (hgamma2 : NumStability.gammaValid fp 2) (alpha : ℂ) :
    ∀ (rest : List ℂ) (stateHat : (ℕ → ℂ) × (ℕ → ℝ))
      (state : ℕ → ℂ),
      (∀ r, ‖stateHat.1 r - state r‖ ≤ stateHat.2 r) →
      ∀ r,
        ‖(rest.foldl
            (fun s b => ch22bFlComplexTaylorStateStep fp alpha b s)
            stateHat).1 r -
          (rest.foldl (fun s b => ch22bComplexTaylorStep alpha b s)
            state) r‖ ≤
          (rest.foldl
            (fun s b => ch22bFlComplexTaylorStateStep fp alpha b s)
            stateHat).2 r := by
  intro rest
  induction rest with
  | nil =>
      intro stateHat state hbound r
      exact hbound r
  | cons a rest ih =>
      intro stateHat state hbound r
      simp only [List.foldl]
      apply ih
      intro j
      exact ch22bFlComplexTaylorStep_error_bound fp hgamma2 alpha a
        stateHat.1 state stateHat.2 hbound j

theorem ch22bFlComplexTaylorDesc_error_bound
    (fp : NumStability.FPModel)
    (hgamma2 : NumStability.gammaValid fp 2)
    (alpha : ℂ) (coeffsDesc : List ℂ) (r : ℕ) :
    ‖ch22bFlComplexTaylorDesc fp alpha coeffsDesc r -
        ch22bComplexTaylorDesc alpha coeffsDesc r‖ ≤
      ch22bFlComplexTaylorForwardBudgetDesc fp alpha coeffsDesc r := by
  cases coeffsDesc with
  | nil =>
      simp [ch22bFlComplexTaylorDesc, ch22bFlComplexTaylorForwardBudgetDesc,
        ch22bFlComplexTaylorStateDesc, ch22bComplexTaylorDesc]
  | cons a rest =>
      apply ch22bFlComplexTaylorStateFold_error_bound fp hgamma2 alpha rest
      intro j
      cases j <;> simp

noncomputable def ch22bFlComplexHigherDerivativeOutput
    (fp : NumStability.FPModel) (alpha : ℂ)
    (coeffsDesc : List ℂ) (r : ℕ) : ℂ :=
  NumStability.fl_complexMul fp (Nat.factorial r : ℂ)
    (ch22bFlComplexTaylorDesc fp alpha coeffsDesc r)

noncomputable def ch22bFlComplexHigherDerivativeForwardBudget
    (fp : NumStability.FPModel) (alpha : ℂ)
    (coeffsDesc : List ℂ) (r : ℕ) : ℝ :=
  (Real.sqrt 2 * NumStability.gamma fp 2) *
      ‖(Nat.factorial r : ℂ) *
        ch22bFlComplexTaylorDesc fp alpha coeffsDesc r‖ +
    (Nat.factorial r : ℝ) *
      ch22bFlComplexTaylorForwardBudgetDesc fp alpha coeffsDesc r

theorem ch22bFlComplexHigherDerivativeOutput_error_bound
    (fp : NumStability.FPModel)
    (hgamma2 : NumStability.gammaValid fp 2)
    (alpha : ℂ) (coeffsDesc : List ℂ) (r : ℕ) :
    ‖ch22bFlComplexHigherDerivativeOutput fp alpha coeffsDesc r -
        ch22bComplexFormalDesc alpha coeffsDesc r‖ ≤
      ch22bFlComplexHigherDerivativeForwardBudget fp alpha coeffsDesc r := by
  let f : ℂ := Nat.factorial r
  let cHat := ch22bFlComplexTaylorDesc fp alpha coeffsDesc r
  let c := ch22bComplexTaylorDesc alpha coeffsDesc r
  let rho := Real.sqrt 2 * NumStability.gamma fp 2
  let B := ch22bFlComplexTaylorForwardBudgetDesc fp alpha coeffsDesc r
  have hstate : ‖cHat - c‖ ≤ B := by
    simpa [cHat, c, B] using
      ch22bFlComplexTaylorDesc_error_bound fp hgamma2 alpha coeffsDesc r
  have hmul :
      ‖NumStability.fl_complexMul fp f cHat - f * cHat‖ ≤
        rho * ‖f * cHat‖ := by
    simpa [f, cHat, rho] using
      NumStability.fl_complexMul_error_bound fp hgamma2 f cHat
  have htransport : ‖f * (cHat - c)‖ ≤ (Nat.factorial r : ℝ) * B := by
    rw [norm_mul]
    have hf : ‖f‖ = (Nat.factorial r : ℝ) := by simp [f]
    rw [hf]
    exact mul_le_mul_of_nonneg_left hstate (by positivity)
  rw [ch22bComplexFormalDesc_eq_factorial_taylor]
  change ‖NumStability.fl_complexMul fp f cHat - f * c‖ ≤ _
  have hid : NumStability.fl_complexMul fp f cHat - f * c =
      (NumStability.fl_complexMul fp f cHat - f * cHat) +
        f * (cHat - c) := by ring
  rw [hid]
  calc
    ‖(NumStability.fl_complexMul fp f cHat - f * cHat) +
        f * (cHat - c)‖ ≤
      ‖NumStability.fl_complexMul fp f cHat - f * cHat‖ +
        ‖f * (cHat - c)‖ := norm_add_le _ _
    _ ≤ rho * ‖f * cHat‖ + (Nat.factorial r : ℝ) * B :=
      add_le_add hmul htransport
    _ = ch22bFlComplexHigherDerivativeForwardBudget fp alpha coeffsDesc r := by
      simp [ch22bFlComplexHigherDerivativeForwardBudget, f, cHat, rho, B]

noncomputable def ch22bComplexHigherDerivativeResidual
    (fp : NumStability.FPModel) (alpha b : ℂ)
    (coeffsDesc : List ℂ) (r : ℕ) : ℂ :=
  NumStability.fl_complexSub fp b
    (ch22bFlComplexHigherDerivativeOutput fp alpha coeffsDesc r)

noncomputable def ch22bComplexHigherDerivativeResidualBudget
    (fp : NumStability.FPModel) (alpha b : ℂ)
    (coeffsDesc : List ℂ) (r : ℕ) : ℝ :=
  ch22bFlComplexHigherDerivativeForwardBudget fp alpha coeffsDesc r +
    fp.u * ‖b - ch22bFlComplexHigherDerivativeOutput fp alpha coeffsDesc r‖

theorem ch22bComplexHigherDerivativeResidual_error_bound
    (fp : NumStability.FPModel)
    (hgamma2 : NumStability.gammaValid fp 2)
    (alpha b : ℂ) (coeffsDesc : List ℂ) (r : ℕ) :
    ‖ch22bComplexHigherDerivativeResidual fp alpha b coeffsDesc r -
        (b - ch22bComplexFormalDesc alpha coeffsDesc r)‖ ≤
      ch22bComplexHigherDerivativeResidualBudget fp alpha b coeffsDesc r := by
  let pHat := ch22bFlComplexHigherDerivativeOutput fp alpha coeffsDesc r
  let p := ch22bComplexFormalDesc alpha coeffsDesc r
  let B := ch22bFlComplexHigherDerivativeForwardBudget fp alpha coeffsDesc r
  have heval : ‖pHat - p‖ ≤ B := by
    simpa [pHat, p, B] using
      ch22bFlComplexHigherDerivativeOutput_error_bound
        fp hgamma2 alpha coeffsDesc r
  have hsub :
      ‖NumStability.fl_complexSub fp b pHat - (b - pHat)‖ ≤
        fp.u * ‖b - pHat‖ :=
    NumStability.fl_complexSub_error_bound fp b pHat
  change ‖NumStability.fl_complexSub fp b pHat - (b - p)‖ ≤ _
  have hid : NumStability.fl_complexSub fp b pHat - (b - p) =
      (NumStability.fl_complexSub fp b pHat - (b - pHat)) +
        (p - pHat) := by ring
  rw [hid]
  calc
    ‖(NumStability.fl_complexSub fp b pHat - (b - pHat)) +
        (p - pHat)‖ ≤
      ‖NumStability.fl_complexSub fp b pHat - (b - pHat)‖ +
        ‖p - pHat‖ := norm_add_le _ _
    _ ≤ fp.u * ‖b - pHat‖ + B :=
      add_le_add hsub (by simpa [norm_sub_rev] using heval)
    _ = ch22bComplexHigherDerivativeResidualBudget fp alpha b coeffsDesc r := by
      simp [ch22bComplexHigherDerivativeResidualBudget, pHat, B]
      ring

noncomputable def ch22bComplexConfluentComputedResidual
    {ι : Type*} [Fintype ι] (fp : NumStability.FPModel)
    (multiplicity : ι → ℕ) (alpha : ι → ℂ)
    (b xHat : Fin (Fintype.card
      (NumStability.Higham22ConfluentSlot multiplicity)) → ℂ)
    (slot : NumStability.Higham22ConfluentSlot multiplicity) : ℂ :=
  ch22bComplexHigherDerivativeResidual fp (alpha slot.1)
    (b (NumStability.higham22ConfluentSlotEquivFin multiplicity slot))
    (List.ofFn xHat).reverse slot.2.val

noncomputable def ch22bComplexConfluentResidualBudget
    {ι : Type*} [Fintype ι] (fp : NumStability.FPModel)
    (multiplicity : ι → ℕ) (alpha : ι → ℂ)
    (b xHat : Fin (Fintype.card
      (NumStability.Higham22ConfluentSlot multiplicity)) → ℂ)
    (slot : NumStability.Higham22ConfluentSlot multiplicity) : ℝ :=
  ch22bComplexHigherDerivativeResidualBudget fp (alpha slot.1)
    (b (NumStability.higham22ConfluentSlotEquivFin multiplicity slot))
    (List.ofFn xHat).reverse slot.2.val

theorem ch22bComplexConfluent_residual_error
    {ι : Type*} [Fintype ι] (fp : NumStability.FPModel)
    (hgamma2 : NumStability.gammaValid fp 2)
    (multiplicity : ι → ℕ) (alpha : ι → ℂ)
    (b xHat : Fin (Fintype.card
      (NumStability.Higham22ConfluentSlot multiplicity)) → ℂ) :
    ∀ slot : NumStability.Higham22ConfluentSlot multiplicity,
      ‖ch22bComplexConfluentComputedResidual fp multiplicity alpha b xHat slot -
          (b (NumStability.higham22ConfluentSlotEquivFin multiplicity slot) -
            (NumStability.higham22ConfluentVandermonde
              multiplicity alpha).transpose.mulVec xHat
                (NumStability.higham22ConfluentSlotEquivFin
                  multiplicity slot))‖ ≤
        ch22bComplexConfluentResidualBudget fp multiplicity alpha b xHat slot := by
  intro slot
  have h := ch22bComplexHigherDerivativeResidual_error_bound fp hgamma2
    (alpha slot.1)
    (b (NumStability.higham22ConfluentSlotEquivFin multiplicity slot))
    (List.ofFn xHat).reverse slot.2.val
  have hformal :
      ch22bComplexFormalDesc (alpha slot.1) (List.ofFn xHat).reverse slot.2.val =
        (NumStability.higham22ConfluentVandermonde
          multiplicity alpha).transpose.mulVec xHat
            (NumStability.higham22ConfluentSlotEquivFin
              multiplicity slot) := by
    rw [ch22bComplexFormalDesc_eq_iterateDerivative_eval,
      ch22bComplexPolyDesc_reverse_ofFn_eq_higham]
    exact (NumStability.higham22_confluentVandermonde_transpose_mulVec_apply
      multiplicity alpha xHat slot).symm
  rw [hformal] at h
  simpa [ch22bComplexConfluentComputedResidual,
    ch22bComplexConfluentResidualBudget] using h

/-- The complex, arbitrary-order confluent residual packaged exactly as the
componentwise residual hypothesis (12.8).  The left side is an executed
Algorithm 5.2 derivative evaluation plus an executed rounded complex
subtraction, and the exact matrix term comes from the Chapter 22 confluent-row
identity. -/
theorem ch22bComplexConfluent_higham12_8_certificate
    {ι : Type*} [Fintype ι] (fp : NumStability.FPModel)
    (hgamma2 : NumStability.gammaValid fp 2) (hu : 0 < fp.u)
    (multiplicity : ι → ℕ) (alpha : ι → ℂ)
    (b xHat : Fin (Fintype.card
      (NumStability.Higham22ConfluentSlot multiplicity)) → ℂ) :
    ∀ slot : NumStability.Higham22ConfluentSlot multiplicity,
      ‖ch22bComplexConfluentComputedResidual fp multiplicity alpha b xHat slot -
          (b (NumStability.higham22ConfluentSlotEquivFin multiplicity slot) -
            (NumStability.higham22ConfluentVandermonde
              multiplicity alpha).transpose.mulVec xHat
                (NumStability.higham22ConfluentSlotEquivFin
                  multiplicity slot))‖ ≤
        fp.u *
          (ch22bComplexConfluentResidualBudget
            fp multiplicity alpha b xHat slot / fp.u) := by
  intro slot
  calc
    ‖ch22bComplexConfluentComputedResidual fp multiplicity alpha b xHat slot -
        (b (NumStability.higham22ConfluentSlotEquivFin multiplicity slot) -
          (NumStability.higham22ConfluentVandermonde
            multiplicity alpha).transpose.mulVec xHat
              (NumStability.higham22ConfluentSlotEquivFin
                multiplicity slot))‖ ≤
      ch22bComplexConfluentResidualBudget
        fp multiplicity alpha b xHat slot :=
      ch22bComplexConfluent_residual_error fp hgamma2
        multiplicity alpha b xHat slot
    _ = fp.u *
        (ch22bComplexConfluentResidualBudget
          fp multiplicity alpha b xHat slot / fp.u) := by field_simp

/-- Complex-norm form of Theorem 12.3's exact one-step inequality (12.14).
It is proved from the same residual identity and triangle inequalities as the
real theorem, so the PDF's stated `ℂ` Vandermonde domain is retained. -/
theorem ch22bComplexHigham12_3_exact_one_step_residual_bound (n : ℕ)
    (A : Fin n → Fin n → ℂ)
    (xHat dHat : Fin n → ℂ) (b r rHat : Fin n → ℂ)
    (f2 y : Fin n → ℂ) (u : ℝ)
    (gTerm hTerm tTerm : Fin n → ℝ)
    (hr : ∀ i : Fin n, r i = b i - ∑ j : Fin n, A i j * xHat j)
    (hy : ∀ i : Fin n, y i = xHat i + dHat i + f2 i)
    (hf1 : ∀ i : Fin n,
      ‖rHat i - ∑ j : Fin n, A i j * dHat j‖ ≤
        u * (gTerm i + hTerm i))
    (hDeltaR : ∀ i : Fin n, ‖rHat i - r i‖ ≤ u * tTerm i)
    (hf2 : ∀ j : Fin n,
      ‖f2 j‖ ≤ u * (‖xHat j‖ + ‖dHat j‖)) :
    ∀ i : Fin n,
      ‖b i - ∑ j : Fin n, A i j * y j‖ ≤
        u * (gTerm i + hTerm i) + u * tTerm i +
          u * ∑ j : Fin n, ‖A i j‖ * (‖xHat j‖ + ‖dHat j‖) := by
  intro i
  have hid : b i - ∑ j : Fin n, A i j * y j =
      (rHat i - ∑ j : Fin n, A i j * dHat j) - (rHat i - r i) -
        ∑ j : Fin n, A i j * f2 j := by
    rw [hr i]
    simp_rw [hy, mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    ring
  have hsum : ‖∑ j : Fin n, A i j * f2 j‖ ≤
      u * ∑ j : Fin n, ‖A i j‖ * (‖xHat j‖ + ‖dHat j‖) := by
    calc
      ‖∑ j : Fin n, A i j * f2 j‖ ≤
          ∑ j : Fin n, ‖A i j * f2 j‖ := norm_sum_le _ _
      _ = ∑ j : Fin n, ‖A i j‖ * ‖f2 j‖ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [norm_mul]
      _ ≤ ∑ j : Fin n, ‖A i j‖ *
          (u * (‖xHat j‖ + ‖dHat j‖)) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hf2 j) (norm_nonneg _)
      _ = u * ∑ j : Fin n, ‖A i j‖ *
          (‖xHat j‖ + ‖dHat j‖) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [hid]
  calc
    ‖(rHat i - ∑ j : Fin n, A i j * dHat j) - (rHat i - r i) -
        ∑ j : Fin n, A i j * f2 j‖ ≤
      (‖rHat i - ∑ j : Fin n, A i j * dHat j‖ +
        ‖rHat i - r i‖) + ‖∑ j : Fin n, A i j * f2 j‖ :=
      (norm_sub_le _ _).trans
        (add_le_add (norm_sub_le _ _) (le_refl _))
    _ ≤ (u * (gTerm i + hTerm i) + u * tTerm i) +
        u * ∑ j : Fin n, ‖A i j‖ * (‖xHat j‖ + ‖dHat j‖) :=
      add_le_add (add_le_add (hf1 i) (hDeltaR i)) hsum
    _ = u * (gTerm i + hTerm i) + u * tTerm i +
        u * ∑ j : Fin n, ‖A i j‖ * (‖xHat j‖ + ‖dHat j‖) := by ring

/-- Complex-norm exact finite (12.10), with the source's unspecified `O(u)`
remainder displayed rather than assumed. -/
theorem ch22bComplexHigham12_10_exact_q_bound (n : ℕ)
    (A : Fin n → Fin n → ℂ)
    (xHat dHat : Fin n → ℂ) (b r rHat : Fin n → ℂ)
    (f2 y : Fin n → ℂ) (u : ℝ)
    (gTerm hTerm tAtX tAtY : Fin n → ℝ)
    (hr : ∀ i : Fin n, r i = b i - ∑ j : Fin n, A i j * xHat j)
    (hy : ∀ i : Fin n, y i = xHat i + dHat i + f2 i)
    (hf1 : ∀ i : Fin n,
      ‖rHat i - ∑ j : Fin n, A i j * dHat j‖ ≤
        u * (gTerm i + hTerm i))
    (hDeltaR : ∀ i : Fin n, ‖rHat i - r i‖ ≤ u * tAtX i)
    (hf2 : ∀ j : Fin n,
      ‖f2 j‖ ≤ u * (‖xHat j‖ + ‖dHat j‖)) :
    ∀ i : Fin n,
      ‖b i - ∑ j : Fin n, A i j * y j‖ ≤
        u * (hTerm i + tAtY i + ∑ j : Fin n, ‖A i j‖ * ‖y j‖) +
        u * (tAtX i - tAtY i + gTerm i +
          ∑ j : Fin n, ‖A i j‖ *
            (‖xHat j‖ - ‖y j‖ + ‖dHat j‖)) := by
  intro i
  have hbase := ch22bComplexHigham12_3_exact_one_step_residual_bound n
    A xHat dHat b r rHat f2 y u gTerm hTerm tAtX hr hy hf1 hDeltaR hf2 i
  have hsum :
      ∑ j : Fin n, ‖A i j‖ * (‖xHat j‖ - ‖y j‖ + ‖dHat j‖) =
        (∑ j : Fin n, ‖A i j‖ * (‖xHat j‖ + ‖dHat j‖)) -
          ∑ j : Fin n, ‖A i j‖ * ‖y j‖ := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  linarith

/-- **Full Chapter 12 → Chapter 22 complex confluent bridge.**

For every node/derivative slot, the residual is produced by rounded complex
Algorithm 5.2 and rounded subtraction.  Its proved (12.8) certificate is then
composed with the correction solve and rounded update through the exact
complex-norm Theorem 12.3 calculation, yielding finite (12.10). -/
theorem ch22bComplexConfluent_theorem12_3_exact_q_bound
    {ι : Type*} [Fintype ι]
    (fp : NumStability.FPModel)
    (hgamma2 : NumStability.gammaValid fp 2) (hu : 0 < fp.u)
    (multiplicity : ι → ℕ) (alpha : ι → ℂ)
    (b xHat dHat rHat f2 y : Fin (Fintype.card
      (NumStability.Higham22ConfluentSlot multiplicity)) → ℂ)
    (gTerm hTerm tAtY : Fin (Fintype.card
      (NumStability.Higham22ConfluentSlot multiplicity)) → ℝ)
    (hrHat : ∀ i,
      rHat i = ch22bComplexConfluentComputedResidual fp multiplicity alpha
        b xHat ((NumStability.higham22ConfluentSlotEquivFin
          multiplicity).symm i))
    (hy : ∀ i, y i = xHat i + dHat i + f2 i)
    (hf1 : ∀ i,
      ‖rHat i - ∑ j,
        (NumStability.higham22ConfluentVandermonde
          multiplicity alpha).transpose i j * dHat j‖ ≤
        fp.u * (gTerm i + hTerm i))
    (hf2 : ∀ j, ‖f2 j‖ ≤ fp.u * (‖xHat j‖ + ‖dHat j‖)) :
    ∀ i,
      ‖b i - ∑ j,
        (NumStability.higham22ConfluentVandermonde
          multiplicity alpha).transpose i j * y j‖ ≤
        fp.u * (hTerm i + tAtY i + ∑ j,
          ‖(NumStability.higham22ConfluentVandermonde
            multiplicity alpha).transpose i j‖ * ‖y j‖) +
        fp.u *
          (ch22bComplexConfluentResidualBudget fp multiplicity alpha b xHat
              ((NumStability.higham22ConfluentSlotEquivFin
                multiplicity).symm i) / fp.u - tAtY i + gTerm i +
            ∑ j,
              ‖(NumStability.higham22ConfluentVandermonde
                multiplicity alpha).transpose i j‖ *
                (‖xHat j‖ - ‖y j‖ + ‖dHat j‖)) := by
  let N := Fintype.card
    (NumStability.Higham22ConfluentSlot multiplicity)
  let A : Fin N → Fin N → ℂ := fun i j =>
    (NumStability.higham22ConfluentVandermonde
      multiplicity alpha).transpose i j
  let computed : Fin N → ℂ := fun i =>
    ch22bComplexConfluentComputedResidual fp multiplicity alpha b xHat
      ((NumStability.higham22ConfluentSlotEquivFin multiplicity).symm i)
  let budget : Fin N → ℝ := fun i =>
    ch22bComplexConfluentResidualBudget fp multiplicity alpha b xHat
      ((NumStability.higham22ConfluentSlotEquivFin multiplicity).symm i)
  let r : Fin N → ℂ := fun i => b i - ∑ j : Fin N, A i j * xHat j
  let tAtX : Fin N → ℝ := fun i => budget i / fp.u
  have hr : ∀ i : Fin N, r i = b i - ∑ j : Fin N, A i j * xHat j := by
    intro i
    rfl
  have hDeltaR : ∀ i : Fin N, ‖rHat i - r i‖ ≤ fp.u * tAtX i := by
    intro i
    have hc := ch22bComplexConfluent_residual_error fp hgamma2
      multiplicity alpha b xHat
      ((NumStability.higham22ConfluentSlotEquivFin multiplicity).symm i)
    have hc' : ‖computed i - r i‖ ≤ budget i := by
      simpa [computed, budget, r, A, Matrix.mulVec, dotProduct] using hc
    calc
      ‖rHat i - r i‖ = ‖computed i - r i‖ := by rw [hrHat i]
      _ ≤ budget i := hc'
      _ = fp.u * tAtX i := by
        dsimp [tAtX]
        field_simp
  have h12 := ch22bComplexHigham12_10_exact_q_bound N A xHat dHat
    b r rHat f2 y fp.u gTerm hTerm tAtX tAtY hr hy
    (by simpa [A] using hf1) hDeltaR hf2
  simpa [N, A, budget, tAtX] using h12

end NumStability.Ch22B
