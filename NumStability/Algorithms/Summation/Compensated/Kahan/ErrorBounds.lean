-- Algorithms/Summation/Compensated/Kahan/ErrorBounds.lean

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.Error
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.Algorithms.Summation.Compensated.Kahan.Coefficients.Affine
import NumStability.Algorithms.Summation.Compensated.Kahan.Coefficients.Coupled
import NumStability.Algorithms.Summation.Compensated.Kahan.Core
import NumStability.Algorithms.Summation.Compensated.Kahan.Exactness
import NumStability.Algorithms.Summation.Compensated.Kahan.LocalCoefficients
import NumStability.Algorithms.Summation.Compensated.Kahan.Majorants

namespace NumStability

/-!
# Kahan compensated summation: reusable error bounds

This module contains source-independent affine coefficient-existence bridges,
conditional returned-sum and compensated-total backward representations, and
generic forward and relative-error consequences. Finite specializations and
source-model audits live in higher layers.
-/

/-- Exact coefficient representation for the compensated prefix total after
absorbing the propagated retained-correction residual.

This is the first residual-absorption form for the C4.5 Knuth/Kahan route:
the previous theorem gives an additive residual bound around the explicit
product-form input coefficients; this theorem distributes that residual across
the source inputs as sign-aligned coefficient increments.  The remaining work
for (4.8) is to bound the product-form input coefficients themselves and
collapse the displayed radius. -/
theorem kahanAffineCoeffSteps_prefixTotal_exists_mu_inputCoeffResidual
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (hu1 : fp.u ≤ 1)
    (hinputAbs :
      0 < ∑ i : Fin (kahanAffineCoeffSteps fp v k hk).length,
        |((kahanAffineCoeffSteps fp v k hk).get i).x|) :
    let steps := kahanAffineCoeffSteps fp v k hk
    ∃ μ : Fin steps.length → ℝ,
      (∀ i,
        |μ i - kahanAffineInputCoeff steps i| ≤
          kahanAffineCorrectionIndexedBudget
            (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
            (fun j =>
              if hj : j < k then
                (kahanInputAbsMajorant fp v j
                  (Nat.le_trans (Nat.le_of_lt hj) hk)).e
              else 0)
            steps /
            (∑ j : Fin steps.length, |(steps.get j).x|)) ∧
        (kahanPrefixState fp v k hk).s +
          (kahanPrefixState fp v k hk).e =
          ∑ i : Fin steps.length, (steps.get i).x * (1 + μ i) := by
  dsimp
  let steps := kahanAffineCoeffSteps fp v k hk
  let budget :=
    kahanAffineCorrectionIndexedBudget
      (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
      (fun j =>
        if hj : j < k then
          (kahanInputAbsMajorant fp v j
            (Nat.le_trans (Nat.le_of_lt hj) hk)).e
        else 0)
      steps
  have hres :
      |((kahanPrefixState fp v k hk).s +
          (kahanPrefixState fp v k hk).e) -
        (∑ i : Fin steps.length,
          (steps.get i).x * (1 + kahanAffineInputCoeff steps i))| ≤
        budget := by
    simpa [steps, budget] using
      kahanAffineCoeffSteps_prefixTotal_sub_sum_inputCoeff_abs_le_inputMajorantBudget
        fp v k hk hu1
  have hinputAbs' :
      0 < ∑ i : Fin steps.length, |(steps.get i).x| := by
    simpa [steps] using hinputAbs
  simpa [steps, budget] using
    exists_summation_coefficients_of_abs_sub_sum_coeff_le
      (fun i : Fin steps.length => (steps.get i).x)
      (fun i : Fin steps.length => kahanAffineInputCoeff steps i)
      hres hinputAbs'


/-- Exact coefficient representation for the actual returned prefix sum after
absorbing both the propagated retained-correction residual and the final
retained correction.

This is the source-facing residual-absorption dependency for Higham (4.8):
the returned stored sum `s` is now expressed exactly as a coefficient
perturbation of the source inputs.  The coefficient increment beyond
`kahanAffineInputCoeff` is bounded by the propagated residual budget plus the
input-only final-correction majorant, normalized by `sum |x_i|`. -/
theorem kahanAffineCoeffSteps_prefixSum_exists_mu_inputCoeffResidual
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (hu1 : fp.u ≤ 1)
    (hinputAbs :
      0 < ∑ i : Fin (kahanAffineCoeffSteps fp v k hk).length,
        |((kahanAffineCoeffSteps fp v k hk).get i).x|) :
    let steps := kahanAffineCoeffSteps fp v k hk
    ∃ μ : Fin steps.length → ℝ,
      (∀ i,
        |μ i - kahanAffineInputCoeff steps i| ≤
          (kahanAffineCorrectionIndexedBudget
            (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
            (fun j =>
              if hj : j < k then
                (kahanInputAbsMajorant fp v j
                  (Nat.le_trans (Nat.le_of_lt hj) hk)).e
              else 0)
            steps +
            (kahanInputAbsMajorant fp v k hk).e) /
            (∑ j : Fin steps.length, |(steps.get j).x|)) ∧
        (kahanPrefixState fp v k hk).s =
          ∑ i : Fin steps.length, (steps.get i).x * (1 + μ i) := by
  dsimp
  let steps := kahanAffineCoeffSteps fp v k hk
  let budget :=
    kahanAffineCorrectionIndexedBudget
      (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
      (fun j =>
        if hj : j < k then
          (kahanInputAbsMajorant fp v j
            (Nat.le_trans (Nat.le_of_lt hj) hk)).e
        else 0)
      steps +
      (kahanInputAbsMajorant fp v k hk).e
  have hres :
      |(kahanPrefixState fp v k hk).s -
        (∑ i : Fin steps.length,
          (steps.get i).x * (1 + kahanAffineInputCoeff steps i))| ≤
        budget := by
    simpa [steps, budget] using
      kahanAffineCoeffSteps_prefixSum_sub_sum_inputCoeff_abs_le_inputMajorantBudget
        fp v k hk hu1
  have hinputAbs' :
      0 < ∑ i : Fin steps.length, |(steps.get i).x| := by
    simpa [steps] using hinputAbs
  simpa [steps, budget] using
    exists_summation_coefficients_of_abs_sub_sum_coeff_le
      (fun i : Fin steps.length => (steps.get i).x)
      (fun i : Fin steps.length => kahanAffineInputCoeff steps i)
      hres hinputAbs'

/-- Returned-prefix-sum coefficient witnesses with the product-form input
coefficient radius made explicit.

This combines the exact residual-absorption theorem with the bound on
`kahanAffineInputCoeff`.  The remaining C4.5 work is to collapse the displayed
product radius and the normalized residual budget to the source-shaped
`2*u + C*n*u^2` form. -/
theorem kahanAffineCoeffSteps_prefixSum_exists_mu_abs_le_productRadius
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (hu1 : fp.u ≤ 1)
    (hinputAbs :
      0 < ∑ i : Fin (kahanAffineCoeffSteps fp v k hk).length,
        |((kahanAffineCoeffSteps fp v k hk).get i).x|) :
    let steps := kahanAffineCoeffSteps fp v k hk
    ∃ μ : Fin steps.length → ℝ,
      (∀ i,
        |μ i| ≤
          kahanAffineInputCoeffProductRadius fp steps i +
            (kahanAffineCorrectionIndexedBudget
              (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
              (fun j =>
                if hj : j < k then
                  (kahanInputAbsMajorant fp v j
                    (Nat.le_trans (Nat.le_of_lt hj) hk)).e
                else 0)
              steps +
              (kahanInputAbsMajorant fp v k hk).e) /
              (∑ j : Fin steps.length, |(steps.get j).x|)) ∧
        (kahanPrefixState fp v k hk).s =
          ∑ i : Fin steps.length, (steps.get i).x * (1 + μ i) := by
  dsimp
  let steps := kahanAffineCoeffSteps fp v k hk
  let residual :=
    (kahanAffineCorrectionIndexedBudget
      (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
      (fun j =>
        if hj : j < k then
          (kahanInputAbsMajorant fp v j
            (Nat.le_trans (Nat.le_of_lt hj) hk)).e
        else 0)
      steps +
      (kahanInputAbsMajorant fp v k hk).e) /
      (∑ j : Fin steps.length, |(steps.get j).x|)
  obtain ⟨μ, hμdiff, hμeq⟩ :=
    kahanAffineCoeffSteps_prefixSum_exists_mu_inputCoeffResidual
      fp v k hk hu1 hinputAbs
  refine ⟨μ, ?_, ?_⟩
  · intro i
    have hcoeff :
        |kahanAffineInputCoeff steps i| ≤
          kahanAffineInputCoeffProductRadius fp steps i := by
      simpa [steps] using
        kahanAffineCoeffSteps_inputCoeff_abs_le_productRadius
          fp v k hk hu1 i
    have hdiff :
        |μ i - kahanAffineInputCoeff steps i| ≤ residual := by
      simpa [steps, residual] using hμdiff i
    calc
      |μ i| =
          |(μ i - kahanAffineInputCoeff steps i) +
            kahanAffineInputCoeff steps i| := by ring_nf
      _ ≤ |μ i - kahanAffineInputCoeff steps i| +
            |kahanAffineInputCoeff steps i| := abs_add_le _ _
      _ ≤ residual +
            kahanAffineInputCoeffProductRadius fp steps i := by
          exact add_le_add hdiff hcoeff
      _ =
          kahanAffineInputCoeffProductRadius fp steps i + residual := by
          ring
  · simpa [steps] using hμeq

/-- Source-shaped returned-prefix Kahan backward-error bridge from a product
radius and a source-scaled retained-correction residual budget.

This is the residual-budget version of the affine Goldberg/Knuth route: if the
product-form current-input coefficients are bounded by `P` and the remaining
retained-correction contribution is at most `D * sum_i |x_i|`, then the actual
stored prefix sum has exact source coefficients bounded by `P + D`. -/
theorem kahanAffineCoeffSteps_prefixSum_exists_mu_abs_le_of_productRadius_and_residualBudget
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (hu1 : fp.u ≤ 1)
    {P D : ℝ}
    (hP :
      let steps := kahanAffineCoeffSteps fp v k hk
      ∀ i : Fin steps.length,
        kahanAffineInputCoeffProductRadius fp steps i ≤ P)
    (hD_nonneg : 0 ≤ D)
    (hResidual :
      let steps := kahanAffineCoeffSteps fp v k hk
      kahanAffineCorrectionIndexedBudget
          (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
          (fun j =>
            if hj : j < k then
              (kahanInputAbsMajorant fp v j
                (Nat.le_trans (Nat.le_of_lt hj) hk)).e
            else 0)
          steps +
          (kahanInputAbsMajorant fp v k hk).e ≤
        D * (∑ j : Fin steps.length, |(steps.get j).x|)) :
    let steps := kahanAffineCoeffSteps fp v k hk
    ∃ μ : Fin steps.length → ℝ,
      (∀ i, |μ i| ≤ P + D) ∧
        (kahanPrefixState fp v k hk).s =
          ∑ i : Fin steps.length, (steps.get i).x * (1 + μ i) := by
  dsimp
  let steps := kahanAffineCoeffSteps fp v k hk
  let base : ℝ :=
    ∑ i : Fin steps.length,
      (steps.get i).x * (1 + kahanAffineInputCoeff steps i)
  let residualBudget : ℝ :=
    kahanAffineCorrectionIndexedBudget
      (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
      (fun j =>
        if hj : j < k then
          (kahanInputAbsMajorant fp v j
            (Nat.le_trans (Nat.le_of_lt hj) hk)).e
        else 0)
      steps +
      (kahanInputAbsMajorant fp v k hk).e
  let r : ℝ := (kahanPrefixState fp v k hk).s - base
  have hres0 : |r| ≤ residualBudget := by
    dsimp [r, base, residualBudget]
    simpa [steps] using
      kahanAffineCoeffSteps_prefixSum_sub_sum_inputCoeff_abs_le_inputMajorantBudget
        fp v k hk hu1
  have hResidual' :
      residualBudget ≤
        D * (∑ j : Fin steps.length, |(steps.get j).x|) := by
    simpa [steps, residualBudget] using hResidual
  have hres :
      |r| ≤ D * (∑ j : Fin steps.length, |(steps.get j).x|) :=
    hres0.trans hResidual'
  obtain ⟨η, hη, hηeq⟩ :=
    exists_summation_source_coefficients_of_abs_le_mul_sum_abs
      (fun i : Fin steps.length => (steps.get i).x)
      hD_nonneg hres
  let μ : Fin steps.length → ℝ :=
    fun i => kahanAffineInputCoeff steps i + η i
  refine ⟨μ, ?_, ?_⟩
  · intro i
    have hcoeff0 :
        |kahanAffineInputCoeff steps i| ≤
          kahanAffineInputCoeffProductRadius fp steps i := by
      simpa [steps] using
        kahanAffineCoeffSteps_inputCoeff_abs_le_productRadius
          fp v k hk hu1 i
    have hcoeff :
        |kahanAffineInputCoeff steps i| ≤ P := by
      exact hcoeff0.trans (by simpa [steps] using hP i)
    calc
      |μ i| =
          |kahanAffineInputCoeff steps i + η i| := by rfl
      _ ≤ |kahanAffineInputCoeff steps i| + |η i| := abs_add_le _ _
      _ ≤ P + D := add_le_add hcoeff (hη i)
  · have hηeq' :
        r = ∑ i : Fin steps.length, (steps.get i).x * η i := by
      simpa using hηeq
    calc
      (kahanPrefixState fp v k hk).s = base + r := by
        dsimp [r]
        ring
      _ = base + ∑ i : Fin steps.length, (steps.get i).x * η i := by
        rw [hηeq']
      _ = ∑ i : Fin steps.length, (steps.get i).x * (1 + μ i) := by
        dsimp [base, μ]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        ring

/-- Final returned-Kahan source bound from affine product smallness and a
source-scaled retained-correction budget.

The theorem packages the remaining Eq. (4.8) ordinary returned-sum work into a
single interpretable estimate: the propagated retained-correction budget must
be bounded by `C * n * u^2 * sum_i |x_i|`.  Under that estimate and the standard
small product condition, the returned Kahan sum has source coefficients with
radius `2*u + (9 + (72 + C)*n)*u^2`. -/
theorem fl_kahanSum_backward_error_source_bound_of_affine_residualBudget
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hu1 : fp.u ≤ 1)
    {C : ℝ} (hC_nonneg : 0 ≤ C)
    (hProductSmall : (n : ℝ) * (3 * fp.u ^ 2) ≤ 1 / 2)
    (hResidual :
      let steps := kahanAffineCoeffSteps fp v n (Nat.le_refl n)
      kahanAffineCorrectionIndexedBudget
          (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
          (fun j =>
            if hj : j < n then
              (kahanInputAbsMajorant fp v j (Nat.le_of_lt hj)).e
            else 0)
          steps +
          (kahanInputAbsMajorant fp v n (Nat.le_refl n)).e ≤
        (C * (n : ℝ) * fp.u ^ 2) *
          (∑ j : Fin steps.length, |(steps.get j).x|)) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fp.u + (9 + (72 + C) * (n : ℝ)) * fp.u ^ 2) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  let steps := kahanAffineCoeffSteps fp v n (Nat.le_refl n)
  let P : ℝ := 2 * fp.u + (9 + 72 * (n : ℝ)) * fp.u ^ 2
  let D : ℝ := C * (n : ℝ) * fp.u ^ 2
  have hlen : n = steps.length := by
    simp [steps, kahanAffineCoeffSteps]
  have hP :
      ∀ i : Fin steps.length,
        kahanAffineInputCoeffProductRadius fp steps i ≤ P := by
    intro i
    have hdrop_nat :
        (steps.drop (i.val + 1)).length ≤ steps.length := by
      rw [List.length_drop]
      exact Nat.sub_le steps.length (i.val + 1)
    have hdrop_le :
        ((steps.drop (i.val + 1)).length : ℝ) ≤ (n : ℝ) := by
      have hdrop_le_steps :
          ((steps.drop (i.val + 1)).length : ℝ) ≤
            (steps.length : ℝ) := by
        exact_mod_cast hdrop_nat
      have hsteps_len : (steps.length : ℝ) = (n : ℝ) := by
        exact_mod_cast hlen.symm
      rw [hsteps_len] at hdrop_le_steps
      exact hdrop_le_steps
    have hc_nonneg : 0 ≤ 3 * fp.u ^ 2 := by
      nlinarith [sq_nonneg fp.u]
    have hsmall_i :
        ((steps.drop (i.val + 1)).length : ℝ) *
            (3 * fp.u ^ 2) ≤ 1 / 2 := by
      have hmul := mul_le_mul_of_nonneg_right hdrop_le hc_nonneg
      exact hmul.trans hProductSmall
    have hlocal :=
      kahanAffineInputCoeffProductRadius_le_two_u_plus
        fp steps i hu1 hsmall_i
    have hcoef :
        9 + 72 * ((steps.drop (i.val + 1)).length : ℝ) ≤
          9 + 72 * (n : ℝ) := by
      nlinarith
    have hcoef_mul :
        (9 + 72 * ((steps.drop (i.val + 1)).length : ℝ)) *
            fp.u ^ 2 ≤
          (9 + 72 * (n : ℝ)) * fp.u ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg fp.u)
    dsimp [P]
    nlinarith
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg
      (mul_nonneg hC_nonneg (by exact_mod_cast Nat.zero_le n))
      (sq_nonneg fp.u)
  have hprefix :
      ∃ μs : Fin steps.length → ℝ,
        (∀ i, |μs i| ≤ P + D) ∧
          (kahanPrefixState fp v n (Nat.le_refl n)).s =
            ∑ i : Fin steps.length, (steps.get i).x * (1 + μs i) := by
    simpa [steps, P, D] using
      (kahanAffineCoeffSteps_prefixSum_exists_mu_abs_le_of_productRadius_and_residualBudget
        fp v n (Nat.le_refl n) hu1
        (P := P) (D := D)
        (by simpa [steps, P] using hP)
        hD_nonneg
        (by simpa [steps, D] using hResidual))
  obtain ⟨μSteps, hμSteps, hsumSteps⟩ := hprefix
  let idx : Fin n → Fin steps.length := fun i => finCongr hlen i
  let μ : Fin n → ℝ := fun i => μSteps (idx i)
  refine ⟨μ, ?_, ?_⟩
  · intro i
    have hcollapse :
        P + D =
          2 * fp.u + (9 + (72 + C) * (n : ℝ)) * fp.u ^ 2 := by
      dsimp [P, D]
      ring
    simpa [μ, hcollapse] using hμSteps (idx i)
  · have hsum_reindex :
        (∑ i : Fin n, v i * (1 + μ i)) =
          ∑ j : Fin steps.length,
            (steps.get j).x * (1 + μSteps j) := by
      refine Fintype.sum_equiv (finCongr hlen) _ _ ?_
      intro i
      dsimp [μ, idx]
      simp [steps, kahanAffineCoeffSteps, kahanAffineCoeffStepOfIndex]
    simpa [fl_kahanSum, fl_kahanState, steps] using
      hsumSteps.trans hsum_reindex.symm

/-- Source-shaped backward-error bridge for the ordinary returned Kahan sum
from a supplied per-input returned-source coefficient bound.

This theorem deliberately keeps the coefficient bound as a hypothesis.  The
open Higham equation (4.8) work is exactly to prove that hypothesis with
`B = 2*u + O(n*u^2)` from the floating-point assumptions. -/
theorem fl_kahanSum_backward_error_source_bound_of_sourceCoeff_s_bound
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) {B : ℝ}
    (hcoeff :
      let steps := kahanCoupledCoeffSteps fp v n (Nat.le_refl n)
      ∀ i : Fin steps.length,
        |(kahanCoupledSourceCoeff steps i).s - 1| ≤ B) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ B) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  let steps := kahanCoupledCoeffSteps fp v n (Nat.le_refl n)
  have hcoeff' :
      ∀ i : Fin steps.length,
        |(kahanCoupledSourceCoeff steps i).s - 1| ≤ B := by
    simpa [steps] using hcoeff
  have hlen : n = steps.length := by
    simp [steps, kahanCoupledCoeffSteps]
  let idx : Fin n → Fin steps.length := fun i => finCongr hlen i
  let μ : Fin n → ℝ := fun i => (kahanCoupledSourceCoeff steps (idx i)).s - 1
  refine ⟨μ, ?_, ?_⟩
  · intro i
    dsimp [μ]
    exact hcoeff' (idx i)
  · have hs :=
      kahanCoupledCoeffSteps_prefixState_s_eq_sum_sourceCoeff
        fp v n (Nat.le_refl n)
    have hsum :
        (∑ i : Fin n, v i * (1 + μ i)) =
          ∑ j : Fin steps.length,
            (steps.get j).x * (kahanCoupledSourceCoeff steps j).s := by
      refine Fintype.sum_equiv (finCongr hlen) _ _ ?_
      intro i
      dsimp [μ, idx]
      simp [steps, kahanCoupledCoeffSteps, kahanCoupledCoeffStepOfIndex]
    simpa [fl_kahanSum, fl_kahanState, steps] using hs.trans hsum.symm

/-- Source-shaped backward-error bridge for the ordinary returned Kahan sum
from explicit witness-family source coefficient bounds.

This is the witness-parametric companion of
`fl_kahanSum_backward_error_source_bound_of_sourceCoeff_s_bound`; it is the
right surface for the exact-subtraction route because the witness family can
be chosen constructively from finite-format/coherence hypotheses. -/
theorem fl_kahanSum_backward_error_source_bound_of_witnessSourceCoeff_s_bound
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (W : KahanPrefixDeltaWitnessFamily fp v n (Nat.le_refl n)) {B : ℝ}
    (hcoeff :
      let steps := kahanCoupledCoeffStepsOfWitnesses fp v n (Nat.le_refl n) W
      ∀ i : Fin steps.length,
        |(kahanCoupledSourceCoeff steps i).s - 1| ≤ B) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ B) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  let steps := kahanCoupledCoeffStepsOfWitnesses fp v n (Nat.le_refl n) W
  have hcoeff' :
      ∀ i : Fin steps.length,
        |(kahanCoupledSourceCoeff steps i).s - 1| ≤ B := by
    simpa [steps] using hcoeff
  have hlen : n = steps.length := by
    simp [steps, kahanCoupledCoeffStepsOfWitnesses]
  let idx : Fin n → Fin steps.length := fun i => finCongr hlen i
  let μ : Fin n → ℝ := fun i => (kahanCoupledSourceCoeff steps (idx i)).s - 1
  refine ⟨μ, ?_, ?_⟩
  · intro i
    dsimp [μ]
    exact hcoeff' (idx i)
  · have hs :=
      kahanCoupledCoeffStepsOfWitnesses_prefixState_s_eq_sum_sourceCoeff
        fp v n (Nat.le_refl n) W
    have hsum :
        (∑ i : Fin n, v i * (1 + μ i)) =
          ∑ j : Fin steps.length,
            (steps.get j).x * (kahanCoupledSourceCoeff steps j).s := by
      refine Fintype.sum_equiv (finCongr hlen) _ _ ?_
      intro i
      dsimp [μ, idx]
      simp [steps, kahanCoupledCoeffStepsOfWitnesses,
        kahanCoupledCoeffStepOfWitness]
    simpa [fl_kahanSum, fl_kahanState, steps] using hs.trans hsum.symm

/-- Conditional source-shaped backward-error representation for the ordinary
returned Kahan sum along an explicit exact-subtraction witness-family route.

This is the Eq. (4.8)-shaped formal surface still missing from the arbitrary
chosen-witness route: the only remaining finite-format obligation is to
construct a witness family satisfying `deltaSub = 0` at each correction
subtraction. -/
theorem fl_kahanSum_backward_error_source_bound_of_exactSubWitnesses
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (W : KahanPrefixDeltaWitnessFamily fp v n (Nat.le_refl n))
    (huSmall : fp.u ≤ 1 / 64)
    (hExactSub :
      kahanCoupledCoeffStepsOfWitnessesExactSub fp v n (Nat.le_refl n) W)
    (hBudget : (3 + 40 * (n : ℝ)) * fp.u ≤ 1) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fp.u + 2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  let steps := kahanCoupledCoeffStepsOfWitnesses fp v n (Nat.le_refl n) W
  refine
    fl_kahanSum_backward_error_source_bound_of_witnessSourceCoeff_s_bound
      fp n v W ?_
  dsimp
  intro j
  have hdrop_nat :
      (steps.drop (j.val + 1)).length ≤ steps.length := by
    rw [List.length_drop]
    exact Nat.sub_le steps.length (j.val + 1)
  have hlen : n = steps.length := by
    simp [steps, kahanCoupledCoeffStepsOfWitnesses]
  have hdrop_le :
      ((steps.drop (j.val + 1)).length : ℝ) ≤ (n : ℝ) := by
    have hdrop_le_steps :
        ((steps.drop (j.val + 1)).length : ℝ) ≤
          (steps.length : ℝ) := by
      exact_mod_cast hdrop_nat
    simp [hlen] at hdrop_le_steps ⊢
  have hbudget_j :
      (3 + 40 * ((steps.drop (j.val + 1)).length : ℝ)) *
          fp.u ≤ 1 := by
    have hcoef :
        3 + 40 * ((steps.drop (j.val + 1)).length : ℝ) ≤
          3 + 40 * (n : ℝ) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hcoef fp.u_nonneg
    nlinarith
  have hcoeff :=
    kahanCoupledCoeffStepsOfWitnesses_sourceCoeff_s_abs_sub_one_le_two_u_plus_exactSubMajorant
      fp v n (Nat.le_refl n) W huSmall hExactSub j
      (by simpa [steps] using hbudget_j)
  have htarget :
      |(kahanCoupledSourceCoeff steps j).s - 1| ≤
        2 * fp.u +
          2 * (3 + 40 * ((steps.drop (j.val + 1)).length : ℝ)) *
            fp.u ^ 2 := by
    simpa [steps] using hcoeff
  have hcoef2 :
      2 * (3 + 40 * ((steps.drop (j.val + 1)).length : ℝ)) *
          fp.u ^ 2 ≤
        2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2 := by
    have hcoef :
        3 + 40 * ((steps.drop (j.val + 1)).length : ℝ) ≤
          3 + 40 * (n : ℝ) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hcoef (sq_nonneg fp.u)
    nlinarith
  nlinarith

/-- Conditional source-shaped backward-error representation for the ordinary
returned Kahan sum from exact correction subtraction in the actual prefix
trace.

This composes the operation-level exact-subtraction surface with the explicit
witness-family route, so callers no longer need to manipulate roundoff
witnesses directly.  The remaining finite-format work is to prove
`KahanPrefixCorrectionSubExact` from concrete correction-formula/coherence
hypotheses. -/
theorem fl_kahanSum_backward_error_source_bound_of_exactSubTrace
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hExactSubTrace :
      KahanPrefixCorrectionSubExact fp v n (Nat.le_refl n))
    (huSmall : fp.u ≤ 1 / 64)
    (hBudget : (3 + 40 * (n : ℝ)) * fp.u ≤ 1) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fp.u + 2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  let W :=
    kahanPrefixDeltaWitnessFamilyOfExactSub
      fp v n (Nat.le_refl n) hExactSubTrace
  have hW :
      kahanCoupledCoeffStepsOfWitnessesExactSub
        fp v n (Nat.le_refl n) W := by
    simpa [W] using
      kahanPrefixDeltaWitnessFamilyOfExactSub_exactSub
        fp v n (Nat.le_refl n) hExactSubTrace
  exact
    fl_kahanSum_backward_error_source_bound_of_exactSubWitnesses
      fp n v W huSmall hW hBudget

/-- Source-shaped backward-error representation for the compensated total
`s+e` retained by Algorithm 4.2.

This closes the paired-total Goldberg/Knuth coefficient route with an explicit
loose `2*u + O(n*u^2)` bound.  It is an intermediate theorem for the
compensated total, not the still-open Higham equation (4.8) theorem for the
ordinary returned value `fl_kahanSum`. -/
theorem fl_kahanCompensatedTotal_backward_error_source_bound
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (huSmall : fp.u ≤ 1 / 64)
    (hBudget : (9 + 200 * (n : ℝ)) * fp.u ≤ 1) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ 2 * fp.u + (9 + 200 * (n : ℝ)) * fp.u ^ 2) ∧
      (fl_kahanState fp n v).s + (fl_kahanState fp n v).e =
        ∑ i : Fin n, v i * (1 + μ i) := by
  let steps := kahanCoupledCoeffSteps fp v n (Nat.le_refl n)
  have hlen : n = steps.length := by
    simp [steps, kahanCoupledCoeffSteps]
  let idx : Fin n → Fin steps.length := fun i => finCongr hlen i
  let μ : Fin n → ℝ := fun i => kahanCoupledSourceTotalCoeff steps (idx i) - 1
  refine ⟨μ, ?_, ?_⟩
  · intro i
    dsimp [μ]
    have hdrop_nat :
        (steps.drop ((idx i).val + 1)).length ≤ steps.length := by
      rw [List.length_drop]
      exact Nat.sub_le steps.length ((idx i).val + 1)
    have hdrop_le :
        ((steps.drop ((idx i).val + 1)).length : ℝ) ≤ (n : ℝ) := by
      have hdrop_le_steps :
          ((steps.drop ((idx i).val + 1)).length : ℝ) ≤
            (steps.length : ℝ) := by
        exact_mod_cast hdrop_nat
      simpa [hlen] using hdrop_le_steps
    have hbudget_i :
        (9 + 200 * ((steps.drop ((idx i).val + 1)).length : ℝ)) *
            fp.u ≤ 1 := by
      have hcoef :
          9 + 200 * ((steps.drop ((idx i).val + 1)).length : ℝ) ≤
            9 + 200 * (n : ℝ) := by nlinarith
      have hmul := mul_le_mul_of_nonneg_right hcoef fp.u_nonneg
      nlinarith
    have hcoeff :=
      kahanCoupledCoeffSteps_sourceTotalCoeff_abs_sub_one_le_two_u_plus_majorant
        fp v n (Nat.le_refl n) huSmall (idx i)
        (by simpa [steps] using hbudget_i)
    have htarget :
        |kahanCoupledSourceTotalCoeff steps (idx i) - 1| ≤
          2 * fp.u +
            (9 + 200 * ((steps.drop ((idx i).val + 1)).length : ℝ)) *
              fp.u ^ 2 := by
      simpa [steps] using hcoeff
    have hcoef2 :
        (9 + 200 * ((steps.drop ((idx i).val + 1)).length : ℝ)) *
            fp.u ^ 2 ≤
          (9 + 200 * (n : ℝ)) * fp.u ^ 2 := by
      have hcoef :
          9 + 200 * ((steps.drop ((idx i).val + 1)).length : ℝ) ≤
            9 + 200 * (n : ℝ) := by nlinarith
      exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg fp.u)
    nlinarith
  · have htotal :=
      kahanCoupledCoeffSteps_prefixState_total_eq_sum_sourceTotalCoeff
        fp v n (Nat.le_refl n)
    have hsum :
        (∑ i : Fin n, v i * (1 + μ i)) =
          ∑ j : Fin steps.length,
            (steps.get j).x * kahanCoupledSourceTotalCoeff steps j := by
      refine Fintype.sum_equiv (finCongr hlen) _ _ ?_
      intro i
      dsimp [μ, idx]
      simp [steps, kahanCoupledCoeffSteps, kahanCoupledCoeffStepOfIndex]
    simpa [fl_kahanState, steps] using htotal.trans hsum.symm



/-- Generic algebraic bridge from a Kahan-style backward-error representation
to the corresponding absolute forward-error bound.

This is the checked "corresponding forward bound" step used by Higham's
transition from (4.8) to (4.9); the hard part is still proving the displayed
Knuth/Kahan backward-error witnesses for the concrete rounded trace. -/
lemma kahan_backward_error_forward_bound_core
    {n : ℕ} (v : Fin n → ℝ) {computed B : ℝ}
    (hback :
      ∃ μ : Fin n → ℝ,
        (∀ i, |μ i| ≤ B) ∧
        computed = ∑ i : Fin n, v i * (1 + μ i)) :
    |computed - ∑ i : Fin n, v i| ≤
      B * ∑ i : Fin n, |v i| := by
  rcases hback with ⟨μ, hμ, hcomputed⟩
  have hdecomp :
      computed - ∑ i : Fin n, v i = ∑ i : Fin n, v i * μ i := by
    rw [hcomputed, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hdecomp]
  calc
    |∑ i : Fin n, v i * μ i|
        ≤ ∑ i : Fin n, |v i * μ i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin n, |v i| * |μ i| := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [abs_mul]
    _ ≤ ∑ i : Fin n, |v i| * B :=
          Finset.sum_le_sum fun i _hi =>
            mul_le_mul_of_nonneg_left (hμ i) (abs_nonneg _)
    _ = B * ∑ i : Fin n, |v i| := by
          rw [← Finset.sum_mul, mul_comm]

/-- If the ordinary Kahan returned sum satisfies a backward-error
representation with componentwise perturbation bound `B`, then it satisfies
the corresponding absolute forward-error bound. -/
theorem fl_kahanSum_forward_error_bound_of_backward
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) {B : ℝ}
    (hback :
      ∃ μ : Fin n → ℝ,
        (∀ i, |μ i| ≤ B) ∧
        fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i)) :
    |fl_kahanSum fp n v - ∑ i : Fin n, v i| ≤
      B * ∑ i : Fin n, |v i| :=
  kahan_backward_error_forward_bound_core v hback

/-- One-signed relative-error consequence of a supplied ordinary Kahan
backward-error representation. -/
theorem fl_kahanSum_relError_le_of_backward_oneSigned
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) {B : ℝ}
    (hback :
      ∃ μ : Fin n → ℝ,
        (∀ i, |μ i| ≤ B) ∧
        fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i))
    (hv : OneSigned v) (hsum : (∑ i : Fin n, v i) ≠ 0) :
    relError (fl_kahanSum fp n v) (∑ i : Fin n, v i) ≤ B := by
  have hden : 0 < |∑ i : Fin n, v i| := abs_pos.mpr hsum
  have hbound := fl_kahanSum_forward_error_bound_of_backward fp n v hback
  have hbound_one :
      |fl_kahanSum fp n v - ∑ i : Fin n, v i| ≤
        B * |∑ i : Fin n, v i| := by
    simpa [sum_abs_eq_abs_sum_of_oneSigned v hv] using hbound
  unfold relError
  rw [div_le_iff₀ hden]
  exact hbound_one

/-- Forward-error bridge for the final-corrected Kahan variant.  The supplied
backward-error representation can use the stronger bound promised by Kahan's
machine-dependent theorem once that theorem is formalized. -/
theorem fl_kahanFinalCorrectedSum_forward_error_bound_of_backward
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) {B : ℝ}
    (hback :
      ∃ μ : Fin n → ℝ,
        (∀ i, |μ i| ≤ B) ∧
        fl_kahanFinalCorrectedSum fp n v =
          ∑ i : Fin n, v i * (1 + μ i)) :
    |fl_kahanFinalCorrectedSum fp n v - ∑ i : Fin n, v i| ≤
      B * ∑ i : Fin n, |v i| :=
  kahan_backward_error_forward_bound_core v hback

/-- One-signed relative-error consequence for the final-corrected Kahan
variant from a supplied backward-error representation. -/
theorem fl_kahanFinalCorrectedSum_relError_le_of_backward_oneSigned
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) {B : ℝ}
    (hback :
      ∃ μ : Fin n → ℝ,
        (∀ i, |μ i| ≤ B) ∧
        fl_kahanFinalCorrectedSum fp n v =
          ∑ i : Fin n, v i * (1 + μ i))
    (hv : OneSigned v) (hsum : (∑ i : Fin n, v i) ≠ 0) :
    relError (fl_kahanFinalCorrectedSum fp n v)
        (∑ i : Fin n, v i) ≤ B := by
  have hden : 0 < |∑ i : Fin n, v i| := abs_pos.mpr hsum
  have hbound :=
    fl_kahanFinalCorrectedSum_forward_error_bound_of_backward fp n v hback
  have hbound_one :
      |fl_kahanFinalCorrectedSum fp n v - ∑ i : Fin n, v i| ≤
        B * |∑ i : Fin n, v i| := by
    simpa [sum_abs_eq_abs_sum_of_oneSigned v hv] using hbound
  unfold relError
  rw [div_le_iff₀ hden]
  exact hbound_one

end NumStability
