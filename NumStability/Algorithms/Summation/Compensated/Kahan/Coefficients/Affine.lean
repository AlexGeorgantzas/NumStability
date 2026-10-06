-- Algorithms/Summation/Compensated/Kahan/Coefficients/Affine.lean

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Analysis.Rounding
import NumStability.Algorithms.Summation.Compensated.Kahan.Core
import NumStability.Algorithms.Summation.Compensated.Kahan.Internal.FinFold
import NumStability.Algorithms.Summation.Compensated.Kahan.LocalCoefficients
import NumStability.Algorithms.Summation.Compensated.Kahan.Majorants

namespace NumStability

/-!
# Kahan compensated summation: affine coefficients

This module develops the reusable residual-aware affine coefficient algebra,
its realization on Kahan traces, and residual inequalities. Coefficient
existence bridges and source-model results live in higher analysis layers.
-/

/-- One step of the residual-aware affine coefficient recurrence that remains
after the local Kahan compensated-total algebra has exposed coefficients for
the previous total, current input, and retained correction. -/
structure KahanAffineCoeffStep where
  A : ℝ
  B : ℝ
  R : ℝ
  x : ℝ
  e : ℝ

/-- Source contribution of one residual-aware affine coefficient step. -/
def KahanAffineCoeffStep.source (step : KahanAffineCoeffStep) : ℝ :=
  step.B * step.x + step.R * step.e

/-- Input contribution of one residual-aware affine coefficient step. -/
def KahanAffineCoeffStep.inputSource (step : KahanAffineCoeffStep) : ℝ :=
  step.B * step.x

/-- Retained-correction contribution of one residual-aware affine coefficient
step. -/
def KahanAffineCoeffStep.correctionSource
    (step : KahanAffineCoeffStep) : ℝ :=
  step.R * step.e

/-- The source contribution splits into the current-input part and the
retained-correction part. -/
theorem KahanAffineCoeffStep.source_eq_input_add_correction
    (step : KahanAffineCoeffStep) :
    step.source = step.inputSource + step.correctionSource := by
  rfl

/-- Product of the old-total coefficients along a coefficient-step suffix. -/
def kahanAffineCoeffTailProd : List KahanAffineCoeffStep → ℝ
  | [] => 1
  | step :: steps => step.A * kahanAffineCoeffTailProd steps

/-- Explicit unrolling of a residual-aware affine coefficient recurrence.

For each step, the source contribution is multiplied by the product of all
later old-total coefficients.  This is the product-form algebra needed before
the ordinary Kahan `mu_i` recursion can bound or absorb retained corrections. -/
def kahanAffineResidualUnroll : List KahanAffineCoeffStep → ℝ
  | [] => 0
  | step :: steps =>
      kahanAffineCoeffTailProd steps * step.source +
        kahanAffineResidualUnroll steps

/-- Product-form unrolling of only the current-input source contributions. -/
def kahanAffineInputUnroll : List KahanAffineCoeffStep → ℝ
  | [] => 0
  | step :: steps =>
      kahanAffineCoeffTailProd steps * step.inputSource +
        kahanAffineInputUnroll steps

/-- Product-form unrolling of only the retained-correction source
contributions. -/
def kahanAffineCorrectionUnroll : List KahanAffineCoeffStep → ℝ
  | [] => 0
  | step :: steps =>
      kahanAffineCoeffTailProd steps * step.correctionSource +
        kahanAffineCorrectionUnroll steps

/-- Absolute-value majorant for the retained-correction product-form
contribution. -/
def kahanAffineCorrectionAbsUnroll : List KahanAffineCoeffStep → ℝ
  | [] => 0
  | step :: steps =>
      |kahanAffineCoeffTailProd steps| * |step.correctionSource| +
        kahanAffineCorrectionAbsUnroll steps

/-- Indexed propagated budget for retained-correction source terms.

For a step list `step_0, ..., step_{k-1}`, this charges the `j`th correction
source by `R * E j` and the product bound `rho^(k-1-j)` for all later
old-total coefficients. -/
def kahanAffineCorrectionIndexedBudget
    (rho R : ℝ) (E : ℕ → ℝ) :
    List KahanAffineCoeffStep → ℝ
  | [] => 0
  | _step :: steps =>
      rho ^ steps.length * R * E 0 +
        kahanAffineCorrectionIndexedBudget rho R (fun j => E (j + 1)) steps

/-- Per-input coefficient induced by the current-input part of a residual-aware
affine Kahan coefficient unroll.

For the step at list index `i`, the coefficient is the current-input
coefficient `B_i` multiplied by all later old-total coefficients, minus `1`.
The propagated retained-correction contribution is kept separate and bounded
by `kahanAffineCorrectionIndexedBudget`. -/
noncomputable def kahanAffineInputCoeff
    (steps : List KahanAffineCoeffStep) (i : Fin steps.length) : ℝ :=
  kahanAffineCoeffTailProd (steps.drop (i.val + 1)) *
      (steps.get i).B - 1

/-- Folded residual-aware affine recurrence with an arbitrary initial total. -/
def kahanAffineResidualFold
    (steps : List KahanAffineCoeffStep) (init : ℝ) : ℝ :=
  steps.foldl
    (fun total step => step.A * total + step.source)
    init

/-- Product-form unrolling for the residual-aware affine recurrence.

This is a generic algebraic dependency for C4.5: once the Kahan prefix trace is
instantiated as a list of coefficient steps, the final compensated total splits
into the initial total multiplied by all old-total coefficients plus the sum of
all input and retained-correction source contributions propagated by later
coefficients. -/
theorem kahanAffineResidualFold_eq_tailProd_mul_init_add_unroll
    (steps : List KahanAffineCoeffStep) (init : ℝ) :
    kahanAffineResidualFold steps init =
      kahanAffineCoeffTailProd steps * init +
        kahanAffineResidualUnroll steps := by
  induction steps generalizing init with
  | nil =>
      simp [kahanAffineResidualFold, kahanAffineCoeffTailProd,
        kahanAffineResidualUnroll]
  | cons step steps ih =>
      dsimp [kahanAffineResidualFold]
      change kahanAffineResidualFold steps (step.A * init + step.source) =
        kahanAffineCoeffTailProd (step :: steps) * init +
          kahanAffineResidualUnroll (step :: steps)
      rw [ih (step.A * init + step.source)]
      dsimp [kahanAffineCoeffTailProd, kahanAffineResidualUnroll,
        KahanAffineCoeffStep.source]
      ring

/-- Product-form unrolling of the residual-aware affine recurrence from the
zero initial total. -/
theorem kahanAffineResidualFold_zero_eq_unroll
    (steps : List KahanAffineCoeffStep) :
    kahanAffineResidualFold steps 0 =
      kahanAffineResidualUnroll steps := by
  simpa using
    kahanAffineResidualFold_eq_tailProd_mul_init_add_unroll steps 0

/-- The residual-aware product-form unroll splits into current-input and
retained-correction propagated contributions. -/
theorem kahanAffineResidualUnroll_eq_input_add_correction
    (steps : List KahanAffineCoeffStep) :
    kahanAffineResidualUnroll steps =
      kahanAffineInputUnroll steps +
        kahanAffineCorrectionUnroll steps := by
  induction steps with
  | nil =>
      simp [kahanAffineResidualUnroll, kahanAffineInputUnroll,
        kahanAffineCorrectionUnroll]
  | cons step steps ih =>
      dsimp [kahanAffineResidualUnroll, kahanAffineInputUnroll,
        kahanAffineCorrectionUnroll, KahanAffineCoeffStep.source,
        KahanAffineCoeffStep.inputSource,
        KahanAffineCoeffStep.correctionSource]
      rw [ih]
      ring

/-- The residual-aware folded recurrence from zero splits into propagated
current-input and retained-correction contributions. -/
theorem kahanAffineResidualFold_zero_eq_input_add_correction
    (steps : List KahanAffineCoeffStep) :
    kahanAffineResidualFold steps 0 =
      kahanAffineInputUnroll steps +
        kahanAffineCorrectionUnroll steps := by
  rw [kahanAffineResidualFold_zero_eq_unroll]
  exact kahanAffineResidualUnroll_eq_input_add_correction steps

/-- Triangle-bound substrate for the propagated retained-correction
contribution. -/
theorem kahanAffineCorrectionUnroll_abs_le
    (steps : List KahanAffineCoeffStep) :
    |kahanAffineCorrectionUnroll steps| ≤
      kahanAffineCorrectionAbsUnroll steps := by
  induction steps with
  | nil =>
      simp [kahanAffineCorrectionUnroll, kahanAffineCorrectionAbsUnroll]
  | cons step steps ih =>
      dsimp [kahanAffineCorrectionUnroll,
        kahanAffineCorrectionAbsUnroll]
      calc
        |kahanAffineCoeffTailProd steps * step.correctionSource +
            kahanAffineCorrectionUnroll steps|
            ≤ |kahanAffineCoeffTailProd steps * step.correctionSource| +
                |kahanAffineCorrectionUnroll steps| := abs_add_le _ _
    _ = |kahanAffineCoeffTailProd steps| * |step.correctionSource| +
                |kahanAffineCorrectionUnroll steps| := by
              rw [abs_mul]
    _ ≤ |kahanAffineCoeffTailProd steps| * |step.correctionSource| +
                kahanAffineCorrectionAbsUnroll steps := by
              exact add_le_add (le_refl _) ih

/-- The propagated current-input part of a residual-aware affine unroll is a
source-term sum with per-input coefficients `kahanAffineInputCoeff`. -/
theorem kahanAffineInputUnroll_eq_sum_inputCoeff
    (steps : List KahanAffineCoeffStep) :
    kahanAffineInputUnroll steps =
      ∑ i : Fin steps.length,
        (steps.get i).x * (1 + kahanAffineInputCoeff steps i) := by
  induction steps with
  | nil =>
      simp [kahanAffineInputUnroll, kahanAffineInputCoeff]
  | cons step steps ih =>
      dsimp [kahanAffineInputUnroll, kahanAffineInputCoeff]
      change kahanAffineCoeffTailProd steps * step.inputSource +
          kahanAffineInputUnroll steps =
        ∑ i : Fin (steps.length + 1),
          ((step :: steps).get i).x *
            (1 + (kahanAffineCoeffTailProd (steps.drop i.val) *
              ((step :: steps).get i).B - 1))
      conv_rhs => rw [Fin.sum_univ_succ]
      rw [ih]
      simp [KahanAffineCoeffStep.inputSource, kahanAffineInputCoeff]
      ring

/-- Exact residual-aware affine fold from zero as a per-input coefficient sum
plus the propagated retained-correction contribution. -/
theorem kahanAffineResidualFold_zero_eq_sum_inputCoeff_add_correction
    (steps : List KahanAffineCoeffStep) :
    kahanAffineResidualFold steps 0 =
      (∑ i : Fin steps.length,
        (steps.get i).x * (1 + kahanAffineInputCoeff steps i)) +
        kahanAffineCorrectionUnroll steps := by
  rw [kahanAffineResidualFold_zero_eq_input_add_correction]
  rw [kahanAffineInputUnroll_eq_sum_inputCoeff]

/-- The additive residual left after replacing the current-input part by its
per-input coefficients is bounded by the retained-correction absolute unroll. -/
theorem kahanAffineResidualFold_zero_sub_sum_inputCoeff_abs_le
    (steps : List KahanAffineCoeffStep) :
    |kahanAffineResidualFold steps 0 -
      (∑ i : Fin steps.length,
        (steps.get i).x * (1 + kahanAffineInputCoeff steps i))| ≤
      kahanAffineCorrectionAbsUnroll steps := by
  have h :=
    kahanAffineResidualFold_zero_eq_sum_inputCoeff_add_correction steps
  rw [h]
  ring_nf
  exact kahanAffineCorrectionUnroll_abs_le steps

/-- If every old-total coefficient in a residual-aware affine step list has
absolute value at most `rho`, then the tail product is bounded by
`rho ^ steps.length`. -/
theorem kahanAffineCoeffTailProd_abs_le_pow
    {rho : ℝ} (hrho : 0 ≤ rho)
    (steps : List KahanAffineCoeffStep)
    (hA : ∀ step ∈ steps, |step.A| ≤ rho) :
    |kahanAffineCoeffTailProd steps| ≤ rho ^ steps.length := by
  induction steps with
  | nil =>
      simp [kahanAffineCoeffTailProd]
  | cons step steps ih =>
      dsimp [kahanAffineCoeffTailProd]
      rw [abs_mul]
      have hstep : |step.A| ≤ rho := hA step (by simp)
      have htail :
          |kahanAffineCoeffTailProd steps| ≤ rho ^ steps.length := by
        exact ih (fun step' hmem => hA step' (by simp [hmem]))
      have hmul :
          |step.A| * |kahanAffineCoeffTailProd steps| ≤
            rho * rho ^ steps.length := by
        exact mul_le_mul hstep htail (abs_nonneg _) hrho
      simpa [pow_succ, Nat.succ_eq_add_one, mul_comm, mul_left_comm,
        mul_assoc] using hmul

/-- If every old-total coefficient in a residual-aware affine step list is
within `eta` of one, then the full tail product is within
`(1 + eta)^m - 1` of one.

This is the product-collapse algebra needed to bound the product-form
`kahanAffineInputCoeff` coefficients. -/
theorem kahanAffineCoeffTailProd_abs_sub_one_le_pow_sub_one
    {eta : ℝ} (heta : 0 ≤ eta)
    (steps : List KahanAffineCoeffStep)
    (hA : ∀ step ∈ steps, |step.A - 1| ≤ eta) :
    |kahanAffineCoeffTailProd steps - 1| ≤
      (1 + eta) ^ steps.length - 1 := by
  induction steps with
  | nil =>
      simp [kahanAffineCoeffTailProd]
  | cons step steps ih =>
      dsimp [kahanAffineCoeffTailProd]
      have hstep : |step.A - 1| ≤ eta := hA step (by simp)
      have htail_close :
          |kahanAffineCoeffTailProd steps - 1| ≤
            (1 + eta) ^ steps.length - 1 := by
        exact ih (fun step' hmem => hA step' (by simp [hmem]))
      have hA_abs_all :
          ∀ step' ∈ steps, |step'.A| ≤ 1 + eta := by
        intro step' hmem
        have hclose := hA step' (by simp [hmem])
        calc
          |step'.A| = |(step'.A - 1) + 1| := by ring_nf
          _ ≤ |step'.A - 1| + |(1 : ℝ)| := abs_add_le _ _
          _ = |step'.A - 1| + 1 := by norm_num
          _ ≤ eta + 1 := by nlinarith [hclose]
          _ = 1 + eta := by ring
      have htail_abs :
          |kahanAffineCoeffTailProd steps| ≤
            (1 + eta) ^ steps.length := by
        exact kahanAffineCoeffTailProd_abs_le_pow
          (rho := 1 + eta) (by nlinarith) steps hA_abs_all
      have hprod :
          |(step.A - 1) * kahanAffineCoeffTailProd steps| ≤
            eta * (1 + eta) ^ steps.length := by
        rw [abs_mul]
        exact mul_le_mul hstep htail_abs (abs_nonneg _) heta
      calc
        |step.A * kahanAffineCoeffTailProd steps - 1|
            = |(step.A - 1) * kahanAffineCoeffTailProd steps +
                (kahanAffineCoeffTailProd steps - 1)| := by
              ring_nf
        _ ≤ |(step.A - 1) * kahanAffineCoeffTailProd steps| +
              |kahanAffineCoeffTailProd steps - 1| := abs_add_le _ _
        _ ≤ eta * (1 + eta) ^ steps.length +
              ((1 + eta) ^ steps.length - 1) := by
            nlinarith
        _ = (1 + eta) ^ (step :: steps).length - 1 := by
            simp [pow_succ]
            ring

/-- Generic product-radius bound for the product-form current-input coefficient.

If all later old-total coefficients are within `eta` of one and every current
input coefficient is within `beta` of one, then the per-input coefficient
`tailProd * B_i - 1` is bounded by the displayed product radius. -/
theorem kahanAffineInputCoeff_abs_le_productRadius
    {eta beta : ℝ} (heta : 0 ≤ eta)
    (steps : List KahanAffineCoeffStep)
    (hA : ∀ step ∈ steps, |step.A - 1| ≤ eta)
    (hB : ∀ step ∈ steps, |step.B - 1| ≤ beta)
    (i : Fin steps.length) :
    |kahanAffineInputCoeff steps i| ≤
      (1 + eta) ^ (steps.drop (i.val + 1)).length * beta +
        ((1 + eta) ^ (steps.drop (i.val + 1)).length - 1) := by
  let tailSteps := steps.drop (i.val + 1)
  let T := kahanAffineCoeffTailProd tailSteps
  let B := (steps.get i).B
  have htailA : ∀ step ∈ tailSteps, |step.A - 1| ≤ eta := by
    intro step hmem
    exact hA step (List.mem_of_mem_drop hmem)
  have htailAbs :
      |T| ≤ (1 + eta) ^ tailSteps.length := by
    have hA_abs : ∀ step ∈ tailSteps, |step.A| ≤ 1 + eta := by
      intro step hmem
      have hclose := htailA step hmem
      calc
        |step.A| = |(step.A - 1) + 1| := by ring_nf
        _ ≤ |step.A - 1| + |(1 : ℝ)| := abs_add_le _ _
        _ = |step.A - 1| + 1 := by norm_num
        _ ≤ eta + 1 := by nlinarith [hclose]
        _ = 1 + eta := by ring
    exact kahanAffineCoeffTailProd_abs_le_pow
      (rho := 1 + eta) (by nlinarith) tailSteps hA_abs
  have htailClose :
      |T - 1| ≤ (1 + eta) ^ tailSteps.length - 1 := by
    simpa [T] using
      kahanAffineCoeffTailProd_abs_sub_one_le_pow_sub_one
        heta tailSteps htailA
  have hBclose : |B - 1| ≤ beta := by
    exact hB (steps.get i) (List.get_mem steps i)
  have hprod :
      |T * (B - 1)| ≤
        (1 + eta) ^ tailSteps.length * beta := by
    rw [abs_mul]
    exact mul_le_mul htailAbs hBclose (abs_nonneg _)
      (pow_nonneg (by nlinarith : 0 ≤ 1 + eta) tailSteps.length)
  calc
    |kahanAffineInputCoeff steps i|
        = |T * B - 1| := by
            simp [kahanAffineInputCoeff, T, B, tailSteps]
    _ = |T * (B - 1) + (T - 1)| := by
            ring_nf
    _ ≤ |T * (B - 1)| + |T - 1| := abs_add_le _ _
    _ ≤ (1 + eta) ^ tailSteps.length * beta +
          ((1 + eta) ^ tailSteps.length - 1) := by
        nlinarith

/-- Generic indexed bound for the propagated retained-correction source
majorant.

This is the list-level algebra used by the ordinary Kahan coefficient route:
if later old-total products are bounded by `rho` per step and the `j`th
correction source is bounded by `R * E j`, then the absolute correction unroll
is bounded by the corresponding indexed propagated budget. -/
theorem kahanAffineCorrectionAbsUnroll_le_indexedBudget
    {rho R : ℝ} (hrho : 0 ≤ rho)
    (E : ℕ → ℝ) (hE : ∀ j, 0 ≤ E j)
    (steps : List KahanAffineCoeffStep)
    (hA : ∀ step ∈ steps, |step.A| ≤ rho)
    (hC :
      ∀ j (hj : j < steps.length),
        |(steps.get ⟨j, hj⟩).correctionSource| ≤ R * E j) :
    kahanAffineCorrectionAbsUnroll steps ≤
      kahanAffineCorrectionIndexedBudget rho R E steps := by
  induction steps generalizing E with
  | nil =>
      simp [kahanAffineCorrectionAbsUnroll,
        kahanAffineCorrectionIndexedBudget]
  | cons step steps ih =>
      dsimp [kahanAffineCorrectionAbsUnroll,
        kahanAffineCorrectionIndexedBudget]
      have htailA : ∀ step' ∈ steps, |step'.A| ≤ rho := by
        intro step' hmem
        exact hA step' (by simp [hmem])
      have htailC :
          ∀ j (hj : j < steps.length),
            |(steps.get ⟨j, hj⟩).correctionSource| ≤
              R * E (j + 1) := by
        intro j hj
        have hmain := hC (j + 1) (Nat.succ_lt_succ hj)
        simpa [List.get_cons_succ] using hmain
      have htail :=
        ih (fun j => E (j + 1)) (fun j => hE (j + 1))
          htailA htailC
      have htailProd :
          |kahanAffineCoeffTailProd steps| ≤ rho ^ steps.length :=
        kahanAffineCoeffTailProd_abs_le_pow hrho steps htailA
      have hheadC :
          |step.correctionSource| ≤ R * E 0 := by
        have hmain := hC 0 (Nat.succ_pos steps.length)
        simpa [List.get_cons_zero] using hmain
      have hhead :
          |kahanAffineCoeffTailProd steps| * |step.correctionSource| ≤
            rho ^ steps.length * (R * E 0) := by
        exact mul_le_mul htailProd hheadC (abs_nonneg _) (pow_nonneg hrho _)
      calc
        |kahanAffineCoeffTailProd steps| * |step.correctionSource| +
              kahanAffineCorrectionAbsUnroll steps
            ≤ rho ^ steps.length * (R * E 0) +
                kahanAffineCorrectionIndexedBudget rho R
                  (fun j => E (j + 1)) steps := by
              exact add_le_add hhead htail
        _ = rho ^ steps.length * R * E 0 +
              kahanAffineCorrectionIndexedBudget rho R
                (fun j => E (j + 1)) steps := by
              ring

/-- The residual-aware affine coefficient step induced by one indexed Kahan
prefix-trace step. -/
noncomputable def kahanAffineCoeffStepOfIndex
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    KahanAffineCoeffStep :=
  let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
  let w := kahanTrace_deltaWitness fp v i
  { A := kahanTotalStateCoeff w.deltaS w.deltaSub w.deltaE
    B := kahanTotalInputCoeff w.deltaY w.deltaS w.deltaSub w.deltaE
    R := kahanTotalResidualCoeff w.deltaY w.deltaS w.deltaSub w.deltaE
    x := v i
    e := state.e }

/-- One indexed Kahan prefix-trace step satisfies the residual-aware affine
coefficient recurrence. -/
theorem kahanTrace_total_eq_affineCoeffStep
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
    let step := kahanAffineCoeffStepOfIndex fp v i
    (kahanTrace fp v i).s + (kahanTrace fp v i).e =
      step.A * (state.s + state.e) + step.source := by
  dsimp
  have h := kahanTrace_deltaWitness_total_compensated_total_coefficients fp v i
  dsimp at h
  rw [h]
  dsimp [kahanAffineCoeffStepOfIndex, KahanAffineCoeffStep.source]
  ring

/-- The old-total coefficient of the actual indexed Kahan affine step is
bounded by `1 + 3*u^2` under the local small-`u` hypothesis. -/
theorem kahanAffineCoeffStepOfIndex_A_abs_le_one_plus_three_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1) :
    |(kahanAffineCoeffStepOfIndex fp v i).A| ≤
      1 + 3 * fp.u ^ 2 := by
  let A := (kahanAffineCoeffStepOfIndex fp v i).A
  have hA1 : |A - 1| ≤ 3 * fp.u ^ 2 := by
    simpa [A, kahanAffineCoeffStepOfIndex] using
      kahanTotalStateCoeff_abs_sub_one_le_three_u_sq
        (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
        (deltaSub := (kahanTrace_deltaWitness fp v i).deltaSub)
        (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
        (u := fp.u) fp.u_nonneg hu1
        (kahanTrace_deltaWitness fp v i).h_deltaS
        (kahanTrace_deltaWitness fp v i).h_deltaSub
        (kahanTrace_deltaWitness fp v i).h_deltaE
  have hrewrite : A = (A - 1) + 1 := by ring
  calc
    |A| = |(A - 1) + 1| := congrArg abs hrewrite
    _ ≤ |A - 1| + |(1 : ℝ)| := abs_add_le (A - 1) 1
    _ ≤ 3 * fp.u ^ 2 + 1 := by
          exact add_le_add hA1 (by norm_num)
    _ = 1 + 3 * fp.u ^ 2 := by ring

/-- The old-total coefficient of the actual indexed Kahan affine step differs
from one by at most `3*u^2`. -/
theorem kahanAffineCoeffStepOfIndex_A_abs_sub_one_le_three_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1) :
    |(kahanAffineCoeffStepOfIndex fp v i).A - 1| ≤
      3 * fp.u ^ 2 := by
  simpa [kahanAffineCoeffStepOfIndex] using
    kahanTotalStateCoeff_abs_sub_one_le_three_u_sq
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaSub := (kahanTrace_deltaWitness fp v i).deltaSub)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg hu1
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaSub
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- The current-input coefficient of the actual indexed Kahan affine step
differs from one by at most `2*u + 9*u^2`. -/
theorem kahanAffineCoeffStepOfIndex_B_abs_sub_one_le_two_u_plus_nine_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1) :
    |(kahanAffineCoeffStepOfIndex fp v i).B - 1| ≤
      2 * fp.u + 9 * fp.u ^ 2 := by
  simpa [kahanAffineCoeffStepOfIndex] using
    kahanTotalInputCoeff_abs_sub_one_le_two_u_plus_nine_u_sq
      (deltaY := (kahanTrace_deltaWitness fp v i).deltaY)
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaSub := (kahanTrace_deltaWitness fp v i).deltaSub)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg hu1
      (kahanTrace_deltaWitness fp v i).h_deltaY
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaSub
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- The retained-correction coefficient of the actual indexed Kahan affine
step satisfies the local small-`u` residual-coefficient bound. -/
theorem kahanAffineCoeffStepOfIndex_R_abs_le_two_u_plus_twelve_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1) :
    |(kahanAffineCoeffStepOfIndex fp v i).R| ≤
      2 * fp.u + 12 * fp.u ^ 2 := by
  simpa [kahanAffineCoeffStepOfIndex] using
    kahanTotalResidualCoeff_abs_le_two_u_plus_twelve_u_sq
      (deltaY := (kahanTrace_deltaWitness fp v i).deltaY)
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaSub := (kahanTrace_deltaWitness fp v i).deltaSub)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg hu1
      (kahanTrace_deltaWitness fp v i).h_deltaY
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaSub
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- The retained-correction source contribution of the actual indexed Kahan
affine step is controlled by the local residual-coefficient radius times the
retained correction. -/
theorem kahanAffineCoeffStepOfIndex_correctionSource_abs_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1) :
    let step := kahanAffineCoeffStepOfIndex fp v i
    |step.correctionSource| ≤
      (2 * fp.u + 12 * fp.u ^ 2) * |step.e| := by
  dsimp
  have hR :=
    kahanAffineCoeffStepOfIndex_R_abs_le_two_u_plus_twelve_u_sq
      fp v i hu1
  calc
    |(kahanAffineCoeffStepOfIndex fp v i).correctionSource|
        = |(kahanAffineCoeffStepOfIndex fp v i).R| *
            |(kahanAffineCoeffStepOfIndex fp v i).e| := by
          rw [KahanAffineCoeffStep.correctionSource, abs_mul]
    _ ≤ (2 * fp.u + 12 * fp.u ^ 2) *
          |(kahanAffineCoeffStepOfIndex fp v i).e| := by
        exact mul_le_mul_of_nonneg_right hR (abs_nonneg _)

/-- The retained-correction source contribution of the actual indexed Kahan
affine step is controlled by the input-only retained-correction majorant for
that prefix.

This is the local handoff from the concrete residual coefficient bound to the
stored-sum-free majorants used by the remaining Goldberg/Knuth coefficient
recursion. -/
theorem kahanAffineCoeffStepOfIndex_correctionSource_abs_le_inputMajorant
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1) :
    let step := kahanAffineCoeffStepOfIndex fp v i
    |step.correctionSource| ≤
      (2 * fp.u + 12 * fp.u ^ 2) *
        (kahanInputAbsMajorant fp v i.val (Nat.le_of_lt i.isLt)).e := by
  dsimp
  have hsource :=
    kahanAffineCoeffStepOfIndex_correctionSource_abs_le fp v i hu1
  have he :=
    kahanPrefixState_e_abs_le_inputMajorant
      fp v i.val (Nat.le_of_lt i.isLt)
  have hcoef : 0 ≤ 2 * fp.u + 12 * fp.u ^ 2 := by
    nlinarith [fp.u_nonneg, sq_nonneg fp.u]
  calc
    |(kahanAffineCoeffStepOfIndex fp v i).correctionSource|
        ≤ (2 * fp.u + 12 * fp.u ^ 2) *
            |(kahanAffineCoeffStepOfIndex fp v i).e| := by
          simpa [kahanAffineCoeffStepOfIndex] using hsource
    _ ≤ (2 * fp.u + 12 * fp.u ^ 2) *
            (kahanInputAbsMajorant fp v i.val (Nat.le_of_lt i.isLt)).e := by
          exact mul_le_mul_of_nonneg_left he hcoef

/-- The first `k` indexed Kahan prefix-trace steps as residual-aware affine
coefficient steps. -/
noncomputable def kahanAffineCoeffSteps
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    List KahanAffineCoeffStep :=
  List.ofFn (fun i : Fin k =>
    kahanAffineCoeffStepOfIndex fp v
      ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩)

/-- Every concrete affine coefficient step in the first `k` Kahan prefix steps
has old-total coefficient bounded by `1 + 3*u^2`. -/
theorem kahanAffineCoeffSteps_A_abs_le_one_plus_three_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1) :
    ∀ step ∈ kahanAffineCoeffSteps fp v k hk,
      |step.A| ≤ 1 + 3 * fp.u ^ 2 := by
  intro step hmem
  rw [kahanAffineCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanAffineCoeffStepOfIndex_A_abs_le_one_plus_three_u_sq
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ hu1

/-- Every concrete affine coefficient step in the first `k` Kahan prefix steps
has old-total coefficient within `3*u^2` of one. -/
theorem kahanAffineCoeffSteps_A_abs_sub_one_le_three_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1) :
    ∀ step ∈ kahanAffineCoeffSteps fp v k hk,
      |step.A - 1| ≤ 3 * fp.u ^ 2 := by
  intro step hmem
  rw [kahanAffineCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanAffineCoeffStepOfIndex_A_abs_sub_one_le_three_u_sq
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ hu1

/-- Every concrete affine coefficient step in the first `k` Kahan prefix steps
has current-input coefficient within `2*u + 9*u^2` of one. -/
theorem kahanAffineCoeffSteps_B_abs_sub_one_le_two_u_plus_nine_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1) :
    ∀ step ∈ kahanAffineCoeffSteps fp v k hk,
      |step.B - 1| ≤ 2 * fp.u + 9 * fp.u ^ 2 := by
  intro step hmem
  rw [kahanAffineCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanAffineCoeffStepOfIndex_B_abs_sub_one_le_two_u_plus_nine_u_sq
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ hu1

/-- The old-total coefficient product for the first `k` concrete Kahan prefix
steps is bounded by `(1 + 3*u^2)^k`. -/
theorem kahanAffineCoeffSteps_tailProd_abs_le_one_plus_three_u_sq_pow
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1) :
    |kahanAffineCoeffTailProd (kahanAffineCoeffSteps fp v k hk)| ≤
      (1 + 3 * fp.u ^ 2) ^ k := by
  have hrho : 0 ≤ 1 + 3 * fp.u ^ 2 := by
    nlinarith [sq_nonneg fp.u]
  have hbound :=
    kahanAffineCoeffTailProd_abs_le_pow
      (rho := 1 + 3 * fp.u ^ 2) hrho
      (kahanAffineCoeffSteps fp v k hk)
      (kahanAffineCoeffSteps_A_abs_le_one_plus_three_u_sq
        fp v k hk hu1)
  simpa [kahanAffineCoeffSteps] using hbound

/-- Product-form radius for the current-input coefficient induced by a Kahan
affine coefficient unroll.

For input index `i`, the exponent is the number of later prefix steps whose
old-total coefficients multiply the local current-input coefficient. -/
def kahanAffineInputCoeffProductRadius
    (fp : FPModel) (steps : List KahanAffineCoeffStep)
    (i : Fin steps.length) : ℝ :=
  (1 + 3 * fp.u ^ 2) ^ (steps.drop (i.val + 1)).length *
      (2 * fp.u + 9 * fp.u ^ 2) +
    ((1 + 3 * fp.u ^ 2) ^ (steps.drop (i.val + 1)).length - 1)

/-- The product-form input coefficient in the first `k` concrete Kahan prefix
steps is bounded by the explicit product radius. -/
theorem kahanAffineCoeffSteps_inputCoeff_abs_le_productRadius
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (hu1 : fp.u ≤ 1)
    (i : Fin (kahanAffineCoeffSteps fp v k hk).length) :
    let steps := kahanAffineCoeffSteps fp v k hk
    |kahanAffineInputCoeff steps i| ≤
      kahanAffineInputCoeffProductRadius fp steps i := by
  dsimp
  let steps := kahanAffineCoeffSteps fp v k hk
  have hA : ∀ step ∈ steps, |step.A - 1| ≤ 3 * fp.u ^ 2 := by
    simpa [steps] using
      kahanAffineCoeffSteps_A_abs_sub_one_le_three_u_sq
        fp v k hk hu1
  have hB :
      ∀ step ∈ steps, |step.B - 1| ≤
        2 * fp.u + 9 * fp.u ^ 2 := by
    simpa [steps] using
      kahanAffineCoeffSteps_B_abs_sub_one_le_two_u_plus_nine_u_sq
        fp v k hk hu1
  simpa [steps, kahanAffineInputCoeffProductRadius] using
    kahanAffineInputCoeff_abs_le_productRadius
      (eta := 3 * fp.u ^ 2)
      (beta := 2 * fp.u + 9 * fp.u ^ 2)
      (by nlinarith [sq_nonneg fp.u]) steps hA hB i

/-- Concrete source-shaped collapse of the Kahan product-form input radius.

For `m` later affine steps, if the second-order product budget
`m * (3*u^2)` is at most `1/2`, then the product-form radius is bounded by
`2*u + (9 + 72*m)*u^2`.  This closes the product-radius half of the final
C4.5 `2*u + C*n*u^2` collapse. -/
theorem kahanAffineInputCoeffProductRadius_le_two_u_plus
    (fp : FPModel) (steps : List KahanAffineCoeffStep)
    (i : Fin steps.length) (hu1 : fp.u ≤ 1)
    (hsmall :
      ((steps.drop (i.val + 1)).length : ℝ) * (3 * fp.u ^ 2) ≤ 1 / 2) :
    kahanAffineInputCoeffProductRadius fp steps i ≤
      2 * fp.u +
        (9 + 72 * ((steps.drop (i.val + 1)).length : ℝ)) * fp.u ^ 2 := by
  let m : ℕ := (steps.drop (i.val + 1)).length
  let u : ℝ := fp.u
  let c : ℝ := 3 * u ^ 2
  let b : ℝ := 2 * u + 9 * u ^ 2
  have hu0 : 0 ≤ u := by
    simpa [u] using fp.u_nonneg
  have hc0 : 0 ≤ c := by
    dsimp [c]
    nlinarith [sq_nonneg u]
  have hgeom :
      (1 + c) ^ m - 1 ≤ 2 * ((m : ℝ) * c) := by
    exact one_add_pow_sub_one_le_two_mul_nat_mul_of_nat_mul_le_half
      m hc0 (by simpa [m, c, u] using hsmall)
  have hgeom' :
      (1 + c) ^ m - 1 ≤ 6 * (m : ℝ) * u ^ 2 := by
    calc
      (1 + c) ^ m - 1 ≤ 2 * ((m : ℝ) * c) := hgeom
      _ = 6 * (m : ℝ) * u ^ 2 := by
          simp [c]
          ring
  have hb1_nonneg : 0 ≤ b + 1 := by
    dsimp [b]
    nlinarith [hu0, sq_nonneg u]
  have hu_sq_le_one : u ^ 2 ≤ 1 := by
    have hmul :=
      mul_le_mul hu1 hu1 hu0 (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have hb1_le : b + 1 ≤ 12 := by
    dsimp [b]
    nlinarith [hu0, hu1, hu_sq_le_one]
  have hD_nonneg : 0 ≤ 6 * (m : ℝ) * u ^ 2 := by
    have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
    nlinarith [hm0, sq_nonneg u]
  have hscaled :
      ((1 + c) ^ m - 1) * (b + 1) ≤
        (6 * (m : ℝ) * u ^ 2) * (b + 1) := by
    exact mul_le_mul_of_nonneg_right hgeom' hb1_nonneg
  have hscaled' :
      (6 * (m : ℝ) * u ^ 2) * (b + 1) ≤
        72 * (m : ℝ) * u ^ 2 := by
    calc
      (6 * (m : ℝ) * u ^ 2) * (b + 1)
          ≤ (6 * (m : ℝ) * u ^ 2) * 12 := by
              exact mul_le_mul_of_nonneg_left hb1_le hD_nonneg
      _ = 72 * (m : ℝ) * u ^ 2 := by ring
  calc
    kahanAffineInputCoeffProductRadius fp steps i =
        b + (((1 + c) ^ m - 1) * (b + 1)) := by
          simp [kahanAffineInputCoeffProductRadius, m, c, b, u]
          ring
    _ ≤ b + 72 * (m : ℝ) * u ^ 2 := by
        nlinarith [hscaled, hscaled']
    _ = 2 * fp.u +
        (9 + 72 * ((steps.drop (i.val + 1)).length : ℝ)) * fp.u ^ 2 := by
        simp [b, m, u]
        ring

/-- Propagated retained-correction source contribution for the first `k`
Kahan steps, bounded only by input magnitudes through the coupled prefix
majorants.

The right-hand side charges prefix `j` by the input-only correction majorant
after `j` earlier steps, the residual coefficient radius `2*u + 12*u^2`, and
the product radius `(1 + 3*u^2)` for each later old-total coefficient. -/
theorem kahanAffineCoeffSteps_correctionAbsUnroll_le_inputMajorantBudget
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (hu1 : fp.u ≤ 1) :
    kahanAffineCorrectionAbsUnroll (kahanAffineCoeffSteps fp v k hk) ≤
      kahanAffineCorrectionIndexedBudget
        (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
        (fun j =>
          if hj : j < k then
            (kahanInputAbsMajorant fp v j
              (Nat.le_trans (Nat.le_of_lt hj) hk)).e
          else 0)
        (kahanAffineCoeffSteps fp v k hk) := by
  let rho : ℝ := 1 + 3 * fp.u ^ 2
  let R : ℝ := 2 * fp.u + 12 * fp.u ^ 2
  let E : ℕ → ℝ := fun j =>
    if hj : j < k then
      (kahanInputAbsMajorant fp v j
        (Nat.le_trans (Nat.le_of_lt hj) hk)).e
    else 0
  have hrho : 0 ≤ rho := by
    dsimp [rho]
    nlinarith [sq_nonneg fp.u]
  have hE : ∀ j, 0 ≤ E j := by
    intro j
    dsimp [E]
    by_cases hj : j < k
    · simp [hj, (kahanInputAbsMajorant_nonneg fp v j
        (Nat.le_trans (Nat.le_of_lt hj) hk)).2]
    · simp [hj]
  have hA : ∀ step ∈ kahanAffineCoeffSteps fp v k hk, |step.A| ≤ rho := by
    intro step hmem
    dsimp [rho]
    exact kahanAffineCoeffSteps_A_abs_le_one_plus_three_u_sq
      fp v k hk hu1 step hmem
  have hC :
      ∀ j (hj : j < (kahanAffineCoeffSteps fp v k hk).length),
        |((kahanAffineCoeffSteps fp v k hk).get ⟨j, hj⟩).correctionSource| ≤
          R * E j := by
    intro j hj
    have hjk : j < k := by
      simpa [kahanAffineCoeffSteps] using hj
    let idx : Fin n := ⟨j, Nat.lt_of_lt_of_le hjk hk⟩
    have hget :
        (kahanAffineCoeffSteps fp v k hk).get ⟨j, hj⟩ =
          kahanAffineCoeffStepOfIndex fp v idx := by
      simp [kahanAffineCoeffSteps, idx]
    have hbound :=
      kahanAffineCoeffStepOfIndex_correctionSource_abs_le_inputMajorant
        fp v idx hu1
    dsimp [R, E]
    change
      |((kahanAffineCoeffSteps fp v k hk).get ⟨j, hj⟩).correctionSource| ≤
        (2 * fp.u + 12 * fp.u ^ 2) *
          (if hj : j < k then
            (kahanInputAbsMajorant fp v j
              (Nat.le_trans (Nat.le_of_lt hj) hk)).e
          else 0)
    rw [hget]
    simpa [idx, hjk] using hbound
  simpa [rho, R, E] using
    kahanAffineCorrectionAbsUnroll_le_indexedBudget
      (rho := rho) (R := R) hrho E hE
      (kahanAffineCoeffSteps fp v k hk) hA hC

/-- The list fold over indexed Kahan affine coefficient steps is the matching
`Fin.foldl` prefix recurrence. -/
theorem kahanAffineCoeffSteps_fold_eq_finFold
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) (init : ℝ) :
    kahanAffineResidualFold (kahanAffineCoeffSteps fp v k hk) init =
      Fin.foldl k
        (fun total i =>
          let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
          let step := kahanAffineCoeffStepOfIndex fp v idx
          step.A * total + step.source)
        init := by
  dsimp [kahanAffineResidualFold, kahanAffineCoeffSteps]
  rw [Compensated.Kahan.Internal.listFoldlOfFn_eq_finFoldl]

/-- The residual-aware affine coefficient recurrence over the first `k`
actual Kahan prefix-trace steps produces the compensated prefix total. -/
theorem kahanAffineCoeffSteps_finFold_eq_prefix_total
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n),
      Fin.foldl k
        (fun total i =>
          let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
          let step := kahanAffineCoeffStepOfIndex fp v idx
          step.A * total + step.source)
        0 =
      (kahanPrefixState fp v k hk).s +
        (kahanPrefixState fp v k hk).e
  | 0, _hk => by
      simp [kahanPrefixState, KahanState.zero]
  | k + 1, hk => by
      have hprev_le : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      let idx : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let prev := kahanPrefixState fp v k hprev_le
      let step := kahanAffineCoeffStepOfIndex fp v idx
      have hih :=
        kahanAffineCoeffSteps_finFold_eq_prefix_total fp v k hprev_le
      have hih' :
          Fin.foldl k
            (fun total i =>
              let idx : Fin n := ⟨(i.castSucc).val,
                Nat.lt_of_lt_of_le (i.castSucc).isLt hk⟩
              let step := kahanAffineCoeffStepOfIndex fp v idx
              step.A * total + step.source)
            0 = prev.s + prev.e := by
        simpa [prev] using hih
      have hfoldPrefix :
          kahanPrefixState fp v (k + 1) hk =
            kahanStep fp (v idx) prev := by
        unfold kahanPrefixState
        rw [Fin.foldl_succ_last]
        rfl
      have hstep :
          (kahanStep fp (v idx) prev).s +
              (kahanStep fp (v idx) prev).e =
            step.A * (prev.s + prev.e) + step.source := by
        have htrace := kahanTrace_total_eq_affineCoeffStep fp v idx
        dsimp at htrace
        simpa [idx, prev, step, kahanTrace, kahanStep,
          KahanStepTrace.nextState] using htrace
      rw [Fin.foldl_succ_last]
      rw [hih']
      rw [hfoldPrefix, hstep]
      simp [step]
      ring

/-- The list of residual-aware affine coefficient steps for the first `k`
actual Kahan steps folds from zero to the compensated prefix total. -/
theorem kahanAffineCoeffSteps_fold_zero_eq_prefix_total
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    kahanAffineResidualFold (kahanAffineCoeffSteps fp v k hk) 0 =
      (kahanPrefixState fp v k hk).s +
        (kahanPrefixState fp v k hk).e := by
  rw [kahanAffineCoeffSteps_fold_eq_finFold]
  exact kahanAffineCoeffSteps_finFold_eq_prefix_total fp v k hk

/-- Concrete Kahan prefix version of the per-input coefficient residual bound.

For the first `k` Algorithm 4.2 steps, the compensated prefix total `s_k+e_k`
differs from the sum of source inputs multiplied by the product-form input
coefficients only by the propagated retained-correction contribution.  That
contribution is bounded by the input-only correction budget closed in the
previous dependency. -/
theorem kahanAffineCoeffSteps_prefixTotal_sub_sum_inputCoeff_abs_le_inputMajorantBudget
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (hu1 : fp.u ≤ 1) :
    let steps := kahanAffineCoeffSteps fp v k hk
    |((kahanPrefixState fp v k hk).s +
        (kahanPrefixState fp v k hk).e) -
      (∑ i : Fin steps.length,
        (steps.get i).x * (1 + kahanAffineInputCoeff steps i))| ≤
      kahanAffineCorrectionIndexedBudget
        (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
        (fun j =>
          if hj : j < k then
            (kahanInputAbsMajorant fp v j
              (Nat.le_trans (Nat.le_of_lt hj) hk)).e
          else 0)
        steps := by
  dsimp
  let steps := kahanAffineCoeffSteps fp v k hk
  have hfold :
      kahanAffineResidualFold steps 0 =
        (kahanPrefixState fp v k hk).s +
          (kahanPrefixState fp v k hk).e := by
    simpa [steps] using
      kahanAffineCoeffSteps_fold_zero_eq_prefix_total fp v k hk
  have hgeneric :=
    kahanAffineResidualFold_zero_sub_sum_inputCoeff_abs_le steps
  have hbudget :
      kahanAffineCorrectionAbsUnroll steps ≤
        kahanAffineCorrectionIndexedBudget
          (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
          (fun j =>
            if hj : j < k then
              (kahanInputAbsMajorant fp v j
                (Nat.le_trans (Nat.le_of_lt hj) hk)).e
            else 0)
          steps := by
    simpa [steps] using
      kahanAffineCoeffSteps_correctionAbsUnroll_le_inputMajorantBudget
        fp v k hk hu1
  calc
    |((kahanPrefixState fp v k hk).s +
        (kahanPrefixState fp v k hk).e) -
      (∑ i : Fin steps.length,
        (steps.get i).x * (1 + kahanAffineInputCoeff steps i))|
        = |kahanAffineResidualFold steps 0 -
            (∑ i : Fin steps.length,
              (steps.get i).x * (1 + kahanAffineInputCoeff steps i))| := by
            rw [hfold]
    _ ≤ kahanAffineCorrectionAbsUnroll steps := hgeneric
    _ ≤ kahanAffineCorrectionIndexedBudget
          (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
          (fun j =>
            if hj : j < k then
              (kahanInputAbsMajorant fp v j
                (Nat.le_trans (Nat.le_of_lt hj) hk)).e
            else 0)
          steps := hbudget

/-- Returned-prefix-sum version of the input-coefficient residual bound.

The source equation (4.8) is stated for the computed sum `s`, not merely for
the compensated total `s+e`.  This theorem charges the final retained
correction by the input-only correction majorant and therefore turns the
`s+e` residual bridge into an additive residual bound for the actual stored
prefix sum. -/
theorem kahanAffineCoeffSteps_prefixSum_sub_sum_inputCoeff_abs_le_inputMajorantBudget
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (hu1 : fp.u ≤ 1) :
    let steps := kahanAffineCoeffSteps fp v k hk
    |(kahanPrefixState fp v k hk).s -
      (∑ i : Fin steps.length,
        (steps.get i).x * (1 + kahanAffineInputCoeff steps i))| ≤
      kahanAffineCorrectionIndexedBudget
        (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
        (fun j =>
          if hj : j < k then
            (kahanInputAbsMajorant fp v j
              (Nat.le_trans (Nat.le_of_lt hj) hk)).e
          else 0)
        steps +
        (kahanInputAbsMajorant fp v k hk).e := by
  dsimp
  let steps := kahanAffineCoeffSteps fp v k hk
  let coeffSum : ℝ :=
    ∑ i : Fin steps.length,
      (steps.get i).x * (1 + kahanAffineInputCoeff steps i)
  let budget :=
    kahanAffineCorrectionIndexedBudget
      (1 + 3 * fp.u ^ 2) (2 * fp.u + 12 * fp.u ^ 2)
      (fun j =>
        if hj : j < k then
          (kahanInputAbsMajorant fp v j
            (Nat.le_trans (Nat.le_of_lt hj) hk)).e
        else 0)
      steps
  have htotal :
      |((kahanPrefixState fp v k hk).s +
          (kahanPrefixState fp v k hk).e) - coeffSum| ≤ budget := by
    simpa [steps, coeffSum, budget] using
      kahanAffineCoeffSteps_prefixTotal_sub_sum_inputCoeff_abs_le_inputMajorantBudget
        fp v k hk hu1
  have he :
      |(kahanPrefixState fp v k hk).e| ≤
        (kahanInputAbsMajorant fp v k hk).e :=
    kahanPrefixState_e_abs_le_inputMajorant fp v k hk
  calc
    |(kahanPrefixState fp v k hk).s - coeffSum|
        = |(((kahanPrefixState fp v k hk).s +
              (kahanPrefixState fp v k hk).e) - coeffSum) -
            (kahanPrefixState fp v k hk).e| := by
            ring_nf
    _ ≤ |((kahanPrefixState fp v k hk).s +
            (kahanPrefixState fp v k hk).e) - coeffSum| +
          |(kahanPrefixState fp v k hk).e| := by
            simpa [sub_eq_add_neg, abs_neg] using
              abs_add_le
                (((kahanPrefixState fp v k hk).s +
                    (kahanPrefixState fp v k hk).e) - coeffSum)
                (-(kahanPrefixState fp v k hk).e)
    _ ≤ budget + (kahanInputAbsMajorant fp v k hk).e :=
          add_le_add htotal he

/-- The full indexed Kahan trace instantiates the residual-aware affine
coefficient recurrence for the final compensated total. -/
theorem kahanAffineCoeffSteps_fold_zero_eq_final_total
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) :
    kahanAffineResidualFold (kahanAffineCoeffSteps fp v n (Nat.le_refl n)) 0 =
      (fl_kahanState fp n v).s + (fl_kahanState fp n v).e := by
  simpa [fl_kahanState] using
    kahanAffineCoeffSteps_fold_zero_eq_prefix_total fp v n (Nat.le_refl n)

end NumStability
