-- Analysis/MullerRecurrence.lean
--
-- Exact Kahan-Muller recurrence algebra for Higham Chapter 1, Problem 1.8.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace NumStability

open Filter
open scoped Topology

/-!
# Kahan-Muller Recurrence

Higham Problem 1.8 asks about the recurrence

`x_{k+1} = 111 - (1130 - 3000 / x_{k-1}) / x_k`,
with `x_0 = 11/2` and `x_1 = 61/11`.

In exact arithmetic the intended solution is the ratio

`x_k = (5^(k+1) + 6^(k+1)) / (5^k + 6^k)`,

which is increasing and tends to `6`.  The same nonlinear recurrence is
obtained from a hidden third-order linear recurrence whose roots are
`5`, `6`, and `100`; a small spurious `100^k` component explains the familiar
finite-precision drift toward `100`.
-/

/-- Linear numerator/denominator sequence for the exact Problem 1.8 solution. -/
noncomputable def mullerY (k : ℕ) : ℝ :=
  (5 : ℝ) ^ k + (6 : ℝ) ^ k

/-- Exact-arithmetic solution of the Kahan-Muller recurrence in Problem 1.8. -/
noncomputable def mullerExact (k : ℕ) : ℝ :=
  mullerY (k + 1) / mullerY k

/-- Limit-friendly form of `mullerExact`, obtained by dividing by `6^k`. -/
noncomputable def mullerExactLimitForm (k : ℕ) : ℝ :=
  ((5 : ℝ) * ((5 : ℝ) / 6) ^ k + 6) / (((5 : ℝ) / 6) ^ k + 1)

/-- The exact denominator sequence is positive. -/
theorem mullerY_pos (k : ℕ) : 0 < mullerY k := by
  unfold mullerY
  positivity

/-- The hidden linear recurrence with roots `5`, `6`, and `100`, restricted to
the exact `5`/`6` solution branch. -/
theorem mullerY_linear_recurrence (k : ℕ) :
    mullerY (k + 3) =
      111 * mullerY (k + 2) - 1130 * mullerY (k + 1) + 3000 * mullerY k := by
  unfold mullerY
  ring_nf
  norm_num
  rfl

/-- Problem 1.8 initial value `x_0 = 11/2`. -/
theorem mullerExact_initial0 :
    mullerExact 0 = (11 : ℝ) / 2 := by
  norm_num [mullerExact, mullerY]

/-- Problem 1.8 initial value `x_1 = 61/11`. -/
theorem mullerExact_initial1 :
    mullerExact 1 = (61 : ℝ) / 11 := by
  norm_num [mullerExact, mullerY]

/-- The closed form satisfies the displayed nonlinear recurrence. -/
theorem mullerExact_satisfies_recurrence (k : ℕ) :
    mullerExact (k + 2) =
      111 - (1130 - 3000 / mullerExact k) / mullerExact (k + 1) := by
  unfold mullerExact
  have h0 : mullerY k ≠ 0 := ne_of_gt (mullerY_pos k)
  have h1 : mullerY (k + 1) ≠ 0 := ne_of_gt (mullerY_pos (k + 1))
  have h2 : mullerY (k + 2) ≠ 0 := ne_of_gt (mullerY_pos (k + 2))
  have hy := mullerY_linear_recurrence k
  field_simp [h0, h1, h2]
  rw [hy]
  ring

/-- In exact arithmetic the sequence is strictly increasing. -/
theorem mullerExact_lt_succ (k : ℕ) :
    mullerExact k < mullerExact (k + 1) := by
  unfold mullerExact mullerY
  have h0 : 0 < (5 : ℝ) ^ k + (6 : ℝ) ^ k := by positivity
  have h1 : 0 < (5 : ℝ) ^ (k + 1) + (6 : ℝ) ^ (k + 1) := by positivity
  field_simp [ne_of_gt h0, ne_of_gt h1]
  ring_nf
  norm_num

/-- The exact sequence is bounded above by its limit `6`. -/
theorem mullerExact_lt_six (k : ℕ) :
    mullerExact k < 6 := by
  unfold mullerExact mullerY
  have h0 : 0 < (5 : ℝ) ^ k + (6 : ℝ) ^ k := by positivity
  field_simp [ne_of_gt h0]
  ring_nf
  norm_num

/-- Dividing numerator and denominator by `6^k` gives the limit-friendly form. -/
theorem mullerExact_eq_limitForm (k : ℕ) :
    mullerExact k = mullerExactLimitForm k := by
  unfold mullerExact mullerY mullerExactLimitForm
  have h6 : (6 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
  have hden1 : (5 : ℝ) ^ k + (6 : ℝ) ^ k ≠ 0 := by positivity
  have hden2 : ((5 : ℝ) / 6) ^ k + 1 ≠ 0 := by positivity
  have hratio : ((5 : ℝ) / 6) ^ k * (6 : ℝ) ^ k = (5 : ℝ) ^ k := by
    rw [div_pow]
    field_simp [h6]
  field_simp [h6, hden1, hden2]
  ring_nf
  rw [hratio]
  ring

/-- Problem 1.8 exact-arithmetic convergence statement: `x_k -> 6`. -/
theorem mullerExact_tendsto_six :
    Tendsto mullerExact atTop (𝓝 6) := by
  have hpow : Tendsto (fun n : ℕ => ((5 : ℝ) / 6) ^ n) atTop (𝓝 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hnum :
      Tendsto (fun n : ℕ => (5 : ℝ) * ((5 : ℝ) / 6) ^ n + 6)
        atTop (𝓝 ((5 : ℝ) * 0 + 6)) := by
    exact (hpow.const_mul 5).add tendsto_const_nhds
  have hden :
      Tendsto (fun n : ℕ => ((5 : ℝ) / 6) ^ n + 1) atTop (𝓝 (0 + 1)) := by
    exact hpow.add tendsto_const_nhds
  have hlim :
      Tendsto mullerExactLimitForm atTop (𝓝 6) := by
    have hdiv := hnum.div hden (by norm_num)
    simpa [mullerExactLimitForm] using hdiv
  have hfun : mullerExact = mullerExactLimitForm := by
    funext n
    exact mullerExact_eq_limitForm n
  rw [hfun]
  exact hlim

/-- The exact value `x_34` rounds to `5.998` to four significant figures. -/
theorem problem_1_8_x34_rounds_to_5_998 :
    (59975 : ℝ) / 10000 < mullerExact 34 ∧
      mullerExact 34 < (59985 : ℝ) / 10000 := by
  norm_num [mullerExact, mullerY]

-- ============================================================
-- A concrete four-significant-decimal calculator-style trace
-- ============================================================

/-- One exact evaluation of the displayed Kahan-Muller nonlinear recurrence
from the two previous displayed values. -/
noncomputable def mullerRecurrenceStep (xm1 xk : ℝ) : ℝ :=
  111 - (1130 - 3000 / xm1) / xk

/-- A concrete four-significant-decimal display trace for Problem 1.8.  This
models the common calculator experiment in the exercise at the level where the
full recurrence expression is evaluated from the displayed values and then
rounded back to four significant decimal digits.  It is not an IEEE
primitive-operation trace. -/
noncomputable def mullerDecimal4Trace : ℕ → ℝ
  | 0 => 11 / 2
  | 1 => 1109 / 200      -- 5.545, the four-significant display of 61/11
  | 2 => 2791 / 500      -- 5.582
  | 3 => 5487 / 1000     -- 5.487
  | 4 => 3007 / 1000     -- 3.007
  | 5 => -8297 / 100     -- -82.97
  | 6 => 563 / 5         -- 112.6
  | 7 => 503 / 5         -- 100.6
  | _ => 100

/-- The exact recurrence value lies in the half-ulp display interval around
the shown next four-significant-decimal value. -/
def mullerDecimal4StepRoundsTo
    (xm1 xk xnext halfUlp : ℝ) : Prop :=
  xnext - halfUlp ≤ mullerRecurrenceStep xm1 xk ∧
    mullerRecurrenceStep xm1 xk < xnext + halfUlp

/-- The first displayed four-significant-decimal steps of Problem 1.8's
calculator-style experiment.  After the displayed values hit `100`, the exact
recurrence has `100` as a fixed point. -/
theorem mullerDecimal4Trace_rounding_intervals :
    mullerDecimal4StepRoundsTo
        (mullerDecimal4Trace 0) (mullerDecimal4Trace 1)
        (mullerDecimal4Trace 2) (1 / 2000) ∧
      mullerDecimal4StepRoundsTo
        (mullerDecimal4Trace 1) (mullerDecimal4Trace 2)
        (mullerDecimal4Trace 3) (1 / 2000) ∧
      mullerDecimal4StepRoundsTo
        (mullerDecimal4Trace 2) (mullerDecimal4Trace 3)
        (mullerDecimal4Trace 4) (1 / 2000) ∧
      mullerDecimal4StepRoundsTo
        (mullerDecimal4Trace 3) (mullerDecimal4Trace 4)
        (mullerDecimal4Trace 5) (1 / 200) ∧
      mullerDecimal4StepRoundsTo
        (mullerDecimal4Trace 4) (mullerDecimal4Trace 5)
        (mullerDecimal4Trace 6) (1 / 20) ∧
      mullerDecimal4StepRoundsTo
        (mullerDecimal4Trace 5) (mullerDecimal4Trace 6)
        (mullerDecimal4Trace 7) (1 / 20) ∧
      mullerDecimal4StepRoundsTo
        (mullerDecimal4Trace 6) (mullerDecimal4Trace 7)
        (mullerDecimal4Trace 8) (1 / 20) ∧
      mullerRecurrenceStep (mullerDecimal4Trace 8)
        (mullerDecimal4Trace 9) = 100 := by
  norm_num [mullerDecimal4StepRoundsTo, mullerRecurrenceStep,
    mullerDecimal4Trace]
  exact (by norm_num : (111 : ℝ) - (1130 - 30) / 100 = 100)

/-- In the concrete four-significant-decimal display trace, the computed
thirty-fourth value is `100`, not the exact value near `5.998`. -/
theorem mullerDecimal4Trace_34_eq_100 :
    mullerDecimal4Trace 34 = 100 := by
  rfl

/-- Quantitative comparison for the concrete Problem 1.8 display trace:
the four-significant-decimal recurrence value at step 34 is more than `94`
away from the exact `x_34`. -/
theorem mullerDecimal4Trace_34_abs_error_gt_94 :
    94 < |mullerDecimal4Trace 34 - mullerExact 34| := by
  have hlt : mullerExact 34 < (59985 : ℝ) / 10000 :=
    problem_1_8_x34_rounds_to_5_998.2
  have hpos : 0 ≤ mullerDecimal4Trace 34 - mullerExact 34 := by
    rw [mullerDecimal4Trace_34_eq_100]
    linarith
  rw [abs_of_nonneg hpos]
  rw [mullerDecimal4Trace_34_eq_100]
  linarith

-- ============================================================
-- Hidden `100^k` mode and finite-precision instability mechanism
-- ============================================================

/-- Three-mode denominator sequence for the same hidden linear recurrence.
The coefficient `c` represents a spurious `100^k` component. -/
noncomputable def mullerModeY (c : ℝ) (k : ℕ) : ℝ :=
  c * (100 : ℝ) ^ k + (5 : ℝ) ^ k + (6 : ℝ) ^ k

/-- Ratio sequence generated by a `5`/`6` solution plus a `100`-mode
contamination. -/
noncomputable def mullerModeRatio (c : ℝ) (k : ℕ) : ℝ :=
  mullerModeY c (k + 1) / mullerModeY c k

/-- With nonnegative contamination the denominator remains positive. -/
theorem mullerModeY_pos {c : ℝ} (hc : 0 ≤ c) (k : ℕ) :
    0 < mullerModeY c k := by
  unfold mullerModeY
  positivity

/-- The contaminated denominator has the same hidden linear recurrence, now
including the `100^k` root. -/
theorem mullerModeY_linear_recurrence (c : ℝ) (k : ℕ) :
    mullerModeY c (k + 3) =
      111 * mullerModeY c (k + 2) -
        1130 * mullerModeY c (k + 1) + 3000 * mullerModeY c k := by
  unfold mullerModeY
  ring_nf
  norm_num
  rfl

/-- Generic three-mode ratio identity exposing the pull toward the root `100`. -/
theorem threeModeRatio_eq_hundred_sub
    (c A B C : ℝ) (h : c * C + A + B ≠ 0) :
    (100 * c * C + 5 * A + 6 * B) / (c * C + A + B) =
      100 - (95 * A + 94 * B) / (c * C + A + B) := by
  field_simp [h]
  ring

/-- A contaminated ratio is `100` minus a shrinking correction when the
`100^k` mode dominates. -/
theorem mullerModeRatio_eq_hundred_sub (c : ℝ) (k : ℕ)
    (hy : mullerModeY c k ≠ 0) :
    mullerModeRatio c k =
      100 - (95 * (5 : ℝ) ^ k + 94 * (6 : ℝ) ^ k) / mullerModeY c k := by
  unfold mullerModeRatio mullerModeY
  rw [pow_succ, pow_succ, pow_succ]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    threeModeRatio_eq_hundred_sub c ((5 : ℝ) ^ k) ((6 : ℝ) ^ k)
      ((100 : ℝ) ^ k) hy

/-- Finite formal instability witness: once the hidden `100^k` component makes
the correction term smaller than one, the ratio is already larger than `99`. -/
theorem mullerModeRatio_gt_99_of_dominant
    (c : ℝ) (k : ℕ) (hc : 0 ≤ c)
    (hdom : 95 * (5 : ℝ) ^ k + 94 * (6 : ℝ) ^ k < mullerModeY c k) :
    99 < mullerModeRatio c k := by
  have hypos : 0 < mullerModeY c k := mullerModeY_pos hc k
  have hy : mullerModeY c k ≠ 0 := ne_of_gt hypos
  have hcorr :
      (95 * (5 : ℝ) ^ k + 94 * (6 : ℝ) ^ k) / mullerModeY c k < 1 := by
    have h := div_lt_div_of_pos_right hdom hypos
    simpa [div_self hy] using h
  rw [mullerModeRatio_eq_hundred_sub c k hy]
  linarith

/-- With nonnegative hidden contamination the contaminated ratio stays below
the attracting root `100`. -/
theorem mullerModeRatio_lt_100_of_nonneg
    (c : ℝ) (k : ℕ) (hc : 0 ≤ c) :
    mullerModeRatio c k < 100 := by
  have hypos : 0 < mullerModeY c k := mullerModeY_pos hc k
  have hy : mullerModeY c k ≠ 0 := ne_of_gt hypos
  have hnumpos :
      0 < 95 * (5 : ℝ) ^ k + 94 * (6 : ℝ) ^ k := by
    positivity
  have hcorrpos :
      0 <
        (95 * (5 : ℝ) ^ k + 94 * (6 : ℝ) ^ k) / mullerModeY c k :=
    div_pos hnumpos hypos
  rw [mullerModeRatio_eq_hundred_sub c k hy]
  linarith

/-- A unit-or-larger hidden `100^k` component dominates the `5^k`/`6^k`
correction terms from index `k = 2` onward. -/
theorem mullerModeY_dominates_of_one_le_of_two_le
    {c : ℝ} {k : ℕ} (hc : 1 ≤ c) (hk : 2 ≤ k) :
    95 * (5 : ℝ) ^ k + 94 * (6 : ℝ) ^ k < mullerModeY c k := by
  have h5le6 : (5 : ℝ) ^ k ≤ (6 : ℝ) ^ k := by
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have htail :
      94 * (5 : ℝ) ^ k + 93 * (6 : ℝ) ^ k ≤ 187 * (6 : ℝ) ^ k := by
    nlinarith
  have h187 : 187 * (6 : ℝ) ^ k < (100 : ℝ) ^ k := by
    rcases Nat.exists_eq_add_of_le hk with ⟨n, rfl⟩
    rw [pow_add, pow_add]
    norm_num
    have hpow : (6 : ℝ) ^ n ≤ (100 : ℝ) ^ n := by
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) n
    have hpos : 0 < (100 : ℝ) ^ n := by
      positivity
    nlinarith
  have hmain :
      94 * (5 : ℝ) ^ k + 93 * (6 : ℝ) ^ k < (100 : ℝ) ^ k :=
    lt_of_le_of_lt htail h187
  have hscale : (100 : ℝ) ^ k ≤ c * (100 : ℝ) ^ k := by
    have hpow_nonneg : 0 ≤ (100 : ℝ) ^ k := by
      positivity
    nlinarith
  unfold mullerModeY
  nlinarith

/-- For any unit-or-larger hidden contamination, the contaminated ratio exceeds
`99` from index `k = 2` onward. -/
theorem mullerModeRatio_gt_99_of_one_le_of_two_le
    {c : ℝ} {k : ℕ} (hc : 1 ≤ c) (hk : 2 ≤ k) :
    99 < mullerModeRatio c k := by
  have hc0 : 0 ≤ c := by
    linarith
  exact mullerModeRatio_gt_99_of_dominant c k hc0
    (mullerModeY_dominates_of_one_le_of_two_le hc hk)

/-- Concrete Problem 1.8 hidden-mode witness: a unit `100^k` contaminant is
already dominant at the source index `k = 34`, so the ratio exceeds `99`. -/
theorem mullerModeRatio_one_34_gt_99 :
    99 < mullerModeRatio 1 34 := by
  exact mullerModeRatio_gt_99_of_one_le_of_two_le (c := (1 : ℝ)) (k := 34)
    (by norm_num) (by norm_num)

/-- The same concrete contaminated ratio remains below the hidden root `100`. -/
theorem mullerModeRatio_one_34_lt_100 :
    mullerModeRatio 1 34 < 100 := by
  exact mullerModeRatio_lt_100_of_nonneg (1 : ℝ) 34 (by norm_num)

/-- At the displayed source index `k = 34`, a unit `100^k` contaminant makes the
hidden-mode ratio lie within one unit of the spurious limit `100`. -/
theorem mullerModeRatio_one_34_within_one_of_hundred :
    |mullerModeRatio 1 34 - 100| < 1 := by
  have hgt : 99 < mullerModeRatio 1 34 := mullerModeRatio_one_34_gt_99
  have hlt : mullerModeRatio 1 34 < 100 := mullerModeRatio_one_34_lt_100
  have hnonpos : mullerModeRatio 1 34 - 100 ≤ 0 := by
    linarith
  rw [abs_of_nonpos hnonpos]
  linarith

end NumStability
