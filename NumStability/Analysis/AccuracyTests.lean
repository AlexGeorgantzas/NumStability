-- Analysis/AccuracyTests.lean
--
-- Exact baselines for Higham Chapter 2, §2.8 accuracy tests.

import NumStability.Analysis.Accumulation
import NumStability.Analysis.Nonassociativity
import NumStability.Analysis.RoundingProductBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace NumStability

noncomputable section

/-!
# Accuracy Test Baselines

Higham Chapter 2, §2.8 gives quick empirical tests for floating-point
arithmetic.  This module records the exact real-arithmetic baselines and the
algebra behind the exponentiation sensitivity discussion.  It does not claim
that the historical machine/table outputs are produced by the current Lean
floating-point model.
-/

/-- The exact real expression behind Table 2.3's unit-roundoff probe.  In exact
arithmetic it is zero; nonzero values are a finite-arithmetic artifact. -/
def unitRoundoffProbeExact : ℝ :=
  |(3 : ℝ) * ((4 : ℝ) / 3 - 1) - 1|

theorem unitRoundoffProbeExact_eq_zero :
    unitRoundoffProbeExact = 0 := by
  norm_num [unitRoundoffProbeExact]
  rfl

/-- Cody's sine-test target expression from §2.8. -/
def codySineTestExact : ℝ :=
  Real.sin 22

/-- The absolute value printed in Table 2.4's exact row for `sin(22)`. -/
def codySineDisplayedTableMagnitude17 : ℝ :=
  (88513092904038759 : ℝ) / 10 ^ 19

/-- The signed decimal printed in Table 2.4's exact row for `sin(22)`. -/
def codySineDisplayedTableDecimal17 : ℝ :=
  -codySineDisplayedTableMagnitude17

/-- The reduced argument behind Cody's sine test: `22` is close to `7*pi`. -/
def codySineReducedArgument : ℝ :=
  22 - 7 * Real.pi

theorem codySineReducedArgument_pos :
    0 < codySineReducedArgument := by
  unfold codySineReducedArgument
  nlinarith [Real.pi_lt_d4]

theorem codySineReducedArgument_lt_one_hundredth :
    codySineReducedArgument < 1 / 100 := by
  unfold codySineReducedArgument
  nlinarith [Real.pi_gt_d4]

theorem codySineReducedArgument_abs_lt_one_hundredth :
    |codySineReducedArgument| < 1 / 100 := by
  rw [abs_of_pos codySineReducedArgument_pos]
  exact codySineReducedArgument_lt_one_hundredth

theorem codySineTestExact_eq_neg_sin_reducedArgument :
    codySineTestExact = -Real.sin codySineReducedArgument := by
  have h := Real.sin_sub_nat_mul_pi (22 : ℝ) 7
  norm_num at h
  rw [codySineTestExact, codySineReducedArgument]
  rw [h]
  ring

theorem codySineTestExact_neg :
    codySineTestExact < 0 := by
  have hltpi : codySineReducedArgument < Real.pi := by
    have hsmall := codySineReducedArgument_lt_one_hundredth
    have hpi : (1 / 100 : ℝ) < Real.pi := by
      nlinarith [Real.pi_gt_three]
    exact lt_trans hsmall hpi
  have hsin : 0 < Real.sin codySineReducedArgument :=
    Real.sin_pos_of_pos_of_lt_pi codySineReducedArgument_pos hltpi
  rw [codySineTestExact_eq_neg_sin_reducedArgument]
  linarith

theorem codySineTestExact_abs_lt_one_hundredth :
    |codySineTestExact| < 1 / 100 := by
  calc
    |codySineTestExact| = |Real.sin codySineReducedArgument| := by
      rw [codySineTestExact_eq_neg_sin_reducedArgument, abs_neg]
    _ ≤ |codySineReducedArgument| := Real.abs_sin_le_abs
    _ < (1 / 100 : ℝ) := codySineReducedArgument_abs_lt_one_hundredth

/-- The first five odd terms of the alternating Taylor polynomial for sine:
`x - x^3/3! + x^5/5! - x^7/7! + x^9/9!`. -/
def sineTaylorOdd5 (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 5,
    (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / (Nat.factorial (2 * i + 1) : ℝ))

theorem sineTaylorOdd5_eq (x : ℝ) :
    sineTaylorOdd5 x =
      x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 := by
  norm_num [sineTaylorOdd5, Finset.sum_range_succ]
  ring_nf
  ac_rfl

private theorem summable_sine_odd_terms (x : ℝ) :
    Summable
      (fun n : ℕ => x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)) := by
  simpa only [Function.comp_apply] using
    (Real.summable_pow_div_factorial x).comp_injective
      (by
        intro a b h
        have hsucc : Nat.succ (2 * a) = Nat.succ (2 * b) := by
          simpa [Nat.succ_eq_add_one] using h
        have hmul : 2 * a = 2 * b := Nat.succ.inj hsucc
        exact Nat.mul_left_cancel (by norm_num : 0 < 2) hmul)

private theorem sine_odd_terms_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone
      (fun n : ℕ => x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)) := by
  refine antitone_nat_of_succ_le ?_
  intro n
  have hx2 : x ^ 2 ≤ 1 := by
    have hmul := mul_le_mul hx1 hx1 hx0 zero_le_one
    nlinarith [hmul]
  have hpow : x ^ (2 * (n + 1) + 1) ≤ x ^ (2 * n + 1) := by
    have hnon : 0 ≤ x ^ (2 * n + 1) := pow_nonneg hx0 _
    calc
      x ^ (2 * (n + 1) + 1) = x ^ (2 * n + 1) * x ^ 2 := by
        have hn : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by omega
        rw [hn, pow_add]
      _ ≤ x ^ (2 * n + 1) * 1 := mul_le_mul_of_nonneg_left hx2 hnon
      _ = x ^ (2 * n + 1) := by ring
  have hden_nonneg : 0 ≤ (Nat.factorial (2 * (n + 1) + 1) : ℝ) := by positivity
  have hden_pos : 0 < (Nat.factorial (2 * n + 1) : ℝ) := by positivity
  have hden_le :
      (Nat.factorial (2 * n + 1) : ℝ) ≤
        (Nat.factorial (2 * (n + 1) + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : 2 * n + 1 ≤ 2 * (n + 1) + 1)
  have hnum_nonneg : 0 ≤ x ^ (2 * n + 1) := pow_nonneg hx0 _
  exact (div_le_div_of_nonneg_right hpow hden_nonneg).trans
    (div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_le)

/-- Alternating-series remainder bound for the five-term odd Taylor polynomial
for `sin` on `[0, 1]`. -/
theorem sineTaylorOdd5_abs_error_le_next (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.sin x - sineTaylorOdd5 x| ≤ x ^ 11 / (Nat.factorial 11 : ℝ) := by
  let f : ℕ → ℝ :=
    fun n => x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)
  have hsummable : Summable f := by
    simpa [f] using summable_sine_odd_terms x
  have hant : Antitone f := by
    simpa [f] using sine_odd_terms_antitone (x := x) hx0 hx1
  have h := alternating_series_error_bound f hant hsummable 5
  have htsum : (∑' i : ℕ, (-1 : ℝ) ^ i * f i) = Real.sin x := by
    simpa [f, div_eq_mul_inv, mul_assoc] using (Real.hasSum_sin x).tsum_eq
  rw [htsum] at h
  have hpartial : (∑ i ∈ Finset.range 5, (-1 : ℝ) ^ i * f i) =
      sineTaylorOdd5 x := by
    simp [f, sineTaylorOdd5]
  have hnext : f 5 = x ^ 11 / (Nat.factorial 11 : ℝ) := by
    norm_num [f]
  simpa [hpartial, hnext] using h

theorem codySineReducedArgument_sineTaylorOdd5_abs_error_lt_one_e20 :
    |Real.sin codySineReducedArgument - sineTaylorOdd5 codySineReducedArgument| <
      (1 : ℝ) / 10 ^ 20 := by
  have hle := sineTaylorOdd5_abs_error_le_next codySineReducedArgument
    (le_of_lt codySineReducedArgument_pos)
    (le_trans (le_of_lt codySineReducedArgument_lt_one_hundredth)
      (by norm_num : (1 / 100 : ℝ) ≤ 1))
  have hr_nonneg : 0 ≤ codySineReducedArgument := le_of_lt codySineReducedArgument_pos
  have hr_le : codySineReducedArgument ≤ (1 / 100 : ℝ) :=
    le_of_lt codySineReducedArgument_lt_one_hundredth
  have hpow : codySineReducedArgument ^ 11 ≤ (1 / 100 : ℝ) ^ 11 :=
    pow_le_pow_left₀ hr_nonneg hr_le 11
  have hrem :
      codySineReducedArgument ^ 11 / (Nat.factorial 11 : ℝ) <
        (1 : ℝ) / 10 ^ 20 := by
    calc
      codySineReducedArgument ^ 11 / (Nat.factorial 11 : ℝ)
          ≤ (1 / 100 : ℝ) ^ 11 / (Nat.factorial 11 : ℝ) := by
              exact div_le_div_of_nonneg_right hpow (by positivity)
      _ < (1 : ℝ) / 10 ^ 20 := by norm_num
  exact lt_of_le_of_lt hle hrem

theorem codySineTestExact_sineTaylorOdd5_abs_error_lt_one_e20 :
    |codySineTestExact + sineTaylorOdd5 codySineReducedArgument| <
      (1 : ℝ) / 10 ^ 20 := by
  have h := codySineReducedArgument_sineTaylorOdd5_abs_error_lt_one_e20
  rw [codySineTestExact_eq_neg_sin_reducedArgument]
  have halg :
      -Real.sin codySineReducedArgument + sineTaylorOdd5 codySineReducedArgument =
        -(Real.sin codySineReducedArgument - sineTaylorOdd5 codySineReducedArgument) := by
    ring
  rw [halg, abs_neg]
  exact h

private def codySineReducedArgumentLowerD20 : ℝ :=
  22 - 7 * (314159265358979323847 : ℝ) / 10 ^ 20

private def codySineReducedArgumentUpperD20 : ℝ :=
  22 - 7 * (314159265358979323846 : ℝ) / 10 ^ 20

private theorem codySineReducedArgumentLowerD20_le :
    codySineReducedArgumentLowerD20 ≤ codySineReducedArgument := by
  unfold codySineReducedArgumentLowerD20 codySineReducedArgument
  nlinarith [Real.pi_lt_d20]

private theorem codySineReducedArgument_leUpperD20 :
    codySineReducedArgument ≤ codySineReducedArgumentUpperD20 := by
  unfold codySineReducedArgumentUpperD20 codySineReducedArgument
  nlinarith [Real.pi_gt_d20]

theorem codySineTaylorOdd5_displayedMagnitude_abs_error_lt_41e21 :
    |sineTaylorOdd5 codySineReducedArgument - codySineDisplayedTableMagnitude17| <
      (41 : ℝ) / 10 ^ 21 := by
  let lo : ℝ := codySineReducedArgumentLowerD20
  let hi : ℝ := codySineReducedArgumentUpperD20
  let r : ℝ := codySineReducedArgument
  let d : ℝ := codySineDisplayedTableMagnitude17
  have hlo : lo ≤ r := by
    simpa [lo, r] using codySineReducedArgumentLowerD20_le
  have hhi : r ≤ hi := by
    simpa [hi, r] using codySineReducedArgument_leUpperD20
  have hlo_nonneg : 0 ≤ lo := by
    norm_num [lo, codySineReducedArgumentLowerD20]
  have hr_nonneg : 0 ≤ r := by
    simpa [r] using le_of_lt codySineReducedArgument_pos
  have hhi_nonneg : 0 ≤ hi := by
    norm_num [hi, codySineReducedArgumentUpperD20]
  have h3lo : lo ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hlo_nonneg hlo 3
  have h5hi : r ^ 5 ≤ hi ^ 5 := pow_le_pow_left₀ hr_nonneg hhi 5
  have h7lo : lo ^ 7 ≤ r ^ 7 := pow_le_pow_left₀ hlo_nonneg hlo 7
  have h9hi : r ^ 9 ≤ hi ^ 9 := pow_le_pow_left₀ hr_nonneg hhi 9
  have h3hi : r ^ 3 ≤ hi ^ 3 := pow_le_pow_left₀ hr_nonneg hhi 3
  have h5lo : lo ^ 5 ≤ r ^ 5 := pow_le_pow_left₀ hlo_nonneg hlo 5
  have h7hi : r ^ 7 ≤ hi ^ 7 := pow_le_pow_left₀ hr_nonneg hhi 7
  have h9lo : lo ^ 9 ≤ r ^ 9 := pow_le_pow_left₀ hlo_nonneg hlo 9
  have hupper :
      sineTaylorOdd5 r - d ≤
        hi - lo ^ 3 / 6 + hi ^ 5 / 120 - lo ^ 7 / 5040 + hi ^ 9 / 362880 - d := by
    rw [sineTaylorOdd5_eq]
    nlinarith
  have hlower :
      lo - hi ^ 3 / 6 + lo ^ 5 / 120 - hi ^ 7 / 5040 + lo ^ 9 / 362880 - d ≤
        sineTaylorOdd5 r - d := by
    rw [sineTaylorOdd5_eq]
    nlinarith
  have hupper_num :
      hi - lo ^ 3 / 6 + hi ^ 5 / 120 - lo ^ 7 / 5040 + hi ^ 9 / 362880 - d <
        (41 : ℝ) / 10 ^ 21 := by
    norm_num [lo, hi, d, codySineReducedArgumentLowerD20,
      codySineReducedArgumentUpperD20, codySineDisplayedTableMagnitude17]
  have hlower_num :
      -((41 : ℝ) / 10 ^ 21) <
        lo - hi ^ 3 / 6 + lo ^ 5 / 120 - hi ^ 7 / 5040 + lo ^ 9 / 362880 - d := by
    norm_num [lo, hi, d, codySineReducedArgumentLowerD20,
      codySineReducedArgumentUpperD20, codySineDisplayedTableMagnitude17]
  rw [abs_lt]
  constructor
  · exact lt_of_lt_of_le hlower_num hlower
  · exact lt_of_le_of_lt hupper hupper_num

theorem codySineTestExact_displayedTableDecimal17_abs_error_lt_half_last_place :
    |codySineTestExact - codySineDisplayedTableDecimal17| <
      (1 / 2 : ℝ) / 10 ^ 19 := by
  have hrem_le := sineTaylorOdd5_abs_error_le_next codySineReducedArgument
    (le_of_lt codySineReducedArgument_pos)
    (le_trans (le_of_lt codySineReducedArgument_lt_one_hundredth)
      (by norm_num : (1 / 100 : ℝ) ≤ 1))
  have hr_nonneg : 0 ≤ codySineReducedArgument := le_of_lt codySineReducedArgument_pos
  have hr_le : codySineReducedArgument ≤ (1 / 100 : ℝ) :=
    le_of_lt codySineReducedArgument_lt_one_hundredth
  have hpow : codySineReducedArgument ^ 11 ≤ (1 / 100 : ℝ) ^ 11 :=
    pow_le_pow_left₀ hr_nonneg hr_le 11
  have hrem :
      |Real.sin codySineReducedArgument - sineTaylorOdd5 codySineReducedArgument| <
        (1 : ℝ) / 10 ^ 21 := by
    refine lt_of_le_of_lt hrem_le ?_
    calc
      codySineReducedArgument ^ 11 / (Nat.factorial 11 : ℝ)
          ≤ (1 / 100 : ℝ) ^ 11 / (Nat.factorial 11 : ℝ) := by
              exact div_le_div_of_nonneg_right hpow (by positivity)
      _ < (1 : ℝ) / 10 ^ 21 := by norm_num
  have hpoly := codySineTaylorOdd5_displayedMagnitude_abs_error_lt_41e21
  have htarget :
      |Real.sin codySineReducedArgument - codySineDisplayedTableMagnitude17| <
        (1 / 2 : ℝ) / 10 ^ 19 := by
    calc
      |Real.sin codySineReducedArgument - codySineDisplayedTableMagnitude17|
          =
            |(Real.sin codySineReducedArgument -
                sineTaylorOdd5 codySineReducedArgument) +
              (sineTaylorOdd5 codySineReducedArgument -
                codySineDisplayedTableMagnitude17)| := by
              ring_nf
      _ ≤ |Real.sin codySineReducedArgument - sineTaylorOdd5 codySineReducedArgument| +
            |sineTaylorOdd5 codySineReducedArgument -
              codySineDisplayedTableMagnitude17| := abs_add_le _ _
      _ < (1 : ℝ) / 10 ^ 21 + (41 : ℝ) / 10 ^ 21 :=
            add_lt_add hrem hpoly
      _ < (1 / 2 : ℝ) / 10 ^ 19 := by norm_num
  rw [codySineTestExact_eq_neg_sin_reducedArgument, codySineDisplayedTableDecimal17]
  have halg :
      -Real.sin codySineReducedArgument - -codySineDisplayedTableMagnitude17 =
        -(Real.sin codySineReducedArgument - codySineDisplayedTableMagnitude17) := by
    ring
  rw [halg, abs_neg]
  exact htarget

/-- Cody's exponentiation-test base `2.5`. -/
def codyPowerBase : ℝ :=
  (5 : ℝ) / 2

/-- Cody's exponentiation-test exponent `125`. -/
def codyPowerExponent : ℕ :=
  125

/-- Exact real value of the source expression `2.5^125`. -/
def codyPowerTestExact : ℝ :=
  codyPowerBase ^ codyPowerExponent

/-- The alternative exact path `exp(125 * log 2.5)`. -/
def codyPowerExpLogPath : ℝ :=
  Real.exp ((codyPowerExponent : ℝ) * Real.log codyPowerBase)

theorem codyPowerBase_pos : 0 < codyPowerBase := by
  norm_num [codyPowerBase]

/-- In exact real arithmetic, the power path and the `exp(y log x)` path agree
for Cody's exponentiation test. -/
theorem codyPowerExpLogPath_eq_exact :
    codyPowerExpLogPath = codyPowerTestExact := by
  have hbase : 0 < ((5 : ℝ) / 2) := by norm_num
  calc
    codyPowerExpLogPath
        = Real.exp ((125 : ℝ) * Real.log ((5 : ℝ) / 2)) := by
            norm_num [codyPowerExpLogPath, codyPowerExponent, codyPowerBase]
    _ = Real.exp (Real.log ((5 : ℝ) / 2) * (125 : ℝ)) := by
            rw [mul_comm]
    _ = ((5 : ℝ) / 2) ^ (125 : ℝ) :=
            (Real.rpow_def_of_pos hbase 125).symm
    _ = ((5 : ℝ) / 2) ^ codyPowerExponent := by
            norm_num [codyPowerExponent, Real.rpow_natCast]
    _ = codyPowerTestExact := by
            rfl

/-- The 21-significant-digit decimal printed in §2.8 for `2.5^125`. -/
def codyPowerDisplayedDecimal21 : ℝ :=
  (552714787526044456025 : ℝ) * 10 ^ 29

/-- The shorter exact-row decimal printed in Table 2.5 for `2.5^125`. -/
def codyPowerDisplayedTableDecimal17 : ℝ :=
  (55271478752604446 : ℝ) * 10 ^ 33

/-- The displayed `5.52714787526044456025 * 10^49` value is correctly rounded
to the last shown significant digit for the exact real value of `2.5^125`. -/
theorem codyPowerTestExact_displayedDecimal21_abs_error_lt_half_last_place :
    |codyPowerTestExact - codyPowerDisplayedDecimal21| < (1 / 2 : ℝ) * 10 ^ 29 := by
  have hraw :
      |codyPowerTestExact - codyPowerDisplayedDecimal21| =
        (1163258592366355681624273596558622262496587443165481090545654296875 : ℝ) /
          42535295865117307932921825928971026432 := by
    norm_num [codyPowerTestExact, codyPowerBase, codyPowerExponent,
      codyPowerDisplayedDecimal21]
  rw [hraw]
  have hlast :
      (1 / 2 : ℝ) * 10 ^ 29 = (50000000000000000000000000000 : ℝ) := by
    norm_num
  rw [hlast]
  rw [div_lt_iff₀ (by norm_num :
    (0 : ℝ) < 42535295865117307932921825928971026432)]
  exact_mod_cast (show
    1163258592366355681624273596558622262496587443165481090545654296875 <
      50000000000000000000000000000 *
        42535295865117307932921825928971026432 by
    native_decide)

/-- The Table 2.5 exact-row value `5.5271478752604446 * 10^49` is correctly
rounded to the last shown significant digit for the exact real value. -/
theorem codyPowerTestExact_displayedTableDecimal17_abs_error_lt_half_last_place :
    |codyPowerTestExact - codyPowerDisplayedTableDecimal17| < (1 / 2 : ℝ) * 10 ^ 33 := by
  have hraw :
      |codyPowerTestExact - codyPowerDisplayedTableDecimal17| =
        (16908943364976496259018050080362541628982496587443165481090545654296875 :
          ℝ) / 42535295865117307932921825928971026432 := by
    norm_num [codyPowerTestExact, codyPowerBase, codyPowerExponent,
      codyPowerDisplayedTableDecimal17]
  rw [hraw]
  have hlast :
      (1 / 2 : ℝ) * 10 ^ 33 = (500000000000000000000000000000000 : ℝ) := by
    norm_num
  rw [hlast]
  rw [div_lt_iff₀ (by norm_num :
    (0 : ℝ) < 42535295865117307932921825928971026432)]
  exact_mod_cast (show
    16908943364976496259018050080362541628982496587443165481090545654296875 <
      500000000000000000000000000000000 *
        42535295865117307932921825928971026432 by
    native_decide)

/-- Exact sensitivity identity used in the exponentiation-test explanation:
an absolute error `deltaW` in `w` turns into relative error
`exp(deltaW) - 1` in `exp w`. -/
theorem exp_absolute_error_relative_error_eq (w deltaW : ℝ) :
    (Real.exp (w + deltaW) - Real.exp w) / Real.exp w =
      Real.exp deltaW - 1 := by
  have hw : Real.exp w ≠ 0 := (Real.exp_pos w).ne'
  rw [Real.exp_add]
  field_simp [hw]

/-- Quantitative version of the §2.8 sensitivity explanation: for a nonzero
small absolute error in `w`, the relative error induced in `exp w` is below
`1.01` times that absolute error. -/
theorem exp_absolute_error_relative_error_abs_lt_101_mul_abs (w deltaW : ℝ)
    (hdelta : deltaW ≠ 0) (hsmall : |deltaW| < 1 / 100) :
    |(Real.exp (w + deltaW) - Real.exp w) / Real.exp w| <
      (101 / 100 : ℝ) * |deltaW| := by
  rw [exp_absolute_error_relative_error_eq]
  exact lt_of_le_of_lt
    (real_abs_exp_sub_one_le_exp_abs_sub_one deltaW)
    (real_exp_sub_one_lt_101_mul_of_pos_of_lt_cent
      (abs_pos.mpr hdelta) hsmall)

/-- First Karpinski guard-digit probe from §2.8, evaluated in exact real
arithmetic. -/
def karpinskiGuardDigitProbeA : ℝ :=
  (9 : ℝ) / 27 * 3 - 1

/-- Second Karpinski guard-digit probe from §2.8, evaluated in exact real
arithmetic. -/
def karpinskiGuardDigitProbeB : ℝ :=
  (9 : ℝ) / 27 * 3 - (1 / 2) - (1 / 2)

/-- Finite-operation trace for Karpinski's first guard-digit probe. -/
def karpinskiGuardDigitFiniteProbeA (fmt : FloatingPointFormat) : ℝ :=
  fmt.finiteRoundToEvenOp BasicOp.sub
    (fmt.finiteRoundToEvenOp BasicOp.mul
      (fmt.finiteRoundToEvenOp BasicOp.div (9 : ℝ) 27) 3)
    1

/-- Finite-operation trace for Karpinski's second guard-digit probe. -/
def karpinskiGuardDigitFiniteProbeB (fmt : FloatingPointFormat) : ℝ :=
  fmt.finiteRoundToEvenOp BasicOp.sub
    (fmt.finiteRoundToEvenOp BasicOp.sub
      (fmt.finiteRoundToEvenOp BasicOp.mul
        (fmt.finiteRoundToEvenOp BasicOp.div (9 : ℝ) 27) 3)
      (1 / 2))
    (1 / 2)

theorem karpinskiGuardDigitProbeA_eq_zero :
    karpinskiGuardDigitProbeA = 0 := by
  norm_num [karpinskiGuardDigitProbeA]
  rfl

theorem karpinskiGuardDigitProbeB_eq_zero :
    karpinskiGuardDigitProbeB = 0 := by
  norm_num [karpinskiGuardDigitProbeB]
  rfl

theorem karpinskiGuardDigitProbes_equal :
    karpinskiGuardDigitProbeA = karpinskiGuardDigitProbeB := by
  rw [karpinskiGuardDigitProbeA_eq_zero, karpinskiGuardDigitProbeB_eq_zero]

namespace FloatingPointFormat

theorem decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_nine_tenths :
    decimalOneDigitThreeExponentFormat.normalizedExponentRepresentation
      (9 / 10 : ℝ) 0 := by
  refine ⟨false, 9, ?_, ?_, ?_⟩
  · norm_num [decimalOneDigitThreeExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  · norm_num [decimalOneDigitThreeExponentFormat, exponentInRange]
  · norm_num [decimalOneDigitThreeExponentFormat, normalizedValue, signValue, betaR]

theorem decimalOneDigitThreeExponentFormat_finiteSystem_nine_tenths :
    decimalOneDigitThreeExponentFormat.finiteSystem (9 / 10 : ℝ) :=
  Or.inr (Or.inl
    (decimalOneDigitThreeExponentFormat.normalizedExponentRepresentation_normalizedSystem
      decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_nine_tenths))

/-- In the existing one-digit decimal format, the finite round-to-even division
step in Karpinski's probe rounds `9/27` to `0.3`. -/
theorem decimalOneDigitThreeExponent_karpinski_div_nine_twentySeven :
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
        BasicOp.div (9 : ℝ) 27 = 3 / 10 := by
  let fmt := decimalOneDigitThreeExponentFormat
  let a : ℝ := fmt.normalizedValue false 3 0
  let b : ℝ := fmt.normalizedValue false 4 0
  let x : ℝ := (1 / 3 : ℝ)
  have hm : fmt.normalizedMantissa 3 := by
    norm_num [fmt, decimalOneDigitThreeExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (3 + 1) := by
    norm_num [fmt, decimalOneDigitThreeExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 3, (0 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have hstrict : a < x ∧ x < b := by
    norm_num [x, a, b, fmt, decimalOneDigitThreeExponentFormat,
      normalizedValue, signValue, betaR]
  have hxrange : fmt.finiteNormalRange x := by
    rw [finiteNormalRange]
    have hxnonneg : 0 ≤ x := by norm_num [x]
    rw [abs_of_nonneg hxnonneg]
    constructor
    · norm_num [x, fmt, decimalOneDigitThreeExponentFormat,
        minNormalMagnitude, betaR]
    · have hmax : fmt.maxFiniteMagnitude = 90 := by
        norm_num [fmt, decimalOneDigitThreeExponentFormat,
          maxFiniteMagnitude, betaR]
        rfl
      simpa [x, hmax] using (by norm_num : (1 / 3 : ℝ) ≤ 90)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    norm_num [x, a, b, fmt, decimalOneDigitThreeExponentFormat,
      normalizedValue, signValue, betaR]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  have htarget : fmt.finiteRoundToEven ((9 : ℝ) / 27) = a := by
    have hxdiv : ((9 : ℝ) / 27) = x := by norm_num [x]
    rw [hxdiv]
    exact hround
  have ha : a = (3 / 10 : ℝ) := by
    norm_num [a, fmt, decimalOneDigitThreeExponentFormat, normalizedValue,
      signValue, betaR]
  simpa [finiteRoundToEvenOp, BasicOp.exact, ha] using htarget

theorem decimalOneDigitThreeExponent_karpinski_mul_three_tenths_three_exact :
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
        BasicOp.mul (3 / 10 : ℝ) 3 = 9 / 10 := by
  have hfin :
      decimalOneDigitThreeExponentFormat.finiteSystem
        (BasicOp.exact BasicOp.mul (3 / 10 : ℝ) 3) := by
    norm_num [BasicOp.exact]
    exact decimalOneDigitThreeExponentFormat_finiteSystem_nine_tenths
  have hround :=
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul) (x := (3 / 10 : ℝ)) (y := (3 : ℝ)) hfin
  change decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
      BasicOp.mul (3 / 10 : ℝ) 3 = (3 / 10 : ℝ) * 3 at hround
  norm_num at hround
  exact hround

theorem decimalOneDigitThreeExponent_karpinski_sub_nine_tenths_one_exact :
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
        BasicOp.sub (9 / 10 : ℝ) 1 = -(1 / 10) := by
  have hfin :
      decimalOneDigitThreeExponentFormat.finiteSystem
        (BasicOp.exact BasicOp.sub (9 / 10 : ℝ) 1) := by
    norm_num [BasicOp.exact]
    exact decimalOneDigitThreeExponentFormat.finiteSystem_neg
      decimalOneDigitThreeExponentFormat_finiteSystem_one_tenth
  have hround :=
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (9 / 10 : ℝ)) (y := (1 : ℝ)) hfin
  change decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
      BasicOp.sub (9 / 10 : ℝ) 1 = (9 / 10 : ℝ) - 1 at hround
  norm_num at hround
  exact hround

theorem decimalOneDigitThreeExponent_karpinski_sub_nine_tenths_half_exact :
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
        BasicOp.sub (9 / 10 : ℝ) (1 / 2) = 2 / 5 := by
  have hfin :
      decimalOneDigitThreeExponentFormat.finiteSystem
        (BasicOp.exact BasicOp.sub (9 / 10 : ℝ) (1 / 2)) := by
    norm_num [BasicOp.exact]
    exact decimalOneDigitThreeExponentFormat_finiteSystem_two_fifths
  have hround :=
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (9 / 10 : ℝ)) (y := (1 / 2 : ℝ)) hfin
  change decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
      BasicOp.sub (9 / 10 : ℝ) (1 / 2) = (9 / 10 : ℝ) - (1 / 2) at hround
  norm_num at hround
  exact hround

theorem decimalOneDigitThreeExponent_karpinski_sub_two_fifths_half_exact :
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
        BasicOp.sub (2 / 5 : ℝ) (1 / 2) = -(1 / 10) := by
  have hfin :
      decimalOneDigitThreeExponentFormat.finiteSystem
        (BasicOp.exact BasicOp.sub (2 / 5 : ℝ) (1 / 2)) := by
    norm_num [BasicOp.exact]
    exact decimalOneDigitThreeExponentFormat.finiteSystem_neg
      decimalOneDigitThreeExponentFormat_finiteSystem_one_tenth
  have hround :=
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (2 / 5 : ℝ)) (y := (1 / 2 : ℝ)) hfin
  change decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
      BasicOp.sub (2 / 5 : ℝ) (1 / 2) = (2 / 5 : ℝ) - (1 / 2) at hround
  norm_num at hround
  exact hround

theorem decimalOneDigitThreeExponent_karpinskiProbeA_eq_neg_one_tenth :
    karpinskiGuardDigitFiniteProbeA decimalOneDigitThreeExponentFormat =
      -(1 / 10 : ℝ) := by
  simp [karpinskiGuardDigitFiniteProbeA,
    decimalOneDigitThreeExponent_karpinski_div_nine_twentySeven,
    decimalOneDigitThreeExponent_karpinski_mul_three_tenths_three_exact,
    decimalOneDigitThreeExponent_karpinski_sub_nine_tenths_one_exact]

theorem decimalOneDigitThreeExponent_karpinskiProbeB_eq_neg_one_tenth :
    karpinskiGuardDigitFiniteProbeB decimalOneDigitThreeExponentFormat =
      -(1 / 10 : ℝ) := by
  unfold karpinskiGuardDigitFiniteProbeB
  rw [decimalOneDigitThreeExponent_karpinski_div_nine_twentySeven]
  rw [decimalOneDigitThreeExponent_karpinski_mul_three_tenths_three_exact]
  change decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
      BasicOp.sub
        (decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
          BasicOp.sub (9 / 10 : ℝ) (1 / 2))
        (1 / 2) = -(1 / 10 : ℝ)
  rw [decimalOneDigitThreeExponent_karpinski_sub_nine_tenths_half_exact]
  exact decimalOneDigitThreeExponent_karpinski_sub_two_fifths_half_exact

/-- A concrete finite round-to-even trace of Karpinski's two probe expressions:
in this one-digit decimal format, both finite-operation paths produce `-0.1`. -/
theorem decimalOneDigitThreeExponent_karpinskiProbes_equal :
    karpinskiGuardDigitFiniteProbeA decimalOneDigitThreeExponentFormat =
      karpinskiGuardDigitFiniteProbeB decimalOneDigitThreeExponentFormat := by
  rw [decimalOneDigitThreeExponent_karpinskiProbeA_eq_neg_one_tenth,
    decimalOneDigitThreeExponent_karpinskiProbeB_eq_neg_one_tenth]

end FloatingPointFormat

end

end NumStability
