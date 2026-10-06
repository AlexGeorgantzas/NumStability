import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Basic
import NumStability.Analysis.FloatingPointArithmetic.Format
import NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError
import NumStability.Analysis.Nonassociativity
import NumStability.Analysis.Rounding
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Source.Higham.Chapter01.Section11.Accumulation.Basic

/-!
# Chapter02 Section11 AccuracyTests Basic

Canonical destination for material split out of
`NumStability.Analysis.AccuracyTests` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

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
end NumStability

end
