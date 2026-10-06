-- Analysis/DoubleRounding.lean
--
-- Concrete finite double-rounding example for Higham Chapter 2, §2.3 and
-- Problem 2.9.

import NumStability.Analysis.FloatingPointArithmetic

namespace NumStability

noncomputable section

namespace FloatingPointFormat

/-!
# Double Rounding

Higham Chapter 2, §2.3 notes that computing first in an extended format and
then rounding again to the destination format can differ from rounding directly
to the destination format.  This file records a small binary round-to-even
counterexample over finite normal values:

* the extended `t = 3` format rounds `21/16` to `5/4`;
* the destination `t = 2` format rounds that midpoint `5/4` to the even
  mantissa endpoint `1`;
* direct destination rounding of `21/16` gives `3/2`.

The example is intentionally finite-format only: it does not claim the full
IEEE double/64-bit-extended arithmetic trace requested in Problem 2.9.
-/

/-- A tiny binary destination format with precision `t = 2` and one normal
exponent bin.  Positive normal finite values are `1` and `3/2`. -/
def binaryT2DoubleRoundingDestinationFormat : FloatingPointFormat where
  beta := 2
  t := 2
  emin := 1
  emax := 1
  beta_ge_two := by norm_num
  t_pos := by norm_num
  emin_le_emax := by norm_num

/-- A tiny binary extended format with precision `t = 3` and one normal
exponent bin.  Positive normal finite values include `5/4` and `3/2`. -/
def binaryT3DoubleRoundingExtendedFormat : FloatingPointFormat where
  beta := 2
  t := 3
  emin := 1
  emax := 1
  beta_ge_two := by norm_num
  t_pos := by norm_num
  emin_le_emax := by norm_num

/-- In the extended `t = 3` format, `21/16` lies between `5/4` and `3/2` and is
strictly closer to `5/4`. -/
theorem binaryT3DoubleRounding_rounds_21_16_to_5_4 :
    binaryT3DoubleRoundingExtendedFormat.finiteRoundToEven (21 / 16 : ℝ) =
      (5 / 4 : ℝ) := by
  let fmt := binaryT3DoubleRoundingExtendedFormat
  let a : ℝ := fmt.normalizedValue false 5 1
  let b : ℝ := fmt.normalizedValue false 6 1
  let x : ℝ := (21 / 16 : ℝ)
  have hm : fmt.normalizedMantissa 5 := by
    norm_num [fmt, binaryT3DoubleRoundingExtendedFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (5 + 1) := by
    norm_num [fmt, binaryT3DoubleRoundingExtendedFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 5, (1 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have hstrict : a < x ∧ x < b := by
    norm_num [x, a, b, fmt, binaryT3DoubleRoundingExtendedFormat,
      normalizedValue, signValue, betaR]
  have hxrange : fmt.finiteNormalRange x := by
    rw [finiteNormalRange]
    have hxnonneg : 0 ≤ x := by norm_num [x]
    rw [abs_of_nonneg hxnonneg]
    constructor
    · norm_num [x, fmt, binaryT3DoubleRoundingExtendedFormat,
        minNormalMagnitude, betaR]
    · have hmax : fmt.maxFiniteMagnitude = (7 / 4 : ℝ) := by
        norm_num [fmt, binaryT3DoubleRoundingExtendedFormat,
          maxFiniteMagnitude, betaR]
      simpa [x, hmax] using (by norm_num : (21 / 16 : ℝ) ≤ 7 / 4)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    norm_num [x, a, b, fmt, binaryT3DoubleRoundingExtendedFormat,
      normalizedValue, signValue, betaR]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  have ha : a = (5 / 4 : ℝ) := by
    norm_num [a, fmt, binaryT3DoubleRoundingExtendedFormat,
      normalizedValue, signValue, betaR]
  simpa [x, fmt, ha] using hround

/-- In the destination `t = 2` format, `5/4` is exactly midway between `1` and
`3/2`; round-to-even selects the left endpoint because mantissa `2` is even. -/
theorem binaryT2DoubleRounding_rounds_5_4_to_1 :
    binaryT2DoubleRoundingDestinationFormat.finiteRoundToEven (5 / 4 : ℝ) =
      (1 : ℝ) := by
  let fmt := binaryT2DoubleRoundingDestinationFormat
  let a : ℝ := fmt.normalizedValue false 2 1
  let b : ℝ := fmt.normalizedValue false 3 1
  let x : ℝ := (5 / 4 : ℝ)
  have hm : fmt.normalizedMantissa 2 := by
    norm_num [fmt, binaryT2DoubleRoundingDestinationFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (2 + 1) := by
    norm_num [fmt, binaryT2DoubleRoundingDestinationFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 2, (1 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value : a = (1 : ℝ) := by
    norm_num [a, fmt, binaryT2DoubleRoundingDestinationFormat,
      normalizedValue, signValue, betaR]
    rfl
  have hb_value : b = (3 / 2 : ℝ) := by
    norm_num [b, fmt, binaryT2DoubleRoundingDestinationFormat,
      normalizedValue, signValue, betaR]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x]
  have hxrange : fmt.finiteNormalRange x := by
    rw [finiteNormalRange]
    have hxnonneg : 0 ≤ x := by norm_num [x]
    rw [abs_of_nonneg hxnonneg]
    constructor
    · norm_num [x, fmt, binaryT2DoubleRoundingDestinationFormat,
        minNormalMagnitude, betaR]
    · have hmax : fmt.maxFiniteMagnitude = (3 / 2 : ℝ) := by
        norm_num [fmt, binaryT2DoubleRoundingDestinationFormat,
          maxFiniteMagnitude, betaR]
      simpa [x, hmax] using (by norm_num : (5 / 4 : ℝ) ≤ 3 / 2)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleft : a = fmt.normalizedValue false 2 (1 : ℤ) := rfl
  have htie : |x - a| = |x - b| := by
    rw [ha_value, hb_value]
    norm_num [x]
  have heven : evenMantissa 2 := by
    norm_num [evenMantissa]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_tie_even
      hpolicy hadj hstrict hm hleft htie heven
  have ha : a = (1 : ℝ) := by
    exact ha_value
  simpa [x, fmt, ha] using hround

/-- Direct destination rounding of `21/16` gives `3/2`, because it is closer to
`3/2` than to `1`. -/
theorem binaryT2DoubleRounding_rounds_21_16_to_3_2 :
    binaryT2DoubleRoundingDestinationFormat.finiteRoundToEven (21 / 16 : ℝ) =
      (3 / 2 : ℝ) := by
  let fmt := binaryT2DoubleRoundingDestinationFormat
  let a : ℝ := fmt.normalizedValue false 2 1
  let b : ℝ := fmt.normalizedValue false 3 1
  let x : ℝ := (21 / 16 : ℝ)
  have hm : fmt.normalizedMantissa 2 := by
    norm_num [fmt, binaryT2DoubleRoundingDestinationFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (2 + 1) := by
    norm_num [fmt, binaryT2DoubleRoundingDestinationFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 2, (1 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value : a = (1 : ℝ) := by
    norm_num [a, fmt, binaryT2DoubleRoundingDestinationFormat,
      normalizedValue, signValue, betaR]
    rfl
  have hb_value : b = (3 / 2 : ℝ) := by
    norm_num [b, fmt, binaryT2DoubleRoundingDestinationFormat,
      normalizedValue, signValue, betaR]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x]
  have hxrange : fmt.finiteNormalRange x := by
    rw [finiteNormalRange]
    have hxnonneg : 0 ≤ x := by norm_num [x]
    rw [abs_of_nonneg hxnonneg]
    constructor
    · norm_num [x, fmt, binaryT2DoubleRoundingDestinationFormat,
        minNormalMagnitude, betaR]
    · have hmax : fmt.maxFiniteMagnitude = (3 / 2 : ℝ) := by
        norm_num [fmt, binaryT2DoubleRoundingDestinationFormat,
          maxFiniteMagnitude, betaR]
      simpa [x, hmax] using (by norm_num : (21 / 16 : ℝ) ≤ 3 / 2)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value]
    norm_num [x]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  have hb : b = (3 / 2 : ℝ) := by
    exact hb_value
  simpa [x, fmt, hb] using hround

/-- Concrete double-rounding counterexample: rounding `21/16` through the
extended `t = 3` format and then to the destination `t = 2` format gives `1`,
whereas direct destination rounding gives `3/2`. -/
theorem binaryDoubleRounding_counterexample :
    binaryT2DoubleRoundingDestinationFormat.finiteRoundToEven
        (binaryT3DoubleRoundingExtendedFormat.finiteRoundToEven (21 / 16 : ℝ)) ≠
      binaryT2DoubleRoundingDestinationFormat.finiteRoundToEven (21 / 16 : ℝ) := by
  rw [binaryT3DoubleRounding_rounds_21_16_to_5_4,
    binaryT2DoubleRounding_rounds_5_4_to_1,
    binaryT2DoubleRounding_rounds_21_16_to_3_2]
  norm_num

/-- The tiny `t = 2` destination format does not contain `-3/16`. -/
theorem binaryT2DoubleRounding_neg_three_sixteenths_not_finiteSystem :
    ¬ binaryT2DoubleRoundingDestinationFormat.finiteSystem (-3 / 16 : ℝ) := by
  intro hfin
  have hnonzero : (-3 / 16 : ℝ) ≠ 0 := by norm_num
  have hfloor :=
    binaryT2DoubleRoundingDestinationFormat.finiteSystem_ne_zero_abs_ge_minSubnormalMagnitude
      hfin hnonzero
  norm_num [binaryT2DoubleRoundingDestinationFormat, minSubnormalMagnitude,
    betaR] at hfloor

/-- The direct `t = 2` rounding error for `21/16` is not representable in the
destination finite system. -/
theorem binaryT2DoubleRounding_roundoff_error_not_finiteSystem :
    ¬ binaryT2DoubleRoundingDestinationFormat.finiteSystem
        ((21 / 16 : ℝ) -
          binaryT2DoubleRoundingDestinationFormat.finiteRoundToEven (21 / 16 : ℝ)) := by
  rw [binaryT2DoubleRounding_rounds_21_16_to_3_2]
  rw [show (21 / 16 : ℝ) - (3 / 2 : ℝ) = -3 / 16 by norm_num]
  exact binaryT2DoubleRounding_neg_three_sixteenths_not_finiteSystem

/-- The source value `21/16` lies inside the finite-normal source range of the
tiny `t = 2` destination format. -/
theorem binaryT2DoubleRounding_21_16_finiteNormalRange :
    binaryT2DoubleRoundingDestinationFormat.finiteNormalRange (21 / 16 : ℝ) := by
  rw [finiteNormalRange]
  have hxnonneg : 0 ≤ (21 / 16 : ℝ) := by norm_num
  rw [abs_of_nonneg hxnonneg]
  constructor
  · norm_num [binaryT2DoubleRoundingDestinationFormat, minNormalMagnitude,
      betaR]
  · have hmax :
        binaryT2DoubleRoundingDestinationFormat.maxFiniteMagnitude =
          (3 / 2 : ℝ) := by
      norm_num [binaryT2DoubleRoundingDestinationFormat, maxFiniteMagnitude,
        betaR]
    simpa [hmax] using (by norm_num : (21 / 16 : ℝ) ≤ 3 / 2)

/-- Finite-normal range and binary round-to-even alone do not imply that the
real roundoff error is finite representable.  The missing Chapter 4 FastTwoSum
dependency must use that the rounded source is the exact sum of finite binary
operands, not just an arbitrary in-range real. -/
theorem finiteNormalRange_not_enough_for_roundoff_error_finiteSystem :
    ∃ fmt : FloatingPointFormat, ∃ x : ℝ,
      fmt.beta = 2 ∧ fmt.finiteNormalRange x ∧
        ¬ fmt.finiteSystem (x - fmt.finiteRoundToEven x) := by
  refine ⟨binaryT2DoubleRoundingDestinationFormat, (21 / 16 : ℝ), ?_, ?_, ?_⟩
  · rfl
  · exact binaryT2DoubleRounding_21_16_finiteNormalRange
  · simpa using binaryT2DoubleRounding_roundoff_error_not_finiteSystem

/-! ## Higham Problem 2.9: `sqrt (1 - 2^-53)` -/

/-- A local binary extended format with a 64-bit mantissa.  The exponent range
is restricted to the neighborhood of `1`, which is the only range used by
Problem 2.9's `sqrt (1 - 2^-53)` example. -/
def binary64MantissaExtendedLocalFormat : FloatingPointFormat where
  beta := 2
  t := 64
  emin := 0
  emax := 1
  beta_ge_two := by norm_num
  t_pos := by norm_num
  emin_le_emax := by norm_num

/-- The exact real value in Higham Problem 2.9. -/
noncomputable def problem2_9Source : ℝ :=
  Real.sqrt (1 - (2 : ℝ) ^ (-53 : ℤ))

private theorem problem2_9_double_predecessor_lt_source :
    (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) < problem2_9Source := by
  rw [problem2_9Source]
  have hp : 0 ≤ (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [zpow_neg]
  rw [Real.lt_sqrt hp]
  norm_num [zpow_neg]

private theorem problem2_9_source_lt_one :
    problem2_9Source < (1 : ℝ) := by
  rw [problem2_9Source]
  have hx : 0 ≤ (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [zpow_neg]
  have hy : 0 ≤ (1 : ℝ) := by norm_num
  rw [Real.sqrt_lt hx hy]
  norm_num [zpow_neg]

private theorem problem2_9_source_lt_double_midpoint :
    problem2_9Source < (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) := by
  rw [problem2_9Source]
  have hx : 0 ≤ (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [zpow_neg]
  have hy : 0 ≤ (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) := by
    norm_num [zpow_neg]
  rw [Real.sqrt_lt hx hy]
  norm_num [zpow_neg]

private theorem problem2_9_extended_half_ulp_below_midpoint_lt_source :
    (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) - (2 : ℝ) ^ (-65 : ℤ) <
      problem2_9Source := by
  rw [problem2_9Source]
  have hp :
      0 ≤ (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) - (2 : ℝ) ^ (-65 : ℤ) := by
    norm_num [zpow_neg]
  rw [Real.lt_sqrt hp]
  norm_num [zpow_neg]

private theorem ieeeDoubleFormat_minNormalMagnitude_le_half :
    ieeeDoubleFormat.minNormalMagnitude ≤ (1 / 2 : ℝ) := by
  rw [minNormalMagnitude, ieeeDoubleFormat, betaR]
  norm_num
  have hden : (2 : ℝ) ≤ (2 : ℝ) ^ (1022 : ℕ) := by
    exact le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (1022 : ℕ) ≠ 0)
  simpa [one_div] using
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hden

private theorem one_le_ieeeDoubleFormat_maxFiniteMagnitude :
    (1 : ℝ) ≤ ieeeDoubleFormat.maxFiniteMagnitude := by
  rw [maxFiniteMagnitude, ieeeDoubleFormat, betaR]
  change (1 : ℝ) ≤ (2 : ℝ) ^ (1024 : ℤ) *
    (1 - (2 : ℝ) ^ (-53 : ℤ))
  have hfactor : (1 / 2 : ℝ) ≤ 1 - (2 : ℝ) ^ (-53 : ℤ) := by
    rw [zpow_neg]
    have hden : (2 : ℝ) ≤ (2 : ℝ) ^ (53 : ℕ) := by
      exact le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (53 : ℕ) ≠ 0)
    have hinv : 1 / ((2 : ℝ) ^ (53 : ℕ)) ≤ 1 / (2 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hden
    norm_num at hinv ⊢
  have hpow_nat : (2 : ℝ) ≤ (2 : ℝ) ^ (1024 : ℕ) := by
    exact le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (1024 : ℕ) ≠ 0)
  have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ (1024 : ℤ) := by
    simpa [zpow_natCast] using hpow_nat
  have hmul := mul_le_mul hpow hfactor
    (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
    (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (1024 : ℤ))
  simpa using hmul

private theorem problem2_9Source_ieeeDoubleFormat_finiteNormalRange :
    ieeeDoubleFormat.finiteNormalRange problem2_9Source := by
  rw [finiteNormalRange]
  have hxnonneg : 0 ≤ problem2_9Source := by
    rw [problem2_9Source]
    exact Real.sqrt_nonneg _
  rw [abs_of_nonneg hxnonneg]
  constructor
  · have hhalf_le : (1 / 2 : ℝ) ≤ problem2_9Source := by
      have hpre : (1 / 2 : ℝ) ≤ 1 - (2 : ℝ) ^ (-53 : ℤ) := by
        norm_num [zpow_neg]
      exact le_trans hpre (le_of_lt problem2_9_double_predecessor_lt_source)
    exact le_trans ieeeDoubleFormat_minNormalMagnitude_le_half hhalf_le
  · exact le_trans (le_of_lt problem2_9_source_lt_one)
      one_le_ieeeDoubleFormat_maxFiniteMagnitude

private theorem problem2_9DoubleMidpoint_ieeeDoubleFormat_finiteNormalRange :
    ieeeDoubleFormat.finiteNormalRange
      ((1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ)) := by
  rw [finiteNormalRange]
  have hxnonneg : 0 ≤ (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) := by
    norm_num [zpow_neg]
  rw [abs_of_nonneg hxnonneg]
  constructor
  · have hhalf_le : (1 / 2 : ℝ) ≤ (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) := by
      norm_num [zpow_neg]
    exact le_trans ieeeDoubleFormat_minNormalMagnitude_le_half hhalf_le
  · have hxle : (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) ≤ 1 := by
      norm_num [zpow_neg]
    exact le_trans hxle one_le_ieeeDoubleFormat_maxFiniteMagnitude

private theorem problem2_9Source_binary64MantissaExtendedLocalFormat_finiteNormalRange :
    binary64MantissaExtendedLocalFormat.finiteNormalRange problem2_9Source := by
  let fmt := binary64MantissaExtendedLocalFormat
  rw [finiteNormalRange]
  have hxnonneg : 0 ≤ problem2_9Source := by
    rw [problem2_9Source]
    exact Real.sqrt_nonneg _
  rw [abs_of_nonneg hxnonneg]
  constructor
  · have hmin : fmt.minNormalMagnitude = (1 / 2 : ℝ) := by
      norm_num [fmt, binary64MantissaExtendedLocalFormat, minNormalMagnitude, betaR]
    rw [hmin]
    have hpre : (1 / 2 : ℝ) ≤ 1 - (2 : ℝ) ^ (-53 : ℤ) := by
      norm_num [zpow_neg]
    exact le_trans hpre (le_of_lt problem2_9_double_predecessor_lt_source)
  · have hmax : (1 : ℝ) ≤ fmt.maxFiniteMagnitude := by
      norm_num [fmt, binary64MantissaExtendedLocalFormat, maxFiniteMagnitude,
        betaR, zpow_neg]
    exact le_trans (le_of_lt problem2_9_source_lt_one) hmax

/-- Direct IEEE-double finite round-to-even evaluation of Problem 2.9's exact
square-root value gives the predecessor of `1`. -/
theorem problem2_9_direct_double_rounds_to_predecessor :
    ieeeDoubleFormat.finiteRoundToEven problem2_9Source =
      (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) := by
  let fmt := ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false fmt.maxNormalMantissa 0
  let b : ℝ := fmt.normalizedValue false fmt.minNormalMantissa 1
  let x : ℝ := problem2_9Source
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨false, (0 : ℤ), Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [a, fmt, ieeeDoubleFormat, normalizedValue, signValue, betaR,
      maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) := by
    norm_num [b, fmt, ieeeDoubleFormat, normalizedValue, signValue, betaR,
      minNormalMantissa, zpow_neg]
    rfl
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    exact ⟨problem2_9_double_predecessor_lt_source, problem2_9_source_lt_one⟩
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      problem2_9Source_ieeeDoubleFormat_finiteNormalRange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value]
    have hxa : 0 ≤ x - ((1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ)) := by
      exact sub_nonneg.mpr (le_of_lt problem2_9_double_predecessor_lt_source)
    have hxb : x - (1 : ℝ) < 0 := by
      exact sub_neg.mpr problem2_9_source_lt_one
    rw [abs_of_nonneg hxa, abs_of_neg hxb]
    have hmid := problem2_9_source_lt_double_midpoint
    norm_num [x, zpow_neg] at hmid ⊢
    linarith
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [x, fmt, ha_value] using hround

/-- The operation-level finite double square-root wrapper has the same direct
Problem 2.9 result. -/
theorem problem2_9_direct_double_sqrt_rounds_to_predecessor :
    ieeeDoubleFormat.finiteRoundToEvenSqrt
        (1 - (2 : ℝ) ^ (-53 : ℤ)) =
      (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) := by
  simpa [finiteRoundToEvenSqrt, problem2_9Source] using
    problem2_9_direct_double_rounds_to_predecessor

/-- First rounding Problem 2.9's exact value to a 64-bit-mantissa extended
format gives the double midpoint `1 - 2^-54`. -/
theorem problem2_9_extended64_rounds_to_double_midpoint :
    binary64MantissaExtendedLocalFormat.finiteRoundToEven problem2_9Source =
      (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) := by
  let fmt := binary64MantissaExtendedLocalFormat
  let m : ℕ := 2 ^ 64 - 2 ^ 10 - 1
  let a : ℝ := fmt.normalizedValue false m 0
  let b : ℝ := fmt.normalizedValue false (m + 1) 0
  let x : ℝ := problem2_9Source
  have hm : fmt.normalizedMantissa m := by
    norm_num [m, fmt, binary64MantissaExtendedLocalFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (m + 1) := by
    norm_num [m, fmt, binary64MantissaExtendedLocalFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, m, (0 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value :
      a = (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) - (2 : ℝ) ^ (-64 : ℤ) := by
    norm_num [a, m, fmt, binary64MantissaExtendedLocalFormat, normalizedValue,
      signValue, betaR, zpow_neg]
  have hb_value : b = (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) := by
    norm_num [b, m, fmt, binary64MantissaExtendedLocalFormat, normalizedValue,
      signValue, betaR, zpow_neg]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    constructor
    · have hlow :
          (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) - (2 : ℝ) ^ (-64 : ℤ) <
            (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) - (2 : ℝ) ^ (-65 : ℤ) := by
        norm_num [zpow_neg]
      exact lt_trans hlow problem2_9_extended_half_ulp_below_midpoint_lt_source
    · exact problem2_9_source_lt_double_midpoint
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      problem2_9Source_binary64MantissaExtendedLocalFormat_finiteNormalRange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value]
    have hxb : x - ((1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ)) < 0 := by
      exact sub_neg.mpr problem2_9_source_lt_double_midpoint
    have hxa :
        0 ≤ x -
          ((1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) - (2 : ℝ) ^ (-64 : ℤ)) := by
      have hax :
          (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) - (2 : ℝ) ^ (-64 : ℤ) < x := by
        simpa [ha_value] using hstrict.1
      exact sub_nonneg.mpr (le_of_lt hax)
    rw [abs_of_neg hxb, abs_of_nonneg hxa]
    have hmid := problem2_9_extended_half_ulp_below_midpoint_lt_source
    norm_num [x, zpow_neg] at hmid ⊢
    linarith
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  simpa [x, fmt, hb_value] using hround

/-- Rounding the 64-bit-mantissa midpoint to IEEE double ties to the even
endpoint `1`. -/
theorem problem2_9_double_rounds_extended_midpoint_to_one :
    ieeeDoubleFormat.finiteRoundToEven
        ((1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ)) = (1 : ℝ) := by
  let fmt := ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false fmt.maxNormalMantissa 0
  let b : ℝ := fmt.normalizedValue false fmt.minNormalMantissa 1
  let x : ℝ := (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ)
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨false, (0 : ℤ), Or.inl ⟨rfl, ?_⟩⟩
    norm_num [b]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have ha_value : a = (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [a, fmt, ieeeDoubleFormat, normalizedValue, signValue, betaR,
      maxNormalMantissa, zpow_neg]
  have hb_value : b = (1 : ℝ) := by
    norm_num [b, fmt, ieeeDoubleFormat, normalizedValue, signValue, betaR,
      minNormalMantissa, zpow_neg]
    rfl
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      problem2_9DoubleMidpoint_ieeeDoubleFormat_finiteNormalRange
  have hleft : a = fmt.normalizedValue false fmt.maxNormalMantissa (0 : ℤ) := rfl
  have htie : |x - a| = |x - b| := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hodd : ¬ evenMantissa fmt.maxNormalMantissa := by
    norm_num [fmt, ieeeDoubleFormat, maxNormalMantissa, evenMantissa]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict (fmt.maxNormalMantissa_normalized) hleft htie hodd
  simpa [x, fmt, hb_value] using hround

/-- Problem 2.9 with double rounding from the local 64-bit-mantissa extended
format returns `1`. -/
theorem problem2_9_double_rounding_from_extended64 :
    ieeeDoubleFormat.finiteRoundToEven
        (binary64MantissaExtendedLocalFormat.finiteRoundToEven problem2_9Source) =
      (1 : ℝ) := by
  rw [problem2_9_extended64_rounds_to_double_midpoint,
    problem2_9_double_rounds_extended_midpoint_to_one]

/-- Problem 2.9's direct double result differs from the result obtained by
first rounding to a 64-bit-mantissa extended format and then to double. -/
theorem problem2_9_direct_double_ne_double_rounded_extended64 :
    ieeeDoubleFormat.finiteRoundToEven problem2_9Source ≠
      ieeeDoubleFormat.finiteRoundToEven
        (binary64MantissaExtendedLocalFormat.finiteRoundToEven problem2_9Source) := by
  rw [problem2_9_direct_double_rounds_to_predecessor,
    problem2_9_double_rounding_from_extended64]
  norm_num [zpow_neg]

end FloatingPointFormat

end

end NumStability
