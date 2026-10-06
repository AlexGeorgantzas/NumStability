import NumStability.Analysis.FloatingPointArithmetic.Format
import NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError
import NumStability.Analysis.FloatingPointArithmetic.Rounding

-- Analysis/DoubleRounding.lean
--
-- Concrete finite double-rounding example for Higham Chapter 2, §2.3 and
-- Problem 2.9.



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
































































/-! ## Higham Problem 2.9: `sqrt (1 - 2^-53)` -/



















































































































































































































































































































end FloatingPointFormat

end

end NumStability
