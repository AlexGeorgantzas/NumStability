import NumStability.Analysis.FloatingPointArithmetic.Format
import NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError
import NumStability.Analysis.FloatingPointArithmetic.RoundToEvenLocalError
import NumStability.Analysis.FloatingPointArithmetic.Rounding
import NumStability.Analysis.Nonassociativity
import NumStability.FloatingPoint.Model

-- Analysis/Midpoint.lean
--
-- Concrete midpoint-rounding examples for Higham Chapter 2, Problem 2.8.



namespace NumStability

noncomputable section

namespace FloatingPointFormat

/-!
# Midpoint Rounding

Higham Problem 2.8 asks for a base-10 violation of
`a < fl((a + b)/2) < b` with floating-point endpoints `a < b`.  The first
theorem below gives a minimal finite round-to-even witness in the existing
one-digit decimal format: `a = 1`, `b = 2`, and the exact midpoint `3/2` is a
tie whose left mantissa is odd, so round-to-even selects `2`.

The later counterexample audits the problem's second sentence.  It shows that
exact subtraction and exact division by `2` are still not enough for the naive
finite round-to-even operation-sequence interpretation of `fl(a + (b-a)/2)`;
the source guard-digit claim is therefore separated below into an exact-operation
model and corrected finite-selector side conditions.
-/

theorem decimalOneDigitTwoExponentFormat_normalizedExponentRepresentation_one :
    decimalOneDigitTwoExponentFormat.normalizedExponentRepresentation (1 : ℝ) 1 := by
  refine ⟨false, 1, ?_, ?_, ?_⟩
  · norm_num [decimalOneDigitTwoExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  · norm_num [decimalOneDigitTwoExponentFormat, exponentInRange]
  · norm_num [decimalOneDigitTwoExponentFormat, normalizedValue, signValue, betaR]

theorem decimalOneDigitTwoExponentFormat_normalizedExponentRepresentation_two :
    decimalOneDigitTwoExponentFormat.normalizedExponentRepresentation (2 : ℝ) 1 := by
  refine ⟨false, 2, ?_, ?_, ?_⟩
  · norm_num [decimalOneDigitTwoExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  · norm_num [decimalOneDigitTwoExponentFormat, exponentInRange]
  · norm_num [decimalOneDigitTwoExponentFormat, normalizedValue, signValue, betaR]

theorem decimalOneDigitTwoExponentFormat_finiteSystem_one :
    decimalOneDigitTwoExponentFormat.finiteSystem (1 : ℝ) :=
  Or.inr (Or.inl
    (decimalOneDigitTwoExponentFormat.normalizedExponentRepresentation_normalizedSystem
      decimalOneDigitTwoExponentFormat_normalizedExponentRepresentation_one))

theorem decimalOneDigitTwoExponentFormat_finiteSystem_two :
    decimalOneDigitTwoExponentFormat.finiteSystem (2 : ℝ) :=
  Or.inr (Or.inl
    (decimalOneDigitTwoExponentFormat.normalizedExponentRepresentation_normalizedSystem
      decimalOneDigitTwoExponentFormat_normalizedExponentRepresentation_two))

theorem decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_one_half :
    decimalOneDigitThreeExponentFormat.normalizedExponentRepresentation
      (1 / 2 : ℝ) 0 := by
  refine ⟨false, 5, ?_, ?_, ?_⟩
  · norm_num [decimalOneDigitThreeExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  · norm_num [decimalOneDigitThreeExponentFormat, exponentInRange]
  · norm_num [decimalOneDigitThreeExponentFormat, normalizedValue, signValue, betaR]

theorem decimalOneDigitThreeExponentFormat_finiteSystem_one_half :
    decimalOneDigitThreeExponentFormat.finiteSystem (1 / 2 : ℝ) :=
  Or.inr (Or.inl
    (decimalOneDigitThreeExponentFormat.normalizedExponentRepresentation_normalizedSystem
      decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_one_half))

theorem decimalOneDigitThreeExponentFormat_finiteSystem_two :
    decimalOneDigitThreeExponentFormat.finiteSystem (2 : ℝ) :=
  Or.inr (Or.inl
    (decimalOneDigitThreeExponentFormat.normalizedExponentRepresentation_normalizedSystem
      decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_two))

/-- In the one-digit decimal format, the exact midpoint of `1` and `2` rounds
to `2`; this is a tie and the left mantissa `1` is odd. -/
theorem decimalOneDigitTwoExponent_midpoint_one_two_rounds_to_two :
    decimalOneDigitTwoExponentFormat.finiteRoundToEven
        (((1 : ℝ) + 2) / 2) = 2 := by
  let fmt := decimalOneDigitTwoExponentFormat
  let a : ℝ := fmt.normalizedValue false 1 1
  let b : ℝ := fmt.normalizedValue false 2 1
  let x : ℝ := (3 / 2 : ℝ)
  have hm : fmt.normalizedMantissa 1 := by
    norm_num [fmt, decimalOneDigitTwoExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (1 + 1) := by
    norm_num [fmt, decimalOneDigitTwoExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 1, (1 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value : a = (1 : ℝ) := by
    norm_num [a, fmt, decimalOneDigitTwoExponentFormat,
      normalizedValue, signValue, betaR]
  have hb_value : b = (2 : ℝ) := by
    norm_num [b, fmt, decimalOneDigitTwoExponentFormat,
      normalizedValue, signValue, betaR]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x]
  have hxrange : fmt.finiteNormalRange x := by
    rw [finiteNormalRange]
    have hxnonneg : 0 ≤ x := by norm_num [x]
    rw [abs_of_nonneg hxnonneg]
    constructor
    · norm_num [x, fmt, decimalOneDigitTwoExponentFormat,
        minNormalMagnitude, betaR]
    · have hmax : fmt.maxFiniteMagnitude = 90 := by
        norm_num [fmt, decimalOneDigitTwoExponentFormat,
          maxFiniteMagnitude, betaR]
        rfl
      simpa [x, hmax] using (by norm_num : (3 / 2 : ℝ) ≤ 90)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleft : a = fmt.normalizedValue false 1 (1 : ℤ) := rfl
  have htie : |x - a| = |x - b| := by
    rw [ha_value, hb_value]
    norm_num [x]
  have hodd : ¬ evenMantissa 1 := by
    norm_num [evenMantissa]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict hm hleft htie hodd
  have hmid : (((1 : ℝ) + 2) / 2) = x := by norm_num [x]
  have htarget : fmt.finiteRoundToEven (((1 : ℝ) + 2) / 2) = b := by
    rw [hmid]
    exact hround
  simpa [fmt, hb_value] using htarget

/-- In the one-digit decimal format with exponent range including `1/2`, the
same exact midpoint `3/2` still rounds to `2`. -/
theorem decimalOneDigitThreeExponent_midpoint_one_two_rounds_to_two :
    decimalOneDigitThreeExponentFormat.finiteRoundToEven
        (((1 : ℝ) + 2) / 2) = 2 := by
  let fmt := decimalOneDigitThreeExponentFormat
  let a : ℝ := fmt.normalizedValue false 1 1
  let b : ℝ := fmt.normalizedValue false 2 1
  let x : ℝ := (3 / 2 : ℝ)
  have hm : fmt.normalizedMantissa 1 := by
    norm_num [fmt, decimalOneDigitThreeExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (1 + 1) := by
    norm_num [fmt, decimalOneDigitThreeExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 1, (1 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value : a = (1 : ℝ) := by
    norm_num [a, fmt, decimalOneDigitThreeExponentFormat,
      normalizedValue, signValue, betaR]
  have hb_value : b = (2 : ℝ) := by
    norm_num [b, fmt, decimalOneDigitThreeExponentFormat,
      normalizedValue, signValue, betaR]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x]
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
      simpa [x, hmax] using (by norm_num : (3 / 2 : ℝ) ≤ 90)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleft : a = fmt.normalizedValue false 1 (1 : ℤ) := rfl
  have htie : |x - a| = |x - b| := by
    rw [ha_value, hb_value]
    norm_num [x]
  have hodd : ¬ evenMantissa 1 := by
    norm_num [evenMantissa]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict hm hleft htie hodd
  have hmid : (((1 : ℝ) + 2) / 2) = x := by norm_num [x]
  have htarget : fmt.finiteRoundToEven (((1 : ℝ) + 2) / 2) = b := by
    rw [hmid]
    exact hround
  simpa [fmt, hb_value] using htarget

/-- In the one-digit decimal format used for the guarded-sequence audit,
the exact midpoint `3/2` is not itself a floating-point value. -/
theorem decimalOneDigitThreeExponentFormat_three_halves_not_finiteSystem :
    ¬ decimalOneDigitThreeExponentFormat.finiteSystem (3 / 2 : ℝ) := by
  intro hfin
  have hfix :
      decimalOneDigitThreeExponentFormat.finiteRoundToEven (3 / 2 : ℝ) =
        (3 / 2 : ℝ) :=
    decimalOneDigitThreeExponentFormat.finiteRoundToEven_eq_self_of_finiteSystem
      hfin
  have hround :
      decimalOneDigitThreeExponentFormat.finiteRoundToEven (3 / 2 : ℝ) =
        2 := by
    have h := decimalOneDigitThreeExponent_midpoint_one_two_rounds_to_two
    norm_num at h
    exact h
  rw [hround] at hfix
  norm_num at hfix

theorem decimalOneDigitThreeExponent_sub_two_one_exact :
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
        BasicOp.sub (2 : ℝ) 1 = 1 := by
  have hfin :
      decimalOneDigitThreeExponentFormat.finiteSystem
        (BasicOp.exact BasicOp.sub (2 : ℝ) 1) := by
    norm_num [BasicOp.exact]
    exact decimalOneDigitThreeExponentFormat_finiteSystem_one
  have hround :=
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (2 : ℝ)) (y := (1 : ℝ)) hfin
  change decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
      BasicOp.sub (2 : ℝ) 1 = (2 : ℝ) - 1 at hround
  norm_num at hround
  exact hround

theorem decimalOneDigitThreeExponent_div_one_two_exact :
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
        BasicOp.div (1 : ℝ) 2 = 1 / 2 := by
  have hfin :
      decimalOneDigitThreeExponentFormat.finiteSystem
        (BasicOp.exact BasicOp.div (1 : ℝ) 2) := by
    norm_num [BasicOp.exact]
    exact decimalOneDigitThreeExponentFormat_finiteSystem_one_half
  have hround :=
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.div) (x := (1 : ℝ)) (y := (2 : ℝ)) hfin
  change decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
      BasicOp.div (1 : ℝ) 2 = (1 : ℝ) / 2 at hround
  exact hround

theorem decimalOneDigitThreeExponent_add_one_one_half_rounds_to_two :
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
        BasicOp.add (1 : ℝ) (1 / 2) = 2 := by
  have harg : (1 : ℝ) + 1 / 2 = ((1 + 2) / 2 : ℝ) := by norm_num
  change decimalOneDigitThreeExponentFormat.finiteRoundToEven
      ((1 : ℝ) + 1 / 2) = 2
  rw [harg]
  exact decimalOneDigitThreeExponent_midpoint_one_two_rounds_to_two

/-- Audit counterexample for the naive finite round-to-even operation-sequence
reading of Problem 2.8's guard-digit midpoint sentence.  Even when the
subtraction `2-1` and division by `2` are exact in a base-10 finite format, the
final rounded addition can select the endpoint `2`, so the strict inequality is
not a consequence of exact subtraction alone. -/
theorem problem2_8_finiteRoundToEven_guarded_sequence_counterexample :
    decimalOneDigitThreeExponentFormat.finiteSystem (1 : ℝ) ∧
      decimalOneDigitThreeExponentFormat.finiteSystem (2 : ℝ) ∧
      (1 : ℝ) < 2 ∧
      decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
        BasicOp.sub (2 : ℝ) 1 = 1 ∧
      decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
        BasicOp.div (1 : ℝ) 2 = 1 / 2 ∧
      decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
        BasicOp.add (1 : ℝ) (1 / 2) = 2 ∧
      ¬ ((1 : ℝ) <
          decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
            BasicOp.add (1 : ℝ)
              (decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
                BasicOp.div
                  (decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
                    BasicOp.sub (2 : ℝ) 1)
                  2) ∧
        decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
            BasicOp.add (1 : ℝ)
              (decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
                BasicOp.div
                  (decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
                    BasicOp.sub (2 : ℝ) 1)
                  2) <
          (2 : ℝ)) := by
  refine ⟨decimalOneDigitThreeExponentFormat_finiteSystem_one,
    decimalOneDigitThreeExponentFormat_finiteSystem_two, by norm_num,
    decimalOneDigitThreeExponent_sub_two_one_exact,
    decimalOneDigitThreeExponent_div_one_two_exact,
    decimalOneDigitThreeExponent_add_one_one_half_rounds_to_two, ?_⟩
  rw [decimalOneDigitThreeExponent_sub_two_one_exact,
    decimalOneDigitThreeExponent_div_one_two_exact,
    decimalOneDigitThreeExponent_add_one_one_half_rounds_to_two]
  norm_num























































































































































end FloatingPointFormat

end

end NumStability
