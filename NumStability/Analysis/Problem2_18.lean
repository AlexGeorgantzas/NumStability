-- Analysis/Problem2_18.lean
--
-- Problem-specific theorem surface for Higham Chapter 2, Problem 2.18.

import NumStability.Analysis.Nonassociativity

namespace NumStability

noncomputable section

/-!
# Higham Chapter 2, Problem 2.18

Problem 2.18 asks whether Higham Theorem 2.4 can be strengthened by replacing
Ferguson's cancellation exponent condition with the simpler hypothesis that the
positive operands' exponents differ by at most one.  The answer is no.

The counterexample below uses the existing one-digit decimal format with
exponents `1` and `2`: `20` and `1` are positive normalized floating-point
numbers with exponents differing by exactly one, and the exact difference `19`
is in the normal range but is not a one-digit decimal number.  The finite
round-to-even operation therefore returns `20`, not `19`.
-/

/-- Problem 2.18's proposed replacement condition: positive normalized operands
whose carried exponents differ by at most one. -/
def problem2_18_positiveExponentGapAtMostOne
    (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  0 < x ∧ 0 < y ∧
    ∃ ex ey : ℤ,
      fmt.normalizedExponentRepresentation x ex ∧
      fmt.normalizedExponentRepresentation y ey ∧
      ex ≤ ey + 1 ∧ ey ≤ ex + 1

theorem problem2_18_decimalOneDigitTwoExponentFormat_normalizedExponentRepresentation_one :
    FloatingPointFormat.normalizedExponentRepresentation
      FloatingPointFormat.decimalOneDigitTwoExponentFormat (1 : ℝ) 1 := by
  refine ⟨false, 1, ?_, ?_, ?_⟩
  · norm_num [FloatingPointFormat.decimalOneDigitTwoExponentFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [FloatingPointFormat.decimalOneDigitTwoExponentFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [FloatingPointFormat.decimalOneDigitTwoExponentFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]

theorem problem2_18_twenty_one_exponent_gap :
    problem2_18_positiveExponentGapAtMostOne
      FloatingPointFormat.decimalOneDigitTwoExponentFormat (20 : ℝ) 1 := by
  refine ⟨by norm_num, by norm_num, 2, 1, ?_, ?_, by norm_num, by norm_num⟩
  · exact
      FloatingPointFormat.decimalOneDigitTwoExponentFormat_normalizedExponentRepresentation_twenty
  · exact
      problem2_18_decimalOneDigitTwoExponentFormat_normalizedExponentRepresentation_one

theorem problem2_18_nineteen_finiteNormalRange :
    FloatingPointFormat.finiteNormalRange
      FloatingPointFormat.decimalOneDigitTwoExponentFormat (19 : ℝ) := by
  rw [FloatingPointFormat.finiteNormalRange]
  have hnonneg : 0 ≤ (19 : ℝ) := by norm_num
  rw [abs_of_nonneg hnonneg]
  constructor
  · norm_num [FloatingPointFormat.decimalOneDigitTwoExponentFormat,
      FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR]
  · have hmax :
        FloatingPointFormat.decimalOneDigitTwoExponentFormat.maxFiniteMagnitude =
          (90 : ℝ) := by
      norm_num [FloatingPointFormat.decimalOneDigitTwoExponentFormat,
        FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR]
      rfl
    simpa [hmax] using (by norm_num : (19 : ℝ) ≤ 90)

/-- In the one-digit decimal format, `20 - 1` rounds to `20`, because the exact
result `19` lies strictly between the adjacent finite values `10` and `20` and
is closer to `20`. -/
theorem problem2_18_sub_twenty_one_rounds_to_twenty :
    FloatingPointFormat.finiteRoundToEvenOp
      FloatingPointFormat.decimalOneDigitTwoExponentFormat
      BasicOp.sub (20 : ℝ) 1 = 20 := by
  let fmt := FloatingPointFormat.decimalOneDigitTwoExponentFormat
  let a : ℝ := fmt.normalizedValue false 1 2
  let b : ℝ := fmt.normalizedValue false 2 2
  let x : ℝ := (19 : ℝ)
  have hm : fmt.normalizedMantissa 1 := by
    norm_num [fmt, FloatingPointFormat.decimalOneDigitTwoExponentFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (1 + 1) := by
    norm_num [fmt, FloatingPointFormat.decimalOneDigitTwoExponentFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 1, (2 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have hstrict : a < x ∧ x < b := by
    norm_num [x, a, b, fmt,
      FloatingPointFormat.decimalOneDigitTwoExponentFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
  have hxrange : fmt.finiteNormalRange x := by
    simpa [fmt, x] using problem2_18_nineteen_finiteNormalRange
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hrightCloser : |x - b| < |x - a| := by
    norm_num [x, a, b, fmt,
      FloatingPointFormat.decimalOneDigitTwoExponentFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    change (1 : ℝ) < |(9 : ℝ)|
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 9)]
    norm_num
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  have htarget : fmt.finiteRoundToEven ((20 : ℝ) - 1) = b := by
    have hxsub : ((20 : ℝ) - 1) = x := by norm_num [x]
    rw [hxsub]
    exact hround
  have hb : b = (20 : ℝ) := by
    norm_num [b, fmt, FloatingPointFormat.decimalOneDigitTwoExponentFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
  simpa [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact, hb] using
    htarget

theorem problem2_18_nineteen_not_finiteSystem :
    ¬ FloatingPointFormat.finiteSystem
      FloatingPointFormat.decimalOneDigitTwoExponentFormat (19 : ℝ) := by
  intro hfinite
  have hself :
      FloatingPointFormat.finiteRoundToEven
        FloatingPointFormat.decimalOneDigitTwoExponentFormat (19 : ℝ) = 19 :=
    FloatingPointFormat.finiteRoundToEven_eq_self_of_finiteSystem hfinite
  have hround :
      FloatingPointFormat.finiteRoundToEven
        FloatingPointFormat.decimalOneDigitTwoExponentFormat (19 : ℝ) = 20 := by
    have hround' :
        FloatingPointFormat.finiteRoundToEven
          FloatingPointFormat.decimalOneDigitTwoExponentFormat ((20 : ℝ) - 1) =
            20 := by
      simpa [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact] using
        problem2_18_sub_twenty_one_rounds_to_twenty
    norm_num at hround'
    exact hround'
  linarith

theorem problem2_18_source_counterexample_exact_values :
    ∃ fmt : FloatingPointFormat, ∃ x y : ℝ,
      problem2_18_positiveExponentGapAtMostOne fmt x y ∧
        x - y = 19 ∧
        fmt.finiteNormalRange (x - y) ∧
        ¬ fmt.finiteSystem (x - y) ∧
        fmt.finiteRoundToEvenOp BasicOp.sub x y = 20 ∧
        fmt.finiteRoundToEvenOp BasicOp.sub x y ≠ x - y := by
  refine
    ⟨FloatingPointFormat.decimalOneDigitTwoExponentFormat, 20, 1,
      problem2_18_twenty_one_exponent_gap, by norm_num, ?_, ?_, ?_, ?_⟩
  · have hdiff : ((20 : ℝ) - 1) = 19 := by norm_num
    rw [hdiff]
    exact problem2_18_nineteen_finiteNormalRange
  · have hdiff : ((20 : ℝ) - 1) = 19 := by norm_num
    rw [hdiff]
    exact problem2_18_nineteen_not_finiteSystem
  · exact problem2_18_sub_twenty_one_rounds_to_twenty
  · rw [problem2_18_sub_twenty_one_rounds_to_twenty]
    intro h
    linarith

/-- The proposed Problem 2.18 strengthening is false for the source-facing
finite operation model: positivity plus exponent gap at most one does not force
`fl(x-y) = x-y`, even when the exact difference is a normal-range real number. -/
theorem problem2_18_exponent_gap_not_sufficient_for_exact_subtraction :
    ∃ fmt : FloatingPointFormat, ∃ x y : ℝ,
      problem2_18_positiveExponentGapAtMostOne fmt x y ∧
        fmt.finiteNormalRange (x - y) ∧
        ¬ fmt.finiteSystem (x - y) ∧
        fmt.finiteRoundToEvenOp BasicOp.sub x y ≠ x - y := by
  refine
    ⟨FloatingPointFormat.decimalOneDigitTwoExponentFormat, 20, 1,
      problem2_18_twenty_one_exponent_gap, ?_, ?_, ?_⟩
  · have hdiff : ((20 : ℝ) - 1) = 19 := by norm_num
    rw [hdiff]
    exact problem2_18_nineteen_finiteNormalRange
  · have hdiff : ((20 : ℝ) - 1) = 19 := by norm_num
    rw [hdiff]
    exact problem2_18_nineteen_not_finiteSystem
  · rw [problem2_18_sub_twenty_one_rounds_to_twenty]
    intro h
    have hdiff : ((20 : ℝ) - 1) = 19 := by norm_num
    rw [hdiff] at h
    have hne : (20 : ℝ) ≠ 19 := by norm_num
    exact hne h

end

end NumStability
