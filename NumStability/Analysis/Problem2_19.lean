-- Analysis/Problem2_19.lean
--
-- Problem-specific theorem surface for Higham Chapter 2, Problem 2.19.

import NumStability.Analysis.Midpoint

namespace NumStability

noncomputable section

/-!
# Higham Chapter 2, Problem 2.19

Problem 2.19 compares two possible requirements on a floating-point square-root
routine:

* `sqrt(x^2) = |x|`;
* `(sqrt x)^2 = |x|`.

The first is reasonable for a correctly rounded finite square-root selector
when the exact result `|x|` is representable: the exact real square root of
`x^2` is `|x|`, and finite round-to-even fixes representable exact results.
The second is too strong: a rounded square root need not square back to the
original input.  The one-digit decimal witness below has
`fl(sqrt(2)) = 1`, so the squared rounded-root path returns `1`, not `2`.
-/

namespace FloatingPointFormat

/-- Problem 2.19's reasonable identity at the finite round-to-even square-root
layer: if `x` is a finite floating-point value, then the square-root wrapper
returns `|x|` exactly on the exact square input `x^2`. -/
theorem problem2_19_sqrt_square_eq_abs_of_finiteSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x) :
    fmt.finiteRoundToEvenSqrt (x ^ 2) = |x| := by
  have hsqrt : Real.sqrt (x ^ 2) = |x| := by
    exact Real.sqrt_sq_eq_abs x
  have habs : fmt.finiteSystem |x| := by
    by_cases hx_nonneg : 0 ≤ x
    · simpa [abs_of_nonneg hx_nonneg] using hx
    · have hx_nonpos : x ≤ 0 := le_of_not_ge hx_nonneg
      have hneg : fmt.finiteSystem (-x) := fmt.finiteSystem_neg hx
      simpa [abs_of_nonpos hx_nonpos] using hneg
  have hround :
      fmt.finiteRoundToEvenSqrt (x ^ 2) = Real.sqrt (x ^ 2) :=
    fmt.finiteRoundToEvenSqrt_eq_exact_of_finiteSystem (x := x ^ 2)
      (by simpa [hsqrt] using habs)
  simpa [hsqrt] using hround

/-- The finite operation sequence that squares the rounded square-root result. -/
def problem2_19_roundedSqrtSquare (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  let y := fmt.finiteRoundToEvenSqrt x
  fmt.finiteRoundToEvenOp BasicOp.mul y y

/-- In the one-digit decimal format, the finite round-to-even square root of
`2` is `1`. -/
theorem problem2_19_decimalOneDigitThreeExponent_sqrt_two_rounds_to_one :
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenSqrt (2 : ℝ) = 1 := by
  let fmt := decimalOneDigitThreeExponentFormat
  let a : ℝ := fmt.normalizedValue false 1 1
  let b : ℝ := fmt.normalizedValue false 2 1
  let s : ℝ := Real.sqrt 2
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
  have hs_gt_one : (1 : ℝ) < s := by
    simpa [s] using
      (Real.lt_sqrt_of_sq_lt (by norm_num : (1 : ℝ) ^ 2 < 2))
  have hs_lt_two : s < (2 : ℝ) := by
    change Real.sqrt (2 : ℝ) < 2
    rw [Real.sqrt_lt (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hstrict : a < s ∧ s < b := by
    simpa [ha_value, hb_value] using ⟨hs_gt_one, hs_lt_two⟩
  have hsrange : fmt.finiteNormalRange s := by
    rw [finiteNormalRange]
    have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg 2
    rw [abs_of_nonneg hs_nonneg]
    constructor
    · have hmin : fmt.minNormalMagnitude = (1 / 10 : ℝ) := by
        norm_num [fmt, decimalOneDigitThreeExponentFormat,
          minNormalMagnitude, betaR]
      rw [hmin]
      linarith
    · have hmax : fmt.maxFiniteMagnitude = (90 : ℝ) := by
        norm_num [fmt, decimalOneDigitThreeExponentFormat,
          maxFiniteMagnitude, betaR]
        rfl
      rw [hmax]
      linarith
  have hpolicy :
      fmt.sourceRoundToEvenEvidence s (fmt.finiteRoundToEven s) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hsrange
  have hleftCloser : |s - a| < |s - b| := by
    rw [ha_value, hb_value]
    have hs_ge_one : (1 : ℝ) ≤ s := le_of_lt hs_gt_one
    have hs_le_two : s ≤ (2 : ℝ) := le_of_lt hs_lt_two
    rw [abs_of_nonneg (sub_nonneg.mpr hs_ge_one),
      abs_of_nonpos (sub_nonpos.mpr hs_le_two)]
    have hs_lt_three_halves : s < (3 / 2 : ℝ) := by
      change Real.sqrt (2 : ℝ) < 3 / 2
      rw [Real.sqrt_lt (by norm_num : (0 : ℝ) ≤ 2)
        (by norm_num : (0 : ℝ) ≤ 3 / 2)]
      norm_num
    linarith
  have hround : fmt.finiteRoundToEven s = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  have htarget : fmt.finiteRoundToEven (Real.sqrt (2 : ℝ)) = a := by
    simpa [s] using hround
  simpa [finiteRoundToEvenSqrt, a, fmt, decimalOneDigitThreeExponentFormat,
    normalizedValue, signValue, betaR] using htarget

/-- Squaring the rounded square root of `2` returns `1` in the one-digit
decimal format. -/
theorem problem2_19_decimalOneDigitThreeExponent_roundedSqrtSquare_two_eq_one :
    problem2_19_roundedSqrtSquare decimalOneDigitThreeExponentFormat
        (2 : ℝ) = 1 := by
  have hsqrt :=
    problem2_19_decimalOneDigitThreeExponent_sqrt_two_rounds_to_one
  have hfin :
      decimalOneDigitThreeExponentFormat.finiteSystem
        (BasicOp.exact BasicOp.mul (1 : ℝ) 1) := by
    norm_num [BasicOp.exact]
    exact decimalOneDigitThreeExponentFormat_finiteSystem_one
  have hmul :
      decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
        BasicOp.mul (1 : ℝ) 1 = 1 := by
    have h :=
      decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.mul) (x := (1 : ℝ)) (y := (1 : ℝ)) hfin
    simpa [BasicOp.exact] using h
  simp [problem2_19_roundedSqrtSquare, hsqrt, hmul]

/-- Problem 2.19's second displayed requirement is not reasonable at the finite
round-to-even layer: a rounded square root need not square back to `|x|`. -/
theorem problem2_19_roundedSqrtSquare_not_abs_counterexample :
    ∃ fmt : FloatingPointFormat, ∃ x : ℝ,
      fmt.finiteSystem x ∧
        problem2_19_roundedSqrtSquare fmt x ≠ |x| := by
  refine
    ⟨decimalOneDigitThreeExponentFormat, (2 : ℝ),
      decimalOneDigitThreeExponentFormat_finiteSystem_two, ?_⟩
  rw [problem2_19_decimalOneDigitThreeExponent_roundedSqrtSquare_two_eq_one]
  norm_num

theorem problem2_19_first_requirement_holds_second_fails :
    (∀ (fmt : FloatingPointFormat) (x : ℝ),
        fmt.finiteSystem x → fmt.finiteRoundToEvenSqrt (x ^ 2) = |x|) ∧
      ∃ fmt : FloatingPointFormat, ∃ x : ℝ,
        fmt.finiteSystem x ∧
          problem2_19_roundedSqrtSquare fmt x = 1 ∧
          |x| = 2 ∧
          problem2_19_roundedSqrtSquare fmt x ≠ |x| := by
  constructor
  · intro fmt x hx
    exact problem2_19_sqrt_square_eq_abs_of_finiteSystem hx
  · refine
      ⟨decimalOneDigitThreeExponentFormat, (2 : ℝ),
        decimalOneDigitThreeExponentFormat_finiteSystem_two,
        problem2_19_decimalOneDigitThreeExponent_roundedSqrtSquare_two_eq_one,
        by norm_num, ?_⟩
    rw [problem2_19_decimalOneDigitThreeExponent_roundedSqrtSquare_two_eq_one]
    norm_num

end FloatingPointFormat

end

end NumStability
