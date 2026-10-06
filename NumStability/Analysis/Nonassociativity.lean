-- Analysis/Nonassociativity.lean
--
-- Concrete finite nonassociativity examples for Higham Chapter 2, §2.9.

import NumStability.Analysis.FloatingPointArithmetic

namespace NumStability

noncomputable section

namespace FloatingPointFormat

/-!
# Nonassociativity

Higham Chapter 2, §2.9 notes that rounded arithmetic is not associative.  This
file records concrete finite round-to-even addition and subtraction
counterexamples in a small decimal format.  The examples avoid overflow and
special values: the only non-exact steps are finite-normal roundings between
adjacent one-digit decimal values.
-/

/-- A tiny decimal finite format with one significant digit and exponents
`1` and `2`.  Positive normalized values are
`1,2,...,9,10,20,...,90`. -/
def decimalOneDigitTwoExponentFormat : FloatingPointFormat where
  beta := 10
  t := 1
  emin := 1
  emax := 2
  beta_ge_two := by norm_num
  t_pos := by norm_num
  emin_le_emax := by norm_num

theorem decimalOneDigitTwoExponentFormat_normalizedExponentRepresentation_four :
    decimalOneDigitTwoExponentFormat.normalizedExponentRepresentation (4 : ℝ) 1 := by
  refine ⟨false, 4, ?_, ?_, ?_⟩
  · norm_num [decimalOneDigitTwoExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  · norm_num [decimalOneDigitTwoExponentFormat, exponentInRange]
  · norm_num [decimalOneDigitTwoExponentFormat, normalizedValue, signValue, betaR]

theorem decimalOneDigitTwoExponentFormat_normalizedExponentRepresentation_neg_four :
    decimalOneDigitTwoExponentFormat.normalizedExponentRepresentation (-4 : ℝ) 1 := by
  refine ⟨true, 4, ?_, ?_, ?_⟩
  · norm_num [decimalOneDigitTwoExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  · norm_num [decimalOneDigitTwoExponentFormat, exponentInRange]
  · norm_num [decimalOneDigitTwoExponentFormat, normalizedValue, signValue, betaR]

theorem decimalOneDigitTwoExponentFormat_normalizedExponentRepresentation_six :
    decimalOneDigitTwoExponentFormat.normalizedExponentRepresentation (6 : ℝ) 1 := by
  refine ⟨false, 6, ?_, ?_, ?_⟩
  · norm_num [decimalOneDigitTwoExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  · norm_num [decimalOneDigitTwoExponentFormat, exponentInRange]
  · norm_num [decimalOneDigitTwoExponentFormat, normalizedValue, signValue, betaR]

theorem decimalOneDigitTwoExponentFormat_normalizedExponentRepresentation_neg_eight :
    decimalOneDigitTwoExponentFormat.normalizedExponentRepresentation (-8 : ℝ) 1 := by
  refine ⟨true, 8, ?_, ?_, ?_⟩
  · norm_num [decimalOneDigitTwoExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  · norm_num [decimalOneDigitTwoExponentFormat, exponentInRange]
  · norm_num [decimalOneDigitTwoExponentFormat, normalizedValue, signValue, betaR]

theorem decimalOneDigitTwoExponentFormat_normalizedExponentRepresentation_ten :
    decimalOneDigitTwoExponentFormat.normalizedExponentRepresentation (10 : ℝ) 2 := by
  refine ⟨false, 1, ?_, ?_, ?_⟩
  · norm_num [decimalOneDigitTwoExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  · norm_num [decimalOneDigitTwoExponentFormat, exponentInRange]
  · norm_num [decimalOneDigitTwoExponentFormat, normalizedValue, signValue, betaR]

theorem decimalOneDigitTwoExponentFormat_normalizedExponentRepresentation_twenty :
    decimalOneDigitTwoExponentFormat.normalizedExponentRepresentation (20 : ℝ) 2 := by
  refine ⟨false, 2, ?_, ?_, ?_⟩
  · norm_num [decimalOneDigitTwoExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  · norm_num [decimalOneDigitTwoExponentFormat, exponentInRange]
  · norm_num [decimalOneDigitTwoExponentFormat, normalizedValue, signValue, betaR]

theorem decimalOneDigitTwoExponentFormat_finiteSystem_four :
    decimalOneDigitTwoExponentFormat.finiteSystem (4 : ℝ) :=
  Or.inr (Or.inl
    (decimalOneDigitTwoExponentFormat.normalizedExponentRepresentation_normalizedSystem
      decimalOneDigitTwoExponentFormat_normalizedExponentRepresentation_four))

theorem decimalOneDigitTwoExponentFormat_finiteSystem_neg_four :
    decimalOneDigitTwoExponentFormat.finiteSystem (-4 : ℝ) :=
  Or.inr (Or.inl
    (decimalOneDigitTwoExponentFormat.normalizedExponentRepresentation_normalizedSystem
      decimalOneDigitTwoExponentFormat_normalizedExponentRepresentation_neg_four))

theorem decimalOneDigitTwoExponentFormat_finiteSystem_six :
    decimalOneDigitTwoExponentFormat.finiteSystem (6 : ℝ) :=
  Or.inr (Or.inl
    (decimalOneDigitTwoExponentFormat.normalizedExponentRepresentation_normalizedSystem
      decimalOneDigitTwoExponentFormat_normalizedExponentRepresentation_six))

theorem decimalOneDigitTwoExponentFormat_finiteSystem_neg_eight :
    decimalOneDigitTwoExponentFormat.finiteSystem (-8 : ℝ) :=
  Or.inr (Or.inl
    (decimalOneDigitTwoExponentFormat.normalizedExponentRepresentation_normalizedSystem
      decimalOneDigitTwoExponentFormat_normalizedExponentRepresentation_neg_eight))

theorem decimalOneDigitTwoExponentFormat_finiteSystem_ten :
    decimalOneDigitTwoExponentFormat.finiteSystem (10 : ℝ) :=
  Or.inr (Or.inl
    (decimalOneDigitTwoExponentFormat.normalizedExponentRepresentation_normalizedSystem
      decimalOneDigitTwoExponentFormat_normalizedExponentRepresentation_ten))

theorem decimalOneDigitTwoExponentFormat_finiteSystem_twenty :
    decimalOneDigitTwoExponentFormat.finiteSystem (20 : ℝ) :=
  Or.inr (Or.inl
    (decimalOneDigitTwoExponentFormat.normalizedExponentRepresentation_normalizedSystem
      decimalOneDigitTwoExponentFormat_normalizedExponentRepresentation_twenty))

/-- In the tiny decimal format, adding `10` and `4` forms exact `14`, whose
nearest one-digit decimal values at exponent `2` are `10` and `20`; it is
strictly closer to `10`. -/
theorem decimalOneDigitTwoExponent_add_ten_four_rounds_to_ten :
    decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp
        BasicOp.add (10 : ℝ) 4 = 10 := by
  let fmt := decimalOneDigitTwoExponentFormat
  let a : ℝ := fmt.normalizedValue false 1 2
  let b : ℝ := fmt.normalizedValue false 2 2
  let x : ℝ := (14 : ℝ)
  have hm : fmt.normalizedMantissa 1 := by
    norm_num [fmt, decimalOneDigitTwoExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (1 + 1) := by
    norm_num [fmt, decimalOneDigitTwoExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 1, (2 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have hstrict : a < x ∧ x < b := by
    norm_num [x, a, b, fmt, decimalOneDigitTwoExponentFormat,
      normalizedValue, signValue, betaR]
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
      simpa [x, hmax] using (by norm_num : (14 : ℝ) ≤ 90)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleft : a = fmt.normalizedValue false 1 (2 : ℤ) := rfl
  have hleftCloser : |x - a| < |x - b| := by
    norm_num [x, a, b, fmt, decimalOneDigitTwoExponentFormat,
      normalizedValue, signValue, betaR]
    change |(4 : ℝ)| < 6
    norm_num
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  have htarget : fmt.finiteRoundToEven ((10 : ℝ) + 4) = a := by
    have hxsum : ((10 : ℝ) + 4) = x := by norm_num [x]
    rw [hxsum]
    exact hround
  simpa [finiteRoundToEvenOp, BasicOp.exact, a, fmt,
    decimalOneDigitTwoExponentFormat, normalizedValue, signValue, betaR]
    using htarget

/-- In the tiny decimal format, subtracting `-8` from `10` forms exact `18`,
whose nearest one-digit decimal values at exponent `2` are `10` and `20`; it is
strictly closer to `20`. -/
theorem decimalOneDigitTwoExponent_sub_ten_neg_eight_rounds_to_twenty :
    decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp
        BasicOp.sub (10 : ℝ) (-8) = 20 := by
  let fmt := decimalOneDigitTwoExponentFormat
  let a : ℝ := fmt.normalizedValue false 1 2
  let b : ℝ := fmt.normalizedValue false 2 2
  let x : ℝ := (18 : ℝ)
  have hm : fmt.normalizedMantissa 1 := by
    norm_num [fmt, decimalOneDigitTwoExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (1 + 1) := by
    norm_num [fmt, decimalOneDigitTwoExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 1, (2 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have hstrict : a < x ∧ x < b := by
    norm_num [x, a, b, fmt, decimalOneDigitTwoExponentFormat,
      normalizedValue, signValue, betaR]
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
      simpa [x, hmax] using (by norm_num : (18 : ℝ) ≤ 90)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hrightCloser : |x - b| < |x - a| := by
    norm_num [x, a, b, fmt, decimalOneDigitTwoExponentFormat,
      normalizedValue, signValue, betaR]
    change (2 : ℝ) < |(8 : ℝ)|
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 8)]
    norm_num
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  have htarget : fmt.finiteRoundToEven ((10 : ℝ) - (-8)) = b := by
    have hxsub : ((10 : ℝ) - (-8)) = x := by norm_num [x]
    rw [hxsub]
    exact hround
  have hb : b = (20 : ℝ) := by
    norm_num [b, fmt, decimalOneDigitTwoExponentFormat, normalizedValue,
      signValue, betaR]
  simpa [finiteRoundToEvenOp, BasicOp.exact, hb] using htarget

theorem decimalOneDigitTwoExponent_add_ten_neg_four_exact :
    decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp
        BasicOp.add (10 : ℝ) (-4) = 6 := by
  have hfin :
      decimalOneDigitTwoExponentFormat.finiteSystem
        (BasicOp.exact BasicOp.add (10 : ℝ) (-4)) := by
    norm_num [BasicOp.exact]
    exact decimalOneDigitTwoExponentFormat_finiteSystem_six
  have hround :=
    decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add) (x := (10 : ℝ)) (y := (-4 : ℝ)) hfin
  change decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp
      BasicOp.add (10 : ℝ) (-4) = (10 : ℝ) + (-4) at hround
  norm_num at hround
  exact hround

theorem decimalOneDigitTwoExponent_sub_ten_neg_four_rounds_to_ten :
    decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp
        BasicOp.sub (10 : ℝ) (-4) = 10 := by
  have h := decimalOneDigitTwoExponent_add_ten_four_rounds_to_ten
  change decimalOneDigitTwoExponentFormat.finiteRoundToEven ((10 : ℝ) + 4) = 10 at h
  change decimalOneDigitTwoExponentFormat.finiteRoundToEven ((10 : ℝ) - (-4)) = 10
  norm_num at h ⊢
  exact h

theorem decimalOneDigitTwoExponent_sub_ten_four_exact :
    decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp
        BasicOp.sub (10 : ℝ) 4 = 6 := by
  have hfin :
      decimalOneDigitTwoExponentFormat.finiteSystem
        (BasicOp.exact BasicOp.sub (10 : ℝ) 4) := by
    norm_num [BasicOp.exact]
    exact decimalOneDigitTwoExponentFormat_finiteSystem_six
  have hround :=
    decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (10 : ℝ)) (y := (4 : ℝ)) hfin
  change decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp
      BasicOp.sub (10 : ℝ) 4 = (10 : ℝ) - 4 at hround
  norm_num at hround
  exact hround

theorem decimalOneDigitTwoExponent_sub_neg_four_four_exact :
    decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp
        BasicOp.sub (-4 : ℝ) 4 = -8 := by
  have hfin :
      decimalOneDigitTwoExponentFormat.finiteSystem
        (BasicOp.exact BasicOp.sub (-4 : ℝ) 4) := by
    norm_num [BasicOp.exact]
    exact decimalOneDigitTwoExponentFormat_finiteSystem_neg_eight
  have hround :=
    decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub) (x := (-4 : ℝ)) (y := (4 : ℝ)) hfin
  change decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp
      BasicOp.sub (-4 : ℝ) 4 = (-4 : ℝ) - 4 at hround
  norm_num at hround
  exact hround

theorem decimalOneDigitTwoExponent_add_four_neg_four_exact :
    decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp
        BasicOp.add (4 : ℝ) (-4) = 0 := by
  have hfin :
      decimalOneDigitTwoExponentFormat.finiteSystem
        (BasicOp.exact BasicOp.add (4 : ℝ) (-4)) := by
    simpa [BasicOp.exact] using
      decimalOneDigitTwoExponentFormat.finiteSystem_zero
  have hround :=
    decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add) (x := (4 : ℝ)) (y := (-4 : ℝ)) hfin
  change decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp
      BasicOp.add (4 : ℝ) (-4) = (4 : ℝ) + (-4) at hround
  norm_num at hround
  exact hround

theorem decimalOneDigitTwoExponent_add_ten_zero_exact :
    decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp
        BasicOp.add (10 : ℝ) 0 = 10 := by
  have hfin :
      decimalOneDigitTwoExponentFormat.finiteSystem
        (BasicOp.exact BasicOp.add (10 : ℝ) 0) := by
    norm_num [BasicOp.exact]
    exact decimalOneDigitTwoExponentFormat_finiteSystem_ten
  have hround :=
    decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.add) (x := (10 : ℝ)) (y := (0 : ℝ)) hfin
  change decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp
      BasicOp.add (10 : ℝ) 0 = (10 : ℝ) + 0 at hround
  norm_num at hround
  exact hround

/-- Concrete finite round-to-even addition is not associative.  All operands
and both final results are finite values in the tiny decimal format; the
nonassociativity comes from the inner rounding `10 ⊕ 4 = 10`. -/
theorem decimalOneDigitTwoExponent_roundToEven_add_nonassociative :
    decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp BasicOp.add
        (decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp
          BasicOp.add (10 : ℝ) 4) (-4) ≠
      decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp BasicOp.add
        (10 : ℝ)
        (decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp
          BasicOp.add (4 : ℝ) (-4)) := by
  rw [decimalOneDigitTwoExponent_add_ten_four_rounds_to_ten,
    decimalOneDigitTwoExponent_add_ten_neg_four_exact,
    decimalOneDigitTwoExponent_add_four_neg_four_exact,
    decimalOneDigitTwoExponent_add_ten_zero_exact]
  norm_num

/-- Concrete finite round-to-even subtraction is not associative.  The inner
rounding `10 ⊖ (-4) = 10` loses the `4`, while the other parenthesization forms
the exact inner result `-8` and then rounds `18` to `20`. -/
theorem decimalOneDigitTwoExponent_roundToEven_sub_nonassociative :
    decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp BasicOp.sub
        (decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp
          BasicOp.sub (10 : ℝ) (-4)) 4 ≠
      decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp BasicOp.sub
        (10 : ℝ)
        (decimalOneDigitTwoExponentFormat.finiteRoundToEvenOp
          BasicOp.sub (-4 : ℝ) 4) := by
  rw [decimalOneDigitTwoExponent_sub_ten_neg_four_rounds_to_ten,
    decimalOneDigitTwoExponent_sub_ten_four_exact,
    decimalOneDigitTwoExponent_sub_neg_four_four_exact,
    decimalOneDigitTwoExponent_sub_ten_neg_eight_rounds_to_twenty]
  norm_num

/-- A tiny decimal finite format with one significant digit and exponents
`0`, `1`, and `2`.  Positive normalized values include
`0.1,0.2,...,0.9,1,2,...,9,10,20,...,90`. -/
def decimalOneDigitThreeExponentFormat : FloatingPointFormat where
  beta := 10
  t := 1
  emin := 0
  emax := 2
  beta_ge_two := by norm_num
  t_pos := by norm_num
  emin_le_emax := by norm_num

theorem decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_one_tenth :
    decimalOneDigitThreeExponentFormat.normalizedExponentRepresentation
      (1 / 10 : ℝ) 0 := by
  refine ⟨false, 1, ?_, ?_, ?_⟩
  · norm_num [decimalOneDigitThreeExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  · norm_num [decimalOneDigitThreeExponentFormat, exponentInRange]
  · norm_num [decimalOneDigitThreeExponentFormat, normalizedValue, signValue, betaR]

theorem decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_one_fifth :
    decimalOneDigitThreeExponentFormat.normalizedExponentRepresentation
      (1 / 5 : ℝ) 0 := by
  refine ⟨false, 2, ?_, ?_, ?_⟩
  · norm_num [decimalOneDigitThreeExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  · norm_num [decimalOneDigitThreeExponentFormat, exponentInRange]
  · norm_num [decimalOneDigitThreeExponentFormat, normalizedValue, signValue, betaR]

theorem decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_three_tenths :
    decimalOneDigitThreeExponentFormat.normalizedExponentRepresentation
      (3 / 10 : ℝ) 0 := by
  refine ⟨false, 3, ?_, ?_, ?_⟩
  · norm_num [decimalOneDigitThreeExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  · norm_num [decimalOneDigitThreeExponentFormat, exponentInRange]
  · norm_num [decimalOneDigitThreeExponentFormat, normalizedValue, signValue, betaR]

theorem decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_two_fifths :
    decimalOneDigitThreeExponentFormat.normalizedExponentRepresentation
      (2 / 5 : ℝ) 0 := by
  refine ⟨false, 4, ?_, ?_, ?_⟩
  · norm_num [decimalOneDigitThreeExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  · norm_num [decimalOneDigitThreeExponentFormat, exponentInRange]
  · norm_num [decimalOneDigitThreeExponentFormat, normalizedValue, signValue, betaR]

theorem decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_three_fifths :
    decimalOneDigitThreeExponentFormat.normalizedExponentRepresentation
      (3 / 5 : ℝ) 0 := by
  refine ⟨false, 6, ?_, ?_, ?_⟩
  · norm_num [decimalOneDigitThreeExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  · norm_num [decimalOneDigitThreeExponentFormat, exponentInRange]
  · norm_num [decimalOneDigitThreeExponentFormat, normalizedValue, signValue, betaR]

theorem decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_two :
    decimalOneDigitThreeExponentFormat.normalizedExponentRepresentation
      (2 : ℝ) 1 := by
  refine ⟨false, 2, ?_, ?_, ?_⟩
  · norm_num [decimalOneDigitThreeExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  · norm_num [decimalOneDigitThreeExponentFormat, exponentInRange]
  · norm_num [decimalOneDigitThreeExponentFormat, normalizedValue, signValue, betaR]

theorem decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_one :
    decimalOneDigitThreeExponentFormat.normalizedExponentRepresentation
      (1 : ℝ) 1 := by
  refine ⟨false, 1, ?_, ?_, ?_⟩
  · norm_num [decimalOneDigitThreeExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  · norm_num [decimalOneDigitThreeExponentFormat, exponentInRange]
  · norm_num [decimalOneDigitThreeExponentFormat, normalizedValue, signValue, betaR]

theorem decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_three :
    decimalOneDigitThreeExponentFormat.normalizedExponentRepresentation
      (3 : ℝ) 1 := by
  refine ⟨false, 3, ?_, ?_, ?_⟩
  · norm_num [decimalOneDigitThreeExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  · norm_num [decimalOneDigitThreeExponentFormat, exponentInRange]
  · norm_num [decimalOneDigitThreeExponentFormat, normalizedValue, signValue, betaR]

theorem decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_ten :
    decimalOneDigitThreeExponentFormat.normalizedExponentRepresentation
      (10 : ℝ) 2 := by
  refine ⟨false, 1, ?_, ?_, ?_⟩
  · norm_num [decimalOneDigitThreeExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  · norm_num [decimalOneDigitThreeExponentFormat, exponentInRange]
  · norm_num [decimalOneDigitThreeExponentFormat, normalizedValue, signValue, betaR]

theorem decimalOneDigitThreeExponentFormat_finiteSystem_one_tenth :
    decimalOneDigitThreeExponentFormat.finiteSystem (1 / 10 : ℝ) :=
  Or.inr (Or.inl
    (decimalOneDigitThreeExponentFormat.normalizedExponentRepresentation_normalizedSystem
      decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_one_tenth))

theorem decimalOneDigitThreeExponentFormat_finiteSystem_one :
    decimalOneDigitThreeExponentFormat.finiteSystem (1 : ℝ) :=
  Or.inr (Or.inl
    (decimalOneDigitThreeExponentFormat.normalizedExponentRepresentation_normalizedSystem
      decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_one))

theorem decimalOneDigitThreeExponentFormat_finiteSystem_three_tenths :
    decimalOneDigitThreeExponentFormat.finiteSystem (3 / 10 : ℝ) :=
  Or.inr (Or.inl
    (decimalOneDigitThreeExponentFormat.normalizedExponentRepresentation_normalizedSystem
      decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_three_tenths))

theorem decimalOneDigitThreeExponentFormat_finiteSystem_two_fifths :
    decimalOneDigitThreeExponentFormat.finiteSystem (2 / 5 : ℝ) :=
  Or.inr (Or.inl
    (decimalOneDigitThreeExponentFormat.normalizedExponentRepresentation_normalizedSystem
      decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_two_fifths))

theorem decimalOneDigitThreeExponentFormat_finiteSystem_ten :
    decimalOneDigitThreeExponentFormat.finiteSystem (10 : ℝ) :=
  Or.inr (Or.inl
    (decimalOneDigitThreeExponentFormat.normalizedExponentRepresentation_normalizedSystem
      decimalOneDigitThreeExponentFormat_normalizedExponentRepresentation_ten))

/-- In the `0..2` one-digit decimal format, `0.2 * 0.6 = 0.12` rounds down to
`0.1`. -/
theorem decimalOneDigitThreeExponent_mul_one_fifth_three_fifths_rounds_to_one_tenth :
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
        BasicOp.mul (1 / 5 : ℝ) (3 / 5) = 1 / 10 := by
  let fmt := decimalOneDigitThreeExponentFormat
  let a : ℝ := fmt.normalizedValue false 1 0
  let b : ℝ := fmt.normalizedValue false 2 0
  let x : ℝ := (3 / 25 : ℝ)
  have hm : fmt.normalizedMantissa 1 := by
    norm_num [fmt, decimalOneDigitThreeExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (1 + 1) := by
    norm_num [fmt, decimalOneDigitThreeExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 1, (0 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
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
      simpa [x, hmax] using (by norm_num : (3 / 25 : ℝ) ≤ 90)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    norm_num [x, a, b, fmt, decimalOneDigitThreeExponentFormat,
      normalizedValue, signValue, betaR]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  have htarget : fmt.finiteRoundToEven ((1 / 5 : ℝ) * (3 / 5)) = a := by
    have hxmul : ((1 / 5 : ℝ) * (3 / 5)) = x := by norm_num [x]
    rw [hxmul]
    exact hround
  have ha : a = (1 / 10 : ℝ) := by
    norm_num [a, fmt, decimalOneDigitThreeExponentFormat, normalizedValue,
      signValue, betaR]
  simpa [finiteRoundToEvenOp, BasicOp.exact, ha] using htarget

/-- In the same one-digit decimal format, `0.6 * 3 = 1.8` rounds up to `2`. -/
theorem decimalOneDigitThreeExponent_mul_three_fifths_three_rounds_to_two :
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
        BasicOp.mul (3 / 5 : ℝ) 3 = 2 := by
  let fmt := decimalOneDigitThreeExponentFormat
  let a : ℝ := fmt.normalizedValue false 1 1
  let b : ℝ := fmt.normalizedValue false 2 1
  let x : ℝ := (9 / 5 : ℝ)
  have hm : fmt.normalizedMantissa 1 := by
    norm_num [fmt, decimalOneDigitThreeExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (1 + 1) := by
    norm_num [fmt, decimalOneDigitThreeExponentFormat, normalizedMantissa,
      mantissaInRange, minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 1, (1 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
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
      simpa [x, hmax] using (by norm_num : (9 / 5 : ℝ) ≤ 90)
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hrightCloser : |x - b| < |x - a| := by
    norm_num [x, a, b, fmt, decimalOneDigitThreeExponentFormat,
      normalizedValue, signValue, betaR]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  have htarget : fmt.finiteRoundToEven ((3 / 5 : ℝ) * 3) = b := by
    have hxmul : ((3 / 5 : ℝ) * 3) = x := by norm_num [x]
    rw [hxmul]
    exact hround
  have hb : b = (2 : ℝ) := by
    norm_num [b, fmt, decimalOneDigitThreeExponentFormat, normalizedValue,
      signValue, betaR]
  simpa [finiteRoundToEvenOp, BasicOp.exact, hb] using htarget

theorem decimalOneDigitThreeExponent_mul_one_tenth_three_exact :
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
        BasicOp.mul (1 / 10 : ℝ) 3 = 3 / 10 := by
  have hfin :
      decimalOneDigitThreeExponentFormat.finiteSystem
        (BasicOp.exact BasicOp.mul (1 / 10 : ℝ) 3) := by
    norm_num [BasicOp.exact]
    exact decimalOneDigitThreeExponentFormat_finiteSystem_three_tenths
  have hround :=
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul) (x := (1 / 10 : ℝ)) (y := (3 : ℝ)) hfin
  change decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
      BasicOp.mul (1 / 10 : ℝ) 3 = (1 / 10 : ℝ) * 3 at hround
  norm_num at hround
  exact hround

theorem decimalOneDigitThreeExponent_mul_one_fifth_two_exact :
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
        BasicOp.mul (1 / 5 : ℝ) 2 = 2 / 5 := by
  have hfin :
      decimalOneDigitThreeExponentFormat.finiteSystem
        (BasicOp.exact BasicOp.mul (1 / 5 : ℝ) 2) := by
    norm_num [BasicOp.exact]
    exact decimalOneDigitThreeExponentFormat_finiteSystem_two_fifths
  have hround :=
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul) (x := (1 / 5 : ℝ)) (y := (2 : ℝ)) hfin
  change decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
      BasicOp.mul (1 / 5 : ℝ) 2 = (1 / 5 : ℝ) * 2 at hround
  norm_num at hround
  exact hround

/-- Concrete finite round-to-even multiplication is not associative.  The
left parenthesization rounds `0.2 * 0.6 = 0.12` to `0.1`, while the right
parenthesization rounds `0.6 * 3 = 1.8` to `2`. -/
theorem decimalOneDigitThreeExponent_roundToEven_mul_nonassociative :
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp BasicOp.mul
        (decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
          BasicOp.mul (1 / 5 : ℝ) (3 / 5)) 3 ≠
      decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp BasicOp.mul
        (1 / 5 : ℝ)
        (decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
          BasicOp.mul (3 / 5 : ℝ) 3) := by
  rw [decimalOneDigitThreeExponent_mul_one_fifth_three_fifths_rounds_to_one_tenth,
    decimalOneDigitThreeExponent_mul_one_tenth_three_exact,
    decimalOneDigitThreeExponent_mul_three_fifths_three_rounds_to_two,
    decimalOneDigitThreeExponent_mul_one_fifth_two_exact]
  norm_num

theorem decimalOneDigitThreeExponent_div_one_tenth_one_tenth_exact :
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
        BasicOp.div (1 / 10 : ℝ) (1 / 10) = 1 := by
  have hfin :
      decimalOneDigitThreeExponentFormat.finiteSystem
        (BasicOp.exact BasicOp.div (1 / 10 : ℝ) (1 / 10)) := by
    norm_num [BasicOp.exact]
    exact decimalOneDigitThreeExponentFormat_finiteSystem_one
  have hround :=
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.div) (x := (1 / 10 : ℝ)) (y := (1 / 10 : ℝ)) hfin
  change decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
      BasicOp.div (1 / 10 : ℝ) (1 / 10) = (1 / 10 : ℝ) / (1 / 10) at hround
  norm_num at hround
  exact hround

theorem decimalOneDigitThreeExponent_div_one_one_tenth_exact :
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
        BasicOp.div (1 : ℝ) (1 / 10) = 10 := by
  have hfin :
      decimalOneDigitThreeExponentFormat.finiteSystem
        (BasicOp.exact BasicOp.div (1 : ℝ) (1 / 10)) := by
    norm_num [BasicOp.exact]
    exact decimalOneDigitThreeExponentFormat_finiteSystem_ten
  have hround :=
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.div) (x := (1 : ℝ)) (y := (1 / 10 : ℝ)) hfin
  change decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
      BasicOp.div (1 : ℝ) (1 / 10) = (1 : ℝ) / (1 / 10) at hround
  norm_num at hround
  exact hround

theorem decimalOneDigitThreeExponent_div_one_tenth_one_exact :
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
        BasicOp.div (1 / 10 : ℝ) 1 = 1 / 10 := by
  have hfin :
      decimalOneDigitThreeExponentFormat.finiteSystem
        (BasicOp.exact BasicOp.div (1 / 10 : ℝ) 1) := by
    norm_num [BasicOp.exact]
    exact decimalOneDigitThreeExponentFormat_finiteSystem_one_tenth
  have hround :=
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.div) (x := (1 / 10 : ℝ)) (y := (1 : ℝ)) hfin
  change decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
      BasicOp.div (1 / 10 : ℝ) 1 = (1 / 10 : ℝ) / 1 at hround
  norm_num at hround
  exact hround

/-- Concrete finite round-to-even division is not associative.  This example
does not require an inexact rounding step: the finite wrapper preserves the
exact representable divisions, and exact division is already nonassociative. -/
theorem decimalOneDigitThreeExponent_roundToEven_div_nonassociative :
    decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp BasicOp.div
        (decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
          BasicOp.div (1 / 10 : ℝ) (1 / 10)) (1 / 10) ≠
      decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp BasicOp.div
        (1 / 10 : ℝ)
        (decimalOneDigitThreeExponentFormat.finiteRoundToEvenOp
          BasicOp.div (1 / 10 : ℝ) (1 / 10)) := by
  rw [decimalOneDigitThreeExponent_div_one_tenth_one_tenth_exact,
    decimalOneDigitThreeExponent_div_one_one_tenth_exact,
    decimalOneDigitThreeExponent_div_one_tenth_one_exact]
  norm_num

end FloatingPointFormat

end

end NumStability
