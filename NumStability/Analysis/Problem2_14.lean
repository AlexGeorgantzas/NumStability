-- Analysis/Problem2_14.lean
--
-- Problem-specific theorem surface for Higham Chapter 2, Problem 2.14.

import NumStability.Analysis.Problem2_13

namespace NumStability

noncomputable section

namespace FloatingPointFormat

/-!
# Higham Chapter 2, Problem 2.14

Problem 2.14 asks the reader to test Kahan's probe
`|3 * (4/3 - 1) - 1|`, with every arithmetic operation rounded, as an
over-estimate of the unit roundoff.  This file records the finite IEEE-double
round-to-even wrapper trace.  It is intentionally not a claim about every
hardware environment or the full IEEE exception/special-value layer.
-/

private theorem problem2_14_ieeeDoubleFormat_minNormalMagnitude_le_one :
    ieeeDoubleFormat.minNormalMagnitude ≤ (1 : ℝ) := by
  norm_num [ieeeDoubleFormat, minNormalMagnitude, betaR, zpow_neg]
  have hden : (1 : ℝ) ≤ (2 : ℝ) ^ (1022 : ℕ) := by
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  simpa [one_div] using
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden

private theorem problem2_14_four_le_ieeeDoubleFormat_maxFiniteMagnitude :
    (4 : ℝ) ≤ ieeeDoubleFormat.maxFiniteMagnitude := by
  rw [maxFiniteMagnitude, ieeeDoubleFormat, betaR]
  norm_num [zpow_neg]
  change (4 : ℝ) ≤ (2 : ℝ) ^ (1024 : ℕ) *
    (9007199254740991 / 9007199254740992 : ℝ)
  have hfactor :
      (1 / 2 : ℝ) ≤ (9007199254740991 / 9007199254740992 : ℝ) := by
    norm_num
  have hpow_nat : (8 : ℝ) ≤ (2 : ℝ) ^ (1024 : ℕ) := by
    calc
      (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ (1024 : ℕ) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num)
  have hmul := mul_le_mul hpow_nat hfactor
    (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
    (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (1024 : ℕ))
  norm_num at hmul
  exact hmul

private theorem problem2_14_ieeeDouble_four_thirds_finiteNormalRange :
    ieeeDoubleFormat.finiteNormalRange (4 / 3 : ℝ) := by
  rw [finiteNormalRange, abs_of_pos (by norm_num : (0 : ℝ) < 4 / 3)]
  constructor
  · exact le_trans problem2_14_ieeeDoubleFormat_minNormalMagnitude_le_one
      (by norm_num : (1 : ℝ) ≤ 4 / 3)
  · exact le_trans (by norm_num : (4 / 3 : ℝ) ≤ 4)
      problem2_14_four_le_ieeeDoubleFormat_maxFiniteMagnitude

private theorem problem2_14_normalizedValue_finiteSystem
    (negative : Bool) (m : ℕ) (e : ℤ)
    (hm : ieeeDoubleFormat.normalizedMantissa m)
    (he : ieeeDoubleFormat.exponentInRange e) :
    ieeeDoubleFormat.finiteSystem
      (ieeeDoubleFormat.normalizedValue negative m e) := by
  exact Or.inr (Or.inl ⟨negative, m, e, hm, he, rfl⟩)

private theorem problem2_14_ieeeSingleFormat_minNormalMagnitude_le_one :
    ieeeSingleFormat.minNormalMagnitude ≤ (1 : ℝ) := by
  norm_num [ieeeSingleFormat, minNormalMagnitude, betaR, zpow_neg]

private theorem problem2_14_four_le_ieeeSingleFormat_maxFiniteMagnitude :
    (4 : ℝ) ≤ ieeeSingleFormat.maxFiniteMagnitude := by
  rw [maxFiniteMagnitude, ieeeSingleFormat, betaR]
  norm_num [zpow_neg]

private theorem problem2_14_ieeeSingle_four_thirds_finiteNormalRange :
    ieeeSingleFormat.finiteNormalRange (4 / 3 : ℝ) := by
  rw [finiteNormalRange, abs_of_pos (by norm_num : (0 : ℝ) < 4 / 3)]
  constructor
  · exact le_trans problem2_14_ieeeSingleFormat_minNormalMagnitude_le_one
      (by norm_num : (1 : ℝ) ≤ 4 / 3)
  · exact le_trans (by norm_num : (4 / 3 : ℝ) ≤ 4)
      problem2_14_four_le_ieeeSingleFormat_maxFiniteMagnitude

private theorem problem2_14_ieeeSingle_normalizedValue_finiteSystem
    (negative : Bool) (m : ℕ) (e : ℤ)
    (hm : ieeeSingleFormat.normalizedMantissa m)
    (he : ieeeSingleFormat.exponentInRange e) :
    ieeeSingleFormat.finiteSystem
      (ieeeSingleFormat.normalizedValue negative m e) := by
  exact Or.inr (Or.inl ⟨negative, m, e, hm, he, rfl⟩)

/-- First rounded operation in Kahan's Problem 2.14 probe:
finite IEEE-double round-to-even rounds `4/3` to the lower adjacent endpoint. -/
theorem problem2_14_ieeeDouble_four_thirds_rounds_to_lower :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div (4 : ℝ) 3 =
      (6004799503160661 : ℝ) * (2 : ℝ) ^ (-52 : ℤ) := by
  let fmt := ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false 6004799503160661 1
  let b : ℝ := fmt.normalizedValue false 6004799503160662 1
  let x : ℝ := (4 / 3 : ℝ)
  have hm : fmt.normalizedMantissa 6004799503160661 := by
    norm_num [fmt, ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (6004799503160661 + 1) := by
    norm_num [fmt, ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 6004799503160661, (1 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, rfl⟩⟩
  have ha_value :
      a = (6004799503160661 : ℝ) * (2 : ℝ) ^ (-52 : ℤ) := by
    norm_num [a, fmt, ieeeDoubleFormat, normalizedValue, signValue, betaR,
      zpow_neg]
  have hb_value :
      b = (6004799503160662 : ℝ) * (2 : ℝ) ^ (-52 : ℤ) := by
    norm_num [b, fmt, ieeeDoubleFormat, normalizedValue, signValue, betaR,
      zpow_neg]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      problem2_14_ieeeDouble_four_thirds_finiteNormalRange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  change fmt.finiteRoundToEven (BasicOp.exact BasicOp.div (4 : ℝ) 3) =
    (6004799503160661 : ℝ) * (2 : ℝ) ^ (-52 : ℤ)
  simpa [BasicOp.exact, x, fmt, ha_value] using hround

/-- After the rounded division, the rounded subtraction by `1` is exact. -/
theorem problem2_14_ieeeDouble_four_thirds_minus_one :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div (4 : ℝ) 3) 1 =
      (6004799503160660 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
  rw [problem2_14_ieeeDouble_four_thirds_rounds_to_lower]
  have hfin :
      ieeeDoubleFormat.finiteSystem
        (BasicOp.exact BasicOp.sub
          ((6004799503160661 : ℝ) * (2 : ℝ) ^ (-52 : ℤ)) 1) := by
    change ieeeDoubleFormat.finiteSystem
      (((6004799503160661 : ℝ) * (2 : ℝ) ^ (-52 : ℤ)) - 1)
    have hnorm :
        ieeeDoubleFormat.finiteSystem
          (ieeeDoubleFormat.normalizedValue false 6004799503160660 (-1)) :=
      problem2_14_normalizedValue_finiteSystem false 6004799503160660 (-1)
        (by
          norm_num [ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
            minNormalMantissa])
        (by norm_num [ieeeDoubleFormat, exponentInRange])
    convert hnorm using 1
    norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR, zpow_neg]
  have hround :=
    (ieeeDoubleFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub)
      (x := (6004799503160661 : ℝ) * (2 : ℝ) ^ (-52 : ℤ))
      (y := 1) hfin)
  rw [hround]
  norm_num [BasicOp.exact, zpow_neg]

/-- Multiplying the rounded `4/3 - 1` value by `3` is exact in the finite
IEEE-double wrapper and gives `1 - 2^-52`. -/
theorem problem2_14_ieeeDouble_three_mul_four_thirds_minus_one :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (3 : ℝ)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub
          (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div (4 : ℝ) 3) 1) =
      (1 : ℝ) - (2 : ℝ) ^ (-52 : ℤ) := by
  rw [problem2_14_ieeeDouble_four_thirds_minus_one]
  have hfin :
      ieeeDoubleFormat.finiteSystem
        (BasicOp.exact BasicOp.mul (3 : ℝ)
          ((6004799503160660 : ℝ) * (2 : ℝ) ^ (-54 : ℤ))) := by
    change ieeeDoubleFormat.finiteSystem
      ((3 : ℝ) * ((6004799503160660 : ℝ) * (2 : ℝ) ^ (-54 : ℤ)))
    have hnorm :
        ieeeDoubleFormat.finiteSystem
          (ieeeDoubleFormat.normalizedValue false 9007199254740990 0) :=
      problem2_14_normalizedValue_finiteSystem false 9007199254740990 0
        (by
          norm_num [ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
            minNormalMantissa])
        (by norm_num [ieeeDoubleFormat, exponentInRange])
    convert hnorm using 1
    norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR, zpow_neg]
  have hround :=
    (ieeeDoubleFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul)
      (x := (3 : ℝ))
      (y := (6004799503160660 : ℝ) * (2 : ℝ) ^ (-54 : ℤ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact, zpow_neg]

/-- The signed final error in Kahan's finite IEEE-double Problem 2.14 probe. -/
theorem problem2_14_ieeeDouble_kahan_probe_error :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (3 : ℝ)
          (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub
            (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div (4 : ℝ) 3) 1)) 1 =
      -((2 : ℝ) ^ (-52 : ℤ)) := by
  rw [problem2_14_ieeeDouble_three_mul_four_thirds_minus_one]
  have hfin :
      ieeeDoubleFormat.finiteSystem
        (BasicOp.exact BasicOp.sub
          ((1 : ℝ) - (2 : ℝ) ^ (-52 : ℤ)) 1) := by
    change ieeeDoubleFormat.finiteSystem
      (((1 : ℝ) - (2 : ℝ) ^ (-52 : ℤ)) - 1)
    have hnorm :
        ieeeDoubleFormat.finiteSystem
          (ieeeDoubleFormat.normalizedValue true 4503599627370496 (-51)) :=
      problem2_14_normalizedValue_finiteSystem true 4503599627370496 (-51)
        (by
          norm_num [ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
            minNormalMantissa])
        (by norm_num [ieeeDoubleFormat, exponentInRange])
    convert hnorm using 1
    norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR, zpow_neg]
  have hround :=
    (ieeeDoubleFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub)
      (x := (1 : ℝ) - (2 : ℝ) ^ (-52 : ℤ))
      (y := 1) hfin)
  simpa [BasicOp.exact, zpow_neg] using hround

/-- Absolute-value form of Kahan's finite IEEE-double Problem 2.14 probe. -/
def problem2_14_ieeeDoubleKahanEstimate : ℝ :=
  |ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub
      (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (3 : ℝ)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub
          (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div (4 : ℝ) 3) 1)) 1|

theorem problem2_14_ieeeDoubleKahanEstimate_eq_machineEpsilon :
    problem2_14_ieeeDoubleKahanEstimate = (2 : ℝ) ^ (-52 : ℤ) := by
  rw [problem2_14_ieeeDoubleKahanEstimate,
    problem2_14_ieeeDouble_kahan_probe_error]
  norm_num [zpow_neg]

theorem problem2_14_ieeeDoubleKahanEstimate_eq_two_unitRoundoff :
    problem2_14_ieeeDoubleKahanEstimate =
      2 * ieeeDoubleFormat.unitRoundoff := by
  rw [problem2_14_ieeeDoubleKahanEstimate_eq_machineEpsilon,
    ieeeDoubleFormat_unitRoundoff]
  norm_num [zpow_neg]

/-- First rounded operation in Kahan's Problem 2.14 probe:
finite IEEE-single round-to-even rounds `4/3` to the upper adjacent endpoint. -/
theorem problem2_14_ieeeSingle_four_thirds_rounds_to_upper :
    ieeeSingleFormat.finiteRoundToEvenOp BasicOp.div (4 : ℝ) 3 =
      (11184811 : ℝ) * (2 : ℝ) ^ (-23 : ℤ) := by
  let fmt := ieeeSingleFormat
  let a : ℝ := fmt.normalizedValue false 11184810 1
  let b : ℝ := fmt.normalizedValue false 11184811 1
  let x : ℝ := (4 / 3 : ℝ)
  have hm : fmt.normalizedMantissa 11184810 := by
    norm_num [fmt, ieeeSingleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (11184810 + 1) := by
    norm_num [fmt, ieeeSingleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 11184810, (1 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, rfl⟩⟩
  have ha_value :
      a = (11184810 : ℝ) * (2 : ℝ) ^ (-23 : ℤ) := by
    norm_num [a, fmt, ieeeSingleFormat, normalizedValue, signValue, betaR,
      zpow_neg]
  have hb_value :
      b = (11184811 : ℝ) * (2 : ℝ) ^ (-23 : ℤ) := by
    norm_num [b, fmt, ieeeSingleFormat, normalizedValue, signValue, betaR,
      zpow_neg]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      problem2_14_ieeeSingle_four_thirds_finiteNormalRange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  change fmt.finiteRoundToEven (BasicOp.exact BasicOp.div (4 : ℝ) 3) =
    (11184811 : ℝ) * (2 : ℝ) ^ (-23 : ℤ)
  simpa [BasicOp.exact, x, fmt, hb_value] using hround

/-- After the single-precision rounded division, the rounded subtraction by
`1` is exact. -/
theorem problem2_14_ieeeSingle_four_thirds_minus_one :
    ieeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (ieeeSingleFormat.finiteRoundToEvenOp BasicOp.div (4 : ℝ) 3) 1 =
      (11184812 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) := by
  rw [problem2_14_ieeeSingle_four_thirds_rounds_to_upper]
  have hfin :
      ieeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.sub
          ((11184811 : ℝ) * (2 : ℝ) ^ (-23 : ℤ)) 1) := by
    change ieeeSingleFormat.finiteSystem
      (((11184811 : ℝ) * (2 : ℝ) ^ (-23 : ℤ)) - 1)
    have hnorm :
        ieeeSingleFormat.finiteSystem
          (ieeeSingleFormat.normalizedValue false 11184812 (-1)) :=
      problem2_14_ieeeSingle_normalizedValue_finiteSystem false 11184812 (-1)
        (by
          norm_num [ieeeSingleFormat, normalizedMantissa, mantissaInRange,
            minNormalMantissa])
        (by norm_num [ieeeSingleFormat, exponentInRange])
    convert hnorm using 1
    norm_num [ieeeSingleFormat, normalizedValue, signValue, betaR, zpow_neg]
  have hround :=
    (ieeeSingleFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub)
      (x := (11184811 : ℝ) * (2 : ℝ) ^ (-23 : ℤ))
      (y := 1) hfin)
  rw [hround]
  norm_num [BasicOp.exact, zpow_neg]

/-- Multiplying the rounded single-precision `4/3 - 1` value by `3` is exact
in the finite wrapper and gives `1 + 2^-23`. -/
theorem problem2_14_ieeeSingle_three_mul_four_thirds_minus_one :
    ieeeSingleFormat.finiteRoundToEvenOp BasicOp.mul (3 : ℝ)
        (ieeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
          (ieeeSingleFormat.finiteRoundToEvenOp BasicOp.div (4 : ℝ) 3) 1) =
      (1 : ℝ) + (2 : ℝ) ^ (-23 : ℤ) := by
  rw [problem2_14_ieeeSingle_four_thirds_minus_one]
  have hfin :
      ieeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.mul (3 : ℝ)
          ((11184812 : ℝ) * (2 : ℝ) ^ (-25 : ℤ))) := by
    change ieeeSingleFormat.finiteSystem
      ((3 : ℝ) * ((11184812 : ℝ) * (2 : ℝ) ^ (-25 : ℤ)))
    have hnorm :
        ieeeSingleFormat.finiteSystem
          (ieeeSingleFormat.normalizedValue false 8388609 1) :=
      problem2_14_ieeeSingle_normalizedValue_finiteSystem false 8388609 1
        (by
          norm_num [ieeeSingleFormat, normalizedMantissa, mantissaInRange,
            minNormalMantissa])
        (by norm_num [ieeeSingleFormat, exponentInRange])
    convert hnorm using 1
    norm_num [ieeeSingleFormat, normalizedValue, signValue, betaR, zpow_neg]
  have hround :=
    (ieeeSingleFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.mul)
      (x := (3 : ℝ))
      (y := (11184812 : ℝ) * (2 : ℝ) ^ (-25 : ℤ)) hfin)
  rw [hround]
  norm_num [BasicOp.exact, zpow_neg]

/-- The signed final error in Kahan's finite IEEE-single Problem 2.14 probe. -/
theorem problem2_14_ieeeSingle_kahan_probe_error :
    ieeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
        (ieeeSingleFormat.finiteRoundToEvenOp BasicOp.mul (3 : ℝ)
          (ieeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
            (ieeeSingleFormat.finiteRoundToEvenOp BasicOp.div (4 : ℝ) 3) 1)) 1 =
      (2 : ℝ) ^ (-23 : ℤ) := by
  rw [problem2_14_ieeeSingle_three_mul_four_thirds_minus_one]
  have hfin :
      ieeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.sub
          ((1 : ℝ) + (2 : ℝ) ^ (-23 : ℤ)) 1) := by
    change ieeeSingleFormat.finiteSystem
      (((1 : ℝ) + (2 : ℝ) ^ (-23 : ℤ)) - 1)
    have hnorm :
        ieeeSingleFormat.finiteSystem
          (ieeeSingleFormat.normalizedValue false 8388608 (-22)) :=
      problem2_14_ieeeSingle_normalizedValue_finiteSystem false 8388608 (-22)
        (by
          norm_num [ieeeSingleFormat, normalizedMantissa, mantissaInRange,
            minNormalMantissa])
        (by norm_num [ieeeSingleFormat, exponentInRange])
    convert hnorm using 1
    norm_num [ieeeSingleFormat, normalizedValue, signValue, betaR, zpow_neg]
  have hround :=
    (ieeeSingleFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem
      (op := BasicOp.sub)
      (x := (1 : ℝ) + (2 : ℝ) ^ (-23 : ℤ))
      (y := 1) hfin)
  simpa [BasicOp.exact, zpow_neg] using hround

/-- Absolute-value form of Kahan's finite IEEE-single Problem 2.14 probe. -/
def problem2_14_ieeeSingleKahanEstimate : ℝ :=
  |ieeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
      (ieeeSingleFormat.finiteRoundToEvenOp BasicOp.mul (3 : ℝ)
        (ieeeSingleFormat.finiteRoundToEvenOp BasicOp.sub
          (ieeeSingleFormat.finiteRoundToEvenOp BasicOp.div (4 : ℝ) 3) 1)) 1|

theorem problem2_14_ieeeSingleKahanEstimate_eq_machineEpsilon :
    problem2_14_ieeeSingleKahanEstimate = (2 : ℝ) ^ (-23 : ℤ) := by
  rw [problem2_14_ieeeSingleKahanEstimate,
    problem2_14_ieeeSingle_kahan_probe_error]
  norm_num [zpow_neg]

theorem problem2_14_ieeeSingleKahanEstimate_eq_two_unitRoundoff :
    problem2_14_ieeeSingleKahanEstimate =
      2 * ieeeSingleFormat.unitRoundoff := by
  rw [problem2_14_ieeeSingleKahanEstimate_eq_machineEpsilon,
    ieeeSingleFormat_unitRoundoff]
  norm_num [zpow_neg]

end FloatingPointFormat

end

end NumStability
