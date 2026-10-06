-- Analysis/Problem2_12.lean
--
-- Problem-specific theorem surface for Higham Chapter 2, Problem 2.12.

import NumStability.Analysis.Problem2_10

namespace NumStability

noncomputable section

namespace FloatingPointFormat

/-!
# Higham Chapter 2, Problem 2.12

Problem 2.12 asks for Edelman's IEEE-double fact that, for a floating-point
`x` with `1 < x < 2`, the rounded computation `fl(x*(1/x))` is either `1` or
`1 - eps/2`, where `eps = 2^-52` is machine epsilon.

The theorems below close that result for the repository's finite real-valued
IEEE-double operation wrapper: any exact product in the half-ulp window
`[1 - 2^-53, 1 + 2^-53]` rounds to one of the two displayed values, and the
rounded-reciprocal product `x * fl(1/x)` lies in that window whenever
`1 < x < 2`.  Full IEEE instruction semantics with flags, traps, signed zeros,
infinities, and NaNs remain outside this real-valued wrapper.
-/

theorem problem2_12_ieeeDouble_predecessor_normalized :
    ieeeDoubleFormat.normalizedExponentRepresentation
      ((1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ)) 0 := by
  refine ⟨false, ieeeDoubleFormat.maxNormalMantissa, ?_, ?_, ?_⟩
  · exact ieeeDoubleFormat.maxNormalMantissa_normalized
  · norm_num [ieeeDoubleFormat, exponentInRange]
  · norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR,
      maxNormalMantissa, zpow_neg]

theorem problem2_12_ieeeDouble_one_normalized :
    ieeeDoubleFormat.normalizedExponentRepresentation (1 : ℝ) 1 := by
  refine ⟨false, ieeeDoubleFormat.minNormalMantissa, ?_, ?_, ?_⟩
  · exact ieeeDoubleFormat.minNormalMantissa_normalized
  · norm_num [ieeeDoubleFormat, exponentInRange]
  · norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR,
      minNormalMantissa, zpow_neg]
    rfl

theorem problem2_12_ieeeDouble_predecessor_finiteSystem :
    ieeeDoubleFormat.finiteSystem ((1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ)) :=
  Or.inr (Or.inl
    (ieeeDoubleFormat.normalizedExponentRepresentation_normalizedSystem
      problem2_12_ieeeDouble_predecessor_normalized))

theorem problem2_12_ieeeDouble_one_finiteSystem :
    ieeeDoubleFormat.finiteSystem (1 : ℝ) :=
  Or.inr (Or.inl
    (ieeeDoubleFormat.normalizedExponentRepresentation_normalizedSystem
      problem2_12_ieeeDouble_one_normalized))

theorem problem2_12_ieeeDouble_rounds_predecessor_to_self :
    ieeeDoubleFormat.finiteRoundToEven
      ((1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ)) =
        (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) :=
  ieeeDoubleFormat.finiteRoundToEven_eq_self_of_finiteSystem
    problem2_12_ieeeDouble_predecessor_finiteSystem

theorem problem2_12_ieeeDouble_rounds_one_to_self :
    ieeeDoubleFormat.finiteRoundToEven (1 : ℝ) = (1 : ℝ) :=
  ieeeDoubleFormat.finiteRoundToEven_eq_self_of_finiteSystem
    problem2_12_ieeeDouble_one_finiteSystem

private theorem problem2_12_ieeeDoubleFormat_minNormalMagnitude_le_half :
    ieeeDoubleFormat.minNormalMagnitude ≤ (1 / 2 : ℝ) := by
  norm_num [ieeeDoubleFormat, minNormalMagnitude, betaR, zpow_neg]
  have hden : (2 : ℝ) ≤ (2 : ℝ) ^ (1022 : ℕ) := by
    exact le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (1022 : ℕ) ≠ 0)
  simpa [one_div] using
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hden

private theorem problem2_12_four_le_ieeeDoubleFormat_maxFiniteMagnitude :
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

/-- The upper midpoint between `1` and the next double ties to the even
endpoint `1`. -/
theorem problem2_12_ieeeDouble_upper_midpoint_rounds_to_one :
    ieeeDoubleFormat.finiteRoundToEven
        ((1 : ℝ) + (2 : ℝ) ^ (-53 : ℤ)) = (1 : ℝ) := by
  let fmt := ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false fmt.minNormalMantissa 1
  let b : ℝ := fmt.normalizedValue false (fmt.minNormalMantissa + 1) 1
  let x : ℝ := (1 : ℝ) + (2 : ℝ) ^ (-53 : ℤ)
  have hm : fmt.normalizedMantissa fmt.minNormalMantissa :=
    fmt.minNormalMantissa_normalized
  have hmnext : fmt.normalizedMantissa (fmt.minNormalMantissa + 1) := by
    norm_num [fmt, ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, fmt.minNormalMantissa, (1 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, rfl⟩⟩
  have ha_value : a = (1 : ℝ) := by
    norm_num [a, fmt, ieeeDoubleFormat, normalizedValue, signValue, betaR,
      minNormalMantissa, zpow_neg]
    rfl
  have hb_value : b = (1 : ℝ) + (2 : ℝ) ^ (-52 : ℤ) := by
    norm_num [b, fmt, ieeeDoubleFormat, normalizedValue, signValue, betaR,
      minNormalMantissa, zpow_neg]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [finiteNormalRange]
    have hxnonneg : 0 ≤ x := by norm_num [x, zpow_neg]
    rw [abs_of_nonneg hxnonneg]
    constructor
    · have hhalf : (1 / 2 : ℝ) ≤ x := by norm_num [x, zpow_neg]
      exact le_trans problem2_12_ieeeDoubleFormat_minNormalMagnitude_le_half hhalf
    · exact le_trans (by norm_num [x, zpow_neg] : x ≤ 2)
        (le_trans (by norm_num : (2 : ℝ) ≤ (4 : ℝ))
          (by
            simpa [fmt] using
              problem2_12_four_le_ieeeDoubleFormat_maxFiniteMagnitude))
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleft : a = fmt.normalizedValue false fmt.minNormalMantissa (1 : ℤ) := rfl
  have htie : |x - a| = |x - b| := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have heven : evenMantissa fmt.minNormalMantissa := by
    norm_num [fmt, ieeeDoubleFormat, minNormalMantissa, evenMantissa]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_tie_even
      hpolicy hadj hstrict hm hleft htie heven
  simpa [x, fmt, ha_value] using hround

theorem problem2_12_ieeeDouble_rounds_to_predecessor_of_mem_lower_half_cell
    {z : ℝ}
    (hzrange : ieeeDoubleFormat.finiteNormalRange z)
    (hlo : (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) ≤ z)
    (hhi : z < (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ)) :
    ieeeDoubleFormat.finiteRoundToEven z =
      (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) := by
  by_cases hzpre : z = (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ)
  · rw [hzpre]
    exact problem2_12_ieeeDouble_rounds_predecessor_to_self
  let fmt := ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false fmt.maxNormalMantissa 0
  let b : ℝ := fmt.normalizedValue false fmt.minNormalMantissa 1
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
  have hpre_lt_z : (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) < z :=
    lt_of_le_of_ne hlo (Ne.symm hzpre)
  have hz_lt_one : z < (1 : ℝ) := by
    have hmid_lt_one :
        (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) < 1 := by
      norm_num [zpow_neg]
    exact lt_trans hhi hmid_lt_one
  have hstrict : a < z ∧ z < b := by
    rw [ha_value, hb_value]
    exact ⟨hpre_lt_z, hz_lt_one⟩
  have hpolicy :
      fmt.sourceRoundToEvenEvidence z (fmt.finiteRoundToEven z) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hzrange
  have hleftCloser : |z - a| < |z - b| := by
    rw [ha_value, hb_value]
    have hza : 0 ≤ z - ((1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ)) :=
      sub_nonneg.mpr hlo
    have hzb : z - (1 : ℝ) < 0 := sub_neg.mpr hz_lt_one
    rw [abs_of_nonneg hza, abs_of_neg hzb]
    norm_num [zpow_neg] at hhi ⊢
    linarith
  have hround : fmt.finiteRoundToEven z = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [fmt, ha_value] using hround

theorem problem2_12_ieeeDouble_rounds_to_one_of_mem_lower_middle_half_cell
    {z : ℝ}
    (hzrange : ieeeDoubleFormat.finiteNormalRange z)
    (hlo : (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) ≤ z)
    (hhi : z ≤ (1 : ℝ)) :
    ieeeDoubleFormat.finiteRoundToEven z = (1 : ℝ) := by
  by_cases hzmid : z = (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ)
  · rw [hzmid]
    exact problem2_9_double_rounds_extended_midpoint_to_one
  by_cases hzone : z = (1 : ℝ)
  · rw [hzone]
    exact problem2_12_ieeeDouble_rounds_one_to_self
  let fmt := ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false fmt.maxNormalMantissa 0
  let b : ℝ := fmt.normalizedValue false fmt.minNormalMantissa 1
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
  have hmid_lt_z : (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) < z :=
    lt_of_le_of_ne hlo (Ne.symm hzmid)
  have hpre_lt_mid :
      (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) <
        (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) := by
    norm_num [zpow_neg]
  have hpre_lt_z : (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) < z :=
    lt_trans hpre_lt_mid hmid_lt_z
  have hz_lt_one : z < (1 : ℝ) :=
    lt_of_le_of_ne hhi hzone
  have hstrict : a < z ∧ z < b := by
    rw [ha_value, hb_value]
    exact ⟨hpre_lt_z, hz_lt_one⟩
  have hpolicy :
      fmt.sourceRoundToEvenEvidence z (fmt.finiteRoundToEven z) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hzrange
  have hrightCloser : |z - b| < |z - a| := by
    rw [ha_value, hb_value]
    have hza : 0 ≤ z - ((1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ)) :=
      sub_nonneg.mpr (le_of_lt hpre_lt_z)
    have hzb : z - (1 : ℝ) < 0 := sub_neg.mpr hz_lt_one
    rw [abs_of_nonneg hza, abs_of_neg hzb]
    norm_num [zpow_neg] at hmid_lt_z ⊢
    linarith
  have hround : fmt.finiteRoundToEven z = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  simpa [fmt, hb_value] using hround

theorem problem2_12_ieeeDouble_rounds_to_one_of_mem_upper_half_cell
    {z : ℝ}
    (hzrange : ieeeDoubleFormat.finiteNormalRange z)
    (hlo : (1 : ℝ) ≤ z)
    (hhi : z ≤ (1 : ℝ) + (2 : ℝ) ^ (-53 : ℤ)) :
    ieeeDoubleFormat.finiteRoundToEven z = (1 : ℝ) := by
  by_cases hzone : z = (1 : ℝ)
  · rw [hzone]
    exact problem2_12_ieeeDouble_rounds_one_to_self
  by_cases hzupper : z = (1 : ℝ) + (2 : ℝ) ^ (-53 : ℤ)
  · rw [hzupper]
    exact problem2_12_ieeeDouble_upper_midpoint_rounds_to_one
  let fmt := ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false fmt.minNormalMantissa 1
  let b : ℝ := fmt.normalizedValue false (fmt.minNormalMantissa + 1) 1
  have hm : fmt.normalizedMantissa fmt.minNormalMantissa :=
    fmt.minNormalMantissa_normalized
  have hmnext : fmt.normalizedMantissa (fmt.minNormalMantissa + 1) := by
    norm_num [fmt, ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, fmt.minNormalMantissa, (1 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, rfl⟩⟩
  have ha_value : a = (1 : ℝ) := by
    norm_num [a, fmt, ieeeDoubleFormat, normalizedValue, signValue, betaR,
      minNormalMantissa, zpow_neg]
    rfl
  have hb_value : b = (1 : ℝ) + (2 : ℝ) ^ (-52 : ℤ) := by
    norm_num [b, fmt, ieeeDoubleFormat, normalizedValue, signValue, betaR,
      minNormalMantissa, zpow_neg]
  have hone_lt_z : (1 : ℝ) < z := lt_of_le_of_ne hlo (Ne.symm hzone)
  have z_lt_upper : z < (1 : ℝ) + (2 : ℝ) ^ (-53 : ℤ) :=
    lt_of_le_of_ne hhi hzupper
  have hupper_lt_next :
      (1 : ℝ) + (2 : ℝ) ^ (-53 : ℤ) <
        (1 : ℝ) + (2 : ℝ) ^ (-52 : ℤ) := by
    norm_num [zpow_neg]
  have hz_lt_next : z < (1 : ℝ) + (2 : ℝ) ^ (-52 : ℤ) :=
    lt_trans z_lt_upper hupper_lt_next
  have hstrict : a < z ∧ z < b := by
    rw [ha_value, hb_value]
    exact ⟨hone_lt_z, hz_lt_next⟩
  have hpolicy :
      fmt.sourceRoundToEvenEvidence z (fmt.finiteRoundToEven z) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hzrange
  have hleftCloser : |z - a| < |z - b| := by
    rw [ha_value, hb_value]
    have hza : 0 ≤ z - (1 : ℝ) := sub_nonneg.mpr hlo
    have hzb : z - ((1 : ℝ) + (2 : ℝ) ^ (-52 : ℤ)) < 0 :=
      sub_neg.mpr hz_lt_next
    rw [abs_of_nonneg hza, abs_of_neg hzb]
    norm_num [zpow_neg] at z_lt_upper ⊢
    linarith
  have hround : fmt.finiteRoundToEven z = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [fmt, ha_value] using hround

/-- Final-rounding half of Problem 2.12: any finite-normal exact product in
the half-ulp window around `1` rounds to either `1 - eps/2` or `1`, where
`eps = 2^-52`. -/
theorem problem2_12_ieeeDouble_final_rounding_options_of_mem_window
    {z : ℝ}
    (hzrange : ieeeDoubleFormat.finiteNormalRange z)
    (hlo : (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) ≤ z)
    (hhi : z ≤ (1 : ℝ) + (2 : ℝ) ^ (-53 : ℤ)) :
    ieeeDoubleFormat.finiteRoundToEven z =
        (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) ∨
      ieeeDoubleFormat.finiteRoundToEven z = (1 : ℝ) := by
  by_cases hlt_mid : z < (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ)
  · exact Or.inl
      (problem2_12_ieeeDouble_rounds_to_predecessor_of_mem_lower_half_cell
        hzrange hlo hlt_mid)
  · have hmid_le : (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) ≤ z :=
      le_of_not_gt hlt_mid
    by_cases hz_le_one : z ≤ (1 : ℝ)
    · exact Or.inr
        (problem2_12_ieeeDouble_rounds_to_one_of_mem_lower_middle_half_cell
          hzrange hmid_le hz_le_one)
    · have hone_le : (1 : ℝ) ≤ z := le_of_lt (lt_of_not_ge hz_le_one)
      exact Or.inr
        (problem2_12_ieeeDouble_rounds_to_one_of_mem_upper_half_cell
          hzrange hone_le hhi)

/-- For the source range `1 < x < 2`, the exact reciprocal is in IEEE-double's
finite normal range. -/
theorem problem2_12_ieeeDouble_reciprocal_finiteNormalRange_of_one_lt_x_lt_two
    {x : ℝ} (hxlo : (1 : ℝ) < x) (hxhi : x < (2 : ℝ)) :
    ieeeDoubleFormat.finiteNormalRange ((1 : ℝ) / x) := by
  have hxpos : 0 < x := lt_trans zero_lt_one hxlo
  have hrecip_pos : 0 < (1 : ℝ) / x := one_div_pos.mpr hxpos
  rw [finiteNormalRange, abs_of_pos hrecip_pos]
  constructor
  · have hhalf_lt : (1 / 2 : ℝ) < (1 : ℝ) / x := by
      simpa using one_div_lt_one_div_of_lt hxpos hxhi
    exact le_trans problem2_12_ieeeDoubleFormat_minNormalMagnitude_le_half
      (le_of_lt hhalf_lt)
  · have hone_le : (1 : ℝ) / x ≤ 1 := by
      have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
        (le_of_lt hxlo)
      simpa using h
    exact le_trans hone_le
      (le_trans (by norm_num : (1 : ℝ) ≤ 4)
        problem2_12_four_le_ieeeDoubleFormat_maxFiniteMagnitude)

/-- The rounded reciprocal, multiplied back by `x`, lies in exactly the
half-ulp window needed by Edelman's Problem 2.12. -/
theorem problem2_12_ieeeDouble_reciprocal_product_mem_window_of_one_lt_x_lt_two
    {x : ℝ} (hxlo : (1 : ℝ) < x) (hxhi : x < (2 : ℝ)) :
    ieeeDoubleFormat.finiteNormalRange
        (x * ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div 1 x) ∧
      (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) ≤
        x * ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div 1 x ∧
      x * ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div 1 x ≤
        (1 : ℝ) + (2 : ℝ) ^ (-53 : ℤ) := by
  have hxpos : 0 < x := lt_trans zero_lt_one hxlo
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hrecipRange :
      ieeeDoubleFormat.finiteNormalRange ((1 : ℝ) / x) :=
    problem2_12_ieeeDouble_reciprocal_finiteNormalRange_of_one_lt_x_lt_two
      hxlo hxhi
  rcases
    ieeeDoubleFormat.finiteRoundToEvenOp_signedRelErrorWitness_lt_of_finiteNormalRange
      (op := BasicOp.div) (x := (1 : ℝ)) (y := x) hrecipRange with
    ⟨δ, _hround, hδ, hwit⟩
  have hδabs :
      |δ| ≤ (2 : ℝ) ^ (-53 : ℤ) := by
    exact le_of_lt (by
      simpa [ieeeDoubleFormat_unitRoundoff] using hδ)
  have hδlo : -((2 : ℝ) ^ (-53 : ℤ)) ≤ δ := (abs_le.mp hδabs).1
  have hδhi : δ ≤ (2 : ℝ) ^ (-53 : ℤ) := (abs_le.mp hδabs).2
  have hz_eq :
      x * ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div 1 x = 1 + δ := by
    unfold signedRelErrorWitness at hwit
    rw [hwit]
    change x * (((1 : ℝ) / x) * (1 + δ)) = 1 + δ
    field_simp [hxne]
  have hzlo :
      (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) ≤
        x * ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div 1 x := by
    rw [hz_eq]
    linarith
  have hzhi :
      x * ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div 1 x ≤
        (1 : ℝ) + (2 : ℝ) ^ (-53 : ℤ) := by
    rw [hz_eq]
    linarith
  have hzpos :
      0 < x * ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div 1 x := by
    rw [hz_eq]
    norm_num [zpow_neg] at hδlo ⊢
    linarith
  have hzrange :
      ieeeDoubleFormat.finiteNormalRange
        (x * ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div 1 x) := by
    rw [finiteNormalRange, abs_of_pos hzpos]
    constructor
    · have hhalf_le :
          (1 / 2 : ℝ) ≤
            x * ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div 1 x := by
        rw [hz_eq]
        norm_num [zpow_neg] at hδlo ⊢
        linarith
      exact le_trans problem2_12_ieeeDoubleFormat_minNormalMagnitude_le_half
        hhalf_le
    · have hle_two :
          x * ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div 1 x ≤
            (2 : ℝ) := by
        rw [hz_eq]
        norm_num [zpow_neg] at hδhi ⊢
        linarith
      exact le_trans hle_two
        (le_trans (by norm_num : (2 : ℝ) ≤ 4)
          problem2_12_four_le_ieeeDoubleFormat_maxFiniteMagnitude)
  exact ⟨hzrange, hzlo, hzhi⟩

/-- Problem 2.12, closed for the repository's finite real-valued IEEE-double
operation wrapper: if `1 < x < 2`, then the rounded computation
`fl(x * fl(1/x))` is either `1 - eps/2` or `1`, where `eps = 2^-52`. -/
theorem problem2_12_ieeeDouble_reciprocal_product_rounding_options
    {x : ℝ} (hxlo : (1 : ℝ) < x) (hxhi : x < (2 : ℝ)) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul x
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div 1 x) =
          (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) ∨
      ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul x
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div 1 x) =
          (1 : ℝ) := by
  rcases
    problem2_12_ieeeDouble_reciprocal_product_mem_window_of_one_lt_x_lt_two
      hxlo hxhi with
    ⟨hzrange, hzlo, hzhi⟩
  change
    ieeeDoubleFormat.finiteRoundToEven
        (x * ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div 1 x) =
          (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) ∨
      ieeeDoubleFormat.finiteRoundToEven
        (x * ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div 1 x) =
          (1 : ℝ)
  exact
    problem2_12_ieeeDouble_final_rounding_options_of_mem_window
      hzrange hzlo hzhi

end FloatingPointFormat

end

end NumStability
