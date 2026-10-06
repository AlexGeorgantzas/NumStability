import NumStability.Source.Higham.Chapter02.Problem09.DoubleRounding.Counterexample.Results

/-!
# Chapter02 Problem12 ReciprocalProduct Basic

Canonical destination for material split out of
`NumStability.Analysis.Problem2_12` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

namespace FloatingPointFormat

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

end FloatingPointFormat
end NumStability

end
