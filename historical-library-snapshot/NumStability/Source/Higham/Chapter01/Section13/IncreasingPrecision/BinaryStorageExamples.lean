-- NumStability/Source/Higham/Chapter01/Section13/IncreasingPrecision/BinaryStorageExamples.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Whole-owner block relocation.
-- Historical owner: `NumStability.Analysis.IncreasingPrecision`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import NumStability.Analysis.BeneficialRounding
import NumStability.Analysis.Error.Measures.ScalarDefinitions
import NumStability.Source.Higham.Chapter01.FloatingPointArithmetic.IncreasingPrecision

/-!
# BinaryStorageExamples

Relocated from `NumStability.Analysis.IncreasingPrecision` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


/-!
# Increasing precision (compatibility module)

Compatibility facade retained so existing imports of
`NumStability.Analysis.IncreasingPrecision`
keep resolving. Most declarations moved unchanged to the canonical Higham
Chapter 1 module imported above. Thirty-four declarations remain here because
their private identities or dependencies on shared modules require the original
module boundary. The module's original imports are re-stated so consumers
reaching identifiers transitively through this path retain the same surface.
-/

namespace NumStability

private theorem increasingPrecision_ieeeSingleFormat_minNormalMagnitude_le_two_thirds :
    FloatingPointFormat.ieeeSingleFormat.minNormalMagnitude ≤ (2 / 3 : ℝ) := by
  rw [FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.betaR]
  norm_num [zpow_neg]
private theorem increasingPrecision_two_thirds_le_ieeeSingleFormat_maxFiniteMagnitude :
    (2 / 3 : ℝ) ≤ FloatingPointFormat.ieeeSingleFormat.maxFiniteMagnitude := by
  rw [FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.betaR]
  norm_num [zpow_neg]
private theorem increasingPrecision_ieeeDoubleFormat_minNormalMagnitude_le_two_thirds :
    FloatingPointFormat.ieeeDoubleFormat.minNormalMagnitude ≤ (2 / 3 : ℝ) := by
  rw [FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.ieeeDoubleFormat,
    FloatingPointFormat.betaR]
  norm_num [zpow_neg]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ 1022 := by positivity
  apply (inv_le_iff_one_le_mul₀ hpos).2
  have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ 1022 := by
    calc
      (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
      _ ≤ (2 : ℝ) ^ 1022 :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (1 : ℕ) ≤ 1022)
  have hmul :
      (2 / 3 : ℝ) * 2 ≤ (2 / 3 : ℝ) * (2 : ℝ) ^ 1022 :=
    mul_le_mul_of_nonneg_left hpow (by norm_num)
  exact le_trans (by norm_num : (1 : ℝ) ≤ (2 / 3 : ℝ) * 2) hmul
private theorem increasingPrecision_two_thirds_le_ieeeDoubleFormat_maxFiniteMagnitude :
    (2 / 3 : ℝ) ≤ FloatingPointFormat.ieeeDoubleFormat.maxFiniteMagnitude := by
  rw [FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.ieeeDoubleFormat,
    FloatingPointFormat.betaR]
  norm_num [zpow_neg]
  have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ 1024 := by
    calc
      (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
      _ ≤ (2 : ℝ) ^ 1024 :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (1 : ℕ) ≤ 1024)
  have hfrac_nonneg :
      0 ≤ (9007199254740991 : ℝ) / 9007199254740992 := by norm_num
  have hprod :=
    mul_le_mul_of_nonneg_right hpow hfrac_nonneg
  have hsmall :
      (2 / 3 : ℝ) ≤
      2 * ((9007199254740991 : ℝ) / 9007199254740992) := by
    norm_num
  exact hsmall.trans hprod
private theorem increasingPrecision_ieeeSingleFormat_minNormalMagnitude_le_one_seventh :
    FloatingPointFormat.ieeeSingleFormat.minNormalMagnitude ≤ (1 / 7 : ℝ) := by
  rw [FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.betaR]
  norm_num [zpow_neg]
private theorem increasingPrecision_ieeeDoubleFormat_minNormalMagnitude_le_one_seventh :
    FloatingPointFormat.ieeeDoubleFormat.minNormalMagnitude ≤ (1 / 7 : ℝ) := by
  rw [FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.ieeeDoubleFormat,
    FloatingPointFormat.betaR]
  norm_num [zpow_neg]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ 1022 := by positivity
  apply (inv_le_iff_one_le_mul₀ hpos).2
  have hpow : (7 : ℝ) ≤ (2 : ℝ) ^ 1022 := by
    calc
      (7 : ℝ) ≤ (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (2 : ℝ) ^ 1022 :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (3 : ℕ) ≤ 1022)
  have hmul :
      (1 / 7 : ℝ) * 7 ≤ (1 / 7 : ℝ) * (2 : ℝ) ^ 1022 :=
    mul_le_mul_of_nonneg_left hpow (by norm_num)
  exact le_trans (by norm_num : (1 : ℝ) ≤ (1 / 7 : ℝ) * 7) hmul
private theorem increasingPrecision_ieeeSingle_two_thirds_finiteNormalRange :
    FloatingPointFormat.ieeeSingleFormat.finiteNormalRange (2 / 3 : ℝ) := by
  rw [FloatingPointFormat.finiteNormalRange,
    abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)]
  exact ⟨increasingPrecision_ieeeSingleFormat_minNormalMagnitude_le_two_thirds,
    increasingPrecision_two_thirds_le_ieeeSingleFormat_maxFiniteMagnitude⟩
private theorem increasingPrecision_ieeeDouble_two_thirds_finiteNormalRange :
    FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange (2 / 3 : ℝ) := by
  rw [FloatingPointFormat.finiteNormalRange,
    abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)]
  exact ⟨increasingPrecision_ieeeDoubleFormat_minNormalMagnitude_le_two_thirds,
    increasingPrecision_two_thirds_le_ieeeDoubleFormat_maxFiniteMagnitude⟩
private theorem increasingPrecision_ieeeSingle_one_seventh_finiteNormalRange :
    FloatingPointFormat.ieeeSingleFormat.finiteNormalRange (1 / 7 : ℝ) := by
  rw [FloatingPointFormat.finiteNormalRange,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 7)]
  exact ⟨increasingPrecision_ieeeSingleFormat_minNormalMagnitude_le_one_seventh,
    (by norm_num : (1 / 7 : ℝ) ≤ 2 / 3).trans
      increasingPrecision_two_thirds_le_ieeeSingleFormat_maxFiniteMagnitude⟩
private theorem increasingPrecision_ieeeDouble_one_seventh_finiteNormalRange :
    FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange (1 / 7 : ℝ) := by
  rw [FloatingPointFormat.finiteNormalRange,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 7)]
  exact ⟨increasingPrecision_ieeeDoubleFormat_minNormalMagnitude_le_one_seventh,
    (by norm_num : (1 / 7 : ℝ) ≤ 2 / 3).trans
      increasingPrecision_two_thirds_le_ieeeDoubleFormat_maxFiniteMagnitude⟩
private theorem increasingPrecision_two_le_ieeeSingleFormat_maxFiniteMagnitude :
    (2 : ℝ) ≤ FloatingPointFormat.ieeeSingleFormat.maxFiniteMagnitude := by
  rw [FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.ieeeSingleFormat,
    FloatingPointFormat.betaR]
  norm_num [zpow_neg]
/-- A concrete local spacing instance for the §1.13 sine example.  At the
binary32 finite point `x = 1`, the source perturbation `10^-8*sin(2^24*x)` is
too small to reach either adjacent binary32 endpoint, so finite round-to-even
returns `1`. -/
theorem increasingPrecisionSinExampleSource_ieeeSingle_roundToEven_one :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEven
      (increasingPrecisionSinExampleSource 1) = (1 : ℝ) := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let s : ℝ := increasingPrecisionSinExampleSource 1
  let pred : ℝ := fmt.normalizedValue false fmt.maxNormalMantissa 0
  let succ : ℝ := fmt.normalizedValue false (fmt.minNormalMantissa + 1) 1
  have hpert : |s - 1| ≤ 1 / (10 : ℝ) ^ 8 := by
    simpa [s] using increasingPrecisionSinExampleSource_perturbation_abs_le (1 : ℝ)
  have hs_lower : 1 - 1 / (10 : ℝ) ^ 8 ≤ s := by
    have h := (abs_le.mp hpert).1
    linarith
  have hs_upper : s ≤ 1 + 1 / (10 : ℝ) ^ 8 := by
    have h := (abs_le.mp hpert).2
    linarith
  have hs_pos : 0 < s := by
    linarith [hs_lower, (by norm_num : (0 : ℝ) < 1 - 1 / (10 : ℝ) ^ 8)]
  have hgap_pred : 2 / (10 : ℝ) ^ 8 < (2 : ℝ) ^ (-24 : ℤ) := by
    norm_num [zpow_neg]
  have hgap_succ : 2 / (10 : ℝ) ^ 8 < (2 : ℝ) ^ (-23 : ℤ) := by
    norm_num [zpow_neg]
  have hgap_pred_single : 1 / (10 : ℝ) ^ 8 < (2 : ℝ) ^ (-24 : ℤ) := by
    norm_num [zpow_neg]
  have hgap_succ_single : 1 / (10 : ℝ) ^ 8 < (2 : ℝ) ^ (-23 : ℤ) := by
    norm_num [zpow_neg]
  have hpred_val : pred = 1 - (2 : ℝ) ^ (-24 : ℤ) := by
    norm_num [pred, fmt, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.minNormalMantissa, zpow_neg]
  have hsucc_val : succ = 1 + (2 : ℝ) ^ (-23 : ℤ) := by
    norm_num [succ, fmt, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.minNormalMantissa, zpow_neg]
  have hpred_lt_s : pred < s := by
    rw [hpred_val]
    have hpred_bound :
        1 - (2 : ℝ) ^ (-24 : ℤ) < 1 - 1 / (10 : ℝ) ^ 8 := by
      linarith [hgap_pred_single]
    exact lt_of_lt_of_le hpred_bound hs_lower
  have hs_lt_succ : s < succ := by
    rw [hsucc_val]
    have hsucc_bound :
        1 + 1 / (10 : ℝ) ^ 8 < 1 + (2 : ℝ) ^ (-23 : ℤ) := by
      linarith [hgap_succ_single]
    exact lt_of_le_of_lt hs_upper hsucc_bound
  have hnormal : fmt.finiteNormalRange s := by
    rw [FloatingPointFormat.finiteNormalRange, abs_of_pos hs_pos]
    constructor
    · have htwo_thirds_le_s : (2 / 3 : ℝ) ≤ s := by
        linarith [hs_lower]
      exact
        (increasingPrecision_ieeeSingleFormat_minNormalMagnitude_le_two_thirds).trans
          htwo_thirds_le_s
    · have hs_le_two : s ≤ (2 : ℝ) := by
        linarith [hs_upper]
      exact hs_le_two.trans increasingPrecision_two_le_ieeeSingleFormat_maxFiniteMagnitude
  have hpolicy :
      fmt.sourceRoundToEvenEvidence s (fmt.finiteRoundToEven s) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hnormal
  have hone_unbounded : fmt.unboundedNormalizedSystem (1 : ℝ) := by
    refine ⟨false, fmt.minNormalMantissa, (1 : ℤ),
      fmt.minNormalMantissa_normalized, ?_⟩
    norm_num [fmt, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.minNormalMantissa, zpow_neg]
    rfl
  rcases lt_trichotomy s (1 : ℝ) with hs_lt_one | hs_eq_one | hone_lt_s
  · have hboundary : fmt.boundaryAdjacentNormalized pred (1 : ℝ) := by
      refine ⟨false, (0 : ℤ), Or.inl ⟨rfl, ?_⟩⟩
      norm_num [fmt, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.minNormalMantissa, zpow_neg]
      rfl
    have hadj : fmt.realOrderAdjacentNormalized pred (1 : ℝ) :=
      fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
    have hrightCloser : |s - 1| < |s - pred| := by
      have hsp_pos : 0 < s - pred := sub_pos.mpr hpred_lt_s
      have hpred_dist : 1 / (10 : ℝ) ^ 8 < |s - pred| := by
        rw [abs_of_pos hsp_pos, hpred_val]
        linarith
      exact lt_of_le_of_lt hpert hpred_dist
    have hsel :=
      FloatingPointFormat.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
        hpolicy hadj ⟨hpred_lt_s, hs_lt_one⟩ hrightCloser
    simpa [fmt, s] using hsel
  · have hself :=
      let hpolicy_one :
          fmt.sourceRoundToEvenEvidence (1 : ℝ) (fmt.finiteRoundToEven s) := by
        simpa [hs_eq_one] using hpolicy
      FloatingPointFormat.sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem
        hone_unbounded hpolicy_one
    simpa [fmt, s, hs_eq_one] using hself
  · have hmnext : fmt.normalizedMantissa (fmt.minNormalMantissa + 1) := by
      norm_num [fmt, FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.minNormalMantissa]
    have hsame : fmt.sameExponentAdjacentNormalized (1 : ℝ) succ := by
      refine ⟨false, fmt.minNormalMantissa, (1 : ℤ),
        fmt.minNormalMantissa_normalized, hmnext, Or.inl ⟨?_, rfl⟩⟩
      norm_num [fmt, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue, FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa,
        FloatingPointFormat.minNormalMantissa, zpow_neg]
      rfl
    have hadj : fmt.realOrderAdjacentNormalized (1 : ℝ) succ :=
      fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hsame
    have hleftCloser : |s - 1| < |s - succ| := by
      have hss_pos : 0 < succ - s := sub_pos.mpr hs_lt_succ
      have hsucc_dist : 1 / (10 : ℝ) ^ 8 < |s - succ| := by
        rw [abs_of_neg (sub_neg.mpr hs_lt_succ), hsucc_val]
        linarith
      exact lt_of_le_of_lt hpert hsucc_dist
    have hsel :=
      FloatingPointFormat.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
        hpolicy hadj ⟨hone_lt_s, hs_lt_succ⟩ hleftCloser
    simpa [fmt, s] using hsel
/-- Concrete IEEE-single round-to-even storage of the source input `1/7` in
the §1.13 sine example.  The stored value is the upper adjacent binary32
endpoint. -/
theorem increasingPrecision_ieeeSingle_roundToEven_one_seventh :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEven (1 / 7 : ℝ) =
      (9586981 : ℝ) * (2 : ℝ) ^ (-26 : ℤ) := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let a : ℝ := fmt.normalizedValue false 9586980 (-2)
  let b : ℝ := fmt.normalizedValue false 9586981 (-2)
  let x : ℝ := (1 / 7 : ℝ)
  have hm : fmt.normalizedMantissa 9586980 := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (9586980 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 9586980, (-2 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value :
      a = (9586980 : ℝ) * (2 : ℝ) ^ (-26 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hb_value :
      b = (9586981 : ℝ) * (2 : ℝ) ^ (-26 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      increasingPrecision_ieeeSingle_one_seventh_finiteNormalRange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  simpa [x, fmt, hb_value] using hround
/-- Concrete IEEE-double round-to-even storage of the source input `1/7` in
the §1.13 sine example.  The stored value is the lower adjacent binary64
endpoint. -/
theorem increasingPrecision_ieeeDouble_roundToEven_one_seventh :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (1 / 7 : ℝ) =
      (5146971002709138 : ℝ) * (2 : ℝ) ^ (-55 : ℤ) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false 5146971002709138 (-2)
  let b : ℝ := fmt.normalizedValue false 5146971002709139 (-2)
  let x : ℝ := (1 / 7 : ℝ)
  have hm : fmt.normalizedMantissa 5146971002709138 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (5146971002709138 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 5146971002709138, (-2 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, rfl⟩⟩
  have ha_value :
      a = (5146971002709138 : ℝ) * (2 : ℝ) ^ (-55 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hb_value :
      b = (5146971002709139 : ℝ) * (2 : ℝ) ^ (-55 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      increasingPrecision_ieeeDouble_one_seventh_finiteNormalRange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [x, fmt, ha_value] using hround
/-- Exact IEEE-single storage error for the §1.13 sine-example source input
`x = 1/7`. -/
theorem increasingPrecision_ieeeSingle_roundToEven_one_seventh_error :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEven (1 / 7 : ℝ) -
      (1 / 7 : ℝ) =
      3 / (7 * (2 : ℝ) ^ 26) := by
  rw [increasingPrecision_ieeeSingle_roundToEven_one_seventh]
  norm_num [zpow_neg]
/-- Exact IEEE-double storage error for the §1.13 sine-example source input
`x = 1/7`. -/
theorem increasingPrecision_ieeeDouble_roundToEven_one_seventh_error :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (1 / 7 : ℝ) -
      (1 / 7 : ℝ) =
      -2 / (7 * (2 : ℝ) ^ 55) := by
  rw [increasingPrecision_ieeeDouble_roundToEven_one_seventh]
  norm_num [zpow_neg]
/-- Any dyadic grid value `z/2^t` is separated from `1/7` by at least
`1/(7*2^t)`.  This is the arithmetic core behind the §1.13 observation that
coarse binary precision is dominated by the representation of `x = 1/7`. -/
theorem increasingPrecision_one_seventh_binary_grid_abs_error_ge
    (z : ℤ) (t : ℕ) :
    1 / (7 * (2 : ℝ) ^ t) ≤
      |(z : ℝ) / (2 : ℝ) ^ t - 1 / 7| := by
  have hpow_pos : 0 < (2 : ℝ) ^ t := by positivity
  have hden_pos : 0 < 7 * (2 : ℝ) ^ t := by positivity
  have hnum_ne : 7 * z - (2 : ℤ) ^ t ≠ 0 := by
    intro hzero
    have hmul : (2 : ℤ) ^ t = 7 * z := by omega
    have hdiv_int : (7 : ℤ) ∣ (2 : ℤ) ^ t := by
      exact ⟨z, hmul⟩
    have hdiv_nat : (7 : ℕ) ∣ 2 ^ t := by
      exact_mod_cast hdiv_int
    exact seven_not_dvd_two_pow_nat t hdiv_nat
  have hnum_abs_int : (1 : ℤ) ≤ |7 * z - (2 : ℤ) ^ t| :=
    Int.one_le_abs hnum_ne
  have hnum_abs_real :
      (1 : ℝ) ≤ |((7 * z - (2 : ℤ) ^ t : ℤ) : ℝ)| := by
    exact_mod_cast hnum_abs_int
  have hrewrite :
      (z : ℝ) / (2 : ℝ) ^ t - 1 / 7 =
        ((7 * z - (2 : ℤ) ^ t : ℤ) : ℝ) /
          (7 * (2 : ℝ) ^ t) := by
    field_simp [ne_of_gt hpow_pos]
    norm_num [Int.cast_pow]
    ring
  rw [hrewrite, abs_div, abs_of_pos hden_pos]
  exact div_le_div_of_nonneg_right hnum_abs_real (le_of_lt hden_pos)
/-- For every dyadic grid value with denominator `2^t`, `t <= 20`, the
representation error for `1/7` is larger than the source sine amplitude
`10^{-8}`.  This closes the non-enumerative arithmetic part of the §1.13
"dominated by representing `x = 1/7`" sentence. -/
theorem increasingPrecision_one_seventh_binary_grid_abs_error_gt_scale_of_t_le_twenty
    (z : ℤ) {t : ℕ} (ht : t ≤ 20) :
    increasingPrecisionSinExampleScale <
      |(z : ℝ) / (2 : ℝ) ^ t - 1 / 7| := by
  have hgrid := increasingPrecision_one_seventh_binary_grid_abs_error_ge z t
  have hpow_le : (2 : ℝ) ^ t ≤ (2 : ℝ) ^ 20 :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ht
  have hden_le : 7 * (2 : ℝ) ^ t ≤ 7 * (2 : ℝ) ^ 20 := by
    nlinarith
  have hlower :
      1 / (7 * (2 : ℝ) ^ 20) ≤ 1 / (7 * (2 : ℝ) ^ t) :=
    one_div_le_one_div_of_le (by positivity) hden_le
  have hscale :
      increasingPrecisionSinExampleScale < 1 / (7 * (2 : ℝ) ^ 20) := by
    norm_num [increasingPrecisionSinExampleScale]
  exact lt_of_lt_of_le hscale (hgrid.trans' hlower)
/-- The exact dyadic-amplitude threshold behind the §1.13 `x = 1/7`
dominance statement: through denominator exponent `t = 23`, the universal
grid-separation lower bound still exceeds the source sine amplitude `10^{-8}`.
-/
theorem increasingPrecision_one_seventh_binary_grid_abs_error_gt_scale_of_t_le_twenty_three
    (z : ℤ) {t : ℕ} (ht : t ≤ 23) :
    increasingPrecisionSinExampleScale <
      |(z : ℝ) / (2 : ℝ) ^ t - 1 / 7| := by
  have hgrid := increasingPrecision_one_seventh_binary_grid_abs_error_ge z t
  have hpow_le : (2 : ℝ) ^ t ≤ (2 : ℝ) ^ 23 :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ht
  have hden_le : 7 * (2 : ℝ) ^ t ≤ 7 * (2 : ℝ) ^ 23 := by
    nlinarith
  have hlower :
      1 / (7 * (2 : ℝ) ^ 23) ≤ 1 / (7 * (2 : ℝ) ^ t) :=
    one_div_le_one_div_of_le (by positivity) hden_le
  have hscale :
      increasingPrecisionSinExampleScale < 1 / (7 * (2 : ℝ) ^ 23) := by
    norm_num [increasingPrecisionSinExampleScale]
  exact lt_of_lt_of_le hscale (hgrid.trans' hlower)
/-- For every dyadic stored input `z/2^t` with `t <= 20`, the sine perturbation
in the source example is smaller than the input-representation error for
`x = 1/7`.  This is the direct formal version of the §1.13 early-precision
"dominated by representing `x = 1/7`" mechanism. -/
theorem increasingPrecisionSinExampleSource_perturbation_lt_one_seventh_binary_grid_error_of_t_le_twenty
    (z : ℤ) {t : ℕ} (ht : t ≤ 20) :
    |increasingPrecisionSinExampleSource ((z : ℝ) / (2 : ℝ) ^ t) -
      (z : ℝ) / (2 : ℝ) ^ t| <
      |(z : ℝ) / (2 : ℝ) ^ t - 1 / 7| := by
  exact lt_of_le_of_lt
    (increasingPrecisionSinExampleSource_perturbation_abs_le
      ((z : ℝ) / (2 : ℝ) ^ t))
    (increasingPrecision_one_seventh_binary_grid_abs_error_gt_scale_of_t_le_twenty
      z ht)
/-- The sharper dyadic-threshold version of the source's early-precision
dominance sentence: for every stored input `z/2^t` through `t = 23`, the sine
perturbation is smaller than the representation error for `x = 1/7`. -/
theorem increasingPrecisionSinExampleSource_perturbation_lt_one_seventh_binary_grid_error_of_t_le_twenty_three
    (z : ℤ) {t : ℕ} (ht : t ≤ 23) :
    |increasingPrecisionSinExampleSource ((z : ℝ) / (2 : ℝ) ^ t) -
      (z : ℝ) / (2 : ℝ) ^ t| <
      |(z : ℝ) / (2 : ℝ) ^ t - 1 / 7| := by
  exact lt_of_le_of_lt
    (increasingPrecisionSinExampleSource_perturbation_abs_le
      ((z : ℝ) / (2 : ℝ) ^ t))
    (increasingPrecision_one_seventh_binary_grid_abs_error_gt_scale_of_t_le_twenty_three
      z ht)
/-- Concrete IEEE-single round-to-even storage of the source input `2/3`.
The stored value is the upper adjacent binary32 endpoint. -/
theorem increasingPrecision_ieeeSingle_roundToEven_two_thirds :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEven (2 / 3 : ℝ) =
      (11184811 : ℝ) * (2 : ℝ) ^ (-24 : ℤ) := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let a : ℝ := fmt.normalizedValue false 11184810 0
  let b : ℝ := fmt.normalizedValue false 11184811 0
  let x : ℝ := (2 / 3 : ℝ)
  have hm : fmt.normalizedMantissa 11184810 := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (11184810 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 11184810, (0 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value :
      a = (11184810 : ℝ) * (2 : ℝ) ^ (-24 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hb_value :
      b = (11184811 : ℝ) * (2 : ℝ) ^ (-24 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      increasingPrecision_ieeeSingle_two_thirds_finiteNormalRange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  simpa [x, fmt, hb_value] using hround
/-- Concrete IEEE-double round-to-even storage of the source input `2/3`.
The stored value is the lower adjacent binary64 endpoint. -/
theorem increasingPrecision_ieeeDouble_roundToEven_two_thirds :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (2 / 3 : ℝ) =
      (6004799503160661 : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false 6004799503160661 0
  let b : ℝ := fmt.normalizedValue false 6004799503160662 0
  let x : ℝ := (2 / 3 : ℝ)
  have hm : fmt.normalizedMantissa 6004799503160661 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (6004799503160661 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 6004799503160661, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, rfl⟩⟩
  have ha_value :
      a = (6004799503160661 : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hb_value :
      b = (6004799503160662 : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      increasingPrecision_ieeeDouble_two_thirds_finiteNormalRange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [x, fmt, ha_value] using hround
/-- The branch variable produced by the concrete IEEE-single stored `2/3`. -/
theorem increasingPrecisionExampleY_ieeeSingle_roundToEven_two_thirds :
    increasingPrecisionExampleY
        (FloatingPointFormat.ieeeSingleFormat.finiteRoundToEven (2 / 3 : ℝ)) =
      (2 : ℝ) ^ (-24 : ℤ) / 25 := by
  rw [increasingPrecision_ieeeSingle_roundToEven_two_thirds]
  norm_num [increasingPrecisionExampleY, zpow_neg]
/-- The branch variable produced by the concrete IEEE-double stored `2/3`. -/
theorem increasingPrecisionExampleY_ieeeDouble_roundToEven_two_thirds :
    increasingPrecisionExampleY
        (FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (2 / 3 : ℝ)) =
      (2 : ℝ) ^ (-53 : ℤ) / 25 := by
  rw [increasingPrecision_ieeeDouble_roundToEven_two_thirds]
  norm_num [increasingPrecisionExampleY, zpow_neg]
private theorem increasingPrecision_ieeeSingle_exp_branch_y_finiteNormalRange :
    FloatingPointFormat.ieeeSingleFormat.finiteNormalRange
      (Real.exp ((2 : ℝ) ^ (-24 : ℤ) / 25)) := by
  rw [FloatingPointFormat.finiteNormalRange,
    abs_of_pos (Real.exp_pos _)]
  constructor
  · exact le_trans
      (by
        rw [FloatingPointFormat.minNormalMagnitude,
          FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
        norm_num [zpow_neg] :
          FloatingPointFormat.ieeeSingleFormat.minNormalMagnitude ≤ (1 : ℝ))
      (by
        have hle := Real.exp_le_exp.mpr
          (by norm_num [zpow_neg] : (0 : ℝ) ≤ (2 : ℝ) ^ (-24 : ℤ) / 25)
        simpa using hle)
  · exact le_trans
      (by
        have hlt : Real.exp ((2 : ℝ) ^ (-24 : ℤ) / 25) < 2 := by
          let y : ℝ := (2 : ℝ) ^ (-24 : ℤ) / 25
          have hy_nonneg : 0 ≤ y := by norm_num [y, zpow_neg]
          have hy_abs : |y| ≤ 1 := by norm_num [y, zpow_neg]
          have hbound := Real.abs_exp_sub_one_le (x := y) hy_abs
          have hdiff_nonneg : 0 ≤ Real.exp y - 1 := by
            have hle := Real.exp_le_exp.mpr hy_nonneg
            simpa using hle
          have hdiff_le : Real.exp y - 1 ≤ 2 * y := by
            have hy_abs_eq : |y| = y := abs_of_nonneg hy_nonneg
            rw [abs_of_nonneg hdiff_nonneg, hy_abs_eq] at hbound
            exact hbound
          have hsmall : 2 * y < 1 := by norm_num [y, zpow_neg]
          have : Real.exp y < 2 := by linarith
          simpa [y] using this
        exact hlt.le)
      (by
        rw [FloatingPointFormat.maxFiniteMagnitude,
          FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
        norm_num [zpow_neg] :
          (2 : ℝ) ≤ FloatingPointFormat.ieeeSingleFormat.maxFiniteMagnitude)
private theorem increasingPrecision_ieeeDouble_exp_branch_y_finiteNormalRange :
    FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      (Real.exp ((2 : ℝ) ^ (-53 : ℤ) / 25)) := by
  rw [FloatingPointFormat.finiteNormalRange,
    abs_of_pos (Real.exp_pos _)]
  constructor
  · exact le_trans
      (by
        rw [FloatingPointFormat.minNormalMagnitude,
          FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
        norm_num [zpow_neg]
        have hpos : (0 : ℝ) < (2 : ℝ) ^ 1022 := by positivity
        apply (inv_le_iff_one_le_mul₀ hpos).2
        have hpow0 : (1 : ℝ) ≤ (2 : ℝ) ^ 1022 := by
          have hpow' : (2 : ℝ) ^ 0 ≤ (2 : ℝ) ^ 1022 :=
            pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
              (by norm_num : (0 : ℕ) ≤ 1022)
          simpa using hpow'
        simpa using hpow0 :
          FloatingPointFormat.ieeeDoubleFormat.minNormalMagnitude ≤ (1 : ℝ))
      (by
        have hle := Real.exp_le_exp.mpr
          (by norm_num [zpow_neg] : (0 : ℝ) ≤ (2 : ℝ) ^ (-53 : ℤ) / 25)
        simpa using hle)
  · exact le_trans
      (by
        have hlt : Real.exp ((2 : ℝ) ^ (-53 : ℤ) / 25) < 2 := by
          let y : ℝ := (2 : ℝ) ^ (-53 : ℤ) / 25
          have hy_nonneg : 0 ≤ y := by norm_num [y, zpow_neg]
          have hy_abs : |y| ≤ 1 := by norm_num [y, zpow_neg]
          have hbound := Real.abs_exp_sub_one_le (x := y) hy_abs
          have hdiff_nonneg : 0 ≤ Real.exp y - 1 := by
            have hle := Real.exp_le_exp.mpr hy_nonneg
            simpa using hle
          have hdiff_le : Real.exp y - 1 ≤ 2 * y := by
            have hy_abs_eq : |y| = y := abs_of_nonneg hy_nonneg
            rw [abs_of_nonneg hdiff_nonneg, hy_abs_eq] at hbound
            exact hbound
          have hsmall : 2 * y < 1 := by norm_num [y, zpow_neg]
          have : Real.exp y < 2 := by linarith
          simpa [y] using this
        exact hlt.le)
      (by
        rw [FloatingPointFormat.maxFiniteMagnitude,
          FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
        norm_num [zpow_neg]
        have hpow' : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ 1024 :=
          pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
            (by norm_num : (2 : ℕ) ≤ 1024)
        have hpow : (4 : ℝ) ≤ (2 : ℝ) ^ 1024 := by
          norm_num at hpow'
          exact hpow'
        have hfrac_nonneg :
            0 ≤ (9007199254740991 : ℝ) / 9007199254740992 := by norm_num
        have hprod :=
          mul_le_mul_of_nonneg_right hpow hfrac_nonneg
        have hsmall :
            (2 : ℝ) ≤
              4 * ((9007199254740991 : ℝ) / 9007199254740992) := by
          norm_num
        exact hsmall.trans hprod :
          (2 : ℝ) ≤ FloatingPointFormat.ieeeDoubleFormat.maxFiniteMagnitude)
private theorem increasingPrecision_exp_single_branch_y_lt_half_ulp :
    Real.exp ((2 : ℝ) ^ (-24 : ℤ) / 25) < 1 + (2 : ℝ) ^ (-24 : ℤ) := by
  let y : ℝ := (2 : ℝ) ^ (-24 : ℤ) / 25
  have hy_nonneg : 0 ≤ y := by norm_num [y, zpow_neg]
  have hy_abs : |y| ≤ 1 := by norm_num [y, zpow_neg]
  have hbound := Real.abs_exp_sub_one_le (x := y) hy_abs
  have hdiff_nonneg : 0 ≤ Real.exp y - 1 := by
    have hle := Real.exp_le_exp.mpr hy_nonneg
    simpa using hle
  have hdiff_le : Real.exp y - 1 ≤ 2 * y := by
    have hy_abs_eq : |y| = y := abs_of_nonneg hy_nonneg
    rw [abs_of_nonneg hdiff_nonneg, hy_abs_eq] at hbound
    exact hbound
  have hsmall : 2 * y < (2 : ℝ) ^ (-24 : ℤ) := by
    norm_num [y, zpow_neg]
  have hlt : Real.exp y < 1 + (2 : ℝ) ^ (-24 : ℤ) := by
    linarith
  simpa [y] using hlt
private theorem increasingPrecision_exp_double_branch_y_lt_half_ulp :
    Real.exp ((2 : ℝ) ^ (-53 : ℤ) / 25) < 1 + (2 : ℝ) ^ (-53 : ℤ) := by
  let y : ℝ := (2 : ℝ) ^ (-53 : ℤ) / 25
  have hy_nonneg : 0 ≤ y := by norm_num [y, zpow_neg]
  have hy_abs : |y| ≤ 1 := by norm_num [y, zpow_neg]
  have hbound := Real.abs_exp_sub_one_le (x := y) hy_abs
  have hdiff_nonneg : 0 ≤ Real.exp y - 1 := by
    have hle := Real.exp_le_exp.mpr hy_nonneg
    simpa using hle
  have hdiff_le : Real.exp y - 1 ≤ 2 * y := by
    have hy_abs_eq : |y| = y := abs_of_nonneg hy_nonneg
    rw [abs_of_nonneg hdiff_nonneg, hy_abs_eq] at hbound
    exact hbound
  have hsmall : 2 * y < (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [y, zpow_neg]
  have hlt : Real.exp y < 1 + (2 : ℝ) ^ (-53 : ℤ) := by
    linarith
  simpa [y] using hlt
/-- The correctly rounded IEEE-single finite exponential of the concrete
stored-input branch variable is `1`. -/
theorem increasingPrecision_ieeeSingle_roundToEven_exp_branch_y_eq_one :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEven
        (Real.exp ((2 : ℝ) ^ (-24 : ℤ) / 25)) = 1 := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let a : ℝ := fmt.normalizedValue false 8388608 1
  let b : ℝ := fmt.normalizedValue false 8388609 1
  let x : ℝ := Real.exp ((2 : ℝ) ^ (-24 : ℤ) / 25)
  have hm : fmt.normalizedMantissa 8388608 := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (8388608 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 8388608, (1 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value : a = 1 := by
    norm_num [a, fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
    rfl
  have hb_value : b = 1 + (2 : ℝ) ^ (-23 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hx_gt : 1 < x := by
    have hy_pos : (0 : ℝ) < (2 : ℝ) ^ (-24 : ℤ) / 25 := by
      norm_num [zpow_neg]
    simpa [x] using Real.one_lt_exp_iff.mpr hy_pos
  have hx_half : x < 1 + (2 : ℝ) ^ (-24 : ℤ) := by
    simpa [x] using increasingPrecision_exp_single_branch_y_lt_half_ulp
  have hx_lt_b : x < b := by
    rw [hb_value]
    have hpow : (2 : ℝ) ^ (-24 : ℤ) < (2 : ℝ) ^ (-23 : ℤ) := by
      norm_num [zpow_neg]
    linarith
  have hstrict : a < x ∧ x < b := by
    exact ⟨by simpa [ha_value] using hx_gt, hx_lt_b⟩
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      increasingPrecision_ieeeSingle_exp_branch_y_finiteNormalRange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value]
    have hxb_nonpos : x - (1 + (2 : ℝ) ^ (-23 : ℤ)) ≤ 0 := by
      linarith
    have hx1_nonneg : 0 ≤ x - 1 := by
      linarith
    rw [abs_of_nonneg hx1_nonneg, abs_of_nonpos hxb_nonpos]
    have hpow : (2 : ℝ) ^ (-23 : ℤ) = 2 * (2 : ℝ) ^ (-24 : ℤ) := by
      norm_num [zpow_neg]
    rw [hpow]
    linarith
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [x, fmt, ha_value] using hround
/-- The correctly rounded IEEE-double finite exponential of the concrete
stored-input branch variable is `1`. -/
theorem increasingPrecision_ieeeDouble_roundToEven_exp_branch_y_eq_one :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven
        (Real.exp ((2 : ℝ) ^ (-53 : ℤ) / 25)) = 1 := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false 4503599627370496 1
  let b : ℝ := fmt.normalizedValue false 4503599627370497 1
  let x : ℝ := Real.exp ((2 : ℝ) ^ (-53 : ℤ) / 25)
  have hm : fmt.normalizedMantissa 4503599627370496 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (4503599627370496 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 4503599627370496, (1 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, rfl⟩⟩
  have ha_value : a = 1 := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
    rfl
  have hb_value : b = 1 + (2 : ℝ) ^ (-52 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hx_gt : 1 < x := by
    have hy_pos : (0 : ℝ) < (2 : ℝ) ^ (-53 : ℤ) / 25 := by
      norm_num [zpow_neg]
    simpa [x] using Real.one_lt_exp_iff.mpr hy_pos
  have hx_half : x < 1 + (2 : ℝ) ^ (-53 : ℤ) := by
    simpa [x] using increasingPrecision_exp_double_branch_y_lt_half_ulp
  have hx_lt_b : x < b := by
    rw [hb_value]
    have hpow : (2 : ℝ) ^ (-53 : ℤ) < (2 : ℝ) ^ (-52 : ℤ) := by
      norm_num [zpow_neg]
    linarith
  have hstrict : a < x ∧ x < b := by
    exact ⟨by simpa [ha_value] using hx_gt, hx_lt_b⟩
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      increasingPrecision_ieeeDouble_exp_branch_y_finiteNormalRange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value]
    have hxb_nonpos : x - (1 + (2 : ℝ) ^ (-52 : ℤ)) ≤ 0 := by
      linarith
    have hx1_nonneg : 0 ≤ x - 1 := by
      linarith
    rw [abs_of_nonneg hx1_nonneg, abs_of_nonpos hxb_nonpos]
    have hpow : (2 : ℝ) ^ (-52 : ℤ) = 2 * (2 : ℝ) ^ (-53 : ℤ) := by
      norm_num [zpow_neg]
    rw [hpow]
    linarith
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [x, fmt, ha_value] using hround
/-- Concrete correctly rounded IEEE-single/double finite-`exp` instance of the
§1.13 branch example.  The stored source inputs give branch variables
`2^-24/25` and `2^-53/25`; correctly rounded finite exponentials of both
variables are `1`, so both modeled precision runs return `0` with relative
error `1` against the exact value `f(2/3)=1`. -/
theorem increasingPrecisionExampleElse_two_precision_failure_of_ieee_roundToEven_stored_exp_source :
    increasingPrecisionExampleElseWithExpHat
        (increasingPrecisionExampleY
          (FloatingPointFormat.ieeeSingleFormat.finiteRoundToEven (2 / 3 : ℝ)))
        (FloatingPointFormat.ieeeSingleFormat.finiteRoundToEven
          (Real.exp (increasingPrecisionExampleY
            (FloatingPointFormat.ieeeSingleFormat.finiteRoundToEven (2 / 3 : ℝ))))) = 0 ∧
    increasingPrecisionExampleElseWithExpHat
        (increasingPrecisionExampleY
          (FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (2 / 3 : ℝ)))
        (FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven
          (Real.exp (increasingPrecisionExampleY
            (FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (2 / 3 : ℝ))))) = 0 ∧
    relError
      (increasingPrecisionExampleElseWithExpHat
        (increasingPrecisionExampleY
          (FloatingPointFormat.ieeeSingleFormat.finiteRoundToEven (2 / 3 : ℝ)))
        (FloatingPointFormat.ieeeSingleFormat.finiteRoundToEven
          (Real.exp (increasingPrecisionExampleY
            (FloatingPointFormat.ieeeSingleFormat.finiteRoundToEven (2 / 3 : ℝ))))))
      (increasingPrecisionExampleExactZ (2 / 3)) = 1 ∧
    relError
      (increasingPrecisionExampleElseWithExpHat
        (increasingPrecisionExampleY
          (FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (2 / 3 : ℝ)))
        (FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven
          (Real.exp (increasingPrecisionExampleY
            (FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (2 / 3 : ℝ))))))
      (increasingPrecisionExampleExactZ (2 / 3)) = 1 := by
  rw [increasingPrecisionExampleY_ieeeSingle_roundToEven_two_thirds,
    increasingPrecisionExampleY_ieeeDouble_roundToEven_two_thirds,
    increasingPrecision_ieeeSingle_roundToEven_exp_branch_y_eq_one,
    increasingPrecision_ieeeDouble_roundToEven_exp_branch_y_eq_one]
  exact increasingPrecisionExampleElse_two_precision_failure_of_expHat_one
    (by norm_num [zpow_neg])
    (by norm_num [zpow_neg])
/-- IEEE-single and IEEE-double finite stored inputs cannot be exactly `2/3`;
therefore the §1.13 branch example enters the nonzero-`y` path for both stored
inputs.  Under the still-supplied hypothesis that each exponential evaluation
returns `1`, both modeled precision runs return `0` with relative error `1`.
This discharges the binary-storage part of the source story, not the hidden
Fortran `exp` routine trace. -/
theorem increasingPrecisionExampleElse_two_precision_failure_of_ieee_finite_stored_inputs_expHat_one
    {xSingle xDouble : ℝ}
    (hSingle :
      FloatingPointFormat.finiteSystem FloatingPointFormat.ieeeSingleFormat xSingle)
    (hDouble :
      FloatingPointFormat.finiteSystem FloatingPointFormat.ieeeDoubleFormat xDouble) :
    increasingPrecisionExampleElseWithExpHat (increasingPrecisionExampleY xSingle) 1 = 0 ∧
    increasingPrecisionExampleElseWithExpHat (increasingPrecisionExampleY xDouble) 1 = 0 ∧
    relError
      (increasingPrecisionExampleElseWithExpHat (increasingPrecisionExampleY xSingle) 1)
      (increasingPrecisionExampleExactZ (2 / 3)) = 1 ∧
    relError
      (increasingPrecisionExampleElseWithExpHat (increasingPrecisionExampleY xDouble) 1)
      (increasingPrecisionExampleExactZ (2 / 3)) = 1 := by
  have hSingle_ne : xSingle ≠ 2 / 3 := by
    intro hx
    exact two_thirds_not_ieeeSingleFiniteSystem (by simpa [hx] using hSingle)
  have hDouble_ne : xDouble ≠ 2 / 3 := by
    intro hx
    exact two_thirds_not_ieeeDoubleFiniteSystem (by simpa [hx] using hDouble)
  exact increasingPrecisionExampleElse_two_precision_failure_of_stored_inputs_expHat_one
    hSingle_ne hDouble_ne
/-- Source-shaped finite round-to-even storage instance of the §1.13 branch
example.  The IEEE-single and IEEE-double round-to-even stored versions of
`2/3` are finite, hence not exactly `2/3`; if each subsequent exponential
evaluation is supplied as `1`, both modeled runs return `0` with relative
error `1`. -/
theorem increasingPrecisionExampleElse_two_precision_failure_of_ieee_roundToEven_stored_source_expHat_one :
    increasingPrecisionExampleElseWithExpHat
        (increasingPrecisionExampleY
          (FloatingPointFormat.ieeeSingleFormat.finiteRoundToEven (2 / 3 : ℝ))) 1 = 0 ∧
    increasingPrecisionExampleElseWithExpHat
        (increasingPrecisionExampleY
          (FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (2 / 3 : ℝ))) 1 = 0 ∧
    relError
      (increasingPrecisionExampleElseWithExpHat
        (increasingPrecisionExampleY
          (FloatingPointFormat.ieeeSingleFormat.finiteRoundToEven (2 / 3 : ℝ))) 1)
      (increasingPrecisionExampleExactZ (2 / 3)) = 1 ∧
    relError
      (increasingPrecisionExampleElseWithExpHat
        (increasingPrecisionExampleY
          (FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (2 / 3 : ℝ))) 1)
      (increasingPrecisionExampleExactZ (2 / 3)) = 1 := by
  exact
    increasingPrecisionExampleElse_two_precision_failure_of_ieee_finite_stored_inputs_expHat_one
      (FloatingPointFormat.ieeeSingleFormat.finiteRoundToEven_finiteSystem (2 / 3 : ℝ))
      (FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven_finiteSystem (2 / 3 : ℝ))

end NumStability
