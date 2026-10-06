-- Analysis/Problem2_5.lean
--
-- Problem-specific theorem surface for Higham Chapter 2, Problem 2.5.

import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import NumStability.Analysis.FloatingPointArithmetic

open scoped BigOperators

namespace NumStability

noncomputable section

namespace FloatingPointFormat

/-!
# Higham Chapter 2, Problem 2.5

Problem 2.5 asks for the repeating binary expansion of `0.1`, then for the
relative error of the IEEE-single rounded value.  The rounding statement below
uses the repository's finite round-to-even selector for the IEEE-single
finite-format tuple; it is not a full IEEE parser/operation result with flags.
-/

/-- The zero-indexed version of Higham Problem 2.5's repeating binary tail:
the source sum over `i = 1, 2, ...` becomes `n + 1` here. -/
def problem2_5_binaryOneTenthTerm (n : ℕ) : ℝ :=
  (1 / 16 : ℝ) ^ (n + 1) + (1 / 2 : ℝ) * (1 / 16 : ℝ) ^ (n + 1)

/-- Problem 2.5: the repeating `0001100...` binary tail sums to `0.1`. -/
theorem problem2_5_binaryOneTenth_hasSum :
    HasSum problem2_5_binaryOneTenthTerm (1 / 10 : ℝ) := by
  let r : ℝ := 1 / 16
  have hrnorm : ‖r‖ < 1 := by
    norm_num [r]
  have hgeom : HasSum (fun n : ℕ => r ^ n) (1 - r)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hrnorm
  have hshift_raw : HasSum (fun n : ℕ => r * r ^ n)
      (r * (1 - r)⁻¹) :=
    hgeom.mul_left r
  have hcongr : (fun n : ℕ => r * r ^ n) =
      fun n : ℕ => r ^ (n + 1) := by
    funext n
    rw [pow_succ']
  have hshift_tmp : HasSum (fun n : ℕ => r ^ (n + 1))
      (r * (1 - r)⁻¹) := by
    rw [← hcongr]
    exact hshift_raw
  have hshift : HasSum (fun n : ℕ => r ^ (n + 1)) (1 / 15 : ℝ) := by
    convert hshift_tmp using 1
    norm_num [r]
  have hhalf : HasSum (fun n : ℕ => (1 / 2 : ℝ) * r ^ (n + 1))
      ((1 / 2 : ℝ) * (1 / 15 : ℝ)) :=
    hshift.mul_left (1 / 2 : ℝ)
  have hadd := hshift.add hhalf
  have htarget :
      HasSum
        (fun n : ℕ => r ^ (n + 1) + (1 / 2 : ℝ) * r ^ (n + 1))
        (1 / 10 : ℝ) := by
    convert hadd using 1
    norm_num
  change
    HasSum
      (fun n : ℕ =>
        (1 / 16 : ℝ) ^ (n + 1) +
          (1 / 2 : ℝ) * (1 / 16 : ℝ) ^ (n + 1))
      (1 / 10 : ℝ)
  simpa [r] using htarget

/-- Problem 2.5 as a `tsum` identity. -/
theorem problem2_5_binaryOneTenth_tsum :
    (∑' n : ℕ, problem2_5_binaryOneTenthTerm n) = (1 / 10 : ℝ) :=
  problem2_5_binaryOneTenth_hasSum.tsum_eq

/-- The exact input `0.1` lies in the IEEE-single finite normal range. -/
theorem problem2_5_ieeeSingle_oneTenth_finiteNormalRange :
    ieeeSingleFormat.finiteNormalRange (1 / 10 : ℝ) := by
  constructor
  · rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 10)]
    norm_num [ieeeSingleFormat, minNormalMagnitude, betaR, zpow_neg]
  · rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 10)]
    have hmax : ieeeSingleFormat.maxFiniteMagnitude =
        (340282346638528859811704183484516925440 : ℝ) := by
      norm_num [ieeeSingleFormat, maxFiniteMagnitude, betaR, zpow_neg]
      rfl
    rw [hmax]
    norm_num

/-- Problem 2.5: finite IEEE-single round-to-even sends `0.1` to the upper
single-precision endpoint in its local bin. -/
theorem problem2_5_ieeeSingle_roundToEven_oneTenth :
    ieeeSingleFormat.finiteRoundToEven (1 / 10 : ℝ) =
      (13421773 : ℝ) * (2 : ℝ) ^ (-27 : ℤ) := by
  let fmt := ieeeSingleFormat
  let a : ℝ := fmt.normalizedValue false 13421772 (-3)
  let b : ℝ := fmt.normalizedValue false 13421773 (-3)
  let x : ℝ := (1 / 10 : ℝ)
  have hm : fmt.normalizedMantissa 13421772 := by
    norm_num [fmt, ieeeSingleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (13421772 + 1) := by
    norm_num [fmt, ieeeSingleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 13421772, (-3 : ℤ), hm, hmnext, Or.inl ⟨rfl, by
        norm_num [b]⟩⟩
  have ha_value : a = (13421772 : ℝ) * (2 : ℝ) ^ (-27 : ℤ) := by
    norm_num [a, fmt, ieeeSingleFormat, normalizedValue, signValue, betaR]
  have hb_value : b = (13421773 : ℝ) * (2 : ℝ) ^ (-27 : ℤ) := by
    norm_num [b, fmt, ieeeSingleFormat, normalizedValue, signValue, betaR]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      problem2_5_ieeeSingle_oneTenth_finiteNormalRange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value]
    have hxb : x - ((13421773 : ℝ) * (2 : ℝ) ^ (-27 : ℤ)) < 0 := by
      norm_num [x, zpow_neg]
    have hxa : 0 ≤ x - ((13421772 : ℝ) * (2 : ℝ) ^ (-27 : ℤ)) := by
      norm_num [x, zpow_neg]
    rw [abs_of_neg hxb, abs_of_nonneg hxa]
    norm_num [x, zpow_neg]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  simpa [x, fmt, hb_value] using hround

/-- Problem 2.5: the finite IEEE-single rounded value of `0.1` has relative
error `-u/4`, where `u = 2^-24`. -/
theorem problem2_5_ieeeSingle_oneTenth_relative_error :
    (((1 / 10 : ℝ) - ieeeSingleFormat.finiteRoundToEven (1 / 10 : ℝ)) /
        (1 / 10 : ℝ)) =
      -((1 / 4 : ℝ) * ieeeSingleFormat.unitRoundoff) := by
  rw [problem2_5_ieeeSingle_roundToEven_oneTenth,
    ieeeSingleFormat_unitRoundoff]
  norm_num [zpow_neg]

end FloatingPointFormat

end

end NumStability
