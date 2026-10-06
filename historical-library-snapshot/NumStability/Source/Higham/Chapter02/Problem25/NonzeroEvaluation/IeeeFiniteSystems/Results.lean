-- NumStability/Source/Higham/Chapter02/Problem25/NonzeroEvaluation/IeeeFiniteSystems/Results.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Whole-owner block relocation.
-- Historical owner: `NumStability.Analysis.Problem2_24`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Source.Higham.Chapter02.Problem10.DivisionRoundTrip.ExhaustiveBinary64.Results
import NumStability.Source.Higham.Chapter02.Problem25.NonzeroEvaluation.Basic

/-!
# Results

Relocated from `NumStability.Analysis.Problem2_24` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


/-!
# Problem2_24 (compatibility module)

Historical path, retained so existing imports of `NumStability.Analysis.Problem2_24`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

noncomputable section

namespace NumStability

namespace FloatingPointFormat

private theorem problem2_24_ieeeSingleFormat_minNormalMagnitude_le_one_third :
    ieeeSingleFormat.minNormalMagnitude ≤ (1 / 3 : ℝ) := by
  norm_num [ieeeSingleFormat, minNormalMagnitude, betaR, zpow_neg]

private theorem problem2_24_one_le_ieeeSingleFormat_maxFiniteMagnitude :
    (1 : ℝ) ≤ ieeeSingleFormat.maxFiniteMagnitude := by
  rw [maxFiniteMagnitude, ieeeSingleFormat, betaR]
  change (1 : ℝ) ≤ (2 : ℝ) ^ (128 : ℤ) *
    (1 - (2 : ℝ) ^ (-24 : ℤ))
  have hfactor : (1 / 2 : ℝ) ≤ 1 - (2 : ℝ) ^ (-24 : ℤ) := by
    rw [zpow_neg]
    have hden : (2 : ℝ) ≤ (2 : ℝ) ^ (24 : ℕ) := by
      exact le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (24 : ℕ) ≠ 0)
    have hinv : 1 / ((2 : ℝ) ^ (24 : ℕ)) ≤ 1 / (2 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hden
    norm_num at hinv ⊢
  have hpow_nat : (2 : ℝ) ≤ (2 : ℝ) ^ (128 : ℕ) := by
    exact le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (128 : ℕ) ≠ 0)
  have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ (128 : ℤ) := by
    simpa [zpow_natCast] using hpow_nat
  have hmul := mul_le_mul hpow hfactor
    (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
    (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (128 : ℤ))
  simpa using hmul

private theorem problem2_24_ieeeSingle_oneThird_finiteNormalRange :
    ieeeSingleFormat.finiteNormalRange (1 / 3 : ℝ) := by
  rw [finiteNormalRange]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3)]
  constructor
  · exact problem2_24_ieeeSingleFormat_minNormalMagnitude_le_one_third
  · exact le_trans (by norm_num : (1 / 3 : ℝ) ≤ 1)
      problem2_24_one_le_ieeeSingleFormat_maxFiniteMagnitude

/-- IEEE-single finite round-to-even sends `1/3` to the upper adjacent
single-precision value. -/
theorem problem2_24_ieeeSingle_oneThird_rounds_to_upper :
    ieeeSingleFormat.finiteRoundToEven (1 / 3 : ℝ) =
      (11184811 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) := by
  let fmt := ieeeSingleFormat
  let a : ℝ := fmt.normalizedValue false 11184810 (-1)
  let b : ℝ := fmt.normalizedValue false 11184811 (-1)
  let x : ℝ := (1 / 3 : ℝ)
  have hm : fmt.normalizedMantissa 11184810 := by
    norm_num [fmt, ieeeSingleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (11184810 + 1) := by
    norm_num [fmt, ieeeSingleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 11184810, (-1 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value :
      a = (11184810 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) := by
    norm_num [a, fmt, ieeeSingleFormat, normalizedValue, signValue, betaR,
      zpow_neg]
  have hb_value :
      b = (11184811 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) := by
    norm_num [b, fmt, ieeeSingleFormat, normalizedValue, signValue, betaR,
      zpow_neg]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      problem2_24_ieeeSingle_oneThird_finiteNormalRange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  simpa [x, fmt, hb_value] using hround

theorem problem2_24_ieeeSingle_one_third_not_finiteSystem :
    ¬ ieeeSingleFormat.finiteSystem (1 / 3 : ℝ) := by
  intro hfin
  have hfix :
      ieeeSingleFormat.finiteRoundToEven (1 / 3 : ℝ) = (1 / 3 : ℝ) :=
    ieeeSingleFormat.finiteRoundToEven_eq_self_of_finiteSystem hfin
  rw [problem2_24_ieeeSingle_oneThird_rounds_to_upper] at hfix
  norm_num [zpow_neg] at hfix

theorem problem2_24_ieeeDouble_one_third_not_finiteSystem :
    ¬ ieeeDoubleFormat.finiteSystem (1 / 3 : ℝ) := by
  intro hfin
  have hfix :
      ieeeDoubleFormat.finiteRoundToEven (1 / 3 : ℝ) = (1 / 3 : ℝ) :=
    ieeeDoubleFormat.finiteRoundToEven_eq_self_of_finiteSystem hfin
  rw [problem2_10_ieeeDouble_oneThird_rounds_to_lower] at hfix
  norm_num [zpow_neg] at hfix

theorem problem2_24_ieeeSingle_finiteSystem_ne_one_third {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x) :
    x ≠ (1 / 3 : ℝ) := by
  intro hxthird
  exact problem2_24_ieeeSingle_one_third_not_finiteSystem (by
    simpa [hxthird] using hx)

theorem problem2_24_ieeeDouble_finiteSystem_ne_one_third {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x) :
    x ≠ (1 / 3 : ℝ) := by
  intro hxthird
  exact problem2_24_ieeeDouble_one_third_not_finiteSystem (by
    simpa [hxthird] using hx)

theorem problem2_24_ieeeSingle_upper_neighbor_le_of_finiteSystem_of_one_third_le
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hge : (1 / 3 : ℝ) ≤ x) :
    (11184811 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) ≤ x := by
  have hgt : (1 / 3 : ℝ) < x :=
    lt_of_le_of_ne hge
      (Ne.symm (problem2_24_ieeeSingle_finiteSystem_ne_one_third hx))
  exact
    problem2_24_ieeeSingle_upper_neighbor_le_of_finiteSystem_of_one_third_lt
      hx hgt

theorem problem2_24_ieeeDouble_upper_neighbor_le_of_finiteSystem_of_one_third_le
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hge : (1 / 3 : ℝ) ≤ x) :
    (6004799503160662 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) ≤ x := by
  have hgt : (1 / 3 : ℝ) < x :=
    lt_of_le_of_ne hge
      (Ne.symm (problem2_24_ieeeDouble_finiteSystem_ne_one_third hx))
  exact
    problem2_24_ieeeDouble_upper_neighbor_le_of_finiteSystem_of_one_third_lt
      hx hgt

theorem problem2_24_ieeeSingle_exactExpr_ne_zero_of_finiteSystem {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x) :
    problem2_24_exactExpr x ≠ 0 :=
  problem2_24_exactExpr_ne_zero_of_ne_one_third
    (problem2_24_ieeeSingle_finiteSystem_ne_one_third hx)

theorem problem2_24_ieeeDouble_exactExpr_ne_zero_of_finiteSystem {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x) :
    problem2_24_exactExpr x ≠ 0 :=
  problem2_24_exactExpr_ne_zero_of_ne_one_third
    (problem2_24_ieeeDouble_finiteSystem_ne_one_third hx)

/-- Problem 2.24, exact-intermediate IEEE-single branch. -/
theorem problem2_24_ieeeSingle_eval_ne_zero_of_finiteSystem_intermediates
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (h1 : ieeeSingleFormat.finiteSystem (x - (1 / 2 : ℝ)))
    (h2 : ieeeSingleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x))
    (h3 : ieeeSingleFormat.finiteSystem
      (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)))
    (h4 : ieeeSingleFormat.finiteSystem
      ((((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x)) :
    ieeeSingleFormat.problem2_24_eval x ≠ 0 := by
  refine
    ieeeSingleFormat.problem2_24_eval_ne_zero_of_finiteSystem_intermediates_of_ne_one_third
      ?_ h1 h2 h3 h4
  exact problem2_24_ieeeSingle_finiteSystem_ne_one_third hx

/-- Problem 2.24, exact-intermediate IEEE-double branch. -/
theorem problem2_24_ieeeDouble_eval_ne_zero_of_finiteSystem_intermediates
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (h1 : ieeeDoubleFormat.finiteSystem (x - (1 / 2 : ℝ)))
    (h2 : ieeeDoubleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x))
    (h3 : ieeeDoubleFormat.finiteSystem
      (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)))
    (h4 : ieeeDoubleFormat.finiteSystem
      ((((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x)) :
    ieeeDoubleFormat.problem2_24_eval x ≠ 0 := by
  refine
    ieeeDoubleFormat.problem2_24_eval_ne_zero_of_finiteSystem_intermediates_of_ne_one_third
      ?_ h1 h2 h3 h4
  exact problem2_24_ieeeDouble_finiteSystem_ne_one_third hx

/-- Problem 2.24, IEEE-single zero-result branch audit.  Any finite single
input producing zero in the modeled path must leave the exact-intermediate
branch at one of the four displayed exact real intermediates. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_implies_exists_nonfinite_exact_intermediate
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    ¬ ieeeSingleFormat.finiteSystem (x - (1 / 2 : ℝ)) ∨
      ¬ ieeeSingleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x) ∨
      ¬ ieeeSingleFormat.finiteSystem
        (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) ∨
      ¬ ieeeSingleFormat.finiteSystem
        ((((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x) :=
  ieeeSingleFormat.problem2_24_eval_eq_zero_implies_exists_nonfinite_exact_intermediate_of_ne_one_third
    (problem2_24_ieeeSingle_finiteSystem_ne_one_third hx) hzero

/-- Problem 2.24, IEEE-double zero-result branch audit.  Any finite double
input producing zero in the modeled path must leave the exact-intermediate
branch at one of the four displayed exact real intermediates. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_implies_exists_nonfinite_exact_intermediate
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    ¬ ieeeDoubleFormat.finiteSystem (x - (1 / 2 : ℝ)) ∨
      ¬ ieeeDoubleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x) ∨
      ¬ ieeeDoubleFormat.finiteSystem
        (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) ∨
      ¬ ieeeDoubleFormat.finiteSystem
        ((((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x) :=
  ieeeDoubleFormat.problem2_24_eval_eq_zero_implies_exists_nonfinite_exact_intermediate_of_ne_one_third
    (problem2_24_ieeeDouble_finiteSystem_ne_one_third hx) hzero

/-- Problem 2.24, IEEE-single narrowed zero-result branch audit.  The first
exact intermediate is finite on every finite zero branch, so any remaining
nonfinite exact-intermediate witness must occur in one of the later three
intermediates. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_implies_later_nonfinite_exact_intermediate
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    ¬ ieeeSingleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x) ∨
      ¬ ieeeSingleFormat.finiteSystem
        (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) ∨
      ¬ ieeeSingleFormat.finiteSystem
        ((((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x) :=
  ieeeSingleFormat.problem2_24_eval_eq_zero_implies_later_nonfinite_exact_intermediate_of_finiteSystem_input_of_ne_one_third
    problem2_24_ieeeSingle_subnormalMantissa_one
    problem2_24_ieeeSingle_half_finiteSystem
    hx
    (problem2_24_ieeeSingle_finiteSystem_ne_one_third hx)
    hzero

/-- Problem 2.24, IEEE-double narrowed zero-result branch audit.  The first
exact intermediate is finite on every finite zero branch, so any remaining
nonfinite exact-intermediate witness must occur in one of the later three
intermediates. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_implies_later_nonfinite_exact_intermediate
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    ¬ ieeeDoubleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x) ∨
      ¬ ieeeDoubleFormat.finiteSystem
        (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) ∨
      ¬ ieeeDoubleFormat.finiteSystem
        ((((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x) :=
  ieeeDoubleFormat.problem2_24_eval_eq_zero_implies_later_nonfinite_exact_intermediate_of_finiteSystem_input_of_ne_one_third
    problem2_24_ieeeDouble_subnormalMantissa_one
    problem2_24_ieeeDouble_half_finiteSystem
    hx
    (problem2_24_ieeeDouble_finiteSystem_ne_one_third hx)
    hzero

/-- Problem 2.24, IEEE-single sharpened zero-result branch audit.  Any finite
single input producing zero must have a nonfinite second or third exact real
intermediate. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_implies_second_or_third_nonfinite_exact_intermediate
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    ¬ ieeeSingleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x) ∨
      ¬ ieeeSingleFormat.finiteSystem
        (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) :=
  ieeeSingleFormat.problem2_24_eval_eq_zero_implies_second_or_third_nonfinite_exact_intermediate_of_finiteSystem_input_of_ne_one_third
    problem2_24_ieeeSingle_subnormalMantissa_one
    problem2_24_ieeeSingle_half_finiteSystem
    hx
    (problem2_24_ieeeSingle_finiteSystem_ne_one_third hx)
    hzero

/-- Problem 2.24, IEEE-double sharpened zero-result branch audit.  Any finite
double input producing zero must have a nonfinite second or third exact real
intermediate. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_implies_second_or_third_nonfinite_exact_intermediate
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    ¬ ieeeDoubleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x) ∨
      ¬ ieeeDoubleFormat.finiteSystem
        (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) :=
  ieeeDoubleFormat.problem2_24_eval_eq_zero_implies_second_or_third_nonfinite_exact_intermediate_of_finiteSystem_input_of_ne_one_third
    problem2_24_ieeeDouble_subnormalMantissa_one
    problem2_24_ieeeDouble_half_finiteSystem
    hx
    (problem2_24_ieeeDouble_finiteSystem_ne_one_third hx)
    hzero

/-- Problem 2.24, IEEE-single upper-branch sharpening.  In the upper adjacent
finite interval from the value above `1/3` through `3/8`, the second exact real
intermediate is finite, so any finite zero branch must have a nonfinite third
exact real intermediate. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_finiteSystem_upper_branch
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hlo : (11184811 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) ≤ x)
    (hhi : x ≤ (3 / 8 : ℝ))
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    ¬ ieeeSingleFormat.finiteSystem
      (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) := by
  have hbranch :
      ¬ ieeeSingleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x) ∨
        ¬ ieeeSingleFormat.finiteSystem
          (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) :=
    problem2_24_ieeeSingle_eval_eq_zero_implies_second_or_third_nonfinite_exact_intermediate
      hx hzero
  have hsecond :
      ieeeSingleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x) :=
    problem2_24_ieeeSingle_second_exact_intermediate_finiteSystem_of_finiteSystem_upper_branch
      hx hlo hhi
  rcases hbranch with hsecond_bad | hthird
  · exact False.elim (hsecond_bad hsecond)
  · exact hthird

/-- Problem 2.24, IEEE-double upper-branch sharpening.  In the upper adjacent
finite interval from the value above `1/3` through `3/8`, the second exact real
intermediate is finite, so any finite zero branch must have a nonfinite third
exact real intermediate. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_finiteSystem_upper_branch
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hlo : (6004799503160662 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) ≤ x)
    (hhi : x ≤ (3 / 8 : ℝ))
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    ¬ ieeeDoubleFormat.finiteSystem
      (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) := by
  have hbranch :
      ¬ ieeeDoubleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x) ∨
        ¬ ieeeDoubleFormat.finiteSystem
          (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) :=
    problem2_24_ieeeDouble_eval_eq_zero_implies_second_or_third_nonfinite_exact_intermediate
      hx hzero
  have hsecond :
      ieeeDoubleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x) :=
    problem2_24_ieeeDouble_second_exact_intermediate_finiteSystem_of_finiteSystem_upper_branch
      hx hlo hhi
  rcases hbranch with hsecond_bad | hthird
  · exact False.elim (hsecond_bad hsecond)
  · exact hthird

/-- Problem 2.24, IEEE-single adjacent branch at or above `1/3`.  Finite
single inputs cannot lie strictly between `1/3` and the adjacent value above
it, so the explicit upper-neighbor theorem applies and forces a nonfinite
third exact real intermediate. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_one_third_le
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hge : (1 / 3 : ℝ) ≤ x)
    (hhi : x ≤ (3 / 8 : ℝ))
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    ¬ ieeeSingleFormat.finiteSystem
      (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) := by
  have hlo :
      (11184811 : ℝ) * (2 : ℝ) ^ (-25 : ℤ) ≤ x :=
    problem2_24_ieeeSingle_upper_neighbor_le_of_finiteSystem_of_one_third_le
      hx hge
  exact
    problem2_24_ieeeSingle_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_finiteSystem_upper_branch
      hx hlo hhi hzero

/-- Problem 2.24, IEEE-double adjacent branch at or above `1/3`.  Finite
double inputs cannot lie strictly between `1/3` and the adjacent value above
it, so the explicit upper-neighbor theorem applies and forces a nonfinite
third exact real intermediate. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_one_third_le
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hge : (1 / 3 : ℝ) ≤ x)
    (hhi : x ≤ (3 / 8 : ℝ))
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    ¬ ieeeDoubleFormat.finiteSystem
      (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) := by
  have hlo :
      (6004799503160662 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) ≤ x :=
    problem2_24_ieeeDouble_upper_neighbor_le_of_finiteSystem_of_one_third_le
      hx hge
  exact
    problem2_24_ieeeDouble_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_finiteSystem_upper_branch
      hx hlo hhi hzero

/-- Problem 2.24, IEEE-single zero-branch sharpening.  Any finite single input
that evaluates to zero in the modeled path must have a nonfinite third exact
real intermediate. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_implies_third_exact_intermediate_nonfinite
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    ¬ ieeeSingleFormat.finiteSystem
      (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) := by
  have hhi : x ≤ (3 / 8 : ℝ) :=
    ieeeSingleFormat.problem2_24_eval_eq_zero_input_le_three_eighths_of_finiteSystem_input
      problem2_24_ieeeSingle_subnormalMantissa_one
      problem2_24_ieeeSingle_half_finiteSystem
      (ieeeSingleFormat.finiteSystem_neg
        problem2_24_ieeeSingle_three_eighths_finiteSystem)
      hx hzero
  by_cases hxlt : x < (1 / 3 : ℝ)
  · exact
      problem2_24_ieeeSingle_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_lt_one_third
        hx hxlt hzero
  · exact
      problem2_24_ieeeSingle_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_one_third_le
        hx (le_of_not_gt hxlt) hhi hzero

/-- Problem 2.24, IEEE-double zero-branch sharpening.  Any finite double input
that evaluates to zero in the modeled path must have a nonfinite third exact
real intermediate. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_implies_third_exact_intermediate_nonfinite
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    ¬ ieeeDoubleFormat.finiteSystem
      (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) := by
  have hhi : x ≤ (3 / 8 : ℝ) :=
    ieeeDoubleFormat.problem2_24_eval_eq_zero_input_le_three_eighths_of_finiteSystem_input
      problem2_24_ieeeDouble_subnormalMantissa_one
      problem2_24_ieeeDouble_half_finiteSystem
      (ieeeDoubleFormat.finiteSystem_neg
        problem2_24_ieeeDouble_three_eighths_finiteSystem)
      hx hzero
  by_cases hxlt : x < (1 / 3 : ℝ)
  · exact
      problem2_24_ieeeDouble_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_lt_one_third
        hx hxlt hzero
  · exact
      problem2_24_ieeeDouble_eval_eq_zero_implies_third_exact_intermediate_nonfinite_of_one_third_le
        hx (le_of_not_gt hxlt) hhi hzero

/-- Problem 2.24, modeled finite IEEE-single path.  No finite single input
can evaluate to zero in the finite round-to-even model. -/
theorem problem2_24_ieeeSingle_eval_ne_zero_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x) :
    ieeeSingleFormat.problem2_24_eval x ≠ 0 := by
  intro hzero
  have hthird_nonfinite :
      ¬ ieeeSingleFormat.finiteSystem
        (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) :=
    problem2_24_ieeeSingle_eval_eq_zero_implies_third_exact_intermediate_nonfinite
      hx hzero
  have hlo : (3 / 10 : ℝ) ≤ x :=
    ieeeSingleFormat.problem2_24_eval_eq_zero_input_ge_three_tenths_of_finiteSystem_input
      problem2_24_ieeeSingle_subnormalMantissa_one
      problem2_24_ieeeSingle_half_finiteSystem
      hx hzero
  have hhi : x ≤ (3 / 8 : ℝ) :=
    ieeeSingleFormat.problem2_24_eval_eq_zero_input_le_three_eighths_of_finiteSystem_input
      problem2_24_ieeeSingle_subnormalMantissa_one
      problem2_24_ieeeSingle_half_finiteSystem
      (ieeeSingleFormat.finiteSystem_neg
        problem2_24_ieeeSingle_three_eighths_finiteSystem)
      hx hzero
  have hthird_finite :
      ieeeSingleFormat.finiteSystem
        (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) :=
    problem2_24_ieeeSingle_third_exact_intermediate_finiteSystem_of_finiteSystem_zero_branch
      hx hlo hhi
  exact hthird_nonfinite hthird_finite

/-- Problem 2.24, modeled finite IEEE-double path.  No finite double input
can evaluate to zero in the finite round-to-even model. -/
theorem problem2_24_ieeeDouble_eval_ne_zero_of_finiteSystem_input
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x) :
    ieeeDoubleFormat.problem2_24_eval x ≠ 0 := by
  intro hzero
  have hthird_nonfinite :
      ¬ ieeeDoubleFormat.finiteSystem
        (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) :=
    problem2_24_ieeeDouble_eval_eq_zero_implies_third_exact_intermediate_nonfinite
      hx hzero
  have hlo : (3 / 10 : ℝ) ≤ x :=
    ieeeDoubleFormat.problem2_24_eval_eq_zero_input_ge_three_tenths_of_finiteSystem_input
      problem2_24_ieeeDouble_subnormalMantissa_one
      problem2_24_ieeeDouble_half_finiteSystem
      hx hzero
  have hhi : x ≤ (3 / 8 : ℝ) :=
    ieeeDoubleFormat.problem2_24_eval_eq_zero_input_le_three_eighths_of_finiteSystem_input
      problem2_24_ieeeDouble_subnormalMantissa_one
      problem2_24_ieeeDouble_half_finiteSystem
      (ieeeDoubleFormat.finiteSystem_neg
        problem2_24_ieeeDouble_three_eighths_finiteSystem)
      hx hzero
  have hthird_finite :
      ieeeDoubleFormat.finiteSystem
        (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) :=
    problem2_24_ieeeDouble_third_exact_intermediate_finiteSystem_of_finiteSystem_zero_branch
      hx hlo hhi
  exact hthird_nonfinite hthird_finite

/-- Problem 2.24, IEEE-single zero-result combined branch audit: a finite input
counterexample would need exact final cancellation and one of the source exact
intermediates to leave the finite system. -/
theorem problem2_24_ieeeSingle_eval_eq_zero_implies_y3_eq_neg_x_and_exists_nonfinite_exact_intermediate
    {x : ℝ}
    (hx : ieeeSingleFormat.finiteSystem x)
    (hzero : ieeeSingleFormat.problem2_24_eval x = 0) :
    ieeeSingleFormat.problem2_24_y3 x = -x ∧
      (¬ ieeeSingleFormat.finiteSystem (x - (1 / 2 : ℝ)) ∨
        ¬ ieeeSingleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x) ∨
        ¬ ieeeSingleFormat.finiteSystem
          (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) ∨
        ¬ ieeeSingleFormat.finiteSystem
          ((((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x)) :=
  ⟨problem2_24_ieeeSingle_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_input
      hx hzero,
    problem2_24_ieeeSingle_eval_eq_zero_implies_exists_nonfinite_exact_intermediate
      hx hzero⟩

/-- Problem 2.24, IEEE-double zero-result combined branch audit: a finite input
counterexample would need exact final cancellation and one of the source exact
intermediates to leave the finite system. -/
theorem problem2_24_ieeeDouble_eval_eq_zero_implies_y3_eq_neg_x_and_exists_nonfinite_exact_intermediate
    {x : ℝ}
    (hx : ieeeDoubleFormat.finiteSystem x)
    (hzero : ieeeDoubleFormat.problem2_24_eval x = 0) :
    ieeeDoubleFormat.problem2_24_y3 x = -x ∧
      (¬ ieeeDoubleFormat.finiteSystem (x - (1 / 2 : ℝ)) ∨
        ¬ ieeeDoubleFormat.finiteSystem ((x - (1 / 2 : ℝ)) + x) ∨
        ¬ ieeeDoubleFormat.finiteSystem
          (((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) ∨
        ¬ ieeeDoubleFormat.finiteSystem
          ((((x - (1 / 2 : ℝ)) + x) - (1 / 2 : ℝ)) + x)) :=
  ⟨problem2_24_ieeeDouble_y3_eq_neg_x_of_eval_eq_zero_of_finiteSystem_input
      hx hzero,
    problem2_24_ieeeDouble_eval_eq_zero_implies_exists_nonfinite_exact_intermediate
      hx hzero⟩

end FloatingPointFormat
end NumStability

end
