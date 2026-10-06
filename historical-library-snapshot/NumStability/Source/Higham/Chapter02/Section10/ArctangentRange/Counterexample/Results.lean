-- NumStability/Source/Higham/Chapter02/Section10/ArctangentRange/Counterexample/Results.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Whole-owner block relocation.
-- Historical owner: `NumStability.Analysis.HighamChapter2ElementaryFunctions`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Source.Higham.Chapter02.Section10.ArctangentRange.Basic

/-!
# Results

Relocated from `NumStability.Analysis.HighamChapter2ElementaryFunctions` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


/-!
# HighamChapter2ElementaryFunctions (compatibility module)

Historical path, retained so existing imports of `NumStability.Analysis.HighamChapter2ElementaryFunctions`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

open Set MeasureTheory
open scoped Interval

noncomputable section

namespace NumStability

private theorem arctan_le_self_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    Real.arctan t ≤ t := by
  have hrat : IntervalIntegrable (fun x : ℝ => (1 + x ^ 2)⁻¹)
      volume 0 t := by
    apply ContinuousOn.intervalIntegrable_of_Icc ht
    exact (continuousOn_const.add ((continuousOn_id' (Icc (0 : ℝ) t)).pow 2)).inv₀
      (fun x _hx => by
        change 1 + x ^ 2 ≠ 0
        nlinarith [sq_nonneg x])
  have hone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 t :=
    continuousOn_const.intervalIntegrable_of_Icc ht
  have hmono := intervalIntegral.integral_mono_on ht hrat hone
    (fun x _hx => by
      have hden : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
      simpa using ((inv_le_one₀ (by positivity : (0 : ℝ) < 1 + x ^ 2)).2 hden))
  simpa using hmono

private theorem higham2_arctan_two_pow_thirty_identity :
    Real.arctan ((2 : ℝ) ^ (30 : ℕ)) =
      Real.pi / 2 - Real.arctan ((2 : ℝ) ^ (-30 : ℤ)) := by
  have hsmall : 0 < (2 : ℝ) ^ (-30 : ℤ) := by positivity
  have hinv : ((2 : ℝ) ^ (-30 : ℤ))⁻¹ = (2 : ℝ) ^ (30 : ℕ) := by
    norm_num [zpow_neg]
  simpa [hinv] using Real.arctan_inv_of_pos hsmall

private theorem higham2ArctanSingleLower_lt_exact :
    higham2ArctanSingleLower < Real.arctan ((2 : ℝ) ^ (30 : ℕ)) := by
  have hatan_le :
      Real.arctan ((2 : ℝ) ^ (-30 : ℤ)) ≤ (2 : ℝ) ^ (-30 : ℤ) :=
    arctan_le_self_of_nonneg (by positivity)
  rw [higham2_arctan_two_pow_thirty_identity,
    higham2ArctanSingleLower_value]
  have hpi := Real.pi_gt_d20
  norm_num [zpow_neg] at hatan_le ⊢
  nlinarith

private theorem higham2ArctanExact_lt_singleUpper :
    Real.arctan ((2 : ℝ) ^ (30 : ℕ)) < higham2ArctanSingleUpper := by
  have hsmall_pos : 0 < (2 : ℝ) ^ (-30 : ℤ) := by positivity
  have hatan_pos : 0 < Real.arctan ((2 : ℝ) ^ (-30 : ℤ)) :=
    Real.arctan_pos.mpr hsmall_pos
  rw [higham2_arctan_two_pow_thirty_identity]
  exact (sub_lt_self _ hatan_pos).trans
    higham2ArctanSingleUpper_gt_pi_div_two

private theorem higham2ArctanExact_right_closer :
    |Real.arctan ((2 : ℝ) ^ (30 : ℕ)) - higham2ArctanSingleUpper| <
      |Real.arctan ((2 : ℝ) ^ (30 : ℕ)) - higham2ArctanSingleLower| := by
  let x := Real.arctan ((2 : ℝ) ^ (30 : ℕ))
  have hleft : higham2ArctanSingleLower < x :=
    higham2ArctanSingleLower_lt_exact
  have hright : x < higham2ArctanSingleUpper :=
    higham2ArctanExact_lt_singleUpper
  have hatan_le :
      Real.arctan ((2 : ℝ) ^ (-30 : ℤ)) ≤ (2 : ℝ) ^ (-30 : ℤ) :=
    arctan_le_self_of_nonneg (by positivity)
  have hmid :
      (higham2ArctanSingleLower + higham2ArctanSingleUpper) / 2 < x := by
    change
      (higham2ArctanSingleLower + higham2ArctanSingleUpper) / 2 <
        Real.arctan ((2 : ℝ) ^ (30 : ℕ))
    rw [higham2_arctan_two_pow_thirty_identity,
      higham2ArctanSingleLower_value, higham2ArctanSingleUpper_value]
    have hpi := Real.pi_gt_d20
    norm_num [zpow_neg] at hatan_le ⊢
    nlinarith
  rw [abs_of_neg (sub_neg.mpr hright), abs_of_pos (sub_pos.mpr hleft)]
  nlinarith

private theorem higham2ArctanExact_finiteNormalRange :
    FloatingPointFormat.ieeeSingleFormat.finiteNormalRange
      (Real.arctan ((2 : ℝ) ^ (30 : ℕ))) := by
  let x := Real.arctan ((2 : ℝ) ^ (30 : ℕ))
  have hleft : higham2ArctanSingleLower < x :=
    higham2ArctanSingleLower_lt_exact
  have hright : x < higham2ArctanSingleUpper :=
    higham2ArctanExact_lt_singleUpper
  have hxpos : 0 < x := by
    rw [Real.arctan_pos]
    positivity
  rw [FloatingPointFormat.finiteNormalRange, abs_of_pos hxpos]
  constructor
  · have hmin :
        FloatingPointFormat.ieeeSingleFormat.minNormalMagnitude ≤
          higham2ArctanSingleLower := by
      rw [higham2ArctanSingleLower_value]
      norm_num [FloatingPointFormat.ieeeSingleFormat,
        FloatingPointFormat.minNormalMagnitude,
        FloatingPointFormat.betaR, zpow_neg]
    exact hmin.trans hleft.le
  · have hmax :
        higham2ArctanSingleUpper ≤
          FloatingPointFormat.ieeeSingleFormat.maxFiniteMagnitude := by
      have hupper_two : higham2ArctanSingleUpper ≤ 2 := by
        rw [higham2ArctanSingleUpper_value]
        norm_num [zpow_neg]
      have htwo_max :
          (2 : ℝ) ≤ FloatingPointFormat.ieeeSingleFormat.maxFiniteMagnitude := by
        rw [FloatingPointFormat.maxFiniteMagnitude,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.betaR]
        norm_num [zpow_neg]
      exact hupper_two.trans htwo_max
    exact hright.le.trans hmax

/-- The correctly rounded IEEE-single value of `arctan (2^30)` is the upper
adjacent single-precision number, which lies strictly above `pi / 2`.

This is the precise range-violation example stated in Higham Section 2.10.
-/
theorem higham2_arctan_two_pow_thirty_correct_rounding_exceeds_pi_div_two :
    FloatingPointFormat.ieeeSingleFormat.finiteRoundToEven
        (Real.arctan ((2 : ℝ) ^ (30 : ℕ))) = higham2ArctanSingleUpper ∧
      Real.pi / 2 < higham2ArctanSingleUpper := by
  let fmt := FloatingPointFormat.ieeeSingleFormat
  let a := higham2ArctanSingleLower
  let b := higham2ArctanSingleUpper
  let x := Real.arctan ((2 : ℝ) ^ (30 : ℕ))
  have hm : fmt.normalizedMantissa 13176794 := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (13176794 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 13176794, (1 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have hstrict : a < x ∧ x < b :=
    ⟨higham2ArctanSingleLower_lt_exact,
      higham2ArctanExact_lt_singleUpper⟩
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      higham2ArctanExact_finiteNormalRange
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict higham2ArctanExact_right_closer
  exact ⟨by simpa [fmt, x, b] using hround,
    higham2ArctanSingleUpper_gt_pi_div_two⟩

end NumStability

end
