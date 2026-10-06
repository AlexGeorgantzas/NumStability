-- NumStability/Source/Higham/Chapter02/Problem21/HypotenuseNormalization/StandardModelCounterexample/Results.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Whole-owner block relocation.
-- Historical owner: `NumStability.Analysis.Problem2_20`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter02.Problem20.SquareRootIdentities.Basic
import NumStability.Source.Higham.Chapter02.Problem21.HypotenuseNormalization.Basic

/-!
# Results

Relocated from `NumStability.Analysis.Problem2_20` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


/-!
# Problem2_20 (compatibility module)

Historical path, retained so existing imports of `NumStability.Analysis.Problem2_20`
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

private def problem2_20_flMul (x y : ℝ) : ℝ :=
  by
    classical
    exact
      if x = (11 / 10 : ℝ) ∧ y = (11 / 10 : ℝ) then
        1
      else
        x * y

/-- A small abstract standard-model instance with `u = 1/5` that rounds
`(11/10)*(11/10)` downward to `1`. -/
private def problem2_20_fp : FPModel where
  u := (1 / 5 : ℝ)
  u_nonneg := by norm_num
  fl_add := fun x y => x + y
  fl_sub := fun x y => x - y
  fl_mul := problem2_20_flMul
  fl_div := fun x y => x / y
  fl_sqrt := Real.sqrt
  fl_add_zero := by
    intro x
    ring
  model_add := by
    intro x y
    exact ⟨0, by norm_num, by ring⟩
  model_sub := by
    intro x y
    exact ⟨0, by norm_num, by ring⟩
  model_mul := by
    intro x y
    by_cases h : x = (11 / 10 : ℝ) ∧ y = (11 / 10 : ℝ)
    · rcases h with ⟨rfl, rfl⟩
      refine ⟨-(21 / 121 : ℝ), by norm_num, ?_⟩
      simp [problem2_20_flMul]
      norm_num
    · refine ⟨0, by norm_num, ?_⟩
      simp [problem2_20_flMul, h]
  model_div := by
    intro x y _hy
    exact ⟨0, by norm_num, by ring⟩
  model_sqrt := by
    intro x _hx
    exact ⟨0, by norm_num, by ring⟩

/-- In the witness model, the rounded naive path computes `11/10`, which is
strictly larger than `1`. -/
theorem problem2_20_computed_witness_ratio_gt_one :
    1 < problem2_20_computedRatio problem2_20_fp (11 / 10 : ℝ) 0 := by
  norm_num [problem2_20_computedRatio, problem2_20_fp, problem2_20_flMul]

/-- Higham Problem 2.20's phenomenon can occur in the standard model: the exact
ratio is `1`, while the rounded naive computation exceeds `1`. -/
theorem problem2_20_standard_model_counterexample :
    ∃ fp : FPModel, ∃ x y : ℝ,
      problem2_20_exactRatio x y = 1 ∧
        1 < problem2_20_computedRatio fp x y := by
  exact
    ⟨problem2_20_fp, (11 / 10 : ℝ), 0,
      problem2_20_exact_witness_ratio_eq_one,
      problem2_20_computed_witness_ratio_gt_one⟩

/-- The standard-model Problem 2.20 witness can be chosen with inputs that are
floating-point values of a concrete finite format.  The rounded operations are
still supplied by the abstract `FPModel`; a concrete finite-operation or IEEE
instruction trace with the source's no-overflow/no-underflow side condition
remains a separate target. -/
theorem problem2_20_standard_model_counterexample_with_decimal_finite_inputs :
    ∃ fmt : FloatingPointFormat, ∃ fp : FPModel, ∃ x y : ℝ,
      fmt.finiteSystem x ∧ fmt.finiteSystem y ∧
        problem2_20_exactRatio x y = 1 ∧
          1 < problem2_20_computedRatio fp x y := by
  refine
    ⟨FloatingPointFormat.problem2_20_decimalTwoDigitThreeExponentFormat,
      problem2_20_fp, (11 / 10 : ℝ), 0, ?_, ?_,
      problem2_20_exact_witness_ratio_eq_one,
      problem2_20_computed_witness_ratio_gt_one⟩
  · exact
      FloatingPointFormat.problem2_20_decimalTwoDigitThreeExponentFormat_finiteSystem_eleven_tenths
  · exact
      FloatingPointFormat.problem2_20_decimalTwoDigitThreeExponentFormat.finiteSystem_zero

end NumStability

end
