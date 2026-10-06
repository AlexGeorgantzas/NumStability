-- NumStability/Source/Higham/Chapter02/Section06/Discriminant/StandardModel/Counterexample/Results.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Whole-owner block relocation.
-- Historical owner: `NumStability.Analysis.Problem2_17`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Analysis.Nonassociativity
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter02.Section06.Discriminant.StandardModel.Basic

/-!
# Results

Relocated from `NumStability.Analysis.Problem2_17` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


/-!
# Problem2_17 (compatibility module)

Historical path, retained so existing imports of `NumStability.Analysis.Problem2_17`
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

private def problem2_17_flMul (x y : ℝ) : ℝ :=
  by
    classical
    exact
      if x = 1 ∧ y = 1 then
        x * y * (1 - (1 / 10 : ℝ))
      else if x = 1 ∧ y = (9 / 10 : ℝ) then
        x * y * (1 + (1 / 10 : ℝ))
      else
        x * y

/-- A small abstract standard-model instance with `u = 1/10` that rounds
`1*1` downward and `1*(9/10)` upward. -/
private def problem2_17_fp : FPModel where
  u := (1 / 10 : ℝ)
  u_nonneg := by norm_num
  fl_add := fun x y => x + y
  fl_sub := fun x y => x - y
  fl_mul := problem2_17_flMul
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
    by_cases h11 : x = 1 ∧ y = 1
    · rcases h11 with ⟨rfl, rfl⟩
      refine ⟨-(1 / 10 : ℝ), by norm_num, ?_⟩
      norm_num [problem2_17_flMul]
    · by_cases h19 : x = 1 ∧ y = (9 / 10 : ℝ)
      · rcases h19 with ⟨rfl, rfl⟩
        refine ⟨(1 / 10 : ℝ), by norm_num, ?_⟩
        norm_num [problem2_17_flMul]
      · refine ⟨0, by norm_num, ?_⟩
        simp [problem2_17_flMul, h11, h19]
  model_div := by
    intro x y _hy
    exact ⟨0, by norm_num, by ring⟩
  model_sqrt := by
    intro x _hx
    exact ⟨0, by norm_num, by ring⟩

theorem problem2_17_computed_discriminant_negative :
    problem2_17_computedDiscriminant problem2_17_fp 1 1 (9 / 10 : ℝ) < 0 := by
  norm_num [problem2_17_computedDiscriminant, problem2_17_fp,
    problem2_17_flMul]

theorem problem2_17_standard_model_witness_exact_values :
    ∃ fp : FPModel,
      fp.u = (1 / 10 : ℝ) ∧
        problem2_17_discriminant 1 1 (9 / 10 : ℝ) = 1 / 10 ∧
          problem2_17_computedDiscriminant fp 1 1 (9 / 10 : ℝ) =
            -(9 / 100 : ℝ) := by
  refine
    ⟨problem2_17_fp, rfl, problem2_17_true_discriminant_eq_one_tenth, ?_⟩
  norm_num [problem2_17_computedDiscriminant, problem2_17_fp,
    problem2_17_flMul]

/-- Higham Problem 2.17's phenomenon can occur in the standard model: the true
`b^2 - a*c` is nonnegative while the rounded product/subtraction path is
negative. -/
theorem problem2_17_standard_model_counterexample :
    ∃ fp : FPModel, ∃ a b c : ℝ,
      0 ≤ problem2_17_discriminant a b c ∧
        problem2_17_computedDiscriminant fp a b c < 0 := by
  exact
    ⟨problem2_17_fp, 1, 1, (9 / 10 : ℝ),
      problem2_17_true_discriminant_nonnegative,
      problem2_17_computed_discriminant_negative⟩

/-- The standard-model Problem 2.17 witness can be chosen with inputs that are
floating-point values of the concrete one-digit decimal finite format.  The
rounded operations are still supplied by the abstract `FPModel`; a concrete
finite-operation or IEEE instruction trace remains a separate target. -/
theorem problem2_17_standard_model_counterexample_with_decimal_finite_inputs :
    ∃ fmt : FloatingPointFormat, ∃ fp : FPModel, ∃ a b c : ℝ,
      fmt.finiteSystem a ∧ fmt.finiteSystem b ∧ fmt.finiteSystem c ∧
        0 ≤ problem2_17_discriminant a b c ∧
          problem2_17_computedDiscriminant fp a b c < 0 := by
  refine
    ⟨FloatingPointFormat.decimalOneDigitThreeExponentFormat,
      problem2_17_fp, 1, 1, (9 / 10 : ℝ), ?_, ?_, ?_,
      problem2_17_true_discriminant_nonnegative,
      problem2_17_computed_discriminant_negative⟩
  · exact FloatingPointFormat.decimalOneDigitThreeExponentFormat_finiteSystem_one
  · exact FloatingPointFormat.decimalOneDigitThreeExponentFormat_finiteSystem_one
  · exact
      FloatingPointFormat.problem2_17_decimalOneDigitThreeExponentFormat_finiteSystem_nine_tenths

end NumStability

end
