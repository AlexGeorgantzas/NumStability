-- Analysis/Problem2_17.lean
--
-- Problem-specific theorem surface for Higham Chapter 2, Problem 2.17.

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Analysis.Nonassociativity
import NumStability.FloatingPoint.Model

namespace NumStability

noncomputable section

/-!
# Higham Chapter 2, Problem 2.17

Problem 2.17 asks whether, while solving `a*x^2 - 2*b*x + c = 0`, the true
value of `b^2 - a*c` can be nonnegative while the computed value is negative.
This file gives a small standard-model witness: two products round in opposite
allowed directions before the final subtraction.
-/

/-- The discriminant-like expression under the square root in
`a*x^2 - 2*b*x + c = 0`. -/
def problem2_17_discriminant (a b c : ℝ) : ℝ :=
  b ^ 2 - a * c

/-- The rounded product/subtraction path for `b^2 - a*c`. -/
def problem2_17_computedDiscriminant (fp : FPModel) (a b c : ℝ) : ℝ :=
  fp.fl_sub (fp.fl_mul b b) (fp.fl_mul a c)

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

theorem problem2_17_true_discriminant_nonnegative :
    0 ≤ problem2_17_discriminant 1 1 (9 / 10 : ℝ) := by
  norm_num [problem2_17_discriminant]

theorem problem2_17_true_discriminant_eq_one_tenth :
    problem2_17_discriminant 1 1 (9 / 10 : ℝ) = 1 / 10 := by
  norm_num [problem2_17_discriminant]

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

namespace FloatingPointFormat

/-- The coefficient `0.9` used in the Problem 2.17 standard-model witness is a
finite value of the repository's one-digit decimal format. -/
theorem problem2_17_decimalOneDigitThreeExponentFormat_finiteSystem_nine_tenths :
    decimalOneDigitThreeExponentFormat.finiteSystem (9 / 10 : ℝ) := by
  refine Or.inr (Or.inl ?_)
  have hrepr :
      decimalOneDigitThreeExponentFormat.normalizedExponentRepresentation
        (9 / 10 : ℝ) 0 := by
    refine ⟨false, 9, ?_, ?_, ?_⟩
    · norm_num [decimalOneDigitThreeExponentFormat, normalizedMantissa,
        mantissaInRange, minNormalMantissa]
    · norm_num [decimalOneDigitThreeExponentFormat, exponentInRange]
    · norm_num [decimalOneDigitThreeExponentFormat, normalizedValue,
        signValue, betaR]
  exact
    decimalOneDigitThreeExponentFormat.normalizedExponentRepresentation_normalizedSystem
      hrepr

end FloatingPointFormat

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

end

end NumStability
