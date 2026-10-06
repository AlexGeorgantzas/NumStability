import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Analysis.Nonassociativity
import NumStability.FloatingPoint.Model

/-!
# Chapter02 Section06 Discriminant StandardModel Basic

Canonical destination for material split out of
`NumStability.Analysis.Problem2_17` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

/-- The discriminant-like expression under the square root in
`a*x^2 - 2*b*x + c = 0`. -/
def problem2_17_discriminant (a b c : ℝ) : ℝ :=
  b ^ 2 - a * c

/-- The rounded product/subtraction path for `b^2 - a*c`. -/
def problem2_17_computedDiscriminant (fp : FPModel) (a b c : ℝ) : ℝ :=
  fp.fl_sub (fp.fl_mul b b) (fp.fl_mul a c)

theorem problem2_17_true_discriminant_nonnegative :
    0 ≤ problem2_17_discriminant 1 1 (9 / 10 : ℝ) := by
  norm_num [problem2_17_discriminant]

theorem problem2_17_true_discriminant_eq_one_tenth :
    problem2_17_discriminant 1 1 (9 / 10 : ℝ) = 1 / 10 := by
  norm_num [problem2_17_discriminant]

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
end NumStability

end
