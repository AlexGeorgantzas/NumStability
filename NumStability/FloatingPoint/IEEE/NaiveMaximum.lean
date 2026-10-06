/-
SPDX-License-Identifier: MIT
-/

import NumStability.Analysis.FloatingPointArithmetic

namespace NumStability

noncomputable section

/-!
# Naive maximum over IEEE values

The literal comparison branch for a maximum operation over the repository's
IEEE-facing value layer. Because modeled IEEE `>` is false when either operand
is NaN, the branch is asymmetric: it discards a left NaN and returns a right
NaN. The API also records correctness on finite operands and the resulting
failure of unconditional NaN propagation.
-/

/-- A literal maximum branch using the modeled IEEE greater-than predicate. -/
def ieeeNaiveMax (x y : IeeeValue) : IeeeValue :=
  by
    classical
    exact if x.ieeeGt y then x else y

theorem ieeeNaiveMax_eq_left_of_ieeeGt
    {x y : IeeeValue} (h : x.ieeeGt y) :
    ieeeNaiveMax x y = x := by
  classical
  simp [ieeeNaiveMax, h]

theorem ieeeNaiveMax_eq_right_of_not_ieeeGt
    {x y : IeeeValue} (h : ¬ x.ieeeGt y) :
    ieeeNaiveMax x y = y := by
  classical
  simp [ieeeNaiveMax, h]

theorem ieeeNaiveMax_finite_finite_left_of_lt
    {x y : ℝ} (h : y < x) :
    ieeeNaiveMax (IeeeValue.finite x) (IeeeValue.finite y) =
      IeeeValue.finite x := by
  exact ieeeNaiveMax_eq_left_of_ieeeGt
    (by simpa [IeeeValue.ieeeGt, IeeeValue.ieeeLt] using h)

theorem ieeeNaiveMax_finite_finite_right_of_le
    {x y : ℝ} (h : x ≤ y) :
    ieeeNaiveMax (IeeeValue.finite x) (IeeeValue.finite y) =
      IeeeValue.finite y := by
  exact ieeeNaiveMax_eq_right_of_not_ieeeGt
    (by
      simpa [IeeeValue.ieeeGt, IeeeValue.ieeeLt] using
        (not_lt.mpr h))

/-- On ordinary finite real operands, the literal branch computes the ordinary
real maximum. The failure is specific to IEEE special-value comparisons. -/
theorem ieeeNaiveMax_finite_finite_eq_max
    (x y : ℝ) :
    ieeeNaiveMax (IeeeValue.finite x) (IeeeValue.finite y) =
      IeeeValue.finite (max x y) := by
  by_cases h : y < x
  · rw [ieeeNaiveMax_finite_finite_left_of_lt h]
    rw [max_eq_left (le_of_lt h)]
  · have hle : x ≤ y := le_of_not_gt h
    rw [ieeeNaiveMax_finite_finite_right_of_le hle]
    rw [max_eq_right hle]

/-- If the left input is NaN, the comparison is false and the branch returns
the right input. -/
theorem ieeeNaiveMax_left_nan
    (y : IeeeValue) :
    ieeeNaiveMax IeeeValue.nan y = y := by
  exact ieeeNaiveMax_eq_right_of_not_ieeeGt
    (IeeeValue.not_ieeeGt_left_nan y)

/-- If the right input is NaN, the comparison is false and the branch returns
that right NaN. -/
theorem ieeeNaiveMax_right_nan
    (x : IeeeValue) :
    ieeeNaiveMax x IeeeValue.nan = IeeeValue.nan := by
  exact ieeeNaiveMax_eq_right_of_not_ieeeGt
    (IeeeValue.not_ieeeGt_right_nan x)

theorem ieeeNaiveMax_nan_finite
    (x : ℝ) :
    ieeeNaiveMax IeeeValue.nan (IeeeValue.finite x) =
      IeeeValue.finite x := by
  exact ieeeNaiveMax_left_nan (IeeeValue.finite x)

theorem ieeeNaiveMax_finite_nan
    (x : ℝ) :
    ieeeNaiveMax (IeeeValue.finite x) IeeeValue.nan =
      IeeeValue.nan := by
  exact ieeeNaiveMax_right_nan (IeeeValue.finite x)

/-- The literal branch is not symmetric in the presence of NaNs. -/
theorem ieeeNaiveMax_nan_finite_ne_finite_nan
    (x : ℝ) :
    ieeeNaiveMax IeeeValue.nan (IeeeValue.finite x) ≠
      ieeeNaiveMax (IeeeValue.finite x) IeeeValue.nan := by
  rw [ieeeNaiveMax_nan_finite, ieeeNaiveMax_finite_nan]
  simp

theorem ieeeNaiveMax_left_nan_finite_result_not_nan
    (x : ℝ) :
    ¬ (ieeeNaiveMax IeeeValue.nan (IeeeValue.finite x)).isNaN := by
  simp [ieeeNaiveMax_nan_finite, IeeeValue.isNaN]

/-- The literal branch does not satisfy the common "propagate any NaN input"
expectation: a left NaN with a finite right operand returns the finite operand. -/
theorem ieeeNaiveMax_not_nan_propagating :
    ¬ (∀ x y : IeeeValue,
      (x.isNaN ∨ y.isNaN) → (ieeeNaiveMax x y).isNaN) := by
  intro h
  have hnan :
      (ieeeNaiveMax IeeeValue.nan (IeeeValue.finite 0)).isNaN :=
    h IeeeValue.nan (IeeeValue.finite 0)
      (Or.inl IeeeValue.nan_isNaN)
  simp [ieeeNaiveMax_nan_finite, IeeeValue.isNaN] at hnan

theorem ieeeNaiveMax_concrete_nan_counterexample :
    ∃ x y : IeeeValue,
      (x.isNaN ∨ y.isNaN) ∧ ¬ (ieeeNaiveMax x y).isNaN := by
  refine ⟨IeeeValue.nan, IeeeValue.finite 0, Or.inl IeeeValue.nan_isNaN, ?_⟩
  exact ieeeNaiveMax_left_nan_finite_result_not_nan 0

theorem ieeeNaiveMax_finite_correct_but_not_nan_propagating :
    (∀ x y : ℝ,
        ieeeNaiveMax (IeeeValue.finite x) (IeeeValue.finite y) =
          IeeeValue.finite (max x y)) ∧
      ¬ (∀ x y : IeeeValue,
        (x.isNaN ∨ y.isNaN) → (ieeeNaiveMax x y).isNaN) := by
  exact ⟨ieeeNaiveMax_finite_finite_eq_max, ieeeNaiveMax_not_nan_propagating⟩

end

end NumStability
