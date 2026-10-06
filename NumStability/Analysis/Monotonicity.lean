-- Analysis/Monotonicity.lean
--
-- Monotonicity foundations for Higham Chapter 2, §2.9.

import Mathlib.Tactic.Linarith
import NumStability.Analysis.FloatingPointArithmetic
import NumStability.Analysis.TieRules

namespace NumStability

noncomputable section

namespace FloatingPointFormat

/-!
# Monotonicity of correctly rounded finite rounding

Higham Chapter 2, §2.9 notes monotonicity as a useful property of correctly
rounded arithmetic.  The local theorems below treat individual adjacent,
underflow, and overflow selectors.  The final theorem proves monotonicity of
the total finite round-to-even selector directly from its global nearest-finite
specification, thereby covering every within-branch and cross-branch case.
-/

theorem nearestAdjacentRoundToEven_eq_left_or_right
    (x a b : ℝ) (leftMantissa : ℕ) :
    nearestAdjacentRoundToEven x a b leftMantissa = a ∨
      nearestAdjacentRoundToEven x a b leftMantissa = b := by
  unfold nearestAdjacentRoundToEven
  by_cases hleft : |x - a| < |x - b|
  · simp [hleft]
  · simp [hleft]
    by_cases hright : |x - b| < |x - a|
    · simp [hright]
    · simp [hright]
      by_cases heven : evenMantissa leftMantissa
      · simp [heven]
      · simp [heven]

theorem left_le_nearestAdjacentRoundToEven
    {x a b : ℝ} {leftMantissa : ℕ}
    (hab : a ≤ b) :
    a ≤ nearestAdjacentRoundToEven x a b leftMantissa := by
  rcases nearestAdjacentRoundToEven_eq_left_or_right x a b leftMantissa with h | h
  · rw [h]
  · rw [h]
    exact hab

theorem nearestAdjacentRoundToEven_le_right
    {x a b : ℝ} {leftMantissa : ℕ}
    (hab : a ≤ b) :
    nearestAdjacentRoundToEven x a b leftMantissa ≤ b := by
  rcases nearestAdjacentRoundToEven_eq_left_or_right x a b leftMantissa with h | h
  · rw [h]
    exact hab
  · rw [h]

/-- On a fixed ordered adjacent bracket, round-to-even is monotone in the exact
input.  The bracket hypotheses are explicit because this is the local selector
used by the source-facing finite rounding policy, not a total IEEE operation. -/
theorem nearestAdjacentRoundToEven_monotone_on_ordered_bracket
    {x y a b : ℝ} {leftMantissa : ℕ}
    (hab : a ≤ b)
    (hx : a ≤ x ∧ x ≤ b)
    (hy : a ≤ y ∧ y ≤ b)
    (hxy : x ≤ y) :
    nearestAdjacentRoundToEven x a b leftMantissa ≤
      nearestAdjacentRoundToEven y a b leftMantissa := by
  have hx_abs_left : |x - a| = x - a := by
    exact abs_of_nonneg (sub_nonneg.mpr hx.1)
  have hx_abs_right : |x - b| = b - x := by
    rw [abs_of_nonpos (sub_nonpos.mpr hx.2)]
    ring
  have hy_abs_left : |y - a| = y - a := by
    exact abs_of_nonneg (sub_nonneg.mpr hy.1)
  have hy_abs_right : |y - b| = b - y := by
    rw [abs_of_nonpos (sub_nonpos.mpr hy.2)]
    ring
  by_cases hx_left : |x - a| < |x - b|
  · have hx_round :
        nearestAdjacentRoundToEven x a b leftMantissa = a :=
      nearestAdjacentRoundToEven_eq_left_of_left_closer hx_left
    rw [hx_round]
    exact left_le_nearestAdjacentRoundToEven hab
  · by_cases hx_right : |x - b| < |x - a|
    · have hx_round :
          nearestAdjacentRoundToEven x a b leftMantissa = b :=
        nearestAdjacentRoundToEven_eq_right_of_right_closer hx_right
      have hy_right : |y - b| < |y - a| := by
        rw [hy_abs_left, hy_abs_right]
        rw [hx_abs_left, hx_abs_right] at hx_right
        linarith
      have hy_round :
          nearestAdjacentRoundToEven y a b leftMantissa = b :=
        nearestAdjacentRoundToEven_eq_right_of_right_closer hy_right
      rw [hx_round, hy_round]
    · have hx_tie : |x - a| = |x - b| := by
        apply le_antisymm
        · exact le_of_not_gt hx_right
        · exact le_of_not_gt hx_left
      by_cases heven : evenMantissa leftMantissa
      · have hx_round :
            nearestAdjacentRoundToEven x a b leftMantissa = a :=
          nearestAdjacentRoundToEven_eq_left_of_tie_even hx_tie heven
        rw [hx_round]
        exact left_le_nearestAdjacentRoundToEven hab
      · have hx_round :
            nearestAdjacentRoundToEven x a b leftMantissa = b :=
          nearestAdjacentRoundToEven_eq_right_of_tie_odd hx_tie heven
        have hy_not_left : ¬ |y - a| < |y - b| := by
          intro hy_left
          rw [hy_abs_left, hy_abs_right] at hy_left
          rw [hx_abs_left, hx_abs_right] at hx_tie
          linarith
        by_cases hy_right : |y - b| < |y - a|
        · have hy_round :
              nearestAdjacentRoundToEven y a b leftMantissa = b :=
            nearestAdjacentRoundToEven_eq_right_of_right_closer hy_right
          rw [hx_round, hy_round]
        · have hy_tie : |y - a| = |y - b| := by
            apply le_antisymm
            · exact le_of_not_gt hy_right
            · exact le_of_not_gt hy_not_left
          have hy_round :
              nearestAdjacentRoundToEven y a b leftMantissa = b :=
            nearestAdjacentRoundToEven_eq_right_of_tie_odd hy_tie heven
          rw [hx_round, hy_round]

theorem nearestAdjacentRoundAway_eq_left_or_right
    (x a b : ℝ) :
    nearestAdjacentRoundAway x a b = a ∨
      nearestAdjacentRoundAway x a b = b := by
  unfold nearestAdjacentRoundAway
  by_cases hleft : |x - a| < |x - b|
  · simp [hleft]
  · simp [hleft]
    by_cases hright : |x - b| < |x - a|
    · simp [hright]
    · simp [hright]
      by_cases hmag : |a| ≤ |b|
      · simp [hmag]
      · simp [hmag]

theorem nearestAdjacentRoundAway_eq_left_of_left_closer
    {x a b : ℝ} (hleftCloser : |x - a| < |x - b|) :
    nearestAdjacentRoundAway x a b = a := by
  unfold nearestAdjacentRoundAway
  simp [hleftCloser]

theorem nearestAdjacentRoundAway_eq_right_of_right_closer
    {x a b : ℝ} (hrightCloser : |x - b| < |x - a|) :
    nearestAdjacentRoundAway x a b = b := by
  unfold nearestAdjacentRoundAway
  have hnot_left : ¬ |x - a| < |x - b| :=
    not_lt_of_ge (le_of_lt hrightCloser)
  simp [hnot_left, hrightCloser]

theorem nearestAdjacentRoundAway_eq_right_of_tie_abs_ge
    {x a b : ℝ} (htie : |x - a| = |x - b|)
    (hmag : |a| ≤ |b|) :
    nearestAdjacentRoundAway x a b = b := by
  unfold nearestAdjacentRoundAway
  have hnot_left : ¬ |x - a| < |x - b| := by
    rw [htie]
    exact lt_irrefl _
  have hnot_right : ¬ |x - b| < |x - a| := by
    rw [htie]
    exact lt_irrefl _
  simp [hnot_left, hnot_right, hmag]

theorem nearestAdjacentRoundAway_eq_left_of_tie_abs_lt
    {x a b : ℝ} (htie : |x - a| = |x - b|)
    (hmag : ¬ |a| ≤ |b|) :
    nearestAdjacentRoundAway x a b = a := by
  unfold nearestAdjacentRoundAway
  have hnot_left : ¬ |x - a| < |x - b| := by
    rw [htie]
    exact lt_irrefl _
  have hnot_right : ¬ |x - b| < |x - a| := by
    rw [htie]
    exact lt_irrefl _
  simp [hnot_left, hnot_right, hmag]

theorem left_le_nearestAdjacentRoundAway
    {x a b : ℝ} (hab : a ≤ b) :
    a ≤ nearestAdjacentRoundAway x a b := by
  rcases nearestAdjacentRoundAway_eq_left_or_right x a b with h | h
  · rw [h]
  · rw [h]
    exact hab

theorem nearestAdjacentRoundAway_le_right
    {x a b : ℝ} (hab : a ≤ b) :
    nearestAdjacentRoundAway x a b ≤ b := by
  rcases nearestAdjacentRoundAway_eq_left_or_right x a b with h | h
  · rw [h]
    exact hab
  · rw [h]

/-- On a fixed ordered adjacent bracket, the local round-away selector is
monotone in the exact input.  This is only the local nearest-rounding policy,
not global finite-format or IEEE operation monotonicity. -/
theorem nearestAdjacentRoundAway_monotone_on_ordered_bracket
    {x y a b : ℝ}
    (hab : a ≤ b)
    (hx : a ≤ x ∧ x ≤ b)
    (hy : a ≤ y ∧ y ≤ b)
    (hxy : x ≤ y) :
    nearestAdjacentRoundAway x a b ≤
      nearestAdjacentRoundAway y a b := by
  have hx_abs_left : |x - a| = x - a := by
    exact abs_of_nonneg (sub_nonneg.mpr hx.1)
  have hx_abs_right : |x - b| = b - x := by
    rw [abs_of_nonpos (sub_nonpos.mpr hx.2)]
    ring
  have hy_abs_left : |y - a| = y - a := by
    exact abs_of_nonneg (sub_nonneg.mpr hy.1)
  have hy_abs_right : |y - b| = b - y := by
    rw [abs_of_nonpos (sub_nonpos.mpr hy.2)]
    ring
  by_cases hx_left : |x - a| < |x - b|
  · have hx_round : nearestAdjacentRoundAway x a b = a :=
      nearestAdjacentRoundAway_eq_left_of_left_closer hx_left
    rw [hx_round]
    exact left_le_nearestAdjacentRoundAway hab
  · by_cases hx_right : |x - b| < |x - a|
    · have hx_round : nearestAdjacentRoundAway x a b = b :=
        nearestAdjacentRoundAway_eq_right_of_right_closer hx_right
      have hy_right : |y - b| < |y - a| := by
        rw [hy_abs_left, hy_abs_right]
        rw [hx_abs_left, hx_abs_right] at hx_right
        linarith
      have hy_round : nearestAdjacentRoundAway y a b = b :=
        nearestAdjacentRoundAway_eq_right_of_right_closer hy_right
      rw [hx_round, hy_round]
    · have hx_tie : |x - a| = |x - b| := by
        apply le_antisymm
        · exact le_of_not_gt hx_right
        · exact le_of_not_gt hx_left
      by_cases hmag : |a| ≤ |b|
      · have hx_round : nearestAdjacentRoundAway x a b = b :=
          nearestAdjacentRoundAway_eq_right_of_tie_abs_ge hx_tie hmag
        have hy_not_left : ¬ |y - a| < |y - b| := by
          intro hy_left
          rw [hy_abs_left, hy_abs_right] at hy_left
          rw [hx_abs_left, hx_abs_right] at hx_tie
          linarith
        by_cases hy_right : |y - b| < |y - a|
        · have hy_round : nearestAdjacentRoundAway y a b = b :=
            nearestAdjacentRoundAway_eq_right_of_right_closer hy_right
          rw [hx_round, hy_round]
        · have hy_tie : |y - a| = |y - b| := by
            apply le_antisymm
            · exact le_of_not_gt hy_right
            · exact le_of_not_gt hy_not_left
          have hy_round : nearestAdjacentRoundAway y a b = b :=
            nearestAdjacentRoundAway_eq_right_of_tie_abs_ge hy_tie hmag
          rw [hx_round, hy_round]
      · have hx_round : nearestAdjacentRoundAway x a b = a :=
          nearestAdjacentRoundAway_eq_left_of_tie_abs_lt hx_tie hmag
        rw [hx_round]
        exact left_le_nearestAdjacentRoundAway hab

theorem nearestAdjacentRoundToOdd_eq_left_or_right
    (x a b : ℝ) (leftMantissa : ℕ) :
    nearestAdjacentRoundToOdd x a b leftMantissa = a ∨
      nearestAdjacentRoundToOdd x a b leftMantissa = b := by
  unfold nearestAdjacentRoundToOdd
  by_cases hleft : |x - a| < |x - b|
  · simp [hleft]
  · simp [hleft]
    by_cases hright : |x - b| < |x - a|
    · simp [hright]
    · simp [hright]
      by_cases heven : evenMantissa leftMantissa
      · simp [heven]
      · simp [heven]

theorem left_le_nearestAdjacentRoundToOdd
    {x a b : ℝ} {leftMantissa : ℕ}
    (hab : a ≤ b) :
    a ≤ nearestAdjacentRoundToOdd x a b leftMantissa := by
  rcases nearestAdjacentRoundToOdd_eq_left_or_right x a b leftMantissa with h | h
  · rw [h]
  · rw [h]
    exact hab

theorem nearestAdjacentRoundToOdd_le_right
    {x a b : ℝ} {leftMantissa : ℕ}
    (hab : a ≤ b) :
    nearestAdjacentRoundToOdd x a b leftMantissa ≤ b := by
  rcases nearestAdjacentRoundToOdd_eq_left_or_right x a b leftMantissa with h | h
  · rw [h]
    exact hab
  · rw [h]

/-- On a fixed ordered adjacent bracket, round-to-odd is monotone in the exact
input.  This matches the same local nearest-rounding monotonicity surface as
round-to-even; it is not full IEEE operation monotonicity. -/
theorem nearestAdjacentRoundToOdd_monotone_on_ordered_bracket
    {x y a b : ℝ} {leftMantissa : ℕ}
    (hab : a ≤ b)
    (hx : a ≤ x ∧ x ≤ b)
    (hy : a ≤ y ∧ y ≤ b)
    (hxy : x ≤ y) :
    nearestAdjacentRoundToOdd x a b leftMantissa ≤
      nearestAdjacentRoundToOdd y a b leftMantissa := by
  have hx_abs_left : |x - a| = x - a := by
    exact abs_of_nonneg (sub_nonneg.mpr hx.1)
  have hx_abs_right : |x - b| = b - x := by
    rw [abs_of_nonpos (sub_nonpos.mpr hx.2)]
    ring
  have hy_abs_left : |y - a| = y - a := by
    exact abs_of_nonneg (sub_nonneg.mpr hy.1)
  have hy_abs_right : |y - b| = b - y := by
    rw [abs_of_nonpos (sub_nonpos.mpr hy.2)]
    ring
  by_cases hx_left : |x - a| < |x - b|
  · have hx_round :
        nearestAdjacentRoundToOdd x a b leftMantissa = a :=
      nearestAdjacentRoundToOdd_eq_left_of_left_closer hx_left
    rw [hx_round]
    exact left_le_nearestAdjacentRoundToOdd hab
  · by_cases hx_right : |x - b| < |x - a|
    · have hx_round :
          nearestAdjacentRoundToOdd x a b leftMantissa = b :=
        nearestAdjacentRoundToOdd_eq_right_of_right_closer hx_right
      have hy_right : |y - b| < |y - a| := by
        rw [hy_abs_left, hy_abs_right]
        rw [hx_abs_left, hx_abs_right] at hx_right
        linarith
      have hy_round :
          nearestAdjacentRoundToOdd y a b leftMantissa = b :=
        nearestAdjacentRoundToOdd_eq_right_of_right_closer hy_right
      rw [hx_round, hy_round]
    · have hx_tie : |x - a| = |x - b| := by
        apply le_antisymm
        · exact le_of_not_gt hx_right
        · exact le_of_not_gt hx_left
      by_cases heven : evenMantissa leftMantissa
      · have hx_round :
            nearestAdjacentRoundToOdd x a b leftMantissa = b :=
          nearestAdjacentRoundToOdd_eq_right_of_tie_even hx_tie heven
        have hy_not_left : ¬ |y - a| < |y - b| := by
          intro hy_left
          rw [hy_abs_left, hy_abs_right] at hy_left
          rw [hx_abs_left, hx_abs_right] at hx_tie
          linarith
        by_cases hy_right : |y - b| < |y - a|
        · have hy_round :
              nearestAdjacentRoundToOdd y a b leftMantissa = b :=
            nearestAdjacentRoundToOdd_eq_right_of_right_closer hy_right
          rw [hx_round, hy_round]
        · have hy_tie : |y - a| = |y - b| := by
            apply le_antisymm
            · exact le_of_not_gt hy_right
            · exact le_of_not_gt hy_not_left
          have hy_round :
              nearestAdjacentRoundToOdd y a b leftMantissa = b :=
            nearestAdjacentRoundToOdd_eq_right_of_tie_even hy_tie heven
          rw [hx_round, hy_round]
      · have hx_round :
            nearestAdjacentRoundToOdd x a b leftMantissa = a :=
          nearestAdjacentRoundToOdd_eq_left_of_tie_odd hx_tie heven
        rw [hx_round]
        exact left_le_nearestAdjacentRoundToOdd hab

theorem adjacentRoundTowardNegative_eq_left_or_right
    (x a b : ℝ) :
    adjacentRoundTowardNegative x a b = a ∨
      adjacentRoundTowardNegative x a b = b := by
  unfold adjacentRoundTowardNegative
  by_cases hxb : x = b
  · simp [hxb]
  · simp [hxb]

theorem left_le_adjacentRoundTowardNegative
    {x a b : ℝ} (hab : a ≤ b) :
    a ≤ adjacentRoundTowardNegative x a b := by
  rcases adjacentRoundTowardNegative_eq_left_or_right x a b with h | h
  · rw [h]
  · rw [h]
    exact hab

theorem adjacentRoundTowardNegative_le_right
    {x a b : ℝ} (hab : a ≤ b) :
    adjacentRoundTowardNegative x a b ≤ b := by
  rcases adjacentRoundTowardNegative_eq_left_or_right x a b with h | h
  · rw [h]
    exact hab
  · rw [h]

/-- On a fixed ordered adjacent bracket, rounding toward negative infinity is
monotone in the exact input.  This is a local endpoint-selector theorem, not
global finite-format or IEEE operation monotonicity. -/
theorem adjacentRoundTowardNegative_monotone_on_ordered_bracket
    {x y a b : ℝ}
    (hab : a ≤ b)
    (_hx : a ≤ x ∧ x ≤ b)
    (hy : a ≤ y ∧ y ≤ b)
    (hxy : x ≤ y) :
    adjacentRoundTowardNegative x a b ≤
      adjacentRoundTowardNegative y a b := by
  by_cases hxb : x = b
  · have hyb : y = b := by
      apply le_antisymm hy.2
      simpa [hxb] using hxy
    rw [adjacentRoundTowardNegative_eq_right_of_eq_right hxb,
      adjacentRoundTowardNegative_eq_right_of_eq_right hyb]
  · rw [adjacentRoundTowardNegative_eq_left_of_ne_right hxb]
    exact left_le_adjacentRoundTowardNegative hab

theorem adjacentRoundTowardPositive_eq_left_or_right
    (x a b : ℝ) :
    adjacentRoundTowardPositive x a b = a ∨
      adjacentRoundTowardPositive x a b = b := by
  unfold adjacentRoundTowardPositive
  by_cases hxa : x = a
  · simp [hxa]
  · simp [hxa]

theorem left_le_adjacentRoundTowardPositive
    {x a b : ℝ} (hab : a ≤ b) :
    a ≤ adjacentRoundTowardPositive x a b := by
  rcases adjacentRoundTowardPositive_eq_left_or_right x a b with h | h
  · rw [h]
  · rw [h]
    exact hab

theorem adjacentRoundTowardPositive_le_right
    {x a b : ℝ} (hab : a ≤ b) :
    adjacentRoundTowardPositive x a b ≤ b := by
  rcases adjacentRoundTowardPositive_eq_left_or_right x a b with h | h
  · rw [h]
    exact hab
  · rw [h]

/-- On a fixed ordered adjacent bracket, rounding toward positive infinity is
monotone in the exact input.  This is a local endpoint-selector theorem, not
global finite-format or IEEE operation monotonicity. -/
theorem adjacentRoundTowardPositive_monotone_on_ordered_bracket
    {x y a b : ℝ}
    (hab : a ≤ b)
    (hx : a ≤ x ∧ x ≤ b)
    (_hy : a ≤ y ∧ y ≤ b)
    (hxy : x ≤ y) :
    adjacentRoundTowardPositive x a b ≤
      adjacentRoundTowardPositive y a b := by
  by_cases hxa : x = a
  · rw [adjacentRoundTowardPositive_eq_left_of_eq_left hxa]
    exact left_le_adjacentRoundTowardPositive hab
  · have hya : y ≠ a := by
      intro hya
      apply hxa
      apply le_antisymm
      · simpa [hya] using hxy
      · exact hx.1
    rw [adjacentRoundTowardPositive_eq_right_of_ne_left hxa,
      adjacentRoundTowardPositive_eq_right_of_ne_left hya]

theorem adjacentRoundTowardZero_eq_towardPositive_of_nonpos_between
    {x a b : ℝ} (hx : x ≤ b) (hb : b ≤ 0) :
    adjacentRoundTowardZero x a b = adjacentRoundTowardPositive x a b := by
  by_cases hxneg : x < 0
  · exact adjacentRoundTowardZero_eq_towardPositive_of_neg hxneg
  · have hx0 : x = 0 := by
      apply le_antisymm
      · exact le_trans hx hb
      · exact not_lt.mp hxneg
    have hb0 : b = 0 := by
      apply le_antisymm hb
      simpa [hx0] using hx
    by_cases hxa : x = a
    · simp [adjacentRoundTowardZero, adjacentRoundTowardNegative,
        adjacentRoundTowardPositive, hx0, hb0]
    · simp [adjacentRoundTowardZero, adjacentRoundTowardNegative,
        adjacentRoundTowardPositive, hx0, hb0]

/-- On a fixed nonnegative ordered adjacent bracket, the local toward-zero
selector is the toward-negative endpoint selector, hence monotone. -/
theorem adjacentRoundTowardZero_monotone_on_nonnegative_ordered_bracket
    {x y a b : ℝ}
    (ha : 0 ≤ a)
    (hab : a ≤ b)
    (hx : a ≤ x ∧ x ≤ b)
    (hy : a ≤ y ∧ y ≤ b)
    (hxy : x ≤ y) :
    adjacentRoundTowardZero x a b ≤ adjacentRoundTowardZero y a b := by
  have hx_nonneg : 0 ≤ x := le_trans ha hx.1
  have hy_nonneg : 0 ≤ y := le_trans ha hy.1
  rw [adjacentRoundTowardZero_eq_towardNegative_of_nonneg hx_nonneg,
    adjacentRoundTowardZero_eq_towardNegative_of_nonneg hy_nonneg]
  exact adjacentRoundTowardNegative_monotone_on_ordered_bracket
    hab hx hy hxy

/-- On a fixed nonpositive ordered adjacent bracket, the local toward-zero
selector is the toward-positive endpoint selector, hence monotone. -/
theorem adjacentRoundTowardZero_monotone_on_nonpositive_ordered_bracket
    {x y a b : ℝ}
    (hb : b ≤ 0)
    (hab : a ≤ b)
    (hx : a ≤ x ∧ x ≤ b)
    (hy : a ≤ y ∧ y ≤ b)
    (hxy : x ≤ y) :
    adjacentRoundTowardZero x a b ≤ adjacentRoundTowardZero y a b := by
  rw [adjacentRoundTowardZero_eq_towardPositive_of_nonpos_between hx.2 hb,
    adjacentRoundTowardZero_eq_towardPositive_of_nonpos_between hy.2 hb]
  exact adjacentRoundTowardPositive_monotone_on_ordered_bracket
    hab hx hy hxy

theorem finiteUnderflowRoundTowardZeroNonneg_eq_floor_mul
    (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.finiteUnderflowRoundTowardZeroNonneg x =
      (Nat.floor (x / fmt.minSubnormalMagnitude) : ℝ) *
        fmt.minSubnormalMagnitude := by
  unfold finiteUnderflowRoundTowardZeroNonneg
  let q : ℝ := x / fmt.minSubnormalMagnitude
  let m : ℕ := Nat.floor q
  change (if m = 0 then 0 else fmt.subnormalValue false m) =
    (m : ℝ) * fmt.minSubnormalMagnitude
  by_cases hm : m = 0
  · simp [hm]
  · simp [hm, subnormalValue, signValue, minSubnormalMagnitude]

theorem finiteUnderflowRoundTowardZeroNonneg_monotone
    (fmt : FloatingPointFormat) {x y : ℝ}
    (hxy : x ≤ y) :
    fmt.finiteUnderflowRoundTowardZeroNonneg x ≤
      fmt.finiteUnderflowRoundTowardZeroNonneg y := by
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude :=
    le_of_lt fmt.minSubnormalMagnitude_pos
  have hq :
      x / fmt.minSubnormalMagnitude ≤
        y / fmt.minSubnormalMagnitude :=
    div_le_div_of_nonneg_right hxy hηnonneg
  have hfloorNat :
      Nat.floor (x / fmt.minSubnormalMagnitude) ≤
        Nat.floor (y / fmt.minSubnormalMagnitude) :=
    Nat.floor_mono hq
  have hfloor :
      (Nat.floor (x / fmt.minSubnormalMagnitude) : ℝ) ≤
        (Nat.floor (y / fmt.minSubnormalMagnitude) : ℝ) := by
    exact_mod_cast hfloorNat
  rw [fmt.finiteUnderflowRoundTowardZeroNonneg_eq_floor_mul,
    fmt.finiteUnderflowRoundTowardZeroNonneg_eq_floor_mul]
  exact mul_le_mul_of_nonneg_right hfloor hηnonneg

theorem finiteUnderflowRoundTowardZero_monotone_on_nonnegative
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hxnonneg : 0 ≤ x) (hynonneg : 0 ≤ y)
    (hxy : x ≤ y) :
    fmt.finiteUnderflowRoundTowardZero x ≤
      fmt.finiteUnderflowRoundTowardZero y := by
  simp [finiteUnderflowRoundTowardZero, hxnonneg, hynonneg,
    fmt.finiteUnderflowRoundTowardZeroNonneg_monotone hxy]

theorem finiteUnderflowRoundTowardZero_monotone_on_nonpositive
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hy_nonpos : y ≤ 0) (hxy : x ≤ y) :
    fmt.finiteUnderflowRoundTowardZero x ≤
      fmt.finiteUnderflowRoundTowardZero y := by
  unfold finiteUnderflowRoundTowardZero
  by_cases hxnonneg : 0 ≤ x
  · have hx0 : x = 0 := le_antisymm (le_trans hxy hy_nonpos) hxnonneg
    have hy0 : y = 0 := le_antisymm hy_nonpos (by simpa [hx0] using hxy)
    simp [hx0, hy0]
  · by_cases hynonneg : 0 ≤ y
    · have hy0 : y = 0 := le_antisymm hy_nonpos hynonneg
      have hzero :
          fmt.finiteUnderflowRoundTowardZeroNonneg 0 = 0 := by
        rw [fmt.finiteUnderflowRoundTowardZeroNonneg_eq_floor_mul]
        norm_num
      simp [hxnonneg, hy0, hzero]
      have hnonneg :=
        fmt.finiteUnderflowRoundTowardZeroNonneg_nonneg (-x)
      linarith
    · simp [hxnonneg, hynonneg]
      have hneg_order : -y ≤ -x := by linarith
      have hmono :=
        fmt.finiteUnderflowRoundTowardZeroNonneg_monotone hneg_order
      linarith

theorem finiteRoundTowardZero_monotone_on_nonnegative_underflow_branch
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hxnonneg : 0 ≤ x) (hynonneg : 0 ≤ y)
    (hx : fmt.finiteUnderflowRange x)
    (hy : fmt.finiteUnderflowRange y)
    (hxy : x ≤ y) :
    fmt.finiteRoundTowardZero x ≤ fmt.finiteRoundTowardZero y := by
  rw [fmt.finiteRoundTowardZero_eq_underflow hx,
    fmt.finiteRoundTowardZero_eq_underflow hy]
  exact
    fmt.finiteUnderflowRoundTowardZero_monotone_on_nonnegative
      hxnonneg hynonneg hxy

theorem finiteRoundTowardZero_monotone_on_nonpositive_underflow_branch
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hy_nonpos : y ≤ 0)
    (hx : fmt.finiteUnderflowRange x)
    (hy : fmt.finiteUnderflowRange y)
    (hxy : x ≤ y) :
    fmt.finiteRoundTowardZero x ≤ fmt.finiteRoundTowardZero y := by
  rw [fmt.finiteRoundTowardZero_eq_underflow hx,
    fmt.finiteRoundTowardZero_eq_underflow hy]
  exact
    fmt.finiteUnderflowRoundTowardZero_monotone_on_nonpositive
      hy_nonpos hxy

theorem finiteUnderflowRoundTowardPositiveNonneg_eq_ceil_mul_of_nonneg_underflow
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxnonneg : 0 ≤ x) (hunder : fmt.finiteUnderflowRange x) :
    fmt.finiteUnderflowRoundTowardPositiveNonneg x =
      (Nat.ceil (x / fmt.minSubnormalMagnitude) : ℝ) *
        fmt.minSubnormalMagnitude := by
  let q : ℝ := x / fmt.minSubnormalMagnitude
  let m : ℕ := Nat.floor q
  have hηpos := fmt.minSubnormalMagnitude_pos
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude := le_of_lt hηpos
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hxnonneg hηnonneg
  have hx_lt_min : x < fmt.minNormalMagnitude := by
    simpa [finiteUnderflowRange, abs_of_nonneg hxnonneg] using hunder
  have hq_lt_M : q < (fmt.minNormalMantissa : ℝ) := by
    have htarget :=
      fmt.minNormalMagnitude_eq_minNormalMantissa_mul_minSubnormalMagnitude
    dsimp [q]
    rw [div_lt_iff₀ hηpos]
    simpa [htarget, mul_comm] using hx_lt_min
  have hfloor_le : (m : ℝ) ≤ q := Nat.floor_le hq_nonneg
  have hfloor_succ : q < (m + 1 : ℕ) := by
    simpa [m] using Nat.lt_floor_add_one q
  have hm_lt_M : m < fmt.minNormalMantissa :=
    Nat.cast_lt.mp (lt_of_le_of_lt hfloor_le hq_lt_M)
  change
    (if q = (m : ℝ) then
      if m = 0 then 0 else fmt.subnormalValue false m
    else if fmt.minNormalMantissa ≤ m + 1 then
      fmt.minNormalMagnitude
    else
      fmt.subnormalValue false (m + 1)) =
        (Nat.ceil q : ℝ) * fmt.minSubnormalMagnitude
  by_cases hqeq : q = (m : ℝ)
  · have hceil : Nat.ceil q = m := by
      rw [hqeq]
      simp
    rw [hceil]
    by_cases hm0 : m = 0
    · simp [hqeq, hm0]
    · simp [hqeq, hm0, subnormalValue, signValue, minSubnormalMagnitude]
  · have hm_lt_q : (m : ℝ) < q :=
      lt_of_le_of_ne hfloor_le (fun h => hqeq h.symm)
    have hceil_succ : Nat.ceil q = m + 1 := by
      apply (Nat.ceil_eq_iff (Nat.succ_ne_zero m)).2
      constructor
      · simpa using hm_lt_q
      · exact le_of_lt hfloor_succ
    simp [hqeq, hceil_succ]
    by_cases htop : fmt.minNormalMantissa ≤ m + 1
    · simp [htop]
      have hsucc_le_M : m + 1 ≤ fmt.minNormalMantissa :=
        Nat.succ_le_iff.mpr hm_lt_M
      have hsucc_eq_M : m + 1 = fmt.minNormalMantissa :=
        le_antisymm hsucc_le_M htop
      have hcast : (fmt.minNormalMantissa : ℝ) = (m : ℝ) + 1 := by
        rw [← hsucc_eq_M, Nat.cast_add, Nat.cast_one]
      rw [fmt.minNormalMagnitude_eq_minNormalMantissa_mul_minSubnormalMagnitude,
        hcast]
    · simp [htop, subnormalValue, signValue, minSubnormalMagnitude]

theorem finiteUnderflowRoundTowardPositiveNonneg_monotone_on_underflow
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hxnonneg : 0 ≤ x) (hynonneg : 0 ≤ y)
    (hx : fmt.finiteUnderflowRange x)
    (hy : fmt.finiteUnderflowRange y)
    (hxy : x ≤ y) :
    fmt.finiteUnderflowRoundTowardPositiveNonneg x ≤
      fmt.finiteUnderflowRoundTowardPositiveNonneg y := by
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude :=
    le_of_lt fmt.minSubnormalMagnitude_pos
  have hq :
      x / fmt.minSubnormalMagnitude ≤
        y / fmt.minSubnormalMagnitude :=
    div_le_div_of_nonneg_right hxy hηnonneg
  have hceilNat :
      Nat.ceil (x / fmt.minSubnormalMagnitude) ≤
        Nat.ceil (y / fmt.minSubnormalMagnitude) :=
    Nat.ceil_mono hq
  have hceil :
      (Nat.ceil (x / fmt.minSubnormalMagnitude) : ℝ) ≤
        (Nat.ceil (y / fmt.minSubnormalMagnitude) : ℝ) := by
    exact_mod_cast hceilNat
  rw [fmt.finiteUnderflowRoundTowardPositiveNonneg_eq_ceil_mul_of_nonneg_underflow
      hxnonneg hx,
    fmt.finiteUnderflowRoundTowardPositiveNonneg_eq_ceil_mul_of_nonneg_underflow
      hynonneg hy]
  exact mul_le_mul_of_nonneg_right hceil hηnonneg

theorem finiteUnderflowRoundTowardPositive_monotone_on_underflow
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteUnderflowRange x)
    (hy : fmt.finiteUnderflowRange y)
    (hxy : x ≤ y) :
    fmt.finiteUnderflowRoundTowardPositive x ≤
      fmt.finiteUnderflowRoundTowardPositive y := by
  unfold finiteUnderflowRoundTowardPositive
  by_cases hxnonneg : 0 ≤ x
  · by_cases hynonneg : 0 ≤ y
    · simp [hxnonneg, hynonneg]
      exact
        fmt.finiteUnderflowRoundTowardPositiveNonneg_monotone_on_underflow
          hxnonneg hynonneg hx hy hxy
    · exfalso
      linarith
  · by_cases hynonneg : 0 ≤ y
    · simp [hxnonneg, hynonneg]
      have hleft_nonneg :=
        fmt.finiteUnderflowRoundTowardZeroNonneg_nonneg (-x)
      have hright_nonneg :=
        fmt.finiteUnderflowRoundTowardPositiveNonneg_nonneg y
      linarith
    · simp [hxnonneg, hynonneg]
      have hneg_order : -y ≤ -x := by linarith
      have hmono :=
        fmt.finiteUnderflowRoundTowardZeroNonneg_monotone hneg_order
      linarith

theorem finiteUnderflowRoundTowardNegative_monotone_on_underflow
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteUnderflowRange x)
    (hy : fmt.finiteUnderflowRange y)
    (hxy : x ≤ y) :
    fmt.finiteUnderflowRoundTowardNegative x ≤
      fmt.finiteUnderflowRoundTowardNegative y := by
  unfold finiteUnderflowRoundTowardNegative
  by_cases hxnonneg : 0 ≤ x
  · by_cases hynonneg : 0 ≤ y
    · simp [hxnonneg, hynonneg]
      exact fmt.finiteUnderflowRoundTowardZeroNonneg_monotone hxy
    · exfalso
      linarith
  · by_cases hynonneg : 0 ≤ y
    · simp [hxnonneg, hynonneg]
      have hleft_nonneg :=
        fmt.finiteUnderflowRoundTowardPositiveNonneg_nonneg (-x)
      have hright_nonneg :=
        fmt.finiteUnderflowRoundTowardZeroNonneg_nonneg y
      linarith
    · simp [hxnonneg, hynonneg]
      have hxneg_nonneg : 0 ≤ -x := by linarith
      have hyneg_nonneg : 0 ≤ -y := by linarith
      have hx_neg : fmt.finiteUnderflowRange (-x) :=
        (fmt.finiteUnderflowRange_neg_iff x).2 hx
      have hy_neg : fmt.finiteUnderflowRange (-y) :=
        (fmt.finiteUnderflowRange_neg_iff y).2 hy
      have hneg_order : -y ≤ -x := by linarith
      have hmono :=
        fmt.finiteUnderflowRoundTowardPositiveNonneg_monotone_on_underflow
          hyneg_nonneg hxneg_nonneg hy_neg hx_neg hneg_order
      linarith

theorem finiteRoundTowardPositive_monotone_on_underflow_branch
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteUnderflowRange x)
    (hy : fmt.finiteUnderflowRange y)
    (hxy : x ≤ y) :
    fmt.finiteRoundTowardPositive x ≤ fmt.finiteRoundTowardPositive y := by
  rw [fmt.finiteRoundTowardPositive_eq_underflow hx,
    fmt.finiteRoundTowardPositive_eq_underflow hy]
  exact fmt.finiteUnderflowRoundTowardPositive_monotone_on_underflow hx hy hxy

theorem finiteRoundTowardNegative_monotone_on_underflow_branch
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteUnderflowRange x)
    (hy : fmt.finiteUnderflowRange y)
    (hxy : x ≤ y) :
    fmt.finiteRoundTowardNegative x ≤ fmt.finiteRoundTowardNegative y := by
  rw [fmt.finiteRoundTowardNegative_eq_underflow hx,
    fmt.finiteRoundTowardNegative_eq_underflow hy]
  exact fmt.finiteUnderflowRoundTowardNegative_monotone_on_underflow hx hy hxy

theorem not_finiteUnderflowRange_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hover : fmt.finiteOverflowRange x) :
    ¬ fmt.finiteUnderflowRange x := by
  intro hunder
  have hle := fmt.minNormalMagnitude_le_maxFiniteMagnitude
  rw [finiteUnderflowRange] at hunder
  rw [finiteOverflowRange] at hover
  linarith

/-- The source-facing finite overflow saturation branch is monotone as a
function of the exact real input.  This is the overflow-branch dependency used
when lifting local selector monotonicity toward total finite selectors; IEEE
overflow infinities and flags are handled by the separate IEEE result layer. -/
theorem finiteOverflowSaturation_monotone
    (fmt : FloatingPointFormat) {x y : ℝ}
    (hxy : x ≤ y) :
    fmt.finiteOverflowSaturation x ≤ fmt.finiteOverflowSaturation y := by
  unfold finiteOverflowSaturation
  by_cases hxneg : x < 0
  · by_cases hyneg : y < 0
    · simp [hxneg, hyneg]
    · simp [hxneg, hyneg]
      have hM := fmt.maxFiniteMagnitude_nonneg
      linarith
  · by_cases hyneg : y < 0
    · have hxnonneg : 0 ≤ x := le_of_not_gt hxneg
      exfalso
      linarith
    · simp [hxneg, hyneg]

theorem finiteRoundAway_eq_overflow_of_not_underflow
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : ¬ fmt.finiteUnderflowRange x)
    (hover : fmt.finiteOverflowRange x) :
    fmt.finiteRoundAway x = fmt.finiteOverflowSaturation x := by
  classical
  unfold finiteRoundAway
  simp [hunder, hover]

theorem finiteRoundToEven_eq_overflow_of_not_underflow
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : ¬ fmt.finiteUnderflowRange x)
    (hover : fmt.finiteOverflowRange x) :
    fmt.finiteRoundToEven x = fmt.finiteOverflowSaturation x := by
  classical
  unfold finiteRoundToEven
  simp [hunder, hover]

theorem finiteRoundAway_monotone_on_overflow_branch
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteOverflowRange x)
    (hy : fmt.finiteOverflowRange y)
    (hxy : x ≤ y) :
    fmt.finiteRoundAway x ≤ fmt.finiteRoundAway y := by
  have hxunder := fmt.not_finiteUnderflowRange_of_finiteOverflowRange hx
  have hyunder := fmt.not_finiteUnderflowRange_of_finiteOverflowRange hy
  rw [fmt.finiteRoundAway_eq_overflow_of_not_underflow hxunder hx,
    fmt.finiteRoundAway_eq_overflow_of_not_underflow hyunder hy]
  exact fmt.finiteOverflowSaturation_monotone hxy

theorem finiteRoundToEven_monotone_on_overflow_branch
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteOverflowRange x)
    (hy : fmt.finiteOverflowRange y)
    (hxy : x ≤ y) :
    fmt.finiteRoundToEven x ≤ fmt.finiteRoundToEven y := by
  have hxunder := fmt.not_finiteUnderflowRange_of_finiteOverflowRange hx
  have hyunder := fmt.not_finiteUnderflowRange_of_finiteOverflowRange hy
  rw [fmt.finiteRoundToEven_eq_overflow_of_not_underflow hxunder hx,
    fmt.finiteRoundToEven_eq_overflow_of_not_underflow hyunder hy]
  exact fmt.finiteOverflowSaturation_monotone hxy

theorem finiteRoundTowardNegative_monotone_on_overflow_branch
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteOverflowRange x)
    (hy : fmt.finiteOverflowRange y)
    (hxy : x ≤ y) :
    fmt.finiteRoundTowardNegative x ≤ fmt.finiteRoundTowardNegative y := by
  have hxunder := fmt.not_finiteUnderflowRange_of_finiteOverflowRange hx
  have hyunder := fmt.not_finiteUnderflowRange_of_finiteOverflowRange hy
  rw [fmt.finiteRoundTowardNegative_eq_overflow_of_not_underflow hxunder hx,
    fmt.finiteRoundTowardNegative_eq_overflow_of_not_underflow hyunder hy]
  exact fmt.finiteOverflowSaturation_monotone hxy

theorem finiteRoundTowardPositive_monotone_on_overflow_branch
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteOverflowRange x)
    (hy : fmt.finiteOverflowRange y)
    (hxy : x ≤ y) :
    fmt.finiteRoundTowardPositive x ≤ fmt.finiteRoundTowardPositive y := by
  have hxunder := fmt.not_finiteUnderflowRange_of_finiteOverflowRange hx
  have hyunder := fmt.not_finiteUnderflowRange_of_finiteOverflowRange hy
  rw [fmt.finiteRoundTowardPositive_eq_overflow_of_not_underflow hxunder hx,
    fmt.finiteRoundTowardPositive_eq_overflow_of_not_underflow hyunder hy]
  exact fmt.finiteOverflowSaturation_monotone hxy

theorem finiteRoundTowardZero_monotone_on_overflow_branch
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteOverflowRange x)
    (hy : fmt.finiteOverflowRange y)
    (hxy : x ≤ y) :
    fmt.finiteRoundTowardZero x ≤ fmt.finiteRoundTowardZero y := by
  have hxunder := fmt.not_finiteUnderflowRange_of_finiteOverflowRange hx
  have hyunder := fmt.not_finiteUnderflowRange_of_finiteOverflowRange hy
  rw [fmt.finiteRoundTowardZero_eq_overflow_of_not_underflow hxunder hx,
    fmt.finiteRoundTowardZero_eq_overflow_of_not_underflow hyunder hy]
  exact fmt.finiteOverflowSaturation_monotone hxy

theorem finiteRoundToMode_monotone_on_overflow_branch
    {fmt : FloatingPointFormat} (mode : IeeeRoundingMode) {x y : ℝ}
    (hx : fmt.finiteOverflowRange x)
    (hy : fmt.finiteOverflowRange y)
    (hxy : x ≤ y) :
    fmt.finiteRoundToMode mode x ≤ fmt.finiteRoundToMode mode y := by
  cases mode
  · exact fmt.finiteRoundToEven_monotone_on_overflow_branch hx hy hxy
  · exact fmt.finiteRoundTowardZero_monotone_on_overflow_branch hx hy hxy
  · exact fmt.finiteRoundTowardPositive_monotone_on_overflow_branch hx hy hxy
  · exact fmt.finiteRoundTowardNegative_monotone_on_overflow_branch hx hy hxy

/-- The total finite round-to-even selector is globally monotone.

The proof uses only the selector's nearest-finite specification.  If ordered
inputs `x < y` rounded in reverse order to finite values `a > b`, nearestness
would put `x` on or to the right of the midpoint of `a,b` and `y` on or to its
left, a contradiction.  Because this argument does not unfold the selector's
dispatch, it includes underflow-to-normal, normal-to-overflow, and direct
underflow-to-overflow crossings as well as all same-branch cases. -/
theorem finiteRoundToEven_monotone
    (fmt : FloatingPointFormat) :
    Monotone fmt.finiteRoundToEven := by
  intro x y hxy
  by_cases hEq : x = y
  · subst y
    exact le_rfl
  have hxy_lt : x < y := lt_of_le_of_ne hxy hEq
  let a := fmt.finiteRoundToEven x
  let b := fmt.finiteRoundToEven y
  have hxround : fmt.nearestRoundingToFinite x a := by
    simpa [a] using fmt.finiteRoundToEven_nearestRoundingToFinite x
  have hyround : fmt.nearestRoundingToFinite y b := by
    simpa [b] using fmt.finiteRoundToEven_nearestRoundingToFinite y
  by_contra hnot
  have hba : b < a := lt_of_not_ge hnot
  have hxnear : |x - a| ≤ |x - b| :=
    nearestRoundingIn_minimal hxround (nearestRoundingIn_mem hyround)
  have hynear : |y - b| ≤ |y - a| :=
    nearestRoundingIn_minimal hyround (nearestRoundingIn_mem hxround)
  have hxsq : (x - a) ^ 2 ≤ (x - b) ^ 2 := (sq_le_sq).2 hxnear
  have hysq : (y - b) ^ 2 ≤ (y - a) ^ 2 := (sq_le_sq).2 hynear
  have hprod : 0 < (a - b) * (y - x) :=
    mul_pos (sub_pos.mpr hba) (sub_pos.mpr hxy_lt)
  nlinarith

/-- Correctly rounded products preserve the ordering needed in Higham's
discriminant example: if the exact products satisfy `a*c ≤ b*b`, their two
rounded values have a nonnegative difference. -/
theorem finiteRoundToEvenOp_mul_self_sub_mul_nonneg
    {fmt : FloatingPointFormat} {a b c : ℝ}
    (hprod : a * c ≤ b * b) :
    0 ≤
      fmt.finiteRoundToEvenOp BasicOp.mul b b -
        fmt.finiteRoundToEvenOp BasicOp.mul a c := by
  apply sub_nonneg.mpr
  simpa [finiteRoundToEvenOp, BasicOp.exact] using
    fmt.finiteRoundToEven_monotone hprod

end FloatingPointFormat

end

end NumStability
