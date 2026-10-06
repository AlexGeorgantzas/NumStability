-- Analysis/Chopping.lean
--
-- Finite chopping/toward-zero bias surfaces for Higham Chapter 2, §2.9.

import NumStability.Analysis.FloatingPointArithmetic

namespace NumStability

noncomputable section

open scoped BigOperators

namespace FloatingPointFormat

/-!
# Chopping

Higham Chapter 2, §2.9 describes chopping as selecting the representable value
toward zero, and notes that positive quantities rounded this way incur
nonpositive final errors.  The theorems below make that finite-format statement
explicit for the repository's source-facing toward-zero selector and for the
operation wrapper that dispatches through the IEEE `towardZero` mode.
-/

/-- Finite toward-zero rounding never exceeds a nonnegative exact value. -/
theorem finiteRoundTowardZero_le_of_nonneg
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 ≤ x) :
    fmt.finiteRoundTowardZero x ≤ x := by
  have habs := fmt.finiteRoundTowardZero_abs_le_abs x
  rw [abs_of_nonneg hx] at habs
  exact le_trans (le_abs_self (fmt.finiteRoundTowardZero x)) habs

/-- Finite toward-zero rounding is never below a nonpositive exact value. -/
theorem le_finiteRoundTowardZero_of_nonpos
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x ≤ 0) :
    x ≤ fmt.finiteRoundTowardZero x := by
  have habs := fmt.finiteRoundTowardZero_abs_le_abs x
  have hy_lower : -|fmt.finiteRoundTowardZero x| ≤
      fmt.finiteRoundTowardZero x :=
    neg_abs_le (fmt.finiteRoundTowardZero x)
  rw [abs_of_nonpos hx] at habs
  linarith

/-- For a nonnegative exact value, the finite chopping error is nonpositive. -/
theorem finiteRoundTowardZero_error_nonpos_of_nonneg
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 ≤ x) :
    fmt.finiteRoundTowardZero x - x ≤ 0 := by
  have hle := fmt.finiteRoundTowardZero_le_of_nonneg hx
  linarith

/-- For a nonpositive exact value, the finite chopping error is nonnegative. -/
theorem finiteRoundTowardZero_error_nonneg_of_nonpos
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x ≤ 0) :
    0 ≤ fmt.finiteRoundTowardZero x - x := by
  have hle := fmt.le_finiteRoundTowardZero_of_nonpos hx
  linarith

/-- The finite operation wrapper in IEEE `towardZero` mode has nonpositive
final error whenever its exact real operation result is nonnegative. -/
theorem finiteRoundToModeOp_towardZero_error_nonpos_of_exact_nonneg
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : 0 ≤ BasicOp.exact op x y) :
    fmt.finiteRoundToModeOp IeeeRoundingMode.towardZero op x y -
        BasicOp.exact op x y ≤ 0 := by
  simpa [finiteRoundToModeOp, finiteRoundToMode] using
    (fmt.finiteRoundTowardZero_error_nonpos_of_nonneg hxy)

/-- The finite operation wrapper in IEEE `towardZero` mode has nonnegative
final error whenever its exact real operation result is nonpositive. -/
theorem finiteRoundToModeOp_towardZero_error_nonneg_of_exact_nonpos
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : BasicOp.exact op x y ≤ 0) :
    0 ≤
      fmt.finiteRoundToModeOp IeeeRoundingMode.towardZero op x y -
        BasicOp.exact op x y := by
  simpa [finiteRoundToModeOp, finiteRoundToMode] using
    (fmt.finiteRoundTowardZero_error_nonneg_of_nonpos hxy)

/-- Accumulating chopping errors over nonnegative exact values preserves the
one-sided bias: every summand is nonpositive, hence so is the total error. -/
theorem finiteRoundTowardZero_sum_errors_nonpos_of_nonneg
    {fmt : FloatingPointFormat} {ι : Type*} {s : Finset ι} {x : ι → ℝ}
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    (∑ i ∈ s, (fmt.finiteRoundTowardZero (x i) - x i)) ≤ 0 := by
  exact Finset.sum_nonpos fun i hi =>
    fmt.finiteRoundTowardZero_error_nonpos_of_nonneg (hx i hi)

end FloatingPointFormat

/-- Decimal scale `10^places`, used for concrete decimal chopping examples. -/
def decimalScale (places : ℕ) : ℝ :=
  (10 : ℝ) ^ places

theorem decimalScale_pos (places : ℕ) : 0 < decimalScale places := by
  unfold decimalScale
  positivity

/-- Concrete nonnegative decimal chopping routine: multiply by `10^places`,
take the integer floor, and rescale.  This models the three-decimal final
chopping in the Vancouver Stock Exchange note when `places = 3`. -/
def decimalChopToPlaces (places : ℕ) (x : ℝ) : ℝ :=
  (Int.floor (decimalScale places * x) : ℝ) / decimalScale places

theorem decimalChopToPlaces_le
    (places : ℕ) (x : ℝ) :
    decimalChopToPlaces places x ≤ x := by
  have hs := decimalScale_pos places
  have hfloor : ((Int.floor (decimalScale places * x) : ℤ) : ℝ) ≤
      decimalScale places * x := Int.floor_le _
  unfold decimalChopToPlaces
  calc
    ((Int.floor (decimalScale places * x) : ℤ) : ℝ) / decimalScale places
        ≤ (decimalScale places * x) / decimalScale places := by
          exact div_le_div_of_nonneg_right hfloor (le_of_lt hs)
    _ = x := by field_simp [ne_of_gt hs]

theorem decimalChopToPlaces_error_nonpos
    (places : ℕ) (x : ℝ) :
    decimalChopToPlaces places x - x ≤ 0 := by
  have hle := decimalChopToPlaces_le places x
  linarith

theorem decimalChopToPlaces_error_nonneg
    (places : ℕ) (x : ℝ) :
    0 ≤ x - decimalChopToPlaces places x := by
  have hle := decimalChopToPlaces_le places x
  linarith

theorem decimalChopToPlaces_abs_error_lt_scale_inv
    (places : ℕ) (x : ℝ) :
    x - decimalChopToPlaces places x < 1 / decimalScale places := by
  have hs := decimalScale_pos places
  have hfloor_lt :
      decimalScale places * x <
        ((Int.floor (decimalScale places * x) : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  unfold decimalChopToPlaces
  have hsub_lt :
      decimalScale places * x -
          ((Int.floor (decimalScale places * x) : ℤ) : ℝ) < 1 := by
    linarith
  calc
    x - ((Int.floor (decimalScale places * x) : ℤ) : ℝ) /
        decimalScale places
        = (decimalScale places * x -
            ((Int.floor (decimalScale places * x) : ℤ) : ℝ)) /
          decimalScale places := by
            field_simp [ne_of_gt hs]
    _ < 1 / decimalScale places := by
        exact div_lt_div_of_pos_right hsub_lt hs

/-- Three-decimal chopping, the concrete final-value policy in Higham's
Vancouver Stock Exchange note. -/
def decimalChopThree (x : ℝ) : ℝ :=
  decimalChopToPlaces 3 x

theorem decimalChopThree_le (x : ℝ) :
    decimalChopThree x ≤ x :=
  decimalChopToPlaces_le 3 x

theorem decimalChopThree_error_nonpos (x : ℝ) :
    decimalChopThree x - x ≤ 0 :=
  decimalChopToPlaces_error_nonpos 3 x

theorem decimalChopThree_error_nonneg (x : ℝ) :
    0 ≤ x - decimalChopThree x :=
  decimalChopToPlaces_error_nonneg 3 x

theorem decimalChopThree_abs_error_lt_one_thousandth (x : ℝ) :
    x - decimalChopThree x < 1 / 1000 := by
  have h := decimalChopToPlaces_abs_error_lt_scale_inv 3 x
  norm_num [decimalChopThree, decimalScale] at h ⊢
  exact h

/-- Exact three-decimal grid values are fixed by three-decimal chopping. -/
theorem decimalChopThree_grid_eq (m : ℤ) :
    decimalChopThree ((m : ℝ) / 1000) = (m : ℝ) / 1000 := by
  unfold decimalChopThree decimalChopToPlaces decimalScale
  norm_num
  rw [show (1000 : ℝ) * ((m : ℝ) / 1000) = (m : ℝ) by ring]
  simp

theorem decimalChopThree_initial_index :
    decimalChopThree (1000 : ℝ) = 1000 := by
  have h := decimalChopThree_grid_eq 1000000
  norm_num at h
  exact h

/-- Over any finite sequence of exact nonnegative index values, the
three-decimal chopping final errors have nonpositive total bias. -/
theorem decimalChopThree_sum_errors_nonpos
    {ι : Type*} {s : Finset ι} {x : ι → ℝ} :
    (∑ i ∈ s, (decimalChopThree (x i) - x i)) ≤ 0 := by
  exact Finset.sum_nonpos fun i hi => decimalChopThree_error_nonpos (x i)

end

end NumStability
