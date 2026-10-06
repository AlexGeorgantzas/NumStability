-- Analysis/AlternativeNumberSystems.lean
--
-- Small exact models for Higham Chapter 2, §2.7 alternative number systems.

import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace NumStability

noncomputable section

/-!
# Alternative Number Systems

Higham Chapter 2, §2.7 is mostly descriptive, but it gives one precise
mathematical representation for level-index arithmetic.  For a level `l` and
fraction `f`, the positive-side value is obtained by applying `exp` `l` times
to `f`; applying `log` the same number of times recovers `f`.  Numbers in
`(0,1)` are represented by taking the reciprocal of such a positive-side value.
-/

/-- Level-index positive-side decoding: apply `exp` `level` times to the
fractional index. -/
def levelIndexForward (level : ℕ) (frac : ℝ) : ℝ :=
  (Real.exp^[level]) frac

/-- Level-index inverse-side decoding: apply `log` `level` times. -/
def levelIndexBackward (level : ℕ) (x : ℝ) : ℝ :=
  (Real.log^[level]) x

@[simp] theorem levelIndexForward_zero (frac : ℝ) :
    levelIndexForward 0 frac = frac := rfl

@[simp] theorem levelIndexBackward_zero (x : ℝ) :
    levelIndexBackward 0 x = x := rfl

theorem levelIndexForward_succ (level : ℕ) (frac : ℝ) :
    levelIndexForward (level + 1) frac =
      Real.exp (levelIndexForward level frac) := by
  simp [levelIndexForward, Function.iterate_succ_apply']

theorem levelIndexBackward_succ (level : ℕ) (x : ℝ) :
    levelIndexBackward (level + 1) x =
      Real.log (levelIndexBackward level x) := by
  simp [levelIndexBackward, Function.iterate_succ_apply']

/-- Applying the logarithm `level` times to the decoded level-index value
recovers the fractional index. -/
theorem levelIndexBackward_forward (level : ℕ) (frac : ℝ) :
    levelIndexBackward level (levelIndexForward level frac) = frac := by
  induction level with
  | zero => rfl
  | succ level ih =>
      rw [levelIndexBackward, levelIndexForward]
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply',
        Real.log_exp]
      simpa [levelIndexBackward, levelIndexForward] using ih

/-- A source-facing level-index code with fractional part in `[0,1]`.  The
stored real index is `level + frac`; the decoded value is the iterated
exponential value. -/
structure LevelIndexCode where
  level : ℕ
  frac : ℝ
  frac_nonneg : 0 ≤ frac
  frac_le_one : frac ≤ 1

namespace LevelIndexCode

/-- The displayed scalar code `l + f`. -/
def index (c : LevelIndexCode) : ℝ :=
  c.level + c.frac

/-- Decode a level-index code on the `x >= 1` side. -/
def value (c : LevelIndexCode) : ℝ :=
  levelIndexForward c.level c.frac

/-- Decode a level-index code for the reciprocal `0 < x < 1` side. -/
def reciprocalValue (c : LevelIndexCode) : ℝ :=
  (c.value)⁻¹

theorem frac_mem_unit_interval (c : LevelIndexCode) :
    c.frac ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨c.frac_nonneg, c.frac_le_one⟩

theorem backward_value_eq_frac (c : LevelIndexCode) :
    levelIndexBackward c.level c.value = c.frac :=
  levelIndexBackward_forward c.level c.frac

theorem value_pos_of_pos_level (c : LevelIndexCode) (hlevel : 0 < c.level) :
    0 < c.value := by
  cases c with
  | mk level frac frac_nonneg frac_le_one =>
      dsimp at hlevel ⊢
      cases level with
      | zero => cases hlevel
      | succ level =>
          rw [value, levelIndexForward_succ]
          exact Real.exp_pos _

theorem reciprocalValue_pos_of_pos_level
    (c : LevelIndexCode) (hlevel : 0 < c.level) :
    0 < c.reciprocalValue := by
  exact inv_pos.mpr (c.value_pos_of_pos_level hlevel)

theorem reciprocalValue_mul_value_of_pos_level
    (c : LevelIndexCode) (hlevel : 0 < c.level) :
    c.reciprocalValue * c.value = 1 := by
  rw [reciprocalValue]
  exact inv_mul_cancel₀ (ne_of_gt (c.value_pos_of_pos_level hlevel))

theorem value_mul_reciprocalValue_of_pos_level
    (c : LevelIndexCode) (hlevel : 0 < c.level) :
    c.value * c.reciprocalValue = 1 := by
  rw [mul_comm]
  exact c.reciprocalValue_mul_value_of_pos_level hlevel

end LevelIndexCode

end

end NumStability
