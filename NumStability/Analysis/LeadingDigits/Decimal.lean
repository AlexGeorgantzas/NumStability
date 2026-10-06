/-
SPDX-License-Identifier: MIT
-/

import Mathlib.Data.Real.Basic

namespace NumStability

noncomputable section

/-!
# Decimal leading digits

The reusable decimal leading-digit predicate and its elementary normalization
properties. Declaration names retain their historical Problem 2.11 prefix for
API compatibility.
-/

/-- Decimal leading-digit relation: digit `d.val + 1` is the leading digit of
`x` if some decimal scaling places `|x|` in that digit's decade cell. -/
def problem2_11_decimalLeadingDigit (x : ℝ) (d : Fin 9) : Prop :=
  ∃ e : ℤ,
    ((d.val + 1 : ℕ) : ℝ) * (10 : ℝ) ^ e ≤ |x| ∧
      |x| < ((d.val + 2 : ℕ) : ℝ) * (10 : ℝ) ^ e

theorem problem2_11_decimalLeadingDigit_digit_between (d : Fin 9) :
    1 ≤ d.val + 1 ∧ d.val + 1 ≤ 9 := by
  constructor
  · exact Nat.succ_pos d.val
  · exact d.isLt

theorem problem2_11_decimalLeadingDigit_abs_pos
    {x : ℝ} {d : Fin 9}
    (h : problem2_11_decimalLeadingDigit x d) :
    0 < |x| := by
  rcases h with ⟨e, hlow, _hhigh⟩
  have hpow_pos : 0 < (10 : ℝ) ^ e := zpow_pos (by norm_num) e
  have hdigit_pos : (0 : ℝ) < ((d.val + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos d.val
  exact lt_of_lt_of_le (mul_pos hdigit_pos hpow_pos) hlow

theorem problem2_11_decimalLeadingDigit_normalized_bin
    {x : ℝ} {d : Fin 9}
    (h : problem2_11_decimalLeadingDigit x d) :
    ∃ e : ℤ,
      ((d.val + 1 : ℕ) : ℝ) ≤ |x| / (10 : ℝ) ^ e ∧
        |x| / (10 : ℝ) ^ e < ((d.val + 2 : ℕ) : ℝ) := by
  rcases h with ⟨e, hlow, hhigh⟩
  refine ⟨e, ?_, ?_⟩
  · rw [le_div_iff₀ (zpow_pos (by norm_num : (0 : ℝ) < 10) e)]
    exact hlow
  · rw [div_lt_iff₀ (zpow_pos (by norm_num : (0 : ℝ) < 10) e)]
    exact hhigh

/-- Formal version of the Problem 2.11 programming note: after division by the
witnessed power of `10`, a sample with a decimal leading digit lies in
`[1,10)`. -/
theorem problem2_11_decimalLeadingDigit_exists_scaled_mem_one_ten
    {x : ℝ} {d : Fin 9}
    (h : problem2_11_decimalLeadingDigit x d) :
    ∃ e : ℤ,
      1 ≤ |x| / (10 : ℝ) ^ e ∧ |x| / (10 : ℝ) ^ e < 10 := by
  rcases problem2_11_decimalLeadingDigit_normalized_bin h with
    ⟨e, hlow, hhigh⟩
  refine ⟨e, ?_, ?_⟩
  · exact le_trans (by norm_num : (1 : ℝ) ≤ ((d.val + 1 : ℕ) : ℝ)) hlow
  · exact lt_of_lt_of_le hhigh
      (by
        have hd : d.val + 1 ≤ 9 := d.isLt
        have hd' : d.val + 2 ≤ 10 := Nat.succ_le_succ hd
        exact_mod_cast hd')

end

end NumStability
