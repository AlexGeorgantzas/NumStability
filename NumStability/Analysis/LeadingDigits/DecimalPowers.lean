/-
SPDX-License-Identifier: MIT
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import NumStability.Analysis.Equidistribution.AddCircle
import NumStability.Analysis.LeadingDigits.Decimal
import NumStability.Analysis.LeadingDigits.LogarithmicDistribution

noncomputable section

open scoped BigOperators ENNReal NNReal Topology ComplexConjugate
open Filter Set MeasureTheory ProbabilityTheory TopologicalSpace ContinuousMap

namespace NumStability

/-!
# Leading digits of decimal powers

This module connects additive equidistribution on the circle with decimal
leading digits of the power sequence `q ^ k`.
-/

/-- A positive real is a rational power of ten when it is `10^r` for some
rational exponent `r`.  This is the exceptional case in Higham's statement. -/
def IsRationalPowerOfTen (q : ℝ) : Prop :=
  ∃ r : ℚ, q = (10 : ℝ) ^ (r : ℝ)

lemma logb_ten_ne_rat_of_not_rationalPower
    {q : ℝ} (hq : 0 < q) (hnot : ¬ IsRationalPowerOfTen q) (r : ℚ) :
    (r : ℝ) ≠ Real.logb 10 q := by
  intro hr
  apply hnot
  refine ⟨r, ?_⟩
  rw [hr]
  exact (Real.rpow_logb (by norm_num) (by norm_num) hq).symm

lemma addOrderOf_logb_ten_eq_zero
    {q : ℝ} (hq : 0 < q) (hnot : ¬ IsRationalPowerOfTen q) :
    addOrderOf ((Real.logb 10 q : ℝ) : AddCircle (1 : ℝ)) = 0 := by
  rw [addOrderOf_eq_zero_iff,
    AddCircle.not_isOfFinAddOrder_iff_forall_rat_ne_div]
  intro r
  simpa using logb_ten_ne_rat_of_not_rationalPower hq hnot r

/-- Left logarithmic endpoint for decimal leading digit `d.val + 1`. -/
def decimalDigitLo (d : Fin 9) : ℝ :=
  Real.logb 10 (((d.val + 1 : ℕ) : ℝ))

/-- Right logarithmic endpoint for decimal leading digit `d.val + 1`. -/
def decimalDigitHi (d : Fin 9) : ℝ :=
  Real.logb 10 (((d.val + 2 : ℕ) : ℝ))

def decimalDigitArc (d : Fin 9) : Set (AddCircle (1 : ℝ)) :=
  halfOpenArc (decimalDigitLo d) (decimalDigitHi d)

lemma decimalDigit_nat_bounds (d : Fin 9) :
    1 ≤ d.val + 1 ∧ d.val + 2 ≤ 10 := by
  exact ⟨Nat.succ_le_succ (Nat.zero_le _), Nat.succ_le_succ d.isLt⟩

lemma decimalDigitLo_lt_hi (d : Fin 9) :
    decimalDigitLo d < decimalDigitHi d := by
  apply Real.logb_lt_logb (by norm_num : (1 : ℝ) < 10)
  · exact_mod_cast Nat.succ_pos d.val
  · exact_mod_cast Nat.lt_succ_self (d.val + 1)

lemma decimalDigitLo_nonneg (d : Fin 9) :
    0 ≤ decimalDigitLo d := by
  apply Real.logb_nonneg (by norm_num : (1 : ℝ) < 10)
  exact_mod_cast (decimalDigit_nat_bounds d).1

lemma decimalDigitHi_le_one (d : Fin 9) :
    decimalDigitHi d ≤ 1 := by
  calc
    decimalDigitHi d ≤ Real.logb 10 (10 : ℝ) := by
      apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 10)
      · exact_mod_cast Nat.succ_pos (d.val + 1)
      · exact_mod_cast (decimalDigit_nat_bounds d).2
    _ = 1 := Real.logb_self_eq_one (by norm_num)

lemma decimalDigit_interval_length_nonneg (d : Fin 9) :
    0 ≤ decimalDigitHi d - decimalDigitLo d :=
  sub_nonneg.mpr (decimalDigitLo_lt_hi d).le

lemma decimalDigit_interval_length_le_one (d : Fin 9) :
    decimalDigitHi d - decimalDigitLo d ≤ 1 := by
  linarith [decimalDigitLo_nonneg d, decimalDigitHi_le_one d]

lemma decimalDigit_interval_length_eq_mass (d : Fin 9) :
    decimalDigitHi d - decimalDigitLo d =
      logarithmicLeadingDigitMass 10 (d.val + 1) := by
  unfold decimalDigitHi decimalDigitLo Real.logb logarithmicLeadingDigitMass
  push_cast
  ring_nf

lemma logb_ten_zpow (e : ℤ) :
    Real.logb 10 ((10 : ℝ) ^ e) = (e : ℝ) := by
  unfold Real.logb
  rw [Real.log_zpow]
  have hlog : Real.log (10 : ℝ) ≠ 0 := by
    exact Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  field_simp

lemma logb_ten_mul_zpow {x : ℝ} (hx : x ≠ 0) (e : ℤ) :
    Real.logb 10 (x * (10 : ℝ) ^ e) = Real.logb 10 x + (e : ℝ) := by
  rw [Real.logb_mul hx (zpow_ne_zero e (by norm_num : (10 : ℝ) ≠ 0)),
    logb_ten_zpow]

lemma problem2_11_decimalLeadingDigit_iff_logb_sub_int
    {x : ℝ} (hx : 0 < x) (d : Fin 9) :
    problem2_11_decimalLeadingDigit x d ↔
      ∃ e : ℤ, Real.logb 10 x - (e : ℝ) ∈
        Ico (decimalDigitLo d) (decimalDigitHi d) := by
  unfold problem2_11_decimalLeadingDigit
  rw [abs_of_pos hx]
  constructor
  · rintro ⟨e, hlow, hhigh⟩
    refine ⟨e, ?_, ?_⟩
    · have hscaled_pos :
          0 < (((d.val + 1 : ℕ) : ℝ) * (10 : ℝ) ^ e) := by positivity
      have hlog :=
        (Real.logb_le_logb (b := (10 : ℝ)) (by norm_num) hscaled_pos hx).2 hlow
      rw [logb_ten_mul_zpow (by positivity) e] at hlog
      exact le_sub_iff_add_le.mpr hlog
    · have hscaled_pos :
          0 < (((d.val + 2 : ℕ) : ℝ) * (10 : ℝ) ^ e) := by positivity
      have hlog :=
        (Real.logb_lt_logb_iff (b := (10 : ℝ)) (by norm_num) hx hscaled_pos).2 hhigh
      rw [logb_ten_mul_zpow (by positivity) e] at hlog
      exact sub_lt_iff_lt_add.mpr hlog
  · rintro ⟨e, hlow, hhigh⟩
    refine ⟨e, ?_, ?_⟩
    · have hscaled_pos :
          0 < (((d.val + 1 : ℕ) : ℝ) * (10 : ℝ) ^ e) := by positivity
      apply (Real.logb_le_logb (b := (10 : ℝ)) (by norm_num) hscaled_pos hx).1
      rw [logb_ten_mul_zpow (by positivity) e]
      exact (le_sub_iff_add_le.mp hlow)
    · have hscaled_pos :
          0 < (((d.val + 2 : ℕ) : ℝ) * (10 : ℝ) ^ e) := by positivity
      apply (Real.logb_lt_logb_iff (b := (10 : ℝ)) (by norm_num) hx hscaled_pos).1
      rw [logb_ten_mul_zpow (by positivity) e]
      exact (sub_lt_iff_lt_add.mp hhigh)

lemma nsmul_logb_ten_coe (q : ℝ) (k : ℕ) :
    k • ((Real.logb 10 q : ℝ) : AddCircle (1 : ℝ)) =
      ((((k : ℕ) : ℝ) * Real.logb 10 q : ℝ) : AddCircle (1 : ℝ)) := by
  simpa [nsmul_eq_mul] using
    (AddCircle.coe_nsmul (1 : ℝ)
      (n := k) (x := Real.logb 10 q)).symm

lemma orbit_mem_decimalDigitArc_iff
    {q : ℝ} (hq : 0 < q) (d : Fin 9) (k : ℕ) :
    k • ((Real.logb 10 q : ℝ) : AddCircle (1 : ℝ)) ∈ decimalDigitArc d ↔
      problem2_11_decimalLeadingDigit (q ^ k) d := by
  rw [nsmul_logb_ten_coe, decimalDigitArc,
    mem_halfOpenArc_coe_iff_exists_int_sub_mem_Ico
      (decimalDigitLo_lt_hi d) (decimalDigit_interval_length_le_one d),
    problem2_11_decimalLeadingDigit_iff_logb_sub_int (pow_pos hq k) d,
    Real.logb_pow]

end NumStability
