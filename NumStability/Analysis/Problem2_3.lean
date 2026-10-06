-- Analysis/Problem2_3.lean
--
-- Problem-specific theorem surface for Higham Chapter 2, Problem 2.3.

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum
import NumStability.Analysis.FloatingPointArithmetic

namespace NumStability

noncomputable section

namespace FloatingPointFormat

/-!
# Higham Chapter 2, Problem 2.3

Problem 2.3 asks how many IEEE-double numbers lie between adjacent nonzero
IEEE-single numbers.  The familiar normalized count `2^29 - 1` comes from the
precision gap: single has `t = 24`, double has `t = 53`, so one normalized
single ulp contains `2^(53-24)` double ulps.

This module records the same-exponent and exponent-boundary normalized
branches for both signs, plus the dyadic-block subnormal grid branch where the
interior count is `2^(52-s) - 1` for block index `s`.  The branch-family
wrappers also connect arbitrary finite normalized real-order adjacent endpoints
and subnormal grid steps to these constructors.
-/

/-- Mantissa refinement factor from IEEE single precision (`t = 24`) to IEEE
double precision (`t = 53`) in a fixed binary binade. -/
def problem2_3_singleToDoubleMantissaScale : ℕ :=
  2 ^ 29

/-- The double mantissas strictly between adjacent same-exponent single
mantissas after scaling by `2^29`. -/
def problem2_3_sameExponentInteriorDoubleMantissas (m : ℕ) : Finset ℕ :=
  Finset.Icc (m * problem2_3_singleToDoubleMantissaScale + 1)
    ((m + 1) * problem2_3_singleToDoubleMantissaScale - 1)

theorem problem2_3_sameExponentInteriorDoubleMantissas_card (m : ℕ) :
    (problem2_3_sameExponentInteriorDoubleMantissas m).card = 2 ^ 29 - 1 := by
  rw [problem2_3_sameExponentInteriorDoubleMantissas, Nat.card_Icc]
  simp [problem2_3_singleToDoubleMantissaScale]
  omega

theorem problem2_3_sameExponentInteriorDoubleMantissas_mem_iff
    {m n : ℕ} :
    n ∈ problem2_3_sameExponentInteriorDoubleMantissas m ↔
      m * problem2_3_singleToDoubleMantissaScale < n ∧
        n < (m + 1) * problem2_3_singleToDoubleMantissaScale := by
  rw [problem2_3_sameExponentInteriorDoubleMantissas, Finset.mem_Icc]
  constructor
  · intro h
    constructor
    · exact Nat.lt_of_succ_le h.1
    · omega
  · intro h
    constructor
    · exact Nat.succ_le_of_lt h.1
    · omega

private theorem problem2_3_ieee_pow_split (e : ℤ) :
    (2 : ℝ) ^ (e - (24 : ℤ)) =
      (2 : ℝ) ^ (29 : ℤ) * (2 : ℝ) ^ (e - (53 : ℤ)) := by
  rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  ring

theorem problem2_3_ieeeSingle_normalizedValue_eq_ieeeDouble_scaledMantissa
    (negative : Bool) (m : ℕ) (e : ℤ) :
    ieeeSingleFormat.normalizedValue negative m e =
      ieeeDoubleFormat.normalizedValue negative
        (m * problem2_3_singleToDoubleMantissaScale) e := by
  cases negative
  · simp [ieeeSingleFormat, ieeeDoubleFormat, normalizedValue, signValue,
      betaR, problem2_3_singleToDoubleMantissaScale, Nat.cast_mul]
    rw [problem2_3_ieee_pow_split e]
    ring
  · simp [ieeeSingleFormat, ieeeDoubleFormat, normalizedValue, signValue,
      betaR, problem2_3_singleToDoubleMantissaScale, Nat.cast_mul]
    rw [problem2_3_ieee_pow_split e]
    ring

theorem problem2_3_ieeeSingle_minNormal_eq_ieeeDouble_minNormal
    (negative : Bool) (e : ℤ) :
    ieeeSingleFormat.normalizedValue negative
        ieeeSingleFormat.minNormalMantissa (e + 1) =
      ieeeDoubleFormat.normalizedValue negative
        ieeeDoubleFormat.minNormalMantissa (e + 1) := by
  have hmant :
      ieeeSingleFormat.minNormalMantissa *
          problem2_3_singleToDoubleMantissaScale =
        ieeeDoubleFormat.minNormalMantissa := by
    norm_num [problem2_3_singleToDoubleMantissaScale, ieeeSingleFormat,
      ieeeDoubleFormat, minNormalMantissa]
  simpa [hmant] using
    (problem2_3_ieeeSingle_normalizedValue_eq_ieeeDouble_scaledMantissa
      negative ieeeSingleFormat.minNormalMantissa (e + 1))

private theorem problem2_3_ieee_boundary_pow_split (e : ℤ) :
    (2 : ℝ) ^ (23 : ℤ) * (2 : ℝ) ^ ((e + 1) - (24 : ℤ)) =
      (2 : ℝ) ^ (53 : ℤ) * (2 : ℝ) ^ (e - (53 : ℤ)) := by
  rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
    ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  ring

private theorem problem2_3_subnormal_block_pow_split
    (s : ℕ) (hs : s ≤ 52) :
    (2 : ℝ) ^ ((-125 : ℤ) - (24 : ℤ)) =
      (2 : ℝ) ^ (((52 - s : ℕ) : ℤ)) *
        (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) := by
  rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  omega

theorem problem2_3_ieeeDouble_sameExponent_between_iff_mem
    {m n : ℕ} {e : ℤ} :
    (ieeeSingleFormat.normalizedValue false m e <
        ieeeDoubleFormat.normalizedValue false n e ∧
      ieeeDoubleFormat.normalizedValue false n e <
        ieeeSingleFormat.normalizedValue false (m + 1) e) ↔
      n ∈ problem2_3_sameExponentInteriorDoubleMantissas m := by
  constructor
  · intro h
    rw [problem2_3_sameExponentInteriorDoubleMantissas_mem_iff]
    constructor
    · have hscale_pos : 0 < (2 : ℝ) ^ (e - (53 : ℤ)) :=
        zpow_pos (by norm_num : (0 : ℝ) < 2) _
      have hmul :
          ((m : ℝ) * (2 : ℝ) ^ (29 : ℤ)) *
              (2 : ℝ) ^ (e - (53 : ℤ)) <
            (n : ℝ) * (2 : ℝ) ^ (e - (53 : ℤ)) := by
        simpa [ieeeSingleFormat, ieeeDoubleFormat, normalizedValue, signValue,
          betaR, problem2_3_ieee_pow_split e, mul_assoc] using h.1
      have hcoeff :
          (m : ℝ) * (2 : ℝ) ^ (29 : ℤ) < (n : ℝ) :=
        lt_of_mul_lt_mul_right hmul (le_of_lt hscale_pos)
      have hcoeff_nat :
          ((m * problem2_3_singleToDoubleMantissaScale : ℕ) : ℝ) <
            (n : ℝ) := by
        norm_num [problem2_3_singleToDoubleMantissaScale] at hcoeff ⊢
        simpa [Nat.cast_mul] using hcoeff
      exact Nat.cast_lt.mp hcoeff_nat
    · have hscale_pos : 0 < (2 : ℝ) ^ (e - (53 : ℤ)) :=
        zpow_pos (by norm_num : (0 : ℝ) < 2) _
      have hmul :
          (n : ℝ) * (2 : ℝ) ^ (e - (53 : ℤ)) <
            ((m + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (29 : ℤ) *
              (2 : ℝ) ^ (e - (53 : ℤ)) := by
        simpa [ieeeSingleFormat, ieeeDoubleFormat, normalizedValue, signValue,
          betaR, problem2_3_ieee_pow_split e, mul_assoc] using h.2
      have hcoeff :
          (n : ℝ) < ((m + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (29 : ℤ) :=
        lt_of_mul_lt_mul_right hmul (le_of_lt hscale_pos)
      have hcoeff_nat :
          (n : ℝ) <
            (((m + 1) * problem2_3_singleToDoubleMantissaScale : ℕ) : ℝ) := by
        norm_num [problem2_3_singleToDoubleMantissaScale] at hcoeff ⊢
        simpa [Nat.cast_mul] using hcoeff
      exact Nat.cast_lt.mp hcoeff_nat
  · intro hn
    have hbounds :=
      (problem2_3_sameExponentInteriorDoubleMantissas_mem_iff).mp hn
    constructor
    · have hcoeff :
          (m : ℝ) * (2 : ℝ) ^ (29 : ℤ) < (n : ℝ) := by
        have hcast :
            ((m * problem2_3_singleToDoubleMantissaScale : ℕ) : ℝ) <
              (n : ℝ) := by
          exact_mod_cast hbounds.1
        norm_num [problem2_3_singleToDoubleMantissaScale] at hcast ⊢
        simpa [Nat.cast_mul] using hcast
      have hscale_pos : 0 < (2 : ℝ) ^ (e - (53 : ℤ)) :=
        zpow_pos (by norm_num : (0 : ℝ) < 2) _
      have hmul := mul_lt_mul_of_pos_right hcoeff hscale_pos
      simp [ieeeSingleFormat, ieeeDoubleFormat, normalizedValue, signValue,
        betaR]
      rw [problem2_3_ieee_pow_split e]
      simpa [mul_assoc] using hmul
    · have hcoeff :
          (n : ℝ) < ((m + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (29 : ℤ) := by
        have hcast :
            (n : ℝ) <
              (((m + 1) * problem2_3_singleToDoubleMantissaScale : ℕ) : ℝ) := by
          exact_mod_cast hbounds.2
        norm_num [problem2_3_singleToDoubleMantissaScale] at hcast ⊢
        simpa [Nat.cast_mul] using hcast
      have hscale_pos : 0 < (2 : ℝ) ^ (e - (53 : ℤ)) :=
        zpow_pos (by norm_num : (0 : ℝ) < 2) _
      have hmul := mul_lt_mul_of_pos_right hcoeff hscale_pos
      simp [ieeeSingleFormat, ieeeDoubleFormat, normalizedValue, signValue,
        betaR]
      rw [problem2_3_ieee_pow_split e]
      simpa [mul_assoc] using hmul

theorem problem2_3_ieeeDouble_sameExponent_negative_between_iff_mem
    {m n : ℕ} {e : ℤ} :
    (ieeeSingleFormat.normalizedValue true (m + 1) e <
        ieeeDoubleFormat.normalizedValue true n e ∧
      ieeeDoubleFormat.normalizedValue true n e <
        ieeeSingleFormat.normalizedValue true m e) ↔
      n ∈ problem2_3_sameExponentInteriorDoubleMantissas m := by
  constructor
  · intro h
    have hleft :
        ieeeSingleFormat.normalizedValue false m e <
          ieeeDoubleFormat.normalizedValue false n e := by
      rw [ieeeDoubleFormat.normalizedValue_true_eq_neg_false n e,
        ieeeSingleFormat.normalizedValue_true_eq_neg_false m e] at h
      simpa using neg_lt_neg h.2
    have hright :
        ieeeDoubleFormat.normalizedValue false n e <
          ieeeSingleFormat.normalizedValue false (m + 1) e := by
      rw [ieeeSingleFormat.normalizedValue_true_eq_neg_false (m + 1) e,
        ieeeDoubleFormat.normalizedValue_true_eq_neg_false n e] at h
      simpa using neg_lt_neg h.1
    exact (problem2_3_ieeeDouble_sameExponent_between_iff_mem).mp
      ⟨hleft, hright⟩
  · intro hn
    have hpos :=
      (problem2_3_ieeeDouble_sameExponent_between_iff_mem
        (m := m) (n := n) (e := e)).mpr hn
    constructor
    · rw [ieeeSingleFormat.normalizedValue_true_eq_neg_false,
        ieeeDoubleFormat.normalizedValue_true_eq_neg_false]
      exact neg_lt_neg hpos.2
    · rw [ieeeDoubleFormat.normalizedValue_true_eq_neg_false,
        ieeeSingleFormat.normalizedValue_true_eq_neg_false]
      exact neg_lt_neg hpos.1

theorem problem2_3_ieeeSingle_exponentInRange_ieeeDouble
    {e : ℤ} (he : ieeeSingleFormat.exponentInRange e) :
    ieeeDoubleFormat.exponentInRange e := by
  norm_num [ieeeSingleFormat, ieeeDoubleFormat, exponentInRange] at he ⊢
  omega

theorem problem2_3_sameExponentInteriorDoubleMantissa_normalized
    {m r : ℕ}
    (hm : ieeeSingleFormat.normalizedMantissa m)
    (hr : r < problem2_3_singleToDoubleMantissaScale) :
    ieeeDoubleFormat.normalizedMantissa
      (m * problem2_3_singleToDoubleMantissaScale + r) := by
  norm_num [problem2_3_singleToDoubleMantissaScale, ieeeSingleFormat,
    ieeeDoubleFormat, normalizedMantissa, mantissaInRange, minNormalMantissa]
    at hm hr ⊢
  omega

theorem problem2_3_sameExponentInteriorDoubleMantissa_normalized_of_mem
    {m n : ℕ}
    (hm : ieeeSingleFormat.normalizedMantissa m)
    (hn : n ∈ problem2_3_sameExponentInteriorDoubleMantissas m) :
    ieeeDoubleFormat.normalizedMantissa n := by
  have hbounds :=
    (problem2_3_sameExponentInteriorDoubleMantissas_mem_iff).mp hn
  norm_num [problem2_3_singleToDoubleMantissaScale, ieeeSingleFormat,
    ieeeDoubleFormat, normalizedMantissa, mantissaInRange, minNormalMantissa]
    at hm hbounds ⊢
  omega

theorem problem2_3_ieeeDouble_normalized_sameExponent_positive_between_mem
    {m n : ℕ} {e eD : ℤ} {negativeD : Bool}
    (hm : ieeeSingleFormat.normalizedMantissa m)
    (hmnext : ieeeSingleFormat.normalizedMantissa (m + 1))
    (hnD : ieeeDoubleFormat.normalizedMantissa n)
    (hbetween :
      ieeeSingleFormat.normalizedValue false m e <
          ieeeDoubleFormat.normalizedValue negativeD n eD ∧
        ieeeDoubleFormat.normalizedValue negativeD n eD <
          ieeeSingleFormat.normalizedValue false (m + 1) e) :
    negativeD = false ∧ eD = e ∧
      n ∈ problem2_3_sameExponentInteriorDoubleMantissas m := by
  cases negativeD
  · have hmD :
        ieeeDoubleFormat.normalizedMantissa
          (m * problem2_3_singleToDoubleMantissaScale) := by
      norm_num [problem2_3_singleToDoubleMantissaScale, ieeeSingleFormat,
        ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
        minNormalMantissa] at hm ⊢
      omega
    have hmnextD :
        ieeeDoubleFormat.normalizedMantissa
          ((m + 1) * problem2_3_singleToDoubleMantissaScale) := by
      norm_num [problem2_3_singleToDoubleMantissaScale, ieeeSingleFormat,
        ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
        minNormalMantissa] at hmnext ⊢
      omega
    have heD_eq : eD = e := by
      rcases lt_trichotomy eD e with hlt | heq | hgt
      · have hz_lt_leftD :
            ieeeDoubleFormat.normalizedValue false n eD <
              ieeeDoubleFormat.normalizedValue false
                (m * problem2_3_singleToDoubleMantissaScale) e :=
          ieeeDoubleFormat.normalizedValue_false_lt_of_exp_lt hnD hmD hlt
        have hz_lt_left :
            ieeeDoubleFormat.normalizedValue false n eD <
              ieeeSingleFormat.normalizedValue false m e := by
          simpa [problem2_3_ieeeSingle_normalizedValue_eq_ieeeDouble_scaledMantissa]
            using hz_lt_leftD
        exact False.elim ((not_lt_of_ge (le_of_lt hz_lt_left)) hbetween.1)
      · exact heq
      · have rightD_lt_z :
            ieeeDoubleFormat.normalizedValue false
                ((m + 1) * problem2_3_singleToDoubleMantissaScale) e <
              ieeeDoubleFormat.normalizedValue false n eD :=
          ieeeDoubleFormat.normalizedValue_false_lt_of_exp_lt hmnextD hnD hgt
        have right_lt_z :
            ieeeSingleFormat.normalizedValue false (m + 1) e <
              ieeeDoubleFormat.normalizedValue false n eD := by
          simpa [problem2_3_ieeeSingle_normalizedValue_eq_ieeeDouble_scaledMantissa]
            using rightD_lt_z
        exact False.elim ((not_lt_of_ge (le_of_lt right_lt_z)) hbetween.2)
    subst eD
    exact ⟨rfl, rfl,
      (problem2_3_ieeeDouble_sameExponent_between_iff_mem
        (m := m) (n := n) (e := e)).mp hbetween⟩
  · have hleft_pos :
        0 < ieeeSingleFormat.normalizedValue false m e :=
      ieeeSingleFormat.normalizedValue_false_pos hm
    have hz_neg :
        ieeeDoubleFormat.normalizedValue true n eD < 0 :=
      ieeeDoubleFormat.normalizedValue_true_neg hnD
    linarith

set_option maxRecDepth 10000 in
theorem problem2_3_ieeeDouble_minNormalMagnitude_lt_ieeeSingle_normalized_false
    {m : ℕ} {e : ℤ}
    (hm : ieeeSingleFormat.normalizedMantissa m)
    (he : ieeeSingleFormat.exponentInRange e) :
    ieeeDoubleFormat.minNormalMagnitude <
      ieeeSingleFormat.normalizedValue false m e := by
  have hemin : (-126 : ℤ) ≤ e := by
    norm_num [ieeeSingleFormat, exponentInRange] at he
    omega
  have hpow :
      ieeeDoubleFormat.minNormalMagnitude < (2 : ℝ) ^ (e - 1) := by
    have hlt :
        (2 : ℝ) ^ (-1022 : ℤ) < (2 : ℝ) ^ (e - 1) :=
      zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2)
        (by omega : (-1022 : ℤ) < e - 1)
    simpa [ieeeDoubleFormat, minNormalMagnitude, betaR] using hlt
  have hleft :
      (2 : ℝ) ^ (e - 1) ≤
        ieeeSingleFormat.normalizedValue false m e := by
    simpa [ieeeSingleFormat, betaR] using
      (ieeeSingleFormat.normalizedValue_false_lower_power
        (m := m) (e := e) hm)
  exact lt_of_lt_of_le hpow hleft

theorem problem2_3_ieeeSingle_normalized_true_lt_neg_ieeeDouble_minNormalMagnitude
    {m : ℕ} {e : ℤ}
    (hm : ieeeSingleFormat.normalizedMantissa m)
    (he : ieeeSingleFormat.exponentInRange e) :
    ieeeSingleFormat.normalizedValue true m e <
      -ieeeDoubleFormat.minNormalMagnitude := by
  have hpos :=
    problem2_3_ieeeDouble_minNormalMagnitude_lt_ieeeSingle_normalized_false
      (m := m) (e := e) hm he
  rw [ieeeSingleFormat.normalizedValue_true_eq_neg_false]
  linarith

/-- Problem 2.3 normalized same-exponent branch: every interior scaled double
mantissa gives a finite IEEE-double number strictly between the adjacent
positive IEEE-single endpoints. -/
theorem problem2_3_ieeeDouble_between_adjacent_ieeeSingle_sameExponent
    {m r : ℕ} {e : ℤ}
    (hm : ieeeSingleFormat.normalizedMantissa m)
    (_hmnext : ieeeSingleFormat.normalizedMantissa (m + 1))
    (he : ieeeSingleFormat.exponentInRange e)
    (hrlo : 0 < r)
    (hrhi : r < problem2_3_singleToDoubleMantissaScale) :
    ieeeDoubleFormat.finiteSystem
        (ieeeDoubleFormat.normalizedValue false
          (m * problem2_3_singleToDoubleMantissaScale + r) e) ∧
      ieeeSingleFormat.normalizedValue false m e <
        ieeeDoubleFormat.normalizedValue false
          (m * problem2_3_singleToDoubleMantissaScale + r) e ∧
      ieeeDoubleFormat.normalizedValue false
          (m * problem2_3_singleToDoubleMantissaScale + r) e <
        ieeeSingleFormat.normalizedValue false (m + 1) e := by
  have heD : ieeeDoubleFormat.exponentInRange e :=
    problem2_3_ieeeSingle_exponentInRange_ieeeDouble he
  have hmD :
      ieeeDoubleFormat.normalizedMantissa
        (m * problem2_3_singleToDoubleMantissaScale + r) :=
    problem2_3_sameExponentInteriorDoubleMantissa_normalized hm hrhi
  constructor
  · exact Or.inr (Or.inl
      ⟨false, m * problem2_3_singleToDoubleMantissaScale + r, e,
        hmD, heD, rfl⟩)
  · constructor
    · have hn :
          m * problem2_3_singleToDoubleMantissaScale <
            m * problem2_3_singleToDoubleMantissaScale + r :=
        Nat.lt_add_of_pos_right hrlo
      have hcoeff :
          (m : ℝ) * (2 : ℝ) ^ 29 <
            ((m * problem2_3_singleToDoubleMantissaScale + r : ℕ) : ℝ) := by
        norm_num [problem2_3_singleToDoubleMantissaScale] at hn ⊢
        exact_mod_cast hn
      have hscale_pos : 0 < (2 : ℝ) ^ (e - (53 : ℤ)) :=
        zpow_pos (by norm_num : (0 : ℝ) < 2) _
      have hmul := mul_lt_mul_of_pos_right hcoeff hscale_pos
      simp [ieeeSingleFormat, ieeeDoubleFormat, normalizedValue, signValue,
        betaR]
      rw [problem2_3_ieee_pow_split e]
      simpa [mul_assoc] using hmul
    · have hn :
          m * problem2_3_singleToDoubleMantissaScale + r <
            (m + 1) * problem2_3_singleToDoubleMantissaScale := by
        unfold problem2_3_singleToDoubleMantissaScale at hrhi ⊢
        norm_num at hrhi ⊢
        omega
      have hcoeff :
          ((m * problem2_3_singleToDoubleMantissaScale + r : ℕ) : ℝ) <
            ((m + 1 : ℕ) : ℝ) * (2 : ℝ) ^ 29 := by
        norm_num [problem2_3_singleToDoubleMantissaScale] at hn ⊢
        exact_mod_cast hn
      have hscale_pos : 0 < (2 : ℝ) ^ (e - (53 : ℤ)) :=
        zpow_pos (by norm_num : (0 : ℝ) < 2) _
      have hmul := mul_lt_mul_of_pos_right hcoeff hscale_pos
      simp [ieeeSingleFormat, ieeeDoubleFormat, normalizedValue, signValue,
        betaR]
      rw [problem2_3_ieee_pow_split e]
      simpa [mul_assoc] using hmul

/-- Signed same-exponent version of the normalized Problem 2.3 branch.  The
order of adjacent endpoints is orientation-independent: for positive endpoints
the mantissa `m` endpoint is the left endpoint, while for negative endpoints
the mantissa `m + 1` endpoint is the left endpoint. -/
theorem problem2_3_ieeeDouble_between_adjacent_ieeeSingle_sameExponent_signed
    {negative : Bool} {m r : ℕ} {e : ℤ}
    (hm : ieeeSingleFormat.normalizedMantissa m)
    (hmnext : ieeeSingleFormat.normalizedMantissa (m + 1))
    (he : ieeeSingleFormat.exponentInRange e)
    (hrlo : 0 < r)
    (hrhi : r < problem2_3_singleToDoubleMantissaScale) :
    ieeeDoubleFormat.finiteSystem
        (ieeeDoubleFormat.normalizedValue negative
          (m * problem2_3_singleToDoubleMantissaScale + r) e) ∧
      ((ieeeSingleFormat.normalizedValue negative m e <
          ieeeDoubleFormat.normalizedValue negative
            (m * problem2_3_singleToDoubleMantissaScale + r) e ∧
        ieeeDoubleFormat.normalizedValue negative
            (m * problem2_3_singleToDoubleMantissaScale + r) e <
          ieeeSingleFormat.normalizedValue negative (m + 1) e) ∨
      (ieeeSingleFormat.normalizedValue negative (m + 1) e <
          ieeeDoubleFormat.normalizedValue negative
            (m * problem2_3_singleToDoubleMantissaScale + r) e ∧
        ieeeDoubleFormat.normalizedValue negative
            (m * problem2_3_singleToDoubleMantissaScale + r) e <
          ieeeSingleFormat.normalizedValue negative m e)) := by
  have hpos :=
    problem2_3_ieeeDouble_between_adjacent_ieeeSingle_sameExponent
      (m := m) (r := r) (e := e) hm hmnext he hrlo hrhi
  cases negative
  · exact ⟨hpos.1, Or.inl hpos.2⟩
  · have heD : ieeeDoubleFormat.exponentInRange e :=
      problem2_3_ieeeSingle_exponentInRange_ieeeDouble he
    have hmD :
        ieeeDoubleFormat.normalizedMantissa
          (m * problem2_3_singleToDoubleMantissaScale + r) :=
      problem2_3_sameExponentInteriorDoubleMantissa_normalized hm hrhi
    constructor
    · exact Or.inr (Or.inl
        ⟨true, m * problem2_3_singleToDoubleMantissaScale + r, e,
          hmD, heD, rfl⟩)
    · right
      constructor
      · rw [ieeeSingleFormat.normalizedValue_true_eq_neg_false,
          ieeeDoubleFormat.normalizedValue_true_eq_neg_false]
        exact neg_lt_neg hpos.2.2
      · rw [ieeeDoubleFormat.normalizedValue_true_eq_neg_false,
          ieeeSingleFormat.normalizedValue_true_eq_neg_false]
        exact neg_lt_neg hpos.2.1

/-- The double mantissas strictly between the largest single mantissa at
exponent `e` and the smallest single mantissa at exponent `e + 1`. -/
def problem2_3_boundaryInteriorDoubleMantissas : Finset ℕ :=
  Finset.Icc
    (ieeeSingleFormat.maxNormalMantissa *
        problem2_3_singleToDoubleMantissaScale + 1)
    ieeeDoubleFormat.maxNormalMantissa

theorem problem2_3_boundaryInteriorDoubleMantissas_card :
    problem2_3_boundaryInteriorDoubleMantissas.card = 2 ^ 29 - 1 := by
  rw [problem2_3_boundaryInteriorDoubleMantissas, Nat.card_Icc]
  norm_num [problem2_3_singleToDoubleMantissaScale, ieeeSingleFormat,
    ieeeDoubleFormat, maxNormalMantissa]

theorem problem2_3_boundaryInteriorDoubleMantissas_mem_iff
    {n : ℕ} :
    n ∈ problem2_3_boundaryInteriorDoubleMantissas ↔
      ieeeSingleFormat.maxNormalMantissa *
          problem2_3_singleToDoubleMantissaScale < n ∧
        n < 2 ^ 53 := by
  rw [problem2_3_boundaryInteriorDoubleMantissas, Finset.mem_Icc]
  norm_num [problem2_3_singleToDoubleMantissaScale, ieeeSingleFormat,
    ieeeDoubleFormat, maxNormalMantissa]
  omega

theorem problem2_3_ieeeDouble_boundary_between_iff_mem
    {n : ℕ} {e : ℤ} :
    (ieeeSingleFormat.normalizedValue false ieeeSingleFormat.maxNormalMantissa e <
        ieeeDoubleFormat.normalizedValue false n e ∧
      ieeeDoubleFormat.normalizedValue false n e <
        ieeeSingleFormat.normalizedValue false
          ieeeSingleFormat.minNormalMantissa (e + 1)) ↔
      n ∈ problem2_3_boundaryInteriorDoubleMantissas := by
  constructor
  · intro h
    rw [problem2_3_boundaryInteriorDoubleMantissas_mem_iff]
    constructor
    · have hscale_pos : 0 < (2 : ℝ) ^ (e - (53 : ℤ)) :=
        zpow_pos (by norm_num : (0 : ℝ) < 2) _
      have hmul :
          ((ieeeSingleFormat.maxNormalMantissa : ℕ) : ℝ) *
                (2 : ℝ) ^ (29 : ℤ) *
              (2 : ℝ) ^ (e - (53 : ℤ)) <
            (n : ℝ) * (2 : ℝ) ^ (e - (53 : ℤ)) := by
        simpa [ieeeSingleFormat, ieeeDoubleFormat, normalizedValue, signValue,
          betaR, maxNormalMantissa, problem2_3_ieee_pow_split e, mul_assoc]
          using h.1
      have hcoeff :
          ((ieeeSingleFormat.maxNormalMantissa : ℕ) : ℝ) *
              (2 : ℝ) ^ (29 : ℤ) < (n : ℝ) :=
        lt_of_mul_lt_mul_right hmul (le_of_lt hscale_pos)
      have hcoeff_nat :
          ((ieeeSingleFormat.maxNormalMantissa *
                problem2_3_singleToDoubleMantissaScale : ℕ) : ℝ) <
            (n : ℝ) := by
        norm_num [problem2_3_singleToDoubleMantissaScale, ieeeSingleFormat,
          maxNormalMantissa] at hcoeff ⊢
        simpa [Nat.cast_mul] using hcoeff
      exact Nat.cast_lt.mp hcoeff_nat
    · have hscale_pos : 0 < (2 : ℝ) ^ (e - (53 : ℤ)) :=
        zpow_pos (by norm_num : (0 : ℝ) < 2) _
      have hmul :
          (n : ℝ) * (2 : ℝ) ^ (e - (53 : ℤ)) <
            (2 : ℝ) ^ (53 : ℤ) * (2 : ℝ) ^ (e - (53 : ℤ)) := by
        calc
          (n : ℝ) * (2 : ℝ) ^ (e - (53 : ℤ)) =
              ieeeDoubleFormat.normalizedValue false n e := by
            simp [ieeeDoubleFormat, normalizedValue, signValue, betaR]
          _ < ieeeSingleFormat.normalizedValue false
                ieeeSingleFormat.minNormalMantissa (e + 1) := h.2
          _ = (2 : ℝ) ^ (53 : ℤ) * (2 : ℝ) ^ (e - (53 : ℤ)) := by
            rw [← problem2_3_ieee_boundary_pow_split e]
            norm_num [ieeeSingleFormat, normalizedValue, signValue, betaR,
              minNormalMantissa]
      have hcoeff : (n : ℝ) < (2 : ℝ) ^ (53 : ℤ) :=
        lt_of_mul_lt_mul_right hmul (le_of_lt hscale_pos)
      have hcoeff_nat : (n : ℝ) < ((2 ^ 53 : ℕ) : ℝ) := by
        norm_num at hcoeff ⊢
        simpa using hcoeff
      exact Nat.cast_lt.mp hcoeff_nat
  · intro hn
    have hbounds :=
      (problem2_3_boundaryInteriorDoubleMantissas_mem_iff).mp hn
    constructor
    · have hcoeff :
          ((ieeeSingleFormat.maxNormalMantissa : ℕ) : ℝ) *
              (2 : ℝ) ^ (29 : ℤ) < (n : ℝ) := by
        have hcast :
            ((ieeeSingleFormat.maxNormalMantissa *
                  problem2_3_singleToDoubleMantissaScale : ℕ) : ℝ) <
              (n : ℝ) := by
          exact_mod_cast hbounds.1
        norm_num [problem2_3_singleToDoubleMantissaScale, ieeeSingleFormat,
          maxNormalMantissa] at hcast ⊢
        simpa [Nat.cast_mul] using hcast
      have hscale_pos : 0 < (2 : ℝ) ^ (e - (53 : ℤ)) :=
        zpow_pos (by norm_num : (0 : ℝ) < 2) _
      have hmul := mul_lt_mul_of_pos_right hcoeff hscale_pos
      simp [ieeeSingleFormat, ieeeDoubleFormat, normalizedValue, signValue,
        betaR, maxNormalMantissa]
      rw [problem2_3_ieee_pow_split e]
      simpa [mul_assoc] using hmul
    · have hcoeff : (n : ℝ) < (2 : ℝ) ^ (53 : ℤ) := by
        have hcast : (n : ℝ) < ((2 ^ 53 : ℕ) : ℝ) := by
          exact_mod_cast hbounds.2
        norm_num at hcast ⊢
        simpa using hcast
      have hscale_pos : 0 < (2 : ℝ) ^ (e - (53 : ℤ)) :=
        zpow_pos (by norm_num : (0 : ℝ) < 2) _
      have hmul := mul_lt_mul_of_pos_right hcoeff hscale_pos
      calc
        ieeeDoubleFormat.normalizedValue false n e =
            (n : ℝ) * (2 : ℝ) ^ (e - (53 : ℤ)) := by
          simp [ieeeDoubleFormat, normalizedValue, signValue, betaR]
        _ < (2 : ℝ) ^ (53 : ℤ) * (2 : ℝ) ^ (e - (53 : ℤ)) := hmul
        _ = ieeeSingleFormat.normalizedValue false
            ieeeSingleFormat.minNormalMantissa (e + 1) := by
          rw [← problem2_3_ieee_boundary_pow_split e]
          norm_num [ieeeSingleFormat, normalizedValue, signValue, betaR,
            minNormalMantissa]

theorem problem2_3_ieeeDouble_boundary_negative_between_iff_mem
    {n : ℕ} {e : ℤ} :
    (ieeeSingleFormat.normalizedValue true
          ieeeSingleFormat.minNormalMantissa (e + 1) <
        ieeeDoubleFormat.normalizedValue true n e ∧
      ieeeDoubleFormat.normalizedValue true n e <
        ieeeSingleFormat.normalizedValue true
          ieeeSingleFormat.maxNormalMantissa e) ↔
      n ∈ problem2_3_boundaryInteriorDoubleMantissas := by
  constructor
  · intro h
    have hleft :
        ieeeSingleFormat.normalizedValue false
            ieeeSingleFormat.maxNormalMantissa e <
          ieeeDoubleFormat.normalizedValue false n e := by
      rw [ieeeDoubleFormat.normalizedValue_true_eq_neg_false n e,
        ieeeSingleFormat.normalizedValue_true_eq_neg_false
          ieeeSingleFormat.maxNormalMantissa e] at h
      simpa using neg_lt_neg h.2
    have hright :
        ieeeDoubleFormat.normalizedValue false n e <
          ieeeSingleFormat.normalizedValue false
            ieeeSingleFormat.minNormalMantissa (e + 1) := by
      rw [ieeeSingleFormat.normalizedValue_true_eq_neg_false
          ieeeSingleFormat.minNormalMantissa (e + 1),
        ieeeDoubleFormat.normalizedValue_true_eq_neg_false n e] at h
      simpa using neg_lt_neg h.1
    exact (problem2_3_ieeeDouble_boundary_between_iff_mem).mp
      ⟨hleft, hright⟩
  · intro hn
    have hpos :=
      (problem2_3_ieeeDouble_boundary_between_iff_mem (n := n) (e := e)).mpr hn
    constructor
    · rw [ieeeSingleFormat.normalizedValue_true_eq_neg_false,
        ieeeDoubleFormat.normalizedValue_true_eq_neg_false]
      exact neg_lt_neg hpos.2
    · rw [ieeeDoubleFormat.normalizedValue_true_eq_neg_false,
        ieeeSingleFormat.normalizedValue_true_eq_neg_false]
      exact neg_lt_neg hpos.1

theorem problem2_3_boundaryInteriorDoubleMantissa_normalized
    {r : ℕ}
    (hr : r < problem2_3_singleToDoubleMantissaScale) :
    ieeeDoubleFormat.normalizedMantissa
      (ieeeSingleFormat.maxNormalMantissa *
        problem2_3_singleToDoubleMantissaScale + r) := by
  norm_num [problem2_3_singleToDoubleMantissaScale, ieeeSingleFormat,
    ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
    minNormalMantissa, maxNormalMantissa] at hr ⊢
  omega

theorem problem2_3_boundaryInteriorDoubleMantissa_normalized_of_mem
    {n : ℕ}
    (hn : n ∈ problem2_3_boundaryInteriorDoubleMantissas) :
    ieeeDoubleFormat.normalizedMantissa n := by
  have hbounds :=
    (problem2_3_boundaryInteriorDoubleMantissas_mem_iff).mp hn
  norm_num [problem2_3_singleToDoubleMantissaScale, ieeeSingleFormat,
    ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
    minNormalMantissa, maxNormalMantissa] at hbounds ⊢
  omega

theorem problem2_3_ieeeDouble_normalized_boundary_positive_between_mem
    {n : ℕ} {e eD : ℤ} {negativeD : Bool}
    (hnD : ieeeDoubleFormat.normalizedMantissa n)
    (hbetween :
      ieeeSingleFormat.normalizedValue false
          ieeeSingleFormat.maxNormalMantissa e <
          ieeeDoubleFormat.normalizedValue negativeD n eD ∧
        ieeeDoubleFormat.normalizedValue negativeD n eD <
          ieeeSingleFormat.normalizedValue false
            ieeeSingleFormat.minNormalMantissa (e + 1)) :
    negativeD = false ∧ eD = e ∧
      n ∈ problem2_3_boundaryInteriorDoubleMantissas := by
  cases negativeD
  · have hleftD :
        ieeeDoubleFormat.normalizedMantissa
          (ieeeSingleFormat.maxNormalMantissa *
            problem2_3_singleToDoubleMantissaScale) := by
      norm_num [problem2_3_singleToDoubleMantissaScale, ieeeSingleFormat,
        ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
        minNormalMantissa, maxNormalMantissa]
    have heD_eq : eD = e := by
      rcases lt_trichotomy eD e with hlt | heq | hgt
      · have hz_lt_leftD :
            ieeeDoubleFormat.normalizedValue false n eD <
              ieeeDoubleFormat.normalizedValue false
                (ieeeSingleFormat.maxNormalMantissa *
                  problem2_3_singleToDoubleMantissaScale) e :=
          ieeeDoubleFormat.normalizedValue_false_lt_of_exp_lt hnD hleftD hlt
        have hz_lt_left :
            ieeeDoubleFormat.normalizedValue false n eD <
              ieeeSingleFormat.normalizedValue false
                ieeeSingleFormat.maxNormalMantissa e := by
          simpa [problem2_3_ieeeSingle_normalizedValue_eq_ieeeDouble_scaledMantissa]
            using hz_lt_leftD
        exact False.elim ((not_lt_of_ge (le_of_lt hz_lt_left)) hbetween.1)
      · exact heq
      · have hrightD_le_z :
            ieeeDoubleFormat.normalizedValue false
                ieeeDoubleFormat.minNormalMantissa (e + 1) ≤
              ieeeDoubleFormat.normalizedValue false n eD :=
          ieeeDoubleFormat.normalizedValue_false_minNormalMantissa_le_of_exp_le
            hnD (by omega : e + 1 ≤ eD)
        have hright_le_z :
            ieeeSingleFormat.normalizedValue false
                ieeeSingleFormat.minNormalMantissa (e + 1) ≤
              ieeeDoubleFormat.normalizedValue false n eD := by
          simpa [problem2_3_ieeeSingle_minNormal_eq_ieeeDouble_minNormal]
            using hrightD_le_z
        exact False.elim ((not_lt_of_ge hright_le_z) hbetween.2)
    subst eD
    exact ⟨rfl, rfl,
      (problem2_3_ieeeDouble_boundary_between_iff_mem
        (n := n) (e := e)).mp hbetween⟩
  · have hleft_pos :
        0 < ieeeSingleFormat.normalizedValue false
          ieeeSingleFormat.maxNormalMantissa e :=
      ieeeSingleFormat.normalizedValue_false_pos
        ieeeSingleFormat.maxNormalMantissa_normalized
    have hz_neg :
        ieeeDoubleFormat.normalizedValue true n eD < 0 :=
      ieeeDoubleFormat.normalizedValue_true_neg hnD
    linarith

/-- Problem 2.3 normalized exponent-boundary branch: every interior scaled
double mantissa gives a finite IEEE-double number strictly between the largest
positive IEEE-single value at exponent `e` and the smallest positive IEEE-single
value at exponent `e + 1`. -/
theorem problem2_3_ieeeDouble_between_adjacent_ieeeSingle_boundary
    {r : ℕ} {e : ℤ}
    (he : ieeeSingleFormat.exponentInRange e)
    (_heNext : ieeeSingleFormat.exponentInRange (e + 1))
    (hrlo : 0 < r)
    (hrhi : r < problem2_3_singleToDoubleMantissaScale) :
    ieeeDoubleFormat.finiteSystem
        (ieeeDoubleFormat.normalizedValue false
          (ieeeSingleFormat.maxNormalMantissa *
            problem2_3_singleToDoubleMantissaScale + r) e) ∧
      ieeeSingleFormat.normalizedValue false ieeeSingleFormat.maxNormalMantissa e <
        ieeeDoubleFormat.normalizedValue false
          (ieeeSingleFormat.maxNormalMantissa *
            problem2_3_singleToDoubleMantissaScale + r) e ∧
      ieeeDoubleFormat.normalizedValue false
          (ieeeSingleFormat.maxNormalMantissa *
            problem2_3_singleToDoubleMantissaScale + r) e <
        ieeeSingleFormat.normalizedValue false ieeeSingleFormat.minNormalMantissa (e + 1) := by
  have heD : ieeeDoubleFormat.exponentInRange e :=
    problem2_3_ieeeSingle_exponentInRange_ieeeDouble he
  have hmD :
      ieeeDoubleFormat.normalizedMantissa
        (ieeeSingleFormat.maxNormalMantissa *
          problem2_3_singleToDoubleMantissaScale + r) :=
    problem2_3_boundaryInteriorDoubleMantissa_normalized hrhi
  constructor
  · exact Or.inr (Or.inl
      ⟨false,
        ieeeSingleFormat.maxNormalMantissa *
          problem2_3_singleToDoubleMantissaScale + r,
        e, hmD, heD, rfl⟩)
  · constructor
    · have hn :
          ieeeSingleFormat.maxNormalMantissa *
              problem2_3_singleToDoubleMantissaScale <
            ieeeSingleFormat.maxNormalMantissa *
              problem2_3_singleToDoubleMantissaScale + r :=
        Nat.lt_add_of_pos_right hrlo
      have hcoeff :
          ((ieeeSingleFormat.maxNormalMantissa : ℕ) : ℝ) * (2 : ℝ) ^ 29 <
            ((ieeeSingleFormat.maxNormalMantissa *
                problem2_3_singleToDoubleMantissaScale + r : ℕ) : ℝ) := by
        norm_num [problem2_3_singleToDoubleMantissaScale, ieeeSingleFormat,
          maxNormalMantissa] at hn ⊢
        exact_mod_cast hn
      have hscale_pos : 0 < (2 : ℝ) ^ (e - (53 : ℤ)) :=
        zpow_pos (by norm_num : (0 : ℝ) < 2) _
      have hmul := mul_lt_mul_of_pos_right hcoeff hscale_pos
      simp [ieeeSingleFormat, ieeeDoubleFormat, normalizedValue, signValue,
        betaR, maxNormalMantissa]
      rw [problem2_3_ieee_pow_split e]
      simpa [mul_assoc] using hmul
    · have hn :
          ieeeSingleFormat.maxNormalMantissa *
              problem2_3_singleToDoubleMantissaScale + r <
            ieeeDoubleFormat.beta ^ ieeeDoubleFormat.t := by
        unfold problem2_3_singleToDoubleMantissaScale at hrhi ⊢
        norm_num [ieeeSingleFormat, ieeeDoubleFormat, maxNormalMantissa] at hrhi ⊢
        omega
      have hcoeff :
          ((ieeeSingleFormat.maxNormalMantissa *
              problem2_3_singleToDoubleMantissaScale + r : ℕ) : ℝ) <
            (2 : ℝ) ^ (53 : ℤ) := by
        norm_num [problem2_3_singleToDoubleMantissaScale, ieeeSingleFormat,
          ieeeDoubleFormat, maxNormalMantissa] at hn ⊢
        exact_mod_cast hn
      have hscale_pos : 0 < (2 : ℝ) ^ (e - (53 : ℤ)) :=
        zpow_pos (by norm_num : (0 : ℝ) < 2) _
      have hmul := mul_lt_mul_of_pos_right hcoeff hscale_pos
      calc
        ieeeDoubleFormat.normalizedValue false
            (ieeeSingleFormat.maxNormalMantissa *
              problem2_3_singleToDoubleMantissaScale + r) e =
            ((ieeeSingleFormat.maxNormalMantissa *
                problem2_3_singleToDoubleMantissaScale + r : ℕ) : ℝ) *
              (2 : ℝ) ^ (e - (53 : ℤ)) := by
          simp [ieeeDoubleFormat, normalizedValue, signValue, betaR]
        _ < (2 : ℝ) ^ (53 : ℤ) * (2 : ℝ) ^ (e - (53 : ℤ)) := hmul
        _ = ieeeSingleFormat.normalizedValue false
            ieeeSingleFormat.minNormalMantissa (e + 1) := by
          rw [← problem2_3_ieee_boundary_pow_split e]
          norm_num [ieeeSingleFormat, normalizedValue, signValue, betaR,
            minNormalMantissa]

/-- Signed exponent-boundary version of the normalized Problem 2.3 branch. -/
theorem problem2_3_ieeeDouble_between_adjacent_ieeeSingle_boundary_signed
    {negative : Bool} {r : ℕ} {e : ℤ}
    (he : ieeeSingleFormat.exponentInRange e)
    (heNext : ieeeSingleFormat.exponentInRange (e + 1))
    (hrlo : 0 < r)
    (hrhi : r < problem2_3_singleToDoubleMantissaScale) :
    ieeeDoubleFormat.finiteSystem
        (ieeeDoubleFormat.normalizedValue negative
          (ieeeSingleFormat.maxNormalMantissa *
            problem2_3_singleToDoubleMantissaScale + r) e) ∧
      ((ieeeSingleFormat.normalizedValue negative ieeeSingleFormat.maxNormalMantissa e <
          ieeeDoubleFormat.normalizedValue negative
            (ieeeSingleFormat.maxNormalMantissa *
              problem2_3_singleToDoubleMantissaScale + r) e ∧
        ieeeDoubleFormat.normalizedValue negative
            (ieeeSingleFormat.maxNormalMantissa *
              problem2_3_singleToDoubleMantissaScale + r) e <
          ieeeSingleFormat.normalizedValue negative
            ieeeSingleFormat.minNormalMantissa (e + 1)) ∨
      (ieeeSingleFormat.normalizedValue negative
            ieeeSingleFormat.minNormalMantissa (e + 1) <
          ieeeDoubleFormat.normalizedValue negative
            (ieeeSingleFormat.maxNormalMantissa *
              problem2_3_singleToDoubleMantissaScale + r) e ∧
        ieeeDoubleFormat.normalizedValue negative
            (ieeeSingleFormat.maxNormalMantissa *
              problem2_3_singleToDoubleMantissaScale + r) e <
          ieeeSingleFormat.normalizedValue negative ieeeSingleFormat.maxNormalMantissa e)) := by
  have hpos :=
    problem2_3_ieeeDouble_between_adjacent_ieeeSingle_boundary
      (r := r) (e := e) he heNext hrlo hrhi
  cases negative
  · exact ⟨hpos.1, Or.inl hpos.2⟩
  · have heD : ieeeDoubleFormat.exponentInRange e :=
      problem2_3_ieeeSingle_exponentInRange_ieeeDouble he
    have hmD :
        ieeeDoubleFormat.normalizedMantissa
          (ieeeSingleFormat.maxNormalMantissa *
            problem2_3_singleToDoubleMantissaScale + r) :=
      problem2_3_boundaryInteriorDoubleMantissa_normalized hrhi
    constructor
    · exact Or.inr (Or.inl
        ⟨true,
          ieeeSingleFormat.maxNormalMantissa *
            problem2_3_singleToDoubleMantissaScale + r,
          e, hmD, heD, rfl⟩)
    · right
      constructor
      · rw [ieeeSingleFormat.normalizedValue_true_eq_neg_false,
          ieeeDoubleFormat.normalizedValue_true_eq_neg_false]
        exact neg_lt_neg hpos.2.2
      · rw [ieeeDoubleFormat.normalizedValue_true_eq_neg_false,
          ieeeSingleFormat.normalizedValue_true_eq_neg_false]
        exact neg_lt_neg hpos.2.1

/-- The double mantissas strictly between the first two positive IEEE-single
subnormal numbers, represented at double exponent `-148`. -/
def problem2_3_smallestSubnormalInteriorDoubleMantissas : Finset ℕ :=
  Finset.Icc (2 ^ 52 + 1) (2 ^ 53 - 1)

theorem problem2_3_smallestSubnormalInteriorDoubleMantissas_card :
    problem2_3_smallestSubnormalInteriorDoubleMantissas.card = 2 ^ 52 - 1 := by
  rw [problem2_3_smallestSubnormalInteriorDoubleMantissas, Nat.card_Icc]
  norm_num

theorem problem2_3_smallestSubnormalInteriorDoubleMantissas_mem_iff
    {n : ℕ} :
    n ∈ problem2_3_smallestSubnormalInteriorDoubleMantissas ↔
      2 ^ 52 < n ∧ n < 2 ^ 53 := by
  rw [problem2_3_smallestSubnormalInteriorDoubleMantissas, Finset.mem_Icc]
  omega

theorem problem2_3_ieeeSingle_one_subnormalMantissa :
    ieeeSingleFormat.subnormalMantissa 1 := by
  norm_num [ieeeSingleFormat, subnormalMantissa, minNormalMantissa]

theorem problem2_3_ieeeSingle_two_subnormalMantissa :
    ieeeSingleFormat.subnormalMantissa 2 := by
  norm_num [ieeeSingleFormat, subnormalMantissa, minNormalMantissa]

theorem problem2_3_smallestSubnormalInteriorDoubleMantissa_normalized
    {r : ℕ}
    (hr : r < 2 ^ 52) :
    ieeeDoubleFormat.normalizedMantissa (2 ^ 52 + r) := by
  norm_num [ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
    minNormalMantissa] at hr ⊢
  omega

/-- The double-mantissa refinement factor for a positive single-subnormal grid
step whose left mantissa lies in the dyadic block indexed by `s`. -/
def problem2_3_subnormalBlockScale (s : ℕ) : ℕ :=
  2 ^ (52 - s)

theorem problem2_3_ieeeSingle_subnormalValue_eq_ieeeDouble_scaledMantissa
    (negative : Bool) (s m : ℕ) (hs : s ≤ 52) :
    ieeeSingleFormat.subnormalValue negative m =
      ieeeDoubleFormat.normalizedValue negative
        (m * problem2_3_subnormalBlockScale s) ((s : ℤ) - 148) := by
  have hpow :
      (2 ^ 149 : ℝ)⁻¹ =
        (2 : ℝ) ^ (((52 - s : ℕ) : ℤ)) *
          (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) := by
    have hleft :
        (2 : ℝ) ^ ((-125 : ℤ) - (24 : ℤ)) = (2 ^ 149 : ℝ)⁻¹ := by
      norm_num [zpow_neg]
    calc
      (2 ^ 149 : ℝ)⁻¹ =
          (2 : ℝ) ^ ((-125 : ℤ) - (24 : ℤ)) := hleft.symm
      _ = (2 : ℝ) ^ (((52 - s : ℕ) : ℤ)) *
          (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) :=
            problem2_3_subnormal_block_pow_split s hs
  have hpowNat :
      (2 ^ 149 : ℝ)⁻¹ =
        (2 : ℝ) ^ (52 - s) *
          (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) := by
    calc
      (2 ^ 149 : ℝ)⁻¹ =
          (2 : ℝ) ^ (((52 - s : ℕ) : ℤ)) *
            (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) := hpow
      _ = (2 : ℝ) ^ (52 - s) *
          (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) := by
        rw [zpow_natCast]
  cases negative
  · simp [ieeeSingleFormat, ieeeDoubleFormat, subnormalValue,
      normalizedValue, signValue, betaR, problem2_3_subnormalBlockScale,
      Nat.cast_mul]
    calc
      (m : ℝ) * (2 ^ 149 : ℝ)⁻¹ =
          (m : ℝ) * ((2 : ℝ) ^ (52 - s) *
            (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ))) := by
        exact congrArg (fun y => (m : ℝ) * y) hpowNat
      _ = (m : ℝ) * (2 : ℝ) ^ (52 - s) *
            (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) := by
        ring
  · simp [ieeeSingleFormat, ieeeDoubleFormat, subnormalValue,
      normalizedValue, signValue, betaR, problem2_3_subnormalBlockScale,
      Nat.cast_mul]
    calc
      (m : ℝ) * (2 ^ 149 : ℝ)⁻¹ =
          (m : ℝ) * ((2 : ℝ) ^ (52 - s) *
            (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ))) := by
        exact congrArg (fun y => (m : ℝ) * y) hpowNat
      _ = (m : ℝ) * (2 : ℝ) ^ (52 - s) *
            (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) := by
        ring

theorem problem2_3_ieeeSingle_subnormalMantissa_of_block
    {s m : ℕ}
    (hs : s ≤ 22)
    (hmlo : 2 ^ s ≤ m)
    (hmhi : m + 1 ≤ 2 ^ (s + 1)) :
    ieeeSingleFormat.subnormalMantissa m := by
  have hpow_pos : 0 < 2 ^ s :=
    pow_pos (by norm_num : (0 : ℕ) < 2) s
  have hmpos : 0 < m := lt_of_lt_of_le hpow_pos hmlo
  have hpow_le : 2 ^ (s + 1) ≤ 2 ^ 23 :=
    pow_le_pow_right₀ (by norm_num : (0 : ℕ) < 2) (by omega : s + 1 ≤ 23)
  have hm_lt : m < 2 ^ 23 :=
    lt_of_lt_of_le (Nat.lt_of_succ_le hmhi) hpow_le
  constructor
  · exact hmpos
  · simpa [ieeeSingleFormat, minNormalMantissa] using hm_lt

theorem problem2_3_exists_subnormalBlock_of_ieeeSingle_subnormalMantissa
    {m : ℕ}
    (hm : ieeeSingleFormat.subnormalMantissa m) :
    ∃ s : ℕ, s ≤ 22 ∧ 2 ^ s ≤ m ∧ m + 1 ≤ 2 ^ (s + 1) := by
  let s := Nat.log 2 m
  have hm_ne : m ≠ 0 := Nat.ne_of_gt hm.1
  have hm_lt : m < 2 ^ 23 := by
    simpa [ieeeSingleFormat, minNormalMantissa] using hm.2
  have hslo : 2 ^ s ≤ m := by
    exact (Nat.le_log_iff_pow_le Nat.one_lt_two hm_ne).mp (le_refl s)
  have hm_lt_next : m < 2 ^ (s + 1) := by
    simpa [s] using Nat.lt_pow_succ_log_self Nat.one_lt_two m
  have hmhi : m + 1 ≤ 2 ^ (s + 1) :=
    Nat.succ_le_of_lt hm_lt_next
  have hs_lt : s < 23 := by
    simpa [s] using Nat.log_lt_of_lt_pow hm_ne hm_lt
  exact ⟨s, by omega, hslo, hmhi⟩

theorem problem2_3_ieeeDouble_minNormalMagnitude_lt_ieeeSingle_subnormal_false
    {m : ℕ}
    (hm : ieeeSingleFormat.subnormalMantissa m) :
    ieeeDoubleFormat.minNormalMagnitude <
      ieeeSingleFormat.subnormalValue false m := by
  have hmin_lt_one :
      ieeeDoubleFormat.minNormalMagnitude <
        ieeeSingleFormat.subnormalValue false 1 := by
    have hpow :
        (2 : ℝ) ^ (-1022 : ℤ) < (2 : ℝ) ^ (-149 : ℤ) :=
      zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2)
        (by norm_num : (-1022 : ℤ) < -149)
    simpa [ieeeDoubleFormat, ieeeSingleFormat, minNormalMagnitude,
      subnormalValue, signValue, betaR] using hpow
  have hone_le :
      ieeeSingleFormat.subnormalValue false 1 ≤
        ieeeSingleFormat.subnormalValue false m :=
    ieeeSingleFormat.subnormalValue_false_one_le_of_subnormalMantissa hm
  exact lt_of_lt_of_le hmin_lt_one hone_le

theorem problem2_3_ieeeSingle_subnormal_true_lt_neg_ieeeDouble_minNormalMagnitude
    {m : ℕ}
    (hm : ieeeSingleFormat.subnormalMantissa m) :
    ieeeSingleFormat.subnormalValue true m <
      -ieeeDoubleFormat.minNormalMagnitude := by
  have hpos :=
    problem2_3_ieeeDouble_minNormalMagnitude_lt_ieeeSingle_subnormal_false
      (m := m) hm
  rw [show ieeeSingleFormat.subnormalValue true m =
      -ieeeSingleFormat.subnormalValue false m by
        exact ieeeSingleFormat.subnormalValue_not_eq_neg false m]
  linarith

/-- The double mantissas strictly between the single-subnormal grid points
`m * 2^-149` and `(m+1) * 2^-149`, represented in the double binade selected
by `s`. -/
def problem2_3_subnormalBlockInteriorDoubleMantissas
    (s m : ℕ) : Finset ℕ :=
  Finset.Icc (m * problem2_3_subnormalBlockScale s + 1)
    ((m + 1) * problem2_3_subnormalBlockScale s - 1)

theorem problem2_3_subnormalBlockInteriorDoubleMantissas_card
    (s m : ℕ) :
    (problem2_3_subnormalBlockInteriorDoubleMantissas s m).card =
      problem2_3_subnormalBlockScale s - 1 := by
  rw [problem2_3_subnormalBlockInteriorDoubleMantissas, Nat.card_Icc]
  have hsucc :
      (m + 1) * problem2_3_subnormalBlockScale s =
        m * problem2_3_subnormalBlockScale s +
          problem2_3_subnormalBlockScale s := by
    ring
  rw [hsucc]
  have hscale_pos : 0 < problem2_3_subnormalBlockScale s := by
    simp [problem2_3_subnormalBlockScale]
  omega

theorem problem2_3_subnormalBlockInteriorDoubleMantissas_mem_iff
    {s m n : ℕ} :
    n ∈ problem2_3_subnormalBlockInteriorDoubleMantissas s m ↔
      m * problem2_3_subnormalBlockScale s < n ∧
        n < (m + 1) * problem2_3_subnormalBlockScale s := by
  rw [problem2_3_subnormalBlockInteriorDoubleMantissas, Finset.mem_Icc]
  constructor
  · intro h
    constructor
    · exact Nat.lt_of_succ_le h.1
    · omega
  · intro h
    constructor
    · exact Nat.succ_le_of_lt h.1
    · omega

theorem problem2_3_ieeeDouble_subnormalBlock_between_iff_mem
    {s m n : ℕ} (hs : s ≤ 52) :
    (ieeeSingleFormat.subnormalValue false m <
        ieeeDoubleFormat.normalizedValue false n ((s : ℤ) - 148) ∧
      ieeeDoubleFormat.normalizedValue false n ((s : ℤ) - 148) <
        ieeeSingleFormat.subnormalValue false (m + 1)) ↔
      n ∈ problem2_3_subnormalBlockInteriorDoubleMantissas s m := by
  constructor
  · intro h
    rw [problem2_3_subnormalBlockInteriorDoubleMantissas_mem_iff]
    constructor
    · have hscale_pos :
          0 < (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) :=
        zpow_pos (by norm_num : (0 : ℝ) < 2) _
      have hmul :
          ((m : ℝ) * (2 : ℝ) ^ (((52 - s : ℕ) : ℤ))) *
              (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) <
            (n : ℝ) *
              (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) := by
        calc
          ((m : ℝ) * (2 : ℝ) ^ (((52 - s : ℕ) : ℤ))) *
              (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) =
              ieeeSingleFormat.subnormalValue false m := by
            rw [show ieeeSingleFormat.subnormalValue false m =
                (m : ℝ) * (2 : ℝ) ^ ((-125 : ℤ) - (24 : ℤ)) by
              simp [ieeeSingleFormat, subnormalValue, signValue, betaR]]
            rw [problem2_3_subnormal_block_pow_split s hs]
            ring
          _ < ieeeDoubleFormat.normalizedValue false n ((s : ℤ) - 148) := h.1
          _ = (n : ℝ) *
              (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) := by
            simp [ieeeDoubleFormat, normalizedValue, signValue, betaR]
      have hcoeff :
          (m : ℝ) * (2 : ℝ) ^ (((52 - s : ℕ) : ℤ)) < (n : ℝ) :=
        lt_of_mul_lt_mul_right hmul (le_of_lt hscale_pos)
      have hcoeff_nat :
          ((m * problem2_3_subnormalBlockScale s : ℕ) : ℝ) <
            (n : ℝ) := by
        simpa [problem2_3_subnormalBlockScale, Nat.cast_mul, Nat.cast_pow,
          zpow_natCast] using hcoeff
      exact Nat.cast_lt.mp hcoeff_nat
    · have hscale_pos :
          0 < (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) :=
        zpow_pos (by norm_num : (0 : ℝ) < 2) _
      have hmul :
          (n : ℝ) *
              (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) <
            ((m + 1 : ℕ) : ℝ) *
                (2 : ℝ) ^ (((52 - s : ℕ) : ℤ)) *
              (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) := by
        calc
          (n : ℝ) *
              (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) =
              ieeeDoubleFormat.normalizedValue false n ((s : ℤ) - 148) := by
            simp [ieeeDoubleFormat, normalizedValue, signValue, betaR]
          _ < ieeeSingleFormat.subnormalValue false (m + 1) := h.2
          _ = ((m + 1 : ℕ) : ℝ) *
                (2 : ℝ) ^ (((52 - s : ℕ) : ℤ)) *
              (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) := by
            rw [show ieeeSingleFormat.subnormalValue false (m + 1) =
                ((m + 1 : ℕ) : ℝ) *
                  (2 : ℝ) ^ ((-125 : ℤ) - (24 : ℤ)) by
              simp [ieeeSingleFormat, subnormalValue, signValue, betaR]]
            rw [problem2_3_subnormal_block_pow_split s hs]
            ring
      have hcoeff :
          (n : ℝ) <
            ((m + 1 : ℕ) : ℝ) *
              (2 : ℝ) ^ (((52 - s : ℕ) : ℤ)) :=
        lt_of_mul_lt_mul_right hmul (le_of_lt hscale_pos)
      have hcoeff_nat :
          (n : ℝ) <
            (((m + 1) * problem2_3_subnormalBlockScale s : ℕ) : ℝ) := by
        simpa [problem2_3_subnormalBlockScale, Nat.cast_mul, Nat.cast_pow,
          zpow_natCast] using hcoeff
      exact Nat.cast_lt.mp hcoeff_nat
  · intro hn
    have hbounds :=
      (problem2_3_subnormalBlockInteriorDoubleMantissas_mem_iff).mp hn
    constructor
    · have hcoeff :
          (m : ℝ) * (2 : ℝ) ^ (((52 - s : ℕ) : ℤ)) < (n : ℝ) := by
        have hcast :
            ((m * problem2_3_subnormalBlockScale s : ℕ) : ℝ) <
              (n : ℝ) := by
          exact_mod_cast hbounds.1
        simpa [problem2_3_subnormalBlockScale, Nat.cast_mul, Nat.cast_pow,
          zpow_natCast] using hcast
      have hscale_pos :
          0 < (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) :=
        zpow_pos (by norm_num : (0 : ℝ) < 2) _
      have hmul := mul_lt_mul_of_pos_right hcoeff hscale_pos
      calc
        ieeeSingleFormat.subnormalValue false m =
            ((m : ℝ) * (2 : ℝ) ^ (((52 - s : ℕ) : ℤ))) *
              (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) := by
          rw [show ieeeSingleFormat.subnormalValue false m =
              (m : ℝ) * (2 : ℝ) ^ ((-125 : ℤ) - (24 : ℤ)) by
            simp [ieeeSingleFormat, subnormalValue, signValue, betaR]]
          rw [problem2_3_subnormal_block_pow_split s hs]
          ring
        _ < (n : ℝ) *
              (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) := hmul
        _ = ieeeDoubleFormat.normalizedValue false n ((s : ℤ) - 148) := by
          simp [ieeeDoubleFormat, normalizedValue, signValue, betaR]
    · have hcoeff :
          (n : ℝ) <
            ((m + 1 : ℕ) : ℝ) *
              (2 : ℝ) ^ (((52 - s : ℕ) : ℤ)) := by
        have hcast :
            (n : ℝ) <
              (((m + 1) * problem2_3_subnormalBlockScale s : ℕ) : ℝ) := by
          exact_mod_cast hbounds.2
        simpa [problem2_3_subnormalBlockScale, Nat.cast_mul, Nat.cast_pow,
          zpow_natCast] using hcast
      have hscale_pos :
          0 < (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) :=
        zpow_pos (by norm_num : (0 : ℝ) < 2) _
      have hmul := mul_lt_mul_of_pos_right hcoeff hscale_pos
      calc
        ieeeDoubleFormat.normalizedValue false n ((s : ℤ) - 148) =
            (n : ℝ) *
              (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) := by
          simp [ieeeDoubleFormat, normalizedValue, signValue, betaR]
        _ < ((m + 1 : ℕ) : ℝ) *
              (2 : ℝ) ^ (((52 - s : ℕ) : ℤ)) *
              (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) := hmul
        _ = ieeeSingleFormat.subnormalValue false (m + 1) := by
          rw [show ieeeSingleFormat.subnormalValue false (m + 1) =
              ((m + 1 : ℕ) : ℝ) *
                (2 : ℝ) ^ ((-125 : ℤ) - (24 : ℤ)) by
            simp [ieeeSingleFormat, subnormalValue, signValue, betaR]]
          rw [problem2_3_subnormal_block_pow_split s hs]
          ring

theorem problem2_3_ieeeDouble_subnormalBlock_negative_between_iff_mem
    {s m n : ℕ} (hs : s ≤ 52) :
    (ieeeSingleFormat.subnormalValue true (m + 1) <
        ieeeDoubleFormat.normalizedValue true n ((s : ℤ) - 148) ∧
      ieeeDoubleFormat.normalizedValue true n ((s : ℤ) - 148) <
        ieeeSingleFormat.subnormalValue true m) ↔
      n ∈ problem2_3_subnormalBlockInteriorDoubleMantissas s m := by
  constructor
  · intro h
    have hleft :
        ieeeSingleFormat.subnormalValue false m <
          ieeeDoubleFormat.normalizedValue false n ((s : ℤ) - 148) := by
      rw [ieeeDoubleFormat.normalizedValue_true_eq_neg_false,
        show ieeeSingleFormat.subnormalValue true m =
          -ieeeSingleFormat.subnormalValue false m by
            exact ieeeSingleFormat.subnormalValue_not_eq_neg false m] at h
      simpa using neg_lt_neg h.2
    have hright :
        ieeeDoubleFormat.normalizedValue false n ((s : ℤ) - 148) <
          ieeeSingleFormat.subnormalValue false (m + 1) := by
      rw [show ieeeSingleFormat.subnormalValue true (m + 1) =
          -ieeeSingleFormat.subnormalValue false (m + 1) by
            exact ieeeSingleFormat.subnormalValue_not_eq_neg false (m + 1),
        ieeeDoubleFormat.normalizedValue_true_eq_neg_false] at h
      simpa using neg_lt_neg h.1
    exact (problem2_3_ieeeDouble_subnormalBlock_between_iff_mem hs).mp
      ⟨hleft, hright⟩
  · intro hn
    have hpos := (problem2_3_ieeeDouble_subnormalBlock_between_iff_mem hs).mpr hn
    constructor
    · rw [show ieeeSingleFormat.subnormalValue true (m + 1) =
          -ieeeSingleFormat.subnormalValue false (m + 1) by
            exact ieeeSingleFormat.subnormalValue_not_eq_neg false (m + 1),
        ieeeDoubleFormat.normalizedValue_true_eq_neg_false]
      exact neg_lt_neg hpos.2
    · rw [ieeeDoubleFormat.normalizedValue_true_eq_neg_false,
        show ieeeSingleFormat.subnormalValue true m =
          -ieeeSingleFormat.subnormalValue false m by
            exact ieeeSingleFormat.subnormalValue_not_eq_neg false m]
      exact neg_lt_neg hpos.1

private theorem problem2_3_subnormalBlockScale_pos (s : ℕ) :
    0 < problem2_3_subnormalBlockScale s := by
  simp [problem2_3_subnormalBlockScale]

private theorem problem2_3_two_pow_mul_subnormalBlockScale
    {s : ℕ} (hs : s ≤ 52) :
    2 ^ s * problem2_3_subnormalBlockScale s = 2 ^ 52 := by
  rw [problem2_3_subnormalBlockScale, ← pow_add]
  congr 1
  omega

private theorem problem2_3_two_pow_succ_mul_subnormalBlockScale
    {s : ℕ} (hs : s ≤ 52) :
    2 ^ (s + 1) * problem2_3_subnormalBlockScale s = 2 ^ 53 := by
  rw [problem2_3_subnormalBlockScale, ← pow_add]
  congr 1
  omega

theorem problem2_3_subnormalBlockInteriorDoubleMantissa_normalized
    {s m r : ℕ}
    (hs : s ≤ 22)
    (hmlo : 2 ^ s ≤ m)
    (hmhi : m + 1 ≤ 2 ^ (s + 1))
    (hrhi : r < problem2_3_subnormalBlockScale s) :
    ieeeDoubleFormat.normalizedMantissa
      (m * problem2_3_subnormalBlockScale s + r) := by
  have hs52 : s ≤ 52 := by omega
  have hscale_pos : 0 < problem2_3_subnormalBlockScale s :=
    problem2_3_subnormalBlockScale_pos s
  have hlo_mul :
      2 ^ s * problem2_3_subnormalBlockScale s ≤
        m * problem2_3_subnormalBlockScale s :=
    Nat.mul_le_mul_right _ hmlo
  have hlo :
      2 ^ 52 ≤ m * problem2_3_subnormalBlockScale s := by
    simpa [problem2_3_two_pow_mul_subnormalBlockScale hs52] using hlo_mul
  have hlt_next :
      m * problem2_3_subnormalBlockScale s + r <
        (m + 1) * problem2_3_subnormalBlockScale s := by
    nlinarith [hscale_pos, hrhi]
  have hhi_mul :
      (m + 1) * problem2_3_subnormalBlockScale s ≤
        2 ^ (s + 1) * problem2_3_subnormalBlockScale s :=
    Nat.mul_le_mul_right _ hmhi
  have hhi :
      m * problem2_3_subnormalBlockScale s + r < 2 ^ 53 := by
    exact lt_of_lt_of_le hlt_next
      (by
        simpa [problem2_3_two_pow_succ_mul_subnormalBlockScale hs52] using
          hhi_mul)
  norm_num [ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
    minNormalMantissa] at hlo hhi ⊢
  omega

theorem problem2_3_subnormalBlockInteriorDoubleMantissa_normalized_of_mem
    {s m n : ℕ}
    (hs : s ≤ 22)
    (hmlo : 2 ^ s ≤ m)
    (hmhi : m + 1 ≤ 2 ^ (s + 1))
    (hn : n ∈ problem2_3_subnormalBlockInteriorDoubleMantissas s m) :
    ieeeDoubleFormat.normalizedMantissa n := by
  have hs52 : s ≤ 52 := by omega
  have hbounds :=
    (problem2_3_subnormalBlockInteriorDoubleMantissas_mem_iff).mp hn
  have hscale_pos : 0 < problem2_3_subnormalBlockScale s :=
    problem2_3_subnormalBlockScale_pos s
  have hlo_mul :
      2 ^ s * problem2_3_subnormalBlockScale s ≤
        m * problem2_3_subnormalBlockScale s :=
    Nat.mul_le_mul_right _ hmlo
  have hlo_base :
      2 ^ 52 ≤ m * problem2_3_subnormalBlockScale s := by
    simpa [problem2_3_two_pow_mul_subnormalBlockScale hs52] using hlo_mul
  have hlo : 2 ^ 52 ≤ n :=
    le_trans hlo_base (Nat.le_of_lt hbounds.1)
  have hhi_mul :
      (m + 1) * problem2_3_subnormalBlockScale s ≤
        2 ^ (s + 1) * problem2_3_subnormalBlockScale s :=
    Nat.mul_le_mul_right _ hmhi
  have hhi : n < 2 ^ 53 :=
    lt_of_lt_of_le hbounds.2
      (by
        simpa [problem2_3_two_pow_succ_mul_subnormalBlockScale hs52] using
          hhi_mul)
  norm_num [ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
    minNormalMantissa] at hscale_pos hlo hhi ⊢
  omega

private theorem problem2_3_ieeeSingle_subnormalValue_false_succ_le_block_upper
    {s m : ℕ}
    (hmhi : m + 1 ≤ 2 ^ (s + 1)) :
    ieeeSingleFormat.subnormalValue false (m + 1) ≤
      (2 : ℝ) ^ ((s : ℤ) - 148) := by
  have hcoeff :
      ((m + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (s + 1) := by
    exact_mod_cast hmhi
  have hscale_nonneg : 0 ≤ (2 : ℝ) ^ (-149 : ℤ) :=
    le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) _)
  have hmul :=
    mul_le_mul_of_nonneg_right hcoeff hscale_nonneg
  calc
    ieeeSingleFormat.subnormalValue false (m + 1) =
        ((m + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-149 : ℤ) := by
      simp [ieeeSingleFormat, subnormalValue, signValue, betaR]
    _ ≤ (2 : ℝ) ^ (s + 1) * (2 : ℝ) ^ (-149 : ℤ) := hmul
    _ = (2 : ℝ) ^ (((s + 1 : ℕ) : ℤ)) *
        (2 : ℝ) ^ (-149 : ℤ) := by
      rw [zpow_natCast]
    _ = (2 : ℝ) ^ ((((s + 1 : ℕ) : ℤ)) + (-149 : ℤ)) := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    _ = (2 : ℝ) ^ ((s : ℤ) - 148) := by
      congr 1
      omega

theorem problem2_3_ieeeDouble_normalized_subnormalBlock_positive_between_mem
    {s m n : ℕ} {eD : ℤ} {negativeD : Bool}
    (hs : s ≤ 22)
    (hmlo : 2 ^ s ≤ m)
    (hmhi : m + 1 ≤ 2 ^ (s + 1))
    (hnD : ieeeDoubleFormat.normalizedMantissa n)
    (hbetween :
      ieeeSingleFormat.subnormalValue false m <
          ieeeDoubleFormat.normalizedValue negativeD n eD ∧
        ieeeDoubleFormat.normalizedValue negativeD n eD <
          ieeeSingleFormat.subnormalValue false (m + 1)) :
    negativeD = false ∧ eD = (s : ℤ) - 148 ∧
      n ∈ problem2_3_subnormalBlockInteriorDoubleMantissas s m := by
  have hs52 : s ≤ 52 := by omega
  cases negativeD
  · have hleftD :
        ieeeDoubleFormat.normalizedMantissa
          (m * problem2_3_subnormalBlockScale s) := by
      simpa using
        (problem2_3_subnormalBlockInteriorDoubleMantissa_normalized
          (s := s) (m := m) (r := 0) hs hmlo hmhi
          (problem2_3_subnormalBlockScale_pos s))
    have heD_eq : eD = (s : ℤ) - 148 := by
      rcases lt_trichotomy eD ((s : ℤ) - 148) with hlt | heq | hgt
      · have hz_lt_leftD :
            ieeeDoubleFormat.normalizedValue false n eD <
              ieeeDoubleFormat.normalizedValue false
                (m * problem2_3_subnormalBlockScale s) ((s : ℤ) - 148) :=
          ieeeDoubleFormat.normalizedValue_false_lt_of_exp_lt hnD hleftD hlt
        have hz_lt_left :
            ieeeDoubleFormat.normalizedValue false n eD <
              ieeeSingleFormat.subnormalValue false m := by
          simpa [problem2_3_ieeeSingle_subnormalValue_eq_ieeeDouble_scaledMantissa
            false s m hs52] using hz_lt_leftD
        exact False.elim ((not_lt_of_ge (le_of_lt hz_lt_left)) hbetween.1)
      · exact heq
      · have hz_ge_lower :
            (2 : ℝ) ^ (eD - 1) ≤
              ieeeDoubleFormat.normalizedValue false n eD := by
          simpa [ieeeDoubleFormat, betaR] using
            (ieeeDoubleFormat.normalizedValue_false_lower_power
              (m := n) (e := eD) hnD)
        have hblock_le_lower :
            (2 : ℝ) ^ ((s : ℤ) - 148) ≤ (2 : ℝ) ^ (eD - 1) :=
          zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
            (by omega : (s : ℤ) - 148 ≤ eD - 1)
        have hright_le_block :
            ieeeSingleFormat.subnormalValue false (m + 1) ≤
              (2 : ℝ) ^ ((s : ℤ) - 148) :=
          problem2_3_ieeeSingle_subnormalValue_false_succ_le_block_upper
            (s := s) (m := m) hmhi
        have hright_le_z :
            ieeeSingleFormat.subnormalValue false (m + 1) ≤
              ieeeDoubleFormat.normalizedValue false n eD :=
          le_trans hright_le_block (le_trans hblock_le_lower hz_ge_lower)
        exact False.elim ((not_lt_of_ge hright_le_z) hbetween.2)
    subst eD
    exact ⟨rfl, rfl,
      (problem2_3_ieeeDouble_subnormalBlock_between_iff_mem
        (s := s) (m := m) (n := n) hs52).mp hbetween⟩
  · have hmSingle : ieeeSingleFormat.subnormalMantissa m :=
      problem2_3_ieeeSingle_subnormalMantissa_of_block hs hmlo hmhi
    have hleft_pos :
        0 < ieeeSingleFormat.subnormalValue false m :=
      ieeeSingleFormat.subnormalValue_false_pos hmSingle
    have hz_neg :
        ieeeDoubleFormat.normalizedValue true n eD < 0 :=
      ieeeDoubleFormat.normalizedValue_true_neg hnD
    linarith

/-- Positive subnormal-grid branch of Problem 2.3.  If the left single
subnormal mantissa `m` lies in the dyadic block `2^s <= m < 2^(s+1)`, then a
single subnormal grid step contains `2^(52-s)-1` listed interior double
mantissas.  The right grid point may be the next subnormal or, at the final
block endpoint, the smallest normal value; this theorem states the real
strict-between fact for the common `m * 2^-149` grid expression. -/
theorem problem2_3_ieeeDouble_between_ieeeSingle_positive_subnormal_block
    {s m r : ℕ}
    (hs : s ≤ 22)
    (hmlo : 2 ^ s ≤ m)
    (hmhi : m + 1 ≤ 2 ^ (s + 1))
    (hrlo : 0 < r)
    (hrhi : r < problem2_3_subnormalBlockScale s) :
    ieeeDoubleFormat.finiteSystem
        (ieeeDoubleFormat.normalizedValue false
          (m * problem2_3_subnormalBlockScale s + r) ((s : ℤ) - 148)) ∧
      ieeeSingleFormat.subnormalValue false m <
        ieeeDoubleFormat.normalizedValue false
          (m * problem2_3_subnormalBlockScale s + r) ((s : ℤ) - 148) ∧
      ieeeDoubleFormat.normalizedValue false
          (m * problem2_3_subnormalBlockScale s + r) ((s : ℤ) - 148) <
        ieeeSingleFormat.subnormalValue false (m + 1) := by
  have hs52 : s ≤ 52 := by omega
  have heD : ieeeDoubleFormat.exponentInRange ((s : ℤ) - 148) := by
    norm_num [ieeeDoubleFormat, exponentInRange]
    omega
  have hmD :
      ieeeDoubleFormat.normalizedMantissa
        (m * problem2_3_subnormalBlockScale s + r) :=
    problem2_3_subnormalBlockInteriorDoubleMantissa_normalized
      hs hmlo hmhi hrhi
  constructor
  · exact Or.inr (Or.inl
      ⟨false, m * problem2_3_subnormalBlockScale s + r,
        (s : ℤ) - 148, hmD, heD, rfl⟩)
  · constructor
    · have hn :
          m * problem2_3_subnormalBlockScale s <
            m * problem2_3_subnormalBlockScale s + r :=
        Nat.lt_add_of_pos_right hrlo
      have hcoeff :
          (m : ℝ) * (2 : ℝ) ^ (((52 - s : ℕ) : ℤ)) <
            ((m * problem2_3_subnormalBlockScale s + r : ℕ) : ℝ) := by
        have hcast :
            ((m * problem2_3_subnormalBlockScale s : ℕ) : ℝ) <
              ((m * problem2_3_subnormalBlockScale s + r : ℕ) : ℝ) := by
          exact_mod_cast hn
        simpa [problem2_3_subnormalBlockScale, Nat.cast_mul, Nat.cast_pow]
          using hcast
      have hscale_pos :
          0 < (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) :=
        zpow_pos (by norm_num : (0 : ℝ) < 2) _
      have hmul := mul_lt_mul_of_pos_right hcoeff hscale_pos
      calc
        ieeeSingleFormat.subnormalValue false m =
            ((m : ℝ) * (2 : ℝ) ^ (((52 - s : ℕ) : ℤ))) *
              (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) := by
          rw [show ieeeSingleFormat.subnormalValue false m =
              (m : ℝ) * (2 : ℝ) ^ ((-125 : ℤ) - (24 : ℤ)) by
            simp [ieeeSingleFormat, subnormalValue, signValue, betaR]]
          rw [problem2_3_subnormal_block_pow_split s hs52]
          ring
        _ < ((m * problem2_3_subnormalBlockScale s + r : ℕ) : ℝ) *
              (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) := hmul
        _ = ieeeDoubleFormat.normalizedValue false
            (m * problem2_3_subnormalBlockScale s + r) ((s : ℤ) - 148) := by
          simp [ieeeDoubleFormat, normalizedValue, signValue, betaR]
    · have hn :
          m * problem2_3_subnormalBlockScale s + r <
            (m + 1) * problem2_3_subnormalBlockScale s := by
        have hscale_pos : 0 < problem2_3_subnormalBlockScale s :=
          problem2_3_subnormalBlockScale_pos s
        nlinarith [hscale_pos, hrhi]
      have hcoeff :
          ((m * problem2_3_subnormalBlockScale s + r : ℕ) : ℝ) <
            ((m + 1 : ℕ) : ℝ) *
              (2 : ℝ) ^ (((52 - s : ℕ) : ℤ)) := by
        have hcast :
            ((m * problem2_3_subnormalBlockScale s + r : ℕ) : ℝ) <
              (((m + 1) * problem2_3_subnormalBlockScale s : ℕ) : ℝ) := by
          exact_mod_cast hn
        simpa [problem2_3_subnormalBlockScale, Nat.cast_mul, Nat.cast_pow]
          using hcast
      have hscale_pos :
          0 < (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) :=
        zpow_pos (by norm_num : (0 : ℝ) < 2) _
      have hmul := mul_lt_mul_of_pos_right hcoeff hscale_pos
      calc
        ieeeDoubleFormat.normalizedValue false
            (m * problem2_3_subnormalBlockScale s + r) ((s : ℤ) - 148) =
            ((m * problem2_3_subnormalBlockScale s + r : ℕ) : ℝ) *
              (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) := by
          simp [ieeeDoubleFormat, normalizedValue, signValue, betaR]
        _ < ((m + 1 : ℕ) : ℝ) *
              (2 : ℝ) ^ (((52 - s : ℕ) : ℤ)) *
              (2 : ℝ) ^ (((s : ℤ) - (148 : ℤ)) - (53 : ℤ)) := hmul
        _ = ieeeSingleFormat.subnormalValue false (m + 1) := by
          rw [show ieeeSingleFormat.subnormalValue false (m + 1) =
              ((m + 1 : ℕ) : ℝ) *
                (2 : ℝ) ^ ((-125 : ℤ) - (24 : ℤ)) by
            simp [ieeeSingleFormat, subnormalValue, signValue, betaR]]
          rw [problem2_3_subnormal_block_pow_split s hs52]
          ring

/-- Signed wrapper for the positive subnormal-grid branch. -/
theorem problem2_3_ieeeDouble_between_ieeeSingle_subnormal_block_signed
    {negative : Bool} {s m r : ℕ}
    (hs : s ≤ 22)
    (hmlo : 2 ^ s ≤ m)
    (hmhi : m + 1 ≤ 2 ^ (s + 1))
    (hrlo : 0 < r)
    (hrhi : r < problem2_3_subnormalBlockScale s) :
    ieeeDoubleFormat.finiteSystem
        (ieeeDoubleFormat.normalizedValue negative
          (m * problem2_3_subnormalBlockScale s + r) ((s : ℤ) - 148)) ∧
      ((ieeeSingleFormat.subnormalValue negative m <
          ieeeDoubleFormat.normalizedValue negative
            (m * problem2_3_subnormalBlockScale s + r) ((s : ℤ) - 148) ∧
        ieeeDoubleFormat.normalizedValue negative
            (m * problem2_3_subnormalBlockScale s + r) ((s : ℤ) - 148) <
          ieeeSingleFormat.subnormalValue negative (m + 1)) ∨
      (ieeeSingleFormat.subnormalValue negative (m + 1) <
          ieeeDoubleFormat.normalizedValue negative
            (m * problem2_3_subnormalBlockScale s + r) ((s : ℤ) - 148) ∧
        ieeeDoubleFormat.normalizedValue negative
            (m * problem2_3_subnormalBlockScale s + r) ((s : ℤ) - 148) <
          ieeeSingleFormat.subnormalValue negative m)) := by
  have hpos :=
    problem2_3_ieeeDouble_between_ieeeSingle_positive_subnormal_block
      (s := s) (m := m) (r := r) hs hmlo hmhi hrlo hrhi
  cases negative
  · exact ⟨hpos.1, Or.inl hpos.2⟩
  · have heD : ieeeDoubleFormat.exponentInRange ((s : ℤ) - 148) := by
      norm_num [ieeeDoubleFormat, exponentInRange]
      omega
    have hmD :
        ieeeDoubleFormat.normalizedMantissa
          (m * problem2_3_subnormalBlockScale s + r) :=
      problem2_3_subnormalBlockInteriorDoubleMantissa_normalized
        hs hmlo hmhi hrhi
    constructor
    · exact Or.inr (Or.inl
        ⟨true, m * problem2_3_subnormalBlockScale s + r,
          (s : ℤ) - 148, hmD, heD, rfl⟩)
    · right
      constructor
      · rw [show ieeeSingleFormat.subnormalValue true (m + 1) =
            -ieeeSingleFormat.subnormalValue false (m + 1) by
              exact ieeeSingleFormat.subnormalValue_not_eq_neg false (m + 1),
          ieeeDoubleFormat.normalizedValue_true_eq_neg_false]
        exact neg_lt_neg hpos.2.2
      · rw [ieeeDoubleFormat.normalizedValue_true_eq_neg_false,
          show ieeeSingleFormat.subnormalValue true m =
            -ieeeSingleFormat.subnormalValue false m by
              exact ieeeSingleFormat.subnormalValue_not_eq_neg false m]
        exact neg_lt_neg hpos.2.1

/-- Problem 2.3 first positive subnormal branch.  Between the first two
positive IEEE-single subnormal values, the interior IEEE-double values already
have cardinality `2^52 - 1`, not the normalized `2^29 - 1` count. -/
theorem problem2_3_ieeeDouble_between_first_two_ieeeSingle_subnormals
    {r : ℕ}
    (hrlo : 0 < r)
    (hrhi : r < 2 ^ 52) :
    ieeeDoubleFormat.finiteSystem
        (ieeeDoubleFormat.normalizedValue false (2 ^ 52 + r) (-148 : ℤ)) ∧
      ieeeSingleFormat.subnormalValue false 1 <
        ieeeDoubleFormat.normalizedValue false (2 ^ 52 + r) (-148 : ℤ) ∧
      ieeeDoubleFormat.normalizedValue false (2 ^ 52 + r) (-148 : ℤ) <
        ieeeSingleFormat.subnormalValue false 2 := by
  have heD : ieeeDoubleFormat.exponentInRange (-148 : ℤ) := by
    norm_num [ieeeDoubleFormat, exponentInRange]
  have hmD : ieeeDoubleFormat.normalizedMantissa (2 ^ 52 + r) :=
    problem2_3_smallestSubnormalInteriorDoubleMantissa_normalized hrhi
  constructor
  · exact Or.inr (Or.inl ⟨false, 2 ^ 52 + r, (-148 : ℤ), hmD, heD, rfl⟩)
  · constructor
    · have hn : 2 ^ 52 < 2 ^ 52 + r :=
        Nat.lt_add_of_pos_right hrlo
      have hcoeff :
          ((2 ^ 52 : ℕ) : ℝ) < ((2 ^ 52 + r : ℕ) : ℝ) := by
        exact_mod_cast hn
      have hscale_pos : 0 < (2 : ℝ) ^ ((-148 : ℤ) - (53 : ℤ)) :=
        zpow_pos (by norm_num : (0 : ℝ) < 2) _
      have hmul := mul_lt_mul_of_pos_right hcoeff hscale_pos
      simp [ieeeSingleFormat, ieeeDoubleFormat, subnormalValue, normalizedValue,
        signValue, betaR]
      norm_num at hmul ⊢
      simpa [mul_assoc] using hmul
    · have hn : 2 ^ 52 + r < 2 ^ 53 := by
        norm_num at hrhi ⊢
        omega
      have hcoeff :
          ((2 ^ 52 + r : ℕ) : ℝ) < (2 : ℝ) ^ (53 : ℤ) := by
        norm_num at hn ⊢
        exact_mod_cast hn
      have hscale_pos : 0 < (2 : ℝ) ^ ((-148 : ℤ) - (53 : ℤ)) :=
        zpow_pos (by norm_num : (0 : ℝ) < 2) _
      have hmul := mul_lt_mul_of_pos_right hcoeff hscale_pos
      simp [ieeeSingleFormat, ieeeDoubleFormat, subnormalValue, normalizedValue,
        signValue, betaR]
      norm_num at hmul ⊢
      simpa [mul_assoc] using hmul

/-- Branch-family data for Problem 2.3 adjacent nonzero IEEE-single gaps.

The constructors correspond to the same-exponent normalized, exponent-boundary
normalized, and dyadic-block subnormal branches formalized above.  This is a
single formulation for the proved branch family; it deliberately does not yet
claim that every finite IEEE-double value between arbitrary adjacent nonzero
single endpoints has been globally classified. -/
inductive Problem2_3IeeeSingleAdjacentGap where
  | sameExponent (negative : Bool) (m : ℕ) (e : ℤ)
      (hm : ieeeSingleFormat.normalizedMantissa m)
      (hmnext : ieeeSingleFormat.normalizedMantissa (m + 1))
      (he : ieeeSingleFormat.exponentInRange e)
  | boundary (negative : Bool) (e : ℤ)
      (he : ieeeSingleFormat.exponentInRange e)
      (heNext : ieeeSingleFormat.exponentInRange (e + 1))
  | subnormalBlock (negative : Bool) (s m : ℕ)
      (hs : s ≤ 22)
      (hmlo : 2 ^ s ≤ m)
      (hmhi : m + 1 ≤ 2 ^ (s + 1))

/-- The listed interior double mantissas for a Problem 2.3 branch gap. -/
def problem2_3_adjacentSingleGapInteriorDoubleMantissas :
    Problem2_3IeeeSingleAdjacentGap → Finset ℕ
  | .sameExponent _ m _ _ _ _ =>
      problem2_3_sameExponentInteriorDoubleMantissas m
  | .boundary _ _ _ _ =>
      problem2_3_boundaryInteriorDoubleMantissas
  | .subnormalBlock _ s m _ _ _ =>
      problem2_3_subnormalBlockInteriorDoubleMantissas s m

/-- The branch-dependent interior count for a Problem 2.3 adjacent single gap. -/
def problem2_3_adjacentSingleGapInteriorCount :
    Problem2_3IeeeSingleAdjacentGap → ℕ
  | .sameExponent _ _ _ _ _ _ => 2 ^ 29 - 1
  | .boundary _ _ _ _ => 2 ^ 29 - 1
  | .subnormalBlock _ s _ _ _ _ => problem2_3_subnormalBlockScale s - 1

/-- The left endpoint of the ordered signed single gap. -/
def problem2_3_adjacentSingleGapLeftValue :
    Problem2_3IeeeSingleAdjacentGap → ℝ
  | .sameExponent false m e _ _ _ =>
      ieeeSingleFormat.normalizedValue false m e
  | .sameExponent true m e _ _ _ =>
      ieeeSingleFormat.normalizedValue true (m + 1) e
  | .boundary false e _ _ =>
      ieeeSingleFormat.normalizedValue false ieeeSingleFormat.maxNormalMantissa e
  | .boundary true e _ _ =>
      ieeeSingleFormat.normalizedValue true
        ieeeSingleFormat.minNormalMantissa (e + 1)
  | .subnormalBlock false _ m _ _ _ =>
      ieeeSingleFormat.subnormalValue false m
  | .subnormalBlock true _ m _ _ _ =>
      ieeeSingleFormat.subnormalValue true (m + 1)

/-- The right endpoint of the ordered signed single gap. -/
def problem2_3_adjacentSingleGapRightValue :
    Problem2_3IeeeSingleAdjacentGap → ℝ
  | .sameExponent false m e _ _ _ =>
      ieeeSingleFormat.normalizedValue false (m + 1) e
  | .sameExponent true m e _ _ _ =>
      ieeeSingleFormat.normalizedValue true m e
  | .boundary false e _ _ =>
      ieeeSingleFormat.normalizedValue false
        ieeeSingleFormat.minNormalMantissa (e + 1)
  | .boundary true e _ _ =>
      ieeeSingleFormat.normalizedValue true ieeeSingleFormat.maxNormalMantissa e
  | .subnormalBlock false _ m _ _ _ =>
      ieeeSingleFormat.subnormalValue false (m + 1)
  | .subnormalBlock true _ m _ _ _ =>
      ieeeSingleFormat.subnormalValue true m

theorem problem2_3_exists_adjacentSingleGap_of_ieeeSingle_subnormalMantissa
    (negative : Bool) {m : ℕ}
    (hm : ieeeSingleFormat.subnormalMantissa m) :
    ∃ g : Problem2_3IeeeSingleAdjacentGap,
      problem2_3_adjacentSingleGapLeftValue g =
        (if negative then ieeeSingleFormat.subnormalValue true (m + 1)
          else ieeeSingleFormat.subnormalValue false m) ∧
      problem2_3_adjacentSingleGapRightValue g =
        (if negative then ieeeSingleFormat.subnormalValue true m
          else ieeeSingleFormat.subnormalValue false (m + 1)) := by
  rcases problem2_3_exists_subnormalBlock_of_ieeeSingle_subnormalMantissa hm
    with ⟨s, hs, hmlo, hmhi⟩
  refine ⟨.subnormalBlock negative s m hs hmlo hmhi, ?_, ?_⟩
  · cases negative <;> rfl
  · cases negative <;> rfl

private theorem problem2_3_ieeeSingle_exponentInRange_of_normalizedSystem_eq
    {x : ℝ} {negative : Bool} {m : ℕ} {e : ℤ}
    (hx : ieeeSingleFormat.normalizedSystem x)
    (hm : ieeeSingleFormat.normalizedMantissa m)
    (hx_eq : x = ieeeSingleFormat.normalizedValue negative m e) :
    ieeeSingleFormat.exponentInRange e := by
  rcases hx with ⟨negative', m', e', hm', he', hx'⟩
  have hval :
      ieeeSingleFormat.normalizedValue negative' m' e' =
        ieeeSingleFormat.normalizedValue negative m e := by
    rw [← hx', hx_eq]
  rcases
      ieeeSingleFormat.normalizedValue_eq_sign_exp_mantissa hm' hm hval
    with ⟨_hneg, heq, _hm⟩
  simpa [heq] using he'

private theorem problem2_3_ieeeSingle_boundary_false_lt (e : ℤ) :
    ieeeSingleFormat.normalizedValue false
        ieeeSingleFormat.maxNormalMantissa e <
      ieeeSingleFormat.normalizedValue false
        ieeeSingleFormat.minNormalMantissa (e + 1) := by
  have hpow_pos : 0 < ieeeSingleFormat.betaR ^ e :=
    ieeeSingleFormat.betaR_zpow_pos e
  have htail_pos : 0 < ieeeSingleFormat.betaR ^ (-(ieeeSingleFormat.t : ℤ)) :=
    ieeeSingleFormat.betaR_zpow_pos (-(ieeeSingleFormat.t : ℤ))
  have hcoeff : 1 - ieeeSingleFormat.betaR ^ (-(ieeeSingleFormat.t : ℤ)) < 1 := by
    linarith
  have hmul := mul_lt_mul_of_pos_left hcoeff hpow_pos
  rw [ieeeSingleFormat.normalizedValue_false_maxNormalMantissa_eq,
    ieeeSingleFormat.normalizedValue_false_minNormalMantissa_succ_eq_beta_pow]
  simpa [mul_comm] using hmul

private theorem problem2_3_ieeeSingle_boundary_true_lt (e : ℤ) :
    ieeeSingleFormat.normalizedValue true
        ieeeSingleFormat.minNormalMantissa (e + 1) <
      ieeeSingleFormat.normalizedValue true
        ieeeSingleFormat.maxNormalMantissa e := by
  rw [ieeeSingleFormat.normalizedValue_true_eq_neg_false,
    ieeeSingleFormat.normalizedValue_true_eq_neg_false]
  exact neg_lt_neg (problem2_3_ieeeSingle_boundary_false_lt e)

theorem problem2_3_exists_adjacentSingleGap_of_ieeeSingle_realOrderAdjacentNormalized_ordered
    {x y : ℝ}
    (hx : ieeeSingleFormat.normalizedSystem x)
    (hy : ieeeSingleFormat.normalizedSystem y)
    (hadj : ieeeSingleFormat.realOrderAdjacentNormalized x y)
    (hxy : x < y) :
    ∃ g : Problem2_3IeeeSingleAdjacentGap,
      problem2_3_adjacentSingleGapLeftValue g = x ∧
        problem2_3_adjacentSingleGapRightValue g = y := by
  have hstruct :=
    ieeeSingleFormat.adjacentNormalized_of_realOrderAdjacentNormalized hadj
  rcases hstruct with hsame | hboundary
  · rcases hsame with ⟨negative, m, e, hm, hmnext, hcases⟩
    cases negative
    · rcases hcases with hordered | hreversed
      · rcases hordered with ⟨hxv, hyv⟩
        have he :
            ieeeSingleFormat.exponentInRange e :=
          problem2_3_ieeeSingle_exponentInRange_of_normalizedSystem_eq
            hx hm hxv
        refine ⟨.sameExponent false m e hm hmnext he, ?_, ?_⟩
        · simpa [problem2_3_adjacentSingleGapLeftValue] using hxv.symm
        · simpa [problem2_3_adjacentSingleGapRightValue] using hyv.symm
      · rcases hreversed with ⟨hxv, hyv⟩
        have hlt :
            ieeeSingleFormat.normalizedValue false (m + 1) e <
              ieeeSingleFormat.normalizedValue false m e := by
          simpa [hxv, hyv] using hxy
        have hnat :
            m + 1 < m :=
          (ieeeSingleFormat.normalizedValue_sameExponent_lt_iff_false
            (m + 1) m e).mp hlt
        omega
    · rcases hcases with hreversed | hordered
      · rcases hreversed with ⟨hxv, hyv⟩
        have hlt :
            ieeeSingleFormat.normalizedValue true m e <
              ieeeSingleFormat.normalizedValue true (m + 1) e := by
          simpa [hxv, hyv] using hxy
        have hnat :
            m + 1 < m :=
          (ieeeSingleFormat.normalizedValue_sameExponent_lt_iff_true
            m (m + 1) e).mp hlt
        omega
      · rcases hordered with ⟨hxv, hyv⟩
        have he :
            ieeeSingleFormat.exponentInRange e :=
          problem2_3_ieeeSingle_exponentInRange_of_normalizedSystem_eq
            hy hm hyv
        refine ⟨.sameExponent true m e hm hmnext he, ?_, ?_⟩
        · simpa [problem2_3_adjacentSingleGapLeftValue] using hxv.symm
        · simpa [problem2_3_adjacentSingleGapRightValue] using hyv.symm
  · rcases hboundary with ⟨negative, e, hcases⟩
    cases negative
    · rcases hcases with hordered | hreversed
      · rcases hordered with ⟨hxv, hyv⟩
        have he :
            ieeeSingleFormat.exponentInRange e :=
          problem2_3_ieeeSingle_exponentInRange_of_normalizedSystem_eq
            hx ieeeSingleFormat.maxNormalMantissa_normalized hxv
        have heNext :
            ieeeSingleFormat.exponentInRange (e + 1) :=
          problem2_3_ieeeSingle_exponentInRange_of_normalizedSystem_eq
            hy ieeeSingleFormat.minNormalMantissa_normalized hyv
        refine ⟨.boundary false e he heNext, ?_, ?_⟩
        · simpa [problem2_3_adjacentSingleGapLeftValue] using hxv.symm
        · simpa [problem2_3_adjacentSingleGapRightValue] using hyv.symm
      · rcases hreversed with ⟨hxv, hyv⟩
        have hlt :
            ieeeSingleFormat.normalizedValue false
                ieeeSingleFormat.minNormalMantissa (e + 1) <
              ieeeSingleFormat.normalizedValue false
                ieeeSingleFormat.maxNormalMantissa e := by
          simpa [hxv, hyv] using hxy
        have hright :=
          problem2_3_ieeeSingle_boundary_false_lt e
        linarith
    · rcases hcases with hreversed | hordered
      · rcases hreversed with ⟨hxv, hyv⟩
        have hlt :
            ieeeSingleFormat.normalizedValue true
                ieeeSingleFormat.maxNormalMantissa e <
              ieeeSingleFormat.normalizedValue true
                ieeeSingleFormat.minNormalMantissa (e + 1) := by
          simpa [hxv, hyv] using hxy
        have hright :=
          problem2_3_ieeeSingle_boundary_true_lt e
        linarith
      · rcases hordered with ⟨hxv, hyv⟩
        have he :
            ieeeSingleFormat.exponentInRange e :=
          problem2_3_ieeeSingle_exponentInRange_of_normalizedSystem_eq
            hy ieeeSingleFormat.maxNormalMantissa_normalized hyv
        have heNext :
            ieeeSingleFormat.exponentInRange (e + 1) :=
          problem2_3_ieeeSingle_exponentInRange_of_normalizedSystem_eq
            hx ieeeSingleFormat.minNormalMantissa_normalized hxv
        refine ⟨.boundary true e he heNext, ?_, ?_⟩
        · simpa [problem2_3_adjacentSingleGapLeftValue] using hxv.symm
        · simpa [problem2_3_adjacentSingleGapRightValue] using hyv.symm

theorem problem2_3_exists_adjacentSingleGap_of_ieeeSingle_realOrderAdjacentNormalized
    {x y : ℝ}
    (hx : ieeeSingleFormat.normalizedSystem x)
    (hy : ieeeSingleFormat.normalizedSystem y)
    (hadj : ieeeSingleFormat.realOrderAdjacentNormalized x y) :
    ∃ g : Problem2_3IeeeSingleAdjacentGap,
      (problem2_3_adjacentSingleGapLeftValue g = x ∧
        problem2_3_adjacentSingleGapRightValue g = y) ∨
      (problem2_3_adjacentSingleGapLeftValue g = y ∧
        problem2_3_adjacentSingleGapRightValue g = x) := by
  rcases lt_or_gt_of_ne hadj.2.2.1 with hxy | hyx
  · rcases
      problem2_3_exists_adjacentSingleGap_of_ieeeSingle_realOrderAdjacentNormalized_ordered
        hx hy hadj hxy with ⟨g, hg⟩
    exact ⟨g, Or.inl hg⟩
  · rcases
      problem2_3_exists_adjacentSingleGap_of_ieeeSingle_realOrderAdjacentNormalized_ordered
        hy hx (ieeeSingleFormat.realOrderAdjacentNormalized_symm hadj) hyx
      with ⟨g, hg⟩
    exact ⟨g, Or.inr hg⟩

/-- The double value associated with a candidate mantissa in a Problem 2.3 gap. -/
def problem2_3_adjacentSingleGapDoubleValue
    (g : Problem2_3IeeeSingleAdjacentGap) (n : ℕ) : ℝ :=
  match g with
  | .sameExponent negative _ e _ _ _ =>
      ieeeDoubleFormat.normalizedValue negative n e
  | .boundary negative e _ _ =>
      ieeeDoubleFormat.normalizedValue negative n e
  | .subnormalBlock negative s _ _ _ _ =>
      ieeeDoubleFormat.normalizedValue negative n ((s : ℤ) - 148)

theorem problem2_3_ieeeDouble_normalized_sameExponent_signed_between_mem
    {negative negativeD : Bool} {m n : ℕ} {e eD : ℤ}
    (hm : ieeeSingleFormat.normalizedMantissa m)
    (hmnext : ieeeSingleFormat.normalizedMantissa (m + 1))
    (he : ieeeSingleFormat.exponentInRange e)
    (hnD : ieeeDoubleFormat.normalizedMantissa n)
    (hbetween :
      problem2_3_adjacentSingleGapLeftValue
            (.sameExponent negative m e hm hmnext he) <
          ieeeDoubleFormat.normalizedValue negativeD n eD ∧
        ieeeDoubleFormat.normalizedValue negativeD n eD <
          problem2_3_adjacentSingleGapRightValue
            (.sameExponent negative m e hm hmnext he)) :
    negativeD = negative ∧ eD = e ∧
      n ∈ problem2_3_sameExponentInteriorDoubleMantissas m := by
  cases negative
  · simpa [problem2_3_adjacentSingleGapLeftValue,
      problem2_3_adjacentSingleGapRightValue] using
      (problem2_3_ieeeDouble_normalized_sameExponent_positive_between_mem
        (m := m) (n := n) (e := e) (eD := eD)
        (negativeD := negativeD) hm hmnext hnD hbetween)
  · cases negativeD
    · have hz_pos :
          0 < ieeeDoubleFormat.normalizedValue false n eD :=
        ieeeDoubleFormat.normalizedValue_false_pos hnD
      have hright_neg :
          ieeeSingleFormat.normalizedValue true m e < 0 :=
        ieeeSingleFormat.normalizedValue_true_neg hm
      have hbetween' :
          ieeeSingleFormat.normalizedValue true (m + 1) e <
              ieeeDoubleFormat.normalizedValue false n eD ∧
            ieeeDoubleFormat.normalizedValue false n eD <
              ieeeSingleFormat.normalizedValue true m e := by
        simpa [problem2_3_adjacentSingleGapLeftValue,
          problem2_3_adjacentSingleGapRightValue] using hbetween
      linarith [hbetween'.2]
    · have hpos_between :
          ieeeSingleFormat.normalizedValue false m e <
              ieeeDoubleFormat.normalizedValue false n eD ∧
            ieeeDoubleFormat.normalizedValue false n eD <
              ieeeSingleFormat.normalizedValue false (m + 1) e := by
        have hbetween' :
            ieeeSingleFormat.normalizedValue true (m + 1) e <
                ieeeDoubleFormat.normalizedValue true n eD ∧
              ieeeDoubleFormat.normalizedValue true n eD <
                ieeeSingleFormat.normalizedValue true m e := by
          simpa [problem2_3_adjacentSingleGapLeftValue,
            problem2_3_adjacentSingleGapRightValue] using hbetween
        constructor
        · have h := neg_lt_neg hbetween'.2
          rw [ieeeDoubleFormat.normalizedValue_true_eq_neg_false,
            ieeeSingleFormat.normalizedValue_true_eq_neg_false] at h
          simpa using h
        · have h := neg_lt_neg hbetween'.1
          rw [ieeeSingleFormat.normalizedValue_true_eq_neg_false,
            ieeeDoubleFormat.normalizedValue_true_eq_neg_false] at h
          simpa using h
      have hpos :=
        problem2_3_ieeeDouble_normalized_sameExponent_positive_between_mem
          (m := m) (n := n) (e := e) (eD := eD)
          (negativeD := false) hm hmnext hnD hpos_between
      exact ⟨rfl, hpos.2.1, hpos.2.2⟩

theorem problem2_3_ieeeDouble_finiteSystem_sameExponent_signed_between_exists_mem
    {negative : Bool} {m : ℕ} {e : ℤ} {z : ℝ}
    (hm : ieeeSingleFormat.normalizedMantissa m)
    (hmnext : ieeeSingleFormat.normalizedMantissa (m + 1))
    (he : ieeeSingleFormat.exponentInRange e)
    (hz : ieeeDoubleFormat.finiteSystem z)
    (hbetween :
      problem2_3_adjacentSingleGapLeftValue
            (.sameExponent negative m e hm hmnext he) < z ∧
        z <
          problem2_3_adjacentSingleGapRightValue
            (.sameExponent negative m e hm hmnext he)) :
    ∃ n : ℕ,
      n ∈ problem2_3_sameExponentInteriorDoubleMantissas m ∧
        z = ieeeDoubleFormat.normalizedValue negative n e := by
  rcases hz with hzero | hnorm | hsub
  · subst z
    cases negative
    · have hleft_pos :
          0 < ieeeSingleFormat.normalizedValue false m e :=
        ieeeSingleFormat.normalizedValue_false_pos hm
      have hbetween' :
          ieeeSingleFormat.normalizedValue false m e < 0 ∧
            0 < ieeeSingleFormat.normalizedValue false (m + 1) e := by
        simpa [problem2_3_adjacentSingleGapLeftValue,
          problem2_3_adjacentSingleGapRightValue] using hbetween
      linarith
    · have hright_neg :
          ieeeSingleFormat.normalizedValue true m e < 0 :=
        ieeeSingleFormat.normalizedValue_true_neg hm
      have hbetween' :
          ieeeSingleFormat.normalizedValue true (m + 1) e < 0 ∧
            0 < ieeeSingleFormat.normalizedValue true m e := by
        simpa [problem2_3_adjacentSingleGapLeftValue,
          problem2_3_adjacentSingleGapRightValue] using hbetween
      linarith
  · rcases hnorm with ⟨negativeD, n, eD, hnD, heD, rfl⟩
    have hclass :=
      problem2_3_ieeeDouble_normalized_sameExponent_signed_between_mem
        (negative := negative) (negativeD := negativeD)
        (m := m) (n := n) (e := e) (eD := eD)
        hm hmnext he hnD hbetween
    rcases hclass with ⟨rfl, rfl, hnmem⟩
    exact ⟨n, hnmem, rfl⟩
  · cases negative
    · have hsub_le :
          z ≤ ieeeDoubleFormat.minNormalMagnitude :=
        ieeeDoubleFormat.subnormalSystem_le_minNormalMagnitude hsub
      have hmin_lt_left :
          ieeeDoubleFormat.minNormalMagnitude <
            ieeeSingleFormat.normalizedValue false m e :=
        problem2_3_ieeeDouble_minNormalMagnitude_lt_ieeeSingle_normalized_false
          (m := m) (e := e) hm he
      have hbetween' :
          ieeeSingleFormat.normalizedValue false m e < z ∧
            z < ieeeSingleFormat.normalizedValue false (m + 1) e := by
        simpa [problem2_3_adjacentSingleGapLeftValue,
          problem2_3_adjacentSingleGapRightValue] using hbetween
      linarith
    · have hnegmin_le :
          -ieeeDoubleFormat.minNormalMagnitude ≤ z :=
        ieeeDoubleFormat.neg_minNormalMagnitude_le_subnormalSystem hsub
      have hright_lt_negmin :
          ieeeSingleFormat.normalizedValue true m e <
            -ieeeDoubleFormat.minNormalMagnitude :=
        problem2_3_ieeeSingle_normalized_true_lt_neg_ieeeDouble_minNormalMagnitude
          (m := m) (e := e) hm he
      have hbetween' :
          ieeeSingleFormat.normalizedValue true (m + 1) e < z ∧
            z < ieeeSingleFormat.normalizedValue true m e := by
        simpa [problem2_3_adjacentSingleGapLeftValue,
          problem2_3_adjacentSingleGapRightValue] using hbetween
      linarith

theorem problem2_3_ieeeDouble_normalized_boundary_signed_between_mem
    {negative negativeD : Bool} {n : ℕ} {e eD : ℤ}
    (he : ieeeSingleFormat.exponentInRange e)
    (heNext : ieeeSingleFormat.exponentInRange (e + 1))
    (hnD : ieeeDoubleFormat.normalizedMantissa n)
    (hbetween :
      problem2_3_adjacentSingleGapLeftValue
            (.boundary negative e he heNext) <
          ieeeDoubleFormat.normalizedValue negativeD n eD ∧
        ieeeDoubleFormat.normalizedValue negativeD n eD <
          problem2_3_adjacentSingleGapRightValue
            (.boundary negative e he heNext)) :
    negativeD = negative ∧ eD = e ∧
      n ∈ problem2_3_boundaryInteriorDoubleMantissas := by
  cases negative
  · simpa [problem2_3_adjacentSingleGapLeftValue,
      problem2_3_adjacentSingleGapRightValue] using
      (problem2_3_ieeeDouble_normalized_boundary_positive_between_mem
        (n := n) (e := e) (eD := eD) (negativeD := negativeD)
        hnD hbetween)
  · cases negativeD
    · have hz_pos :
          0 < ieeeDoubleFormat.normalizedValue false n eD :=
        ieeeDoubleFormat.normalizedValue_false_pos hnD
      have hright_neg :
          ieeeSingleFormat.normalizedValue true
            ieeeSingleFormat.maxNormalMantissa e < 0 :=
        ieeeSingleFormat.normalizedValue_true_neg
          ieeeSingleFormat.maxNormalMantissa_normalized
      have hbetween' :
          ieeeSingleFormat.normalizedValue true
              ieeeSingleFormat.minNormalMantissa (e + 1) <
              ieeeDoubleFormat.normalizedValue false n eD ∧
            ieeeDoubleFormat.normalizedValue false n eD <
              ieeeSingleFormat.normalizedValue true
                ieeeSingleFormat.maxNormalMantissa e := by
        simpa [problem2_3_adjacentSingleGapLeftValue,
          problem2_3_adjacentSingleGapRightValue] using hbetween
      linarith [hbetween'.2]
    · have hpos_between :
          ieeeSingleFormat.normalizedValue false
              ieeeSingleFormat.maxNormalMantissa e <
              ieeeDoubleFormat.normalizedValue false n eD ∧
            ieeeDoubleFormat.normalizedValue false n eD <
              ieeeSingleFormat.normalizedValue false
                ieeeSingleFormat.minNormalMantissa (e + 1) := by
        have hbetween' :
            ieeeSingleFormat.normalizedValue true
                ieeeSingleFormat.minNormalMantissa (e + 1) <
                ieeeDoubleFormat.normalizedValue true n eD ∧
              ieeeDoubleFormat.normalizedValue true n eD <
                ieeeSingleFormat.normalizedValue true
                  ieeeSingleFormat.maxNormalMantissa e := by
          simpa [problem2_3_adjacentSingleGapLeftValue,
            problem2_3_adjacentSingleGapRightValue] using hbetween
        constructor
        · have h := neg_lt_neg hbetween'.2
          rw [ieeeDoubleFormat.normalizedValue_true_eq_neg_false,
            ieeeSingleFormat.normalizedValue_true_eq_neg_false] at h
          simpa using h
        · have h := neg_lt_neg hbetween'.1
          rw [ieeeSingleFormat.normalizedValue_true_eq_neg_false,
            ieeeDoubleFormat.normalizedValue_true_eq_neg_false] at h
          simpa using h
      have hpos :=
        problem2_3_ieeeDouble_normalized_boundary_positive_between_mem
          (n := n) (e := e) (eD := eD) (negativeD := false)
          hnD hpos_between
      exact ⟨rfl, hpos.2.1, hpos.2.2⟩

theorem problem2_3_ieeeDouble_finiteSystem_boundary_signed_between_exists_mem
    {negative : Bool} {e : ℤ} {z : ℝ}
    (he : ieeeSingleFormat.exponentInRange e)
    (heNext : ieeeSingleFormat.exponentInRange (e + 1))
    (hz : ieeeDoubleFormat.finiteSystem z)
    (hbetween :
      problem2_3_adjacentSingleGapLeftValue
            (.boundary negative e he heNext) < z ∧
        z <
          problem2_3_adjacentSingleGapRightValue
            (.boundary negative e he heNext)) :
    ∃ n : ℕ,
      n ∈ problem2_3_boundaryInteriorDoubleMantissas ∧
        z = ieeeDoubleFormat.normalizedValue negative n e := by
  rcases hz with hzero | hnorm | hsub
  · subst z
    cases negative
    · have hleft_pos :
          0 < ieeeSingleFormat.normalizedValue false
            ieeeSingleFormat.maxNormalMantissa e :=
        ieeeSingleFormat.normalizedValue_false_pos
          ieeeSingleFormat.maxNormalMantissa_normalized
      have hbetween' :
          ieeeSingleFormat.normalizedValue false
              ieeeSingleFormat.maxNormalMantissa e < 0 ∧
            0 < ieeeSingleFormat.normalizedValue false
              ieeeSingleFormat.minNormalMantissa (e + 1) := by
        simpa [problem2_3_adjacentSingleGapLeftValue,
          problem2_3_adjacentSingleGapRightValue] using hbetween
      linarith
    · have hright_neg :
          ieeeSingleFormat.normalizedValue true
            ieeeSingleFormat.maxNormalMantissa e < 0 :=
        ieeeSingleFormat.normalizedValue_true_neg
          ieeeSingleFormat.maxNormalMantissa_normalized
      have hbetween' :
          ieeeSingleFormat.normalizedValue true
              ieeeSingleFormat.minNormalMantissa (e + 1) < 0 ∧
            0 < ieeeSingleFormat.normalizedValue true
              ieeeSingleFormat.maxNormalMantissa e := by
        simpa [problem2_3_adjacentSingleGapLeftValue,
          problem2_3_adjacentSingleGapRightValue] using hbetween
      linarith
  · rcases hnorm with ⟨negativeD, n, eD, hnD, heD, rfl⟩
    have hclass :=
      problem2_3_ieeeDouble_normalized_boundary_signed_between_mem
        (negative := negative) (negativeD := negativeD)
        (n := n) (e := e) (eD := eD) he heNext hnD hbetween
    rcases hclass with ⟨rfl, rfl, hnmem⟩
    exact ⟨n, hnmem, rfl⟩
  · cases negative
    · have hsub_le :
          z ≤ ieeeDoubleFormat.minNormalMagnitude :=
        ieeeDoubleFormat.subnormalSystem_le_minNormalMagnitude hsub
      have hmin_lt_left :
          ieeeDoubleFormat.minNormalMagnitude <
            ieeeSingleFormat.normalizedValue false
              ieeeSingleFormat.maxNormalMantissa e :=
        problem2_3_ieeeDouble_minNormalMagnitude_lt_ieeeSingle_normalized_false
          (m := ieeeSingleFormat.maxNormalMantissa) (e := e)
          ieeeSingleFormat.maxNormalMantissa_normalized he
      have hbetween' :
          ieeeSingleFormat.normalizedValue false
              ieeeSingleFormat.maxNormalMantissa e < z ∧
            z < ieeeSingleFormat.normalizedValue false
              ieeeSingleFormat.minNormalMantissa (e + 1) := by
        simpa [problem2_3_adjacentSingleGapLeftValue,
          problem2_3_adjacentSingleGapRightValue] using hbetween
      linarith
    · have hnegmin_le :
          -ieeeDoubleFormat.minNormalMagnitude ≤ z :=
        ieeeDoubleFormat.neg_minNormalMagnitude_le_subnormalSystem hsub
      have hright_lt_negmin :
          ieeeSingleFormat.normalizedValue true
              ieeeSingleFormat.maxNormalMantissa e <
            -ieeeDoubleFormat.minNormalMagnitude :=
        problem2_3_ieeeSingle_normalized_true_lt_neg_ieeeDouble_minNormalMagnitude
          (m := ieeeSingleFormat.maxNormalMantissa) (e := e)
          ieeeSingleFormat.maxNormalMantissa_normalized he
      have hbetween' :
          ieeeSingleFormat.normalizedValue true
              ieeeSingleFormat.minNormalMantissa (e + 1) < z ∧
            z < ieeeSingleFormat.normalizedValue true
              ieeeSingleFormat.maxNormalMantissa e := by
        simpa [problem2_3_adjacentSingleGapLeftValue,
          problem2_3_adjacentSingleGapRightValue] using hbetween
      linarith

theorem problem2_3_ieeeDouble_normalized_subnormalBlock_signed_between_mem
    {negative negativeD : Bool} {s m n : ℕ} {eD : ℤ}
    (hs : s ≤ 22)
    (hmlo : 2 ^ s ≤ m)
    (hmhi : m + 1 ≤ 2 ^ (s + 1))
    (hnD : ieeeDoubleFormat.normalizedMantissa n)
    (hbetween :
      problem2_3_adjacentSingleGapLeftValue
            (.subnormalBlock negative s m hs hmlo hmhi) <
          ieeeDoubleFormat.normalizedValue negativeD n eD ∧
        ieeeDoubleFormat.normalizedValue negativeD n eD <
          problem2_3_adjacentSingleGapRightValue
            (.subnormalBlock negative s m hs hmlo hmhi)) :
    negativeD = negative ∧ eD = (s : ℤ) - 148 ∧
      n ∈ problem2_3_subnormalBlockInteriorDoubleMantissas s m := by
  cases negative
  · simpa [problem2_3_adjacentSingleGapLeftValue,
      problem2_3_adjacentSingleGapRightValue] using
      (problem2_3_ieeeDouble_normalized_subnormalBlock_positive_between_mem
        (s := s) (m := m) (n := n) (eD := eD)
        (negativeD := negativeD) hs hmlo hmhi hnD hbetween)
  · cases negativeD
    · have hmSingle : ieeeSingleFormat.subnormalMantissa m :=
        problem2_3_ieeeSingle_subnormalMantissa_of_block hs hmlo hmhi
      have hz_pos :
          0 < ieeeDoubleFormat.normalizedValue false n eD :=
        ieeeDoubleFormat.normalizedValue_false_pos hnD
      have hright_neg :
          ieeeSingleFormat.subnormalValue true m < 0 :=
        ieeeSingleFormat.subnormalValue_true_neg hmSingle
      have hbetween' :
          ieeeSingleFormat.subnormalValue true (m + 1) <
              ieeeDoubleFormat.normalizedValue false n eD ∧
            ieeeDoubleFormat.normalizedValue false n eD <
              ieeeSingleFormat.subnormalValue true m := by
        simpa [problem2_3_adjacentSingleGapLeftValue,
          problem2_3_adjacentSingleGapRightValue] using hbetween
      linarith [hbetween'.2]
    · have hpos_between :
          ieeeSingleFormat.subnormalValue false m <
              ieeeDoubleFormat.normalizedValue false n eD ∧
            ieeeDoubleFormat.normalizedValue false n eD <
              ieeeSingleFormat.subnormalValue false (m + 1) := by
        have hbetween' :
            ieeeSingleFormat.subnormalValue true (m + 1) <
                ieeeDoubleFormat.normalizedValue true n eD ∧
              ieeeDoubleFormat.normalizedValue true n eD <
                ieeeSingleFormat.subnormalValue true m := by
          simpa [problem2_3_adjacentSingleGapLeftValue,
            problem2_3_adjacentSingleGapRightValue] using hbetween
        constructor
        · have h := neg_lt_neg hbetween'.2
          rw [ieeeDoubleFormat.normalizedValue_true_eq_neg_false,
            show ieeeSingleFormat.subnormalValue true m =
              -ieeeSingleFormat.subnormalValue false m by
                exact ieeeSingleFormat.subnormalValue_not_eq_neg false m] at h
          simpa using h
        · have h := neg_lt_neg hbetween'.1
          rw [show ieeeSingleFormat.subnormalValue true (m + 1) =
              -ieeeSingleFormat.subnormalValue false (m + 1) by
                exact ieeeSingleFormat.subnormalValue_not_eq_neg false (m + 1),
            ieeeDoubleFormat.normalizedValue_true_eq_neg_false] at h
          simpa using h
      have hpos :=
        problem2_3_ieeeDouble_normalized_subnormalBlock_positive_between_mem
          (s := s) (m := m) (n := n) (eD := eD)
          (negativeD := false) hs hmlo hmhi hnD hpos_between
      exact ⟨rfl, hpos.2.1, hpos.2.2⟩

theorem problem2_3_ieeeDouble_finiteSystem_subnormalBlock_signed_between_exists_mem
    {negative : Bool} {s m : ℕ} {z : ℝ}
    (hs : s ≤ 22)
    (hmlo : 2 ^ s ≤ m)
    (hmhi : m + 1 ≤ 2 ^ (s + 1))
    (hz : ieeeDoubleFormat.finiteSystem z)
    (hbetween :
      problem2_3_adjacentSingleGapLeftValue
            (.subnormalBlock negative s m hs hmlo hmhi) < z ∧
        z <
          problem2_3_adjacentSingleGapRightValue
            (.subnormalBlock negative s m hs hmlo hmhi)) :
    ∃ n : ℕ,
      n ∈ problem2_3_subnormalBlockInteriorDoubleMantissas s m ∧
        z = ieeeDoubleFormat.normalizedValue negative n ((s : ℤ) - 148) := by
  have hmSingle : ieeeSingleFormat.subnormalMantissa m :=
    problem2_3_ieeeSingle_subnormalMantissa_of_block hs hmlo hmhi
  rcases hz with hzero | hnorm | hsub
  · subst z
    cases negative
    · have hleft_pos :
          0 < ieeeSingleFormat.subnormalValue false m :=
        ieeeSingleFormat.subnormalValue_false_pos hmSingle
      have hbetween' :
          ieeeSingleFormat.subnormalValue false m < 0 ∧
            0 < ieeeSingleFormat.subnormalValue false (m + 1) := by
        simpa [problem2_3_adjacentSingleGapLeftValue,
          problem2_3_adjacentSingleGapRightValue] using hbetween
      linarith
    · have hright_neg :
          ieeeSingleFormat.subnormalValue true m < 0 :=
        ieeeSingleFormat.subnormalValue_true_neg hmSingle
      have hbetween' :
          ieeeSingleFormat.subnormalValue true (m + 1) < 0 ∧
            0 < ieeeSingleFormat.subnormalValue true m := by
        simpa [problem2_3_adjacentSingleGapLeftValue,
          problem2_3_adjacentSingleGapRightValue] using hbetween
      linarith
  · rcases hnorm with ⟨negativeD, n, eD, hnD, heD, rfl⟩
    have hclass :=
      problem2_3_ieeeDouble_normalized_subnormalBlock_signed_between_mem
        (negative := negative) (negativeD := negativeD)
        (s := s) (m := m) (n := n) (eD := eD)
        hs hmlo hmhi hnD hbetween
    rcases hclass with ⟨rfl, rfl, hnmem⟩
    exact ⟨n, hnmem, rfl⟩
  · cases negative
    · have hsub_le :
          z ≤ ieeeDoubleFormat.minNormalMagnitude :=
        ieeeDoubleFormat.subnormalSystem_le_minNormalMagnitude hsub
      have hmin_lt_left :
          ieeeDoubleFormat.minNormalMagnitude <
            ieeeSingleFormat.subnormalValue false m :=
        problem2_3_ieeeDouble_minNormalMagnitude_lt_ieeeSingle_subnormal_false
          hmSingle
      have hbetween' :
          ieeeSingleFormat.subnormalValue false m < z ∧
            z < ieeeSingleFormat.subnormalValue false (m + 1) := by
        simpa [problem2_3_adjacentSingleGapLeftValue,
          problem2_3_adjacentSingleGapRightValue] using hbetween
      linarith
    · have hnegmin_le :
          -ieeeDoubleFormat.minNormalMagnitude ≤ z :=
        ieeeDoubleFormat.neg_minNormalMagnitude_le_subnormalSystem hsub
      have hright_lt_negmin :
          ieeeSingleFormat.subnormalValue true m <
            -ieeeDoubleFormat.minNormalMagnitude :=
        problem2_3_ieeeSingle_subnormal_true_lt_neg_ieeeDouble_minNormalMagnitude
          hmSingle
      have hbetween' :
          ieeeSingleFormat.subnormalValue true (m + 1) < z ∧
            z < ieeeSingleFormat.subnormalValue true m := by
        simpa [problem2_3_adjacentSingleGapLeftValue,
          problem2_3_adjacentSingleGapRightValue] using hbetween
      linarith

theorem problem2_3_adjacentSingleGap_finiteSystem_between_exists_mem
    (g : Problem2_3IeeeSingleAdjacentGap) {z : ℝ}
    (hz : ieeeDoubleFormat.finiteSystem z)
    (hbetween :
      problem2_3_adjacentSingleGapLeftValue g < z ∧
        z < problem2_3_adjacentSingleGapRightValue g) :
    ∃ n : ℕ,
      n ∈ problem2_3_adjacentSingleGapInteriorDoubleMantissas g ∧
        z = problem2_3_adjacentSingleGapDoubleValue g n := by
  cases g with
  | sameExponent negative m e hm hmnext he =>
      rcases
        problem2_3_ieeeDouble_finiteSystem_sameExponent_signed_between_exists_mem
          (negative := negative) (m := m) (e := e) hm hmnext he hz hbetween
        with ⟨n, hnmem, hz_eq⟩
      exact ⟨n, by
        simpa [problem2_3_adjacentSingleGapInteriorDoubleMantissas] using hnmem,
        by
          simpa [problem2_3_adjacentSingleGapDoubleValue] using hz_eq⟩
  | boundary negative e he heNext =>
      rcases
        problem2_3_ieeeDouble_finiteSystem_boundary_signed_between_exists_mem
          (negative := negative) (e := e) he heNext hz hbetween
        with ⟨n, hnmem, hz_eq⟩
      exact ⟨n, by
        simpa [problem2_3_adjacentSingleGapInteriorDoubleMantissas] using hnmem,
        by
          simpa [problem2_3_adjacentSingleGapDoubleValue] using hz_eq⟩
  | subnormalBlock negative s m hs hmlo hmhi =>
      rcases
        problem2_3_ieeeDouble_finiteSystem_subnormalBlock_signed_between_exists_mem
          (negative := negative) (s := s) (m := m) hs hmlo hmhi hz hbetween
        with ⟨n, hnmem, hz_eq⟩
      exact ⟨n, by
        simpa [problem2_3_adjacentSingleGapInteriorDoubleMantissas] using hnmem,
        by
          simpa [problem2_3_adjacentSingleGapDoubleValue] using hz_eq⟩

theorem problem2_3_adjacentSingleGapInteriorDoubleMantissas_card
    (g : Problem2_3IeeeSingleAdjacentGap) :
    (problem2_3_adjacentSingleGapInteriorDoubleMantissas g).card =
      problem2_3_adjacentSingleGapInteriorCount g := by
  cases g with
  | sameExponent negative m e hm hmnext he =>
      exact problem2_3_sameExponentInteriorDoubleMantissas_card m
  | boundary negative e he heNext =>
      exact problem2_3_boundaryInteriorDoubleMantissas_card
  | subnormalBlock negative s m hs hmlo hmhi =>
      exact problem2_3_subnormalBlockInteriorDoubleMantissas_card s m

theorem problem2_3_adjacentSingleGap_between_iff_mem
    (g : Problem2_3IeeeSingleAdjacentGap) {n : ℕ} :
    (problem2_3_adjacentSingleGapLeftValue g <
        problem2_3_adjacentSingleGapDoubleValue g n ∧
      problem2_3_adjacentSingleGapDoubleValue g n <
        problem2_3_adjacentSingleGapRightValue g) ↔
      n ∈ problem2_3_adjacentSingleGapInteriorDoubleMantissas g := by
  cases g with
  | sameExponent negative m e hm hmnext he =>
      cases negative
      · simpa [problem2_3_adjacentSingleGapLeftValue,
          problem2_3_adjacentSingleGapRightValue,
          problem2_3_adjacentSingleGapDoubleValue,
          problem2_3_adjacentSingleGapInteriorDoubleMantissas] using
          (problem2_3_ieeeDouble_sameExponent_between_iff_mem
            (m := m) (n := n) (e := e))
      · simpa [problem2_3_adjacentSingleGapLeftValue,
          problem2_3_adjacentSingleGapRightValue,
          problem2_3_adjacentSingleGapDoubleValue,
          problem2_3_adjacentSingleGapInteriorDoubleMantissas] using
          (problem2_3_ieeeDouble_sameExponent_negative_between_iff_mem
            (m := m) (n := n) (e := e))
  | boundary negative e he heNext =>
      cases negative
      · simpa [problem2_3_adjacentSingleGapLeftValue,
          problem2_3_adjacentSingleGapRightValue,
          problem2_3_adjacentSingleGapDoubleValue,
          problem2_3_adjacentSingleGapInteriorDoubleMantissas] using
          (problem2_3_ieeeDouble_boundary_between_iff_mem
            (n := n) (e := e))
      · simpa [problem2_3_adjacentSingleGapLeftValue,
          problem2_3_adjacentSingleGapRightValue,
          problem2_3_adjacentSingleGapDoubleValue,
          problem2_3_adjacentSingleGapInteriorDoubleMantissas] using
          (problem2_3_ieeeDouble_boundary_negative_between_iff_mem
            (n := n) (e := e))
  | subnormalBlock negative s m hs hmlo hmhi =>
      have hs52 : s ≤ 52 := by omega
      cases negative
      · simpa [problem2_3_adjacentSingleGapLeftValue,
          problem2_3_adjacentSingleGapRightValue,
          problem2_3_adjacentSingleGapDoubleValue,
          problem2_3_adjacentSingleGapInteriorDoubleMantissas] using
          (problem2_3_ieeeDouble_subnormalBlock_between_iff_mem
            (s := s) (m := m) (n := n) hs52)
      · simpa [problem2_3_adjacentSingleGapLeftValue,
          problem2_3_adjacentSingleGapRightValue,
          problem2_3_adjacentSingleGapDoubleValue,
          problem2_3_adjacentSingleGapInteriorDoubleMantissas] using
          (problem2_3_ieeeDouble_subnormalBlock_negative_between_iff_mem
            (s := s) (m := m) (n := n) hs52)

theorem problem2_3_adjacentSingleGapDoubleValue_finiteSystem_of_mem
    (g : Problem2_3IeeeSingleAdjacentGap) {n : ℕ}
    (hn : n ∈ problem2_3_adjacentSingleGapInteriorDoubleMantissas g) :
    ieeeDoubleFormat.finiteSystem
      (problem2_3_adjacentSingleGapDoubleValue g n) := by
  cases g with
  | sameExponent negative m e hm hmnext he =>
      have hn_branch :
          n ∈ problem2_3_sameExponentInteriorDoubleMantissas m := by
        simpa [problem2_3_adjacentSingleGapInteriorDoubleMantissas] using hn
      have hmD :
          ieeeDoubleFormat.normalizedMantissa n :=
        problem2_3_sameExponentInteriorDoubleMantissa_normalized_of_mem
          hm hn_branch
      have heD : ieeeDoubleFormat.exponentInRange e :=
        problem2_3_ieeeSingle_exponentInRange_ieeeDouble he
      exact Or.inr (Or.inl ⟨negative, n, e, hmD, heD, rfl⟩)
  | boundary negative e he heNext =>
      have hn_branch :
          n ∈ problem2_3_boundaryInteriorDoubleMantissas := by
        simpa [problem2_3_adjacentSingleGapInteriorDoubleMantissas] using hn
      have hmD :
          ieeeDoubleFormat.normalizedMantissa n :=
        problem2_3_boundaryInteriorDoubleMantissa_normalized_of_mem hn_branch
      have heD : ieeeDoubleFormat.exponentInRange e :=
        problem2_3_ieeeSingle_exponentInRange_ieeeDouble he
      exact Or.inr (Or.inl ⟨negative, n, e, hmD, heD, rfl⟩)
  | subnormalBlock negative s m hs hmlo hmhi =>
      have hn_branch :
          n ∈ problem2_3_subnormalBlockInteriorDoubleMantissas s m := by
        simpa [problem2_3_adjacentSingleGapInteriorDoubleMantissas] using hn
      have hmD :
          ieeeDoubleFormat.normalizedMantissa n :=
        problem2_3_subnormalBlockInteriorDoubleMantissa_normalized_of_mem
          hs hmlo hmhi hn_branch
      have heD :
          ieeeDoubleFormat.exponentInRange ((s : ℤ) - 148) := by
        norm_num [ieeeDoubleFormat, exponentInRange]
        omega
      exact Or.inr (Or.inl
        ⟨negative, n, (s : ℤ) - 148, hmD, heD, rfl⟩)

end FloatingPointFormat

end

end NumStability
