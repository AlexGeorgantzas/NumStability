-- Analysis/Problem2_6.lean
--
-- Problem-specific theorem surface for Higham Chapter 2, Problem 2.6.

import Mathlib.Tactic.NormNum
import NumStability.Analysis.FloatingPointArithmetic

namespace NumStability

noncomputable section

namespace FloatingPointFormat

/-!
# Higham Chapter 2, Problem 2.6

Problem 2.6 asks for the largest integer `p` such that every integer in
`[-p,p]` is exactly representable in IEEE double precision, and for the
corresponding single precision value.  The theorem surface below records the
claim in the repository's finite-format model: an integer interval is
representable when every natural integer up to `p`, with either sign, is a
member of `finiteSystem`.
-/

/-- Source-shaped predicate for Problem 2.6's symmetric integer interval. -/
def integerIntervalRepresentable (fmt : FloatingPointFormat) (p : ℕ) : Prop :=
  (∀ n : ℕ, n ≤ p → fmt.finiteSystem (n : ℝ)) ∧
    ∀ n : ℕ, n ≤ p → fmt.finiteSystem (-(n : ℝ))

theorem problem2_6_ieeeSingle_two_pow_24_finiteSystem :
    ieeeSingleFormat.finiteSystem ((2 : ℝ) ^ 24) := by
  have h :=
    ieeeSingleFormat.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
      (negative := false) (k := (8388608 : ℤ)) (e := (25 : ℤ))
      (by norm_num [ieeeSingleFormat, exponentInRange])
      (by norm_num [ieeeSingleFormat])
  convert h using 1
  norm_num [ieeeSingleFormat, signValue, betaR, zpow_neg]

theorem problem2_6_ieeeSingle_neg_two_pow_24_finiteSystem :
    ieeeSingleFormat.finiteSystem (-((2 : ℝ) ^ 24)) := by
  have h :=
    ieeeSingleFormat.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
      (negative := true) (k := (8388608 : ℤ)) (e := (25 : ℤ))
      (by norm_num [ieeeSingleFormat, exponentInRange])
      (by norm_num [ieeeSingleFormat])
  convert h using 1
  norm_num [ieeeSingleFormat, signValue, betaR, zpow_neg]

theorem problem2_6_ieeeDouble_two_pow_53_finiteSystem :
    ieeeDoubleFormat.finiteSystem ((2 : ℝ) ^ 53) := by
  have h :=
    ieeeDoubleFormat.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
      (negative := false) (k := (4503599627370496 : ℤ)) (e := (54 : ℤ))
      (by norm_num [ieeeDoubleFormat, exponentInRange])
      (by norm_num [ieeeDoubleFormat])
  convert h using 1
  norm_num [ieeeDoubleFormat, signValue, betaR, zpow_neg]

theorem problem2_6_ieeeDouble_neg_two_pow_53_finiteSystem :
    ieeeDoubleFormat.finiteSystem (-((2 : ℝ) ^ 53)) := by
  have h :=
    ieeeDoubleFormat.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
      (negative := true) (k := (4503599627370496 : ℤ)) (e := (54 : ℤ))
      (by norm_num [ieeeDoubleFormat, exponentInRange])
      (by norm_num [ieeeDoubleFormat])
  convert h using 1
  norm_num [ieeeDoubleFormat, signValue, betaR, zpow_neg]

theorem problem2_6_ieeeSingle_integerIntervalRepresentable_two_pow_24 :
    integerIntervalRepresentable ieeeSingleFormat (2 ^ 24) := by
  constructor
  · intro n hn
    by_cases hlt : n < 2 ^ 24
    · have h :=
        ieeeSingleFormat.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
          (negative := false) (k := (n : ℤ)) (e := (24 : ℤ))
          (by norm_num [ieeeSingleFormat, exponentInRange])
          (by simpa [ieeeSingleFormat] using hlt)
      convert h using 1
      norm_num [ieeeSingleFormat, signValue, betaR, zpow_neg]
    · have hn_eq : n = 2 ^ 24 := by omega
      subst n
      convert problem2_6_ieeeSingle_two_pow_24_finiteSystem using 1
      norm_num
  · intro n hn
    by_cases hlt : n < 2 ^ 24
    · have h :=
        ieeeSingleFormat.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
          (negative := true) (k := (n : ℤ)) (e := (24 : ℤ))
          (by norm_num [ieeeSingleFormat, exponentInRange])
          (by simpa [ieeeSingleFormat] using hlt)
      convert h using 1
      norm_num [ieeeSingleFormat, signValue, betaR, zpow_neg]
    · have hn_eq : n = 2 ^ 24 := by omega
      subst n
      convert problem2_6_ieeeSingle_neg_two_pow_24_finiteSystem using 1
      norm_num

theorem problem2_6_ieeeDouble_integerIntervalRepresentable_two_pow_53 :
    integerIntervalRepresentable ieeeDoubleFormat (2 ^ 53) := by
  constructor
  · intro n hn
    by_cases hlt : n < 2 ^ 53
    · have h :=
        ieeeDoubleFormat.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
          (negative := false) (k := (n : ℤ)) (e := (53 : ℤ))
          (by norm_num [ieeeDoubleFormat, exponentInRange])
          (by simpa [ieeeDoubleFormat] using hlt)
      convert h using 1
      norm_num [ieeeDoubleFormat, signValue, betaR, zpow_neg]
    · have hn_eq : n = 2 ^ 53 := by omega
      subst n
      convert problem2_6_ieeeDouble_two_pow_53_finiteSystem using 1
      norm_num
  · intro n hn
    by_cases hlt : n < 2 ^ 53
    · have h :=
        ieeeDoubleFormat.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
          (negative := true) (k := (n : ℤ)) (e := (53 : ℤ))
          (by norm_num [ieeeDoubleFormat, exponentInRange])
          (by simpa [ieeeDoubleFormat] using hlt)
      convert h using 1
      norm_num [ieeeDoubleFormat, signValue, betaR, zpow_neg]
    · have hn_eq : n = 2 ^ 53 := by omega
      subst n
      convert problem2_6_ieeeDouble_neg_two_pow_53_finiteSystem using 1
      norm_num

theorem problem2_6_ieeeSingle_two_pow_24_add_one_not_finiteSystem :
    ¬ ieeeSingleFormat.finiteSystem (((2 ^ 24 + 1 : ℕ) : ℝ)) := by
  let a : ℝ := ieeeSingleFormat.normalizedValue false 8388608 (25 : ℤ)
  let b : ℝ := ieeeSingleFormat.normalizedValue false 8388609 (25 : ℤ)
  have hm : ieeeSingleFormat.normalizedMantissa 8388608 := by
    norm_num [ieeeSingleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  have hmnext : ieeeSingleFormat.normalizedMantissa (8388608 + 1) := by
    norm_num [ieeeSingleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  have hadj : ieeeSingleFormat.realOrderAdjacentNormalized a b :=
    ieeeSingleFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 8388608, (25 : ℤ), hm, hmnext, Or.inl ⟨rfl, by
        norm_num [b]⟩⟩
  intro hfin
  have hzun :
      ieeeSingleFormat.unboundedNormalizedSystem (((2 ^ 24 + 1 : ℕ) : ℝ)) := by
    rcases hfin with hzero | hnorm | hsub
    · norm_num at hzero
    · exact ieeeSingleFormat.normalizedSystem_unboundedNormalizedSystem hnorm
    · have hle := ieeeSingleFormat.subnormalSystem_le_minNormalMagnitude hsub
      norm_num [ieeeSingleFormat, minNormalMagnitude, betaR, zpow_neg] at hle
  have hbetween :
      (a < (((2 ^ 24 + 1 : ℕ) : ℝ)) ∧
          (((2 ^ 24 + 1 : ℕ) : ℝ)) < b) ∨
        (b < (((2 ^ 24 + 1 : ℕ) : ℝ)) ∧
          (((2 ^ 24 + 1 : ℕ) : ℝ)) < a) := by
    left
    norm_num [a, b, ieeeSingleFormat, normalizedValue, signValue, betaR,
      zpow_neg]
  exact hadj.2.2.2 (((2 ^ 24 + 1 : ℕ) : ℝ)) hzun hbetween

theorem problem2_6_ieeeDouble_two_pow_53_add_one_not_finiteSystem :
    ¬ ieeeDoubleFormat.finiteSystem (((2 ^ 53 + 1 : ℕ) : ℝ)) := by
  let a : ℝ := ieeeDoubleFormat.normalizedValue false 4503599627370496 (54 : ℤ)
  let b : ℝ := ieeeDoubleFormat.normalizedValue false 4503599627370497 (54 : ℤ)
  have hm : ieeeDoubleFormat.normalizedMantissa 4503599627370496 := by
    norm_num [ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  have hmnext : ieeeDoubleFormat.normalizedMantissa (4503599627370496 + 1) := by
    norm_num [ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  have hadj : ieeeDoubleFormat.realOrderAdjacentNormalized a b :=
    ieeeDoubleFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 4503599627370496, (54 : ℤ), hm, hmnext, Or.inl ⟨rfl, by
        norm_num [b]⟩⟩
  intro hfin
  have hzun :
      ieeeDoubleFormat.unboundedNormalizedSystem (((2 ^ 53 + 1 : ℕ) : ℝ)) := by
    rcases hfin with hzero | hnorm | hsub
    · norm_num at hzero
    · exact ieeeDoubleFormat.normalizedSystem_unboundedNormalizedSystem hnorm
    · have hle := ieeeDoubleFormat.subnormalSystem_le_minNormalMagnitude hsub
      norm_num [ieeeDoubleFormat, minNormalMagnitude, betaR, zpow_neg] at hle
      have hupper : ((2 : ℝ) ^ 1022)⁻¹ ≤ 1 := by
        have hge : (1 : ℝ) ≤ (2 : ℝ) ^ 1022 :=
          one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
        exact inv_le_one_of_one_le₀ hge
      have hbig : (1 : ℝ) < 9007199254740993 := by norm_num
      exact False.elim ((not_lt_of_ge hupper) (lt_of_lt_of_le hbig hle))
  have hbetween :
      (a < (((2 ^ 53 + 1 : ℕ) : ℝ)) ∧
          (((2 ^ 53 + 1 : ℕ) : ℝ)) < b) ∨
        (b < (((2 ^ 53 + 1 : ℕ) : ℝ)) ∧
          (((2 ^ 53 + 1 : ℕ) : ℝ)) < a) := by
    left
    norm_num [a, b, ieeeDoubleFormat, normalizedValue, signValue, betaR,
      zpow_neg]
  exact hadj.2.2.2 (((2 ^ 53 + 1 : ℕ) : ℝ)) hzun hbetween

theorem problem2_6_ieeeSingle_integerIntervalRepresentable_bound
    {p : ℕ} (h : integerIntervalRepresentable ieeeSingleFormat p) :
    p ≤ 2 ^ 24 := by
  by_contra hp
  have hnext : 2 ^ 24 + 1 ≤ p := by omega
  exact problem2_6_ieeeSingle_two_pow_24_add_one_not_finiteSystem
    (h.1 (2 ^ 24 + 1) hnext)

theorem problem2_6_ieeeDouble_integerIntervalRepresentable_bound
    {p : ℕ} (h : integerIntervalRepresentable ieeeDoubleFormat p) :
    p ≤ 2 ^ 53 := by
  by_contra hp
  have hnext : 2 ^ 53 + 1 ≤ p := by omega
  exact problem2_6_ieeeDouble_two_pow_53_add_one_not_finiteSystem
    (h.1 (2 ^ 53 + 1) hnext)

/-- Problem 2.6 single-precision answer: the largest such integer is `2^24`. -/
theorem problem2_6_ieeeSingle_largest_integer_interval :
    integerIntervalRepresentable ieeeSingleFormat (2 ^ 24) ∧
      ∀ p : ℕ, integerIntervalRepresentable ieeeSingleFormat p → p ≤ 2 ^ 24 :=
  ⟨problem2_6_ieeeSingle_integerIntervalRepresentable_two_pow_24,
    fun _ h => problem2_6_ieeeSingle_integerIntervalRepresentable_bound h⟩

/-- Problem 2.6 double-precision answer: the largest such integer is `2^53`. -/
theorem problem2_6_ieeeDouble_largest_integer_interval :
    integerIntervalRepresentable ieeeDoubleFormat (2 ^ 53) ∧
      ∀ p : ℕ, integerIntervalRepresentable ieeeDoubleFormat p → p ≤ 2 ^ 53 :=
  ⟨problem2_6_ieeeDouble_integerIntervalRepresentable_two_pow_53,
    fun _ h => problem2_6_ieeeDouble_integerIntervalRepresentable_bound h⟩

end FloatingPointFormat

end

end NumStability
