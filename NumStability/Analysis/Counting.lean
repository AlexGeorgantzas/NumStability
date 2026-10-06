-- Analysis/Counting.lean
--
-- Counting facts for Higham Chapter 2, Problem 2.1.

import Mathlib.Tactic.NormNum
import NumStability.Analysis.FloatingPointArithmetic

namespace NumStability

noncomputable section

namespace FloatingPointFormat

/-!
# Higham Chapter 2, Problem 2.1

Problem 2.1 asks for the number of normalized and subnormal numbers in the
finite system `F`, then for the corresponding IEEE single and double precision
figures.  The source format here uses the repository's inclusive exponent range
`emin <= e <= emax`, the same convention recorded in `FloatingPointFormat`.

These counts are nonzero signed value-parameter counts: one sign bit, one
valid mantissa, and, for normalized numbers, one exponent.  The normalized
value representation is already proved unique by
`normalizedValue_eq_iff_sign_exp_mantissa`; this file also records the analogous
subnormal uniqueness theorem.
-/

/-- Number of exponent parameters in the inclusive normalized exponent range. -/
def normalizedExponentParameterCount (fmt : FloatingPointFormat) : ℕ :=
  Int.toNat (fmt.emax - fmt.emin + 1)

/-- Number of valid normalized mantissas, `beta^t - beta^(t-1)`. -/
def normalizedMantissaParameterCount (fmt : FloatingPointFormat) : ℕ :=
  fmt.maxNormalMantissa - fmt.minNormalMantissa + 1

/-- Number of valid nonzero subnormal mantissas, `beta^(t-1) - 1`. -/
def subnormalMantissaParameterCount (fmt : FloatingPointFormat) : ℕ :=
  fmt.minNormalMantissa - 1

/-- Two ordinary signs, positive and negative. -/
def signedParameterCount (_fmt : FloatingPointFormat) : ℕ :=
  2

/-- Number of signed nonzero normalized finite-format parameters. -/
def normalizedNumberParameterCount (fmt : FloatingPointFormat) : ℕ :=
  fmt.signedParameterCount *
    fmt.normalizedExponentParameterCount *
      fmt.normalizedMantissaParameterCount

/-- Number of signed nonzero subnormal finite-format parameters. -/
def subnormalNumberParameterCount (fmt : FloatingPointFormat) : ℕ :=
  fmt.signedParameterCount * fmt.subnormalMantissaParameterCount

theorem normalizedMantissaParameterCount_eq_beta_pow_sub
    (fmt : FloatingPointFormat) :
    fmt.normalizedMantissaParameterCount =
      fmt.beta ^ fmt.t - fmt.beta ^ (fmt.t - 1) := by
  unfold normalizedMantissaParameterCount
  have hle : fmt.minNormalMantissa ≤ fmt.maxNormalMantissa :=
    fmt.minNormalMantissa_le_maxNormalMantissa
  have hcount :
      fmt.maxNormalMantissa - fmt.minNormalMantissa + 1 =
        fmt.maxNormalMantissa + 1 - fmt.minNormalMantissa := by
    omega
  rw [hcount, fmt.maxNormalMantissa_add_one]
  unfold minNormalMantissa
  rfl

theorem subnormalMantissaParameterCount_eq_beta_pow_sub_one
    (fmt : FloatingPointFormat) :
    fmt.subnormalMantissaParameterCount =
      fmt.beta ^ (fmt.t - 1) - 1 := rfl

theorem normalizedNumberParameterCount_eq_problem2_1_formula
    (fmt : FloatingPointFormat) :
    fmt.normalizedNumberParameterCount =
      2 * Int.toNat (fmt.emax - fmt.emin + 1) *
        (fmt.beta ^ fmt.t - fmt.beta ^ (fmt.t - 1)) := by
  simp [normalizedNumberParameterCount, signedParameterCount,
    normalizedExponentParameterCount,
    normalizedMantissaParameterCount_eq_beta_pow_sub]

theorem subnormalNumberParameterCount_eq_problem2_1_formula
    (fmt : FloatingPointFormat) :
    fmt.subnormalNumberParameterCount =
      2 * (fmt.beta ^ (fmt.t - 1) - 1) := by
  simp [subnormalNumberParameterCount, signedParameterCount,
    subnormalMantissaParameterCount_eq_beta_pow_sub_one]

theorem subnormalValue_false_eq_iff
    {fmt : FloatingPointFormat} {m n : ℕ}
    (_hm : fmt.subnormalMantissa m) (_hn : fmt.subnormalMantissa n) :
    fmt.subnormalValue false m = fmt.subnormalValue false n ↔ m = n := by
  constructor
  · intro h
    have hscale_ne :
        fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) ≠ 0 :=
      ne_of_gt (fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ)))
    have hmn_real : (m : ℝ) = (n : ℝ) := by
      have h' := h
      simp only [subnormalValue, signValue, Bool.false_eq_true,
        ↓reduceIte, one_mul] at h'
      exact mul_right_cancel₀ hscale_ne h'
    exact_mod_cast hmn_real
  · intro h
    subst n
    rfl

theorem subnormalValue_true_eq_iff
    {fmt : FloatingPointFormat} {m n : ℕ}
    (hm : fmt.subnormalMantissa m) (hn : fmt.subnormalMantissa n) :
    fmt.subnormalValue true m = fmt.subnormalValue true n ↔ m = n := by
  constructor
  · intro h
    have hfalse :
        fmt.subnormalValue false m = fmt.subnormalValue false n := by
      have hmflip :
          fmt.subnormalValue true m =
            -fmt.subnormalValue false m := by
        simpa using fmt.subnormalValue_not_eq_neg false m
      have hnflip :
          fmt.subnormalValue true n =
            -fmt.subnormalValue false n := by
        simpa using fmt.subnormalValue_not_eq_neg false n
      rw [hmflip, hnflip] at h
      exact neg_inj.mp h
    exact (fmt.subnormalValue_false_eq_iff hm hn).1 hfalse
  · intro h
    subst n
    rfl

theorem subnormalValue_false_ne_true
    {fmt : FloatingPointFormat} {m n : ℕ}
    (hm : fmt.subnormalMantissa m) (hn : fmt.subnormalMantissa n) :
    fmt.subnormalValue false m ≠ fmt.subnormalValue true n := by
  intro h
  have hpos : 0 < fmt.subnormalValue true n := by
    simpa [h] using fmt.subnormalValue_false_pos hm
  exact (not_lt_of_ge (le_of_lt (fmt.subnormalValue_true_neg hn))) hpos

theorem subnormalValue_eq_sign_mantissa
    {fmt : FloatingPointFormat} {negative negative' : Bool}
    {m n : ℕ}
    (hm : fmt.subnormalMantissa m) (hn : fmt.subnormalMantissa n)
    (h :
      fmt.subnormalValue negative m =
        fmt.subnormalValue negative' n) :
    negative = negative' ∧ m = n := by
  cases negative <;> cases negative'
  · exact ⟨rfl, (fmt.subnormalValue_false_eq_iff hm hn).1 h⟩
  · exact False.elim ((fmt.subnormalValue_false_ne_true hm hn) h)
  · exact False.elim ((fmt.subnormalValue_false_ne_true hn hm) h.symm)
  · exact ⟨rfl, (fmt.subnormalValue_true_eq_iff hm hn).1 h⟩

theorem subnormalValue_eq_iff_sign_mantissa
    {fmt : FloatingPointFormat} {negative negative' : Bool}
    {m n : ℕ}
    (hm : fmt.subnormalMantissa m) (hn : fmt.subnormalMantissa n) :
    fmt.subnormalValue negative m =
        fmt.subnormalValue negative' n ↔
      negative = negative' ∧ m = n := by
  constructor
  · exact fmt.subnormalValue_eq_sign_mantissa hm hn
  · rintro ⟨rfl, rfl⟩
    rfl

theorem ieeeSingleFormat_normalizedExponentParameterCount :
    ieeeSingleFormat.normalizedExponentParameterCount = 254 := by
  norm_num [normalizedExponentParameterCount, ieeeSingleFormat]
  native_decide

theorem ieeeSingleFormat_normalizedMantissaParameterCount :
    ieeeSingleFormat.normalizedMantissaParameterCount = 8388608 := by
  norm_num [normalizedMantissaParameterCount, maxNormalMantissa,
    minNormalMantissa, ieeeSingleFormat]

theorem ieeeSingleFormat_subnormalMantissaParameterCount :
    ieeeSingleFormat.subnormalMantissaParameterCount = 8388607 := by
  norm_num [subnormalMantissaParameterCount, minNormalMantissa,
    ieeeSingleFormat]

/-- Problem 2.1 IEEE single normalized-number figure:
`2 * 254 * 2^23 = 4,261,412,864`. -/
theorem problem2_1_ieeeSingle_normalizedNumberParameterCount :
    ieeeSingleFormat.normalizedNumberParameterCount = 4261412864 := by
  norm_num [normalizedNumberParameterCount, signedParameterCount,
    normalizedExponentParameterCount, normalizedMantissaParameterCount,
    maxNormalMantissa, minNormalMantissa, ieeeSingleFormat]
  native_decide

/-- Problem 2.1 IEEE single subnormal-number figure:
`2 * (2^23 - 1) = 16,777,214`. -/
theorem problem2_1_ieeeSingle_subnormalNumberParameterCount :
    ieeeSingleFormat.subnormalNumberParameterCount = 16777214 := by
  norm_num [subnormalNumberParameterCount, signedParameterCount,
    subnormalMantissaParameterCount, minNormalMantissa, ieeeSingleFormat]

theorem ieeeDoubleFormat_normalizedExponentParameterCount :
    ieeeDoubleFormat.normalizedExponentParameterCount = 2046 := by
  norm_num [normalizedExponentParameterCount, ieeeDoubleFormat]
  native_decide

theorem ieeeDoubleFormat_normalizedMantissaParameterCount :
    ieeeDoubleFormat.normalizedMantissaParameterCount = 4503599627370496 := by
  norm_num [normalizedMantissaParameterCount, maxNormalMantissa,
    minNormalMantissa, ieeeDoubleFormat]

theorem ieeeDoubleFormat_subnormalMantissaParameterCount :
    ieeeDoubleFormat.subnormalMantissaParameterCount = 4503599627370495 := by
  norm_num [subnormalMantissaParameterCount, minNormalMantissa,
    ieeeDoubleFormat]

/-- Problem 2.1 IEEE double normalized-number figure:
`2 * 2046 * 2^52 = 18,428,729,675,200,069,632`. -/
theorem problem2_1_ieeeDouble_normalizedNumberParameterCount :
    ieeeDoubleFormat.normalizedNumberParameterCount =
      18428729675200069632 := by
  norm_num [normalizedNumberParameterCount, signedParameterCount,
    normalizedExponentParameterCount, normalizedMantissaParameterCount,
    maxNormalMantissa, minNormalMantissa, ieeeDoubleFormat]
  native_decide

/-- Problem 2.1 IEEE double subnormal-number figure:
`2 * (2^52 - 1) = 9,007,199,254,740,990`. -/
theorem problem2_1_ieeeDouble_subnormalNumberParameterCount :
    ieeeDoubleFormat.subnormalNumberParameterCount =
      9007199254740990 := by
  norm_num [subnormalNumberParameterCount, signedParameterCount,
    subnormalMantissaParameterCount, minNormalMantissa, ieeeDoubleFormat]

end FloatingPointFormat

end

end NumStability
