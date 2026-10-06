-- Analysis/BeneficialRounding.lean
--
-- Exact examples from Higham Chapter 1, Section 1.15.

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Continuity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Topology.Order.IntermediateValue
import NumStability.Analysis.FloatingPointArithmetic
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.PerturbationTheory
import NumStability.Algorithms.LU.LUSolve

namespace NumStability

open Filter

open scoped BigOperators
open scoped Topology

/-!
# Rounding Errors Can Be Beneficial

This file records the exact real-arithmetic part of the power-method example in
Higham §1.15. The matrix is singular and the displayed starting vector is a
zero-eigenvalue eigenvector, so exact arithmetic produces the zero vector in one
power-method step. The file also records the terminating-binary storage
obstruction, the concrete IEEE-double entrywise storage first step, and the
exact first-step perturbation substrate. It does not claim the subsequent
MATLAB iteration trace.
-/

/-- A real number with a terminating binary expansion: `z / 2^n`. -/
def BinaryTerminating (x : ℝ) : Prop :=
  ∃ z : ℤ, ∃ n : ℕ, x = z / (2 : ℝ) ^ n

/-- Every entry of a displayed real matrix has a terminating binary expansion. -/
def MatrixEntriesBinaryTerminating {m n : Type*} (A : m → n → ℝ) : Prop :=
  ∀ i j, BinaryTerminating (A i j)

/-- Every entry of a displayed real matrix belongs exactly to a finite
floating-point format. -/
def MatrixEntriesFiniteSystem {m n : Type*}
    (fmt : FloatingPointFormat) (A : m → n → ℝ) : Prop :=
  ∀ i j, FloatingPointFormat.finiteSystem fmt (A i j)

/-- No power of two is divisible by five. -/
theorem five_not_dvd_two_pow_nat (n : ℕ) : ¬ (5 : ℕ) ∣ 2 ^ n := by
  intro h
  have hp : Nat.Prime 5 := by decide
  have h52 : (5 : ℕ) ∣ 2 := hp.dvd_of_dvd_pow h
  norm_num at h52

/-- No power of two is divisible by three. -/
theorem three_not_dvd_two_pow_nat (n : ℕ) : ¬ (3 : ℕ) ∣ 2 ^ n := by
  intro h
  have hp : Nat.Prime 3 := by decide
  have h32 : (3 : ℕ) ∣ 2 := hp.dvd_of_dvd_pow h
  norm_num at h32

/-- No power of two is divisible by seven. -/
theorem seven_not_dvd_two_pow_nat (n : ℕ) : ¬ (7 : ℕ) ∣ 2 ^ n := by
  intro h
  have hp : Nat.Prime 7 := by decide
  have h72 : (7 : ℕ) ∣ 2 := hp.dvd_of_dvd_pow h
  norm_num at h72

/-- The source entry `1/5` is not a terminating binary fraction. -/
theorem one_fifth_not_binaryTerminating :
    ¬ BinaryTerminating (1 / 5 : ℝ) := by
  rintro ⟨z, n, h⟩
  have hpow_ne : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hmul : (2 : ℝ) ^ n = (5 : ℝ) * z := by
    field_simp [hpow_ne] at h
    linarith
  have hmul_int : (2 : ℤ) ^ n = 5 * z := by
    exact_mod_cast hmul
  have hdiv_int : (5 : ℤ) ∣ (2 : ℤ) ^ n := by
    exact ⟨z, hmul_int⟩
  have hdiv_nat : (5 : ℕ) ∣ 2 ^ n := by
    exact_mod_cast hdiv_int
  exact five_not_dvd_two_pow_nat n hdiv_nat

/-- The source input `2/3` is not a terminating binary fraction. -/
theorem two_thirds_not_binaryTerminating :
    ¬ BinaryTerminating (2 / 3 : ℝ) := by
  rintro ⟨z, n, h⟩
  have hpow_ne : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hmul : (2 : ℝ) * (2 : ℝ) ^ n = (3 : ℝ) * z := by
    field_simp [hpow_ne] at h
    linarith
  have hmul_int : (2 : ℤ) * (2 : ℤ) ^ n = 3 * z := by
    exact_mod_cast hmul
  have hpow_int : (2 : ℤ) ^ (n + 1) = 3 * z := by
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hmul_int
  have hdiv_int : (3 : ℤ) ∣ (2 : ℤ) ^ (n + 1) := by
    exact ⟨z, hpow_int⟩
  have hdiv_nat : (3 : ℕ) ∣ 2 ^ (n + 1) := by
    exact_mod_cast hdiv_int
  exact three_not_dvd_two_pow_nat (n + 1) hdiv_nat

/-- The source input `1/7` is not a terminating binary fraction. -/
theorem one_seventh_not_binaryTerminating :
    ¬ BinaryTerminating (1 / 7 : ℝ) := by
  rintro ⟨z, n, h⟩
  have hpow_ne : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hmul : (2 : ℝ) ^ n = (7 : ℝ) * z := by
    field_simp [hpow_ne] at h
    linarith
  have hmul_int : (2 : ℤ) ^ n = 7 * z := by
    exact_mod_cast hmul
  have hdiv_int : (7 : ℤ) ∣ (2 : ℤ) ^ n := by
    exact ⟨z, hmul_int⟩
  have hdiv_nat : (7 : ℕ) ∣ 2 ^ n := by
    exact_mod_cast hdiv_int
  exact seven_not_dvd_two_pow_nat n hdiv_nat

/-- For every positive power of ten, `1/10^m` is not a terminating binary
fraction.  This records the §1.11 observation that `1/n` has a nonterminating
binary expansion when `n` is a power of ten. -/
theorem one_div_ten_pow_succ_not_binaryTerminating (k : ℕ) :
    ¬ BinaryTerminating (1 / (10 : ℝ) ^ (k + 1)) := by
  rintro ⟨z, n, h⟩
  have hpow2_ne : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hpow10_ne : (10 : ℝ) ^ (k + 1) ≠ 0 := by positivity
  have hmul : (2 : ℝ) ^ n = (10 : ℝ) ^ (k + 1) * z := by
    field_simp [hpow2_ne, hpow10_ne] at h
    linarith
  have hmul_int : (2 : ℤ) ^ n = (10 : ℤ) ^ (k + 1) * z := by
    exact_mod_cast hmul
  have h10dvd : (10 : ℤ) ^ (k + 1) ∣ (2 : ℤ) ^ n := by
    exact ⟨z, hmul_int⟩
  have h5dvd10 : (5 : ℤ) ∣ (10 : ℤ) := by norm_num
  have hk1_ne : k + 1 ≠ 0 := by exact Nat.succ_ne_zero k
  have h5dvd10pow : (5 : ℤ) ∣ (10 : ℤ) ^ (k + 1) :=
    dvd_pow h5dvd10 hk1_ne
  have hdiv_int : (5 : ℤ) ∣ (2 : ℤ) ^ n :=
    dvd_trans h5dvd10pow h10dvd
  have hdiv_nat : (5 : ℕ) ∣ 2 ^ n := by
    exact_mod_cast hdiv_int
  exact five_not_dvd_two_pow_nat n hdiv_nat

/-- Every normalized IEEE-double finite value is a terminating binary fraction.
The fixed denominator `2^1074` is the least-positive-subnormal denominator. -/
theorem ieeeDoubleFormat_normalizedSystem_binaryTerminating
    {x : ℝ}
    (hx : FloatingPointFormat.normalizedSystem
      FloatingPointFormat.ieeeDoubleFormat x) :
    BinaryTerminating x := by
  rcases hx with ⟨negative, m, e, _hm, he, hx⟩
  have he' : -1021 ≤ e ∧ e ≤ 1024 := by
    simpa [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.exponentInRange] using he
  have hk_nonneg : 0 ≤ e + 1021 := by omega
  let k : ℕ := Int.toNat (e + 1021)
  let zAbs : ℤ := (m : ℤ) * (2 : ℤ) ^ k
  refine ⟨if negative then -zAbs else zAbs, 1074, ?_⟩
  rw [hx]
  subst k
  subst zAbs
  have htoNat : (((e + 1021).toNat : ℕ) : ℤ) = e + 1021 :=
    Int.toNat_of_nonneg hk_nonneg
  have hpow :
      (2 : ℝ) ^ (e - 53) =
        (2 : ℝ) ^ ((e + 1021).toNat : ℕ) * ((2 : ℝ) ^ 1074)⁻¹ := by
    have hsplit : e - 53 = (e + 1021) - (1074 : ℤ) := by ring
    rw [hsplit]
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have hnum :
        (2 : ℝ) ^ (e + 1021) =
          (2 : ℝ) ^ ((e + 1021).toNat : ℕ) := by
      rw [← htoNat]
      exact zpow_natCast (2 : ℝ) ((e + 1021).toNat)
    have hden :
        (2 : ℝ) ^ (1074 : ℤ) = (2 : ℝ) ^ (1074 : ℕ) := by
      simpa using (zpow_natCast (2 : ℝ) (1074 : ℕ))
    rw [hnum, hden]
    rw [div_eq_mul_inv]
  have hzAbs_cast :
      (((m : ℤ) * (2 : ℤ) ^ (e + 1021).toNat : ℤ) : ℝ) =
        (m : ℝ) * (2 : ℝ) ^ ((e + 1021).toNat : ℕ) := by
    norm_num [Int.cast_pow]
  cases negative
  · simp [FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.ieeeDoubleFormat, hpow,
      div_eq_mul_inv, hzAbs_cast, mul_assoc]
  · simp [FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.ieeeDoubleFormat, hpow,
      div_eq_mul_inv, hzAbs_cast, mul_assoc]

/-- Every normalized IEEE-single finite value is a terminating binary fraction.
The fixed denominator `2^149` is the least-positive-subnormal denominator. -/
theorem ieeeSingleFormat_normalizedSystem_binaryTerminating
    {x : ℝ}
    (hx : FloatingPointFormat.normalizedSystem
      FloatingPointFormat.ieeeSingleFormat x) :
    BinaryTerminating x := by
  rcases hx with ⟨negative, m, e, _hm, he, hx⟩
  have he' : -125 ≤ e ∧ e ≤ 128 := by
    simpa [FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange] using he
  have hk_nonneg : 0 ≤ e + 125 := by omega
  let k : ℕ := Int.toNat (e + 125)
  let zAbs : ℤ := (m : ℤ) * (2 : ℤ) ^ k
  refine ⟨if negative then -zAbs else zAbs, 149, ?_⟩
  rw [hx]
  subst k
  subst zAbs
  have htoNat : (((e + 125).toNat : ℕ) : ℤ) = e + 125 :=
    Int.toNat_of_nonneg hk_nonneg
  have hpow :
      (2 : ℝ) ^ (e - 24) =
        (2 : ℝ) ^ ((e + 125).toNat : ℕ) * ((2 : ℝ) ^ 149)⁻¹ := by
    have hsplit : e - 24 = (e + 125) - (149 : ℤ) := by ring
    rw [hsplit]
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have hnum :
        (2 : ℝ) ^ (e + 125) =
          (2 : ℝ) ^ ((e + 125).toNat : ℕ) := by
      rw [← htoNat]
      exact zpow_natCast (2 : ℝ) ((e + 125).toNat)
    have hden :
        (2 : ℝ) ^ (149 : ℤ) = (2 : ℝ) ^ (149 : ℕ) := by
      simpa using (zpow_natCast (2 : ℝ) (149 : ℕ))
    rw [hnum, hden]
    rw [div_eq_mul_inv]
  have hzAbs_cast :
      (((m : ℤ) * (2 : ℤ) ^ (e + 125).toNat : ℤ) : ℝ) =
        (m : ℝ) * (2 : ℝ) ^ ((e + 125).toNat : ℕ) := by
    norm_num [Int.cast_pow]
  cases negative
  · simp [FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.ieeeSingleFormat, hpow,
      div_eq_mul_inv, hzAbs_cast, mul_assoc]
  · simp [FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.ieeeSingleFormat, hpow,
      div_eq_mul_inv, hzAbs_cast, mul_assoc]

/-- Every subnormal IEEE-double finite value is a terminating binary fraction,
again with denominator `2^1074`. -/
theorem ieeeDoubleFormat_subnormalSystem_binaryTerminating
    {x : ℝ}
    (hx : FloatingPointFormat.subnormalSystem
      FloatingPointFormat.ieeeDoubleFormat x) :
    BinaryTerminating x := by
  rcases hx with ⟨negative, m, _hm, hx⟩
  let zAbs : ℤ := m
  refine ⟨if negative then -zAbs else zAbs, 1074, ?_⟩
  rw [hx]
  subst zAbs
  have hpow :
      (2 : ℝ) ^ (-1074 : ℤ) = ((2 : ℝ) ^ (1074 : ℕ))⁻¹ := by
    rw [zpow_neg]
    rw [show (1074 : ℤ) = ((1074 : ℕ) : ℤ) by norm_num]
    rw [zpow_natCast]
  cases negative
  · simp [FloatingPointFormat.subnormalValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.ieeeDoubleFormat, hpow,
      div_eq_mul_inv]
  · simp [FloatingPointFormat.subnormalValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.ieeeDoubleFormat, hpow,
      div_eq_mul_inv]

/-- Every subnormal IEEE-single finite value is a terminating binary fraction,
again with denominator `2^149`. -/
theorem ieeeSingleFormat_subnormalSystem_binaryTerminating
    {x : ℝ}
    (hx : FloatingPointFormat.subnormalSystem
      FloatingPointFormat.ieeeSingleFormat x) :
    BinaryTerminating x := by
  rcases hx with ⟨negative, m, _hm, hx⟩
  let zAbs : ℤ := m
  refine ⟨if negative then -zAbs else zAbs, 149, ?_⟩
  rw [hx]
  subst zAbs
  have hpow :
      (2 : ℝ) ^ (-149 : ℤ) = ((2 : ℝ) ^ (149 : ℕ))⁻¹ := by
    rw [zpow_neg]
    rw [show (149 : ℤ) = ((149 : ℕ) : ℤ) by norm_num]
    rw [zpow_natCast]
  cases negative
  · simp [FloatingPointFormat.subnormalValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.ieeeSingleFormat, hpow,
      div_eq_mul_inv]
  · simp [FloatingPointFormat.subnormalValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.ieeeSingleFormat, hpow,
      div_eq_mul_inv]

/-- Every finite IEEE-double value is a terminating binary fraction. -/
theorem ieeeDoubleFormat_finiteSystem_binaryTerminating
    {x : ℝ}
    (hx : FloatingPointFormat.finiteSystem
      FloatingPointFormat.ieeeDoubleFormat x) :
    BinaryTerminating x := by
  rcases hx with hx0 | hnorm | hsub
  · refine ⟨0, 0, ?_⟩
    simp [hx0]
  · exact ieeeDoubleFormat_normalizedSystem_binaryTerminating hnorm
  · exact ieeeDoubleFormat_subnormalSystem_binaryTerminating hsub

/-- Every finite IEEE-single value is a terminating binary fraction. -/
theorem ieeeSingleFormat_finiteSystem_binaryTerminating
    {x : ℝ}
    (hx : FloatingPointFormat.finiteSystem
      FloatingPointFormat.ieeeSingleFormat x) :
    BinaryTerminating x := by
  rcases hx with hx0 | hnorm | hsub
  · refine ⟨0, 0, ?_⟩
    simp [hx0]
  · exact ieeeSingleFormat_normalizedSystem_binaryTerminating hnorm
  · exact ieeeSingleFormat_subnormalSystem_binaryTerminating hsub

/-- The source entry `1/5` is not exactly an IEEE-double finite value. -/
theorem one_fifth_not_ieeeDoubleFiniteSystem :
    ¬ FloatingPointFormat.finiteSystem
      FloatingPointFormat.ieeeDoubleFormat (1 / 5 : ℝ) := by
  intro h
  exact one_fifth_not_binaryTerminating
    (ieeeDoubleFormat_finiteSystem_binaryTerminating h)

/-- The source input `2/3` is not exactly an IEEE-single finite value. -/
theorem two_thirds_not_ieeeSingleFiniteSystem :
    ¬ FloatingPointFormat.finiteSystem
      FloatingPointFormat.ieeeSingleFormat (2 / 3 : ℝ) := by
  intro h
  exact two_thirds_not_binaryTerminating
    (ieeeSingleFormat_finiteSystem_binaryTerminating h)

/-- The source input `1/7` is not exactly an IEEE-single finite value. -/
theorem one_seventh_not_ieeeSingleFiniteSystem :
    ¬ FloatingPointFormat.finiteSystem
      FloatingPointFormat.ieeeSingleFormat (1 / 7 : ℝ) := by
  intro h
  exact one_seventh_not_binaryTerminating
    (ieeeSingleFormat_finiteSystem_binaryTerminating h)

/-- The source input `2/3` is not exactly an IEEE-double finite value. -/
theorem two_thirds_not_ieeeDoubleFiniteSystem :
    ¬ FloatingPointFormat.finiteSystem
      FloatingPointFormat.ieeeDoubleFormat (2 / 3 : ℝ) := by
  intro h
  exact two_thirds_not_binaryTerminating
    (ieeeDoubleFormat_finiteSystem_binaryTerminating h)

/-- The source input `1/7` is not exactly an IEEE-double finite value. -/
theorem one_seventh_not_ieeeDoubleFiniteSystem :
    ¬ FloatingPointFormat.finiteSystem
      FloatingPointFormat.ieeeDoubleFormat (1 / 7 : ℝ) := by
  intro h
  exact one_seventh_not_binaryTerminating
    (ieeeDoubleFormat_finiteSystem_binaryTerminating h)

private theorem ieeeDoubleFormat_minNormalMagnitude_le_one_fifth :
    FloatingPointFormat.ieeeDoubleFormat.minNormalMagnitude ≤ (1 / 5 : ℝ) := by
  norm_num [FloatingPointFormat.ieeeDoubleFormat,
    FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR,
    zpow_neg]
  have hden : (5 : ℝ) ≤ (2 : ℝ) ^ 1022 := by
    have hsmall : (5 : ℝ) ≤ (2 : ℝ) ^ 3 := by norm_num
    have hmono : (2 : ℝ) ^ 3 ≤ (2 : ℝ) ^ 1022 :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (3 : ℕ) ≤ 1022)
    exact hsmall.trans hmono
  simpa [one_div] using
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 5) hden

private theorem ieeeDoubleFormat_minNormalMagnitude_le_one_tenth :
    FloatingPointFormat.ieeeDoubleFormat.minNormalMagnitude ≤ (1 / 10 : ℝ) := by
  norm_num [FloatingPointFormat.ieeeDoubleFormat,
    FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR,
    zpow_neg]
  have hden : (10 : ℝ) ≤ (2 : ℝ) ^ 1022 := by
    have hsmall : (10 : ℝ) ≤ (2 : ℝ) ^ 4 := by norm_num
    have hmono : (2 : ℝ) ^ 4 ≤ (2 : ℝ) ^ 1022 :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (4 : ℕ) ≤ 1022)
    exact hsmall.trans hmono
  simpa [one_div] using
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 10) hden

private theorem ieeeDoubleFormat_one_le_maxFiniteMagnitude :
    (1 : ℝ) ≤ FloatingPointFormat.ieeeDoubleFormat.maxFiniteMagnitude := by
  norm_num [FloatingPointFormat.ieeeDoubleFormat,
    FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR,
    zpow_neg]
  have hpow_ge_two : (2 : ℝ) ≤ (2 : ℝ) ^ 1024 := by
    have hmono : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ 1024 :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (1 : ℕ) ≤ 1024)
    simpa using hmono
  have hfirst : (1 : ℝ) ≤ (2 : ℝ) ^ 1024 * (1 / 2 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hpow_ge_two
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    norm_num at h
    exact h
  have hhalf : (1 / 2 : ℝ) ≤
      (9007199254740991 : ℝ) / 9007199254740992 := by norm_num
  exact hfirst.trans
    (mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ (2 : ℝ) ^ 1024))

/-- The source fraction `1/5` lies in the IEEE-double normal range. -/
theorem ieeeDoubleFormat_one_fifth_finiteNormalRange :
    FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange (1 / 5 : ℝ) := by
  rw [FloatingPointFormat.finiteNormalRange,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 5)]
  constructor
  · exact ieeeDoubleFormat_minNormalMagnitude_le_one_fifth
  · calc
      (1 / 5 : ℝ) ≤ 1 := by norm_num
      _ ≤ FloatingPointFormat.ieeeDoubleFormat.maxFiniteMagnitude :=
        ieeeDoubleFormat_one_le_maxFiniteMagnitude

/-- The source fraction `1/10` lies in the IEEE-double normal range. -/
theorem ieeeDoubleFormat_one_tenth_finiteNormalRange :
    FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange (1 / 10 : ℝ) := by
  rw [FloatingPointFormat.finiteNormalRange,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 10)]
  constructor
  · exact ieeeDoubleFormat_minNormalMagnitude_le_one_tenth
  · calc
      (1 / 10 : ℝ) ≤ 1 := by norm_num
      _ ≤ FloatingPointFormat.ieeeDoubleFormat.maxFiniteMagnitude :=
        ieeeDoubleFormat_one_le_maxFiniteMagnitude

/-- The source fraction `2/5` lies in the IEEE-double normal range. -/
theorem ieeeDoubleFormat_two_fifths_finiteNormalRange :
    FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange (2 / 5 : ℝ) := by
  rw [FloatingPointFormat.finiteNormalRange,
    abs_of_pos (by norm_num : (0 : ℝ) < 2 / 5)]
  constructor
  · exact ieeeDoubleFormat_minNormalMagnitude_le_one_fifth.trans
      (by norm_num : (1 / 5 : ℝ) ≤ 2 / 5)
  · calc
      (2 / 5 : ℝ) ≤ 1 := by norm_num
      _ ≤ FloatingPointFormat.ieeeDoubleFormat.maxFiniteMagnitude :=
        ieeeDoubleFormat_one_le_maxFiniteMagnitude

/-- The source fraction `3/10` lies in the IEEE-double normal range. -/
theorem ieeeDoubleFormat_three_tenths_finiteNormalRange :
    FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange (3 / 10 : ℝ) := by
  rw [FloatingPointFormat.finiteNormalRange,
    abs_of_pos (by norm_num : (0 : ℝ) < 3 / 10)]
  constructor
  · exact ieeeDoubleFormat_minNormalMagnitude_le_one_tenth.trans
      (by norm_num : (1 / 10 : ℝ) ≤ 3 / 10)
  · calc
      (3 / 10 : ℝ) ≤ 1 := by norm_num
      _ ≤ FloatingPointFormat.ieeeDoubleFormat.maxFiniteMagnitude :=
        ieeeDoubleFormat_one_le_maxFiniteMagnitude

/-- The source fraction `3/5` lies in the IEEE-double normal range. -/
theorem ieeeDoubleFormat_three_fifths_finiteNormalRange :
    FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange (3 / 5 : ℝ) := by
  rw [FloatingPointFormat.finiteNormalRange,
    abs_of_pos (by norm_num : (0 : ℝ) < 3 / 5)]
  constructor
  · exact ieeeDoubleFormat_minNormalMagnitude_le_one_fifth.trans
      (by norm_num : (1 / 5 : ℝ) ≤ 3 / 5)
  · calc
      (3 / 5 : ℝ) ≤ 1 := by norm_num
      _ ≤ FloatingPointFormat.ieeeDoubleFormat.maxFiniteMagnitude :=
        ieeeDoubleFormat_one_le_maxFiniteMagnitude

/-- The source fraction `7/10` lies in the IEEE-double normal range. -/
theorem ieeeDoubleFormat_seven_tenths_finiteNormalRange :
    FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange (7 / 10 : ℝ) := by
  rw [FloatingPointFormat.finiteNormalRange,
    abs_of_pos (by norm_num : (0 : ℝ) < 7 / 10)]
  constructor
  · exact ieeeDoubleFormat_minNormalMagnitude_le_one_tenth.trans
      (by norm_num : (1 / 10 : ℝ) ≤ 7 / 10)
  · calc
      (7 / 10 : ℝ) ≤ 1 := by norm_num
      _ ≤ FloatingPointFormat.ieeeDoubleFormat.maxFiniteMagnitude :=
        ieeeDoubleFormat_one_le_maxFiniteMagnitude

/-- IEEE-double round-to-even sends `1/5` to its upper adjacent normal value. -/
theorem ieeeDoubleFormat_one_fifth_rounds_to :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (1 / 5 : ℝ) =
      (7205759403792794 : ℝ) * (2 : ℝ) ^ (-55 : ℤ) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false 7205759403792793 (-2 : ℤ)
  let b : ℝ := fmt.normalizedValue false 7205759403792794 (-2 : ℤ)
  let x : ℝ := (1 / 5 : ℝ)
  have hm : fmt.normalizedMantissa 7205759403792793 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (7205759403792793 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 7205759403792793, (-2 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, rfl⟩⟩
  have ha_value :
      a = (7205759403792793 : ℝ) * (2 : ℝ) ^ (-55 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hb_value :
      b = (7205759403792794 : ℝ) * (2 : ℝ) ^ (-55 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      ieeeDoubleFormat_one_fifth_finiteNormalRange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  simpa [x, fmt, hb_value] using hround

/-- IEEE-double round-to-even sends `1/10` to its upper adjacent normal value. -/
theorem ieeeDoubleFormat_one_tenth_rounds_to :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (1 / 10 : ℝ) =
      (7205759403792794 : ℝ) * (2 : ℝ) ^ (-56 : ℤ) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false 7205759403792793 (-3 : ℤ)
  let b : ℝ := fmt.normalizedValue false 7205759403792794 (-3 : ℤ)
  let x : ℝ := (1 / 10 : ℝ)
  have hm : fmt.normalizedMantissa 7205759403792793 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (7205759403792793 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 7205759403792793, (-3 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, rfl⟩⟩
  have ha_value :
      a = (7205759403792793 : ℝ) * (2 : ℝ) ^ (-56 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hb_value :
      b = (7205759403792794 : ℝ) * (2 : ℝ) ^ (-56 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      ieeeDoubleFormat_one_tenth_finiteNormalRange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  simpa [x, fmt, hb_value] using hround

/-- IEEE-double round-to-even sends `2/5` to its upper adjacent normal value. -/
theorem ieeeDoubleFormat_two_fifths_rounds_to :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (2 / 5 : ℝ) =
      (7205759403792794 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false 7205759403792793 (-1 : ℤ)
  let b : ℝ := fmt.normalizedValue false 7205759403792794 (-1 : ℤ)
  let x : ℝ := (2 / 5 : ℝ)
  have hm : fmt.normalizedMantissa 7205759403792793 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (7205759403792793 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 7205759403792793, (-1 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, rfl⟩⟩
  have ha_value :
      a = (7205759403792793 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hb_value :
      b = (7205759403792794 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      ieeeDoubleFormat_two_fifths_finiteNormalRange
  have hrightCloser : |x - b| < |x - a| := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  simpa [x, fmt, hb_value] using hround

/-- IEEE-double round-to-even sends `3/10` to its lower adjacent normal value. -/
theorem ieeeDoubleFormat_three_tenths_rounds_to :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (3 / 10 : ℝ) =
      (5404319552844595 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false 5404319552844595 (-1 : ℤ)
  let b : ℝ := fmt.normalizedValue false 5404319552844596 (-1 : ℤ)
  let x : ℝ := (3 / 10 : ℝ)
  have hm : fmt.normalizedMantissa 5404319552844595 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (5404319552844595 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 5404319552844595, (-1 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, rfl⟩⟩
  have ha_value :
      a = (5404319552844595 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hb_value :
      b = (5404319552844596 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      ieeeDoubleFormat_three_tenths_finiteNormalRange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [x, fmt, ha_value] using hround

/-- IEEE-double round-to-even sends `3/5` to its lower adjacent normal value. -/
theorem ieeeDoubleFormat_three_fifths_rounds_to :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (3 / 5 : ℝ) =
      (5404319552844595 : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false 5404319552844595 (0 : ℤ)
  let b : ℝ := fmt.normalizedValue false 5404319552844596 (0 : ℤ)
  let x : ℝ := (3 / 5 : ℝ)
  have hm : fmt.normalizedMantissa 5404319552844595 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (5404319552844595 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 5404319552844595, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, rfl⟩⟩
  have ha_value :
      a = (5404319552844595 : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hb_value :
      b = (5404319552844596 : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      ieeeDoubleFormat_three_fifths_finiteNormalRange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [x, fmt, ha_value] using hround

/-- IEEE-double round-to-even sends `7/10` to its lower adjacent normal value. -/
theorem ieeeDoubleFormat_seven_tenths_rounds_to :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (7 / 10 : ℝ) =
      (6305039478318694 : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false 6305039478318694 (0 : ℤ)
  let b : ℝ := fmt.normalizedValue false 6305039478318695 (0 : ℤ)
  let x : ℝ := (7 / 10 : ℝ)
  have hm : fmt.normalizedMantissa 6305039478318694 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (6305039478318694 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 6305039478318694, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, rfl⟩⟩
  have ha_value :
      a = (6305039478318694 : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hb_value :
      b = (6305039478318695 : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      ieeeDoubleFormat_seven_tenths_finiteNormalRange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [x, fmt, ha_value] using hround

/-- IEEE-double round-to-even is symmetric on the source fraction `1/10`. -/
theorem ieeeDoubleFormat_neg_one_tenth_rounds_to :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (-1 / 10 : ℝ) =
      -((7205759403792794 : ℝ) * (2 : ℝ) ^ (-56 : ℤ)) := by
  have hneg :=
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven_neg_of_finiteNormalRange
      (by norm_num [FloatingPointFormat.evenMantissa,
        FloatingPointFormat.ieeeDoubleFormat])
      (by norm_num [FloatingPointFormat.ieeeDoubleFormat])
      ieeeDoubleFormat_one_tenth_finiteNormalRange
  have hround := ieeeDoubleFormat_one_tenth_rounds_to
  rw [show (-1 / 10 : ℝ) = -(1 / 10 : ℝ) by norm_num]
  rw [hneg, hround]

/-- IEEE-double round-to-even is symmetric on the source fraction `2/5`. -/
theorem ieeeDoubleFormat_neg_two_fifths_rounds_to :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (-2 / 5 : ℝ) =
      -((7205759403792794 : ℝ) * (2 : ℝ) ^ (-54 : ℤ)) := by
  have hneg :=
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven_neg_of_finiteNormalRange
      (by norm_num [FloatingPointFormat.evenMantissa,
        FloatingPointFormat.ieeeDoubleFormat])
      (by norm_num [FloatingPointFormat.ieeeDoubleFormat])
      ieeeDoubleFormat_two_fifths_finiteNormalRange
  have hround := ieeeDoubleFormat_two_fifths_rounds_to
  rw [show (-2 / 5 : ℝ) = -(2 / 5 : ℝ) by norm_num]
  rw [hneg, hround]

/-- IEEE-double round-to-even is symmetric on the source fraction `3/10`. -/
theorem ieeeDoubleFormat_neg_three_tenths_rounds_to :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (-3 / 10 : ℝ) =
      -((5404319552844595 : ℝ) * (2 : ℝ) ^ (-54 : ℤ)) := by
  have hneg :=
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven_neg_of_finiteNormalRange
      (by norm_num [FloatingPointFormat.evenMantissa,
        FloatingPointFormat.ieeeDoubleFormat])
      (by norm_num [FloatingPointFormat.ieeeDoubleFormat])
      ieeeDoubleFormat_three_tenths_finiteNormalRange
  have hround := ieeeDoubleFormat_three_tenths_rounds_to
  rw [show (-3 / 10 : ℝ) = -(3 / 10 : ℝ) by norm_num]
  rw [hneg, hround]

/-- The source fraction `1/2` is an exact IEEE-double finite value. -/
theorem ieeeDoubleFormat_one_half_finiteSystem :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem (1 / 2 : ℝ) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  have hm : fmt.normalizedMantissa 4503599627370496 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (0 : ℤ) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.exponentInRange]
  have hval :
      fmt.normalizedValue false 4503599627370496 (0 : ℤ) = (1 / 2 : ℝ) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hfin : fmt.finiteSystem
      (fmt.normalizedValue false 4503599627370496 (0 : ℤ)) :=
    Or.inr (Or.inl ⟨false, 4503599627370496, (0 : ℤ), hm, he, rfl⟩)
  simpa [fmt, hval] using hfin

/-- IEEE-double round-to-even fixes the exactly representable source fraction
`1/2`. -/
theorem ieeeDoubleFormat_one_half_rounds_to :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (1 / 2 : ℝ) =
      (1 / 2 : ℝ) := by
  exact
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven_eq_self_of_finiteSystem
      ieeeDoubleFormat_one_half_finiteSystem

/-- The tiny dyadic `2^-54` is an exact IEEE-double finite value. -/
theorem ieeeDoubleFormat_two_pow_neg54_finiteSystem :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem
      ((1 : ℝ) / (2 : ℝ) ^ 54) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  have hm : fmt.normalizedMantissa 4503599627370496 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (-53 : ℤ) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.exponentInRange]
  have hval :
      fmt.normalizedValue false 4503599627370496 (-53 : ℤ) =
        ((1 : ℝ) / (2 : ℝ) ^ 54) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hfin : fmt.finiteSystem
      (fmt.normalizedValue false 4503599627370496 (-53 : ℤ)) :=
    Or.inr (Or.inl ⟨false, 4503599627370496, (-53 : ℤ), hm, he, rfl⟩)
  simpa [fmt, hval] using hfin

/-- The tiny dyadic `2^-55` is an exact IEEE-double finite value. -/
theorem ieeeDoubleFormat_two_pow_neg55_finiteSystem :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem
      ((1 : ℝ) / (2 : ℝ) ^ 55) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  have hm : fmt.normalizedMantissa 4503599627370496 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (-54 : ℤ) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.exponentInRange]
  have hval :
      fmt.normalizedValue false 4503599627370496 (-54 : ℤ) =
        ((1 : ℝ) / (2 : ℝ) ^ 55) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  have hfin : fmt.finiteSystem
      (fmt.normalizedValue false 4503599627370496 (-54 : ℤ)) :=
    Or.inr (Or.inl ⟨false, 4503599627370496, (-54 : ℤ), hm, he, rfl⟩)
  simpa [fmt, hval] using hfin

/-- At the lower edge of the binade containing `1/2`, the value
`1/2 + 2^-55` is still closer to `1/2` than to the next IEEE-double value. -/
theorem ieeeDoubleFormat_half_plus_two_pow_neg55_rounds_to_half :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven
        ((1 : ℝ) / 2 + (2 : ℝ) ^ (-55 : ℤ)) =
      (1 / 2 : ℝ) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false fmt.minNormalMantissa 0
  let b : ℝ := fmt.normalizedValue false (fmt.minNormalMantissa + 1) 0
  let x : ℝ := (1 : ℝ) / 2 + (2 : ℝ) ^ (-55 : ℤ)
  have hm : fmt.normalizedMantissa fmt.minNormalMantissa :=
    fmt.minNormalMantissa_normalized
  have hmnext : fmt.normalizedMantissa (fmt.minNormalMantissa + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, fmt.minNormalMantissa, (0 : ℤ), hm, hmnext,
        Or.inl ⟨rfl, rfl⟩⟩
  have ha_value : a = (1 / 2 : ℝ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.minNormalMantissa,
      zpow_neg]
  have hb_value : b = (1 / 2 : ℝ) + (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.minNormalMantissa,
      zpow_neg]
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by norm_num [x, zpow_neg]
    rw [abs_of_nonneg hxnonneg]
    constructor
    · exact le_trans ieeeDoubleFormat_minNormalMagnitude_le_one_tenth
        (by norm_num [x, zpow_neg] : (1 / 10 : ℝ) ≤ x)
    · exact le_trans (by norm_num [x, zpow_neg] : x ≤ (1 : ℝ))
        ieeeDoubleFormat_one_le_maxFiniteMagnitude
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  simpa [x, fmt, ha_value] using hround

/-- Signed companion of
`ieeeDoubleFormat_half_plus_two_pow_neg55_rounds_to_half`. -/
theorem ieeeDoubleFormat_neg_half_plus_two_pow_neg55_rounds_to_neg_half :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven
        (-((1 : ℝ) / 2 + (2 : ℝ) ^ (-55 : ℤ))) =
      -(1 / 2 : ℝ) := by
  rw [FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven_neg]
  · rw [ieeeDoubleFormat_half_plus_two_pow_neg55_rounds_to_half]
  · norm_num [FloatingPointFormat.evenMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat]

/-- IEEE-double round-to-even is symmetric on the source fraction `3/5`. -/
theorem ieeeDoubleFormat_neg_three_fifths_rounds_to :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (-3 / 5 : ℝ) =
      -((5404319552844595 : ℝ) * (2 : ℝ) ^ (-53 : ℤ)) := by
  have hneg :=
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven_neg_of_finiteNormalRange
      (by norm_num [FloatingPointFormat.evenMantissa,
        FloatingPointFormat.ieeeDoubleFormat])
      (by norm_num [FloatingPointFormat.ieeeDoubleFormat])
      ieeeDoubleFormat_three_fifths_finiteNormalRange
  have hround := ieeeDoubleFormat_three_fifths_rounds_to
  rw [show (-3 / 5 : ℝ) = -(3 / 5 : ℝ) by norm_num]
  rw [hneg, hround]

/-- One unnormalized power-method step, `x := A*x`. -/
noncomputable def powerMethodStep (n : ℕ) (A : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  matMulVec n A x

/-- `k` unnormalized power-method steps, starting from `x`. -/
noncomputable def powerMethodIterate (n : ℕ) (A : Fin n → Fin n → ℝ) :
    ℕ → (Fin n → ℝ) → (Fin n → ℝ)
  | 0, x => x
  | k + 1, x => powerMethodStep n A (powerMethodIterate n A k x)

/-- A nonzero right-eigenvector/eigenvalue relation for legacy square matrices. -/
def IsRightEigenpair (n : ℕ) (A : Fin n → Fin n → ℝ)
    (lambda : ℝ) (x : Fin n → ℝ) : Prop :=
  (∃ i : Fin n, x i ≠ 0) ∧
    ∀ i : Fin n, matMulVec n A x i = lambda * x i

/-- The shifted matrix `A - mu I` used in inverse iteration. -/
noncomputable def inverseIterationShiftedMatrix (n : ℕ)
    (A : Fin n → Fin n → ℝ) (mu : ℝ) : Fin n → Fin n → ℝ :=
  fun i j => A i j - mu * idMatrix n i j

/-- The shifted linear solve `(A - mu I) y = x` used to apply the shifted
inverse without explicitly forming it. -/
def SolvesInverseIterationShiftedSystem (n : ℕ)
    (A : Fin n → Fin n → ℝ) (mu : ℝ)
    (x y : Fin n → ℝ) : Prop :=
  matMulVec n (inverseIterationShiftedMatrix n A mu) y = x

/-- Rank-one backward-error perturbation for the inverse-iteration shifted
system.  For an approximate solve output `yhat`, this is the Higham Lemma 1.1
rank-one perturbation applied to `(A - mu I)y = rhs`. -/
noncomputable def inverseIterationShiftedRankOneBackwardError (n : ℕ)
    (A : Fin n → Fin n → ℝ) (mu : ℝ)
    (rhs yhat : Fin n → ℝ) : Fin n → Fin n → ℝ :=
  residualRankOnePerturbation n
    (residualVec n (inverseIterationShiftedMatrix n A mu) yhat rhs) yhat

/-- The shifted rank-one backward error makes an approximate inverse-iteration
output an exact solution of a perturbed shifted system. -/
theorem inverseIterationShiftedRankOneBackwardError_solves
    (n : ℕ) (A : Fin n → Fin n → ℝ) (mu : ℝ)
    (rhs yhat : Fin n → ℝ) (hyhat : vecNorm2 yhat ≠ 0) :
    ∀ i : Fin n,
      ∑ j : Fin n,
        (inverseIterationShiftedMatrix n A mu i j +
            inverseIterationShiftedRankOneBackwardError n A mu rhs yhat i j) *
          yhat j =
        rhs i := by
  simpa [inverseIterationShiftedRankOneBackwardError] using
    residualRankOnePerturbation_solves n
      (inverseIterationShiftedMatrix n A mu) yhat rhs hyhat

/-- Operator-norm certificate for the shifted rank-one backward error. -/
theorem inverseIterationShiftedRankOneBackwardError_opNorm2Le
    (n : ℕ) (A : Fin n → Fin n → ℝ) (mu : ℝ)
    (rhs yhat : Fin n → ℝ) (hyhat : vecNorm2 yhat ≠ 0) :
    opNorm2Le (inverseIterationShiftedRankOneBackwardError n A mu rhs yhat)
      (vecNorm2 (residualVec n (inverseIterationShiftedMatrix n A mu) yhat rhs) /
        vecNorm2 yhat) := by
  simpa [inverseIterationShiftedRankOneBackwardError] using
    opNorm2Le_residualRankOnePerturbation n
      (residualVec n (inverseIterationShiftedMatrix n A mu) yhat rhs) yhat
      hyhat

/-- Source-facing operator-norm certificate for the shifted rank-one backward
error.  If a concrete shifted solver proves the usual relative residual bound
`||rhs - (A - mu I)yhat||_2 <= rho * ||yhat||_2`, then the canonical rank-one
perturbation has operator 2-norm at most `rho`. -/
theorem inverseIterationShiftedRankOneBackwardError_opNorm2Le_of_residual_norm_le
    (n : ℕ) (A : Fin n → Fin n → ℝ) (mu : ℝ)
    (rhs yhat : Fin n → ℝ) (rho : ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hres :
      vecNorm2 (residualVec n (inverseIterationShiftedMatrix n A mu) yhat rhs) ≤
        rho * vecNorm2 yhat) :
    opNorm2Le (inverseIterationShiftedRankOneBackwardError n A mu rhs yhat)
      rho := by
  have hypos : 0 < vecNorm2 yhat :=
    lt_of_le_of_ne (vecNorm2_nonneg yhat) (Ne.symm hyhat)
  have hquot :
      vecNorm2 (residualVec n (inverseIterationShiftedMatrix n A mu) yhat rhs) /
          vecNorm2 yhat ≤
        rho := by
    rw [div_le_iff₀ hypos]
    simpa [mul_comm] using hres
  intro x
  exact
    le_trans
      (inverseIterationShiftedRankOneBackwardError_opNorm2Le n A mu rhs yhat
        hyhat x)
      (mul_le_mul_of_nonneg_right hquot (vecNorm2_nonneg x))

/-- The action of the shifted rank-one backward error on the approximate solve
output is exactly the shifted-system residual. -/
theorem inverseIterationShiftedRankOneBackwardError_mul_yhat_eq_residual
    (n : ℕ) (A : Fin n → Fin n → ℝ) (mu : ℝ)
    (rhs yhat : Fin n → ℝ) (hyhat : vecNorm2 yhat ≠ 0) :
    matMulVec n (inverseIterationShiftedRankOneBackwardError n A mu rhs yhat)
        yhat =
      residualVec n (inverseIterationShiftedMatrix n A mu) yhat rhs := by
  simpa [inverseIterationShiftedRankOneBackwardError] using
    residualRankOnePerturbation_mul_vec n
      (residualVec n (inverseIterationShiftedMatrix n A mu) yhat rhs) yhat
      hyhat

/-- The target coefficient used by the rank-one inverse-iteration wrappers can
be stated directly in terms of the shifted residual.  This avoids requiring a
future solver/source theorem to mention the internal rank-one perturbation when
it supplies target-direction evidence. -/
theorem inverseIterationShiftedRankOneBackwardError_targetCoeff_eq_neg_residualCoeff
    (n : ℕ) (A V_inv : Fin n → Fin n → ℝ) (mu : ℝ)
    (rhs yhat : Fin n → ℝ) (target : Fin n)
    (hyhat : vecNorm2 yhat ≠ 0) :
    matMulVec n V_inv
        (fun i : Fin n =>
          -matMulVec n
            (inverseIterationShiftedRankOneBackwardError n A mu rhs yhat)
            yhat i) target =
      matMulVec n V_inv
        (fun i : Fin n =>
          -residualVec n (inverseIterationShiftedMatrix n A mu) yhat rhs i)
        target := by
  have hmul :=
    inverseIterationShiftedRankOneBackwardError_mul_yhat_eq_residual
      n A mu rhs yhat hyhat
  exact congrArg (fun z : Fin n → ℝ => matMulVec n V_inv (fun i => -z i) target)
    hmul

/-- Nonzero target-direction evidence for the rank-one inverse-iteration route
is equivalent to the same evidence stated for the actual shifted residual. -/
theorem inverseIterationShiftedRankOneBackwardError_targetCoeff_ne_iff_neg_residualCoeff_ne
    (n : ℕ) (A V_inv : Fin n → Fin n → ℝ) (mu : ℝ)
    (rhs yhat : Fin n → ℝ) (target : Fin n)
    (hyhat : vecNorm2 yhat ≠ 0) :
    (matMulVec n V_inv
        (fun i : Fin n =>
          -matMulVec n
            (inverseIterationShiftedRankOneBackwardError n A mu rhs yhat)
            yhat i) target ≠ 0) ↔
      (matMulVec n V_inv
        (fun i : Fin n =>
          -residualVec n (inverseIterationShiftedMatrix n A mu) yhat rhs i)
        target ≠ 0) := by
  rw [inverseIterationShiftedRankOneBackwardError_targetCoeff_eq_neg_residualCoeff
    n A V_inv mu rhs yhat target hyhat]

/-- Existence form of the shifted-system rank-one backward-error certificate.
This closes the local `DeltaS`/operator-norm part of the inverse-iteration
solver-certificate obligation; separation and target-coefficient facts remain
separate source/solver hypotheses. -/
theorem inverseIterationShiftedRankOneBackwardError_exists_certificate
    (n : ℕ) (A : Fin n → Fin n → ℝ) (mu : ℝ)
    (rhs yhat : Fin n → ℝ) (hyhat : vecNorm2 yhat ≠ 0) :
    ∃ DeltaS : Fin n → Fin n → ℝ,
      (∀ i : Fin n,
        ∑ j : Fin n,
          (inverseIterationShiftedMatrix n A mu i j + DeltaS i j) *
            yhat j =
          rhs i) ∧
      opNorm2Le DeltaS
        (vecNorm2
            (residualVec n (inverseIterationShiftedMatrix n A mu) yhat rhs) /
          vecNorm2 yhat) := by
  refine
    ⟨inverseIterationShiftedRankOneBackwardError n A mu rhs yhat, ?_, ?_⟩
  · exact inverseIterationShiftedRankOneBackwardError_solves n A mu rhs yhat hyhat
  · exact inverseIterationShiftedRankOneBackwardError_opNorm2Le n A mu rhs yhat hyhat

/-- Existence form of the source-facing relative-residual certificate.  This is
the rank-one shifted-system bridge a future rounded solver can consume after it
has proved a visible residual bound with constant `rho`. -/
theorem inverseIterationShiftedRankOneBackwardError_exists_certificate_of_residual_norm_le
    (n : ℕ) (A : Fin n → Fin n → ℝ) (mu : ℝ)
    (rhs yhat : Fin n → ℝ) (rho : ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hres :
      vecNorm2 (residualVec n (inverseIterationShiftedMatrix n A mu) yhat rhs) ≤
        rho * vecNorm2 yhat) :
    ∃ DeltaS : Fin n → Fin n → ℝ,
      (∀ i : Fin n,
        ∑ j : Fin n,
          (inverseIterationShiftedMatrix n A mu i j + DeltaS i j) *
            yhat j =
          rhs i) ∧
      opNorm2Le DeltaS rho := by
  refine
    ⟨inverseIterationShiftedRankOneBackwardError n A mu rhs yhat, ?_, ?_⟩
  · exact inverseIterationShiftedRankOneBackwardError_solves n A mu rhs yhat hyhat
  · exact
      inverseIterationShiftedRankOneBackwardError_opNorm2Le_of_residual_norm_le
        n A mu rhs yhat rho hyhat hres

/-- Multiplying by the shifted matrix subtracts `mu*x` from `A*x`. -/
theorem inverseIterationShiftedMatrix_mulVec (n : ℕ)
    (A : Fin n → Fin n → ℝ) (mu : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    matMulVec n (inverseIterationShiftedMatrix n A mu) x i =
      matMulVec n A x i - mu * x i := by
  unfold matMulVec inverseIterationShiftedMatrix
  have hscale :
      (∑ j : Fin n, (mu * idMatrix n i j) * x j) = mu * x i := by
    calc
      (∑ j : Fin n, (mu * idMatrix n i j) * x j)
          = mu * (∑ j : Fin n, idMatrix n i j * x j) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = mu * x i := by
          have hid := congrFun (idMatrix_mulVec n x) i
          simp [hid]
  calc
    (∑ j : Fin n, (A i j - mu * idMatrix n i j) * x j)
        = (∑ j : Fin n, A i j * x j) -
            (∑ j : Fin n, (mu * idMatrix n i j) * x j) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = (∑ j : Fin n, A i j * x j) - mu * x i := by
          rw [hscale]

/-- If `x` is an eigenvector of `A`, then `A - mu I` maps it to
`(lambda - mu) x`. -/
theorem inverseIteration_shiftedMatrix_mul_eigenvector
    {n : ℕ} {A : Fin n → Fin n → ℝ} {lambda mu : ℝ}
    {x : Fin n → ℝ} (hx : IsRightEigenpair n A lambda x) (i : Fin n) :
    matMulVec n (inverseIterationShiftedMatrix n A mu) x i =
      (lambda - mu) * x i := by
  rw [inverseIterationShiftedMatrix_mulVec]
  rw [hx.2 i]
  ring

/-- On an eigenvector direction, the inverse-iteration shifted solve has the
exact solution `(lambda - mu)^{-1} x`. -/
theorem inverseIteration_shiftedSystem_solution_on_eigenvector
    {n : ℕ} {A : Fin n → Fin n → ℝ} {lambda mu : ℝ}
    {x : Fin n → ℝ} (hx : IsRightEigenpair n A lambda x)
    (hshift : lambda - mu ≠ 0) :
    SolvesInverseIterationShiftedSystem n A mu x
      (fun i => (lambda - mu)⁻¹ * x i) := by
  unfold SolvesInverseIterationShiftedSystem
  ext i
  calc
    matMulVec n (inverseIterationShiftedMatrix n A mu)
        (fun i => (lambda - mu)⁻¹ * x i) i
        = (lambda - mu)⁻¹ *
            matMulVec n (inverseIterationShiftedMatrix n A mu) x i := by
            unfold matMulVec
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = (lambda - mu)⁻¹ * ((lambda - mu) * x i) := by
          rw [inverseIteration_shiftedMatrix_mul_eigenvector hx i]
    _ = x i := by
          rw [← mul_assoc, inv_mul_cancel₀ hshift, one_mul]

/-- If `B` is a left inverse for `A - mu I`, then applying the shifted inverse
to an eigenvector scales that eigenvector by `(lambda - mu)^{-1}`. -/
theorem inverseIteration_shiftedInverse_mul_eigenvector_of_leftInverse
    {n : ℕ} {A B : Fin n → Fin n → ℝ} {lambda mu : ℝ}
    {x : Fin n → ℝ} (hx : IsRightEigenpair n A lambda x)
    (hshift : lambda - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B) :
    matMulVec n B x = fun i => (lambda - mu)⁻¹ * x i := by
  let y : Fin n → ℝ := fun i => (lambda - mu)⁻¹ * x i
  have hsolve :
      matMulVec n (inverseIterationShiftedMatrix n A mu) y = x := by
    simpa [y] using inverseIteration_shiftedSystem_solution_on_eigenvector hx hshift
  have hmat :
      matMul n B (inverseIterationShiftedMatrix n A mu) = idMatrix n := by
    ext i j
    exact hB i j
  ext i
  calc
    matMulVec n B x i
        = matMulVec n B
            (matMulVec n (inverseIterationShiftedMatrix n A mu) y) i := by
            rw [hsolve]
    _ = matMulVec n
          (matMul n B (inverseIterationShiftedMatrix n A mu)) y i := by
          rw [matMulVec_matMul]
    _ = y i := by
          rw [hmat, matMulVec_id]
    _ = (lambda - mu)⁻¹ * x i := rfl

/-- The scalar amplification in inverse iteration is the reciprocal of the
distance from the shift to the eigenvalue. -/
theorem inverseIteration_shiftedInverse_amplification_abs_eq
    (lambda mu : ℝ) :
    |(lambda - mu)⁻¹| = (|lambda - mu|)⁻¹ := by
  rw [abs_inv]

/-- A shift closer to an eigenvalue gives a larger exact inverse-iteration
scalar amplification. -/
theorem inverseIteration_shiftedInverse_amplification_strict_of_abs_shift_lt
    {lambda muClose muFar : ℝ}
    (hclose_pos : 0 < |lambda - muClose|)
    (hclose_far : |lambda - muClose| < |lambda - muFar|) :
    |(lambda - muFar)⁻¹| < |(lambda - muClose)⁻¹| := by
  rw [abs_inv, abs_inv]
  simpa [one_div] using
    one_div_lt_one_div_of_lt hclose_pos hclose_far

/-- Source-facing scalar separation adapter for inverse iteration.  If the
shift is within `radius` of the target eigenvalue and the other eigenvalue is
at least `sep + radius` away from the target eigenvalue, then the other
eigenvalue is at least `sep` away from the shift. -/
theorem inverseIteration_nonTarget_shift_gap_of_eigenvalue_gap_and_target_radius
    {lambdaTarget lambdaOther mu radius sep : ℝ}
    (htarget : |lambdaTarget - mu| ≤ radius)
    (hgap : sep + radius ≤ |lambdaOther - lambdaTarget|) :
    sep ≤ |lambdaOther - mu| := by
  have htri :
      |lambdaOther - lambdaTarget| ≤
        |lambdaOther - mu| + |lambdaTarget - mu| := by
    calc
      |lambdaOther - lambdaTarget|
          = |(lambdaOther - mu) + (mu - lambdaTarget)| := by
              congr 1
              ring
      _ ≤ |lambdaOther - mu| + |mu - lambdaTarget| :=
            abs_add_le (lambdaOther - mu) (mu - lambdaTarget)
      _ = |lambdaOther - mu| + |lambdaTarget - mu| := by
            rw [abs_sub_comm mu lambdaTarget]
  have hgap_to_shift :
      sep + radius ≤ |lambdaOther - mu| + |lambdaTarget - mu| :=
    hgap.trans htri
  linarith

/-- Finite-family version of
`inverseIteration_nonTarget_shift_gap_of_eigenvalue_gap_and_target_radius`.
It turns an eigenvalue-separation condition around the target eigenvalue into
the uniform non-target shift-distance hypothesis consumed by the residual/gap
inverse-iteration wrappers. -/
theorem inverseIteration_nonTarget_shift_gap_of_uniform_eigenvalue_gap_and_target_radius
    {m : ℕ} (target : Fin m) (lambda : Fin m → ℝ)
    (mu radius sep : ℝ)
    (htarget : |lambda target - mu| ≤ radius)
    (hgap :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) →
        sep + radius ≤ |lambda a - lambda target|) :
    ∀ a : Fin m, a ∈ (Finset.univ.erase target) →
      sep ≤ |lambda a - mu| := by
  intro a ha
  exact
    inverseIteration_nonTarget_shift_gap_of_eigenvalue_gap_and_target_radius
      htarget (hgap a ha)

/-- If the target shift is within radius `radius` of its eigenvalue and every
other shift distance is at least `sep`, then the non-target reciprocal
amplification is at most `(radius / sep)` times the target reciprocal
amplification.  This is the scalar separation adapter used by the inverse
iteration bottleneck: a source theorem may state ordinary distance bounds, while
the local spectral-tail theorem consumes reciprocal-distance ratios. -/
theorem inverseIteration_reciprocal_shift_distance_le_ratio_of_target_distance_le_of_sep_le
    {lambdaTarget lambdaOther mu radius sep : ℝ}
    (hsep_pos : 0 < sep)
    (htarget_pos : 0 < |lambdaTarget - mu|)
    (htarget : |lambdaTarget - mu| ≤ radius)
    (hother : sep ≤ |lambdaOther - mu|) :
    |(lambdaOther - mu)⁻¹| ≤
      (radius / sep) * |(lambdaTarget - mu)⁻¹| := by
  rw [abs_inv, abs_inv]
  have hfirst : 1 / |lambdaOther - mu| ≤ 1 / sep :=
    one_div_le_one_div_of_le hsep_pos hother
  have htarget_ratio : 1 ≤ radius / |lambdaTarget - mu| := by
    exact (one_le_div htarget_pos).mpr htarget
  have hsep_inv_nonneg : 0 ≤ 1 / sep := le_of_lt (one_div_pos.mpr hsep_pos)
  have hmul :
      (1 / sep) * 1 ≤
        (1 / sep) * (radius / |lambdaTarget - mu|) :=
    mul_le_mul_of_nonneg_left htarget_ratio hsep_inv_nonneg
  have hsecond :
      1 / sep ≤ (radius / sep) * (1 / |lambdaTarget - mu|) := by
    calc
      1 / sep = (1 / sep) * 1 := by ring
      _ ≤ (1 / sep) * (radius / |lambdaTarget - mu|) := hmul
      _ = (radius / sep) * (1 / |lambdaTarget - mu|) := by
          field_simp [ne_of_gt hsep_pos, ne_of_gt htarget_pos]
  simpa [one_div] using le_trans hfirst hsecond

/-- Finite-family wrapper for
`inverseIteration_reciprocal_shift_distance_le_ratio_of_target_distance_le_of_sep_le`.
It supplies the `hshift_ratio` hypothesis of
`inverseIterationShiftedInverseSpectralTail_norm_div_target_scale_le_sum_of_component_shift_ratios`
from one target-radius bound and one uniform non-target separation bound. -/
theorem inverseIteration_shift_ratio_of_uniform_target_radius_and_gap
    {m : ℕ} (target : Fin m) (lambda : Fin m → ℝ) (mu radius sep : ℝ)
    (hsep_pos : 0 < sep)
    (htarget_pos : 0 < |lambda target - mu|)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|) :
    ∀ a : Fin m, a ∈ (Finset.univ.erase target) →
      |(lambda a - mu)⁻¹| ≤
        (radius / sep) * |(lambda target - mu)⁻¹| := by
  intro a ha
  exact
    inverseIteration_reciprocal_shift_distance_le_ratio_of_target_distance_le_of_sep_le
      hsep_pos htarget_pos htarget (hsep a ha)

/-- Matrix-vector multiplication commutes with scalar multiplication in the
vector argument. -/
theorem matMulVec_smul_right (n : ℕ) (A : Fin n → Fin n → ℝ)
    (c : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    matMulVec n A (fun j => c * x j) i = c * matMulVec n A x i := by
  unfold matMulVec
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Matrix-vector multiplication distributes over a finite sum in the vector
argument. -/
theorem matMulVec_fin_sum_right {m n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin m → Fin n → ℝ) (i : Fin n) :
    matMulVec n A (fun j => ∑ a : Fin m, x a j) i =
      ∑ a : Fin m, matMulVec n A (x a) i := by
  unfold matMulVec
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Spectral-expansion form of the shifted inverse-iteration solve.  If the
solve residual is expanded in right eigenvector directions and `B` is a left
inverse of `A - mu I`, then applying `B` scales each residual component by the
corresponding reciprocal shift distance. -/
theorem inverseIteration_shiftedInverse_eigenvector_expansion_of_leftInverse
    {m n : ℕ} {A B : Fin n → Fin n → ℝ} {mu : ℝ}
    {lambda : Fin m → ℝ} {v : Fin m → Fin n → ℝ}
    (hEig : ∀ a : Fin m, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin m, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (coeff : Fin m → ℝ) :
    matMulVec n B (fun i => ∑ a : Fin m, coeff a * v a i) =
      fun i => ∑ a : Fin m, coeff a * (lambda a - mu)⁻¹ * v a i := by
  ext i
  rw [matMulVec_fin_sum_right]
  apply Finset.sum_congr rfl
  intro a _
  rw [matMulVec_smul_right]
  have hBv :=
    congrFun
      (inverseIteration_shiftedInverse_mul_eigenvector_of_leftInverse
        (n := n) (A := A) (B := B) (lambda := lambda a) (mu := mu)
        (x := v a) (hEig a) (hshift a) hB) i
  rw [hBv]
  ring

/-- The non-target part of the shifted-inverse residual expansion.  When the
shift is much closer to the target eigenvalue than to the others, this is the
tail term whose size the cited inverse-iteration perturbation theorem must
control. -/
noncomputable def inverseIterationShiftedInverseSpectralTail {m n : ℕ}
    (target : Fin m) (lambda : Fin m → ℝ) (mu : ℝ)
    (v : Fin m → Fin n → ℝ) (coeff : Fin m → ℝ) : Fin n → ℝ :=
  fun i => Finset.sum (Finset.univ.erase target)
    (fun a => coeff a * (lambda a - mu)⁻¹ * v a i)

/-- Target-plus-tail form of the shifted inverse-iteration residual expansion.
This is the exact algebraic mechanism behind the source statement that, near
the target eigenvalue, solve errors are dominated by the required eigenvector
direction; the remaining analytical work is to bound the tail term from
separation/conditioning or a concrete solve certificate. -/
theorem inverseIteration_shiftedInverse_eigenvector_expansion_target_tail_of_leftInverse
    {m n : ℕ} {A B : Fin n → Fin n → ℝ} {mu : ℝ}
    {lambda : Fin m → ℝ} {v : Fin m → Fin n → ℝ}
    (hEig : ∀ a : Fin m, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin m, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (coeff : Fin m → ℝ) (target : Fin m) :
    matMulVec n B (fun i => ∑ a : Fin m, coeff a * v a i) =
      fun i =>
        coeff target * (lambda target - mu)⁻¹ * v target i +
          inverseIterationShiftedInverseSpectralTail target lambda mu v coeff i := by
  rw [inverseIteration_shiftedInverse_eigenvector_expansion_of_leftInverse
    hEig hshift hB coeff]
  ext i
  have hsplit :=
    Finset.sum_eq_add_sum_diff_singleton
      (s := (Finset.univ : Finset (Fin m))) target
      (fun a => coeff a * (lambda a - mu)⁻¹ * v a i)
      (by intro hnot; simp at hnot)
  simp [inverseIterationShiftedInverseSpectralTail] at hsplit ⊢

/-- Applying `A` to a zero linear combination of three right eigenvectors
multiplies each coefficient by the corresponding eigenvalue. -/
theorem linear_combo_three_rightEigenvectors_zero_apply_A
    {n : ℕ} {A : Fin n → Fin n → ℝ}
    {lambda₁ lambda₂ lambda₃ coeff₁ coeff₂ coeff₃ : ℝ}
    {v₁ v₂ v₃ : Fin n → ℝ}
    (h₁ : IsRightEigenpair n A lambda₁ v₁)
    (h₂ : IsRightEigenpair n A lambda₂ v₂)
    (h₃ : IsRightEigenpair n A lambda₃ v₃)
    (hzero :
      ∀ i : Fin n, coeff₁ * v₁ i + coeff₂ * v₂ i + coeff₃ * v₃ i = 0) :
    ∀ i : Fin n,
      coeff₁ * lambda₁ * v₁ i +
          coeff₂ * lambda₂ * v₂ i + coeff₃ * lambda₃ * v₃ i = 0 := by
  intro i
  have hstep :
      matMulVec n A
          (fun j => coeff₁ * v₁ j + (coeff₂ * v₂ j + coeff₃ * v₃ j)) i =
        coeff₁ * lambda₁ * v₁ i +
          (coeff₂ * lambda₂ * v₂ i + coeff₃ * lambda₃ * v₃ i) := by
    rw [congrFun
      (matMulVec_add_right n A
        (fun j => coeff₁ * v₁ j)
        (fun j => coeff₂ * v₂ j + coeff₃ * v₃ j)) i]
    rw [matMulVec_smul_right, h₁.2 i]
    rw [congrFun
      (matMulVec_add_right n A
        (fun j => coeff₂ * v₂ j)
        (fun j => coeff₃ * v₃ j)) i]
    rw [matMulVec_smul_right, matMulVec_smul_right, h₂.2 i, h₃.2 i]
    ring
  have hzero_vec :
      (fun j => coeff₁ * v₁ j + (coeff₂ * v₂ j + coeff₃ * v₃ j)) =
        fun _ => 0 := by
    ext j
    have hj := hzero j
    linarith
  have hmat_zero :
      matMulVec n A
          (fun j => coeff₁ * v₁ j + (coeff₂ * v₂ j + coeff₃ * v₃ j)) i =
        0 := by
    rw [hzero_vec]
    simp [matMulVec]
  linarith

/-- Three right eigenvectors with pairwise distinct eigenvalues are linearly
independent, written in the coefficient form needed by the finite-tail
certificate route. -/
theorem three_rightEigenvectors_pairwise_distinct_linear_combo_eq_zero_coeffs_zero
    {n : ℕ} {A : Fin n → Fin n → ℝ}
    {lambda₁ lambda₂ lambda₃ coeff₁ coeff₂ coeff₃ : ℝ}
    {v₁ v₂ v₃ : Fin n → ℝ}
    (h₁ : IsRightEigenpair n A lambda₁ v₁)
    (h₂ : IsRightEigenpair n A lambda₂ v₂)
    (h₃ : IsRightEigenpair n A lambda₃ v₃)
    (h₁₂ : lambda₁ ≠ lambda₂)
    (h₁₃ : lambda₁ ≠ lambda₃)
    (h₂₃ : lambda₂ ≠ lambda₃)
    (hzero :
      ∀ i : Fin n, coeff₁ * v₁ i + coeff₂ * v₂ i + coeff₃ * v₃ i = 0) :
    coeff₁ = 0 ∧ coeff₂ = 0 ∧ coeff₃ = 0 := by
  have hstep₁ :=
    linear_combo_three_rightEigenvectors_zero_apply_A h₁ h₂ h₃ hzero
  have hstep₂ :
      ∀ i : Fin n,
        coeff₁ * lambda₁ ^ 2 * v₁ i +
            coeff₂ * lambda₂ ^ 2 * v₂ i +
            coeff₃ * lambda₃ ^ 2 * v₃ i = 0 := by
    have hnext :=
      linear_combo_three_rightEigenvectors_zero_apply_A
        (A := A) (lambda₁ := lambda₁) (lambda₂ := lambda₂)
        (lambda₃ := lambda₃) (coeff₁ := coeff₁ * lambda₁)
        (coeff₂ := coeff₂ * lambda₂) (coeff₃ := coeff₃ * lambda₃)
        h₁ h₂ h₃
        (by
          intro i
          have hi := hstep₁ i
          ring_nf at hi ⊢
          exact hi)
    intro i
    have hi := hnext i
    ring_nf at hi ⊢
    exact hi
  have hcoeff₁ : coeff₁ = 0 := by
    rcases h₁.1 with ⟨i, hv⟩
    have hpoly : coeff₁ * (lambda₁ - lambda₂) * (lambda₁ - lambda₃) * v₁ i = 0 := by
      have hcomb :
          (coeff₁ * lambda₁ ^ 2 * v₁ i +
              coeff₂ * lambda₂ ^ 2 * v₂ i +
              coeff₃ * lambda₃ ^ 2 * v₃ i) -
            (lambda₂ + lambda₃) *
              (coeff₁ * lambda₁ * v₁ i +
                coeff₂ * lambda₂ * v₂ i +
                coeff₃ * lambda₃ * v₃ i) +
            lambda₂ * lambda₃ *
              (coeff₁ * v₁ i + coeff₂ * v₂ i + coeff₃ * v₃ i) = 0 := by
        rw [hstep₂ i, hstep₁ i, hzero i]
        ring
      ring_nf at hcomb ⊢
      exact hcomb
    have hprod :
        (lambda₁ - lambda₂) * (lambda₁ - lambda₃) * v₁ i ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h₁₂) (sub_ne_zero.mpr h₁₃)) hv
    have hpoly' :
        coeff₁ * ((lambda₁ - lambda₂) * (lambda₁ - lambda₃) * v₁ i) = 0 := by
      simpa [mul_assoc] using hpoly
    exact (mul_eq_zero.mp hpoly').resolve_right hprod
  have hcoeff₂ : coeff₂ = 0 := by
    rcases h₂.1 with ⟨i, hv⟩
    have hpoly : coeff₂ * (lambda₂ - lambda₁) * (lambda₂ - lambda₃) * v₂ i = 0 := by
      have hcomb :
          (coeff₁ * lambda₁ ^ 2 * v₁ i +
              coeff₂ * lambda₂ ^ 2 * v₂ i +
              coeff₃ * lambda₃ ^ 2 * v₃ i) -
            (lambda₁ + lambda₃) *
              (coeff₁ * lambda₁ * v₁ i +
                coeff₂ * lambda₂ * v₂ i +
                coeff₃ * lambda₃ * v₃ i) +
            lambda₁ * lambda₃ *
              (coeff₁ * v₁ i + coeff₂ * v₂ i + coeff₃ * v₃ i) = 0 := by
        rw [hstep₂ i, hstep₁ i, hzero i]
        ring
      ring_nf at hcomb ⊢
      exact hcomb
    have hprod :
        (lambda₂ - lambda₁) * (lambda₂ - lambda₃) * v₂ i ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h₁₂.symm) (sub_ne_zero.mpr h₂₃)) hv
    have hpoly' :
        coeff₂ * ((lambda₂ - lambda₁) * (lambda₂ - lambda₃) * v₂ i) = 0 := by
      simpa [mul_assoc] using hpoly
    exact (mul_eq_zero.mp hpoly').resolve_right hprod
  have hcoeff₃ : coeff₃ = 0 := by
    rcases h₃.1 with ⟨i, hv⟩
    have hpoly : coeff₃ * (lambda₃ - lambda₁) * (lambda₃ - lambda₂) * v₃ i = 0 := by
      have hcomb :
          (coeff₁ * lambda₁ ^ 2 * v₁ i +
              coeff₂ * lambda₂ ^ 2 * v₂ i +
              coeff₃ * lambda₃ ^ 2 * v₃ i) -
            (lambda₁ + lambda₂) *
              (coeff₁ * lambda₁ * v₁ i +
                coeff₂ * lambda₂ * v₂ i +
                coeff₃ * lambda₃ * v₃ i) +
            lambda₁ * lambda₂ *
              (coeff₁ * v₁ i + coeff₂ * v₂ i + coeff₃ * v₃ i) = 0 := by
        rw [hstep₂ i, hstep₁ i, hzero i]
        ring
      ring_nf at hcomb ⊢
      exact hcomb
    have hprod :
        (lambda₃ - lambda₁) * (lambda₃ - lambda₂) * v₃ i ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h₁₃.symm) (sub_ne_zero.mpr h₂₃.symm)) hv
    have hpoly' :
        coeff₃ * ((lambda₃ - lambda₁) * (lambda₃ - lambda₂) * v₃ i) = 0 := by
      simpa [mul_assoc] using hpoly
    exact (mul_eq_zero.mp hpoly').resolve_right hprod
  exact ⟨hcoeff₁, hcoeff₂, hcoeff₃⟩

/-- The `3 x 3` matrix whose columns are the three supplied vectors. -/
noncomputable def threeColumnMatrix (v₁ v₂ v₃ : Fin 3 → ℝ) :
    Fin 3 → Fin 3 → ℝ
  | i, ⟨0, _⟩ => v₁ i
  | i, ⟨1, _⟩ => v₂ i
  | i, ⟨2, _⟩ => v₃ i

/-- A coefficient-form linear-independence certificate for three columns makes
the associated `3 x 3` column matrix nonsingular. -/
theorem threeColumnMatrix_det_ne_zero_of_linear_combo_eq_zero_coeffs_zero
    {v₁ v₂ v₃ : Fin 3 → ℝ}
    (hlin :
      ∀ coeff₁ coeff₂ coeff₃ : ℝ,
        (∀ i : Fin 3,
          coeff₁ * v₁ i + coeff₂ * v₂ i + coeff₃ * v₃ i = 0) →
        coeff₁ = 0 ∧ coeff₂ = 0 ∧ coeff₃ = 0) :
    Matrix.det
        (threeColumnMatrix v₁ v₂ v₃ :
          Matrix (Fin 3) (Fin 3) ℝ) ≠ 0 := by
  intro hdet
  rcases
    (Matrix.exists_mulVec_eq_zero_iff
      (M := (threeColumnMatrix v₁ v₂ v₃ :
        Matrix (Fin 3) (Fin 3) ℝ))).mpr hdet with
    ⟨coeff, hcoeff_ne, hmul_zero⟩
  have hcombo :
      ∀ i : Fin 3,
        coeff 0 * v₁ i + coeff 1 * v₂ i + coeff 2 * v₃ i = 0 := by
    intro i
    have hi := congrFun hmul_zero i
    have hi' : v₁ i * coeff 0 + v₂ i * coeff 1 + v₃ i * coeff 2 = 0 := by
      change
        (∑ j : Fin 3,
            threeColumnMatrix v₁ v₂ v₃ i j * coeff j) = 0 at hi
      simpa [threeColumnMatrix, Fin.sum_univ_three] using hi
    ring_nf at hi' ⊢
    exact hi'
  rcases hlin (coeff 0) (coeff 1) (coeff 2) hcombo with
    ⟨hcoeff₁, hcoeff₂, hcoeff₃⟩
  apply hcoeff_ne
  ext j
  fin_cases j <;> simp [hcoeff₁, hcoeff₂, hcoeff₃]

/-- Three right eigenvectors with pairwise distinct eigenvalues form a
nonsingular `3 x 3` column matrix. -/
theorem three_rightEigenvectors_pairwise_distinct_threeColumnMatrix_det_ne_zero
    {A : Fin 3 → Fin 3 → ℝ}
    {lambda₁ lambda₂ lambda₃ : ℝ}
    {v₁ v₂ v₃ : Fin 3 → ℝ}
    (h₁ : IsRightEigenpair 3 A lambda₁ v₁)
    (h₂ : IsRightEigenpair 3 A lambda₂ v₂)
    (h₃ : IsRightEigenpair 3 A lambda₃ v₃)
    (h₁₂ : lambda₁ ≠ lambda₂)
    (h₁₃ : lambda₁ ≠ lambda₃)
    (h₂₃ : lambda₂ ≠ lambda₃) :
    Matrix.det
        (threeColumnMatrix v₁ v₂ v₃ :
          Matrix (Fin 3) (Fin 3) ℝ) ≠ 0 :=
  threeColumnMatrix_det_ne_zero_of_linear_combo_eq_zero_coeffs_zero
    (fun _ _ _ hzero =>
      three_rightEigenvectors_pairwise_distinct_linear_combo_eq_zero_coeffs_zero
        h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hzero)

/-- Three right eigenvectors with pairwise distinct eigenvalues have a
right-invertible column matrix in the repository's legacy inverse predicate. -/
theorem three_rightEigenvectors_pairwise_distinct_threeColumnMatrix_isRightInverse
    {A : Fin 3 → Fin 3 → ℝ}
    {lambda₁ lambda₂ lambda₃ : ℝ}
    {v₁ v₂ v₃ : Fin 3 → ℝ}
    (h₁ : IsRightEigenpair 3 A lambda₁ v₁)
    (h₂ : IsRightEigenpair 3 A lambda₂ v₂)
    (h₃ : IsRightEigenpair 3 A lambda₃ v₃)
    (h₁₂ : lambda₁ ≠ lambda₂)
    (h₁₃ : lambda₁ ≠ lambda₃)
    (h₂₃ : lambda₂ ≠ lambda₃) :
    IsRightInverse 3 (threeColumnMatrix v₁ v₂ v₃)
      (nonsingInv 3 (threeColumnMatrix v₁ v₂ v₃)) :=
  (isInverse_nonsingInv_of_det_ne_zero 3 (threeColumnMatrix v₁ v₂ v₃)
    (three_rightEigenvectors_pairwise_distinct_threeColumnMatrix_det_ne_zero
      h₁ h₂ h₃ h₁₂ h₁₃ h₂₃)).2

/-- A right inverse gives an explicit coefficient vector for decomposing any
vector into the columns of a square matrix. -/
theorem matrix_columns_decompose_of_rightInverse
    {n : ℕ} {V V_inv : Fin n → Fin n → ℝ}
    (hV_inv : IsRightInverse n V V_inv) (x : Fin n → ℝ) :
    matMulVec n V (matMulVec n V_inv x) = x := by
  have hmat : matMul n V V_inv = idMatrix n := by
    ext i j
    exact hV_inv i j
  ext i
  calc
    matMulVec n V (matMulVec n V_inv x) i
        = matMulVec n (matMul n V V_inv) x i := by
            exact (matMulVec_matMul n V V_inv x i).symm
    _ = matMulVec n (idMatrix n) x i := by
          rw [hmat]
    _ = x i := by
          rw [matMulVec_id]

/-- Three-column specialization of the right-inverse coefficient handoff:
the coefficients `V_inv*x` reconstruct `x` in column coordinates. -/
theorem threeColumnMatrix_decompose_of_rightInverse
    {v₁ v₂ v₃ : Fin 3 → ℝ} {V_inv : Fin 3 → Fin 3 → ℝ}
    (hV_inv : IsRightInverse 3 (threeColumnMatrix v₁ v₂ v₃) V_inv)
    (x : Fin 3 → ℝ) :
    let coeff := matMulVec 3 V_inv x
    x = fun i => coeff 0 * v₁ i + coeff 1 * v₂ i + coeff 2 * v₃ i := by
  let coeff := matMulVec 3 V_inv x
  have h := matrix_columns_decompose_of_rightInverse hV_inv x
  ext i
  have hi := congrFun h i
  change
    (∑ j : Fin 3, threeColumnMatrix v₁ v₂ v₃ i j * coeff j) = x i at hi
  simp [threeColumnMatrix, Fin.sum_univ_three, coeff] at hi
  ring_nf at hi ⊢
  exact hi.symm

/-- Column-coordinate expansion for a square eigenvector family.  If `V` has
columns `v a` and `V_inv` is a right inverse, then `V_inv*x` gives the
coefficients of `x` in that eigenvector basis. -/
theorem eigenbasis_residual_expansion_of_rightInverse
    {n : ℕ} (v : Fin n → Fin n → ℝ) {V V_inv : Fin n → Fin n → ℝ}
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv) (x : Fin n → ℝ) :
    x = fun i => ∑ a : Fin n, (matMulVec n V_inv x) a * v a i := by
  have h := matrix_columns_decompose_of_rightInverse hV_inv x
  ext i
  calc
    x i = matMulVec n V (matMulVec n V_inv x) i := by
      exact (congrFun h i).symm
    _ = ∑ a : Fin n, (matMulVec n V_inv x) a * v a i := by
      unfold matMulVec
      apply Finset.sum_congr rfl
      intro a _
      rw [hV_cols i a]
      ring

/-- Coordinate bound for coefficients produced by a bounded inverse/eigenbasis
map.  This is the small bridge from an operator-norm certificate for `V_inv` to
per-mode coefficient estimates. -/
theorem eigenbasis_coeff_abs_le_of_inverse_opNorm
    {n : ℕ} (V_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (V_inv_norm : ℝ) (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (a : Fin n) :
    |matMulVec n V_inv x a| ≤ V_inv_norm * vecNorm2 x :=
  (abs_coord_le_vecNorm2 (matMulVec n V_inv x) a).trans (hV_inv_op x)

/-- Coefficient/eigenvector-norm budget derived from an operator-norm bound on
the coefficient map and a residual norm budget. -/
theorem eigenbasis_coeff_vecNorm_le_of_inverse_opNorm_budget
    {n : ℕ} (v : Fin n → Fin n → ℝ) (V_inv : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (V_inv_norm residualNorm : ℝ)
    (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (hx_norm : vecNorm2 x ≤ residualNorm) (a : Fin n) :
    |matMulVec n V_inv x a| * vecNorm2 (v a) ≤
      (V_inv_norm * residualNorm) * vecNorm2 (v a) := by
  have hcoeff :
      |matMulVec n V_inv x a| ≤ V_inv_norm * vecNorm2 x :=
    eigenbasis_coeff_abs_le_of_inverse_opNorm V_inv x V_inv_norm hV_inv_op a
  have hcoeff_budget : V_inv_norm * vecNorm2 x ≤ V_inv_norm * residualNorm :=
    mul_le_mul_of_nonneg_left hx_norm hV_inv_norm_nonneg
  calc
    |matMulVec n V_inv x a| * vecNorm2 (v a)
        ≤ (V_inv_norm * vecNorm2 x) * vecNorm2 (v a) := by
          exact mul_le_mul_of_nonneg_right hcoeff (vecNorm2_nonneg (v a))
    _ ≤ (V_inv_norm * residualNorm) * vecNorm2 (v a) := by
          exact mul_le_mul_of_nonneg_right hcoeff_budget (vecNorm2_nonneg (v a))

/-- Absolute shifted-inverse component budget derived from an eigenbasis inverse
operator bound, a residual norm budget, and a uniform non-target separation
gap.  This feeds the absolute-budget inverse-iteration handoff without
introducing a target coefficient scale. -/
theorem inverseIteration_eigenbasis_shiftedInverse_component_budget_of_inverse_opNorm_residual_gap
    {n : ℕ} (target : Fin n) (lambda : Fin n → ℝ) (mu : ℝ)
    (v : Fin n → Fin n → ℝ) (V_inv : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (V_inv_norm residualNorm sep : ℝ)
    (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (hx_norm : vecNorm2 x ≤ residualNorm)
    (hsep_pos : 0 < sep)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|) :
    ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
      |matMulVec n V_inv x a| * |(lambda a - mu)⁻¹| * vecNorm2 (v a) ≤
        ((V_inv_norm * residualNorm) * (1 / sep)) * vecNorm2 (v a) := by
  intro a ha
  have hcoeff :
      |matMulVec n V_inv x a| ≤ V_inv_norm * vecNorm2 x :=
    eigenbasis_coeff_abs_le_of_inverse_opNorm V_inv x V_inv_norm hV_inv_op a
  have hcoeff_budget :
      V_inv_norm * vecNorm2 x ≤ V_inv_norm * residualNorm :=
    mul_le_mul_of_nonneg_left hx_norm hV_inv_norm_nonneg
  have hcoeff_le :
      |matMulVec n V_inv x a| ≤ V_inv_norm * residualNorm :=
    hcoeff.trans hcoeff_budget
  have hresidual_nonneg : 0 ≤ residualNorm :=
    le_trans (vecNorm2_nonneg x) hx_norm
  have hcoeff_budget_nonneg : 0 ≤ V_inv_norm * residualNorm :=
    mul_nonneg hV_inv_norm_nonneg hresidual_nonneg
  have hshift :
      |(lambda a - mu)⁻¹| ≤ 1 / sep := by
    rw [abs_inv]
    simpa [one_div] using
      one_div_le_one_div_of_le hsep_pos (hsep a ha)
  have hprod :
      |matMulVec n V_inv x a| * |(lambda a - mu)⁻¹| ≤
        (V_inv_norm * residualNorm) * (1 / sep) :=
    mul_le_mul hcoeff_le hshift (abs_nonneg _) hcoeff_budget_nonneg
  exact mul_le_mul_of_nonneg_right hprod (vecNorm2_nonneg (v a))

/-- Removing one target index from a full `Fin n` family leaves `n - 1`
indices. -/
theorem finset_card_univ_erase_fin_eq_sub_one {n : ℕ} (target : Fin n) :
    (Finset.univ.erase target).card = n - 1 := by
  rw [Finset.card_erase_of_mem]
  · simp [Fintype.card_fin]
  · exact Finset.mem_univ target

/-- Uniform-eigenvector-norm collapse of the residual/gap inverse-iteration tail
sum.  If every non-target eigenvector has norm at most `vNormBound`, then the
absolute residual/gap tail budget is bounded by the number of non-target modes
times the common scalar budget. -/
theorem inverseIteration_residual_gap_tail_sum_le_uniform_eigenvector_norm
    {n : ℕ} (target : Fin n) (v : Fin n → Fin n → ℝ)
    (V_inv_norm residualNorm sep vNormBound : ℝ)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (hresidualNorm_nonneg : 0 ≤ residualNorm)
    (hsep_pos : 0 < sep)
    (hv_bound :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        vecNorm2 (v a) ≤ vNormBound) :
    Finset.sum (Finset.univ.erase target)
        (fun a =>
          ((V_inv_norm * residualNorm) * (1 / sep)) * vecNorm2 (v a)) ≤
      ((n - 1 : ℕ) : ℝ) *
        (((V_inv_norm * residualNorm) * (1 / sep)) * vNormBound) := by
  classical
  let c : ℝ := (V_inv_norm * residualNorm) * (1 / sep)
  have hc_nonneg : 0 ≤ c := by
    exact mul_nonneg (mul_nonneg hV_inv_norm_nonneg hresidualNorm_nonneg)
      (le_of_lt (one_div_pos.mpr hsep_pos))
  calc
    Finset.sum (Finset.univ.erase target)
        (fun a =>
          ((V_inv_norm * residualNorm) * (1 / sep)) * vecNorm2 (v a))
        ≤ Finset.sum (Finset.univ.erase target)
            (fun _a => c * vNormBound) := by
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left (hv_bound a ha) hc_nonneg
    _ = ((Finset.univ.erase target).card : ℝ) * (c * vNormBound) := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ = ((n - 1 : ℕ) : ℝ) *
        (((V_inv_norm * residualNorm) * (1 / sep)) * vNormBound) := by
          rw [finset_card_univ_erase_fin_eq_sub_one target]

/-- Source-certificate helper for inverse iteration.  Once a solver theorem has
bounded the residual in norm and an eigenbasis inverse is bounded by
`V_inv_norm`, this lemma packages the coefficient-ratio hypothesis consumed by
`inverseIterationShiftedInverseSpectralTail_norm_div_target_scale_le_sum_of_component_shift_ratios`.
The remaining `hbudget` inequality is the visible separation/conditioning
comparison, not a hidden assumption. -/
theorem inverseIteration_eigenbasis_coeff_ratio_of_inverse_opNorm_budget
    {n : ℕ} (target : Fin n) (v : Fin n → Fin n → ℝ)
    (V_inv : Fin n → Fin n → ℝ) (x beta : Fin n → ℝ)
    (V_inv_norm residualNorm : ℝ)
    (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (hx_norm : vecNorm2 x ≤ residualNorm)
    (hbudget :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        (V_inv_norm * residualNorm) * vecNorm2 (v a) ≤
          beta a *
            (|matMulVec n V_inv x target| * vecNorm2 (v target))) :
    ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
      |matMulVec n V_inv x a| * vecNorm2 (v a) ≤
        beta a *
          (|matMulVec n V_inv x target| * vecNorm2 (v target)) := by
  intro a ha
  exact
    (eigenbasis_coeff_vecNorm_le_of_inverse_opNorm_budget
      v V_inv x V_inv_norm residualNorm hV_inv_op
      hV_inv_norm_nonneg hx_norm a).trans (hbudget a ha)

/-- Explicit target-scale version of
`inverseIteration_eigenbasis_coeff_ratio_of_inverse_opNorm_budget`.  A source
theorem or solver certificate may lower-bound the target coefficient scale by
`targetScale`; this lemma then exposes the concrete non-target budgets
`((V_inv_norm * residualNorm) * ||v a||₂) / targetScale` rather than leaving an
abstract per-mode `hbudget`. -/
theorem inverseIteration_eigenbasis_coeff_ratio_of_inverse_opNorm_explicit_beta
    {n : ℕ} (target : Fin n) (v : Fin n → Fin n → ℝ)
    (V_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (V_inv_norm residualNorm targetScale : ℝ)
    (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (hx_norm : vecNorm2 x ≤ residualNorm)
    (htargetScale_pos : 0 < targetScale)
    (htargetScale_le :
      targetScale ≤ |matMulVec n V_inv x target| * vecNorm2 (v target)) :
    (∀ a : Fin n, a ∈ (Finset.univ.erase target) →
      0 ≤ ((V_inv_norm * residualNorm) * vecNorm2 (v a)) / targetScale) ∧
    (∀ a : Fin n, a ∈ (Finset.univ.erase target) →
      |matMulVec n V_inv x a| * vecNorm2 (v a) ≤
        (((V_inv_norm * residualNorm) * vecNorm2 (v a)) / targetScale) *
          (|matMulVec n V_inv x target| * vecNorm2 (v target))) := by
  have hresidual_nonneg : 0 ≤ residualNorm :=
    le_trans (vecNorm2_nonneg x) hx_norm
  have hnum_nonneg :
      ∀ a : Fin n, 0 ≤ (V_inv_norm * residualNorm) * vecNorm2 (v a) := by
    intro a
    exact
      mul_nonneg
        (mul_nonneg hV_inv_norm_nonneg hresidual_nonneg)
        (vecNorm2_nonneg (v a))
  have hbeta_nonneg :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        0 ≤ ((V_inv_norm * residualNorm) * vecNorm2 (v a)) / targetScale := by
    intro a _ha
    exact div_nonneg (hnum_nonneg a) (le_of_lt htargetScale_pos)
  have hbudget :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        (V_inv_norm * residualNorm) * vecNorm2 (v a) ≤
          (((V_inv_norm * residualNorm) * vecNorm2 (v a)) / targetScale) *
            (|matMulVec n V_inv x target| * vecNorm2 (v target)) := by
    intro a ha
    have hscale_ne : targetScale ≠ 0 := ne_of_gt htargetScale_pos
    calc
      (V_inv_norm * residualNorm) * vecNorm2 (v a)
          =
            (((V_inv_norm * residualNorm) * vecNorm2 (v a)) / targetScale) *
              targetScale := by
              field_simp [hscale_ne]
      _ ≤
            (((V_inv_norm * residualNorm) * vecNorm2 (v a)) / targetScale) *
              (|matMulVec n V_inv x target| * vecNorm2 (v target)) := by
              exact mul_le_mul_of_nonneg_left htargetScale_le (hbeta_nonneg a ha)
  exact
    ⟨hbeta_nonneg,
      inverseIteration_eigenbasis_coeff_ratio_of_inverse_opNorm_budget
        target v V_inv x
        (fun a => ((V_inv_norm * residualNorm) * vecNorm2 (v a)) / targetScale)
        V_inv_norm residualNorm hV_inv_op hV_inv_norm_nonneg hx_norm hbudget⟩

/-- Positivity of the target coefficient/eigenvector scale used by the
inverse-iteration explicit-beta route.  A future source theorem or solver
certificate may provide the target coefficient directly; this helper turns that
evidence into the positive scale consumed by the denominator-explicit
wrappers. -/
theorem inverseIteration_target_coeff_vecNorm_scale_pos_of_coeff_ne_zero
    {n : ℕ} (target : Fin n) (v : Fin n → Fin n → ℝ)
    (V_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hcoeff : matMulVec n V_inv x target ≠ 0)
    (hvec : ∃ i : Fin n, v target i ≠ 0) :
    0 < |matMulVec n V_inv x target| * vecNorm2 (v target) := by
  have hcoeff_pos : 0 < |matMulVec n V_inv x target| := abs_pos.mpr hcoeff
  have hv_norm_ne : vecNorm2 (v target) ≠ 0 := by
    intro hzero
    rcases hvec with ⟨i, hi⟩
    exact hi ((vecNorm2_eq_zero_iff (v target)).mp hzero i)
  have hv_norm_pos : 0 < vecNorm2 (v target) :=
    lt_of_le_of_ne (vecNorm2_nonneg (v target)) (Ne.symm hv_norm_ne)
  exact mul_pos hcoeff_pos hv_norm_pos

/-- Direct target-coefficient version of
`inverseIteration_eigenbasis_coeff_ratio_of_inverse_opNorm_explicit_beta`.
Instead of supplying an abstract lower bound `targetScale`, this wrapper uses
the actual target coefficient/eigenvector scale as the denominator, under the
visible nonzero target coefficient and target eigenvector hypotheses. -/
theorem inverseIteration_eigenbasis_coeff_ratio_of_inverse_opNorm_direct_target
    {n : ℕ} (target : Fin n) (v : Fin n → Fin n → ℝ)
    (V_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (V_inv_norm residualNorm : ℝ)
    (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (hx_norm : vecNorm2 x ≤ residualNorm)
    (hcoeff : matMulVec n V_inv x target ≠ 0)
    (hvec : ∃ i : Fin n, v target i ≠ 0) :
    (∀ a : Fin n, a ∈ (Finset.univ.erase target) →
      0 ≤ ((V_inv_norm * residualNorm) * vecNorm2 (v a)) /
        (|matMulVec n V_inv x target| * vecNorm2 (v target))) ∧
    (∀ a : Fin n, a ∈ (Finset.univ.erase target) →
      |matMulVec n V_inv x a| * vecNorm2 (v a) ≤
        (((V_inv_norm * residualNorm) * vecNorm2 (v a)) /
            (|matMulVec n V_inv x target| * vecNorm2 (v target))) *
          (|matMulVec n V_inv x target| * vecNorm2 (v target))) := by
  exact
    inverseIteration_eigenbasis_coeff_ratio_of_inverse_opNorm_explicit_beta
      target v V_inv x V_inv_norm residualNorm
      (|matMulVec n V_inv x target| * vecNorm2 (v target))
      hV_inv_op hV_inv_norm_nonneg hx_norm
      (inverseIteration_target_coeff_vecNorm_scale_pos_of_coeff_ne_zero
        target v V_inv x hcoeff hvec)
      (le_rfl)

/-- If replacing the third column by `x` keeps a three-column matrix
nonsingular, then the coefficient of the original third column in the
right-inverse decomposition of `x` is nonzero. -/
theorem threeColumnMatrix_decompose_coeff_two_ne_zero_of_replacement_det_ne_zero
    {v₁ v₂ v₃ x : Fin 3 → ℝ} {V_inv : Fin 3 → Fin 3 → ℝ}
    (hV_inv : IsRightInverse 3 (threeColumnMatrix v₁ v₂ v₃) V_inv)
    (hdet :
      Matrix.det
        (threeColumnMatrix v₁ v₂ x : Matrix (Fin 3) (Fin 3) ℝ) ≠ 0) :
    (matMulVec 3 V_inv x) 2 ≠ 0 := by
  let coeff := matMulVec 3 V_inv x
  intro hcoeff₂
  have hcoeff₂' : coeff 2 = 0 := by
    simpa [coeff] using hcoeff₂
  have hdecomp := threeColumnMatrix_decompose_of_rightInverse hV_inv x
  change x = fun i => coeff 0 * v₁ i + coeff 1 * v₂ i + coeff 2 * v₃ i at hdecomp
  let w : Fin 3 → ℝ
    | ⟨0, _⟩ => coeff 0
    | ⟨1, _⟩ => coeff 1
    | ⟨2, _⟩ => -1
  have hw_ne : w ≠ fun _ : Fin 3 => 0 := by
    intro hw
    have htwo := congrFun hw (2 : Fin 3)
    norm_num [w] at htwo
  have hmul_zero :
      Matrix.mulVec
        (threeColumnMatrix v₁ v₂ x : Matrix (Fin 3) (Fin 3) ℝ) w = 0 := by
    ext i
    have hi := congrFun hdecomp i
    change (∑ j : Fin 3, threeColumnMatrix v₁ v₂ x i j * w j) = 0
    rw [Fin.sum_univ_three]
    simp [threeColumnMatrix, w]
    rw [hi, hcoeff₂']
    ring
  exact hdet
    ((Matrix.exists_mulVec_eq_zero_iff
      (M := (threeColumnMatrix v₁ v₂ x :
        Matrix (Fin 3) (Fin 3) ℝ))).mp ⟨w, hw_ne, hmul_zero⟩)

/-- Finite-sum Euclidean triangle inequality over an arbitrary finite set. -/
theorem vecNorm2_finset_sum_le {α : Type*} [DecidableEq α] {n : ℕ}
    (s : Finset α) (x : α → Fin n → ℝ) :
    vecNorm2 (fun i => Finset.sum s (fun a => x a i)) ≤
      Finset.sum s (fun a => vecNorm2 (x a)) := by
  classical
  refine Finset.induction_on s ?empty ?insert
  · simp [vecNorm2_zero]
  · intro a s has ih
    calc
      vecNorm2 (fun i => Finset.sum (insert a s) (fun b => x b i))
          = vecNorm2 (fun i => x a i + Finset.sum s (fun b => x b i)) := by
              congr 1
              ext i
              simp [Finset.sum_insert has]
      _ ≤ vecNorm2 (x a) +
            vecNorm2 (fun i => Finset.sum s (fun b => x b i)) :=
          vecNorm2_add_le (x a) (fun i => Finset.sum s (fun b => x b i))
      _ ≤ vecNorm2 (x a) + Finset.sum s (fun b => vecNorm2 (x b)) := by
          linarith [ih]
      _ = Finset.sum (insert a s) (fun b => vecNorm2 (x b)) := by
          rw [Finset.sum_insert has]

/-- Finite-family Euclidean triangle inequality for `Fin m`-indexed vectors. -/
theorem vecNorm2_fin_sum_le {m n : ℕ}
    (x : Fin m → Fin n → ℝ) :
    vecNorm2 (fun i => ∑ a : Fin m, x a i) ≤
      ∑ a : Fin m, vecNorm2 (x a) := by
  simpa using
    vecNorm2_finset_sum_le (s := (Finset.univ : Finset (Fin m))) x

/-- Norm bound for the non-target spectral tail of a shifted-inverse residual
expansion.  This is the exact finite-dimensional triangle inequality layer
that a Parlett/Golub--Van Loan route or a concrete solver certificate must feed
with separation/conditioning bounds. -/
theorem inverseIterationShiftedInverseSpectralTail_norm_le_sum {m n : ℕ}
    (target : Fin m) (lambda : Fin m → ℝ) (mu : ℝ)
    (v : Fin m → Fin n → ℝ) (coeff : Fin m → ℝ) :
    vecNorm2
        (inverseIterationShiftedInverseSpectralTail target lambda mu v coeff) ≤
      Finset.sum (Finset.univ.erase target)
        (fun a => |coeff a| * |(lambda a - mu)⁻¹| * vecNorm2 (v a)) := by
  classical
  calc
    vecNorm2
        (inverseIterationShiftedInverseSpectralTail target lambda mu v coeff)
        ≤ Finset.sum (Finset.univ.erase target) (fun a =>
            vecNorm2 (fun i => coeff a * (lambda a - mu)⁻¹ * v a i)) := by
            change
              vecNorm2
                  (fun i => Finset.sum (Finset.univ.erase target)
                    (fun a => coeff a * (lambda a - mu)⁻¹ * v a i)) ≤
                Finset.sum (Finset.univ.erase target) (fun a =>
                  vecNorm2
                    (fun i => coeff a * (lambda a - mu)⁻¹ * v a i))
            exact
              vecNorm2_finset_sum_le
                (s := (Finset.univ.erase target))
                (x := fun a i => coeff a * (lambda a - mu)⁻¹ * v a i)
    _ = Finset.sum (Finset.univ.erase target)
        (fun a => |coeff a| * |(lambda a - mu)⁻¹| * vecNorm2 (v a)) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [vecNorm2_smul, abs_mul]

/-- Budgeted version of the spectral-tail norm bound.  Later source-theorem
instantiations can supply per-mode tail budgets without reopening the finite
triangle-inequality proof. -/
theorem inverseIterationShiftedInverseSpectralTail_norm_le_of_component_budget
    {m n : ℕ} (target : Fin m) (lambda : Fin m → ℝ) (mu : ℝ)
    (v : Fin m → Fin n → ℝ) (coeff budget : Fin m → ℝ)
    (hbudget :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) →
        |coeff a| * |(lambda a - mu)⁻¹| * vecNorm2 (v a) ≤ budget a) :
    vecNorm2
        (inverseIterationShiftedInverseSpectralTail target lambda mu v coeff) ≤
      Finset.sum (Finset.univ.erase target) budget := by
  exact le_trans
    (inverseIterationShiftedInverseSpectralTail_norm_le_sum
      target lambda mu v coeff)
    (Finset.sum_le_sum (fun a ha => hbudget a ha))

/-- Source-theorem adapter for inverse iteration: if each non-target
shifted-inverse component is bounded by a ratio `q a` times the target
amplified component, then the whole non-target spectral tail is bounded by the
finite sum of those ratios times the same target scale.  This is the exact
normalization layer that a Parlett/Golub--Van Loan separation estimate or a
concrete shifted-solve certificate should instantiate. -/
theorem inverseIterationShiftedInverseSpectralTail_norm_le_target_scale_mul_sum
    {m n : ℕ} (target : Fin m) (lambda : Fin m → ℝ) (mu : ℝ)
    (v : Fin m → Fin n → ℝ) (coeff q : Fin m → ℝ)
    (hbudget :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) →
        |coeff a| * |(lambda a - mu)⁻¹| * vecNorm2 (v a) ≤
          q a *
            (|coeff target| * |(lambda target - mu)⁻¹| *
              vecNorm2 (v target))) :
    vecNorm2
        (inverseIterationShiftedInverseSpectralTail target lambda mu v coeff) ≤
      Finset.sum (Finset.univ.erase target) q *
        (|coeff target| * |(lambda target - mu)⁻¹| *
          vecNorm2 (v target)) := by
  classical
  calc
    vecNorm2
        (inverseIterationShiftedInverseSpectralTail target lambda mu v coeff)
        ≤ Finset.sum (Finset.univ.erase target)
            (fun a =>
              q a *
                (|coeff target| * |(lambda target - mu)⁻¹| *
                  vecNorm2 (v target))) := by
            exact
              inverseIterationShiftedInverseSpectralTail_norm_le_of_component_budget
                target lambda mu v coeff
                (fun a =>
                  q a *
                    (|coeff target| * |(lambda target - mu)⁻¹| *
                      vecNorm2 (v target)))
                hbudget
    _ = Finset.sum (Finset.univ.erase target) q *
        (|coeff target| * |(lambda target - mu)⁻¹| *
          vecNorm2 (v target)) := by
          rw [Finset.sum_mul]

/-- Normalized version of
`inverseIterationShiftedInverseSpectralTail_norm_le_target_scale_mul_sum`.
When the target amplified component has positive scale, the non-target tail
divided by that target scale is bounded by the finite sum of supplied
per-mode ratios. -/
theorem inverseIterationShiftedInverseSpectralTail_norm_div_target_scale_le_sum
    {m n : ℕ} (target : Fin m) (lambda : Fin m → ℝ) (mu : ℝ)
    (v : Fin m → Fin n → ℝ) (coeff q : Fin m → ℝ)
    (hscale :
      0 <
        |coeff target| * |(lambda target - mu)⁻¹| *
          vecNorm2 (v target))
    (hbudget :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) →
        |coeff a| * |(lambda a - mu)⁻¹| * vecNorm2 (v a) ≤
          q a *
            (|coeff target| * |(lambda target - mu)⁻¹| *
              vecNorm2 (v target))) :
    vecNorm2
        (inverseIterationShiftedInverseSpectralTail target lambda mu v coeff) /
        (|coeff target| * |(lambda target - mu)⁻¹| *
          vecNorm2 (v target)) ≤
      Finset.sum (Finset.univ.erase target) q := by
  exact (div_le_iff₀ hscale).mpr
    (inverseIterationShiftedInverseSpectralTail_norm_le_target_scale_mul_sum
      target lambda mu v coeff q hbudget)

/-- Positivity adapter for the target amplified component in the inverse
iteration spectral-tail route.  A nonzero target coefficient, nonzero target
shift, and nonzero target eigenvector make the target scale strictly positive. -/
theorem inverseIteration_target_amplified_scale_pos_of_coeff_ne_zero
    {m n : ℕ} (target : Fin m) {lambda coeff : Fin m → ℝ}
    {v : Fin m → Fin n → ℝ} {mu : ℝ}
    (hcoeff : coeff target ≠ 0)
    (hshift_target : lambda target - mu ≠ 0)
    (hvec : ∃ i : Fin n, v target i ≠ 0) :
    0 <
      |coeff target| * |(lambda target - mu)⁻¹| *
        vecNorm2 (v target) := by
  have hcoeff_pos : 0 < |coeff target| := abs_pos.mpr hcoeff
  have hshift_inv_pos : 0 < |(lambda target - mu)⁻¹| :=
    abs_pos.mpr (inv_ne_zero hshift_target)
  have hv_norm_ne : vecNorm2 (v target) ≠ 0 := by
    intro hzero
    rcases hvec with ⟨i, hi⟩
    exact hi ((vecNorm2_eq_zero_iff (v target)).mp hzero i)
  have hv_norm_pos : 0 < vecNorm2 (v target) :=
    lt_of_le_of_ne (vecNorm2_nonneg (v target)) (Ne.symm hv_norm_ne)
  exact mul_pos (mul_pos hcoeff_pos hshift_inv_pos) hv_norm_pos

/-- Separation-facing version of the normalized spectral-tail adapter.  If the
coefficient/eigenvector norm part of each non-target mode is at most `beta a`
times the target coefficient/eigenvector norm, and the reciprocal shift-distance
part is at most `sigma a` times the target reciprocal shift distance, then the
whole normalized tail is bounded by the finite sum of `beta a * sigma a`.

This is still an adapter: a source perturbation theorem or concrete solver
certificate must supply the `beta` and `sigma` hypotheses. -/
theorem inverseIterationShiftedInverseSpectralTail_norm_div_target_scale_le_sum_of_component_shift_ratios
    {m n : ℕ} (target : Fin m) (lambda : Fin m → ℝ) (mu : ℝ)
    (v : Fin m → Fin n → ℝ) (coeff beta sigma : Fin m → ℝ)
    (hscale :
      0 <
        |coeff target| * |(lambda target - mu)⁻¹| *
          vecNorm2 (v target))
    (hbeta_nonneg :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) → 0 ≤ beta a)
    (hcoeff_ratio :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) →
        |coeff a| * vecNorm2 (v a) ≤
          beta a * (|coeff target| * vecNorm2 (v target)))
    (hshift_ratio :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) →
        |(lambda a - mu)⁻¹| ≤
          sigma a * |(lambda target - mu)⁻¹|) :
    vecNorm2
        (inverseIterationShiftedInverseSpectralTail target lambda mu v coeff) /
        (|coeff target| * |(lambda target - mu)⁻¹| *
          vecNorm2 (v target)) ≤
      Finset.sum (Finset.univ.erase target) (fun a => beta a * sigma a) := by
  classical
  refine
    inverseIterationShiftedInverseSpectralTail_norm_div_target_scale_le_sum
      target lambda mu v coeff (fun a => beta a * sigma a) hscale ?_
  intro a ha
  have hcoeff := hcoeff_ratio a ha
  have hshift := hshift_ratio a ha
  have hshift_nonneg : 0 ≤ |(lambda a - mu)⁻¹| := abs_nonneg _
  have hcoeff_target_nonneg :
      0 ≤ |coeff target| * vecNorm2 (v target) :=
    mul_nonneg (abs_nonneg _) (vecNorm2_nonneg _)
  have hcoeff_bound_nonneg :
      0 ≤ beta a * (|coeff target| * vecNorm2 (v target)) :=
    mul_nonneg (hbeta_nonneg a ha) hcoeff_target_nonneg
  have hprod :
      (|coeff a| * vecNorm2 (v a)) * |(lambda a - mu)⁻¹| ≤
        (beta a * (|coeff target| * vecNorm2 (v target))) *
          (sigma a * |(lambda target - mu)⁻¹|) :=
    mul_le_mul hcoeff hshift hshift_nonneg hcoeff_bound_nonneg
  calc
    |coeff a| * |(lambda a - mu)⁻¹| * vecNorm2 (v a)
        = (|coeff a| * vecNorm2 (v a)) * |(lambda a - mu)⁻¹| := by
            ring
    _ ≤ (beta a * (|coeff target| * vecNorm2 (v target))) *
          (sigma a * |(lambda target - mu)⁻¹|) := hprod
    _ = (beta a * sigma a) *
        (|coeff target| * |(lambda target - mu)⁻¹| *
          vecNorm2 (v target)) := by
          ring

/-- If a starting vector is a sum of two right-eigenvector components, then
`k` unnormalized power-method steps scale each component by the corresponding
`k`th eigenvalue power.  This is the algebraic substrate for the Chapter 1
statement that a nonzero dominant component is amplified relative to smaller
components. -/
theorem powerMethodIterate_two_eigencomponents
    {n : ℕ} {A : Fin n → Fin n → ℝ}
    {lambdaDominant lambdaOther coeffDominant coeffOther : ℝ}
    {vDominant vOther : Fin n → ℝ}
    (hDominant : IsRightEigenpair n A lambdaDominant vDominant)
    (hOther : IsRightEigenpair n A lambdaOther vOther) (k : ℕ) :
    powerMethodIterate n A k
        (fun i => coeffDominant * vDominant i + coeffOther * vOther i) =
      fun i =>
        coeffDominant * lambdaDominant ^ k * vDominant i +
          coeffOther * lambdaOther ^ k * vOther i := by
  induction k with
  | zero =>
      ext i
      simp [powerMethodIterate]
  | succ k ih =>
      ext i
      calc
        powerMethodIterate n A (k + 1)
            (fun i => coeffDominant * vDominant i + coeffOther * vOther i) i
            = powerMethodStep n A
                (fun i =>
                  coeffDominant * lambdaDominant ^ k * vDominant i +
                    coeffOther * lambdaOther ^ k * vOther i) i := by
                simp [powerMethodIterate, ih]
        _ = coeffDominant * lambdaDominant ^ (k + 1) * vDominant i +
              coeffOther * lambdaOther ^ (k + 1) * vOther i := by
              unfold powerMethodStep
              rw [congrFun
                (matMulVec_add_right n A
                  (fun i => coeffDominant * lambdaDominant ^ k * vDominant i)
                  (fun i => coeffOther * lambdaOther ^ k * vOther i)) i]
              rw [matMulVec_smul_right, matMulVec_smul_right]
              rw [hDominant.2 i, hOther.2 i]
              ring

/-- Finite-tail version of the power-method eigencomponent identity.  If the
starting vector is a dominant right-eigenvector component plus any finite sum
of other right-eigenvector components, then `k` unnormalized power-method steps
scale each component by the corresponding `k`th eigenvalue power. -/
theorem powerMethodIterate_dominant_plus_finite_tail
    {n m : ℕ} {A : Fin n → Fin n → ℝ}
    {lambdaDominant coeffDominant : ℝ}
    {lambdaTail coeffTail : Fin m → ℝ}
    {vDominant : Fin n → ℝ} {vTail : Fin m → Fin n → ℝ}
    (hDominant : IsRightEigenpair n A lambdaDominant vDominant)
    (hTail : ∀ a : Fin m, IsRightEigenpair n A (lambdaTail a) (vTail a))
    (k : ℕ) :
    powerMethodIterate n A k
        (fun i => coeffDominant * vDominant i +
          ∑ a : Fin m, coeffTail a * vTail a i) =
      fun i =>
        coeffDominant * lambdaDominant ^ k * vDominant i +
          ∑ a : Fin m, coeffTail a * lambdaTail a ^ k * vTail a i := by
  induction k with
  | zero =>
      ext i
      simp [powerMethodIterate]
  | succ k ih =>
      ext i
      calc
        powerMethodIterate n A (k + 1)
            (fun i => coeffDominant * vDominant i +
              ∑ a : Fin m, coeffTail a * vTail a i) i
            = powerMethodStep n A
                (fun i =>
                  coeffDominant * lambdaDominant ^ k * vDominant i +
                    ∑ a : Fin m,
                      coeffTail a * lambdaTail a ^ k * vTail a i) i := by
                simp [powerMethodIterate, ih]
        _ = coeffDominant * lambdaDominant ^ (k + 1) * vDominant i +
              ∑ a : Fin m,
                coeffTail a * lambdaTail a ^ (k + 1) * vTail a i := by
              unfold powerMethodStep
              have htail :
                  matMulVec n A
                      (fun i =>
                        ∑ a : Fin m,
                          coeffTail a * lambdaTail a ^ k * vTail a i) i =
                    ∑ a : Fin m,
                      coeffTail a * lambdaTail a ^ (k + 1) * vTail a i := by
                rw [matMulVec_fin_sum_right]
                apply Finset.sum_congr rfl
                intro a _
                rw [matMulVec_smul_right]
                rw [(hTail a).2 i]
                ring
              rw [congrFun
                (matMulVec_add_right n A
                  (fun i => coeffDominant * lambdaDominant ^ k * vDominant i)
                  (fun i =>
                    ∑ a : Fin m,
                      coeffTail a * lambdaTail a ^ k * vTail a i)) i]
              rw [matMulVec_smul_right]
              rw [hDominant.2 i, htail]
              ring

/-- Exact ratio formula for the scalar coefficients in the two-component power
method model: the non-dominant-to-dominant component ratio is the initial
coefficient ratio times the spectral ratio to the `k`th power. -/
theorem powerMethod_component_abs_ratio_eq_initial_mul_spectral_ratio
    {lambdaDominant lambdaOther coeffDominant coeffOther : ℝ} (k : ℕ)
    (hCoeff : coeffDominant ≠ 0) (hLambda : lambdaDominant ≠ 0) :
    |coeffOther * lambdaOther ^ k| /
        |coeffDominant * lambdaDominant ^ k| =
      (|coeffOther| / |coeffDominant|) *
        (|lambdaOther| / |lambdaDominant|) ^ k := by
  have hCoeffAbs : |coeffDominant| ≠ 0 :=
    ne_of_gt (abs_pos.mpr hCoeff)
  have hLambdaAbs : |lambdaDominant| ≠ 0 :=
    ne_of_gt (abs_pos.mpr hLambda)
  rw [abs_mul, abs_mul, abs_pow, abs_pow, div_pow]
  field_simp [hCoeffAbs, hLambdaAbs, pow_ne_zero k hLambdaAbs]

/-- Linear-rate ratio bound for the two-component power-method model.  If the
spectral ratio is at most `q`, then the smaller component is bounded by the
initial component ratio times `q^k`. -/
theorem powerMethod_component_abs_ratio_le_geometric_of_spectral_ratio_le
    {lambdaDominant lambdaOther coeffDominant coeffOther q : ℝ} (k : ℕ)
    (hCoeff : coeffDominant ≠ 0) (hLambda : lambdaDominant ≠ 0)
    (hRatio : |lambdaOther| / |lambdaDominant| ≤ q) :
    |coeffOther * lambdaOther ^ k| /
        |coeffDominant * lambdaDominant ^ k| ≤
      (|coeffOther| / |coeffDominant|) * q ^ k := by
  rw [powerMethod_component_abs_ratio_eq_initial_mul_spectral_ratio
    (k := k) hCoeff hLambda]
  have hSpectralNonneg : 0 ≤ |lambdaOther| / |lambdaDominant| :=
    div_nonneg (abs_nonneg _) (abs_nonneg _)
  have hpow :
      (|lambdaOther| / |lambdaDominant|) ^ k ≤ q ^ k :=
    pow_le_pow_left₀ hSpectralNonneg hRatio k
  exact mul_le_mul_of_nonneg_left hpow
    (div_nonneg (abs_nonneg _) (abs_nonneg _))

/-- Convergence-rate form of the same two-component power-method model: if the
spectral ratio is strictly below one, the non-dominant-to-dominant coefficient
ratio tends to zero. -/
theorem powerMethod_component_abs_ratio_tendsto_zero_of_spectral_ratio_lt_one
    {lambdaDominant lambdaOther coeffDominant coeffOther : ℝ}
    (hCoeff : coeffDominant ≠ 0) (hLambda : lambdaDominant ≠ 0)
    (hRatioNonneg : 0 ≤ |lambdaOther| / |lambdaDominant|)
    (hRatioLtOne : |lambdaOther| / |lambdaDominant| < 1) :
    Tendsto
      (fun k : ℕ =>
        |coeffOther * lambdaOther ^ k| /
          |coeffDominant * lambdaDominant ^ k|)
      atTop (𝓝 0) := by
  have hpow :
      Tendsto
        (fun k : ℕ => (|lambdaOther| / |lambdaDominant|) ^ k)
        atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hRatioNonneg hRatioLtOne
  have hfun :
      (fun k : ℕ =>
        |coeffOther * lambdaOther ^ k| /
          |coeffDominant * lambdaDominant ^ k|) =
        fun k : ℕ =>
          (|coeffOther| / |coeffDominant|) *
            (|lambdaOther| / |lambdaDominant|) ^ k := by
    funext k
    exact powerMethod_component_abs_ratio_eq_initial_mul_spectral_ratio
      (k := k) hCoeff hLambda
  rw [hfun]
  simpa using hpow.const_mul (|coeffOther| / |coeffDominant|)

/-- Aggregate geometric bound for a finite non-dominant tail in the
power-method model.  If every tail spectral ratio is at most `q`, then the sum
of tail coefficient magnitudes, normalized by the dominant coefficient
magnitude, is bounded by the initial finite-tail ratio times `q^k`. -/
theorem powerMethod_finite_tail_abs_sum_ratio_le_geometric_of_spectral_ratio_le
    {m : ℕ} {lambdaDominant coeffDominant q : ℝ}
    {lambdaTail coeffTail : Fin m → ℝ} (k : ℕ)
    (hCoeff : coeffDominant ≠ 0) (hLambda : lambdaDominant ≠ 0)
    (hRatio : ∀ a : Fin m, |lambdaTail a| / |lambdaDominant| ≤ q) :
    (∑ a : Fin m, |coeffTail a * lambdaTail a ^ k|) /
        |coeffDominant * lambdaDominant ^ k| ≤
      ((∑ a : Fin m, |coeffTail a|) / |coeffDominant|) * q ^ k := by
  rw [Finset.sum_div]
  calc
    (∑ a : Fin m,
        |coeffTail a * lambdaTail a ^ k| /
          |coeffDominant * lambdaDominant ^ k|)
        ≤ ∑ a : Fin m, (|coeffTail a| / |coeffDominant|) * q ^ k := by
            apply Finset.sum_le_sum
            intro a _
            exact
              powerMethod_component_abs_ratio_le_geometric_of_spectral_ratio_le
                (k := k) (coeffOther := coeffTail a)
                (lambdaOther := lambdaTail a) hCoeff hLambda (hRatio a)
    _ = ((∑ a : Fin m, |coeffTail a|) / |coeffDominant|) * q ^ k := by
          rw [← Finset.sum_mul]
          congr 1
          rw [Finset.sum_div]

/-- The geometric upper bound used for a finite non-dominant power-method tail
tends to zero whenever the common spectral-ratio bound is strictly below one. -/
theorem powerMethod_finite_tail_geometric_bound_tendsto_zero
    {m : ℕ} {coeffDominant q : ℝ} {coeffTail : Fin m → ℝ}
    (hqNonneg : 0 ≤ q) (hqLtOne : q < 1) :
    Tendsto
      (fun k : ℕ =>
        ((∑ a : Fin m, |coeffTail a|) / |coeffDominant|) * q ^ k)
      atTop (𝓝 0) := by
  have hpow : Tendsto (fun k : ℕ => q ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hqNonneg hqLtOne
  simpa using
    hpow.const_mul ((∑ a : Fin m, |coeffTail a|) / |coeffDominant|)

/-- Convergence-rate form for the finite-tail power-method model: under a
common spectral-ratio bound `q < 1`, the normalized aggregate non-dominant tail
tends to zero. -/
theorem powerMethod_finite_tail_abs_sum_ratio_tendsto_zero_of_geometric_bound
    {m : ℕ} {lambdaDominant coeffDominant q : ℝ}
    {lambdaTail coeffTail : Fin m → ℝ}
    (hCoeff : coeffDominant ≠ 0) (hLambda : lambdaDominant ≠ 0)
    (hRatio : ∀ a : Fin m, |lambdaTail a| / |lambdaDominant| ≤ q)
    (hqNonneg : 0 ≤ q) (hqLtOne : q < 1) :
    Tendsto
      (fun k : ℕ =>
        (∑ a : Fin m, |coeffTail a * lambdaTail a ^ k|) /
          |coeffDominant * lambdaDominant ^ k|)
      atTop (𝓝 0) := by
  have hUpper :
      ∀ k : ℕ,
        (∑ a : Fin m, |coeffTail a * lambdaTail a ^ k|) /
            |coeffDominant * lambdaDominant ^ k| ≤
          ((∑ a : Fin m, |coeffTail a|) / |coeffDominant|) * q ^ k :=
    fun k =>
      powerMethod_finite_tail_abs_sum_ratio_le_geometric_of_spectral_ratio_le
        (k := k) hCoeff hLambda hRatio
  have hLower :
      ∀ k : ℕ,
        0 ≤
          (∑ a : Fin m, |coeffTail a * lambdaTail a ^ k|) /
            |coeffDominant * lambdaDominant ^ k| :=
    fun _ =>
      div_nonneg
        (Finset.sum_nonneg fun a _ => abs_nonneg _)
        (abs_nonneg _)
  have hBoundTend :
      Tendsto
        (fun k : ℕ =>
          ((∑ a : Fin m, |coeffTail a|) / |coeffDominant|) * q ^ k)
        atTop (𝓝 0) :=
    powerMethod_finite_tail_geometric_bound_tendsto_zero
      (m := m) (coeffDominant := coeffDominant)
      (coeffTail := coeffTail) hqNonneg hqLtOne
  exact squeeze_zero hLower hUpper hBoundTend

/-- Norm-level finite-tail power-method bound.  The Euclidean norm of the
finite non-dominant tail, normalized by the dominant scalar magnitude, is
bounded by the initial weighted tail norm ratio times `q^k`. -/
theorem powerMethod_finite_tail_vecNorm2_ratio_le_geometric_of_spectral_ratio_le
    {n m : ℕ} {lambdaDominant coeffDominant q : ℝ}
    {lambdaTail coeffTail : Fin m → ℝ}
    {vTail : Fin m → Fin n → ℝ} (k : ℕ)
    (hCoeff : coeffDominant ≠ 0) (hLambda : lambdaDominant ≠ 0)
    (hRatio : ∀ a : Fin m, |lambdaTail a| / |lambdaDominant| ≤ q) :
    vecNorm2
        (fun i =>
          ∑ a : Fin m, coeffTail a * lambdaTail a ^ k * vTail a i) /
        |coeffDominant * lambdaDominant ^ k| ≤
      ((∑ a : Fin m, |coeffTail a| * vecNorm2 (vTail a)) /
          |coeffDominant|) * q ^ k := by
  have hnorm :
      vecNorm2
          (fun i =>
            ∑ a : Fin m, coeffTail a * lambdaTail a ^ k * vTail a i) ≤
        ∑ a : Fin m,
          vecNorm2
            (fun i => coeffTail a * lambdaTail a ^ k * vTail a i) :=
    vecNorm2_fin_sum_le
      (fun a i => coeffTail a * lambdaTail a ^ k * vTail a i)
  have hden_nonneg :
      0 ≤ |coeffDominant * lambdaDominant ^ k| := abs_nonneg _
  calc
    vecNorm2
        (fun i =>
          ∑ a : Fin m, coeffTail a * lambdaTail a ^ k * vTail a i) /
        |coeffDominant * lambdaDominant ^ k|
        ≤ (∑ a : Fin m,
            vecNorm2
              (fun i => coeffTail a * lambdaTail a ^ k * vTail a i)) /
          |coeffDominant * lambdaDominant ^ k| :=
            div_le_div_of_nonneg_right hnorm hden_nonneg
    _ = (∑ a : Fin m,
            |coeffTail a * lambdaTail a ^ k| * vecNorm2 (vTail a)) /
          |coeffDominant * lambdaDominant ^ k| := by
          congr 1
          apply Finset.sum_congr rfl
          intro a _
          rw [vecNorm2_smul]
    _ = ∑ a : Fin m,
          (|coeffTail a * lambdaTail a ^ k| /
              |coeffDominant * lambdaDominant ^ k|) *
            vecNorm2 (vTail a) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro a _
          ring
    _ ≤ ∑ a : Fin m,
          ((|coeffTail a| / |coeffDominant|) * q ^ k) *
            vecNorm2 (vTail a) := by
          apply Finset.sum_le_sum
          intro a _
          exact mul_le_mul_of_nonneg_right
            (powerMethod_component_abs_ratio_le_geometric_of_spectral_ratio_le
              (k := k) (coeffOther := coeffTail a)
              (lambdaOther := lambdaTail a) hCoeff hLambda (hRatio a))
            (vecNorm2_nonneg (vTail a))
    _ = ∑ a : Fin m,
          ((|coeffTail a| * vecNorm2 (vTail a)) /
              |coeffDominant|) * q ^ k := by
          apply Finset.sum_congr rfl
          intro a _
          ring
    _ = ((∑ a : Fin m, |coeffTail a| * vecNorm2 (vTail a)) /
          |coeffDominant|) * q ^ k := by
          rw [← Finset.sum_mul]
          congr 1
          rw [Finset.sum_div]

/-- Norm-level convergence form for a finite non-dominant tail in the
power-method model. -/
theorem powerMethod_finite_tail_vecNorm2_ratio_tendsto_zero_of_geometric_bound
    {n m : ℕ} {lambdaDominant coeffDominant q : ℝ}
    {lambdaTail coeffTail : Fin m → ℝ}
    {vTail : Fin m → Fin n → ℝ}
    (hCoeff : coeffDominant ≠ 0) (hLambda : lambdaDominant ≠ 0)
    (hRatio : ∀ a : Fin m, |lambdaTail a| / |lambdaDominant| ≤ q)
    (hqNonneg : 0 ≤ q) (hqLtOne : q < 1) :
    Tendsto
      (fun k : ℕ =>
        vecNorm2
            (fun i =>
              ∑ a : Fin m, coeffTail a * lambdaTail a ^ k * vTail a i) /
          |coeffDominant * lambdaDominant ^ k|)
      atTop (𝓝 0) := by
  have hLower :
      ∀ k : ℕ,
        0 ≤
          vecNorm2
              (fun i =>
                ∑ a : Fin m, coeffTail a * lambdaTail a ^ k * vTail a i) /
            |coeffDominant * lambdaDominant ^ k| :=
    fun _ => div_nonneg (vecNorm2_nonneg _) (abs_nonneg _)
  have hUpper :
      ∀ k : ℕ,
        vecNorm2
            (fun i =>
              ∑ a : Fin m, coeffTail a * lambdaTail a ^ k * vTail a i) /
            |coeffDominant * lambdaDominant ^ k| ≤
          ((∑ a : Fin m, |coeffTail a| * vecNorm2 (vTail a)) /
              |coeffDominant|) * q ^ k :=
    fun k =>
      powerMethod_finite_tail_vecNorm2_ratio_le_geometric_of_spectral_ratio_le
        (k := k) hCoeff hLambda hRatio
  have hpow : Tendsto (fun k : ℕ => q ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hqNonneg hqLtOne
  have hBoundTend :
      Tendsto
        (fun k : ℕ =>
          ((∑ a : Fin m, |coeffTail a| * vecNorm2 (vTail a)) /
              |coeffDominant|) * q ^ k)
        atTop (𝓝 0) := by
    simpa using
      hpow.const_mul
        ((∑ a : Fin m, |coeffTail a| * vecNorm2 (vTail a)) /
          |coeffDominant|)
  exact squeeze_zero hLower hUpper hBoundTend

/-- Direct finite-tail power-method residual bound: after subtracting the
dominant component from the actual `k`th unnormalized iterate, the normalized
Euclidean residual is bounded by the weighted finite-tail ratio times `q^k`. -/
theorem powerMethodIterate_dominant_scaled_residual_ratio_le_geometric_of_finite_tail
    {n m : ℕ} {A : Fin n → Fin n → ℝ}
    {lambdaDominant coeffDominant q : ℝ}
    {lambdaTail coeffTail : Fin m → ℝ}
    {vDominant : Fin n → ℝ} {vTail : Fin m → Fin n → ℝ}
    (hDominant : IsRightEigenpair n A lambdaDominant vDominant)
    (hTail : ∀ a : Fin m, IsRightEigenpair n A (lambdaTail a) (vTail a))
    (hCoeff : coeffDominant ≠ 0) (hLambda : lambdaDominant ≠ 0)
    (hRatio : ∀ a : Fin m, |lambdaTail a| / |lambdaDominant| ≤ q)
    (k : ℕ) :
    vecNorm2
        (fun i =>
          powerMethodIterate n A k
              (fun i => coeffDominant * vDominant i +
                ∑ a : Fin m, coeffTail a * vTail a i) i -
            coeffDominant * lambdaDominant ^ k * vDominant i) /
        |coeffDominant * lambdaDominant ^ k| ≤
      ((∑ a : Fin m, |coeffTail a| * vecNorm2 (vTail a)) /
          |coeffDominant|) * q ^ k := by
  have hres :
      vecNorm2
          (fun i =>
            powerMethodIterate n A k
                (fun i => coeffDominant * vDominant i +
                  ∑ a : Fin m, coeffTail a * vTail a i) i -
              coeffDominant * lambdaDominant ^ k * vDominant i) =
        vecNorm2
          (fun i =>
            ∑ a : Fin m, coeffTail a * lambdaTail a ^ k * vTail a i) := by
    congr 1
    ext i
    rw [congrFun
      (powerMethodIterate_dominant_plus_finite_tail
        hDominant hTail k) i]
    ring
  rw [hres]
  exact
    powerMethod_finite_tail_vecNorm2_ratio_le_geometric_of_spectral_ratio_le
      (k := k) hCoeff hLambda hRatio

/-- Direct convergence form of the finite-tail power-method bridge.  Under a
common spectral-ratio bound `0 <= q < 1`, the actual unnormalized iterate,
after subtracting the dominant component and scaling by the dominant scalar
magnitude, has Euclidean norm tending to zero. -/
theorem powerMethodIterate_dominant_scaled_residual_tendsto_zero_of_finite_tail
    {n m : ℕ} {A : Fin n → Fin n → ℝ}
    {lambdaDominant coeffDominant q : ℝ}
    {lambdaTail coeffTail : Fin m → ℝ}
    {vDominant : Fin n → ℝ} {vTail : Fin m → Fin n → ℝ}
    (hDominant : IsRightEigenpair n A lambdaDominant vDominant)
    (hTail : ∀ a : Fin m, IsRightEigenpair n A (lambdaTail a) (vTail a))
    (hCoeff : coeffDominant ≠ 0) (hLambda : lambdaDominant ≠ 0)
    (hRatio : ∀ a : Fin m, |lambdaTail a| / |lambdaDominant| ≤ q)
    (hqNonneg : 0 ≤ q) (hqLtOne : q < 1) :
    Tendsto
      (fun k : ℕ =>
        vecNorm2
            (fun i =>
              powerMethodIterate n A k
                  (fun i => coeffDominant * vDominant i +
                    ∑ a : Fin m, coeffTail a * vTail a i) i -
                coeffDominant * lambdaDominant ^ k * vDominant i) /
          |coeffDominant * lambdaDominant ^ k|)
      atTop (𝓝 0) := by
  have hfun :
      (fun k : ℕ =>
        vecNorm2
            (fun i =>
              powerMethodIterate n A k
                  (fun i => coeffDominant * vDominant i +
                    ∑ a : Fin m, coeffTail a * vTail a i) i -
                coeffDominant * lambdaDominant ^ k * vDominant i) /
          |coeffDominant * lambdaDominant ^ k|) =
        fun k : ℕ =>
          vecNorm2
              (fun i =>
                ∑ a : Fin m, coeffTail a * lambdaTail a ^ k * vTail a i) /
            |coeffDominant * lambdaDominant ^ k| := by
    funext k
    congr 1
    congr 1
    ext i
    rw [congrFun
      (powerMethodIterate_dominant_plus_finite_tail
        hDominant hTail k) i]
    ring
  rw [hfun]
  exact
    powerMethod_finite_tail_vecNorm2_ratio_tendsto_zero_of_geometric_bound
      hCoeff hLambda hRatio hqNonneg hqLtOne

/-- A reusable certificate that a starting vector has a nonzero dominant
eigencomponent plus a finite non-dominant tail with a common spectral-ratio
bound.  This is the exact handoff needed before the generic finite-tail
power-method convergence theorem can be applied to a concrete stored matrix. -/
structure PowerMethodDominantFiniteTailCertificate
    (n m : ℕ) (A : Fin n → Fin n → ℝ) (x0 : Fin n → ℝ) where
  lambdaDominant : ℝ
  coeffDominant : ℝ
  q : ℝ
  lambdaTail : Fin m → ℝ
  coeffTail : Fin m → ℝ
  vDominant : Fin n → ℝ
  vTail : Fin m → Fin n → ℝ
  start_decomposition :
    x0 = fun i => coeffDominant * vDominant i +
      ∑ a : Fin m, coeffTail a * vTail a i
  dominant_eigenpair : IsRightEigenpair n A lambdaDominant vDominant
  tail_eigenpairs :
    ∀ a : Fin m, IsRightEigenpair n A (lambdaTail a) (vTail a)
  coeffDominant_ne_zero : coeffDominant ≠ 0
  lambdaDominant_ne_zero : lambdaDominant ≠ 0
  tail_spectral_ratio_le :
    ∀ a : Fin m, |lambdaTail a| / |lambdaDominant| ≤ q
  q_nonneg : 0 ≤ q
  q_lt_one : q < 1

/-- A dominant finite-tail certificate immediately gives the scaled
power-method residual convergence theorem for the certified starting vector. -/
theorem PowerMethodDominantFiniteTailCertificate.scaled_residual_tendsto_zero
    {n m : ℕ} {A : Fin n → Fin n → ℝ} {x0 : Fin n → ℝ}
    (cert : PowerMethodDominantFiniteTailCertificate n m A x0) :
    Tendsto
      (fun k : ℕ =>
        vecNorm2
            (fun i =>
              powerMethodIterate n A k x0 i -
                cert.coeffDominant * cert.lambdaDominant ^ k *
                  cert.vDominant i) /
          |cert.coeffDominant * cert.lambdaDominant ^ k|)
      atTop (𝓝 0) := by
  simpa [cert.start_decomposition] using
    powerMethodIterate_dominant_scaled_residual_tendsto_zero_of_finite_tail
      cert.dominant_eigenpair cert.tail_eigenpairs
      cert.coeffDominant_ne_zero cert.lambdaDominant_ne_zero
      cert.tail_spectral_ratio_le cert.q_nonneg cert.q_lt_one

/-- A nonzero scalar multiple of a right eigenvector is the same right
eigenvector direction. -/
theorem isRightEigenpair_smul
    {n : ℕ} {A : Fin n → Fin n → ℝ} {lambda : ℝ} {x : Fin n → ℝ}
    (hx : IsRightEigenpair n A lambda x) {c : ℝ} (hc : c ≠ 0) :
    IsRightEigenpair n A lambda (fun i => c * x i) := by
  rcases hx.1 with ⟨i0, hi0⟩
  refine ⟨⟨i0, mul_ne_zero hc hi0⟩, ?_⟩
  intro i
  rw [matMulVec_smul_right]
  rw [hx.2 i]
  ring

/-- Exact version of the "harmless direction" part of the inverse-iteration
discussion: if the shifted-solve error is parallel to the required eigenvector,
then the returned vector is still in that eigenvector direction, provided the
resulting scalar is nonzero. This does not prove that floating-point solve
errors are parallel; it records why such an error is harmless once supplied. -/
theorem inverseIteration_parallel_error_output_isRightEigenpair
    {n : ℕ} {A : Fin n → Fin n → ℝ} {lambda mu : ℝ}
    {x err : Fin n → ℝ} (hx : IsRightEigenpair n A lambda x)
    (eta : ℝ) (herr : err = fun i => eta * x i)
    (hcoeff : (lambda - mu)⁻¹ + eta ≠ 0) :
    IsRightEigenpair n A lambda
      (fun i => (lambda - mu)⁻¹ * x i + err i) := by
  have hout :
      (fun i => (lambda - mu)⁻¹ * x i + err i) =
        fun i => ((lambda - mu)⁻¹ + eta) * x i := by
    ext i
    rw [herr]
    ring
  rw [hout]
  exact isRightEigenpair_smul hx hcoeff

/-- Eigen-residual vector `A*y - lambda*y`.  This is zero exactly on exact
right-eigenvector directions, and is the quantity controlled by the
near-parallel inverse-iteration bridge below. -/
noncomputable def eigenResidualVec (n : ℕ) (A : Fin n → Fin n → ℝ)
    (lambda : ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => matMulVec n A y i - lambda * y i

/-- Adding any scalar multiple of an exact right eigenvector does not change
the eigen-residual of the nonparallel component. -/
theorem eigenResidualVec_add_parallel_eq
    {n : ℕ} {A : Fin n → Fin n → ℝ} {lambda : ℝ}
    {x r : Fin n → ℝ} (hx : IsRightEigenpair n A lambda x) (c : ℝ) :
    eigenResidualVec n A lambda (fun i => c * x i + r i) =
      eigenResidualVec n A lambda r := by
  ext i
  unfold eigenResidualVec matMulVec
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hsum :
      (∑ j : Fin n, A i j * (c * x j)) =
        c * ∑ j : Fin n, A i j * x j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hx_i : (∑ j : Fin n, A i j * x j) = lambda * x i := by
    simpa [matMulVec] using hx.2 i
  rw [hsum, hx_i]
  ring

/-- Operator-norm bound for the eigen-residual of any vector. -/
theorem eigenResidualVec_norm_le_opNorm_add_abs
    {n : ℕ} (A : Fin n → Fin n → ℝ) (lambda A_norm : ℝ)
    (r : Fin n → ℝ) (hA : opNorm2Le A A_norm) :
    vecNorm2 (eigenResidualVec n A lambda r) ≤
      (A_norm + |lambda|) * vecNorm2 r := by
  unfold eigenResidualVec
  have htri :
      vecNorm2 (fun i => matMulVec n A r i - lambda * r i) ≤
        vecNorm2 (matMulVec n A r) + vecNorm2 (fun i => (-lambda) * r i) := by
    simpa [sub_eq_add_neg, neg_mul] using
      (vecNorm2_add_le (matMulVec n A r) (fun i => (-lambda) * r i))
  have hsmul : vecNorm2 (fun i => (-lambda) * r i) = |lambda| * vecNorm2 r := by
    rw [vecNorm2_smul]
    simp
  calc
    vecNorm2 (fun i => matMulVec n A r i - lambda * r i)
        ≤ vecNorm2 (matMulVec n A r) + vecNorm2 (fun i => (-lambda) * r i) :=
          htri
    _ ≤ A_norm * vecNorm2 r + |lambda| * vecNorm2 r := by
          exact add_le_add (hA r) (le_of_eq hsmul)
    _ = (A_norm + |lambda|) * vecNorm2 r := by ring

/-- Near-parallel inverse-iteration bridge: if the shifted-solve error splits
as a harmless parallel component plus a residual component `r`, then the
eigen-residual of the returned vector depends only on `r`. -/
theorem inverseIteration_near_parallel_error_eigenResidual_eq
    {n : ℕ} {A : Fin n → Fin n → ℝ} {lambda mu : ℝ}
    {x err r : Fin n → ℝ} (hx : IsRightEigenpair n A lambda x)
    (eta : ℝ) (herr : err = fun i => eta * x i + r i) :
    eigenResidualVec n A lambda
        (fun i => (lambda - mu)⁻¹ * x i + err i) =
      eigenResidualVec n A lambda r := by
  subst err
  have hfun :
      (fun i => (lambda - mu)⁻¹ * x i + (eta * x i + r i)) =
        fun i => ((lambda - mu)⁻¹ + eta) * x i + r i := by
    ext i
    ring
  have h :=
    eigenResidualVec_add_parallel_eq
      (n := n) (A := A) (lambda := lambda) (x := x) (r := r)
      hx ((lambda - mu)⁻¹ + eta)
  simpa [hfun] using h

/-- Quantitative near-parallel inverse-iteration bridge: after decomposing the
shifted-solve error into a parallel part and residual `r`, the returned vector's
eigen-residual is bounded by `(||A||₂ + |lambda|) ||r||₂` under the repository's
operator-2 predicate surface.  A concrete floating-point shifted solve still
has to supply the decomposition and a bound on `r`. -/
theorem inverseIteration_near_parallel_error_eigenResidual_norm_le
    {n : ℕ} {A : Fin n → Fin n → ℝ} {lambda mu A_norm : ℝ}
    {x err r : Fin n → ℝ} (hx : IsRightEigenpair n A lambda x)
    (eta : ℝ) (herr : err = fun i => eta * x i + r i)
    (hA : opNorm2Le A A_norm) :
    vecNorm2
        (eigenResidualVec n A lambda
          (fun i => (lambda - mu)⁻¹ * x i + err i)) ≤
      (A_norm + |lambda|) * vecNorm2 r := by
  rw [inverseIteration_near_parallel_error_eigenResidual_eq hx eta herr]
  exact eigenResidualVec_norm_le_opNorm_add_abs A lambda A_norm r hA

/-- Source-certificate composition for inverse iteration.  If a shifted-solve
error is obtained by applying a left inverse of `A - mu I` to a residual that
has an eigenbasis expansion, and the non-target coefficients and shift
distances satisfy explicit component/shift ratio bounds, then the eigen-residual
of the returned inverse-iteration vector is controlled by the normalized
non-target spectral tail.  This is a solver-certificate target for the
Parlett/Golub--Van Loan route: the source theorem still has to supply the
coefficient and separation hypotheses, but the local algebraic handoff is now
closed. -/
theorem
    inverseIteration_shiftedSolve_error_eigenResidual_norm_le_of_residual_eigenbasis_component_shift_ratios
    {m n : ℕ} {A B : Fin n → Fin n → ℝ} {mu A_norm : ℝ}
    {lambda : Fin m → ℝ} {v : Fin m → Fin n → ℝ}
    (target : Fin m) (coeff beta sigma : Fin m → ℝ)
    (hEig : ∀ a : Fin m, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin m, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_bound_nonneg : 0 ≤ A_norm + |lambda target|)
    (hscale :
      0 <
        |coeff target| * |(lambda target - mu)⁻¹| *
          vecNorm2 (v target))
    (hbeta_nonneg :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) → 0 ≤ beta a)
    (hcoeff_ratio :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) →
        |coeff a| * vecNorm2 (v a) ≤
          beta a * (|coeff target| * vecNorm2 (v target)))
    (hshift_ratio :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) →
        |(lambda a - mu)⁻¹| ≤
          sigma a * |(lambda target - mu)⁻¹|) :
    vecNorm2
        (eigenResidualVec n A (lambda target)
          (fun i =>
            (lambda target - mu)⁻¹ * v target i +
              matMulVec n B (fun i => ∑ a : Fin m, coeff a * v a i) i)) ≤
      (A_norm + |lambda target|) *
        (Finset.sum (Finset.univ.erase target)
            (fun a => beta a * sigma a) *
          (|coeff target| * |(lambda target - mu)⁻¹| *
            vecNorm2 (v target))) := by
  classical
  let residual : Fin n → ℝ := fun i => ∑ a : Fin m, coeff a * v a i
  let tail : Fin n → ℝ :=
    inverseIterationShiftedInverseSpectralTail target lambda mu v coeff
  have herr :
      matMulVec n B residual =
        fun i =>
          (coeff target * (lambda target - mu)⁻¹) * v target i +
            tail i := by
    ext i
    have h :=
      congrFun
        (inverseIteration_shiftedInverse_eigenvector_expansion_target_tail_of_leftInverse
          (n := n) (A := A) (B := B) (mu := mu)
          (lambda := lambda) (v := v) hEig hshift hB coeff target) i
    dsimp [residual, tail] at h ⊢
    rw [h]
  have hnear :
      vecNorm2
          (eigenResidualVec n A (lambda target)
            (fun i =>
              (lambda target - mu)⁻¹ * v target i +
                matMulVec n B residual i)) ≤
        (A_norm + |lambda target|) * vecNorm2 tail := by
    simpa [tail] using
      (inverseIteration_near_parallel_error_eigenResidual_norm_le
        (n := n) (A := A) (lambda := lambda target) (mu := mu)
        (A_norm := A_norm) (x := v target)
        (err := matMulVec n B residual) (r := tail)
        (hEig target) (coeff target * (lambda target - mu)⁻¹) herr hA)
  have hratio :
      vecNorm2
          (inverseIterationShiftedInverseSpectralTail target lambda mu v coeff) /
          (|coeff target| * |(lambda target - mu)⁻¹| *
            vecNorm2 (v target)) ≤
        Finset.sum (Finset.univ.erase target) (fun a => beta a * sigma a) :=
    inverseIterationShiftedInverseSpectralTail_norm_div_target_scale_le_sum_of_component_shift_ratios
      target lambda mu v coeff beta sigma hscale hbeta_nonneg hcoeff_ratio
      hshift_ratio
  have htail :
      vecNorm2 tail ≤
        Finset.sum (Finset.univ.erase target) (fun a => beta a * sigma a) *
          (|coeff target| * |(lambda target - mu)⁻¹| *
            vecNorm2 (v target)) := by
    have hmul := (div_le_iff₀ hscale).mp hratio
    simpa [tail] using hmul
  exact le_trans
    (by simpa [residual] using hnear)
    (mul_le_mul_of_nonneg_left htail hA_bound_nonneg)

/-- Source-shaped variant of
`inverseIteration_shiftedSolve_error_eigenResidual_norm_le_of_residual_eigenbasis_component_shift_ratios`
where the nonnegativity side condition is stated as the ordinary operator-norm
bound `0 <= A_norm`. -/
theorem
    inverseIteration_shiftedSolve_error_eigenResidual_norm_le_of_residual_eigenbasis_component_shift_ratios_of_A_norm_nonneg
    {m n : ℕ} {A B : Fin n → Fin n → ℝ} {mu A_norm : ℝ}
    {lambda : Fin m → ℝ} {v : Fin m → Fin n → ℝ}
    (target : Fin m) (coeff beta sigma : Fin m → ℝ)
    (hEig : ∀ a : Fin m, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin m, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (hscale :
      0 <
        |coeff target| * |(lambda target - mu)⁻¹| *
          vecNorm2 (v target))
    (hbeta_nonneg :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) → 0 ≤ beta a)
    (hcoeff_ratio :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) →
        |coeff a| * vecNorm2 (v a) ≤
          beta a * (|coeff target| * vecNorm2 (v target)))
    (hshift_ratio :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) →
        |(lambda a - mu)⁻¹| ≤
          sigma a * |(lambda target - mu)⁻¹|) :
    vecNorm2
        (eigenResidualVec n A (lambda target)
          (fun i =>
            (lambda target - mu)⁻¹ * v target i +
              matMulVec n B (fun i => ∑ a : Fin m, coeff a * v a i) i)) ≤
      (A_norm + |lambda target|) *
        (Finset.sum (Finset.univ.erase target)
            (fun a => beta a * sigma a) *
          (|coeff target| * |(lambda target - mu)⁻¹| *
            vecNorm2 (v target))) := by
  exact
    inverseIteration_shiftedSolve_error_eigenResidual_norm_le_of_residual_eigenbasis_component_shift_ratios
      (n := n) (A := A) (B := B) (mu := mu) (A_norm := A_norm)
      (lambda := lambda) (v := v) target coeff beta sigma hEig hshift hB hA
      (add_nonneg hA_norm_nonneg (abs_nonneg (lambda target))) hscale
      hbeta_nonneg hcoeff_ratio hshift_ratio

/-- Source-shaped inverse-iteration certificate using ordinary shift-distance
data.  This specializes
`inverseIteration_shiftedSolve_error_eigenResidual_norm_le_of_residual_eigenbasis_component_shift_ratios`
by deriving the reciprocal shift-ratio hypothesis from a target shift radius
and a uniform non-target gap.  The remaining source/certificate obligations are
the eigenbasis residual expansion and coefficient/eigenvector norm ratios. -/
theorem
    inverseIteration_shiftedSolve_error_eigenResidual_norm_le_of_residual_eigenbasis_component_target_radius_gap
    {m n : ℕ} {A B : Fin n → Fin n → ℝ} {mu A_norm radius sep : ℝ}
    {lambda : Fin m → ℝ} {v : Fin m → Fin n → ℝ}
    (target : Fin m) (coeff beta : Fin m → ℝ)
    (hEig : ∀ a : Fin m, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin m, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_bound_nonneg : 0 ≤ A_norm + |lambda target|)
    (hscale :
      0 <
        |coeff target| * |(lambda target - mu)⁻¹| *
          vecNorm2 (v target))
    (hsep_pos : 0 < sep)
    (htarget_pos : 0 < |lambda target - mu|)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|)
    (hbeta_nonneg :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) → 0 ≤ beta a)
    (hcoeff_ratio :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) →
        |coeff a| * vecNorm2 (v a) ≤
          beta a * (|coeff target| * vecNorm2 (v target))) :
    vecNorm2
        (eigenResidualVec n A (lambda target)
          (fun i =>
            (lambda target - mu)⁻¹ * v target i +
              matMulVec n B (fun i => ∑ a : Fin m, coeff a * v a i) i)) ≤
      (A_norm + |lambda target|) *
        ((Finset.sum (Finset.univ.erase target)
            (fun a => beta a * (radius / sep))) *
          (|coeff target| * |(lambda target - mu)⁻¹| *
            vecNorm2 (v target))) := by
  exact
    inverseIteration_shiftedSolve_error_eigenResidual_norm_le_of_residual_eigenbasis_component_shift_ratios
      (n := n) (A := A) (B := B) (mu := mu) (A_norm := A_norm)
      (lambda := lambda) (v := v) target coeff beta (fun _ => radius / sep)
      hEig hshift hB hA hA_bound_nonneg hscale hbeta_nonneg hcoeff_ratio
      (inverseIteration_shift_ratio_of_uniform_target_radius_and_gap
        target lambda mu radius sep hsep_pos htarget_pos htarget hsep)

/-- Source-shaped radius/gap variant with the norm-bound side condition stated as
`0 <= A_norm`. -/
theorem
    inverseIteration_shiftedSolve_error_eigenResidual_norm_le_of_residual_eigenbasis_component_target_radius_gap_of_A_norm_nonneg
    {m n : ℕ} {A B : Fin n → Fin n → ℝ} {mu A_norm radius sep : ℝ}
    {lambda : Fin m → ℝ} {v : Fin m → Fin n → ℝ}
    (target : Fin m) (coeff beta : Fin m → ℝ)
    (hEig : ∀ a : Fin m, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin m, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (hscale :
      0 <
        |coeff target| * |(lambda target - mu)⁻¹| *
          vecNorm2 (v target))
    (hsep_pos : 0 < sep)
    (htarget_pos : 0 < |lambda target - mu|)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|)
    (hbeta_nonneg :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) → 0 ≤ beta a)
    (hcoeff_ratio :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) →
        |coeff a| * vecNorm2 (v a) ≤
          beta a * (|coeff target| * vecNorm2 (v target))) :
    vecNorm2
        (eigenResidualVec n A (lambda target)
          (fun i =>
            (lambda target - mu)⁻¹ * v target i +
              matMulVec n B (fun i => ∑ a : Fin m, coeff a * v a i) i)) ≤
      (A_norm + |lambda target|) *
        ((Finset.sum (Finset.univ.erase target)
            (fun a => beta a * (radius / sep))) *
          (|coeff target| * |(lambda target - mu)⁻¹| *
            vecNorm2 (v target))) := by
  exact
    inverseIteration_shiftedSolve_error_eigenResidual_norm_le_of_residual_eigenbasis_component_target_radius_gap
      (n := n) (A := A) (B := B) (mu := mu) (A_norm := A_norm)
      (radius := radius) (sep := sep) (lambda := lambda) (v := v)
      target coeff beta hEig hshift hB hA
      (add_nonneg hA_norm_nonneg (abs_nonneg (lambda target))) hscale
      hsep_pos htarget_pos htarget hsep hbeta_nonneg hcoeff_ratio

/-- Perturbed shifted-solve identity for the inverse-iteration certificate
route.  If `yhat` solves `(A - mu I + DeltaS)yhat = v_target` and
`-DeltaS*yhat` has the supplied eigenbasis expansion, then `yhat` is the exact
target shifted-inverse output plus the left-inverse image of that residual
expansion.  The minus sign is the usual residual sign:
`(A - mu I)yhat = v_target - DeltaS*yhat`. -/
theorem inverseIteration_perturbed_shiftedSolve_eq_exact_add_leftInverse_residual_expansion
    {m n : ℕ} {A B DeltaS : Fin n → Fin n → ℝ} {mu : ℝ}
    {lambda : Fin m → ℝ} {v : Fin m → Fin n → ℝ}
    (target : Fin m) (coeff : Fin m → ℝ) (yhat : Fin n → ℝ)
    (hEig : ∀ a : Fin m, IsRightEigenpair n A (lambda a) (v a))
    (hshift_target : lambda target - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hPerturbed :
      ∀ i : Fin n,
        ∑ j : Fin n,
          (inverseIterationShiftedMatrix n A mu i j + DeltaS i j) *
            yhat j =
            v target i)
    (hresExpansion :
      (fun i : Fin n => -matMulVec n DeltaS yhat i) =
        fun i => ∑ a : Fin m, coeff a * v a i) :
    yhat =
      fun i =>
        (lambda target - mu)⁻¹ * v target i +
          matMulVec n B (fun i => ∑ a : Fin m, coeff a * v a i) i := by
  let S : Fin n → Fin n → ℝ := inverseIterationShiftedMatrix n A mu
  have hS_y :
      matMulVec n S yhat =
        fun i => v target i + ∑ a : Fin m, coeff a * v a i := by
    ext i
    have hpert_i :
        ∑ j : Fin n, (S i j + DeltaS i j) * yhat j =
          v target i := by
      simpa [S] using hPerturbed i
    have hexp_i := congrFun hresExpansion i
    unfold matMulVec at hpert_i hexp_i ⊢
    have hsplit :
        ∑ j : Fin n, (S i j + DeltaS i j) * yhat j =
          ∑ j : Fin n, S i j * yhat j +
            ∑ j : Fin n, DeltaS i j * yhat j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsplit] at hpert_i
    linarith
  have hmat : matMul n B S = idMatrix n := by
    ext i j
    exact hB i j
  have hy_eq : yhat = matMulVec n B (matMulVec n S yhat) := by
    ext i
    calc
      yhat i = matMulVec n (idMatrix n) yhat i := by
        rw [matMulVec_id]
      _ = matMulVec n (matMul n B S) yhat i := by
        rw [hmat]
      _ = matMulVec n B (matMulVec n S yhat) i := by
        rw [matMulVec_matMul]
  have hvtarget :
      matMulVec n B (v target) =
        fun i => (lambda target - mu)⁻¹ * v target i :=
    inverseIteration_shiftedInverse_mul_eigenvector_of_leftInverse
      (hEig target) hshift_target (by simpa [S] using hB)
  calc
    yhat = matMulVec n B (matMulVec n S yhat) := hy_eq
    _ = matMulVec n B
          (fun i => v target i + ∑ a : Fin m, coeff a * v a i) := by
        rw [hS_y]
    _ = fun i =>
          (lambda target - mu)⁻¹ * v target i +
            matMulVec n B (fun i => ∑ a : Fin m, coeff a * v a i) i := by
        rw [matMulVec_add_right, hvtarget]

/-- Source-facing near-parallel decomposition for inverse iteration.  If a
modeled shifted solve `(A - mu I + DeltaS)yhat = v_target` has backward-error
action `-DeltaS*yhat` expanded in the right eigenbasis, and the supplied
component and shift-distance estimates make the non-target spectral tail small,
then the returned vector is the exact target shifted-inverse vector plus a
parallel target-eigenvector component and a quantitatively bounded tail.

This is the formal shape of the source phrase that the solve error lies almost
entirely in the required eigenvector direction.  It is still a certificate
theorem: a concrete rounded solver or the cited Parlett/Golub--Van Loan theorem
must supply the perturbation, expansion, and separation hypotheses. -/
theorem
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_eigenbasis_component_target_radius_gap
    {m n : ℕ} {A B DeltaS : Fin n → Fin n → ℝ}
    {mu radius sep : ℝ}
    {lambda : Fin m → ℝ} {v : Fin m → Fin n → ℝ}
    (target : Fin m) (coeff beta : Fin m → ℝ) (yhat : Fin n → ℝ)
    (hEig : ∀ a : Fin m, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin m, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hscale :
      0 <
        |coeff target| * |(lambda target - mu)⁻¹| *
          vecNorm2 (v target))
    (hsep_pos : 0 < sep)
    (htarget_pos : 0 < |lambda target - mu|)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|)
    (hbeta_nonneg :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) → 0 ≤ beta a)
    (hcoeff_ratio :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) →
        |coeff a| * vecNorm2 (v a) ≤
          beta a * (|coeff target| * vecNorm2 (v target)))
    (hPerturbed :
      ∀ i : Fin n,
        ∑ j : Fin n,
          (inverseIterationShiftedMatrix n A mu i j + DeltaS i j) *
            yhat j =
            v target i)
    (hresExpansion :
      (fun i : Fin n => -matMulVec n DeltaS yhat i) =
        fun i => ∑ a : Fin m, coeff a * v a i) :
    ∃ eta : ℝ, ∃ r : Fin n → ℝ,
      (yhat =
        fun i =>
          (lambda target - mu)⁻¹ * v target i +
            (eta * v target i + r i)) ∧
      vecNorm2 r ≤
        Finset.sum (Finset.univ.erase target)
            (fun a => beta a * (radius / sep)) *
          (|coeff target| * |(lambda target - mu)⁻¹| *
            vecNorm2 (v target)) := by
  classical
  let residual : Fin n → ℝ := fun i => ∑ a : Fin m, coeff a * v a i
  let tail : Fin n → ℝ :=
    inverseIterationShiftedInverseSpectralTail target lambda mu v coeff
  refine ⟨coeff target * (lambda target - mu)⁻¹, tail, ?_, ?_⟩
  · have hy :=
      inverseIteration_perturbed_shiftedSolve_eq_exact_add_leftInverse_residual_expansion
        target coeff yhat hEig (hshift target) hB hPerturbed hresExpansion
    have htail :
        matMulVec n B residual =
          fun i =>
            coeff target * (lambda target - mu)⁻¹ * v target i +
              tail i := by
      ext i
      have h :=
        congrFun
          (inverseIteration_shiftedInverse_eigenvector_expansion_target_tail_of_leftInverse
            (n := n) (A := A) (B := B) (mu := mu)
            (lambda := lambda) (v := v) hEig hshift hB coeff target) i
      simpa [residual, tail] using h
    ext i
    have hy_i := congrFun hy i
    have htail_i := congrFun htail i
    calc
      yhat i =
          (lambda target - mu)⁻¹ * v target i +
            matMulVec n B residual i := by
              simpa [residual] using hy_i
      _ =
          (lambda target - mu)⁻¹ * v target i +
            (coeff target * (lambda target - mu)⁻¹ * v target i +
              tail i) := by
              rw [htail_i]
      _ =
          (lambda target - mu)⁻¹ * v target i +
            ((coeff target * (lambda target - mu)⁻¹) * v target i +
              tail i) := by
              ring
  · have hratio :
      vecNorm2
          (inverseIterationShiftedInverseSpectralTail target lambda mu v coeff) /
          (|coeff target| * |(lambda target - mu)⁻¹| *
            vecNorm2 (v target)) ≤
        Finset.sum (Finset.univ.erase target)
          (fun a => beta a * (radius / sep)) :=
      inverseIterationShiftedInverseSpectralTail_norm_div_target_scale_le_sum_of_component_shift_ratios
        target lambda mu v coeff beta (fun _ => radius / sep) hscale
        hbeta_nonneg hcoeff_ratio
        (inverseIteration_shift_ratio_of_uniform_target_radius_and_gap
          target lambda mu radius sep hsep_pos htarget_pos htarget hsep)
    have hmul := (div_le_iff₀ hscale).mp hratio
    simpa [tail] using hmul

/-- Absolute-budget source-facing near-parallel decomposition for inverse
iteration.  This is the same perturbed shifted-solve algebra as
`inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_eigenbasis_component_target_radius_gap`,
but it accepts direct non-target shifted-inverse budgets instead of normalizing
by a positive target coefficient scale.  This matches a future source theorem
or solver certificate that proves the non-target tail is small in absolute
norm, and keeps the still-missing perturbation theorem visible rather than
assuming a historical shifted-solve trace. -/
theorem
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_eigenbasis_component_absolute_budget
    {m n : ℕ} {A B DeltaS : Fin n → Fin n → ℝ}
    {mu : ℝ}
    {lambda : Fin m → ℝ} {v : Fin m → Fin n → ℝ}
    (target : Fin m) (coeff budget : Fin m → ℝ) (yhat : Fin n → ℝ)
    (hEig : ∀ a : Fin m, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin m, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hbudget :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) →
        |coeff a| * |(lambda a - mu)⁻¹| * vecNorm2 (v a) ≤ budget a)
    (hPerturbed :
      ∀ i : Fin n,
        ∑ j : Fin n,
          (inverseIterationShiftedMatrix n A mu i j + DeltaS i j) *
            yhat j =
            v target i)
    (hresExpansion :
      (fun i : Fin n => -matMulVec n DeltaS yhat i) =
        fun i => ∑ a : Fin m, coeff a * v a i) :
    ∃ eta : ℝ, ∃ r : Fin n → ℝ,
      (yhat =
        fun i =>
          (lambda target - mu)⁻¹ * v target i +
            (eta * v target i + r i)) ∧
      vecNorm2 r ≤ Finset.sum (Finset.univ.erase target) budget := by
  classical
  let residual : Fin n → ℝ := fun i => ∑ a : Fin m, coeff a * v a i
  let tail : Fin n → ℝ :=
    inverseIterationShiftedInverseSpectralTail target lambda mu v coeff
  refine ⟨coeff target * (lambda target - mu)⁻¹, tail, ?_, ?_⟩
  · have hy :=
      inverseIteration_perturbed_shiftedSolve_eq_exact_add_leftInverse_residual_expansion
        target coeff yhat hEig (hshift target) hB hPerturbed hresExpansion
    have htail :
        matMulVec n B residual =
          fun i =>
            coeff target * (lambda target - mu)⁻¹ * v target i +
              tail i := by
      ext i
      have h :=
        congrFun
          (inverseIteration_shiftedInverse_eigenvector_expansion_target_tail_of_leftInverse
            (n := n) (A := A) (B := B) (mu := mu)
            (lambda := lambda) (v := v) hEig hshift hB coeff target) i
      simpa [residual, tail] using h
    ext i
    have hy_i := congrFun hy i
    have htail_i := congrFun htail i
    calc
      yhat i =
          (lambda target - mu)⁻¹ * v target i +
            matMulVec n B residual i := by
              simpa [residual] using hy_i
      _ =
          (lambda target - mu)⁻¹ * v target i +
            (coeff target * (lambda target - mu)⁻¹ * v target i +
              tail i) := by
              rw [htail_i]
      _ =
          (lambda target - mu)⁻¹ * v target i +
            ((coeff target * (lambda target - mu)⁻¹) * v target i +
              tail i) := by
              ring
  · simpa [tail] using
      (inverseIterationShiftedInverseSpectralTail_norm_le_of_component_budget
        target lambda mu v coeff budget hbudget)

/-- Absolute residual/gap near-parallel decomposition wrapper.  A residual norm
bound, an eigenbasis-inverse operator-norm certificate, and a uniform
non-target separation gap supply direct non-target shifted-inverse budgets for
the absolute-budget handoff. -/
theorem
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_inverse_opNorm_residual_gap_absolute
    {n : ℕ} {A B DeltaS V V_inv : Fin n → Fin n → ℝ}
    {mu V_inv_norm residualNorm sep : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (hres_norm :
      vecNorm2 (fun i : Fin n => -matMulVec n DeltaS yhat i) ≤ residualNorm)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hsep_pos : 0 < sep)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|)
    (hPerturbed :
      ∀ i : Fin n,
        ∑ j : Fin n,
          (inverseIterationShiftedMatrix n A mu i j + DeltaS i j) *
            yhat j =
            v target i) :
    ∃ eta : ℝ, ∃ r : Fin n → ℝ,
      (yhat =
        fun i =>
          (lambda target - mu)⁻¹ * v target i +
            (eta * v target i + r i)) ∧
      vecNorm2 r ≤
        Finset.sum (Finset.univ.erase target)
          (fun a =>
            ((V_inv_norm * residualNorm) * (1 / sep)) * vecNorm2 (v a)) := by
  let residual : Fin n → ℝ := fun i => -matMulVec n DeltaS yhat i
  let coeff : Fin n → ℝ := matMulVec n V_inv residual
  have hresExpansion :
      residual = fun i => ∑ a : Fin n, coeff a * v a i := by
    simpa [residual, coeff] using
      (eigenbasis_residual_expansion_of_rightInverse
        v hV_cols hV_inv residual)
  have hbudget :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        |coeff a| * |(lambda a - mu)⁻¹| * vecNorm2 (v a) ≤
          ((V_inv_norm * residualNorm) * (1 / sep)) * vecNorm2 (v a) := by
    simpa [residual, coeff] using
      (inverseIteration_eigenbasis_shiftedInverse_component_budget_of_inverse_opNorm_residual_gap
        target lambda mu v V_inv residual V_inv_norm residualNorm sep
        hV_inv_op hV_inv_norm_nonneg hres_norm hsep_pos hsep)
  simpa [residual, coeff] using
    (inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_eigenbasis_component_absolute_budget
      (n := n) (A := A) (B := B) (DeltaS := DeltaS) (mu := mu)
      (lambda := lambda) (v := v) target coeff
      (fun a =>
        ((V_inv_norm * residualNorm) * (1 / sep)) * vecNorm2 (v a))
      yhat hEig hshift hB hbudget hPerturbed hresExpansion)

/-- Perturbed shifted-solve certificate for inverse iteration.  If the modeled
computed vector `yhat` solves `(A - mu I + DeltaS)yhat = v_target`, the
backward-error action `-DeltaS*yhat` has an eigenbasis expansion with supplied
component/eigenvector ratios, and the shift satisfies a target-radius/non-target
gap condition, then the actual returned vector's eigen-residual is bounded by
the source-shaped finite tail budget.  This reduces a concrete solver route to
proving the exposed perturbation, expansion, and ratio hypotheses; it is not a
hidden proof of a specific floating-point solver. -/
theorem
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_eigenbasis_component_target_radius_gap
    {m n : ℕ} {A B DeltaS : Fin n → Fin n → ℝ}
    {mu A_norm radius sep : ℝ}
    {lambda : Fin m → ℝ} {v : Fin m → Fin n → ℝ}
    (target : Fin m) (coeff beta : Fin m → ℝ) (yhat : Fin n → ℝ)
    (hEig : ∀ a : Fin m, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin m, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_bound_nonneg : 0 ≤ A_norm + |lambda target|)
    (hscale :
      0 <
        |coeff target| * |(lambda target - mu)⁻¹| *
          vecNorm2 (v target))
    (hsep_pos : 0 < sep)
    (htarget_pos : 0 < |lambda target - mu|)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|)
    (hbeta_nonneg :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) → 0 ≤ beta a)
    (hcoeff_ratio :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) →
        |coeff a| * vecNorm2 (v a) ≤
          beta a * (|coeff target| * vecNorm2 (v target)))
    (hPerturbed :
      ∀ i : Fin n,
        ∑ j : Fin n,
          (inverseIterationShiftedMatrix n A mu i j + DeltaS i j) *
            yhat j =
            v target i)
    (hresExpansion :
      (fun i : Fin n => -matMulVec n DeltaS yhat i) =
        fun i => ∑ a : Fin m, coeff a * v a i) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) *
        (Finset.sum (Finset.univ.erase target)
            (fun a => beta a * (radius / sep)) *
          (|coeff target| * |(lambda target - mu)⁻¹| *
            vecNorm2 (v target))) := by
  have hy :=
    inverseIteration_perturbed_shiftedSolve_eq_exact_add_leftInverse_residual_expansion
      target coeff yhat hEig (hshift target) hB hPerturbed hresExpansion
  rw [hy]
  exact
    inverseIteration_shiftedSolve_error_eigenResidual_norm_le_of_residual_eigenbasis_component_target_radius_gap
      (n := n) (A := A) (B := B) (mu := mu) (A_norm := A_norm)
      (radius := radius) (sep := sep) (lambda := lambda) (v := v)
      target coeff beta hEig hshift hB hA hA_bound_nonneg hscale
      hsep_pos htarget_pos htarget hsep hbeta_nonneg hcoeff_ratio

/-- Absolute-budget perturbed shifted-solve residual certificate.  A source
theorem or concrete solver model may supply direct bounds for each non-target
shifted-inverse component; the local algebra then bounds the returned vector's
eigen-residual without a positive target-scale hypothesis. -/
theorem
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_eigenbasis_component_absolute_budget
    {m n : ℕ} {A B DeltaS : Fin n → Fin n → ℝ}
    {mu A_norm : ℝ}
    {lambda : Fin m → ℝ} {v : Fin m → Fin n → ℝ}
    (target : Fin m) (coeff budget : Fin m → ℝ) (yhat : Fin n → ℝ)
    (hEig : ∀ a : Fin m, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin m, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_bound_nonneg : 0 ≤ A_norm + |lambda target|)
    (hbudget :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) →
        |coeff a| * |(lambda a - mu)⁻¹| * vecNorm2 (v a) ≤ budget a)
    (hPerturbed :
      ∀ i : Fin n,
        ∑ j : Fin n,
          (inverseIterationShiftedMatrix n A mu i j + DeltaS i j) *
            yhat j =
            v target i)
    (hresExpansion :
      (fun i : Fin n => -matMulVec n DeltaS yhat i) =
        fun i => ∑ a : Fin m, coeff a * v a i) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) *
        Finset.sum (Finset.univ.erase target) budget := by
  rcases
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_eigenbasis_component_absolute_budget
      (n := n) (A := A) (B := B) (DeltaS := DeltaS) (mu := mu)
      (lambda := lambda) (v := v) target coeff budget yhat hEig hshift hB
      hbudget hPerturbed hresExpansion with
    ⟨eta, r, hy, hr⟩
  rw [hy]
  have hres :
      vecNorm2
          (eigenResidualVec n A (lambda target)
            (fun i =>
              (lambda target - mu)⁻¹ * v target i +
                (eta * v target i + r i))) ≤
        (A_norm + |lambda target|) * vecNorm2 r := by
    simpa using
      (inverseIteration_near_parallel_error_eigenResidual_norm_le
        (n := n) (A := A) (lambda := lambda target) (mu := mu)
        (A_norm := A_norm) (x := v target)
        (err := fun i : Fin n => eta * v target i + r i) (r := r)
        (hEig target) eta rfl hA)
  exact le_trans hres (mul_le_mul_of_nonneg_left hr hA_bound_nonneg)

/-- Absolute residual/gap perturbed shifted-solve residual certificate.  This
is the eigen-residual counterpart of
`inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_inverse_opNorm_residual_gap_absolute`;
it avoids target-scale hypotheses when the source/solver route supplies a
residual norm bound, eigenbasis-inverse conditioning, and non-target gap. -/
theorem
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_inverse_opNorm_residual_gap_absolute_of_A_norm_nonneg
    {n : ℕ} {A B DeltaS V V_inv : Fin n → Fin n → ℝ}
    {mu A_norm V_inv_norm residualNorm sep : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (hres_norm :
      vecNorm2 (fun i : Fin n => -matMulVec n DeltaS yhat i) ≤ residualNorm)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (hsep_pos : 0 < sep)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|)
    (hPerturbed :
      ∀ i : Fin n,
        ∑ j : Fin n,
          (inverseIterationShiftedMatrix n A mu i j + DeltaS i j) *
            yhat j =
            v target i) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) *
        Finset.sum (Finset.univ.erase target)
          (fun a =>
            ((V_inv_norm * residualNorm) * (1 / sep)) * vecNorm2 (v a)) := by
  let residual : Fin n → ℝ := fun i => -matMulVec n DeltaS yhat i
  let coeff : Fin n → ℝ := matMulVec n V_inv residual
  have hresExpansion :
      residual = fun i => ∑ a : Fin n, coeff a * v a i := by
    simpa [residual, coeff] using
      (eigenbasis_residual_expansion_of_rightInverse
        v hV_cols hV_inv residual)
  have hbudget :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        |coeff a| * |(lambda a - mu)⁻¹| * vecNorm2 (v a) ≤
          ((V_inv_norm * residualNorm) * (1 / sep)) * vecNorm2 (v a) := by
    simpa [residual, coeff] using
      (inverseIteration_eigenbasis_shiftedInverse_component_budget_of_inverse_opNorm_residual_gap
        target lambda mu v V_inv residual V_inv_norm residualNorm sep
        hV_inv_op hV_inv_norm_nonneg hres_norm hsep_pos hsep)
  simpa [residual, coeff] using
    (inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_eigenbasis_component_absolute_budget
      (n := n) (A := A) (B := B) (DeltaS := DeltaS) (mu := mu)
      (A_norm := A_norm) (lambda := lambda) (v := v) target coeff
      (fun a =>
        ((V_inv_norm * residualNorm) * (1 / sep)) * vecNorm2 (v a))
      yhat hEig hshift hB hA
      (add_nonneg hA_norm_nonneg (abs_nonneg (lambda target))) hbudget
      hPerturbed hresExpansion)

/-- Uniform-eigenvector-norm version of the absolute residual/gap near-parallel
decomposition.  This packages the finite non-target tail in the source-readable
form `(n - 1) * (V_inv_norm*residualNorm/sep) * vNormBound`. -/
theorem
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_inverse_opNorm_residual_gap_absolute_uniform_eigenvector_norm
    {n : ℕ} {A B DeltaS V V_inv : Fin n → Fin n → ℝ}
    {mu V_inv_norm residualNorm sep vNormBound : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (hres_norm :
      vecNorm2 (fun i : Fin n => -matMulVec n DeltaS yhat i) ≤ residualNorm)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hsep_pos : 0 < sep)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|)
    (hv_bound :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        vecNorm2 (v a) ≤ vNormBound)
    (hPerturbed :
      ∀ i : Fin n,
        ∑ j : Fin n,
          (inverseIterationShiftedMatrix n A mu i j + DeltaS i j) *
            yhat j =
            v target i) :
    ∃ eta : ℝ, ∃ r : Fin n → ℝ,
      (yhat =
        fun i =>
          (lambda target - mu)⁻¹ * v target i +
            (eta * v target i + r i)) ∧
      vecNorm2 r ≤
        ((n - 1 : ℕ) : ℝ) *
          (((V_inv_norm * residualNorm) * (1 / sep)) * vNormBound) := by
  rcases
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_inverse_opNorm_residual_gap_absolute
      (n := n) (A := A) (B := B) (DeltaS := DeltaS) (V := V)
      (V_inv := V_inv) (mu := mu) (V_inv_norm := V_inv_norm)
      (residualNorm := residualNorm) (sep := sep) (lambda := lambda)
      (v := v) target yhat hV_cols hV_inv hV_inv_op hV_inv_norm_nonneg
      hres_norm hEig hshift hB hsep_pos hsep hPerturbed with
  ⟨eta, r, hy, hr⟩
  have hresidualNorm_nonneg : 0 ≤ residualNorm :=
    le_trans
      (vecNorm2_nonneg (fun i : Fin n => -matMulVec n DeltaS yhat i))
      hres_norm
  have htail :
      Finset.sum (Finset.univ.erase target)
          (fun a =>
            ((V_inv_norm * residualNorm) * (1 / sep)) *
              vecNorm2 (v a)) ≤
        ((n - 1 : ℕ) : ℝ) *
          (((V_inv_norm * residualNorm) * (1 / sep)) * vNormBound) :=
    inverseIteration_residual_gap_tail_sum_le_uniform_eigenvector_norm
      target v V_inv_norm residualNorm sep vNormBound hV_inv_norm_nonneg
      hresidualNorm_nonneg hsep_pos hv_bound
  exact ⟨eta, r, hy, hr.trans htail⟩

/-- Uniform-eigenvector-norm eigen-residual bound for the absolute residual/gap
inverse-iteration route.  It is the residual counterpart of the preceding
near-parallel decomposition wrapper. -/
theorem
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_inverse_opNorm_residual_gap_absolute_uniform_eigenvector_norm_of_A_norm_nonneg
    {n : ℕ} {A B DeltaS V V_inv : Fin n → Fin n → ℝ}
    {mu A_norm V_inv_norm residualNorm sep vNormBound : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (hres_norm :
      vecNorm2 (fun i : Fin n => -matMulVec n DeltaS yhat i) ≤ residualNorm)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (hsep_pos : 0 < sep)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|)
    (hv_bound :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        vecNorm2 (v a) ≤ vNormBound)
    (hPerturbed :
      ∀ i : Fin n,
        ∑ j : Fin n,
          (inverseIterationShiftedMatrix n A mu i j + DeltaS i j) *
            yhat j =
            v target i) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) *
        (((n - 1 : ℕ) : ℝ) *
          (((V_inv_norm * residualNorm) * (1 / sep)) * vNormBound)) := by
  have hbase :=
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_inverse_opNorm_residual_gap_absolute_of_A_norm_nonneg
      (n := n) (A := A) (B := B) (DeltaS := DeltaS) (V := V)
      (V_inv := V_inv) (mu := mu) (A_norm := A_norm)
      (V_inv_norm := V_inv_norm) (residualNorm := residualNorm)
      (sep := sep) (lambda := lambda) (v := v) target yhat hV_cols
      hV_inv hV_inv_op hV_inv_norm_nonneg hres_norm hEig hshift hB hA
      hA_norm_nonneg hsep_pos hsep hPerturbed
  have hresidualNorm_nonneg : 0 ≤ residualNorm :=
    le_trans
      (vecNorm2_nonneg (fun i : Fin n => -matMulVec n DeltaS yhat i))
      hres_norm
  have htail :
      Finset.sum (Finset.univ.erase target)
          (fun a =>
            ((V_inv_norm * residualNorm) * (1 / sep)) * vecNorm2 (v a)) ≤
        ((n - 1 : ℕ) : ℝ) *
          (((V_inv_norm * residualNorm) * (1 / sep)) * vNormBound) :=
    inverseIteration_residual_gap_tail_sum_le_uniform_eigenvector_norm
      target v V_inv_norm residualNorm sep vNormBound hV_inv_norm_nonneg
      hresidualNorm_nonneg hsep_pos hv_bound
  exact hbase.trans
    (mul_le_mul_of_nonneg_left htail
      (add_nonneg hA_norm_nonneg (abs_nonneg (lambda target))))

/-- If the eigenvector columns form an orthogonal matrix, every source
eigenvector has norm at most one.  This is the unit-column bridge used by the
orthogonal inverse-iteration handoff. -/
theorem inverseIteration_eigenvector_norm_le_one_of_orthogonal_columns
    {n : ℕ} {V : Fin n → Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_orth : IsOrthogonal n V) :
    ∀ a : Fin n, vecNorm2 (v a) ≤ 1 := by
  intro a
  have hv_eq : v a = fun i : Fin n => V i a := by
    ext i
    exact (hV_cols i a).symm
  simpa [hv_eq] using hV_orth.column_vecNorm2_le_one a

/-- Orthogonal-eigenbasis specialization of the absolute residual/gap
near-parallel decomposition.  The orthogonality hypothesis supplies both the
transpose inverse operator certificate with norm one and the unit eigenvector
tail bound, leaving the solver/source theorem to supply residual-size and
non-target separation facts. -/
theorem
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_orthogonal_eigenbasis_residual_gap_absolute
    {n : ℕ} {A B DeltaS V : Fin n → Fin n → ℝ}
    {mu residualNorm sep : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_orth : IsOrthogonal n V)
    (hres_norm :
      vecNorm2 (fun i : Fin n => -matMulVec n DeltaS yhat i) ≤ residualNorm)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hsep_pos : 0 < sep)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|)
    (hPerturbed :
      ∀ i : Fin n,
        ∑ j : Fin n,
          (inverseIterationShiftedMatrix n A mu i j + DeltaS i j) *
            yhat j =
            v target i) :
    ∃ eta : ℝ, ∃ r : Fin n → ℝ,
      (yhat =
        fun i =>
          (lambda target - mu)⁻¹ * v target i +
            (eta * v target i + r i)) ∧
      vecNorm2 r ≤ ((n - 1 : ℕ) : ℝ) * (residualNorm * (1 / sep)) := by
  have hv_bound :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        vecNorm2 (v a) ≤ 1 := by
    intro a _ha
    exact
      inverseIteration_eigenvector_norm_le_one_of_orthogonal_columns
        hV_cols hV_orth a
  rcases
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_inverse_opNorm_residual_gap_absolute_uniform_eigenvector_norm
      (n := n) (A := A) (B := B) (DeltaS := DeltaS) (V := V)
      (V_inv := matTranspose V) (mu := mu) (V_inv_norm := 1)
      (residualNorm := residualNorm) (sep := sep) (vNormBound := 1)
      (lambda := lambda) (v := v) target yhat hV_cols hV_orth.right_inv
      hV_orth.transpose_opNorm2Le_one (by norm_num) hres_norm hEig hshift
      hB hsep_pos hsep hv_bound hPerturbed with
  ⟨eta, r, hy, hr⟩
  exact ⟨eta, r, hy, by simpa [one_mul, mul_one] using hr⟩

/-- Orthogonal-eigenbasis eigen-residual bound for the absolute residual/gap
inverse-iteration route.  This is the residual counterpart of the preceding
near-parallel decomposition wrapper. -/
theorem
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_orthogonal_eigenbasis_residual_gap_absolute_of_A_norm_nonneg
    {n : ℕ} {A B DeltaS V : Fin n → Fin n → ℝ}
    {mu A_norm residualNorm sep : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_orth : IsOrthogonal n V)
    (hres_norm :
      vecNorm2 (fun i : Fin n => -matMulVec n DeltaS yhat i) ≤ residualNorm)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (hsep_pos : 0 < sep)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|)
    (hPerturbed :
      ∀ i : Fin n,
        ∑ j : Fin n,
          (inverseIterationShiftedMatrix n A mu i j + DeltaS i j) *
            yhat j =
            v target i) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) *
        (((n - 1 : ℕ) : ℝ) * (residualNorm * (1 / sep))) := by
  have hv_bound :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        vecNorm2 (v a) ≤ 1 := by
    intro a _ha
    exact
      inverseIteration_eigenvector_norm_le_one_of_orthogonal_columns
        hV_cols hV_orth a
  have hbase :=
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_inverse_opNorm_residual_gap_absolute_uniform_eigenvector_norm_of_A_norm_nonneg
      (n := n) (A := A) (B := B) (DeltaS := DeltaS) (V := V)
      (V_inv := matTranspose V) (mu := mu) (A_norm := A_norm)
      (V_inv_norm := 1) (residualNorm := residualNorm) (sep := sep)
      (vNormBound := 1) (lambda := lambda) (v := v) target yhat
      hV_cols hV_orth.right_inv hV_orth.transpose_opNorm2Le_one
      (by norm_num) hres_norm hEig hshift hB hA hA_norm_nonneg hsep_pos
      hsep hv_bound hPerturbed
  simpa [one_mul, mul_one] using hbase

/-- Orthogonal-eigenbasis residual/gap decomposition with the non-target gap
derived from a source-shaped eigenvalue-separation condition.  Instead of
assuming `sep <= |lambda a - mu|` directly, this wrapper assumes the shift is
within `radius` of the target eigenvalue and every non-target eigenvalue is at
least `sep + radius` from the target eigenvalue. -/
theorem
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_orthogonal_eigenbasis_residual_eigengap_absolute
    {n : ℕ} {A B DeltaS V : Fin n → Fin n → ℝ}
    {mu radius residualNorm sep : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_orth : IsOrthogonal n V)
    (hres_norm :
      vecNorm2 (fun i : Fin n => -matMulVec n DeltaS yhat i) ≤ residualNorm)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (htarget_radius : |lambda target - mu| ≤ radius)
    (hsep_pos : 0 < sep)
    (hgap :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep + radius ≤ |lambda a - lambda target|)
    (hPerturbed :
      ∀ i : Fin n,
        ∑ j : Fin n,
          (inverseIterationShiftedMatrix n A mu i j + DeltaS i j) *
            yhat j =
            v target i) :
    ∃ eta : ℝ, ∃ r : Fin n → ℝ,
      (yhat =
        fun i =>
          (lambda target - mu)⁻¹ * v target i +
            (eta * v target i + r i)) ∧
      vecNorm2 r ≤ ((n - 1 : ℕ) : ℝ) * (residualNorm * (1 / sep)) := by
  have hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu| :=
    inverseIteration_nonTarget_shift_gap_of_uniform_eigenvalue_gap_and_target_radius
      target lambda mu radius sep htarget_radius hgap
  exact
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_orthogonal_eigenbasis_residual_gap_absolute
      (n := n) (A := A) (B := B) (DeltaS := DeltaS) (V := V)
      (mu := mu) (residualNorm := residualNorm) (sep := sep)
      (lambda := lambda) (v := v) target yhat hV_cols hV_orth
      hres_norm hEig hshift hB hsep_pos hsep hPerturbed

/-- Eigen-residual bound for the orthogonal-eigenbasis residual/gap route with
the non-target shift gap derived from eigenvalue separation and a target-shift
radius. -/
theorem
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_orthogonal_eigenbasis_residual_eigengap_absolute_of_A_norm_nonneg
    {n : ℕ} {A B DeltaS V : Fin n → Fin n → ℝ}
    {mu A_norm radius residualNorm sep : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_orth : IsOrthogonal n V)
    (hres_norm :
      vecNorm2 (fun i : Fin n => -matMulVec n DeltaS yhat i) ≤ residualNorm)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (htarget_radius : |lambda target - mu| ≤ radius)
    (hsep_pos : 0 < sep)
    (hgap :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep + radius ≤ |lambda a - lambda target|)
    (hPerturbed :
      ∀ i : Fin n,
        ∑ j : Fin n,
          (inverseIterationShiftedMatrix n A mu i j + DeltaS i j) *
            yhat j =
            v target i) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) *
        (((n - 1 : ℕ) : ℝ) * (residualNorm * (1 / sep))) := by
  have hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu| :=
    inverseIteration_nonTarget_shift_gap_of_uniform_eigenvalue_gap_and_target_radius
      target lambda mu radius sep htarget_radius hgap
  exact
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_orthogonal_eigenbasis_residual_gap_absolute_of_A_norm_nonneg
      (n := n) (A := A) (B := B) (DeltaS := DeltaS) (V := V)
      (mu := mu) (A_norm := A_norm) (residualNorm := residualNorm)
      (sep := sep) (lambda := lambda) (v := v) target yhat hV_cols
      hV_orth hres_norm hEig hshift hB hA hA_norm_nonneg hsep_pos hsep
      hPerturbed

/-- Perturbed shifted-solve certificate with the norm-bound side condition stated
as the ordinary source-facing hypothesis `0 <= A_norm`. -/
theorem
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_eigenbasis_component_target_radius_gap_of_A_norm_nonneg
    {m n : ℕ} {A B DeltaS : Fin n → Fin n → ℝ}
    {mu A_norm radius sep : ℝ}
    {lambda : Fin m → ℝ} {v : Fin m → Fin n → ℝ}
    (target : Fin m) (coeff beta : Fin m → ℝ) (yhat : Fin n → ℝ)
    (hEig : ∀ a : Fin m, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin m, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (hscale :
      0 <
        |coeff target| * |(lambda target - mu)⁻¹| *
          vecNorm2 (v target))
    (hsep_pos : 0 < sep)
    (htarget_pos : 0 < |lambda target - mu|)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|)
    (hbeta_nonneg :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) → 0 ≤ beta a)
    (hcoeff_ratio :
      ∀ a : Fin m, a ∈ (Finset.univ.erase target) →
        |coeff a| * vecNorm2 (v a) ≤
          beta a * (|coeff target| * vecNorm2 (v target)))
    (hPerturbed :
      ∀ i : Fin n,
        ∑ j : Fin n,
          (inverseIterationShiftedMatrix n A mu i j + DeltaS i j) *
            yhat j =
            v target i)
    (hresExpansion :
      (fun i : Fin n => -matMulVec n DeltaS yhat i) =
        fun i => ∑ a : Fin m, coeff a * v a i) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) *
        (Finset.sum (Finset.univ.erase target)
            (fun a => beta a * (radius / sep)) *
          (|coeff target| * |(lambda target - mu)⁻¹| *
            vecNorm2 (v target))) := by
  exact
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_eigenbasis_component_target_radius_gap
      (n := n) (A := A) (B := B) (DeltaS := DeltaS) (mu := mu)
      (A_norm := A_norm) (radius := radius) (sep := sep)
      (lambda := lambda) (v := v) target coeff beta yhat hEig hshift hB hA
      (add_nonneg hA_norm_nonneg (abs_nonneg (lambda target))) hscale
      hsep_pos htarget_pos htarget hsep hbeta_nonneg hcoeff_ratio
      hPerturbed hresExpansion

/-- Norm bound for the backward-error action appearing in the inverse-iteration
certificate route.  An operator-norm bound on the modeled perturbation matrix
`DeltaS` immediately bounds the residual action `-DeltaS*yhat`; the minus sign
does not change the Euclidean norm. -/
theorem inverseIteration_backwardErrorAction_vecNorm2_le_of_opNorm2Le
    {n : ℕ} (DeltaS : Fin n → Fin n → ℝ) (yhat : Fin n → ℝ)
    (DeltaS_norm : ℝ) (hDeltaS : opNorm2Le DeltaS DeltaS_norm) :
    vecNorm2 (fun i : Fin n => -matMulVec n DeltaS yhat i) ≤
      DeltaS_norm * vecNorm2 yhat := by
  calc
    vecNorm2 (fun i : Fin n => -matMulVec n DeltaS yhat i)
        = vecNorm2 (matMulVec n DeltaS yhat) := by
          simpa using (vecNorm2_neg (matMulVec n DeltaS yhat))
    _ ≤ DeltaS_norm * vecNorm2 yhat := hDeltaS yhat

/-- Orthogonal-eigenbasis eigengap wrapper that derives the residual-size
hypothesis from an operator-norm backward-error certificate for `DeltaS`. -/
theorem
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_orthogonal_eigenbasis_opNorm_eigengap_absolute
    {n : ℕ} {A B DeltaS V : Fin n → Fin n → ℝ}
    {mu radius DeltaS_norm sep : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_orth : IsOrthogonal n V)
    (hDeltaS_op : opNorm2Le DeltaS DeltaS_norm)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (htarget_radius : |lambda target - mu| ≤ radius)
    (hsep_pos : 0 < sep)
    (hgap :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep + radius ≤ |lambda a - lambda target|)
    (hPerturbed :
      ∀ i : Fin n,
        ∑ j : Fin n,
          (inverseIterationShiftedMatrix n A mu i j + DeltaS i j) *
            yhat j =
            v target i) :
    ∃ eta : ℝ, ∃ r : Fin n → ℝ,
      (yhat =
        fun i =>
          (lambda target - mu)⁻¹ * v target i +
            (eta * v target i + r i)) ∧
      vecNorm2 r ≤
        ((n - 1 : ℕ) : ℝ) * ((DeltaS_norm * vecNorm2 yhat) * (1 / sep)) := by
  exact
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_orthogonal_eigenbasis_residual_eigengap_absolute
      (n := n) (A := A) (B := B) (DeltaS := DeltaS) (V := V)
      (mu := mu) (radius := radius)
      (residualNorm := DeltaS_norm * vecNorm2 yhat) (sep := sep)
      (lambda := lambda) (v := v) target yhat hV_cols hV_orth
      (inverseIteration_backwardErrorAction_vecNorm2_le_of_opNorm2Le
        DeltaS yhat DeltaS_norm hDeltaS_op)
      hEig hshift hB htarget_radius hsep_pos hgap hPerturbed

/-- Eigen-residual eigengap wrapper for an orthogonal eigenbasis, with the
residual-size side condition discharged by an operator-norm certificate for
the modeled shifted-system perturbation. -/
theorem
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_orthogonal_eigenbasis_opNorm_eigengap_absolute_of_A_norm_nonneg
    {n : ℕ} {A B DeltaS V : Fin n → Fin n → ℝ}
    {mu A_norm radius DeltaS_norm sep : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_orth : IsOrthogonal n V)
    (hDeltaS_op : opNorm2Le DeltaS DeltaS_norm)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (htarget_radius : |lambda target - mu| ≤ radius)
    (hsep_pos : 0 < sep)
    (hgap :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep + radius ≤ |lambda a - lambda target|)
    (hPerturbed :
      ∀ i : Fin n,
        ∑ j : Fin n,
          (inverseIterationShiftedMatrix n A mu i j + DeltaS i j) *
            yhat j =
            v target i) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) *
        (((n - 1 : ℕ) : ℝ) *
          ((DeltaS_norm * vecNorm2 yhat) * (1 / sep))) := by
  exact
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_orthogonal_eigenbasis_residual_eigengap_absolute_of_A_norm_nonneg
      (n := n) (A := A) (B := B) (DeltaS := DeltaS) (V := V)
      (mu := mu) (A_norm := A_norm) (radius := radius)
      (residualNorm := DeltaS_norm * vecNorm2 yhat) (sep := sep)
      (lambda := lambda) (v := v) target yhat hV_cols hV_orth
      (inverseIteration_backwardErrorAction_vecNorm2_le_of_opNorm2Le
        DeltaS yhat DeltaS_norm hDeltaS_op)
      hEig hshift hB hA hA_norm_nonneg htarget_radius hsep_pos hgap
      hPerturbed

/-- Solver-facing orthogonal/eigengap near-parallel theorem.  A concrete
shifted solver only has to prove the standard relative residual estimate; the
canonical rank-one shifted-system perturbation supplies the modeled
backward-error certificate consumed by the orthogonal/eigengap route. -/
theorem
    inverseIteration_shiftedSolve_near_parallel_decomposition_of_relative_residual_orthogonal_eigenbasis_eigengap_absolute
    {n : ℕ} {A B V : Fin n → Fin n → ℝ}
    {mu radius rho sep : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_orth : IsOrthogonal n V)
    (hres :
      vecNorm2 (residualVec n (inverseIterationShiftedMatrix n A mu) yhat
        (v target)) ≤ rho * vecNorm2 yhat)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (htarget_radius : |lambda target - mu| ≤ radius)
    (hsep_pos : 0 < sep)
    (hgap :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep + radius ≤ |lambda a - lambda target|) :
    ∃ eta : ℝ, ∃ r : Fin n → ℝ,
      (yhat =
        fun i =>
          (lambda target - mu)⁻¹ * v target i +
            (eta * v target i + r i)) ∧
      vecNorm2 r ≤
        ((n - 1 : ℕ) : ℝ) * ((rho * vecNorm2 yhat) * (1 / sep)) := by
  exact
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_orthogonal_eigenbasis_opNorm_eigengap_absolute
      (n := n) (A := A) (B := B)
      (DeltaS := inverseIterationShiftedRankOneBackwardError n A mu
        (v target) yhat)
      (V := V) (mu := mu) (radius := radius) (DeltaS_norm := rho)
      (sep := sep) (lambda := lambda) (v := v) target yhat hV_cols
      hV_orth
      (inverseIterationShiftedRankOneBackwardError_opNorm2Le_of_residual_norm_le
        n A mu (v target) yhat rho hyhat hres)
      hEig hshift hB htarget_radius hsep_pos hgap
      (inverseIterationShiftedRankOneBackwardError_solves n A mu
        (v target) yhat hyhat)

/-- Solver-facing orthogonal/eigengap eigen-residual theorem.  This is the
final local handoff from a visible shifted-solver relative residual estimate to
the inverse-iteration eigen-residual bound under orthogonal eigenbasis,
target-radius, and eigengap hypotheses. -/
theorem
    inverseIteration_shiftedSolve_eigenResidual_norm_le_of_relative_residual_orthogonal_eigenbasis_eigengap_absolute_of_A_norm_nonneg
    {n : ℕ} {A B V : Fin n → Fin n → ℝ}
    {mu A_norm radius rho sep : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_orth : IsOrthogonal n V)
    (hres :
      vecNorm2 (residualVec n (inverseIterationShiftedMatrix n A mu) yhat
        (v target)) ≤ rho * vecNorm2 yhat)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (htarget_radius : |lambda target - mu| ≤ radius)
    (hsep_pos : 0 < sep)
    (hgap :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep + radius ≤ |lambda a - lambda target|) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) *
        (((n - 1 : ℕ) : ℝ) * ((rho * vecNorm2 yhat) * (1 / sep))) := by
  exact
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_orthogonal_eigenbasis_opNorm_eigengap_absolute_of_A_norm_nonneg
      (n := n) (A := A) (B := B)
      (DeltaS := inverseIterationShiftedRankOneBackwardError n A mu
        (v target) yhat)
      (V := V) (mu := mu) (A_norm := A_norm) (radius := radius)
      (DeltaS_norm := rho) (sep := sep) (lambda := lambda) (v := v)
      target yhat hV_cols hV_orth
      (inverseIterationShiftedRankOneBackwardError_opNorm2Le_of_residual_norm_le
        n A mu (v target) yhat rho hyhat hres)
      hEig hshift hB hA hA_norm_nonneg htarget_radius hsep_pos hgap
      (inverseIterationShiftedRankOneBackwardError_solves n A mu
        (v target) yhat hyhat)

/-- Normalized solver-facing orthogonal/eigengap near-parallel theorem.  This
turns the expanded local tail radius into the source-readable relative form
`||r||_2 <= eps * ||yhat||_2` once the residual/eigengap factor satisfies
`(n - 1) * rho / sep <= eps`. -/
theorem
    inverseIteration_shiftedSolve_near_parallel_decomposition_of_relative_residual_orthogonal_eigenbasis_eigengap_relative_tail
    {n : ℕ} {A B V : Fin n → Fin n → ℝ}
    {mu radius rho sep eps : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_orth : IsOrthogonal n V)
    (hres :
      vecNorm2 (residualVec n (inverseIterationShiftedMatrix n A mu) yhat
        (v target)) ≤ rho * vecNorm2 yhat)
    (hrelative_tail :
      ((n - 1 : ℕ) : ℝ) * (rho * (1 / sep)) ≤ eps)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (htarget_radius : |lambda target - mu| ≤ radius)
    (hsep_pos : 0 < sep)
    (hgap :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep + radius ≤ |lambda a - lambda target|) :
    ∃ eta : ℝ, ∃ r : Fin n → ℝ,
      (yhat =
        fun i =>
          (lambda target - mu)⁻¹ * v target i +
            (eta * v target i + r i)) ∧
      vecNorm2 r ≤ eps * vecNorm2 yhat := by
  obtain ⟨eta, r, hy, hr⟩ :=
    inverseIteration_shiftedSolve_near_parallel_decomposition_of_relative_residual_orthogonal_eigenbasis_eigengap_absolute
      (n := n) (A := A) (B := B) (V := V) (mu := mu)
      (radius := radius) (rho := rho) (sep := sep) (lambda := lambda)
      (v := v) target yhat hyhat hV_cols hV_orth hres hEig hshift hB
      htarget_radius hsep_pos hgap
  refine ⟨eta, r, hy, ?_⟩
  have hnorm_nonneg : 0 ≤ vecNorm2 yhat := vecNorm2_nonneg yhat
  have htail_eq :
      ((n - 1 : ℕ) : ℝ) * ((rho * vecNorm2 yhat) * (1 / sep)) =
        (((n - 1 : ℕ) : ℝ) * (rho * (1 / sep))) * vecNorm2 yhat := by
    ring
  calc
    vecNorm2 r ≤
        ((n - 1 : ℕ) : ℝ) * ((rho * vecNorm2 yhat) * (1 / sep)) := hr
    _ = (((n - 1 : ℕ) : ℝ) * (rho * (1 / sep))) * vecNorm2 yhat := htail_eq
    _ ≤ eps * vecNorm2 yhat :=
      mul_le_mul_of_nonneg_right hrelative_tail hnorm_nonneg

/-- Normalized solver-facing orthogonal/eigengap eigen-residual theorem.  It
uses the same relative-tail premise to expose the final residual as
`(A_norm + |lambda_target|) * eps * ||yhat||_2`. -/
theorem
    inverseIteration_shiftedSolve_eigenResidual_norm_le_of_relative_residual_orthogonal_eigenbasis_eigengap_relative_tail_of_A_norm_nonneg
    {n : ℕ} {A B V : Fin n → Fin n → ℝ}
    {mu A_norm radius rho sep eps : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_orth : IsOrthogonal n V)
    (hres :
      vecNorm2 (residualVec n (inverseIterationShiftedMatrix n A mu) yhat
        (v target)) ≤ rho * vecNorm2 yhat)
    (hrelative_tail :
      ((n - 1 : ℕ) : ℝ) * (rho * (1 / sep)) ≤ eps)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (htarget_radius : |lambda target - mu| ≤ radius)
    (hsep_pos : 0 < sep)
    (hgap :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep + radius ≤ |lambda a - lambda target|) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) * (eps * vecNorm2 yhat) := by
  have hbase :=
    inverseIteration_shiftedSolve_eigenResidual_norm_le_of_relative_residual_orthogonal_eigenbasis_eigengap_absolute_of_A_norm_nonneg
      (n := n) (A := A) (B := B) (V := V) (mu := mu)
      (A_norm := A_norm) (radius := radius) (rho := rho) (sep := sep)
      (lambda := lambda) (v := v) target yhat hyhat hV_cols hV_orth
      hres hEig hshift hB hA hA_norm_nonneg htarget_radius hsep_pos hgap
  have hnorm_nonneg : 0 ≤ vecNorm2 yhat := vecNorm2_nonneg yhat
  have htail_eq :
      ((n - 1 : ℕ) : ℝ) * ((rho * vecNorm2 yhat) * (1 / sep)) =
        (((n - 1 : ℕ) : ℝ) * (rho * (1 / sep))) * vecNorm2 yhat := by
    ring
  have htail_le :
      ((n - 1 : ℕ) : ℝ) * ((rho * vecNorm2 yhat) * (1 / sep)) ≤
        eps * vecNorm2 yhat := by
    rw [htail_eq]
    exact mul_le_mul_of_nonneg_right hrelative_tail hnorm_nonneg
  have hfactor_nonneg : 0 ≤ A_norm + |lambda target| :=
    add_nonneg hA_norm_nonneg (abs_nonneg (lambda target))
  exact le_trans hbase (mul_le_mul_of_nonneg_left htail_le hfactor_nonneg)

/-- Source-readable residual/eigengap cap for the inverse-iteration
relative-tail premise.  If the shifted-solver residual factor `rho` is small
enough compared with the non-target separation `sep`, then the normalized tail
factor required by the orthogonal/eigengap handoff is at most `eps`. -/
theorem inverseIteration_relative_tail_le_of_pred_mul_rho_le_eps_mul_sep
    {n : ℕ} {rho sep eps : ℝ}
    (hsep_pos : 0 < sep)
    (hcap : ((n - 1 : ℕ) : ℝ) * rho ≤ eps * sep) :
    ((n - 1 : ℕ) : ℝ) * (rho * (1 / sep)) ≤ eps := by
  have hsep_inv_nonneg : 0 ≤ 1 / sep := le_of_lt (one_div_pos.mpr hsep_pos)
  calc
    ((n - 1 : ℕ) : ℝ) * (rho * (1 / sep))
        = (((n - 1 : ℕ) : ℝ) * rho) * (1 / sep) := by ring
    _ ≤ (eps * sep) * (1 / sep) :=
      mul_le_mul_of_nonneg_right hcap hsep_inv_nonneg
    _ = eps := by field_simp [ne_of_gt hsep_pos]

/-- Division-form variant of
`inverseIteration_relative_tail_le_of_pred_mul_rho_le_eps_mul_sep`.  For
nontrivial dimensions `1 < n`, it is enough to bound the relative residual
factor as `rho <= eps*sep/(n-1)`. -/
theorem inverseIteration_relative_tail_le_of_rho_le_eps_mul_sep_div_pred
    {n : ℕ} {rho sep eps : ℝ}
    (hn : 1 < n)
    (hsep_pos : 0 < sep)
    (hrho : rho ≤ eps * sep / (((n - 1 : ℕ) : ℝ))) :
    ((n - 1 : ℕ) : ℝ) * (rho * (1 / sep)) ≤ eps := by
  have hpred_pos : 0 < (((n - 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.sub_pos_of_lt hn
  apply inverseIteration_relative_tail_le_of_pred_mul_rho_le_eps_mul_sep
    (n := n) (rho := rho) (sep := sep) (eps := eps) hsep_pos
  calc
    ((n - 1 : ℕ) : ℝ) * rho
        ≤ ((n - 1 : ℕ) : ℝ) *
            (eps * sep / (((n - 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hrho (le_of_lt hpred_pos)
    _ = eps * sep := by field_simp [ne_of_gt hpred_pos]

/-- Concrete LU shifted-solve residual bridge for inverse iteration.  If the
computed vector `yhat` is produced by the repository's modeled
forward/back-substitution LU solve for `(A - mu I)y = v_target`, and the
Higham §9.4 componentwise LU solve perturbation has Frobenius budget `rho`,
then the shifted-system residual is bounded by `rho * ||yhat||_2`. -/
theorem
    inverseIteration_lu_shiftedSolve_residual_norm_le_of_component_frob_budget
    {n : ℕ} {fp : FPModel} {A L_hat U_hat : Fin n → Fin n → ℝ}
    {mu rho : ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat_eq :
      yhat = fl_backSub fp n U_hat (fl_forwardSub fp n L_hat (v target)))
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU :
      LUBackwardError n (inverseIterationShiftedMatrix n A mu) L_hat U_hat
        (gamma fp n))
    (hn : gammaValid fp n)
    (hLU_frob :
      frobNorm (fun i j =>
        (3 * gamma fp n + gamma fp n ^ 2) *
          ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ≤ rho) :
    vecNorm2
        (residualVec n (inverseIterationShiftedMatrix n A mu) yhat
          (v target)) ≤
      rho * vecNorm2 yhat := by
  let S : Fin n → Fin n → ℝ := inverseIterationShiftedMatrix n A mu
  let E : Fin n → Fin n → ℝ := fun i j =>
    (3 * gamma fp n + gamma fp n ^ 2) *
      ∑ k : Fin n, |L_hat i k| * |U_hat k j|
  obtain ⟨DeltaS, hDelta_bound, hDelta_solve0⟩ :=
    lu_solve_backward_error fp n S L_hat U_hat (v target)
      hL_diag hU_diag (by simpa [S] using hLU) hn
  have hDelta_solve :
      ∀ i : Fin n, ∑ j : Fin n, (S i j + DeltaS i j) * yhat j =
        v target i := by
    intro i
    rw [hyhat_eq]
    simpa [S] using hDelta_solve0 i
  have hE_nonneg : ∀ i j, 0 ≤ E i j := by
    intro i j
    have hcoef_nonneg : 0 ≤ 3 * gamma fp n + gamma fp n ^ 2 :=
      add_nonneg (mul_nonneg (by norm_num) (gamma_nonneg fp hn))
        (sq_nonneg (gamma fp n))
    have hsum_nonneg :
        0 ≤ ∑ k : Fin n, |L_hat i k| * |U_hat k j| :=
      Finset.sum_nonneg
        (fun k _ => mul_nonneg (abs_nonneg (L_hat i k))
          (abs_nonneg (U_hat k j)))
    exact mul_nonneg hcoef_nonneg hsum_nonneg
  have hDelta_frob_le : frobNorm DeltaS ≤ frobNorm E :=
    frobNorm_le_of_entry_abs_le DeltaS E hE_nonneg (by
      intro i j
      simpa [E] using hDelta_bound i j)
  have hDelta_frob : frobNorm DeltaS ≤ rho :=
    le_trans hDelta_frob_le (by simpa [E] using hLU_frob)
  have hDelta_op : opNorm2Le DeltaS rho :=
    opNorm2Le_of_frobNorm_le DeltaS hDelta_frob
  have hres_eq :
      residualVec n S yhat (v target) = matMulVec n DeltaS yhat :=
    residualVec_eq_matMulVec_of_perturbed_solve n S DeltaS yhat
      (v target) hDelta_solve
  have hres : vecNorm2 (residualVec n S yhat (v target)) ≤
      rho * vecNorm2 yhat := by
    rw [hres_eq]
    exact hDelta_op yhat
  simpa [S] using hres

/-- LU-solver-facing near-parallel inverse-iteration theorem.  This composes
the concrete Higham §9.4 LU solve backward error with the orthogonal
eigenbasis/eigengap inverse-iteration residual theorem, so the residual
premise is discharged by the modeled LU shifted solve and its explicit
componentwise Frobenius budget. -/
theorem
    inverseIteration_lu_shiftedSolve_near_parallel_decomposition_of_component_frob_budget_orthogonal_eigenbasis_eigengap_relative_tail
    {n : ℕ} {fp : FPModel} {A L_hat U_hat B V : Fin n → Fin n → ℝ}
    {mu radius rho sep eps : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hyhat_eq :
      yhat = fl_backSub fp n U_hat (fl_forwardSub fp n L_hat (v target)))
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU :
      LUBackwardError n (inverseIterationShiftedMatrix n A mu) L_hat U_hat
        (gamma fp n))
    (hn : gammaValid fp n)
    (hLU_frob :
      frobNorm (fun i j =>
        (3 * gamma fp n + gamma fp n ^ 2) *
          ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ≤ rho)
    (hrelative_tail :
      ((n - 1 : ℕ) : ℝ) * (rho * (1 / sep)) ≤ eps)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_orth : IsOrthogonal n V)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (htarget_radius : |lambda target - mu| ≤ radius)
    (hsep_pos : 0 < sep)
    (hgap :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep + radius ≤ |lambda a - lambda target|) :
    ∃ eta : ℝ, ∃ r : Fin n → ℝ,
      (yhat =
        fun i =>
          (lambda target - mu)⁻¹ * v target i +
            (eta * v target i + r i)) ∧
      vecNorm2 r ≤ eps * vecNorm2 yhat := by
  have hres :=
    inverseIteration_lu_shiftedSolve_residual_norm_le_of_component_frob_budget
      (n := n) (fp := fp) (A := A) (L_hat := L_hat) (U_hat := U_hat)
      (mu := mu) (rho := rho) (v := v) target yhat hyhat_eq
      hL_diag hU_diag hLU hn hLU_frob
  exact
    inverseIteration_shiftedSolve_near_parallel_decomposition_of_relative_residual_orthogonal_eigenbasis_eigengap_relative_tail
      (n := n) (A := A) (B := B) (V := V) (mu := mu)
      (radius := radius) (rho := rho) (sep := sep) (eps := eps)
      (lambda := lambda) (v := v) target yhat hyhat hV_cols hV_orth
      hres hrelative_tail hEig hshift hB htarget_radius hsep_pos hgap

/-- LU-solver-facing eigen-residual inverse-iteration theorem.  The final
bound is stated with the source-readable relative-tail premise while the
residual budget itself is supplied by the concrete modeled LU shifted solve. -/
theorem
    inverseIteration_lu_shiftedSolve_eigenResidual_norm_le_of_component_frob_budget_orthogonal_eigenbasis_eigengap_relative_tail_of_A_norm_nonneg
    {n : ℕ} {fp : FPModel} {A L_hat U_hat B V : Fin n → Fin n → ℝ}
    {mu A_norm radius rho sep eps : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hyhat_eq :
      yhat = fl_backSub fp n U_hat (fl_forwardSub fp n L_hat (v target)))
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU :
      LUBackwardError n (inverseIterationShiftedMatrix n A mu) L_hat U_hat
        (gamma fp n))
    (hn : gammaValid fp n)
    (hLU_frob :
      frobNorm (fun i j =>
        (3 * gamma fp n + gamma fp n ^ 2) *
          ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ≤ rho)
    (hrelative_tail :
      ((n - 1 : ℕ) : ℝ) * (rho * (1 / sep)) ≤ eps)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_orth : IsOrthogonal n V)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (htarget_radius : |lambda target - mu| ≤ radius)
    (hsep_pos : 0 < sep)
    (hgap :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep + radius ≤ |lambda a - lambda target|) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) * (eps * vecNorm2 yhat) := by
  have hres :=
    inverseIteration_lu_shiftedSolve_residual_norm_le_of_component_frob_budget
      (n := n) (fp := fp) (A := A) (L_hat := L_hat) (U_hat := U_hat)
      (mu := mu) (rho := rho) (v := v) target yhat hyhat_eq
      hL_diag hU_diag hLU hn hLU_frob
  exact
    inverseIteration_shiftedSolve_eigenResidual_norm_le_of_relative_residual_orthogonal_eigenbasis_eigengap_relative_tail_of_A_norm_nonneg
      (n := n) (A := A) (B := B) (V := V) (mu := mu)
      (A_norm := A_norm) (radius := radius) (rho := rho) (sep := sep)
      (eps := eps) (lambda := lambda) (v := v) target yhat hyhat
      hV_cols hV_orth hres hrelative_tail hEig hshift hB hA
      hA_norm_nonneg htarget_radius hsep_pos hgap

/-- LU-solver-facing near-parallel inverse-iteration theorem with the
relative-tail premise stated as the residual/eigengap cap
`(n-1)*rho <= eps*sep`. -/
theorem
    inverseIteration_lu_shiftedSolve_near_parallel_decomposition_of_component_frob_budget_orthogonal_eigenbasis_eigengap_relative_tail_of_residual_gap_cap
    {n : ℕ} {fp : FPModel} {A L_hat U_hat B V : Fin n → Fin n → ℝ}
    {mu radius rho sep eps : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hyhat_eq :
      yhat = fl_backSub fp n U_hat (fl_forwardSub fp n L_hat (v target)))
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU :
      LUBackwardError n (inverseIterationShiftedMatrix n A mu) L_hat U_hat
        (gamma fp n))
    (hn : gammaValid fp n)
    (hLU_frob :
      frobNorm (fun i j =>
        (3 * gamma fp n + gamma fp n ^ 2) *
          ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ≤ rho)
    (hresidual_gap_cap : ((n - 1 : ℕ) : ℝ) * rho ≤ eps * sep)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_orth : IsOrthogonal n V)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (htarget_radius : |lambda target - mu| ≤ radius)
    (hsep_pos : 0 < sep)
    (hgap :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep + radius ≤ |lambda a - lambda target|) :
    ∃ eta : ℝ, ∃ r : Fin n → ℝ,
      (yhat =
        fun i =>
          (lambda target - mu)⁻¹ * v target i +
            (eta * v target i + r i)) ∧
      vecNorm2 r ≤ eps * vecNorm2 yhat := by
  exact
    inverseIteration_lu_shiftedSolve_near_parallel_decomposition_of_component_frob_budget_orthogonal_eigenbasis_eigengap_relative_tail
      (n := n) (fp := fp) (A := A) (L_hat := L_hat) (U_hat := U_hat)
      (B := B) (V := V) (mu := mu) (radius := radius) (rho := rho)
      (sep := sep) (eps := eps) (lambda := lambda) (v := v)
      target yhat hyhat hyhat_eq hL_diag hU_diag hLU hn hLU_frob
      (inverseIteration_relative_tail_le_of_pred_mul_rho_le_eps_mul_sep
        (n := n) (rho := rho) (sep := sep) (eps := eps) hsep_pos
        hresidual_gap_cap)
      hV_cols hV_orth hEig hshift hB htarget_radius hsep_pos hgap

/-- LU-solver-facing eigen-residual inverse-iteration theorem with the
relative-tail premise stated as the residual/eigengap cap
`(n-1)*rho <= eps*sep`. -/
theorem
    inverseIteration_lu_shiftedSolve_eigenResidual_norm_le_of_component_frob_budget_orthogonal_eigenbasis_eigengap_relative_tail_of_residual_gap_cap_of_A_norm_nonneg
    {n : ℕ} {fp : FPModel} {A L_hat U_hat B V : Fin n → Fin n → ℝ}
    {mu A_norm radius rho sep eps : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hyhat_eq :
      yhat = fl_backSub fp n U_hat (fl_forwardSub fp n L_hat (v target)))
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU :
      LUBackwardError n (inverseIterationShiftedMatrix n A mu) L_hat U_hat
        (gamma fp n))
    (hn : gammaValid fp n)
    (hLU_frob :
      frobNorm (fun i j =>
        (3 * gamma fp n + gamma fp n ^ 2) *
          ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ≤ rho)
    (hresidual_gap_cap : ((n - 1 : ℕ) : ℝ) * rho ≤ eps * sep)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_orth : IsOrthogonal n V)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (htarget_radius : |lambda target - mu| ≤ radius)
    (hsep_pos : 0 < sep)
    (hgap :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep + radius ≤ |lambda a - lambda target|) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) * (eps * vecNorm2 yhat) := by
  exact
    inverseIteration_lu_shiftedSolve_eigenResidual_norm_le_of_component_frob_budget_orthogonal_eigenbasis_eigengap_relative_tail_of_A_norm_nonneg
      (n := n) (fp := fp) (A := A) (L_hat := L_hat) (U_hat := U_hat)
      (B := B) (V := V) (mu := mu) (A_norm := A_norm)
      (radius := radius) (rho := rho) (sep := sep) (eps := eps)
      (lambda := lambda) (v := v) target yhat hyhat hyhat_eq
      hL_diag hU_diag hLU hn hLU_frob
      (inverseIteration_relative_tail_le_of_pred_mul_rho_le_eps_mul_sep
        (n := n) (rho := rho) (sep := sep) (eps := eps) hsep_pos
        hresidual_gap_cap)
      hV_cols hV_orth hEig hshift hB hA hA_norm_nonneg htarget_radius
      hsep_pos hgap

/-- Matrix-budget wrapper for the source-facing near-parallel decomposition.
It discharges the eigenbasis residual expansion and the coefficient-ratio
hypotheses from a square eigenvector matrix right inverse, an operator-norm
bound for that inverse, and an operator-norm bound for the modeled
backward-error matrix `DeltaS`.  The remaining `hbudget` is the explicit
conditioning/separation estimate still owed by a cited perturbation theorem or
by a concrete rounded shifted-solver analysis. -/
theorem
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_matrix_inverse_opNorm_budget
    {n : ℕ} {A B DeltaS V V_inv : Fin n → Fin n → ℝ}
    {mu radius sep DeltaS_norm V_inv_norm : ℝ}
    {lambda beta : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (hDeltaS_op : opNorm2Le DeltaS DeltaS_norm)
    (hbudget :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        (V_inv_norm * (DeltaS_norm * vecNorm2 yhat)) * vecNorm2 (v a) ≤
          beta a *
            (|matMulVec n V_inv
                (fun i : Fin n => -matMulVec n DeltaS yhat i) target| *
              vecNorm2 (v target)))
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hscale :
      0 <
        |matMulVec n V_inv
            (fun i : Fin n => -matMulVec n DeltaS yhat i) target| *
          |(lambda target - mu)⁻¹| * vecNorm2 (v target))
    (hsep_pos : 0 < sep)
    (htarget_pos : 0 < |lambda target - mu|)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|)
    (hbeta_nonneg :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) → 0 ≤ beta a)
    (hPerturbed :
      ∀ i : Fin n,
        ∑ j : Fin n,
          (inverseIterationShiftedMatrix n A mu i j + DeltaS i j) *
            yhat j =
            v target i) :
    ∃ eta : ℝ, ∃ r : Fin n → ℝ,
      (yhat =
        fun i =>
          (lambda target - mu)⁻¹ * v target i +
            (eta * v target i + r i)) ∧
      vecNorm2 r ≤
        Finset.sum (Finset.univ.erase target)
            (fun a => beta a * (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n => -matMulVec n DeltaS yhat i) target| *
                |(lambda target - mu)⁻¹| * vecNorm2 (v target)) := by
  let residual : Fin n → ℝ := fun i => -matMulVec n DeltaS yhat i
  let coeff : Fin n → ℝ := matMulVec n V_inv residual
  have hresExpansion :
      residual = fun i => ∑ a : Fin n, coeff a * v a i := by
    simpa [residual, coeff] using
      (eigenbasis_residual_expansion_of_rightInverse
        v hV_cols hV_inv residual)
  have hres_norm :
      vecNorm2 residual ≤ DeltaS_norm * vecNorm2 yhat := by
    simpa [residual] using
      (inverseIteration_backwardErrorAction_vecNorm2_le_of_opNorm2Le
        DeltaS yhat DeltaS_norm hDeltaS_op)
  have hcoeff_ratio :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        |coeff a| * vecNorm2 (v a) ≤
          beta a * (|coeff target| * vecNorm2 (v target)) := by
    simpa [residual, coeff] using
      (inverseIteration_eigenbasis_coeff_ratio_of_inverse_opNorm_budget
        target v V_inv residual beta V_inv_norm
        (DeltaS_norm * vecNorm2 yhat) hV_inv_op hV_inv_norm_nonneg
        hres_norm hbudget)
  simpa [residual, coeff] using
    (inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_eigenbasis_component_target_radius_gap
      (n := n) (A := A) (B := B) (DeltaS := DeltaS) (mu := mu)
      (radius := radius) (sep := sep) (lambda := lambda) (v := v)
      target coeff beta yhat hEig hshift hB hscale hsep_pos htarget_pos
      htarget hsep hbeta_nonneg hcoeff_ratio hPerturbed hresExpansion)

/-- Explicit-beta matrix-budget wrapper for the source-facing near-parallel
decomposition.  Compared with
`inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_matrix_inverse_opNorm_budget`,
this version removes the abstract per-mode `hbudget`: a positive lower bound
for the target coefficient scale supplies the concrete beta values
`((V_inv_norm * (DeltaS_norm * ||yhat||₂)) * ||v a||₂) / targetScale`.
The remaining hypotheses are solver/source facts, not a replay of a hidden
machine computation. -/
theorem
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_matrix_inverse_opNorm_explicit_beta
    {n : ℕ} {A B DeltaS V V_inv : Fin n → Fin n → ℝ}
    {mu radius sep DeltaS_norm V_inv_norm targetScale : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (hDeltaS_op : opNorm2Le DeltaS DeltaS_norm)
    (htargetScale_pos : 0 < targetScale)
    (htargetScale_le :
      targetScale ≤
        |matMulVec n V_inv
            (fun i : Fin n => -matMulVec n DeltaS yhat i) target| *
          vecNorm2 (v target))
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hsep_pos : 0 < sep)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|)
    (hPerturbed :
      ∀ i : Fin n,
        ∑ j : Fin n,
          (inverseIterationShiftedMatrix n A mu i j + DeltaS i j) *
            yhat j =
            v target i) :
    ∃ eta : ℝ, ∃ r : Fin n → ℝ,
      (yhat =
        fun i =>
          (lambda target - mu)⁻¹ * v target i +
            (eta * v target i + r i)) ∧
      vecNorm2 r ≤
        Finset.sum (Finset.univ.erase target)
            (fun a =>
              (((V_inv_norm * (DeltaS_norm * vecNorm2 yhat)) *
                    vecNorm2 (v a)) / targetScale) *
                (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n => -matMulVec n DeltaS yhat i) target| *
                |(lambda target - mu)⁻¹| * vecNorm2 (v target)) := by
  let residual : Fin n → ℝ := fun i => -matMulVec n DeltaS yhat i
  let coeff : Fin n → ℝ := matMulVec n V_inv residual
  let beta : Fin n → ℝ :=
    fun a =>
      ((V_inv_norm * (DeltaS_norm * vecNorm2 yhat)) *
          vecNorm2 (v a)) / targetScale
  have hresExpansion :
      residual = fun i => ∑ a : Fin n, coeff a * v a i := by
    simpa [residual, coeff] using
      (eigenbasis_residual_expansion_of_rightInverse
        v hV_cols hV_inv residual)
  have hres_norm :
      vecNorm2 residual ≤ DeltaS_norm * vecNorm2 yhat := by
    simpa [residual] using
      (inverseIteration_backwardErrorAction_vecNorm2_le_of_opNorm2Le
        DeltaS yhat DeltaS_norm hDeltaS_op)
  have hbeta :
      (∀ a : Fin n, a ∈ (Finset.univ.erase target) → 0 ≤ beta a) ∧
      (∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        |coeff a| * vecNorm2 (v a) ≤
          beta a * (|coeff target| * vecNorm2 (v target))) := by
    simpa [residual, coeff, beta] using
      (inverseIteration_eigenbasis_coeff_ratio_of_inverse_opNorm_explicit_beta
        target v V_inv residual V_inv_norm
        (DeltaS_norm * vecNorm2 yhat) targetScale hV_inv_op
        hV_inv_norm_nonneg hres_norm htargetScale_pos htargetScale_le)
  have htarget_pos : 0 < |lambda target - mu| :=
    abs_pos.mpr (hshift target)
  have htargetCoeffScale_pos :
      0 < |coeff target| * vecNorm2 (v target) := by
    simpa [residual, coeff] using
      (lt_of_lt_of_le htargetScale_pos htargetScale_le)
  have hinv_pos : 0 < |(lambda target - mu)⁻¹| :=
    abs_pos.mpr (inv_ne_zero (hshift target))
  have hscale :
      0 <
        |coeff target| * |(lambda target - mu)⁻¹| *
          vecNorm2 (v target) := by
    have hprod :
        0 <
          |(lambda target - mu)⁻¹| *
            (|coeff target| * vecNorm2 (v target)) :=
      mul_pos hinv_pos htargetCoeffScale_pos
    rw [show
        |coeff target| * |(lambda target - mu)⁻¹| *
            vecNorm2 (v target) =
          |(lambda target - mu)⁻¹| *
            (|coeff target| * vecNorm2 (v target)) by ring]
    exact hprod
  simpa [residual, coeff, beta] using
    (inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_eigenbasis_component_target_radius_gap
      (n := n) (A := A) (B := B) (DeltaS := DeltaS) (mu := mu)
      (radius := radius) (sep := sep) (lambda := lambda) (v := v)
      target coeff beta yhat hEig hshift hB hscale hsep_pos htarget_pos
      htarget hsep hbeta.1 hbeta.2 hPerturbed hresExpansion)

/-- Perturbed shifted-solve certificate with the eigenbasis expansion and
coefficient-ratio assumptions discharged from a square eigenvector basis right
inverse and an operator-norm budget for that inverse.  The remaining
`hbudget` hypothesis is the visible conditioning/separation estimate that a
future Parlett/Golub--Van Loan theorem or concrete rounded-solver model must
prove; no historical shifted-solve trace is assumed. -/
theorem
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_inverse_opNorm_budget
    {n : ℕ} {A B DeltaS V V_inv : Fin n → Fin n → ℝ}
    {mu A_norm radius sep V_inv_norm residualNorm : ℝ}
    {lambda beta : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (hres_norm : vecNorm2 (fun i : Fin n => -matMulVec n DeltaS yhat i) ≤
      residualNorm)
    (hbudget :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        (V_inv_norm * residualNorm) * vecNorm2 (v a) ≤
          beta a *
            (|matMulVec n V_inv
                (fun i : Fin n => -matMulVec n DeltaS yhat i) target| *
              vecNorm2 (v target)))
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_bound_nonneg : 0 ≤ A_norm + |lambda target|)
    (hscale :
      0 <
        |matMulVec n V_inv
            (fun i : Fin n => -matMulVec n DeltaS yhat i) target| *
          |(lambda target - mu)⁻¹| * vecNorm2 (v target))
    (hsep_pos : 0 < sep)
    (htarget_pos : 0 < |lambda target - mu|)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|)
    (hbeta_nonneg :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) → 0 ≤ beta a)
    (hPerturbed :
      ∀ i : Fin n,
        ∑ j : Fin n,
          (inverseIterationShiftedMatrix n A mu i j + DeltaS i j) *
            yhat j =
            v target i) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) *
        ((Finset.sum (Finset.univ.erase target)
            (fun a => beta a * (radius / sep))) *
          (|matMulVec n V_inv
              (fun i : Fin n => -matMulVec n DeltaS yhat i) target| *
                |(lambda target - mu)⁻¹| * vecNorm2 (v target))) := by
  let residual : Fin n → ℝ := fun i => -matMulVec n DeltaS yhat i
  let coeff : Fin n → ℝ := matMulVec n V_inv residual
  have hresExpansion :
      residual = fun i => ∑ a : Fin n, coeff a * v a i := by
    simpa [residual, coeff] using
      (eigenbasis_residual_expansion_of_rightInverse
        v hV_cols hV_inv residual)
  have hcoeff_ratio :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        |coeff a| * vecNorm2 (v a) ≤
          beta a * (|coeff target| * vecNorm2 (v target)) := by
    simpa [residual, coeff] using
      (inverseIteration_eigenbasis_coeff_ratio_of_inverse_opNorm_budget
        target v V_inv residual beta V_inv_norm residualNorm hV_inv_op
        hV_inv_norm_nonneg hres_norm hbudget)
  simpa [residual, coeff] using
    (inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_eigenbasis_component_target_radius_gap
      (n := n) (A := A) (B := B) (DeltaS := DeltaS) (mu := mu)
      (A_norm := A_norm) (radius := radius) (sep := sep)
      (lambda := lambda) (v := v) target coeff beta yhat hEig hshift hB hA
      hA_bound_nonneg hscale hsep_pos htarget_pos htarget hsep
      hbeta_nonneg hcoeff_ratio hPerturbed hresExpansion)

/-- Variant of
`inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_inverse_opNorm_budget`
that obtains the residual norm budget directly from an operator-norm certificate
for the modeled backward-error matrix `DeltaS`.  This is the most direct local
handoff for a future rounded shifted-solver theorem: the solver may provide
`opNorm2Le DeltaS DeltaS_norm`, and the remaining `hbudget` exposes the
separation/conditioning comparison using the explicit residual radius
`DeltaS_norm * ||yhat||_2`. -/
theorem
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_matrix_inverse_opNorm_budget
    {n : ℕ} {A B DeltaS V V_inv : Fin n → Fin n → ℝ}
    {mu A_norm radius sep DeltaS_norm V_inv_norm : ℝ}
    {lambda beta : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (hDeltaS_op : opNorm2Le DeltaS DeltaS_norm)
    (hbudget :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        (V_inv_norm * (DeltaS_norm * vecNorm2 yhat)) * vecNorm2 (v a) ≤
          beta a *
            (|matMulVec n V_inv
                (fun i : Fin n => -matMulVec n DeltaS yhat i) target| *
              vecNorm2 (v target)))
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_bound_nonneg : 0 ≤ A_norm + |lambda target|)
    (hscale :
      0 <
        |matMulVec n V_inv
            (fun i : Fin n => -matMulVec n DeltaS yhat i) target| *
          |(lambda target - mu)⁻¹| * vecNorm2 (v target))
    (hsep_pos : 0 < sep)
    (htarget_pos : 0 < |lambda target - mu|)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|)
    (hbeta_nonneg :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) → 0 ≤ beta a)
    (hPerturbed :
      ∀ i : Fin n,
        ∑ j : Fin n,
          (inverseIterationShiftedMatrix n A mu i j + DeltaS i j) *
            yhat j =
            v target i) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) *
        ((Finset.sum (Finset.univ.erase target)
            (fun a => beta a * (radius / sep))) *
          (|matMulVec n V_inv
              (fun i : Fin n => -matMulVec n DeltaS yhat i) target| *
                |(lambda target - mu)⁻¹| * vecNorm2 (v target))) := by
  exact
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_inverse_opNorm_budget
      (n := n) (A := A) (B := B) (DeltaS := DeltaS) (V := V)
      (V_inv := V_inv) (mu := mu) (A_norm := A_norm) (radius := radius)
      (sep := sep) (V_inv_norm := V_inv_norm)
      (residualNorm := DeltaS_norm * vecNorm2 yhat) (lambda := lambda)
      (beta := beta) (v := v) target yhat hV_cols hV_inv hV_inv_op
      hV_inv_norm_nonneg
      (inverseIteration_backwardErrorAction_vecNorm2_le_of_opNorm2Le
        DeltaS yhat DeltaS_norm hDeltaS_op)
      hbudget hEig hshift hB hA hA_bound_nonneg hscale hsep_pos
      htarget_pos htarget hsep hbeta_nonneg hPerturbed

/-- Explicit-beta matrix-budget wrapper for the final inverse-iteration
eigen-residual bound.  This removes the abstract coefficient budget from the
matrix-budget residual theorem, just as the near-parallel decomposition wrapper
does: a positive lower bound on the target coefficient/eigenvector scale
constructs the concrete beta values
`((V_inv_norm * (DeltaS_norm * ||yhat||₂)) * ||v a||₂) / targetScale`.
The remaining assumptions are the source/solver facts that a Parlett--Golub--Van
Loan theorem or a fully specified rounded shifted-solver certificate must
supply. -/
theorem
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_matrix_inverse_opNorm_explicit_beta
    {n : ℕ} {A B DeltaS V V_inv : Fin n → Fin n → ℝ}
    {mu A_norm radius sep DeltaS_norm V_inv_norm targetScale : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (hDeltaS_op : opNorm2Le DeltaS DeltaS_norm)
    (htargetScale_pos : 0 < targetScale)
    (htargetScale_le :
      targetScale ≤
        |matMulVec n V_inv
            (fun i : Fin n => -matMulVec n DeltaS yhat i) target| *
          vecNorm2 (v target))
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_bound_nonneg : 0 ≤ A_norm + |lambda target|)
    (hsep_pos : 0 < sep)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|)
    (hPerturbed :
      ∀ i : Fin n,
        ∑ j : Fin n,
          (inverseIterationShiftedMatrix n A mu i j + DeltaS i j) *
            yhat j =
            v target i) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) *
        (Finset.sum (Finset.univ.erase target)
            (fun a =>
              (((V_inv_norm * (DeltaS_norm * vecNorm2 yhat)) *
                    vecNorm2 (v a)) / targetScale) *
                (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n => -matMulVec n DeltaS yhat i) target| *
            |(lambda target - mu)⁻¹| * vecNorm2 (v target))) := by
  let residual : Fin n → ℝ := fun i => -matMulVec n DeltaS yhat i
  let coeff : Fin n → ℝ := matMulVec n V_inv residual
  let beta : Fin n → ℝ :=
    fun a =>
      ((V_inv_norm * (DeltaS_norm * vecNorm2 yhat)) *
          vecNorm2 (v a)) / targetScale
  have hresExpansion :
      residual = fun i => ∑ a : Fin n, coeff a * v a i := by
    simpa [residual, coeff] using
      (eigenbasis_residual_expansion_of_rightInverse
        v hV_cols hV_inv residual)
  have hres_norm :
      vecNorm2 residual ≤ DeltaS_norm * vecNorm2 yhat := by
    simpa [residual] using
      (inverseIteration_backwardErrorAction_vecNorm2_le_of_opNorm2Le
        DeltaS yhat DeltaS_norm hDeltaS_op)
  have hbeta :
      (∀ a : Fin n, a ∈ (Finset.univ.erase target) → 0 ≤ beta a) ∧
      (∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        |coeff a| * vecNorm2 (v a) ≤
          beta a * (|coeff target| * vecNorm2 (v target))) := by
    simpa [residual, coeff, beta] using
      (inverseIteration_eigenbasis_coeff_ratio_of_inverse_opNorm_explicit_beta
        target v V_inv residual V_inv_norm
        (DeltaS_norm * vecNorm2 yhat) targetScale hV_inv_op
        hV_inv_norm_nonneg hres_norm htargetScale_pos htargetScale_le)
  have htarget_pos : 0 < |lambda target - mu| :=
    abs_pos.mpr (hshift target)
  have htargetCoeffScale_pos :
      0 < |coeff target| * vecNorm2 (v target) := by
    simpa [residual, coeff] using
      (lt_of_lt_of_le htargetScale_pos htargetScale_le)
  have hinv_pos : 0 < |(lambda target - mu)⁻¹| :=
    abs_pos.mpr (inv_ne_zero (hshift target))
  have hscale :
      0 <
        |coeff target| * |(lambda target - mu)⁻¹| *
          vecNorm2 (v target) := by
    have hprod :
        0 <
          |(lambda target - mu)⁻¹| *
            (|coeff target| * vecNorm2 (v target)) :=
      mul_pos hinv_pos htargetCoeffScale_pos
    rw [show
        |coeff target| * |(lambda target - mu)⁻¹| *
            vecNorm2 (v target) =
          |(lambda target - mu)⁻¹| *
            (|coeff target| * vecNorm2 (v target)) by ring]
    exact hprod
  simpa [residual, coeff, beta] using
    (inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_eigenbasis_component_target_radius_gap
      (n := n) (A := A) (B := B) (DeltaS := DeltaS) (mu := mu)
      (A_norm := A_norm) (radius := radius) (sep := sep)
      (lambda := lambda) (v := v) target coeff beta yhat hEig hshift hB hA
      hA_bound_nonneg hscale hsep_pos htarget_pos htarget hsep
      hbeta.1 hbeta.2 hPerturbed hresExpansion)

/-- Source-facing version of
`inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_matrix_inverse_opNorm_explicit_beta`
where the nonnegativity side condition is the ordinary operator-norm premise
`0 <= A_norm`. -/
theorem
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_matrix_inverse_opNorm_explicit_beta_of_A_norm_nonneg
    {n : ℕ} {A B DeltaS V V_inv : Fin n → Fin n → ℝ}
    {mu A_norm radius sep DeltaS_norm V_inv_norm targetScale : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (hDeltaS_op : opNorm2Le DeltaS DeltaS_norm)
    (htargetScale_pos : 0 < targetScale)
    (htargetScale_le :
      targetScale ≤
        |matMulVec n V_inv
            (fun i : Fin n => -matMulVec n DeltaS yhat i) target| *
          vecNorm2 (v target))
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (hsep_pos : 0 < sep)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|)
    (hPerturbed :
      ∀ i : Fin n,
        ∑ j : Fin n,
          (inverseIterationShiftedMatrix n A mu i j + DeltaS i j) *
            yhat j =
            v target i) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) *
        (Finset.sum (Finset.univ.erase target)
            (fun a =>
              (((V_inv_norm * (DeltaS_norm * vecNorm2 yhat)) *
                    vecNorm2 (v a)) / targetScale) *
                (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n => -matMulVec n DeltaS yhat i) target| *
            |(lambda target - mu)⁻¹| * vecNorm2 (v target))) := by
  exact
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_matrix_inverse_opNorm_explicit_beta
      (n := n) (A := A) (B := B) (DeltaS := DeltaS) (V := V)
      (V_inv := V_inv) (mu := mu) (A_norm := A_norm) (radius := radius)
      (sep := sep) (DeltaS_norm := DeltaS_norm)
      (V_inv_norm := V_inv_norm) (targetScale := targetScale)
      (lambda := lambda) (v := v) target yhat hV_cols hV_inv hV_inv_op
      hV_inv_norm_nonneg hDeltaS_op htargetScale_pos htargetScale_le hEig
      hshift hB hA (add_nonneg hA_norm_nonneg (abs_nonneg (lambda target)))
      hsep_pos htarget hsep hPerturbed

/-- Direct-target-coefficient version of the source-facing near-parallel
decomposition.  This keeps the future solver/source obligations visible
(`DeltaS`, eigenbasis inverse norm, target-radius/non-target-gap, and the
modeled perturbed solve), but replaces the abstract `targetScale` parameter by
the actual nonzero target residual coefficient times the target eigenvector
norm. -/
theorem
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_matrix_inverse_opNorm_direct_target
    {n : ℕ} {A B DeltaS V V_inv : Fin n → Fin n → ℝ}
    {mu radius sep DeltaS_norm V_inv_norm : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (hDeltaS_op : opNorm2Le DeltaS DeltaS_norm)
    (hcoeff :
      matMulVec n V_inv
        (fun i : Fin n => -matMulVec n DeltaS yhat i) target ≠ 0)
    (hvec : ∃ i : Fin n, v target i ≠ 0)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hsep_pos : 0 < sep)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|)
    (hPerturbed :
      ∀ i : Fin n,
        ∑ j : Fin n,
          (inverseIterationShiftedMatrix n A mu i j + DeltaS i j) *
            yhat j =
            v target i) :
    ∃ eta : ℝ, ∃ r : Fin n → ℝ,
      (yhat =
        fun i =>
          (lambda target - mu)⁻¹ * v target i +
            (eta * v target i + r i)) ∧
      vecNorm2 r ≤
        Finset.sum (Finset.univ.erase target)
            (fun a =>
              (((V_inv_norm * (DeltaS_norm * vecNorm2 yhat)) *
                    vecNorm2 (v a)) /
                  (|matMulVec n V_inv
                      (fun i : Fin n => -matMulVec n DeltaS yhat i) target| *
                    vecNorm2 (v target))) *
                (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n => -matMulVec n DeltaS yhat i) target| *
            |(lambda target - mu)⁻¹| * vecNorm2 (v target)) := by
  exact
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_matrix_inverse_opNorm_explicit_beta
      (n := n) (A := A) (B := B) (DeltaS := DeltaS) (V := V)
      (V_inv := V_inv) (mu := mu) (radius := radius) (sep := sep)
      (DeltaS_norm := DeltaS_norm) (V_inv_norm := V_inv_norm)
      (targetScale :=
        |matMulVec n V_inv
            (fun i : Fin n => -matMulVec n DeltaS yhat i) target| *
          vecNorm2 (v target))
      (lambda := lambda) (v := v) target yhat hV_cols hV_inv hV_inv_op
      hV_inv_norm_nonneg hDeltaS_op
      (inverseIteration_target_coeff_vecNorm_scale_pos_of_coeff_ne_zero
        target v V_inv
        (fun i : Fin n => -matMulVec n DeltaS yhat i) hcoeff hvec)
      (le_rfl) hEig hshift hB hsep_pos htarget hsep hPerturbed

/-- Direct-target-coefficient version of the final inverse-iteration
eigen-residual bound.  This is the source-facing final wrapper for the current
local route: a future Parlett/Golub--Van Loan theorem or a concrete rounded
shifted-solver certificate may supply the nonzero target coefficient evidence,
and Lean then constructs the explicit beta denominator itself. -/
theorem
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_matrix_inverse_opNorm_direct_target_of_A_norm_nonneg
    {n : ℕ} {A B DeltaS V V_inv : Fin n → Fin n → ℝ}
    {mu A_norm radius sep DeltaS_norm V_inv_norm : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (hDeltaS_op : opNorm2Le DeltaS DeltaS_norm)
    (hcoeff :
      matMulVec n V_inv
        (fun i : Fin n => -matMulVec n DeltaS yhat i) target ≠ 0)
    (hvec : ∃ i : Fin n, v target i ≠ 0)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (hsep_pos : 0 < sep)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|)
    (hPerturbed :
      ∀ i : Fin n,
        ∑ j : Fin n,
          (inverseIterationShiftedMatrix n A mu i j + DeltaS i j) *
            yhat j =
            v target i) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) *
        (Finset.sum (Finset.univ.erase target)
            (fun a =>
              (((V_inv_norm * (DeltaS_norm * vecNorm2 yhat)) *
                    vecNorm2 (v a)) /
                  (|matMulVec n V_inv
                      (fun i : Fin n => -matMulVec n DeltaS yhat i) target| *
                    vecNorm2 (v target))) *
                (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n => -matMulVec n DeltaS yhat i) target| *
            |(lambda target - mu)⁻¹| * vecNorm2 (v target))) := by
  exact
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_matrix_inverse_opNorm_explicit_beta_of_A_norm_nonneg
      (n := n) (A := A) (B := B) (DeltaS := DeltaS) (V := V)
      (V_inv := V_inv) (mu := mu) (A_norm := A_norm) (radius := radius)
      (sep := sep) (DeltaS_norm := DeltaS_norm)
      (V_inv_norm := V_inv_norm)
      (targetScale :=
        |matMulVec n V_inv
            (fun i : Fin n => -matMulVec n DeltaS yhat i) target| *
          vecNorm2 (v target))
      (lambda := lambda) (v := v) target yhat hV_cols hV_inv hV_inv_op
      hV_inv_norm_nonneg hDeltaS_op
      (inverseIteration_target_coeff_vecNorm_scale_pos_of_coeff_ne_zero
        target v V_inv
        (fun i : Fin n => -matMulVec n DeltaS yhat i) hcoeff hvec)
      (le_rfl) hEig hshift hB hA hA_norm_nonneg hsep_pos htarget hsep
      hPerturbed

/-- Rank-one-residual version of the source-facing near-parallel decomposition.
This instantiates the abstract backward-error matrix in
`inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_matrix_inverse_opNorm_direct_target`
with the canonical rank-one shifted-system residual perturbation.  It therefore
exposes the solver side as the actual residual of the approximate shifted solve,
while leaving the genuine source/solver hypotheses about eigenbasis
conditioning, separation, and target coefficient evidence visible. -/
theorem
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_rank_one_backward_error_direct_target
    {n : ℕ} {A B V V_inv : Fin n → Fin n → ℝ}
    {mu radius sep V_inv_norm : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (hcoeff :
      matMulVec n V_inv
        (fun i : Fin n =>
          -matMulVec n
            (inverseIterationShiftedRankOneBackwardError n A mu (v target) yhat)
            yhat i) target ≠ 0)
    (hvec : ∃ i : Fin n, v target i ≠ 0)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hsep_pos : 0 < sep)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|) :
    ∃ eta : ℝ, ∃ r : Fin n → ℝ,
      (yhat =
        fun i =>
          (lambda target - mu)⁻¹ * v target i +
            (eta * v target i + r i)) ∧
      vecNorm2 r ≤
        Finset.sum (Finset.univ.erase target)
            (fun a =>
              (((V_inv_norm *
                    ((vecNorm2
                          (residualVec n
                            (inverseIterationShiftedMatrix n A mu) yhat
                            (v target)) /
                        vecNorm2 yhat) *
                      vecNorm2 yhat)) *
                    vecNorm2 (v a)) /
                  (|matMulVec n V_inv
                      (fun i : Fin n =>
                        -matMulVec n
                          (inverseIterationShiftedRankOneBackwardError n A mu
                            (v target) yhat) yhat i) target| *
                    vecNorm2 (v target))) *
                (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n =>
                -matMulVec n
                  (inverseIterationShiftedRankOneBackwardError n A mu
                    (v target) yhat) yhat i) target| *
            |(lambda target - mu)⁻¹| * vecNorm2 (v target)) := by
  exact
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_matrix_inverse_opNorm_direct_target
      (n := n) (A := A) (B := B)
      (DeltaS := inverseIterationShiftedRankOneBackwardError n A mu (v target) yhat)
      (V := V) (V_inv := V_inv) (mu := mu) (radius := radius)
      (sep := sep)
      (DeltaS_norm :=
        vecNorm2
            (residualVec n (inverseIterationShiftedMatrix n A mu) yhat
              (v target)) /
          vecNorm2 yhat)
      (V_inv_norm := V_inv_norm) (lambda := lambda) (v := v)
      target yhat hV_cols hV_inv hV_inv_op hV_inv_norm_nonneg
      (inverseIterationShiftedRankOneBackwardError_opNorm2Le n A mu
        (v target) yhat hyhat)
      hcoeff hvec hEig hshift hB hsep_pos htarget hsep
      (inverseIterationShiftedRankOneBackwardError_solves n A mu
        (v target) yhat hyhat)

/-- Rank-one-residual version of the final inverse-iteration eigen-residual
bound.  This is the most concrete local handoff currently available without
choosing a Parlett/Golub--Van Loan theorem or a fully specified rounded solver:
the abstract backward-error matrix is the canonical rank-one residual
perturbation of the actual shifted solve output. -/
theorem
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_rank_one_backward_error_direct_target_of_A_norm_nonneg
    {n : ℕ} {A B V V_inv : Fin n → Fin n → ℝ}
    {mu A_norm radius sep V_inv_norm : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (hcoeff :
      matMulVec n V_inv
        (fun i : Fin n =>
          -matMulVec n
            (inverseIterationShiftedRankOneBackwardError n A mu (v target) yhat)
            yhat i) target ≠ 0)
    (hvec : ∃ i : Fin n, v target i ≠ 0)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (hsep_pos : 0 < sep)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) *
        (Finset.sum (Finset.univ.erase target)
            (fun a =>
              (((V_inv_norm *
                    ((vecNorm2
                          (residualVec n
                            (inverseIterationShiftedMatrix n A mu) yhat
                            (v target)) /
                        vecNorm2 yhat) *
                      vecNorm2 yhat)) *
                    vecNorm2 (v a)) /
                  (|matMulVec n V_inv
                      (fun i : Fin n =>
                        -matMulVec n
                          (inverseIterationShiftedRankOneBackwardError n A mu
                            (v target) yhat) yhat i) target| *
                    vecNorm2 (v target))) *
                (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n =>
                -matMulVec n
                  (inverseIterationShiftedRankOneBackwardError n A mu
                    (v target) yhat) yhat i) target| *
            |(lambda target - mu)⁻¹| * vecNorm2 (v target))) := by
  exact
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_matrix_inverse_opNorm_direct_target_of_A_norm_nonneg
      (n := n) (A := A) (B := B)
      (DeltaS := inverseIterationShiftedRankOneBackwardError n A mu (v target) yhat)
      (V := V) (V_inv := V_inv) (mu := mu) (A_norm := A_norm)
      (radius := radius) (sep := sep)
      (DeltaS_norm :=
        vecNorm2
            (residualVec n (inverseIterationShiftedMatrix n A mu) yhat
              (v target)) /
          vecNorm2 yhat)
      (V_inv_norm := V_inv_norm) (lambda := lambda) (v := v)
      target yhat hV_cols hV_inv hV_inv_op hV_inv_norm_nonneg
      (inverseIterationShiftedRankOneBackwardError_opNorm2Le n A mu
        (v target) yhat hyhat)
      hcoeff hvec hEig hshift hB hA hA_norm_nonneg hsep_pos htarget hsep
      (inverseIterationShiftedRankOneBackwardError_solves n A mu
        (v target) yhat hyhat)

/-- Cleaner residual-norm form of
`inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_rank_one_backward_error_direct_target`.
It cancels the normalization factor introduced by the rank-one backward-error
certificate, so the displayed tail bound uses the shifted residual norm itself.
-/
theorem
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_rank_one_backward_error_direct_target_residual_norm
    {n : ℕ} {A B V V_inv : Fin n → Fin n → ℝ}
    {mu radius sep V_inv_norm : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (hcoeff :
      matMulVec n V_inv
        (fun i : Fin n =>
          -matMulVec n
            (inverseIterationShiftedRankOneBackwardError n A mu (v target) yhat)
            yhat i) target ≠ 0)
    (hvec : ∃ i : Fin n, v target i ≠ 0)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hsep_pos : 0 < sep)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|) :
    ∃ eta : ℝ, ∃ r : Fin n → ℝ,
      (yhat =
        fun i =>
          (lambda target - mu)⁻¹ * v target i +
            (eta * v target i + r i)) ∧
      vecNorm2 r ≤
        Finset.sum (Finset.univ.erase target)
            (fun a =>
              (((V_inv_norm *
                    vecNorm2
                      (residualVec n
                        (inverseIterationShiftedMatrix n A mu) yhat
                        (v target))) *
                    vecNorm2 (v a)) /
                  (|matMulVec n V_inv
                      (fun i : Fin n =>
                        -matMulVec n
                          (inverseIterationShiftedRankOneBackwardError n A mu
                            (v target) yhat) yhat i) target| *
                    vecNorm2 (v target))) *
                (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n =>
                -matMulVec n
                  (inverseIterationShiftedRankOneBackwardError n A mu
                    (v target) yhat) yhat i) target| *
            |(lambda target - mu)⁻¹| * vecNorm2 (v target)) := by
  have hcancel :
      (vecNorm2
            (residualVec n (inverseIterationShiftedMatrix n A mu) yhat
              (v target)) /
          vecNorm2 yhat) *
        vecNorm2 yhat =
          vecNorm2
            (residualVec n (inverseIterationShiftedMatrix n A mu) yhat
              (v target)) := by
    field_simp [hyhat]
  simpa [hcancel] using
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_rank_one_backward_error_direct_target
      (n := n) (A := A) (B := B) (V := V) (V_inv := V_inv)
      (mu := mu) (radius := radius) (sep := sep)
      (V_inv_norm := V_inv_norm) (lambda := lambda) (v := v)
      target yhat hyhat hV_cols hV_inv hV_inv_op hV_inv_norm_nonneg
      hcoeff hvec hEig hshift hB hsep_pos htarget hsep

/-- Cleaner residual-norm form of the rank-one-residual inverse-iteration
eigen-residual bound.  The only change from the direct-target theorem above is
that the residual quotient times `||yhat||_2` is simplified to the actual
shifted residual norm. -/
theorem
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_rank_one_backward_error_direct_target_residual_norm_of_A_norm_nonneg
    {n : ℕ} {A B V V_inv : Fin n → Fin n → ℝ}
    {mu A_norm radius sep V_inv_norm : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (hcoeff :
      matMulVec n V_inv
        (fun i : Fin n =>
          -matMulVec n
            (inverseIterationShiftedRankOneBackwardError n A mu (v target) yhat)
            yhat i) target ≠ 0)
    (hvec : ∃ i : Fin n, v target i ≠ 0)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (hsep_pos : 0 < sep)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) *
        (Finset.sum (Finset.univ.erase target)
            (fun a =>
              (((V_inv_norm *
                    vecNorm2
                      (residualVec n
                        (inverseIterationShiftedMatrix n A mu) yhat
                        (v target))) *
                    vecNorm2 (v a)) /
                  (|matMulVec n V_inv
                      (fun i : Fin n =>
                        -matMulVec n
                          (inverseIterationShiftedRankOneBackwardError n A mu
                            (v target) yhat) yhat i) target| *
                    vecNorm2 (v target))) *
                (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n =>
                -matMulVec n
                  (inverseIterationShiftedRankOneBackwardError n A mu
                    (v target) yhat) yhat i) target| *
            |(lambda target - mu)⁻¹| * vecNorm2 (v target))) := by
  have hcancel :
      (vecNorm2
            (residualVec n (inverseIterationShiftedMatrix n A mu) yhat
              (v target)) /
          vecNorm2 yhat) *
        vecNorm2 yhat =
          vecNorm2
            (residualVec n (inverseIterationShiftedMatrix n A mu) yhat
              (v target)) := by
    field_simp [hyhat]
  simpa [hcancel] using
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_rank_one_backward_error_direct_target_of_A_norm_nonneg
      (n := n) (A := A) (B := B) (V := V) (V_inv := V_inv)
      (mu := mu) (A_norm := A_norm) (radius := radius) (sep := sep)
      (V_inv_norm := V_inv_norm) (lambda := lambda) (v := v)
      target yhat hyhat hV_cols hV_inv hV_inv_op hV_inv_norm_nonneg
      hcoeff hvec hEig hshift hB hA hA_norm_nonneg hsep_pos htarget hsep

/-- Source-facing residual-coefficient form of the rank-one-residual
near-parallel decomposition.  Compared with
`inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_rank_one_backward_error_direct_target_residual_norm`,
the nonzero target-coefficient hypothesis and displayed bound are stated using
the actual shifted residual rather than the internal rank-one perturbation. -/
theorem
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_rank_one_backward_error_residual_target_coeff
    {n : ℕ} {A B V V_inv : Fin n → Fin n → ℝ}
    {mu radius sep V_inv_norm : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (hcoeff :
      matMulVec n V_inv
        (fun i : Fin n =>
          -residualVec n (inverseIterationShiftedMatrix n A mu) yhat
            (v target) i) target ≠ 0)
    (hvec : ∃ i : Fin n, v target i ≠ 0)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hsep_pos : 0 < sep)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|) :
    ∃ eta : ℝ, ∃ r : Fin n → ℝ,
      (yhat =
        fun i =>
          (lambda target - mu)⁻¹ * v target i +
            (eta * v target i + r i)) ∧
      vecNorm2 r ≤
        Finset.sum (Finset.univ.erase target)
            (fun a =>
              (((V_inv_norm *
                    vecNorm2
                      (residualVec n
                        (inverseIterationShiftedMatrix n A mu) yhat
                        (v target))) *
                    vecNorm2 (v a)) /
                  (|matMulVec n V_inv
                      (fun i : Fin n =>
                        -residualVec n
                          (inverseIterationShiftedMatrix n A mu) yhat
                          (v target) i) target| *
                    vecNorm2 (v target))) *
                (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n =>
                -residualVec n
                  (inverseIterationShiftedMatrix n A mu) yhat
                  (v target) i) target| *
            |(lambda target - mu)⁻¹| * vecNorm2 (v target)) := by
  have hcoeff_rank :
      matMulVec n V_inv
        (fun i : Fin n =>
          -matMulVec n
            (inverseIterationShiftedRankOneBackwardError n A mu (v target) yhat)
            yhat i) target ≠ 0 := by
    rw [inverseIterationShiftedRankOneBackwardError_targetCoeff_eq_neg_residualCoeff
      n A V_inv mu (v target) yhat target hyhat]
    exact hcoeff
  simpa [inverseIterationShiftedRankOneBackwardError_targetCoeff_eq_neg_residualCoeff
      n A V_inv mu (v target) yhat target hyhat] using
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_rank_one_backward_error_direct_target_residual_norm
      (n := n) (A := A) (B := B) (V := V) (V_inv := V_inv)
      (mu := mu) (radius := radius) (sep := sep)
      (V_inv_norm := V_inv_norm) (lambda := lambda) (v := v)
      target yhat hyhat hV_cols hV_inv hV_inv_op hV_inv_norm_nonneg
      hcoeff_rank hvec hEig hshift hB hsep_pos htarget hsep

/-- Source-facing residual-coefficient form of the rank-one-residual
inverse-iteration eigen-residual bound.  This is the same final local handoff
as the direct-target residual-norm theorem, but the target-direction evidence is
phrased in terms of the actual shifted residual. -/
theorem
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_rank_one_backward_error_residual_target_coeff_of_A_norm_nonneg
    {n : ℕ} {A B V V_inv : Fin n → Fin n → ℝ}
    {mu A_norm radius sep V_inv_norm : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (hcoeff :
      matMulVec n V_inv
        (fun i : Fin n =>
          -residualVec n (inverseIterationShiftedMatrix n A mu) yhat
            (v target) i) target ≠ 0)
    (hvec : ∃ i : Fin n, v target i ≠ 0)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (hsep_pos : 0 < sep)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) *
        (Finset.sum (Finset.univ.erase target)
            (fun a =>
              (((V_inv_norm *
                    vecNorm2
                      (residualVec n
                        (inverseIterationShiftedMatrix n A mu) yhat
                        (v target))) *
                    vecNorm2 (v a)) /
                  (|matMulVec n V_inv
                      (fun i : Fin n =>
                        -residualVec n
                          (inverseIterationShiftedMatrix n A mu) yhat
                          (v target) i) target| *
                    vecNorm2 (v target))) *
                (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n =>
                -residualVec n
                  (inverseIterationShiftedMatrix n A mu) yhat
                  (v target) i) target| *
            |(lambda target - mu)⁻¹| * vecNorm2 (v target))) := by
  have hcoeff_rank :
      matMulVec n V_inv
        (fun i : Fin n =>
          -matMulVec n
            (inverseIterationShiftedRankOneBackwardError n A mu (v target) yhat)
            yhat i) target ≠ 0 := by
    rw [inverseIterationShiftedRankOneBackwardError_targetCoeff_eq_neg_residualCoeff
      n A V_inv mu (v target) yhat target hyhat]
    exact hcoeff
  simpa [inverseIterationShiftedRankOneBackwardError_targetCoeff_eq_neg_residualCoeff
      n A V_inv mu (v target) yhat target hyhat] using
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_rank_one_backward_error_direct_target_residual_norm_of_A_norm_nonneg
      (n := n) (A := A) (B := B) (V := V) (V_inv := V_inv)
      (mu := mu) (A_norm := A_norm) (radius := radius) (sep := sep)
      (V_inv_norm := V_inv_norm) (lambda := lambda) (v := v)
      target yhat hyhat hV_cols hV_inv hV_inv_op hV_inv_norm_nonneg
      hcoeff_rank hvec hEig hshift hB hA hA_norm_nonneg hsep_pos htarget hsep

/-- Source-facing target-scale form of the rank-one-residual near-parallel
decomposition.  This is the version a future Parlett/Golub--Van Loan theorem
or rounded shifted-solver certificate can use when it supplies a positive lower
bound for the actual shifted-residual target coefficient scale, rather than
only a nonzero coefficient. -/
theorem
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_rank_one_backward_error_residual_target_scale
    {n : ℕ} {A B V V_inv : Fin n → Fin n → ℝ}
    {mu radius sep V_inv_norm targetScale : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (htargetScale_pos : 0 < targetScale)
    (htargetScale_le :
      targetScale ≤
        |matMulVec n V_inv
            (fun i : Fin n =>
              -residualVec n (inverseIterationShiftedMatrix n A mu) yhat
                (v target) i) target| *
          vecNorm2 (v target))
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hsep_pos : 0 < sep)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|) :
    ∃ eta : ℝ, ∃ r : Fin n → ℝ,
      (yhat =
        fun i =>
          (lambda target - mu)⁻¹ * v target i +
            (eta * v target i + r i)) ∧
      vecNorm2 r ≤
        Finset.sum (Finset.univ.erase target)
            (fun a =>
              (((V_inv_norm *
                    vecNorm2
                      (residualVec n
                        (inverseIterationShiftedMatrix n A mu) yhat
                        (v target))) *
                    vecNorm2 (v a)) /
                  targetScale) *
                (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n =>
                -residualVec n
                  (inverseIterationShiftedMatrix n A mu) yhat
                  (v target) i) target| *
            |(lambda target - mu)⁻¹| * vecNorm2 (v target)) := by
  have hcancel :
      (vecNorm2
            (residualVec n (inverseIterationShiftedMatrix n A mu) yhat
              (v target)) /
          vecNorm2 yhat) *
        vecNorm2 yhat =
          vecNorm2
            (residualVec n (inverseIterationShiftedMatrix n A mu) yhat
              (v target)) := by
    field_simp [hyhat]
  have htargetScale_le_rank :
      targetScale ≤
        |matMulVec n V_inv
            (fun i : Fin n =>
              -matMulVec n
                (inverseIterationShiftedRankOneBackwardError n A mu
                  (v target) yhat) yhat i) target| *
          vecNorm2 (v target) := by
    simpa [inverseIterationShiftedRankOneBackwardError_targetCoeff_eq_neg_residualCoeff
      n A V_inv mu (v target) yhat target hyhat] using htargetScale_le
  simpa [hcancel,
      inverseIterationShiftedRankOneBackwardError_targetCoeff_eq_neg_residualCoeff
        n A V_inv mu (v target) yhat target hyhat] using
    (inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_matrix_inverse_opNorm_explicit_beta
      (n := n) (A := A) (B := B)
      (DeltaS := inverseIterationShiftedRankOneBackwardError n A mu (v target) yhat)
      (V := V) (V_inv := V_inv) (mu := mu) (radius := radius)
      (sep := sep)
      (DeltaS_norm :=
        vecNorm2
            (residualVec n (inverseIterationShiftedMatrix n A mu) yhat
              (v target)) /
          vecNorm2 yhat)
      (V_inv_norm := V_inv_norm) (targetScale := targetScale)
      (lambda := lambda) (v := v) target yhat hV_cols hV_inv
      hV_inv_op hV_inv_norm_nonneg
      (inverseIterationShiftedRankOneBackwardError_opNorm2Le n A mu
        (v target) yhat hyhat)
      htargetScale_pos htargetScale_le_rank hEig hshift hB hsep_pos htarget
      hsep
      (inverseIterationShiftedRankOneBackwardError_solves n A mu
        (v target) yhat hyhat))

/-- Source-facing target-scale form of the rank-one-residual final
inverse-iteration eigen-residual bound.  The target coefficient lower bound is
stated for the actual shifted residual, and the displayed beta term uses the
actual shifted residual norm. -/
theorem
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_rank_one_backward_error_residual_target_scale_of_A_norm_nonneg
    {n : ℕ} {A B V V_inv : Fin n → Fin n → ℝ}
    {mu A_norm radius sep V_inv_norm targetScale : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (htargetScale_pos : 0 < targetScale)
    (htargetScale_le :
      targetScale ≤
        |matMulVec n V_inv
            (fun i : Fin n =>
              -residualVec n (inverseIterationShiftedMatrix n A mu) yhat
                (v target) i) target| *
          vecNorm2 (v target))
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (hsep_pos : 0 < sep)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) *
        (Finset.sum (Finset.univ.erase target)
            (fun a =>
              (((V_inv_norm *
                    vecNorm2
                      (residualVec n
                        (inverseIterationShiftedMatrix n A mu) yhat
                        (v target))) *
                    vecNorm2 (v a)) /
                  targetScale) *
                (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n =>
                -residualVec n
                  (inverseIterationShiftedMatrix n A mu) yhat
                  (v target) i) target| *
            |(lambda target - mu)⁻¹| * vecNorm2 (v target))) := by
  have hcancel :
      (vecNorm2
            (residualVec n (inverseIterationShiftedMatrix n A mu) yhat
              (v target)) /
          vecNorm2 yhat) *
        vecNorm2 yhat =
          vecNorm2
            (residualVec n (inverseIterationShiftedMatrix n A mu) yhat
              (v target)) := by
    field_simp [hyhat]
  have htargetScale_le_rank :
      targetScale ≤
        |matMulVec n V_inv
            (fun i : Fin n =>
              -matMulVec n
                (inverseIterationShiftedRankOneBackwardError n A mu
                  (v target) yhat) yhat i) target| *
          vecNorm2 (v target) := by
    simpa [inverseIterationShiftedRankOneBackwardError_targetCoeff_eq_neg_residualCoeff
      n A V_inv mu (v target) yhat target hyhat] using htargetScale_le
  simpa [hcancel,
      inverseIterationShiftedRankOneBackwardError_targetCoeff_eq_neg_residualCoeff
        n A V_inv mu (v target) yhat target hyhat] using
    (inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_matrix_inverse_opNorm_explicit_beta_of_A_norm_nonneg
      (n := n) (A := A) (B := B)
      (DeltaS := inverseIterationShiftedRankOneBackwardError n A mu (v target) yhat)
      (V := V) (V_inv := V_inv) (mu := mu) (A_norm := A_norm)
      (radius := radius) (sep := sep)
      (DeltaS_norm :=
        vecNorm2
            (residualVec n (inverseIterationShiftedMatrix n A mu) yhat
              (v target)) /
          vecNorm2 yhat)
      (V_inv_norm := V_inv_norm) (targetScale := targetScale)
      (lambda := lambda) (v := v) target yhat hV_cols hV_inv
      hV_inv_op hV_inv_norm_nonneg
      (inverseIterationShiftedRankOneBackwardError_opNorm2Le n A mu
        (v target) yhat hyhat)
      htargetScale_pos htargetScale_le_rank hEig hshift hB hA
      hA_norm_nonneg hsep_pos htarget hsep
      (inverseIterationShiftedRankOneBackwardError_solves n A mu
        (v target) yhat hyhat))

/-- Frobenius-inverse specialization of the residual-norm target-scale
rank-one residual near-parallel decomposition.  This is the actual-residual
counterpart of the relative-residual Frobenius wrapper below: the displayed
beta factor uses `||rhs-(A-mu I)yhat||_2` and the eigenbasis-inverse budget is
`frobNorm V_inv`. -/
theorem
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_rank_one_backward_error_residual_target_scale_frobNorm_inverse
    {n : ℕ} {A B V V_inv : Fin n → Fin n → ℝ}
    {mu radius sep targetScale : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (htargetScale_pos : 0 < targetScale)
    (htargetScale_le :
      targetScale ≤
        |matMulVec n V_inv
            (fun i : Fin n =>
              -residualVec n (inverseIterationShiftedMatrix n A mu) yhat
                (v target) i) target| *
          vecNorm2 (v target))
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hsep_pos : 0 < sep)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|) :
    ∃ eta : ℝ, ∃ r : Fin n → ℝ,
      (yhat =
        fun i =>
          (lambda target - mu)⁻¹ * v target i +
            (eta * v target i + r i)) ∧
      vecNorm2 r ≤
        Finset.sum (Finset.univ.erase target)
            (fun a =>
              (((frobNorm V_inv *
                    vecNorm2
                      (residualVec n
                        (inverseIterationShiftedMatrix n A mu) yhat
                        (v target))) *
                    vecNorm2 (v a)) /
                  targetScale) *
                (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n =>
                -residualVec n
                  (inverseIterationShiftedMatrix n A mu) yhat
                  (v target) i) target| *
            |(lambda target - mu)⁻¹| * vecNorm2 (v target)) := by
  exact
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_rank_one_backward_error_residual_target_scale
      (n := n) (A := A) (B := B) (V := V) (V_inv := V_inv)
      (mu := mu) (radius := radius) (sep := sep)
      (V_inv_norm := frobNorm V_inv) (targetScale := targetScale)
      (lambda := lambda) (v := v) target yhat hyhat hV_cols hV_inv
      (opNorm2Le_of_frobNorm_self V_inv) (frobNorm_nonneg V_inv)
      htargetScale_pos htargetScale_le hEig hshift hB hsep_pos htarget
      hsep

/-- Frobenius-inverse specialization of the residual-norm target-scale final
inverse-iteration eigen-residual bound. -/
theorem
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_rank_one_backward_error_residual_target_scale_frobNorm_inverse_of_A_norm_nonneg
    {n : ℕ} {A B V V_inv : Fin n → Fin n → ℝ}
    {mu A_norm radius sep targetScale : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (htargetScale_pos : 0 < targetScale)
    (htargetScale_le :
      targetScale ≤
        |matMulVec n V_inv
            (fun i : Fin n =>
              -residualVec n (inverseIterationShiftedMatrix n A mu) yhat
                (v target) i) target| *
          vecNorm2 (v target))
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (hsep_pos : 0 < sep)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) *
        (Finset.sum (Finset.univ.erase target)
            (fun a =>
              (((frobNorm V_inv *
                    vecNorm2
                      (residualVec n
                        (inverseIterationShiftedMatrix n A mu) yhat
                        (v target))) *
                    vecNorm2 (v a)) /
                  targetScale) *
                (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n =>
                -residualVec n
                  (inverseIterationShiftedMatrix n A mu) yhat
                  (v target) i) target| *
            |(lambda target - mu)⁻¹| * vecNorm2 (v target))) := by
  exact
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_rank_one_backward_error_residual_target_scale_of_A_norm_nonneg
      (n := n) (A := A) (B := B) (V := V) (V_inv := V_inv)
      (mu := mu) (A_norm := A_norm) (radius := radius) (sep := sep)
      (V_inv_norm := frobNorm V_inv) (targetScale := targetScale)
      (lambda := lambda) (v := v) target yhat hyhat hV_cols hV_inv
      (opNorm2Le_of_frobNorm_self V_inv) (frobNorm_nonneg V_inv)
      htargetScale_pos htargetScale_le hEig hshift hB hA hA_norm_nonneg
      hsep_pos htarget hsep

/-- Direct-target Frobenius-inverse residual-norm rank-one residual
near-parallel decomposition.  The source/solver side can now supply the actual
nonzero shifted-residual target coefficient while Lean uses `frobNorm V_inv`
and the actual shifted residual norm in the displayed bound. -/
theorem
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_rank_one_backward_error_residual_target_coeff_frobNorm_inverse
    {n : ℕ} {A B V V_inv : Fin n → Fin n → ℝ}
    {mu radius sep : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hcoeff :
      matMulVec n V_inv
        (fun i : Fin n =>
          -residualVec n (inverseIterationShiftedMatrix n A mu) yhat
            (v target) i) target ≠ 0)
    (hvec : ∃ i : Fin n, v target i ≠ 0)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hsep_pos : 0 < sep)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|) :
    ∃ eta : ℝ, ∃ r : Fin n → ℝ,
      (yhat =
        fun i =>
          (lambda target - mu)⁻¹ * v target i +
            (eta * v target i + r i)) ∧
      vecNorm2 r ≤
        Finset.sum (Finset.univ.erase target)
            (fun a =>
              (((frobNorm V_inv *
                    vecNorm2
                      (residualVec n
                        (inverseIterationShiftedMatrix n A mu) yhat
                        (v target))) *
                    vecNorm2 (v a)) /
                  (|matMulVec n V_inv
                      (fun i : Fin n =>
                        -residualVec n
                          (inverseIterationShiftedMatrix n A mu) yhat
                          (v target) i) target| *
                    vecNorm2 (v target))) *
                (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n =>
                -residualVec n
                  (inverseIterationShiftedMatrix n A mu) yhat
                  (v target) i) target| *
            |(lambda target - mu)⁻¹| * vecNorm2 (v target)) := by
  exact
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_rank_one_backward_error_residual_target_scale_frobNorm_inverse
      (n := n) (A := A) (B := B) (V := V) (V_inv := V_inv)
      (mu := mu) (radius := radius) (sep := sep)
      (targetScale :=
        |matMulVec n V_inv
            (fun i : Fin n =>
              -residualVec n (inverseIterationShiftedMatrix n A mu) yhat
                (v target) i) target| *
          vecNorm2 (v target))
      (lambda := lambda) (v := v) target yhat hyhat hV_cols hV_inv
      (inverseIteration_target_coeff_vecNorm_scale_pos_of_coeff_ne_zero
        target v V_inv
        (fun i : Fin n =>
          -residualVec n (inverseIterationShiftedMatrix n A mu) yhat
            (v target) i) hcoeff hvec)
      (le_rfl) hEig hshift hB hsep_pos htarget hsep

/-- Direct-target Frobenius-inverse residual-norm final inverse-iteration
eigen-residual bound. -/
theorem
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_rank_one_backward_error_residual_target_coeff_frobNorm_inverse_of_A_norm_nonneg
    {n : ℕ} {A B V V_inv : Fin n → Fin n → ℝ}
    {mu A_norm radius sep : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hcoeff :
      matMulVec n V_inv
        (fun i : Fin n =>
          -residualVec n (inverseIterationShiftedMatrix n A mu) yhat
            (v target) i) target ≠ 0)
    (hvec : ∃ i : Fin n, v target i ≠ 0)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (hsep_pos : 0 < sep)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) *
        (Finset.sum (Finset.univ.erase target)
            (fun a =>
              (((frobNorm V_inv *
                    vecNorm2
                      (residualVec n
                        (inverseIterationShiftedMatrix n A mu) yhat
                        (v target))) *
                    vecNorm2 (v a)) /
                  (|matMulVec n V_inv
                      (fun i : Fin n =>
                        -residualVec n
                          (inverseIterationShiftedMatrix n A mu) yhat
                          (v target) i) target| *
                    vecNorm2 (v target))) *
                (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n =>
                -residualVec n
                  (inverseIterationShiftedMatrix n A mu) yhat
                  (v target) i) target| *
            |(lambda target - mu)⁻¹| * vecNorm2 (v target))) := by
  exact
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_rank_one_backward_error_residual_target_scale_frobNorm_inverse_of_A_norm_nonneg
      (n := n) (A := A) (B := B) (V := V) (V_inv := V_inv)
      (mu := mu) (A_norm := A_norm) (radius := radius) (sep := sep)
      (targetScale :=
        |matMulVec n V_inv
            (fun i : Fin n =>
              -residualVec n (inverseIterationShiftedMatrix n A mu) yhat
                (v target) i) target| *
          vecNorm2 (v target))
      (lambda := lambda) (v := v) target yhat hyhat hV_cols hV_inv
      (inverseIteration_target_coeff_vecNorm_scale_pos_of_coeff_ne_zero
        target v V_inv
        (fun i : Fin n =>
          -residualVec n (inverseIterationShiftedMatrix n A mu) yhat
            (v target) i) hcoeff hvec)
      (le_rfl) hEig hshift hB hA hA_norm_nonneg hsep_pos htarget hsep

/-- Eigenpair-nonzero version of the direct-target Frobenius residual-norm
near-parallel decomposition.  This removes the separate target-eigenvector
nonzero hypothesis because `IsRightEigenpair` already contains it. -/
theorem
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_rank_one_backward_error_residual_target_coeff_frobNorm_inverse_of_eigenpair
    {n : ℕ} {A B V V_inv : Fin n → Fin n → ℝ}
    {mu radius sep : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hcoeff :
      matMulVec n V_inv
        (fun i : Fin n =>
          -residualVec n (inverseIterationShiftedMatrix n A mu) yhat
            (v target) i) target ≠ 0)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hsep_pos : 0 < sep)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|) :
    ∃ eta : ℝ, ∃ r : Fin n → ℝ,
      (yhat =
        fun i =>
          (lambda target - mu)⁻¹ * v target i +
            (eta * v target i + r i)) ∧
      vecNorm2 r ≤
        Finset.sum (Finset.univ.erase target)
            (fun a =>
              (((frobNorm V_inv *
                    vecNorm2
                      (residualVec n
                        (inverseIterationShiftedMatrix n A mu) yhat
                        (v target))) *
                    vecNorm2 (v a)) /
                  (|matMulVec n V_inv
                      (fun i : Fin n =>
                        -residualVec n
                          (inverseIterationShiftedMatrix n A mu) yhat
                          (v target) i) target| *
                    vecNorm2 (v target))) *
                (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n =>
                -residualVec n
                  (inverseIterationShiftedMatrix n A mu) yhat
                  (v target) i) target| *
            |(lambda target - mu)⁻¹| * vecNorm2 (v target)) := by
  exact
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_rank_one_backward_error_residual_target_coeff_frobNorm_inverse
      (n := n) (A := A) (B := B) (V := V) (V_inv := V_inv)
      (mu := mu) (radius := radius) (sep := sep)
      (lambda := lambda) (v := v) target yhat hyhat hV_cols hV_inv
      hcoeff (hEig target).1 hEig hshift hB hsep_pos htarget hsep

/-- Eigenpair-nonzero version of the direct-target Frobenius residual-norm final
inverse-iteration eigen-residual bound. -/
theorem
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_rank_one_backward_error_residual_target_coeff_frobNorm_inverse_of_eigenpair_of_A_norm_nonneg
    {n : ℕ} {A B V V_inv : Fin n → Fin n → ℝ}
    {mu A_norm radius sep : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hcoeff :
      matMulVec n V_inv
        (fun i : Fin n =>
          -residualVec n (inverseIterationShiftedMatrix n A mu) yhat
            (v target) i) target ≠ 0)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (hsep_pos : 0 < sep)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) *
        (Finset.sum (Finset.univ.erase target)
            (fun a =>
              (((frobNorm V_inv *
                    vecNorm2
                      (residualVec n
                        (inverseIterationShiftedMatrix n A mu) yhat
                        (v target))) *
                    vecNorm2 (v a)) /
                  (|matMulVec n V_inv
                      (fun i : Fin n =>
                        -residualVec n
                          (inverseIterationShiftedMatrix n A mu) yhat
                          (v target) i) target| *
                    vecNorm2 (v target))) *
                (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n =>
                -residualVec n
                  (inverseIterationShiftedMatrix n A mu) yhat
                  (v target) i) target| *
            |(lambda target - mu)⁻¹| * vecNorm2 (v target))) := by
  exact
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_rank_one_backward_error_residual_target_coeff_frobNorm_inverse_of_A_norm_nonneg
      (n := n) (A := A) (B := B) (V := V) (V_inv := V_inv)
      (mu := mu) (A_norm := A_norm) (radius := radius) (sep := sep)
      (lambda := lambda) (v := v) target yhat hyhat hV_cols hV_inv
      hcoeff (hEig target).1 hEig hshift hB hA hA_norm_nonneg hsep_pos
      htarget hsep

/-- Relative-residual source-facing target-scale form of the rank-one-residual
near-parallel decomposition.  This is the same local handoff as
`inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_rank_one_backward_error_residual_target_scale`,
but it consumes the standard shifted-solver estimate
`||v_target - (A - mu I)yhat||_2 <= rho * ||yhat||_2` directly.  The displayed
tail bound therefore uses the solver-supplied relative residual radius
`rho * ||yhat||_2`, not the exact residual norm or the internal rank-one
perturbation quotient. -/
theorem
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_rank_one_backward_error_residual_target_scale_of_relative_residual
    {n : ℕ} {A B V V_inv : Fin n → Fin n → ℝ}
    {mu radius sep V_inv_norm targetScale rho : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (hres :
      vecNorm2 (residualVec n (inverseIterationShiftedMatrix n A mu) yhat
        (v target)) ≤ rho * vecNorm2 yhat)
    (htargetScale_pos : 0 < targetScale)
    (htargetScale_le :
      targetScale ≤
        |matMulVec n V_inv
            (fun i : Fin n =>
              -residualVec n (inverseIterationShiftedMatrix n A mu) yhat
                (v target) i) target| *
          vecNorm2 (v target))
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hsep_pos : 0 < sep)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|) :
    ∃ eta : ℝ, ∃ r : Fin n → ℝ,
      (yhat =
        fun i =>
          (lambda target - mu)⁻¹ * v target i +
            (eta * v target i + r i)) ∧
      vecNorm2 r ≤
        Finset.sum (Finset.univ.erase target)
            (fun a =>
              (((V_inv_norm * (rho * vecNorm2 yhat)) *
                    vecNorm2 (v a)) /
                  targetScale) *
                (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n =>
                -residualVec n
                  (inverseIterationShiftedMatrix n A mu) yhat
                  (v target) i) target| *
            |(lambda target - mu)⁻¹| * vecNorm2 (v target)) := by
  have htargetScale_le_rank :
      targetScale ≤
        |matMulVec n V_inv
            (fun i : Fin n =>
              -matMulVec n
                (inverseIterationShiftedRankOneBackwardError n A mu
                  (v target) yhat) yhat i) target| *
          vecNorm2 (v target) := by
    simpa [inverseIterationShiftedRankOneBackwardError_targetCoeff_eq_neg_residualCoeff
      n A V_inv mu (v target) yhat target hyhat] using htargetScale_le
  simpa [inverseIterationShiftedRankOneBackwardError_targetCoeff_eq_neg_residualCoeff
      n A V_inv mu (v target) yhat target hyhat] using
    (inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_backward_error_matrix_inverse_opNorm_explicit_beta
      (n := n) (A := A) (B := B)
      (DeltaS := inverseIterationShiftedRankOneBackwardError n A mu (v target) yhat)
      (V := V) (V_inv := V_inv) (mu := mu) (radius := radius)
      (sep := sep) (DeltaS_norm := rho)
      (V_inv_norm := V_inv_norm) (targetScale := targetScale)
      (lambda := lambda) (v := v) target yhat hV_cols hV_inv
      hV_inv_op hV_inv_norm_nonneg
      (inverseIterationShiftedRankOneBackwardError_opNorm2Le_of_residual_norm_le
        n A mu (v target) yhat rho hyhat hres)
      htargetScale_pos htargetScale_le_rank hEig hshift hB hsep_pos htarget
      hsep
      (inverseIterationShiftedRankOneBackwardError_solves n A mu
        (v target) yhat hyhat))

/-- Relative-residual source-facing target-scale form of the final
inverse-iteration eigen-residual bound.  A future Parlett/Golub--Van Loan
theorem or a concrete rounded shifted-solver analysis may provide the visible
relative residual estimate with radius `rho`; this wrapper threads that estimate
through the rank-one residual certificate and keeps the remaining
eigenbasis-conditioning, target-scale, and separation/gap assumptions explicit. -/
theorem
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_rank_one_backward_error_residual_target_scale_of_relative_residual_of_A_norm_nonneg
    {n : ℕ} {A B V V_inv : Fin n → Fin n → ℝ}
    {mu A_norm radius sep V_inv_norm targetScale rho : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hV_inv_op : opNorm2Le V_inv V_inv_norm)
    (hV_inv_norm_nonneg : 0 ≤ V_inv_norm)
    (hres :
      vecNorm2 (residualVec n (inverseIterationShiftedMatrix n A mu) yhat
        (v target)) ≤ rho * vecNorm2 yhat)
    (htargetScale_pos : 0 < targetScale)
    (htargetScale_le :
      targetScale ≤
        |matMulVec n V_inv
            (fun i : Fin n =>
              -residualVec n (inverseIterationShiftedMatrix n A mu) yhat
                (v target) i) target| *
          vecNorm2 (v target))
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (hsep_pos : 0 < sep)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) *
        (Finset.sum (Finset.univ.erase target)
            (fun a =>
              (((V_inv_norm * (rho * vecNorm2 yhat)) *
                    vecNorm2 (v a)) /
                  targetScale) *
                (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n =>
                -residualVec n
                  (inverseIterationShiftedMatrix n A mu) yhat
                  (v target) i) target| *
            |(lambda target - mu)⁻¹| * vecNorm2 (v target))) := by
  have htargetScale_le_rank :
      targetScale ≤
        |matMulVec n V_inv
            (fun i : Fin n =>
              -matMulVec n
                (inverseIterationShiftedRankOneBackwardError n A mu
                  (v target) yhat) yhat i) target| *
          vecNorm2 (v target) := by
    simpa [inverseIterationShiftedRankOneBackwardError_targetCoeff_eq_neg_residualCoeff
      n A V_inv mu (v target) yhat target hyhat] using htargetScale_le
  simpa [inverseIterationShiftedRankOneBackwardError_targetCoeff_eq_neg_residualCoeff
      n A V_inv mu (v target) yhat target hyhat] using
    (inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_backward_error_matrix_inverse_opNorm_explicit_beta_of_A_norm_nonneg
      (n := n) (A := A) (B := B)
      (DeltaS := inverseIterationShiftedRankOneBackwardError n A mu (v target) yhat)
      (V := V) (V_inv := V_inv) (mu := mu) (A_norm := A_norm)
      (radius := radius) (sep := sep) (DeltaS_norm := rho)
      (V_inv_norm := V_inv_norm) (targetScale := targetScale)
      (lambda := lambda) (v := v) target yhat hV_cols hV_inv
      hV_inv_op hV_inv_norm_nonneg
      (inverseIterationShiftedRankOneBackwardError_opNorm2Le_of_residual_norm_le
        n A mu (v target) yhat rho hyhat hres)
      htargetScale_pos htargetScale_le_rank hEig hshift hB hA
      hA_norm_nonneg hsep_pos htarget hsep
      (inverseIterationShiftedRankOneBackwardError_solves n A mu
        (v target) yhat hyhat))

/-- Frobenius-inverse specialization of the relative-residual target-scale
rank-one residual near-parallel decomposition.  This wrapper removes the
separate eigenbasis-inverse operator-norm certificate by using the Frobenius
norm of `V_inv`, via `opNorm2Le_of_frobNorm_self`. -/
theorem
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_rank_one_backward_error_residual_target_scale_of_relative_residual_frobNorm_inverse
    {n : ℕ} {A B V V_inv : Fin n → Fin n → ℝ}
    {mu radius sep targetScale rho : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hres :
      vecNorm2 (residualVec n (inverseIterationShiftedMatrix n A mu) yhat
        (v target)) ≤ rho * vecNorm2 yhat)
    (htargetScale_pos : 0 < targetScale)
    (htargetScale_le :
      targetScale ≤
        |matMulVec n V_inv
            (fun i : Fin n =>
              -residualVec n (inverseIterationShiftedMatrix n A mu) yhat
                (v target) i) target| *
          vecNorm2 (v target))
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hsep_pos : 0 < sep)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|) :
    ∃ eta : ℝ, ∃ r : Fin n → ℝ,
      (yhat =
        fun i =>
          (lambda target - mu)⁻¹ * v target i +
            (eta * v target i + r i)) ∧
      vecNorm2 r ≤
        Finset.sum (Finset.univ.erase target)
            (fun a =>
              (((frobNorm V_inv * (rho * vecNorm2 yhat)) *
                    vecNorm2 (v a)) /
                  targetScale) *
                (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n =>
                -residualVec n
                  (inverseIterationShiftedMatrix n A mu) yhat
                  (v target) i) target| *
            |(lambda target - mu)⁻¹| * vecNorm2 (v target)) := by
  exact
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_rank_one_backward_error_residual_target_scale_of_relative_residual
      (n := n) (A := A) (B := B) (V := V) (V_inv := V_inv)
      (mu := mu) (radius := radius) (sep := sep)
      (V_inv_norm := frobNorm V_inv) (targetScale := targetScale)
      (rho := rho) (lambda := lambda) (v := v) target yhat hyhat
      hV_cols hV_inv (opNorm2Le_of_frobNorm_self V_inv)
      (frobNorm_nonneg V_inv) hres htargetScale_pos htargetScale_le
      hEig hshift hB hsep_pos htarget hsep

/-- Frobenius-inverse specialization of the relative-residual target-scale
final inverse-iteration eigen-residual bound.  The bound displays
`frobNorm V_inv` as the eigenbasis-inverse conditioning quantity instead of
requiring a separate `opNorm2Le V_inv V_inv_norm` certificate. -/
theorem
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_rank_one_backward_error_residual_target_scale_of_relative_residual_frobNorm_inverse_of_A_norm_nonneg
    {n : ℕ} {A B V V_inv : Fin n → Fin n → ℝ}
    {mu A_norm radius sep targetScale rho : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hres :
      vecNorm2 (residualVec n (inverseIterationShiftedMatrix n A mu) yhat
        (v target)) ≤ rho * vecNorm2 yhat)
    (htargetScale_pos : 0 < targetScale)
    (htargetScale_le :
      targetScale ≤
        |matMulVec n V_inv
            (fun i : Fin n =>
              -residualVec n (inverseIterationShiftedMatrix n A mu) yhat
                (v target) i) target| *
          vecNorm2 (v target))
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (hsep_pos : 0 < sep)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) *
        (Finset.sum (Finset.univ.erase target)
            (fun a =>
              (((frobNorm V_inv * (rho * vecNorm2 yhat)) *
                    vecNorm2 (v a)) /
                  targetScale) *
                (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n =>
                -residualVec n
                  (inverseIterationShiftedMatrix n A mu) yhat
                  (v target) i) target| *
            |(lambda target - mu)⁻¹| * vecNorm2 (v target))) := by
  exact
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_rank_one_backward_error_residual_target_scale_of_relative_residual_of_A_norm_nonneg
      (n := n) (A := A) (B := B) (V := V) (V_inv := V_inv)
      (mu := mu) (A_norm := A_norm) (radius := radius) (sep := sep)
      (V_inv_norm := frobNorm V_inv) (targetScale := targetScale)
      (rho := rho) (lambda := lambda) (v := v) target yhat hyhat
      hV_cols hV_inv (opNorm2Le_of_frobNorm_self V_inv)
      (frobNorm_nonneg V_inv) hres htargetScale_pos htargetScale_le
      hEig hshift hB hA hA_norm_nonneg hsep_pos htarget hsep

/-- Direct-target version of the Frobenius-inverse relative-residual
rank-one residual near-parallel decomposition.  This removes both local
certificate artifacts from the common source-facing route: the eigenbasis
inverse norm is the Frobenius norm of `V_inv`, and the positive target scale is
the actual shifted-residual target coefficient times the target eigenvector
norm, under explicit nonzero evidence. -/
theorem
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_rank_one_backward_error_residual_target_coeff_of_relative_residual_frobNorm_inverse
    {n : ℕ} {A B V V_inv : Fin n → Fin n → ℝ}
    {mu radius sep rho : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hres :
      vecNorm2 (residualVec n (inverseIterationShiftedMatrix n A mu) yhat
        (v target)) ≤ rho * vecNorm2 yhat)
    (hcoeff :
      matMulVec n V_inv
        (fun i : Fin n =>
          -residualVec n (inverseIterationShiftedMatrix n A mu) yhat
            (v target) i) target ≠ 0)
    (hvec : ∃ i : Fin n, v target i ≠ 0)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hsep_pos : 0 < sep)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|) :
    ∃ eta : ℝ, ∃ r : Fin n → ℝ,
      (yhat =
        fun i =>
          (lambda target - mu)⁻¹ * v target i +
            (eta * v target i + r i)) ∧
      vecNorm2 r ≤
        Finset.sum (Finset.univ.erase target)
            (fun a =>
              (((frobNorm V_inv * (rho * vecNorm2 yhat)) *
                    vecNorm2 (v a)) /
                  (|matMulVec n V_inv
                      (fun i : Fin n =>
                        -residualVec n
                          (inverseIterationShiftedMatrix n A mu) yhat
                          (v target) i) target| *
                    vecNorm2 (v target))) *
                (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n =>
                -residualVec n
                  (inverseIterationShiftedMatrix n A mu) yhat
                  (v target) i) target| *
            |(lambda target - mu)⁻¹| * vecNorm2 (v target)) := by
  exact
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_rank_one_backward_error_residual_target_scale_of_relative_residual_frobNorm_inverse
      (n := n) (A := A) (B := B) (V := V) (V_inv := V_inv)
      (mu := mu) (radius := radius) (sep := sep)
      (targetScale :=
        |matMulVec n V_inv
            (fun i : Fin n =>
              -residualVec n (inverseIterationShiftedMatrix n A mu) yhat
                (v target) i) target| *
          vecNorm2 (v target))
      (rho := rho) (lambda := lambda) (v := v) target yhat hyhat
      hV_cols hV_inv hres
      (inverseIteration_target_coeff_vecNorm_scale_pos_of_coeff_ne_zero
        target v V_inv
        (fun i : Fin n =>
          -residualVec n (inverseIterationShiftedMatrix n A mu) yhat
            (v target) i) hcoeff hvec)
      (le_rfl) hEig hshift hB hsep_pos htarget hsep

/-- Direct-target version of the Frobenius-inverse relative-residual final
inverse-iteration eigen-residual bound.  A future source theorem or rounded
shifted-solver certificate may state the ordinary residual estimate and the
actual nonzero target residual coefficient; this wrapper constructs the
denominator and uses `frobNorm V_inv` for the eigenbasis-inverse budget. -/
theorem
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_rank_one_backward_error_residual_target_coeff_of_relative_residual_frobNorm_inverse_of_A_norm_nonneg
    {n : ℕ} {A B V V_inv : Fin n → Fin n → ℝ}
    {mu A_norm radius sep rho : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hres :
      vecNorm2 (residualVec n (inverseIterationShiftedMatrix n A mu) yhat
        (v target)) ≤ rho * vecNorm2 yhat)
    (hcoeff :
      matMulVec n V_inv
        (fun i : Fin n =>
          -residualVec n (inverseIterationShiftedMatrix n A mu) yhat
            (v target) i) target ≠ 0)
    (hvec : ∃ i : Fin n, v target i ≠ 0)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (hsep_pos : 0 < sep)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) *
        (Finset.sum (Finset.univ.erase target)
            (fun a =>
              (((frobNorm V_inv * (rho * vecNorm2 yhat)) *
                    vecNorm2 (v a)) /
                  (|matMulVec n V_inv
                      (fun i : Fin n =>
                        -residualVec n
                          (inverseIterationShiftedMatrix n A mu) yhat
                          (v target) i) target| *
                    vecNorm2 (v target))) *
                (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n =>
                -residualVec n
                  (inverseIterationShiftedMatrix n A mu) yhat
                  (v target) i) target| *
            |(lambda target - mu)⁻¹| * vecNorm2 (v target))) := by
  exact
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_rank_one_backward_error_residual_target_scale_of_relative_residual_frobNorm_inverse_of_A_norm_nonneg
      (n := n) (A := A) (B := B) (V := V) (V_inv := V_inv)
      (mu := mu) (A_norm := A_norm) (radius := radius) (sep := sep)
      (targetScale :=
        |matMulVec n V_inv
            (fun i : Fin n =>
              -residualVec n (inverseIterationShiftedMatrix n A mu) yhat
                (v target) i) target| *
          vecNorm2 (v target))
      (rho := rho) (lambda := lambda) (v := v) target yhat hyhat
      hV_cols hV_inv hres
      (inverseIteration_target_coeff_vecNorm_scale_pos_of_coeff_ne_zero
        target v V_inv
        (fun i : Fin n =>
          -residualVec n (inverseIterationShiftedMatrix n A mu) yhat
            (v target) i) hcoeff hvec)
      (le_rfl) hEig hshift hB hA hA_norm_nonneg hsep_pos htarget hsep

/-- Eigenpair-nonzero version of the direct-target Frobenius relative-residual
near-parallel decomposition.  The only direct target-direction evidence still
required here is the nonzero shifted-residual target coefficient; the nonzero
target eigenvector comes from `hEig target`. -/
theorem
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_rank_one_backward_error_residual_target_coeff_of_relative_residual_frobNorm_inverse_of_eigenpair
    {n : ℕ} {A B V V_inv : Fin n → Fin n → ℝ}
    {mu radius sep rho : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hres :
      vecNorm2 (residualVec n (inverseIterationShiftedMatrix n A mu) yhat
        (v target)) ≤ rho * vecNorm2 yhat)
    (hcoeff :
      matMulVec n V_inv
        (fun i : Fin n =>
          -residualVec n (inverseIterationShiftedMatrix n A mu) yhat
            (v target) i) target ≠ 0)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hsep_pos : 0 < sep)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|) :
    ∃ eta : ℝ, ∃ r : Fin n → ℝ,
      (yhat =
        fun i =>
          (lambda target - mu)⁻¹ * v target i +
            (eta * v target i + r i)) ∧
      vecNorm2 r ≤
        Finset.sum (Finset.univ.erase target)
            (fun a =>
              (((frobNorm V_inv * (rho * vecNorm2 yhat)) *
                    vecNorm2 (v a)) /
                  (|matMulVec n V_inv
                      (fun i : Fin n =>
                        -residualVec n
                          (inverseIterationShiftedMatrix n A mu) yhat
                          (v target) i) target| *
                    vecNorm2 (v target))) *
                (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n =>
                -residualVec n
                  (inverseIterationShiftedMatrix n A mu) yhat
                  (v target) i) target| *
            |(lambda target - mu)⁻¹| * vecNorm2 (v target)) := by
  exact
    inverseIteration_perturbed_shiftedSolve_near_parallel_decomposition_of_rank_one_backward_error_residual_target_coeff_of_relative_residual_frobNorm_inverse
      (n := n) (A := A) (B := B) (V := V) (V_inv := V_inv)
      (mu := mu) (radius := radius) (sep := sep) (rho := rho)
      (lambda := lambda) (v := v) target yhat hyhat hV_cols hV_inv
      hres hcoeff (hEig target).1 hEig hshift hB hsep_pos htarget hsep

/-- Eigenpair-nonzero version of the direct-target Frobenius relative-residual
final inverse-iteration eigen-residual bound. -/
theorem
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_rank_one_backward_error_residual_target_coeff_of_relative_residual_frobNorm_inverse_of_eigenpair_of_A_norm_nonneg
    {n : ℕ} {A B V V_inv : Fin n → Fin n → ℝ}
    {mu A_norm radius sep rho : ℝ}
    {lambda : Fin n → ℝ} {v : Fin n → Fin n → ℝ}
    (target : Fin n) (yhat : Fin n → ℝ)
    (hyhat : vecNorm2 yhat ≠ 0)
    (hV_cols : ∀ i a, V i a = v a i)
    (hV_inv : IsRightInverse n V V_inv)
    (hres :
      vecNorm2 (residualVec n (inverseIterationShiftedMatrix n A mu) yhat
        (v target)) ≤ rho * vecNorm2 yhat)
    (hcoeff :
      matMulVec n V_inv
        (fun i : Fin n =>
          -residualVec n (inverseIterationShiftedMatrix n A mu) yhat
            (v target) i) target ≠ 0)
    (hEig : ∀ a : Fin n, IsRightEigenpair n A (lambda a) (v a))
    (hshift : ∀ a : Fin n, lambda a - mu ≠ 0)
    (hB : IsLeftInverse n (inverseIterationShiftedMatrix n A mu) B)
    (hA : opNorm2Le A A_norm)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (hsep_pos : 0 < sep)
    (htarget : |lambda target - mu| ≤ radius)
    (hsep :
      ∀ a : Fin n, a ∈ (Finset.univ.erase target) →
        sep ≤ |lambda a - mu|) :
    vecNorm2 (eigenResidualVec n A (lambda target) yhat) ≤
      (A_norm + |lambda target|) *
        (Finset.sum (Finset.univ.erase target)
            (fun a =>
              (((frobNorm V_inv * (rho * vecNorm2 yhat)) *
                    vecNorm2 (v a)) /
                  (|matMulVec n V_inv
                      (fun i : Fin n =>
                        -residualVec n
                          (inverseIterationShiftedMatrix n A mu) yhat
                          (v target) i) target| *
                    vecNorm2 (v target))) *
                (radius / sep)) *
          (|matMulVec n V_inv
              (fun i : Fin n =>
                -residualVec n
                  (inverseIterationShiftedMatrix n A mu) yhat
                  (v target) i) target| *
            |(lambda target - mu)⁻¹| * vecNorm2 (v target))) := by
  exact
    inverseIteration_perturbed_shiftedSolve_eigenResidual_norm_le_of_rank_one_backward_error_residual_target_coeff_of_relative_residual_frobNorm_inverse_of_A_norm_nonneg
      (n := n) (A := A) (B := B) (V := V) (V_inv := V_inv)
      (mu := mu) (A_norm := A_norm) (radius := radius) (sep := sep)
      (rho := rho) (lambda := lambda) (v := v) target yhat hyhat
      hV_cols hV_inv hres hcoeff (hEig target).1 hEig hshift hB hA
      hA_norm_nonneg hsep_pos htarget hsep

/-- The §1.15 power-method example matrix. -/
noncomputable def beneficialPowerMatrix : Fin 3 → Fin 3 → ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => 2 / 5
  | ⟨0, _⟩, ⟨1, _⟩ => -3 / 5
  | ⟨0, _⟩, ⟨2, _⟩ => 1 / 5
  | ⟨1, _⟩, ⟨0, _⟩ => -3 / 10
  | ⟨1, _⟩, ⟨1, _⟩ => 7 / 10
  | ⟨1, _⟩, ⟨2, _⟩ => -2 / 5
  | ⟨2, _⟩, ⟨0, _⟩ => -1 / 10
  | ⟨2, _⟩, ⟨1, _⟩ => -2 / 5
  | ⟨2, _⟩, ⟨2, _⟩ => 1 / 2

/-- The displayed §1.15 matrix with each entry rounded to the repository's
finite IEEE-double round-to-even model. -/
noncomputable def beneficialPowerMatrixIeeeDoubleRounded :
    Fin 3 → Fin 3 → ℝ :=
  fun i j =>
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven
      (beneficialPowerMatrix i j)

/-- The entrywise IEEE-double stored §1.15 matrix, written as exact rationals.
This is a certificate-friendly expansion of
`beneficialPowerMatrixIeeeDoubleRounded`. -/
noncomputable def beneficialPowerMatrixIeeeDoubleRoundedExplicit :
    Fin 3 → Fin 3 → ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => (7205759403792794 : ℝ) * (2 : ℝ) ^ (-54 : ℤ)
  | ⟨0, _⟩, ⟨1, _⟩ => -((5404319552844595 : ℝ) * (2 : ℝ) ^ (-53 : ℤ))
  | ⟨0, _⟩, ⟨2, _⟩ => (7205759403792794 : ℝ) * (2 : ℝ) ^ (-55 : ℤ)
  | ⟨1, _⟩, ⟨0, _⟩ => -((5404319552844595 : ℝ) * (2 : ℝ) ^ (-54 : ℤ))
  | ⟨1, _⟩, ⟨1, _⟩ => (6305039478318694 : ℝ) * (2 : ℝ) ^ (-53 : ℤ)
  | ⟨1, _⟩, ⟨2, _⟩ => -((7205759403792794 : ℝ) * (2 : ℝ) ^ (-54 : ℤ))
  | ⟨2, _⟩, ⟨0, _⟩ => -((7205759403792794 : ℝ) * (2 : ℝ) ^ (-56 : ℤ))
  | ⟨2, _⟩, ⟨1, _⟩ => -((7205759403792794 : ℝ) * (2 : ℝ) ^ (-54 : ℤ))
  | ⟨2, _⟩, ⟨2, _⟩ => 1 / 2

/-- The exact rational expansion agrees with entrywise IEEE-double storage. -/
theorem beneficialPowerMatrixIeeeDoubleRounded_eq_explicit :
    beneficialPowerMatrixIeeeDoubleRounded =
      beneficialPowerMatrixIeeeDoubleRoundedExplicit := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [beneficialPowerMatrixIeeeDoubleRounded, beneficialPowerMatrix,
      beneficialPowerMatrixIeeeDoubleRoundedExplicit,
      ieeeDoubleFormat_two_fifths_rounds_to,
      ieeeDoubleFormat_neg_three_fifths_rounds_to,
      ieeeDoubleFormat_neg_three_tenths_rounds_to,
      ieeeDoubleFormat_seven_tenths_rounds_to,
      ieeeDoubleFormat_neg_two_fifths_rounds_to,
      ieeeDoubleFormat_neg_one_tenth_rounds_to]
  · rw [show ((5 : ℝ)⁻¹) = (1 / 5 : ℝ) by norm_num]
    rw [ieeeDoubleFormat_one_fifth_rounds_to]
    norm_num [zpow_neg]
  · rw [show ((2 : ℝ)⁻¹) = (1 / 2 : ℝ) by norm_num]
    rw [ieeeDoubleFormat_one_half_rounds_to]

/-- Uniform entrywise perturbation radius from the displayed §1.15 matrix to
its entrywise IEEE-double stored version.  This is a concrete, non-empirical
certificate about the stored matrix; it is not a MATLAB/BLAS iteration trace. -/
theorem beneficialPowerMatrixIeeeDoubleRounded_entrywise_abs_error_le_two_pow_neg53 :
    ∀ i j : Fin 3,
      |beneficialPowerMatrixIeeeDoubleRounded i j - beneficialPowerMatrix i j|
        ≤ (1 : ℝ) / (2 : ℝ) ^ 53 := by
  intro i j
  fin_cases i <;> fin_cases j
  · simp [beneficialPowerMatrixIeeeDoubleRounded, beneficialPowerMatrix,
      ieeeDoubleFormat_two_fifths_rounds_to]
    norm_num [_root_.zpow_neg]
  · simp [beneficialPowerMatrixIeeeDoubleRounded, beneficialPowerMatrix,
      ieeeDoubleFormat_neg_three_fifths_rounds_to]
    norm_num [_root_.zpow_neg]
  · simp [beneficialPowerMatrixIeeeDoubleRounded, beneficialPowerMatrix]
    rw [show ((5 : ℝ)⁻¹) = (1 / 5 : ℝ) by norm_num]
    rw [ieeeDoubleFormat_one_fifth_rounds_to]
    norm_num [_root_.zpow_neg]
  · simp [beneficialPowerMatrixIeeeDoubleRounded, beneficialPowerMatrix,
      ieeeDoubleFormat_neg_three_tenths_rounds_to]
    norm_num [_root_.zpow_neg]
  · simp [beneficialPowerMatrixIeeeDoubleRounded, beneficialPowerMatrix,
      ieeeDoubleFormat_seven_tenths_rounds_to]
    norm_num [_root_.zpow_neg]
  · simp [beneficialPowerMatrixIeeeDoubleRounded, beneficialPowerMatrix,
      ieeeDoubleFormat_neg_two_fifths_rounds_to]
    norm_num [_root_.zpow_neg]
  · simp [beneficialPowerMatrixIeeeDoubleRounded, beneficialPowerMatrix,
      ieeeDoubleFormat_neg_one_tenth_rounds_to]
    norm_num [_root_.zpow_neg]
  · simp [beneficialPowerMatrixIeeeDoubleRounded, beneficialPowerMatrix,
      ieeeDoubleFormat_neg_two_fifths_rounds_to]
    norm_num [_root_.zpow_neg]
  · simp [beneficialPowerMatrixIeeeDoubleRounded, beneficialPowerMatrix]
    rw [show ((2 : ℝ)⁻¹) = (1 / 2 : ℝ) by norm_num]
    rw [ieeeDoubleFormat_one_half_rounds_to]
    norm_num [_root_.zpow_neg]

/-- The entrywise IEEE-double stored §1.15 matrix is nonsingular.  This is a
concrete spectral dependency toward the remaining dominant-component
certificate: storage has moved the displayed zero eigenvalue away from zero. -/
theorem beneficialPowerMatrixIeeeDoubleRounded_det_ne_zero :
    Matrix.det
      (beneficialPowerMatrixIeeeDoubleRounded : Matrix (Fin 3) (Fin 3) ℝ) ≠
        0 := by
  rw [beneficialPowerMatrixIeeeDoubleRounded_eq_explicit]
  rw [Matrix.det_fin_three]
  simp [beneficialPowerMatrixIeeeDoubleRoundedExplicit]
  norm_num [zpow_neg]

/-- The characteristic matrix `lambda I - A_stored` for the entrywise
IEEE-double stored §1.15 power-method matrix. -/
noncomputable def beneficialPowerMatrixIeeeDoubleRoundedCharMatrix
    (lambda : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j =>
    (if i = j then lambda else 0) - beneficialPowerMatrixIeeeDoubleRounded i j

/-- Zero is not an eigenvalue of the entrywise IEEE-double stored §1.15 matrix,
as witnessed by the nonzero characteristic determinant at `lambda = 0`. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharDet_zero_ne :
    Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix 0) ≠ 0 := by
  rw [Matrix.det_fin_three]
  simp [beneficialPowerMatrixIeeeDoubleRoundedCharMatrix,
    beneficialPowerMatrixIeeeDoubleRounded_eq_explicit,
    beneficialPowerMatrixIeeeDoubleRoundedExplicit]
  norm_num [zpow_neg]

/-- Exact characteristic determinant of the entrywise IEEE-double stored §1.15
matrix.  This cubic is the concrete spectral anchor for the remaining
dominant-eigencomponent certificate. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharDet_eq (lambda : ℝ) :
    Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda) =
      lambda ^ 3 -
        (14411518807585587 / 9007199254740992 : ℝ) * lambda ^ 2 +
        (331008924731595251230755975677869 /
          649037107316853453566312041152512 : ℝ) * lambda +
        (12980742146337072764277935266857 /
          2923003274661805836407369665432566039311865085952 : ℝ) := by
  rw [Matrix.det_fin_three]
  simp [beneficialPowerMatrixIeeeDoubleRoundedCharMatrix,
    beneficialPowerMatrixIeeeDoubleRounded_eq_explicit,
    beneficialPowerMatrixIeeeDoubleRoundedExplicit]
  ring_nf

/-- The stored-matrix characteristic determinant changes sign just to the
left of zero.  This is the first concrete bracketing datum for the displaced
small eigenvalue. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharDet_neg_one_e14_lt_zero :
    Matrix.det
        (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix
          (-(1 : ℝ) / (10 : ℝ) ^ 14)) < 0 := by
  rw [beneficialPowerMatrixIeeeDoubleRoundedCharDet_eq]
  norm_num

/-- A tighter lower-endpoint sign for the stored eigenvalue displaced from the
displayed zero eigenvalue.  This gives a small enough interval to prove the
stored-start dominant coefficient is nonzero by a determinant sign argument. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharDet_neg_one_e17_lt_zero :
    Matrix.det
        (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix
          (-(1 : ℝ) / (10 : ℝ) ^ 17)) < 0 := by
  rw [beneficialPowerMatrixIeeeDoubleRoundedCharDet_eq]
  norm_num

/-- The stored-matrix characteristic determinant is positive at zero. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharDet_zero_pos :
    0 < Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix 0) := by
  rw [beneficialPowerMatrixIeeeDoubleRoundedCharDet_eq]
  positivity

/-- Lower endpoint sign for the stored eigenvalue near the displayed smaller
nonzero eigenvalue. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharDet_439_1000_pos :
    0 <
      Matrix.det
        (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix
          ((439 : ℝ) / 1000)) := by
  rw [beneficialPowerMatrixIeeeDoubleRoundedCharDet_eq]
  norm_num

/-- Upper endpoint sign for the stored eigenvalue near the displayed smaller
nonzero eigenvalue. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharDet_11_25_lt_zero :
    Matrix.det
        (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix
          ((11 : ℝ) / 25)) < 0 := by
  rw [beneficialPowerMatrixIeeeDoubleRoundedCharDet_eq]
  norm_num

/-- Lower endpoint sign for the stored dominant eigenvalue interval. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharDet_29_25_lt_zero :
    Matrix.det
        (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix
          ((29 : ℝ) / 25)) < 0 := by
  rw [beneficialPowerMatrixIeeeDoubleRoundedCharDet_eq]
  norm_num

/-- Upper endpoint sign for the stored dominant eigenvalue interval. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharDet_117_100_pos :
    0 <
      Matrix.det
        (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix
          ((117 : ℝ) / 100)) := by
  rw [beneficialPowerMatrixIeeeDoubleRoundedCharDet_eq]
  norm_num

/-- The stored-matrix characteristic determinant is a continuous scalar
function of `lambda`. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharDet_continuous :
    Continuous fun lambda : ℝ =>
      Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda) := by
  apply Continuous.congr
    (by
      simpa only using
        (by
          continuity :
            Continuous fun lambda : ℝ =>
              lambda ^ 3 -
                (14411518807585587 / 9007199254740992 : ℝ) * lambda ^ 2 +
                (331008924731595251230755975677869 /
                  649037107316853453566312041152512 : ℝ) * lambda +
                (12980742146337072764277935266857 /
                  2923003274661805836407369665432566039311865085952 : ℝ)))
  intro lambda
  exact (beneficialPowerMatrixIeeeDoubleRoundedCharDet_eq lambda).symm

/-- The stored characteristic determinant has a root in the small interval
where the displayed zero eigenvalue is displaced. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_root_neg_one_e14_zero :
    ∃ lambda ∈ Set.Icc (-(1 : ℝ) / (10 : ℝ) ^ 14) 0,
      Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda) = 0 := by
  let f : ℝ → ℝ :=
    fun lambda => Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda)
  have hcont : ContinuousOn f (Set.Icc (-(1 : ℝ) / (10 : ℝ) ^ 14) 0) :=
    beneficialPowerMatrixIeeeDoubleRoundedCharDet_continuous.continuousOn
  have hab : (-(1 : ℝ) / (10 : ℝ) ^ 14) ≤ 0 := by norm_num
  have hmem :
      (0 : ℝ) ∈ Set.Icc (f (-(1 : ℝ) / (10 : ℝ) ^ 14)) (f 0) := by
    constructor
    · exact le_of_lt beneficialPowerMatrixIeeeDoubleRoundedCharDet_neg_one_e14_lt_zero
    · exact le_of_lt beneficialPowerMatrixIeeeDoubleRoundedCharDet_zero_pos
  rcases intermediate_value_Icc hab hcont hmem with ⟨lambda, hlambda, hflambda⟩
  exact ⟨lambda, hlambda, hflambda⟩

/-- The displaced small stored root also lies in the tighter interval
`[-10^-17, 0]`. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_root_neg_one_e17_zero :
    ∃ lambda ∈ Set.Icc (-(1 : ℝ) / (10 : ℝ) ^ 17) 0,
      Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda) = 0 := by
  let f : ℝ → ℝ :=
    fun lambda => Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda)
  have hcont : ContinuousOn f (Set.Icc (-(1 : ℝ) / (10 : ℝ) ^ 17) 0) :=
    beneficialPowerMatrixIeeeDoubleRoundedCharDet_continuous.continuousOn
  have hab : (-(1 : ℝ) / (10 : ℝ) ^ 17) ≤ 0 := by norm_num
  have hmem :
      (0 : ℝ) ∈ Set.Icc (f (-(1 : ℝ) / (10 : ℝ) ^ 17)) (f 0) := by
    constructor
    · exact le_of_lt beneficialPowerMatrixIeeeDoubleRoundedCharDet_neg_one_e17_lt_zero
    · exact le_of_lt beneficialPowerMatrixIeeeDoubleRoundedCharDet_zero_pos
  rcases intermediate_value_Icc hab hcont hmem with ⟨lambda, hlambda, hflambda⟩
  exact ⟨lambda, hlambda, hflambda⟩

/-- The stored characteristic determinant has a root in the interval around the
smaller nonzero displayed eigenvalue. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_root_439_1000_11_25 :
    ∃ lambda ∈ Set.Icc ((439 : ℝ) / 1000) ((11 : ℝ) / 25),
      Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda) = 0 := by
  let f : ℝ → ℝ :=
    fun lambda => Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda)
  have hcont :
      ContinuousOn f (Set.Icc ((439 : ℝ) / 1000) ((11 : ℝ) / 25)) :=
    beneficialPowerMatrixIeeeDoubleRoundedCharDet_continuous.continuousOn
  have hab : ((439 : ℝ) / 1000) ≤ ((11 : ℝ) / 25) := by norm_num
  have hmem :
      (0 : ℝ) ∈ Set.Icc (f ((11 : ℝ) / 25)) (f ((439 : ℝ) / 1000)) := by
    constructor
    · exact le_of_lt beneficialPowerMatrixIeeeDoubleRoundedCharDet_11_25_lt_zero
    · exact le_of_lt beneficialPowerMatrixIeeeDoubleRoundedCharDet_439_1000_pos
  rcases intermediate_value_Icc' hab hcont hmem with ⟨lambda, hlambda, hflambda⟩
  exact ⟨lambda, hlambda, hflambda⟩

/-- The stored characteristic determinant has a root in the interval around the
dominant displayed eigenvalue. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_root_29_25_117_100 :
    ∃ lambda ∈ Set.Icc ((29 : ℝ) / 25) ((117 : ℝ) / 100),
      Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda) = 0 := by
  let f : ℝ → ℝ :=
    fun lambda => Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda)
  have hcont :
      ContinuousOn f (Set.Icc ((29 : ℝ) / 25) ((117 : ℝ) / 100)) :=
    beneficialPowerMatrixIeeeDoubleRoundedCharDet_continuous.continuousOn
  have hab : ((29 : ℝ) / 25) ≤ ((117 : ℝ) / 100) := by norm_num
  have hmem :
      (0 : ℝ) ∈ Set.Icc (f ((29 : ℝ) / 25)) (f ((117 : ℝ) / 100)) := by
    constructor
    · exact le_of_lt beneficialPowerMatrixIeeeDoubleRoundedCharDet_29_25_lt_zero
    · exact le_of_lt beneficialPowerMatrixIeeeDoubleRoundedCharDet_117_100_pos
  rcases intermediate_value_Icc hab hcont hmem with ⟨lambda, hlambda, hflambda⟩
  exact ⟨lambda, hlambda, hflambda⟩

/-- The exact scalar characteristic polynomial of the entrywise IEEE-double
stored §1.15 matrix. -/
noncomputable def beneficialPowerMatrixIeeeDoubleRoundedCharPoly
    (lambda : ℝ) : ℝ :=
  lambda ^ 3 -
    (14411518807585587 / 9007199254740992 : ℝ) * lambda ^ 2 +
    (331008924731595251230755975677869 /
      649037107316853453566312041152512 : ℝ) * lambda +
    (12980742146337072764277935266857 /
      2923003274661805836407369665432566039311865085952 : ℝ)

/-- The stored characteristic determinant agrees with the scalar cubic wrapper. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharDet_eq_poly
    (lambda : ℝ) :
    Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda) =
      beneficialPowerMatrixIeeeDoubleRoundedCharPoly lambda := by
  rw [beneficialPowerMatrixIeeeDoubleRoundedCharDet_eq]
  rfl

/-- Derivative of the exact scalar characteristic polynomial of the stored
§1.15 matrix. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharPoly_hasDerivAt
    (lambda : ℝ) :
    HasDerivAt beneficialPowerMatrixIeeeDoubleRoundedCharPoly
      (3 * lambda ^ 2 -
        2 * (14411518807585587 / 9007199254740992 : ℝ) * lambda +
        (331008924731595251230755975677869 /
          649037107316853453566312041152512 : ℝ))
      lambda := by
  let a : ℝ := 14411518807585587 / 9007199254740992
  let b : ℝ :=
    331008924731595251230755975677869 /
      649037107316853453566312041152512
  let c : ℝ :=
    12980742146337072764277935266857 /
      2923003274661805836407369665432566039311865085952
  change HasDerivAt (fun t : ℝ => t ^ 3 - a * t ^ 2 + b * t + c)
    (3 * lambda ^ 2 - 2 * a * lambda + b) lambda
  have h3 :
      HasDerivAt (fun t : ℝ => t ^ 3) (3 * lambda ^ 2) lambda := by
    simpa using (hasDerivAt_id lambda).fun_pow 3
  have h2 :
      HasDerivAt (fun t : ℝ => a * t ^ 2) (2 * a * lambda) lambda := by
    have hpow :
        HasDerivAt (fun t : ℝ => t ^ 2) (2 * lambda) lambda := by
      simpa using (hasDerivAt_id lambda).fun_pow 2
    simpa [mul_assoc, mul_comm, mul_left_comm] using hpow.const_mul a
  have hlin : HasDerivAt (fun t : ℝ => b * t) b lambda := by
    simpa using (hasDerivAt_id lambda).const_mul b
  have hconst : HasDerivAt (fun _t : ℝ => c) 0 lambda :=
    hasDerivAt_const lambda c
  convert (h3.sub h2).add (hlin.add hconst) using 1
  · funext t
    simp only [Pi.add_apply, Pi.sub_apply]
    ring_nf
  · ring_nf

/-- The stored characteristic cubic is strictly increasing across the small
root interval. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharPoly_strictMonoOn_neg_one_e14_zero :
    StrictMonoOn beneficialPowerMatrixIeeeDoubleRoundedCharPoly
      (Set.Icc (-(1 : ℝ) / (10 : ℝ) ^ 14) 0) := by
  let d : ℝ → ℝ := fun x =>
    3 * x ^ 2 -
      2 * (14411518807585587 / 9007199254740992 : ℝ) * x +
      (331008924731595251230755975677869 /
        649037107316853453566312041152512 : ℝ)
  refine strictMonoOn_of_hasDerivWithinAt_pos
    (D := Set.Icc (-(1 : ℝ) / (10 : ℝ) ^ 14) 0)
    (f := beneficialPowerMatrixIeeeDoubleRoundedCharPoly) (f' := d)
    (convex_Icc _ _) ?hcont ?hderiv ?hpos
  · exact (continuous_iff_continuousAt.mpr
        (fun x =>
          (beneficialPowerMatrixIeeeDoubleRoundedCharPoly_hasDerivAt x).continuousAt)).continuousOn
  · intro x _hx
    exact (beneficialPowerMatrixIeeeDoubleRoundedCharPoly_hasDerivAt x).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hxlo : -(1 : ℝ) / (10 : ℝ) ^ 14 < x := hx.1
    have hxhi : x < 0 := hx.2
    dsimp [d]
    nlinarith [sq_nonneg x]

/-- The stored characteristic cubic is strictly decreasing across the interval
around the smaller nonzero root. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharPoly_strictAntiOn_439_1000_11_25 :
    StrictAntiOn beneficialPowerMatrixIeeeDoubleRoundedCharPoly
      (Set.Icc ((439 : ℝ) / 1000) ((11 : ℝ) / 25)) := by
  let d : ℝ → ℝ := fun x =>
    3 * x ^ 2 -
      2 * (14411518807585587 / 9007199254740992 : ℝ) * x +
      (331008924731595251230755975677869 /
        649037107316853453566312041152512 : ℝ)
  refine strictAntiOn_of_hasDerivWithinAt_neg
    (D := Set.Icc ((439 : ℝ) / 1000) ((11 : ℝ) / 25))
    (f := beneficialPowerMatrixIeeeDoubleRoundedCharPoly) (f' := d)
    (convex_Icc _ _) ?hcont ?hderiv ?hneg
  · exact (continuous_iff_continuousAt.mpr
        (fun x =>
          (beneficialPowerMatrixIeeeDoubleRoundedCharPoly_hasDerivAt x).continuousAt)).continuousOn
  · intro x _hx
    exact (beneficialPowerMatrixIeeeDoubleRoundedCharPoly_hasDerivAt x).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hxlo : (439 : ℝ) / 1000 < x := hx.1
    have hxhi : x < (11 : ℝ) / 25 := hx.2
    dsimp [d]
    nlinarith [sq_nonneg (x - (8 / 15 : ℝ))]

/-- The stored characteristic cubic is strictly increasing across the dominant
root interval. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharPoly_strictMonoOn_29_25_117_100 :
    StrictMonoOn beneficialPowerMatrixIeeeDoubleRoundedCharPoly
      (Set.Icc ((29 : ℝ) / 25) ((117 : ℝ) / 100)) := by
  let d : ℝ → ℝ := fun x =>
    3 * x ^ 2 -
      2 * (14411518807585587 / 9007199254740992 : ℝ) * x +
      (331008924731595251230755975677869 /
        649037107316853453566312041152512 : ℝ)
  refine strictMonoOn_of_hasDerivWithinAt_pos
    (D := Set.Icc ((29 : ℝ) / 25) ((117 : ℝ) / 100))
    (f := beneficialPowerMatrixIeeeDoubleRoundedCharPoly) (f' := d)
    (convex_Icc _ _) ?hcont ?hderiv ?hpos
  · exact (continuous_iff_continuousAt.mpr
        (fun x =>
          (beneficialPowerMatrixIeeeDoubleRoundedCharPoly_hasDerivAt x).continuousAt)).continuousOn
  · intro x _hx
    exact (beneficialPowerMatrixIeeeDoubleRoundedCharPoly_hasDerivAt x).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hxlo : (29 : ℝ) / 25 < x := hx.1
    have hxhi : x < (117 : ℝ) / 100 := hx.2
    dsimp [d]
    nlinarith [sq_nonneg (x - (8 / 15 : ℝ))]

/-- The small displaced root of the stored characteristic determinant is unique
in its certified bracket. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharDet_existsUnique_root_neg_one_e14_zero :
    ∃! lambda : ℝ,
      lambda ∈ Set.Icc (-(1 : ℝ) / (10 : ℝ) ^ 14) 0 ∧
        Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda) = 0 := by
  rcases beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_root_neg_one_e14_zero with
    ⟨lambda, hlambda, hroot⟩
  refine ⟨lambda, ⟨hlambda, hroot⟩, ?_⟩
  intro mu hmu
  by_cases h : mu = lambda
  · exact h
  have hpoly_lambda :
      beneficialPowerMatrixIeeeDoubleRoundedCharPoly lambda = 0 := by
    rw [← beneficialPowerMatrixIeeeDoubleRoundedCharDet_eq_poly]
    exact hroot
  have hpoly_mu :
      beneficialPowerMatrixIeeeDoubleRoundedCharPoly mu = 0 := by
    rw [← beneficialPowerMatrixIeeeDoubleRoundedCharDet_eq_poly]
    exact hmu.2
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have hmono :=
      beneficialPowerMatrixIeeeDoubleRoundedCharPoly_strictMonoOn_neg_one_e14_zero
        hmu.1 hlambda hlt
    rw [hpoly_mu, hpoly_lambda] at hmono
    linarith
  · have hmono :=
      beneficialPowerMatrixIeeeDoubleRoundedCharPoly_strictMonoOn_neg_one_e14_zero
        hlambda hmu.1 hgt
    rw [hpoly_lambda, hpoly_mu] at hmono
    linarith

/-- The stored characteristic determinant root near the smaller nonzero
displayed eigenvalue is unique in its certified bracket. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharDet_existsUnique_root_439_1000_11_25 :
    ∃! lambda : ℝ,
      lambda ∈ Set.Icc ((439 : ℝ) / 1000) ((11 : ℝ) / 25) ∧
        Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda) = 0 := by
  rcases beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_root_439_1000_11_25 with
    ⟨lambda, hlambda, hroot⟩
  refine ⟨lambda, ⟨hlambda, hroot⟩, ?_⟩
  intro mu hmu
  by_cases h : mu = lambda
  · exact h
  have hpoly_lambda :
      beneficialPowerMatrixIeeeDoubleRoundedCharPoly lambda = 0 := by
    rw [← beneficialPowerMatrixIeeeDoubleRoundedCharDet_eq_poly]
    exact hroot
  have hpoly_mu :
      beneficialPowerMatrixIeeeDoubleRoundedCharPoly mu = 0 := by
    rw [← beneficialPowerMatrixIeeeDoubleRoundedCharDet_eq_poly]
    exact hmu.2
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have hanti :=
      beneficialPowerMatrixIeeeDoubleRoundedCharPoly_strictAntiOn_439_1000_11_25
        hmu.1 hlambda hlt
    rw [hpoly_lambda, hpoly_mu] at hanti
    linarith
  · have hanti :=
      beneficialPowerMatrixIeeeDoubleRoundedCharPoly_strictAntiOn_439_1000_11_25
        hlambda hmu.1 hgt
    rw [hpoly_mu, hpoly_lambda] at hanti
    linarith

/-- The stored characteristic determinant root near the dominant displayed
eigenvalue is unique in its certified bracket. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharDet_existsUnique_root_29_25_117_100 :
    ∃! lambda : ℝ,
      lambda ∈ Set.Icc ((29 : ℝ) / 25) ((117 : ℝ) / 100) ∧
        Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda) = 0 := by
  rcases beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_root_29_25_117_100 with
    ⟨lambda, hlambda, hroot⟩
  refine ⟨lambda, ⟨hlambda, hroot⟩, ?_⟩
  intro mu hmu
  by_cases h : mu = lambda
  · exact h
  have hpoly_lambda :
      beneficialPowerMatrixIeeeDoubleRoundedCharPoly lambda = 0 := by
    rw [← beneficialPowerMatrixIeeeDoubleRoundedCharDet_eq_poly]
    exact hroot
  have hpoly_mu :
      beneficialPowerMatrixIeeeDoubleRoundedCharPoly mu = 0 := by
    rw [← beneficialPowerMatrixIeeeDoubleRoundedCharDet_eq_poly]
    exact hmu.2
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have hmono :=
      beneficialPowerMatrixIeeeDoubleRoundedCharPoly_strictMonoOn_29_25_117_100
        hmu.1 hlambda hlt
    rw [hpoly_mu, hpoly_lambda] at hmono
    linarith
  · have hmono :=
      beneficialPowerMatrixIeeeDoubleRoundedCharPoly_strictMonoOn_29_25_117_100
        hlambda hmu.1 hgt
    rw [hpoly_lambda, hpoly_mu] at hmono
    linarith

/-- Any root chosen from the certified dominant stored-root bracket is positive.
This supplies the nonzero denominator side condition for the finite-tail
power-method certificate once the dominant root has been selected. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharRoot_dominant_pos_of_mem
    {lambdaDominant : ℝ}
    (hdom : lambdaDominant ∈ Set.Icc ((29 : ℝ) / 25) ((117 : ℝ) / 100)) :
    0 < lambdaDominant :=
  (by norm_num : (0 : ℝ) < (29 : ℝ) / 25).trans_le hdom.1

/-- Any root chosen from the certified dominant stored-root bracket is nonzero. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharRoot_dominant_ne_zero_of_mem
    {lambdaDominant : ℝ}
    (hdom : lambdaDominant ∈ Set.Icc ((29 : ℝ) / 25) ((117 : ℝ) / 100)) :
    lambdaDominant ≠ 0 := by
  have hpos :=
    beneficialPowerMatrixIeeeDoubleRoundedCharRoot_dominant_pos_of_mem hdom
  exact ne_of_gt hpos

/-- The small displaced stored root has spectral ratio at most `1/2` relative
to any root chosen from the certified dominant stored-root bracket. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharRoot_small_abs_div_dominant_le_half
    {lambdaSmall lambdaDominant : ℝ}
    (hsmall : lambdaSmall ∈ Set.Icc (-(1 : ℝ) / (10 : ℝ) ^ 14) 0)
    (hdom : lambdaDominant ∈ Set.Icc ((29 : ℝ) / 25) ((117 : ℝ) / 100)) :
    |lambdaSmall| / |lambdaDominant| ≤ (1 : ℝ) / 2 := by
  have hsmall_abs : |lambdaSmall| = -lambdaSmall :=
    abs_of_nonpos hsmall.2
  have hdom_pos :=
    beneficialPowerMatrixIeeeDoubleRoundedCharRoot_dominant_pos_of_mem hdom
  have hdom_abs : |lambdaDominant| = lambdaDominant :=
    abs_of_pos hdom_pos
  rw [hsmall_abs, hdom_abs]
  exact (div_le_iff₀ hdom_pos).mpr (by
    nlinarith [hsmall.1, hdom.1])

/-- The stored root in the middle bracket has spectral ratio at most `1/2`
relative to any root chosen from the certified dominant stored-root bracket. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharRoot_mid_abs_div_dominant_le_half
    {lambdaMid lambdaDominant : ℝ}
    (hmid : lambdaMid ∈ Set.Icc ((439 : ℝ) / 1000) ((11 : ℝ) / 25))
    (hdom : lambdaDominant ∈ Set.Icc ((29 : ℝ) / 25) ((117 : ℝ) / 100)) :
    |lambdaMid| / |lambdaDominant| ≤ (1 : ℝ) / 2 := by
  have hmid_nonneg : 0 ≤ lambdaMid :=
    (by norm_num : (0 : ℝ) ≤ (439 : ℝ) / 1000).trans hmid.1
  have hmid_abs : |lambdaMid| = lambdaMid :=
    abs_of_nonneg hmid_nonneg
  have hdom_pos :=
    beneficialPowerMatrixIeeeDoubleRoundedCharRoot_dominant_pos_of_mem hdom
  have hdom_abs : |lambdaDominant| = lambdaDominant :=
    abs_of_pos hdom_pos
  rw [hmid_abs, hdom_abs]
  exact (div_le_iff₀ hdom_pos).mpr (by
    nlinarith [hmid.2, hdom.1])

/-- If the two non-dominant stored roots are chosen from the certified small
and middle brackets and the dominant root is chosen from its certified bracket,
then `q = 1/2` satisfies the finite-tail spectral-ratio side conditions. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharRoot_two_tail_spectral_ratio_le_half
    {lambdaSmall lambdaMid lambdaDominant : ℝ}
    (hsmall : lambdaSmall ∈ Set.Icc (-(1 : ℝ) / (10 : ℝ) ^ 14) 0)
    (hmid : lambdaMid ∈ Set.Icc ((439 : ℝ) / 1000) ((11 : ℝ) / 25))
    (hdom : lambdaDominant ∈ Set.Icc ((29 : ℝ) / 25) ((117 : ℝ) / 100)) :
    (∀ a : Fin 2,
        |(fun a : Fin 2 => if a = 0 then lambdaSmall else lambdaMid) a| /
            |lambdaDominant| ≤ (1 : ℝ) / 2) ∧
      0 ≤ (1 : ℝ) / 2 ∧ (1 : ℝ) / 2 < 1 := by
  constructor
  · intro a
    fin_cases a
    · simpa using
        beneficialPowerMatrixIeeeDoubleRoundedCharRoot_small_abs_div_dominant_le_half
          hsmall hdom
    · simpa using
        beneficialPowerMatrixIeeeDoubleRoundedCharRoot_mid_abs_div_dominant_le_half
          hmid hdom
  · constructor <;> norm_num

/-- The three certified stored-root brackets contain roots whose two
non-dominant-to-dominant spectral ratios are bounded by `1/2`.  This packages
the root-existence layer with the numerical `q < 1` side condition; it does not
yet prove global exhaustiveness or construct the associated eigenvectors. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_three_bracketed_roots_tail_ratio_le_half :
    ∃ lambdaSmall lambdaMid lambdaDominant : ℝ,
      (lambdaSmall ∈ Set.Icc (-(1 : ℝ) / (10 : ℝ) ^ 14) 0 ∧
        Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambdaSmall) = 0) ∧
      (lambdaMid ∈ Set.Icc ((439 : ℝ) / 1000) ((11 : ℝ) / 25) ∧
        Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambdaMid) = 0) ∧
      (lambdaDominant ∈ Set.Icc ((29 : ℝ) / 25) ((117 : ℝ) / 100) ∧
        Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambdaDominant) = 0) ∧
      (∀ a : Fin 2,
        |(fun a : Fin 2 => if a = 0 then lambdaSmall else lambdaMid) a| /
            |lambdaDominant| ≤ (1 : ℝ) / 2) ∧
      0 ≤ (1 : ℝ) / 2 ∧ (1 : ℝ) / 2 < 1 := by
  rcases beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_root_neg_one_e14_zero with
    ⟨lambdaSmall, hsmall, hrootSmall⟩
  rcases beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_root_439_1000_11_25 with
    ⟨lambdaMid, hmid, hrootMid⟩
  rcases beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_root_29_25_117_100 with
    ⟨lambdaDominant, hdom, hrootDominant⟩
  rcases
    beneficialPowerMatrixIeeeDoubleRoundedCharRoot_two_tail_spectral_ratio_le_half
      hsmall hmid hdom with
    ⟨hratio, hq_nonneg, hq_lt_one⟩
  exact
    ⟨lambdaSmall, lambdaMid, lambdaDominant,
      ⟨hsmall, hrootSmall⟩, ⟨hmid, hrootMid⟩, ⟨hdom, hrootDominant⟩,
      hratio, hq_nonneg, hq_lt_one⟩

/-- A concrete kernel vector for `lambda I - A`, formed as the cross product of
the first two rows of the stored beneficial-rounding characteristic matrix. -/
noncomputable def beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector
    (lambda : ℝ) : Fin 3 → ℝ
  | 0 =>
      beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda 0 1 *
          beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda 1 2 -
        beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda 0 2 *
          beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda 1 1
  | 1 =>
      beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda 0 2 *
          beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda 1 0 -
        beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda 0 0 *
          beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda 1 2
  | 2 =>
      beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda 0 0 *
          beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda 1 1 -
        beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda 0 1 *
          beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda 1 0

theorem beneficialPowerMatrixIeeeDoubleRoundedCharMatrix_kernel_isRightEigenpair
    {lambda : ℝ} {v : Fin 3 → ℝ}
    (hv_ne : ∃ i : Fin 3, v i ≠ 0)
    (hv_ker :
      ∀ i : Fin 3,
        matMulVec 3 (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda) v i = 0) :
    IsRightEigenpair 3 beneficialPowerMatrixIeeeDoubleRounded lambda v := by
  refine ⟨hv_ne, ?_⟩
  intro i
  have hchar :
      matMulVec 3 (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda) v i =
        lambda * v i - matMulVec 3 beneficialPowerMatrixIeeeDoubleRounded v i := by
    fin_cases i <;>
      simp [matMulVec, beneficialPowerMatrixIeeeDoubleRoundedCharMatrix,
        Fin.sum_univ_three] <;>
      ring_nf
  have h0 := hv_ker i
  rw [hchar] at h0
  linarith

theorem beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector_mulVec_eq_zero
    {lambda : ℝ}
    (hroot :
      Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda) = 0) :
    ∀ i : Fin 3,
      matMulVec 3 (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda)
          (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambda) i = 0 := by
  intro i
  fin_cases i
  · simp [matMulVec, beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector,
      Fin.sum_univ_three]
    ring_nf
  · simp [matMulVec, beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector,
      Fin.sum_univ_three]
    ring_nf
  · have hdet := hroot
    rw [Matrix.det_fin_three] at hdet
    simp [matMulVec, beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector,
      Fin.sum_univ_three] at hdet ⊢
    ring_nf at hdet ⊢
    exact hdet

theorem beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector_first_component_pos_of_gt_neg_half
    {lambda : ℝ}
    (hlambda : -(1 / 2 : ℝ) < lambda) :
    0 < beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambda 0 := by
  simp [beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector,
    beneficialPowerMatrixIeeeDoubleRoundedCharMatrix,
    beneficialPowerMatrixIeeeDoubleRounded_eq_explicit,
    beneficialPowerMatrixIeeeDoubleRoundedExplicit, zpow_neg]
  linarith

theorem beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector_nonzero_of_gt_neg_half
    {lambda : ℝ}
    (hlambda : -(1 / 2 : ℝ) < lambda) :
    ∃ i : Fin 3,
      beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambda i ≠ 0 := by
  exact ⟨0,
    ne_of_gt
      (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector_first_component_pos_of_gt_neg_half
        hlambda)⟩

theorem beneficialPowerMatrixIeeeDoubleRoundedCharRoot_isRightEigenpair_of_gt_neg_half
    {lambda : ℝ}
    (hlambda : -(1 / 2 : ℝ) < lambda)
    (hroot :
      Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda) = 0) :
    IsRightEigenpair 3 beneficialPowerMatrixIeeeDoubleRounded lambda
      (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambda) := by
  exact beneficialPowerMatrixIeeeDoubleRoundedCharMatrix_kernel_isRightEigenpair
    (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector_nonzero_of_gt_neg_half
      hlambda)
    (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector_mulVec_eq_zero hroot)

theorem beneficialPowerMatrixIeeeDoubleRoundedCharRoot_dominant_isRightEigenpair_of_mem
    {lambda : ℝ}
    (hDominant : lambda ∈ Set.Icc (29 / 25 : ℝ) (117 / 100 : ℝ))
    (hroot :
      Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda) = 0) :
    IsRightEigenpair 3 beneficialPowerMatrixIeeeDoubleRounded lambda
      (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambda) := by
  exact beneficialPowerMatrixIeeeDoubleRoundedCharRoot_isRightEigenpair_of_gt_neg_half
    (by linarith [hDominant.1]) hroot

theorem beneficialPowerMatrixIeeeDoubleRoundedCharRoot_small_isRightEigenpair_of_mem
    {lambda : ℝ}
    (hSmall : lambda ∈ Set.Icc (-(1 : ℝ) / (10 : ℝ) ^ 14) 0)
    (hroot :
      Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda) = 0) :
    IsRightEigenpair 3 beneficialPowerMatrixIeeeDoubleRounded lambda
      (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambda) := by
  exact beneficialPowerMatrixIeeeDoubleRoundedCharRoot_isRightEigenpair_of_gt_neg_half
    (by nlinarith [hSmall.1]) hroot

theorem beneficialPowerMatrixIeeeDoubleRoundedCharRoot_mid_isRightEigenpair_of_mem
    {lambda : ℝ}
    (hMid : lambda ∈ Set.Icc (439 / 1000 : ℝ) (11 / 25 : ℝ))
    (hroot :
      Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambda) = 0) :
    IsRightEigenpair 3 beneficialPowerMatrixIeeeDoubleRounded lambda
      (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambda) := by
  exact beneficialPowerMatrixIeeeDoubleRoundedCharRoot_isRightEigenpair_of_gt_neg_half
    (by nlinarith [hMid.1]) hroot

theorem beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_three_bracketed_roots_eigenpairs_tail_ratio_le_half :
    ∃ lambdaSmall lambdaMid lambdaDominant : ℝ,
      (lambdaSmall ∈ Set.Icc (-(1 : ℝ) / (10 : ℝ) ^ 14) 0 ∧
        Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambdaSmall) = 0 ∧
        IsRightEigenpair 3 beneficialPowerMatrixIeeeDoubleRounded lambdaSmall
          (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaSmall)) ∧
      (lambdaMid ∈ Set.Icc ((439 : ℝ) / 1000) ((11 : ℝ) / 25) ∧
        Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambdaMid) = 0 ∧
        IsRightEigenpair 3 beneficialPowerMatrixIeeeDoubleRounded lambdaMid
          (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaMid)) ∧
      (lambdaDominant ∈ Set.Icc ((29 : ℝ) / 25) ((117 : ℝ) / 100) ∧
        Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambdaDominant) = 0 ∧
        IsRightEigenpair 3 beneficialPowerMatrixIeeeDoubleRounded lambdaDominant
          (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaDominant)) ∧
      (∀ a : Fin 2,
        |(fun a : Fin 2 => if a = 0 then lambdaSmall else lambdaMid) a| /
            |lambdaDominant| ≤ (1 : ℝ) / 2) ∧
      0 ≤ (1 : ℝ) / 2 ∧ (1 : ℝ) / 2 < 1 := by
  rcases
    beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_three_bracketed_roots_tail_ratio_le_half
      with
    ⟨lambdaSmall, lambdaMid, lambdaDominant,
      ⟨hSmall, hrootSmall⟩, ⟨hMid, hrootMid⟩,
      ⟨hDominant, hrootDominant⟩, hratio, hq_nonneg, hq_lt_one⟩
  exact
    ⟨lambdaSmall, lambdaMid, lambdaDominant,
      ⟨hSmall, hrootSmall,
        beneficialPowerMatrixIeeeDoubleRoundedCharRoot_small_isRightEigenpair_of_mem
          hSmall hrootSmall⟩,
      ⟨hMid, hrootMid,
        beneficialPowerMatrixIeeeDoubleRoundedCharRoot_mid_isRightEigenpair_of_mem
          hMid hrootMid⟩,
      ⟨hDominant, hrootDominant,
        beneficialPowerMatrixIeeeDoubleRoundedCharRoot_dominant_isRightEigenpair_of_mem
          hDominant hrootDominant⟩,
      hratio, hq_nonneg, hq_lt_one⟩

theorem beneficialPowerMatrixIeeeDoubleRoundedCharRoot_three_brackets_pairwise_ne
    {lambdaSmall lambdaMid lambdaDominant : ℝ}
    (hSmall : lambdaSmall ∈ Set.Icc (-(1 : ℝ) / (10 : ℝ) ^ 14) 0)
    (hMid : lambdaMid ∈ Set.Icc (439 / 1000 : ℝ) (11 / 25 : ℝ))
    (hDominant : lambdaDominant ∈ Set.Icc (29 / 25 : ℝ) (117 / 100 : ℝ)) :
    lambdaSmall ≠ lambdaMid ∧
      lambdaSmall ≠ lambdaDominant ∧ lambdaMid ≠ lambdaDominant := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    nlinarith [hSmall.2, hMid.1]
  · intro h
    nlinarith [hSmall.2, hDominant.1]
  · intro h
    nlinarith [hMid.2, hDominant.1]

theorem beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_three_bracketed_distinct_roots_eigenpairs_tail_ratio_le_half :
    ∃ lambdaSmall lambdaMid lambdaDominant : ℝ,
      (lambdaSmall ∈ Set.Icc (-(1 : ℝ) / (10 : ℝ) ^ 14) 0 ∧
        Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambdaSmall) = 0 ∧
        IsRightEigenpair 3 beneficialPowerMatrixIeeeDoubleRounded lambdaSmall
          (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaSmall)) ∧
      (lambdaMid ∈ Set.Icc ((439 : ℝ) / 1000) ((11 : ℝ) / 25) ∧
        Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambdaMid) = 0 ∧
        IsRightEigenpair 3 beneficialPowerMatrixIeeeDoubleRounded lambdaMid
          (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaMid)) ∧
      (lambdaDominant ∈ Set.Icc ((29 : ℝ) / 25) ((117 : ℝ) / 100) ∧
        Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambdaDominant) = 0 ∧
        IsRightEigenpair 3 beneficialPowerMatrixIeeeDoubleRounded lambdaDominant
          (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaDominant)) ∧
      lambdaSmall ≠ lambdaMid ∧
      lambdaSmall ≠ lambdaDominant ∧
      lambdaMid ≠ lambdaDominant ∧
      (∀ a : Fin 2,
        |(fun a : Fin 2 => if a = 0 then lambdaSmall else lambdaMid) a| /
            |lambdaDominant| ≤ (1 : ℝ) / 2) ∧
      0 ≤ (1 : ℝ) / 2 ∧ (1 : ℝ) / 2 < 1 := by
  rcases
    beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_three_bracketed_roots_eigenpairs_tail_ratio_le_half
      with
    ⟨lambdaSmall, lambdaMid, lambdaDominant,
      hSmallData, hMidData, hDominantData, hratio, hq_nonneg, hq_lt_one⟩
  rcases hSmallData with ⟨hSmall, hrootSmall, heigSmall⟩
  rcases hMidData with ⟨hMid, hrootMid, heigMid⟩
  rcases hDominantData with ⟨hDominant, hrootDominant, heigDominant⟩
  rcases
    beneficialPowerMatrixIeeeDoubleRoundedCharRoot_three_brackets_pairwise_ne
      hSmall hMid hDominant with
    ⟨hSmallMid, hSmallDominant, hMidDominant⟩
  exact
    ⟨lambdaSmall, lambdaMid, lambdaDominant,
      ⟨hSmall, hrootSmall, heigSmall⟩,
      ⟨hMid, hrootMid, heigMid⟩,
      ⟨hDominant, hrootDominant, heigDominant⟩,
      hSmallMid, hSmallDominant, hMidDominant, hratio, hq_nonneg, hq_lt_one⟩

/-- The stored §1.15 eigenvector-column matrix formed from the characteristic
kernel vectors associated with the small, middle, and dominant stored roots. -/
noncomputable def beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix
    (lambdaSmall lambdaMid lambdaDominant : ℝ) : Fin 3 → Fin 3 → ℝ :=
  threeColumnMatrix
    (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaSmall)
    (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaMid)
    (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaDominant)

theorem beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix_det_ne_zero_of_distinct_eigenpairs
    {lambdaSmall lambdaMid lambdaDominant : ℝ}
    (hSmall :
      IsRightEigenpair 3 beneficialPowerMatrixIeeeDoubleRounded lambdaSmall
        (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaSmall))
    (hMid :
      IsRightEigenpair 3 beneficialPowerMatrixIeeeDoubleRounded lambdaMid
        (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaMid))
    (hDominant :
      IsRightEigenpair 3 beneficialPowerMatrixIeeeDoubleRounded lambdaDominant
        (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaDominant))
    (hSmallMid : lambdaSmall ≠ lambdaMid)
    (hSmallDominant : lambdaSmall ≠ lambdaDominant)
    (hMidDominant : lambdaMid ≠ lambdaDominant) :
    Matrix.det
        (beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix
          lambdaSmall lambdaMid lambdaDominant :
          Matrix (Fin 3) (Fin 3) ℝ) ≠ 0 := by
  simpa [beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix] using
    three_rightEigenvectors_pairwise_distinct_threeColumnMatrix_det_ne_zero
      hSmall hMid hDominant hSmallMid hSmallDominant hMidDominant

theorem beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix_det_ne_zero_of_bracketed_roots
    {lambdaSmall lambdaMid lambdaDominant : ℝ}
    (hSmall : lambdaSmall ∈ Set.Icc (-(1 : ℝ) / (10 : ℝ) ^ 14) 0)
    (hrootSmall :
      Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambdaSmall) = 0)
    (hMid : lambdaMid ∈ Set.Icc ((439 : ℝ) / 1000) ((11 : ℝ) / 25))
    (hrootMid :
      Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambdaMid) = 0)
    (hDominant :
      lambdaDominant ∈ Set.Icc ((29 : ℝ) / 25) ((117 : ℝ) / 100))
    (hrootDominant :
      Matrix.det
        (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambdaDominant) = 0) :
    Matrix.det
        (beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix
          lambdaSmall lambdaMid lambdaDominant :
          Matrix (Fin 3) (Fin 3) ℝ) ≠ 0 := by
  have heigSmall :=
    beneficialPowerMatrixIeeeDoubleRoundedCharRoot_small_isRightEigenpair_of_mem
      hSmall hrootSmall
  have heigMid :=
    beneficialPowerMatrixIeeeDoubleRoundedCharRoot_mid_isRightEigenpair_of_mem
      hMid hrootMid
  have heigDominant :=
    beneficialPowerMatrixIeeeDoubleRoundedCharRoot_dominant_isRightEigenpair_of_mem
      hDominant hrootDominant
  rcases
    beneficialPowerMatrixIeeeDoubleRoundedCharRoot_three_brackets_pairwise_ne
      hSmall hMid hDominant with
    ⟨hSmallMid, hSmallDominant, hMidDominant⟩
  exact
    beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix_det_ne_zero_of_distinct_eigenpairs
      heigSmall heigMid heigDominant
      hSmallMid hSmallDominant hMidDominant

theorem beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix_isRightInverse_of_bracketed_roots
    {lambdaSmall lambdaMid lambdaDominant : ℝ}
    (hSmall : lambdaSmall ∈ Set.Icc (-(1 : ℝ) / (10 : ℝ) ^ 14) 0)
    (hrootSmall :
      Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambdaSmall) = 0)
    (hMid : lambdaMid ∈ Set.Icc ((439 : ℝ) / 1000) ((11 : ℝ) / 25))
    (hrootMid :
      Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambdaMid) = 0)
    (hDominant :
      lambdaDominant ∈ Set.Icc ((29 : ℝ) / 25) ((117 : ℝ) / 100))
    (hrootDominant :
      Matrix.det
        (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambdaDominant) = 0) :
    IsRightInverse 3
      (beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix
        lambdaSmall lambdaMid lambdaDominant)
      (nonsingInv 3
        (beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix
          lambdaSmall lambdaMid lambdaDominant)) :=
  (isInverse_nonsingInv_of_det_ne_zero 3
    (beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix
      lambdaSmall lambdaMid lambdaDominant)
    (beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix_det_ne_zero_of_bracketed_roots
      hSmall hrootSmall hMid hrootMid hDominant hrootDominant)).2

theorem beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_three_bracketed_distinct_roots_eigenbasis_rightInverse_tail_ratio_le_half :
    ∃ lambdaSmall lambdaMid lambdaDominant : ℝ,
      (lambdaSmall ∈ Set.Icc (-(1 : ℝ) / (10 : ℝ) ^ 14) 0 ∧
        Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambdaSmall) = 0 ∧
        IsRightEigenpair 3 beneficialPowerMatrixIeeeDoubleRounded lambdaSmall
          (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaSmall)) ∧
      (lambdaMid ∈ Set.Icc ((439 : ℝ) / 1000) ((11 : ℝ) / 25) ∧
        Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambdaMid) = 0 ∧
        IsRightEigenpair 3 beneficialPowerMatrixIeeeDoubleRounded lambdaMid
          (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaMid)) ∧
      (lambdaDominant ∈ Set.Icc ((29 : ℝ) / 25) ((117 : ℝ) / 100) ∧
        Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambdaDominant) = 0 ∧
        IsRightEigenpair 3 beneficialPowerMatrixIeeeDoubleRounded lambdaDominant
          (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaDominant)) ∧
      lambdaSmall ≠ lambdaMid ∧
      lambdaSmall ≠ lambdaDominant ∧
      lambdaMid ≠ lambdaDominant ∧
      Matrix.det
        (beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix
          lambdaSmall lambdaMid lambdaDominant :
          Matrix (Fin 3) (Fin 3) ℝ) ≠ 0 ∧
      IsRightInverse 3
        (beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix
          lambdaSmall lambdaMid lambdaDominant)
        (nonsingInv 3
          (beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix
            lambdaSmall lambdaMid lambdaDominant)) ∧
      (∀ a : Fin 2,
        |(fun a : Fin 2 => if a = 0 then lambdaSmall else lambdaMid) a| /
            |lambdaDominant| ≤ (1 : ℝ) / 2) ∧
      0 ≤ (1 : ℝ) / 2 ∧ (1 : ℝ) / 2 < 1 := by
  rcases
    beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_three_bracketed_distinct_roots_eigenpairs_tail_ratio_le_half
      with
    ⟨lambdaSmall, lambdaMid, lambdaDominant,
      hSmallData, hMidData, hDominantData,
      hSmallMid, hSmallDominant, hMidDominant,
      hratio, hq_nonneg, hq_lt_one⟩
  rcases hSmallData with ⟨hSmall, hrootSmall, heigSmall⟩
  rcases hMidData with ⟨hMid, hrootMid, heigMid⟩
  rcases hDominantData with ⟨hDominant, hrootDominant, heigDominant⟩
  have hdet :
      Matrix.det
        (beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix
          lambdaSmall lambdaMid lambdaDominant :
          Matrix (Fin 3) (Fin 3) ℝ) ≠ 0 :=
    beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix_det_ne_zero_of_distinct_eigenpairs
      heigSmall heigMid heigDominant
      hSmallMid hSmallDominant hMidDominant
  have hright :
      IsRightInverse 3
        (beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix
          lambdaSmall lambdaMid lambdaDominant)
        (nonsingInv 3
          (beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix
            lambdaSmall lambdaMid lambdaDominant)) :=
    (isInverse_nonsingInv_of_det_ne_zero 3
      (beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix
        lambdaSmall lambdaMid lambdaDominant) hdet).2
  exact
    ⟨lambdaSmall, lambdaMid, lambdaDominant,
      ⟨hSmall, hrootSmall, heigSmall⟩,
      ⟨hMid, hrootMid, heigMid⟩,
      ⟨hDominant, hrootDominant, heigDominant⟩,
      hSmallMid, hSmallDominant, hMidDominant, hdet, hright,
      hratio, hq_nonneg, hq_lt_one⟩

/-- The displayed matrix entry `(1,3)` is the nonterminating binary fraction
`1/5`. -/
theorem beneficialPowerMatrix_entry_zero_two_eq_one_fifth :
    beneficialPowerMatrix 0 2 = 1 / 5 := by
  norm_num [beneficialPowerMatrix]

/-- The displayed matrix entry `(1,3)` cannot be stored exactly as a terminating
binary fraction. -/
theorem beneficialPowerMatrix_entry_zero_two_not_binaryTerminating :
    ¬ BinaryTerminating (beneficialPowerMatrix 0 2) := by
  simpa [beneficialPowerMatrix_entry_zero_two_eq_one_fifth] using
    one_fifth_not_binaryTerminating

/-- The displayed matrix entry `(1,3)` is not exactly an IEEE-double finite
value. -/
theorem beneficialPowerMatrix_entry_zero_two_not_ieeeDoubleFiniteSystem :
    ¬ FloatingPointFormat.finiteSystem FloatingPointFormat.ieeeDoubleFormat
        (beneficialPowerMatrix 0 2) := by
  simpa [beneficialPowerMatrix_entry_zero_two_eq_one_fifth] using
    one_fifth_not_ieeeDoubleFiniteSystem

/-- The displayed §1.15 matrix is not exactly storable entrywise in binary:
at least one displayed entry is not a terminating binary fraction. -/
theorem beneficialPowerMatrix_not_matrixEntriesBinaryTerminating :
    ¬ MatrixEntriesBinaryTerminating beneficialPowerMatrix := by
  intro h
  exact beneficialPowerMatrix_entry_zero_two_not_binaryTerminating (h 0 2)

/-- The displayed §1.15 matrix is not exactly storable entrywise in the
repository's IEEE-double finite system. -/
theorem beneficialPowerMatrix_not_matrixEntriesIeeeDoubleFiniteSystem :
    ¬ MatrixEntriesFiniteSystem FloatingPointFormat.ieeeDoubleFormat
        beneficialPowerMatrix := by
  intro h
  exact beneficialPowerMatrix_entry_zero_two_not_ieeeDoubleFiniteSystem (h 0 2)

/-- The displayed starting vector `[1,1,1]^T`. -/
noncomputable def beneficialPowerStart : Fin 3 → ℝ :=
  fun _ => 1

theorem beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_three_bracketed_distinct_roots_eigenbasis_coefficients_tail_ratio_le_half :
    ∃ lambdaSmall lambdaMid lambdaDominant
        coeffSmall coeffMid coeffDominant : ℝ,
      (lambdaSmall ∈ Set.Icc (-(1 : ℝ) / (10 : ℝ) ^ 14) 0 ∧
        Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambdaSmall) = 0 ∧
        IsRightEigenpair 3 beneficialPowerMatrixIeeeDoubleRounded lambdaSmall
          (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaSmall)) ∧
      (lambdaMid ∈ Set.Icc ((439 : ℝ) / 1000) ((11 : ℝ) / 25) ∧
        Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambdaMid) = 0 ∧
        IsRightEigenpair 3 beneficialPowerMatrixIeeeDoubleRounded lambdaMid
          (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaMid)) ∧
      (lambdaDominant ∈ Set.Icc ((29 : ℝ) / 25) ((117 : ℝ) / 100) ∧
        Matrix.det (beneficialPowerMatrixIeeeDoubleRoundedCharMatrix lambdaDominant) = 0 ∧
        IsRightEigenpair 3 beneficialPowerMatrixIeeeDoubleRounded lambdaDominant
          (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaDominant)) ∧
      lambdaSmall ≠ lambdaMid ∧
      lambdaSmall ≠ lambdaDominant ∧
      lambdaMid ≠ lambdaDominant ∧
      Matrix.det
        (beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix
          lambdaSmall lambdaMid lambdaDominant :
          Matrix (Fin 3) (Fin 3) ℝ) ≠ 0 ∧
      IsRightInverse 3
        (beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix
          lambdaSmall lambdaMid lambdaDominant)
        (nonsingInv 3
          (beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix
            lambdaSmall lambdaMid lambdaDominant)) ∧
      (beneficialPowerStart =
        fun i =>
          coeffDominant *
              beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector
                lambdaDominant i +
            ∑ a : Fin 2,
              (if a = 0 then coeffSmall else coeffMid) *
                (if a = 0 then
                  beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector
                    lambdaSmall i
                else
                  beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector
                    lambdaMid i)) ∧
      (∀ a : Fin 2,
        |(fun a : Fin 2 => if a = 0 then lambdaSmall else lambdaMid) a| /
            |lambdaDominant| ≤ (1 : ℝ) / 2) ∧
      0 ≤ (1 : ℝ) / 2 ∧ (1 : ℝ) / 2 < 1 := by
  rcases
    beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_three_bracketed_distinct_roots_eigenbasis_rightInverse_tail_ratio_le_half
      with
    ⟨lambdaSmall, lambdaMid, lambdaDominant,
      hSmallData, hMidData, hDominantData,
      hSmallMid, hSmallDominant, hMidDominant, hdet, hright,
      hratio, hq_nonneg, hq_lt_one⟩
  let V :=
    beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix
      lambdaSmall lambdaMid lambdaDominant
  let V_inv := nonsingInv 3 V
  let coeff := matMulVec 3 V_inv beneficialPowerStart
  have hright' :
      IsRightInverse 3
        (threeColumnMatrix
          (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaSmall)
          (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaMid)
          (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector
            lambdaDominant))
        V_inv := by
    simpa [V, V_inv, beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix]
      using hright
  have hcolumns :
      beneficialPowerStart =
        fun i =>
          coeff 0 *
              beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector
                lambdaSmall i +
            coeff 1 *
              beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector
                lambdaMid i +
            coeff 2 *
              beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector
                lambdaDominant i := by
    simpa [coeff, V_inv, V,
      beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix] using
      (threeColumnMatrix_decompose_of_rightInverse
        (v₁ :=
          beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaSmall)
        (v₂ :=
          beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaMid)
        (v₃ :=
          beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector
            lambdaDominant)
        (V_inv := V_inv) hright' beneficialPowerStart)
  have htail :
      beneficialPowerStart =
        fun i =>
          coeff 2 *
              beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector
                lambdaDominant i +
            ∑ a : Fin 2,
              (if a = 0 then coeff 0 else coeff 1) *
                (if a = 0 then
                  beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector
                    lambdaSmall i
                else
                  beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector
                    lambdaMid i) := by
    rw [hcolumns]
    ext i
    rw [Fin.sum_univ_two]
    simp
    ring
  exact
    ⟨lambdaSmall, lambdaMid, lambdaDominant, coeff 0, coeff 1, coeff 2,
      hSmallData, hMidData, hDominantData,
      hSmallMid, hSmallDominant, hMidDominant, hdet, hright, htail,
      hratio, hq_nonneg, hq_lt_one⟩

theorem beneficialPowerMatrixIeeeDoubleRoundedCharStartReplacement_det_eq
    (lambdaSmall lambdaMid : ℝ) :
    Matrix.det
        (threeColumnMatrix
          (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaSmall)
          (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaMid)
          beneficialPowerStart :
          Matrix (Fin 3) (Fin 3) ℝ) =
      -((3602879701896397 : ℝ) * (lambdaMid - lambdaSmall) *
        ((973555660975280180349468061728768 : ℝ) *
            lambdaMid * lambdaSmall -
          (18014398509481984 : ℝ) * lambdaMid -
          (18014398509481984 : ℝ) * lambdaSmall +
          (18014398509481985 : ℝ))) /
        (5846006549323611672814739330865132078623730171904 : ℝ) := by
  rw [Matrix.det_fin_three]
  simp [threeColumnMatrix,
    beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector,
    beneficialPowerMatrixIeeeDoubleRoundedCharMatrix,
    beneficialPowerMatrixIeeeDoubleRounded_eq_explicit,
    beneficialPowerMatrixIeeeDoubleRoundedExplicit,
    beneficialPowerStart, zpow_neg]
  ring_nf

theorem beneficialPowerMatrixIeeeDoubleRoundedCharStartReplacement_det_lt_zero_of_tight_small_mid
    {lambdaSmall lambdaMid : ℝ}
    (hSmall : lambdaSmall ∈ Set.Icc (-(1 : ℝ) / (10 : ℝ) ^ 17) 0)
    (hMid : lambdaMid ∈ Set.Icc ((439 : ℝ) / 1000) ((11 : ℝ) / 25)) :
    Matrix.det
        (threeColumnMatrix
          (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaSmall)
          (beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaMid)
          beneficialPowerStart :
          Matrix (Fin 3) (Fin 3) ℝ) < 0 := by
  rw [beneficialPowerMatrixIeeeDoubleRoundedCharStartReplacement_det_eq]
  have hdiff_pos : 0 < lambdaMid - lambdaSmall := by
    nlinarith [hMid.1, hSmall.2]
  have hmid_gap_nonneg : 0 ≤ (11 / 25 : ℝ) - lambdaMid := by
    nlinarith [hMid.2]
  have hprod_gap_nonpos :
      ((11 / 25 : ℝ) - lambdaMid) * lambdaSmall ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hmid_gap_nonneg hSmall.2
  have hprod_lower :
      (11 / 25 : ℝ) * lambdaSmall ≤ lambdaMid * lambdaSmall := by
    nlinarith [hprod_gap_nonpos]
  have hprod_tight :
      -((11 : ℝ) / ((25 : ℝ) * (10 : ℝ) ^ 17)) ≤
        lambdaMid * lambdaSmall := by
    nlinarith [hprod_lower, hSmall.1]
  have hP_pos :
      0 <
        (973555660975280180349468061728768 : ℝ) *
            lambdaMid * lambdaSmall -
          (18014398509481984 : ℝ) * lambdaMid -
          (18014398509481984 : ℝ) * lambdaSmall +
          (18014398509481985 : ℝ) := by
    have hterm1 :
        -((973555660975280180349468061728768 : ℝ) * (11 : ℝ) /
            ((25 : ℝ) * (10 : ℝ) ^ 17)) ≤
          (973555660975280180349468061728768 : ℝ) *
            lambdaMid * lambdaSmall := by
      nlinarith [hprod_tight]
    have hterm2 :
        -((18014398509481984 : ℝ) * (11 : ℝ) / 25) ≤
          -(18014398509481984 : ℝ) * lambdaMid := by
      nlinarith [hMid.2]
    have hterm3 :
        0 ≤ -(18014398509481984 : ℝ) * lambdaSmall := by
      nlinarith [hSmall.2]
    nlinarith
  have hconst_pos : 0 < (3602879701896397 : ℝ) := by norm_num
  have hden_pos :
      0 < (5846006549323611672814739330865132078623730171904 : ℝ) := by
    norm_num
  nlinarith

/-- The concrete §1.15 certificate type for the entrywise IEEE-double stored
matrix and displayed start vector.  A value of this type is exactly the
dominant-eigencomponent package consumed by the finite-tail convergence
theorem. -/
noncomputable abbrev BeneficialPowerStoredStartDominantComponentCertificate
    (m : ℕ) : Type :=
  PowerMethodDominantFiniteTailCertificate 3 m
    beneficialPowerMatrixIeeeDoubleRounded beneficialPowerStart

/-- Concrete non-empirical dominant-component certificate for the entrywise
IEEE-double stored §1.15 matrix and displayed start vector.  The small stored
root is selected from the tighter `[-10^-17,0]` bracket so that the determinant
with `beneficialPowerStart` replacing the dominant column has a certified
nonzero sign; this proves the constructed dominant coefficient is nonzero. -/
theorem beneficialPowerStoredStart_exists_dominant_component_certificate :
    ∃ cert : BeneficialPowerStoredStartDominantComponentCertificate 2,
      cert.q = (1 : ℝ) / 2 := by
  rcases
    beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_root_neg_one_e17_zero with
    ⟨lambdaSmall, hSmallTight, hrootSmall⟩
  rcases
    beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_root_439_1000_11_25 with
    ⟨lambdaMid, hMid, hrootMid⟩
  rcases
    beneficialPowerMatrixIeeeDoubleRoundedCharDet_exists_root_29_25_117_100 with
    ⟨lambdaDominant, hDominant, hrootDominant⟩
  have hSmall :
      lambdaSmall ∈ Set.Icc (-(1 : ℝ) / (10 : ℝ) ^ 14) 0 := by
    constructor
    · nlinarith [hSmallTight.1]
    · exact hSmallTight.2
  let vSmall := beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaSmall
  let vMid := beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaMid
  let vDominant :=
    beneficialPowerMatrixIeeeDoubleRoundedCharKernelVector lambdaDominant
  let V :=
    beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix
      lambdaSmall lambdaMid lambdaDominant
  let V_inv := nonsingInv 3 V
  let coeff := matMulVec 3 V_inv beneficialPowerStart
  have heigSmall :
      IsRightEigenpair 3 beneficialPowerMatrixIeeeDoubleRounded lambdaSmall
        vSmall := by
    simpa [vSmall] using
      beneficialPowerMatrixIeeeDoubleRoundedCharRoot_small_isRightEigenpair_of_mem
        hSmall hrootSmall
  have heigMid :
      IsRightEigenpair 3 beneficialPowerMatrixIeeeDoubleRounded lambdaMid
        vMid := by
    simpa [vMid] using
      beneficialPowerMatrixIeeeDoubleRoundedCharRoot_mid_isRightEigenpair_of_mem
        hMid hrootMid
  have heigDominant :
      IsRightEigenpair 3 beneficialPowerMatrixIeeeDoubleRounded lambdaDominant
        vDominant := by
    simpa [vDominant] using
      beneficialPowerMatrixIeeeDoubleRoundedCharRoot_dominant_isRightEigenpair_of_mem
        hDominant hrootDominant
  have hright :
      IsRightInverse 3
        (beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix
          lambdaSmall lambdaMid lambdaDominant)
        (nonsingInv 3
          (beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix
            lambdaSmall lambdaMid lambdaDominant)) :=
    beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix_isRightInverse_of_bracketed_roots
      hSmall hrootSmall hMid hrootMid hDominant hrootDominant
  have hright' :
      IsRightInverse 3 (threeColumnMatrix vSmall vMid vDominant) V_inv := by
    simpa [V, V_inv, vSmall, vMid, vDominant,
      beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix] using hright
  have hcolumns :
      beneficialPowerStart =
        fun i => coeff 0 * vSmall i + coeff 1 * vMid i +
          coeff 2 * vDominant i := by
    simpa [coeff, V_inv, V, vSmall, vMid, vDominant,
      beneficialPowerMatrixIeeeDoubleRoundedCharEigenvectorMatrix] using
      (threeColumnMatrix_decompose_of_rightInverse
        (v₁ := vSmall) (v₂ := vMid) (v₃ := vDominant)
        (V_inv := V_inv) hright' beneficialPowerStart)
  have hdecomp :
      beneficialPowerStart =
        fun i =>
          coeff 2 * vDominant i +
            ∑ a : Fin 2,
              (if a = 0 then coeff 0 else coeff 1) *
                (if a = 0 then vSmall i else vMid i) := by
    rw [hcolumns]
    ext i
    rw [Fin.sum_univ_two]
    simp
    ring
  have hreplace_ne :
      Matrix.det
        (threeColumnMatrix vSmall vMid beneficialPowerStart :
          Matrix (Fin 3) (Fin 3) ℝ) ≠ 0 := by
    exact ne_of_lt
      (by
        simpa [vSmall, vMid] using
          beneficialPowerMatrixIeeeDoubleRoundedCharStartReplacement_det_lt_zero_of_tight_small_mid
            hSmallTight hMid)
  have hcoeffDominant_ne : coeff 2 ≠ 0 :=
    threeColumnMatrix_decompose_coeff_two_ne_zero_of_replacement_det_ne_zero
      (v₁ := vSmall) (v₂ := vMid) (v₃ := vDominant)
      (x := beneficialPowerStart) (V_inv := V_inv) hright' hreplace_ne
  have hlambdaDominant_ne : lambdaDominant ≠ 0 :=
    beneficialPowerMatrixIeeeDoubleRoundedCharRoot_dominant_ne_zero_of_mem
      hDominant
  have hratio :
      ∀ a : Fin 2,
        |(fun a : Fin 2 => if a = 0 then lambdaSmall else lambdaMid) a| /
            |lambdaDominant| ≤ (1 : ℝ) / 2 :=
    (beneficialPowerMatrixIeeeDoubleRoundedCharRoot_two_tail_spectral_ratio_le_half
      hSmall hMid hDominant).1
  refine
    ⟨{
      lambdaDominant := lambdaDominant
      coeffDominant := coeff 2
      q := (1 : ℝ) / 2
      lambdaTail := fun a : Fin 2 => if a = 0 then lambdaSmall else lambdaMid
      coeffTail := fun a : Fin 2 => if a = 0 then coeff 0 else coeff 1
      vDominant := vDominant
      vTail := fun a : Fin 2 => if a = 0 then vSmall else vMid
      start_decomposition := hdecomp
      dominant_eigenpair := heigDominant
      tail_eigenpairs := ?tail_eigenpairs
      coeffDominant_ne_zero := hcoeffDominant_ne
      lambdaDominant_ne_zero := hlambdaDominant_ne
      tail_spectral_ratio_le := hratio
      q_nonneg := by norm_num
      q_lt_one := by norm_num
    }, rfl⟩
  intro a
  fin_cases a <;> simp [heigSmall, heigMid]

/-- If the remaining §1.15 stored-matrix dominant-component certificate is
supplied, the displayed start vector's scaled power-method residual for the
entrywise IEEE-double stored matrix tends to zero.  This is an implementation
handoff theorem, not a proof that the certificate holds. -/
theorem beneficialPowerStoredStart_dominant_component_certificate_scaled_residual_tendsto_zero
    {m : ℕ}
    (cert : BeneficialPowerStoredStartDominantComponentCertificate m) :
    Tendsto
      (fun k : ℕ =>
        vecNorm2
            (fun i =>
              powerMethodIterate 3 beneficialPowerMatrixIeeeDoubleRounded k
                  beneficialPowerStart i -
                cert.coeffDominant * cert.lambdaDominant ^ k *
                  cert.vDominant i) /
          |cert.coeffDominant * cert.lambdaDominant ^ k|)
      atTop (𝓝 0) :=
  cert.scaled_residual_tendsto_zero

/-- A named concrete finite-tail certificate for the entrywise IEEE-double
stored §1.15 matrix and the displayed start vector.  This extracts the
certificate proved above, rather than treating the historical MATLAB/BLAS
display as a theorem target. -/
noncomputable def beneficialPowerStoredStartDominantComponentCert :
    BeneficialPowerStoredStartDominantComponentCertificate 2 :=
  Classical.choose beneficialPowerStoredStart_exists_dominant_component_certificate

/-- The named concrete §1.15 stored-start certificate has the source-facing
geometric tail ratio `q = 1/2`. -/
theorem beneficialPowerStoredStartDominantComponentCert_q_eq :
    beneficialPowerStoredStartDominantComponentCert.q = (1 : ℝ) / 2 :=
  Classical.choose_spec beneficialPowerStoredStart_exists_dominant_component_certificate

/-- Source-level stored-matrix power-method convergence theorem for §1.15.
For the entrywise IEEE-double stored matrix and displayed start vector, Lean
proves that the residual after subtracting the certified dominant component,
scaled by that dominant component, tends to zero.  This is the closed
machine-independent mathematical phenomenon; the historical MATLAB/BLAS
first-step printout and 38-iteration display remain empirical artifacts unless
an explicit routine/display model is supplied. -/
theorem beneficialPowerStoredStart_scaled_residual_tendsto_zero :
    Tendsto
      (fun k : ℕ =>
        vecNorm2
            (fun i =>
              powerMethodIterate 3 beneficialPowerMatrixIeeeDoubleRounded k
                  beneficialPowerStart i -
                beneficialPowerStoredStartDominantComponentCert.coeffDominant *
                  beneficialPowerStoredStartDominantComponentCert.lambdaDominant ^ k *
                  beneficialPowerStoredStartDominantComponentCert.vDominant i) /
          |beneficialPowerStoredStartDominantComponentCert.coeffDominant *
            beneficialPowerStoredStartDominantComponentCert.lambdaDominant ^ k|)
      atTop (𝓝 0) := by
  exact
    beneficialPowerStoredStart_dominant_component_certificate_scaled_residual_tendsto_zero
      beneficialPowerStoredStartDominantComponentCert

/-- The exact first-step vector produced by entrywise IEEE-double storage of
the displayed §1.15 matrix, before any subsequent normalization. -/
noncomputable def beneficialPowerMatrixIeeeDoubleRoundedFirstStep : Fin 3 → ℝ
  | ⟨0, _⟩ => (1 : ℝ) / (2 : ℝ) ^ 54
  | ⟨1, _⟩ => -((1 : ℝ) / (2 : ℝ) ^ 54)
  | ⟨2, _⟩ => -((1 : ℝ) / (2 : ℝ) ^ 55)

/-- A concrete left-to-right rounded row-sum trace for the first multiplication
by `[1,1,1]^T` after entrywise IEEE-double storage.  Multiplication by the
exact entries of the start vector is suppressed because all start entries are
`1`; this definition isolates the rounded additions in the row sums. -/
noncomputable def beneficialPowerMatrixIeeeDoubleRoundedFirstStepLeftToRight :
    Fin 3 → ℝ :=
  fun i =>
    let fmt := FloatingPointFormat.ieeeDoubleFormat
    let s01 := fmt.finiteRoundToEvenOp BasicOp.add
      (beneficialPowerMatrixIeeeDoubleRounded i 0)
      (beneficialPowerMatrixIeeeDoubleRounded i 1)
    fmt.finiteRoundToEvenOp BasicOp.add s01
      (beneficialPowerMatrixIeeeDoubleRounded i 2)

private theorem beneficialPowerMatrixIeeeDoubleRounded_leftToRight_row_two_first_add_eq :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
        (beneficialPowerMatrixIeeeDoubleRounded 2 0)
        (beneficialPowerMatrixIeeeDoubleRounded 2 1) =
      -(1 / 2 : ℝ) := by
  unfold beneficialPowerMatrixIeeeDoubleRounded
  simp [beneficialPowerMatrix, ieeeDoubleFormat_neg_one_tenth_rounds_to,
    ieeeDoubleFormat_neg_two_fifths_rounds_to]
  simp [FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact]
  convert ieeeDoubleFormat_neg_half_plus_two_pow_neg55_rounds_to_neg_half using 1 <;>
    norm_num [zpow_neg]

/-- In a left-to-right rounded-add row-sum trace, the third component cancels
to zero after the first rounded add has produced exactly `-1/2`.  This shows
that the hidden MATLAB/BLAS operation order matters: the entrywise-stored exact
row sum is `-2^-55`, but this particular rounded-add trace loses it. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedFirstStepLeftToRight_two_component_eq_zero :
    beneficialPowerMatrixIeeeDoubleRoundedFirstStepLeftToRight 2 = 0 := by
  unfold beneficialPowerMatrixIeeeDoubleRoundedFirstStepLeftToRight
  change FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
      (FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
        (beneficialPowerMatrixIeeeDoubleRounded 2 0)
        (beneficialPowerMatrixIeeeDoubleRounded 2 1))
      (beneficialPowerMatrixIeeeDoubleRounded 2 2) = 0
  rw [beneficialPowerMatrixIeeeDoubleRounded_leftToRight_row_two_first_add_eq]
  simp [beneficialPowerMatrixIeeeDoubleRounded, beneficialPowerMatrix]
  rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num,
    ieeeDoubleFormat_one_half_rounds_to]
  have hfinite :
      FloatingPointFormat.ieeeDoubleFormat.finiteSystem
        (BasicOp.exact BasicOp.add (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) := by
    simpa [BasicOp.exact] using
      (FloatingPointFormat.ieeeDoubleFormat.finiteSystem_zero)
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite]
  norm_num [BasicOp.exact]
  rfl

/-- The concrete left-to-right rounded-add trace is not identical to the
entrywise-stored exact row-sum vector: its third component is zero, while the
entrywise row sum is `-2^-55`. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedFirstStepLeftToRight_ne_firstStep :
    beneficialPowerMatrixIeeeDoubleRoundedFirstStepLeftToRight ≠
      beneficialPowerMatrixIeeeDoubleRoundedFirstStep := by
  intro h
  have hcomp := congr_fun h (2 : Fin 3)
  rw [beneficialPowerMatrixIeeeDoubleRoundedFirstStepLeftToRight_two_component_eq_zero]
    at hcomp
  norm_num [beneficialPowerMatrixIeeeDoubleRoundedFirstStep] at hcomp

private theorem ieeeDoubleFormat_normalizedValue_finiteSystem
    (negative : Bool) {m : ℕ} {e : ℤ}
    (hm : FloatingPointFormat.ieeeDoubleFormat.normalizedMantissa m)
    (he : FloatingPointFormat.ieeeDoubleFormat.exponentInRange e) :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem
      (FloatingPointFormat.ieeeDoubleFormat.normalizedValue negative m e) :=
  Or.inr (Or.inl ⟨negative, m, e, hm, he, rfl⟩)

private theorem ieeeDoubleFormat_neg_7205759403792793_two_pow_neg54_finiteSystem :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem
      (-((7205759403792793 : ℝ) * (2 : ℝ) ^ (-54 : ℤ))) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  have hm : fmt.normalizedMantissa 7205759403792793 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (-1 : ℤ) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.exponentInRange]
  have hval :
      fmt.normalizedValue true 7205759403792793 (-1 : ℤ) =
        -((7205759403792793 : ℝ) * (2 : ℝ) ^ (-54 : ℤ)) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  simpa [fmt, hval] using
    (ieeeDoubleFormat_normalizedValue_finiteSystem true hm he)

private theorem ieeeDoubleFormat_5404319552844594_two_pow_neg54_finiteSystem :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem
      ((5404319552844594 : ℝ) * (2 : ℝ) ^ (-54 : ℤ)) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  have hm : fmt.normalizedMantissa 5404319552844594 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (-1 : ℤ) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.exponentInRange]
  have hval :
      fmt.normalizedValue false 5404319552844594 (-1 : ℤ) =
        (5404319552844594 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  simpa [fmt, hval] using
    (ieeeDoubleFormat_normalizedValue_finiteSystem false hm he)

private theorem ieeeDoubleFormat_7205759403792792_two_pow_neg56_finiteSystem :
    FloatingPointFormat.ieeeDoubleFormat.finiteSystem
      ((7205759403792792 : ℝ) * (2 : ℝ) ^ (-56 : ℤ)) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  have hm : fmt.normalizedMantissa 7205759403792792 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have he : fmt.exponentInRange (-3 : ℤ) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.exponentInRange]
  have hval :
      fmt.normalizedValue false 7205759403792792 (-3 : ℤ) =
        (7205759403792792 : ℝ) * (2 : ℝ) ^ (-56 : ℤ) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, zpow_neg]
  simpa [fmt, hval] using
    (ieeeDoubleFormat_normalizedValue_finiteSystem false hm he)

/-- A concrete right-to-left rounded row-sum trace for the first multiplication
by `[1,1,1]^T` after entrywise IEEE-double storage.  This is the same modeled
routine as the left-to-right trace, but it first adds columns `1` and `2`, then
adds column `0`. -/
noncomputable def beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft :
    Fin 3 → ℝ :=
  fun i =>
    let fmt := FloatingPointFormat.ieeeDoubleFormat
    let s12 := fmt.finiteRoundToEvenOp BasicOp.add
      (beneficialPowerMatrixIeeeDoubleRounded i 1)
      (beneficialPowerMatrixIeeeDoubleRounded i 2)
    fmt.finiteRoundToEvenOp BasicOp.add
      (beneficialPowerMatrixIeeeDoubleRounded i 0) s12

private theorem beneficialPowerMatrixIeeeDoubleRounded_rightToLeft_row_zero_first_add_eq :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
        (beneficialPowerMatrixIeeeDoubleRounded 0 1)
        (beneficialPowerMatrixIeeeDoubleRounded 0 2) =
      -((7205759403792793 : ℝ) * (2 : ℝ) ^ (-54 : ℤ)) := by
  unfold beneficialPowerMatrixIeeeDoubleRounded
  simp [beneficialPowerMatrix, ieeeDoubleFormat_neg_three_fifths_rounds_to]
  rw [show ((5 : ℝ)⁻¹) = (1 / 5 : ℝ) by norm_num]
  rw [ieeeDoubleFormat_one_fifth_rounds_to]
  unfold FloatingPointFormat.finiteRoundToEvenOp
  convert
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven_eq_self_of_finiteSystem
      ieeeDoubleFormat_neg_7205759403792793_two_pow_neg54_finiteSystem
    using 1
  all_goals norm_num [BasicOp.exact, zpow_neg]

private theorem beneficialPowerMatrixIeeeDoubleRounded_rightToLeft_row_one_first_add_eq :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
        (beneficialPowerMatrixIeeeDoubleRounded 1 1)
        (beneficialPowerMatrixIeeeDoubleRounded 1 2) =
      (5404319552844594 : ℝ) * (2 : ℝ) ^ (-54 : ℤ) := by
  unfold beneficialPowerMatrixIeeeDoubleRounded
  simp [beneficialPowerMatrix, ieeeDoubleFormat_seven_tenths_rounds_to,
    ieeeDoubleFormat_neg_two_fifths_rounds_to]
  unfold FloatingPointFormat.finiteRoundToEvenOp
  convert
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven_eq_self_of_finiteSystem
      ieeeDoubleFormat_5404319552844594_two_pow_neg54_finiteSystem
    using 1
  all_goals norm_num [BasicOp.exact, zpow_neg]

private theorem beneficialPowerMatrixIeeeDoubleRounded_rightToLeft_row_two_first_add_eq :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
        (beneficialPowerMatrixIeeeDoubleRounded 2 1)
        (beneficialPowerMatrixIeeeDoubleRounded 2 2) =
      (7205759403792792 : ℝ) * (2 : ℝ) ^ (-56 : ℤ) := by
  unfold beneficialPowerMatrixIeeeDoubleRounded
  simp [beneficialPowerMatrix, ieeeDoubleFormat_neg_two_fifths_rounds_to]
  rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num,
    ieeeDoubleFormat_one_half_rounds_to]
  unfold FloatingPointFormat.finiteRoundToEvenOp
  convert
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven_eq_self_of_finiteSystem
      ieeeDoubleFormat_7205759403792792_two_pow_neg56_finiteSystem
    using 1
  all_goals norm_num [BasicOp.exact, zpow_neg]

/-- In the right-to-left rounded-add row-sum trace, the first component agrees
with the entrywise-stored exact row sum `2^-54`. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft_zero_component_eq :
    beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft 0 =
      (1 : ℝ) / (2 : ℝ) ^ 54 := by
  unfold beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft
  change FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
      (beneficialPowerMatrixIeeeDoubleRounded 0 0)
      (FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
        (beneficialPowerMatrixIeeeDoubleRounded 0 1)
        (beneficialPowerMatrixIeeeDoubleRounded 0 2)) =
    (1 : ℝ) / (2 : ℝ) ^ 54
  rw [beneficialPowerMatrixIeeeDoubleRounded_rightToLeft_row_zero_first_add_eq]
  simp [beneficialPowerMatrixIeeeDoubleRounded, beneficialPowerMatrix,
    ieeeDoubleFormat_two_fifths_rounds_to]
  have hfinite :
      FloatingPointFormat.ieeeDoubleFormat.finiteSystem
        (BasicOp.exact BasicOp.add
          ((7205759403792794 : ℝ) * ((2 : ℝ) ^ 54)⁻¹)
          (-((7205759403792793 : ℝ) * ((2 : ℝ) ^ 54)⁻¹))) := by
    convert ieeeDoubleFormat_two_pow_neg54_finiteSystem using 1
    norm_num [BasicOp.exact]
  convert
    FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite
    using 1
  norm_num [BasicOp.exact]

/-- In the right-to-left rounded-add row-sum trace, the second component agrees
with the entrywise-stored exact row sum `-2^-54`. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft_one_component_eq :
    beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft 1 =
      -((1 : ℝ) / (2 : ℝ) ^ 54) := by
  unfold beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft
  change FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
      (beneficialPowerMatrixIeeeDoubleRounded 1 0)
      (FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
        (beneficialPowerMatrixIeeeDoubleRounded 1 1)
        (beneficialPowerMatrixIeeeDoubleRounded 1 2)) =
    -((1 : ℝ) / (2 : ℝ) ^ 54)
  rw [beneficialPowerMatrixIeeeDoubleRounded_rightToLeft_row_one_first_add_eq]
  simp [beneficialPowerMatrixIeeeDoubleRounded, beneficialPowerMatrix,
    ieeeDoubleFormat_neg_three_tenths_rounds_to]
  have hfinite :
      FloatingPointFormat.ieeeDoubleFormat.finiteSystem
        (BasicOp.exact BasicOp.add
          (-((5404319552844595 : ℝ) * ((2 : ℝ) ^ 54)⁻¹))
          ((5404319552844594 : ℝ) * ((2 : ℝ) ^ 54)⁻¹)) := by
    convert
      (FloatingPointFormat.ieeeDoubleFormat.finiteSystem_neg
        ieeeDoubleFormat_two_pow_neg54_finiteSystem) using 1
    norm_num [BasicOp.exact]
  convert
    FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite
    using 1
  norm_num [BasicOp.exact]

/-- In the right-to-left rounded-add row-sum trace, the third component agrees
with the entrywise-stored exact row sum `-2^-55`. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft_two_component_eq :
    beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft 2 =
      -((1 : ℝ) / (2 : ℝ) ^ 55) := by
  unfold beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft
  change FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
      (beneficialPowerMatrixIeeeDoubleRounded 2 0)
      (FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
        (beneficialPowerMatrixIeeeDoubleRounded 2 1)
        (beneficialPowerMatrixIeeeDoubleRounded 2 2)) =
    -((1 : ℝ) / (2 : ℝ) ^ 55)
  rw [beneficialPowerMatrixIeeeDoubleRounded_rightToLeft_row_two_first_add_eq]
  simp [beneficialPowerMatrixIeeeDoubleRounded, beneficialPowerMatrix,
    ieeeDoubleFormat_neg_one_tenth_rounds_to]
  have hfinite :
      FloatingPointFormat.ieeeDoubleFormat.finiteSystem
        (BasicOp.exact BasicOp.add
          (-((7205759403792794 : ℝ) * ((2 : ℝ) ^ 56)⁻¹))
          ((7205759403792792 : ℝ) * ((2 : ℝ) ^ 56)⁻¹)) := by
    convert
      (FloatingPointFormat.ieeeDoubleFormat.finiteSystem_neg
        ieeeDoubleFormat_two_pow_neg55_finiteSystem) using 1
    norm_num [BasicOp.exact]
  convert
    FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite
    using 1
  norm_num [BasicOp.exact]

/-- The right-to-left rounded-add trace recovers the same first-step vector as
the exact entrywise-stored row-sum model.  Together with the left-to-right
caveat, this records the operation-order sensitivity for any optional
machine-model replay; the historical MATLAB printout is not a required
Chapter 1 theorem target. -/
theorem beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft_eq_firstStep :
    beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft =
      beneficialPowerMatrixIeeeDoubleRoundedFirstStep := by
  ext i
  fin_cases i
  · exact beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft_zero_component_eq
  · exact beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft_one_component_eq
  · exact beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft_two_component_eq

/-- The first row of the IEEE-double stored §1.15 matrix has a concrete
nonzero row sum.  This is the source of the first nonzero rounded power-method
component in the displayed example. -/
theorem beneficialPowerMatrixIeeeDoubleRounded_row_zero_sum_eq :
    ∑ j : Fin 3, beneficialPowerMatrixIeeeDoubleRounded 0 j =
      (1 : ℝ) / (2 : ℝ) ^ 54 := by
  rw [Fin.sum_univ_three]
  simp [beneficialPowerMatrixIeeeDoubleRounded, beneficialPowerMatrix,
    ieeeDoubleFormat_two_fifths_rounds_to,
    ieeeDoubleFormat_neg_three_fifths_rounds_to]
  rw [show ((5 : ℝ)⁻¹) = (1 / 5 : ℝ) by norm_num]
  rw [ieeeDoubleFormat_one_fifth_rounds_to]
  norm_num [zpow_neg]

/-- The second row of the IEEE-double stored §1.15 matrix has the opposite
`2^-54` row sum. -/
theorem beneficialPowerMatrixIeeeDoubleRounded_row_one_sum_eq :
    ∑ j : Fin 3, beneficialPowerMatrixIeeeDoubleRounded 1 j =
      -((1 : ℝ) / (2 : ℝ) ^ 54) := by
  rw [Fin.sum_univ_three]
  simp [beneficialPowerMatrixIeeeDoubleRounded, beneficialPowerMatrix,
    ieeeDoubleFormat_neg_three_tenths_rounds_to,
    ieeeDoubleFormat_seven_tenths_rounds_to,
    ieeeDoubleFormat_neg_two_fifths_rounds_to]
  norm_num [zpow_neg]

/-- The third row of the IEEE-double stored §1.15 matrix has row sum
`-2^-55`. -/
theorem beneficialPowerMatrixIeeeDoubleRounded_row_two_sum_eq :
    ∑ j : Fin 3, beneficialPowerMatrixIeeeDoubleRounded 2 j =
      -((1 : ℝ) / (2 : ℝ) ^ 55) := by
  rw [Fin.sum_univ_three]
  simp [beneficialPowerMatrixIeeeDoubleRounded, beneficialPowerMatrix,
    ieeeDoubleFormat_neg_one_tenth_rounds_to,
    ieeeDoubleFormat_neg_two_fifths_rounds_to]
  rw [show ((2 : ℝ)⁻¹) = (1 / 2 : ℝ) by norm_num]
  rw [ieeeDoubleFormat_one_half_rounds_to]
  norm_num [zpow_neg]

/-- The first component of the IEEE-double stored §1.15 power-method step is
exactly `2^-54`, rather than zero. -/
theorem beneficialPowerMatrixIeeeDoubleRounded_firstStep_zero_component_eq :
    powerMethodStep 3 beneficialPowerMatrixIeeeDoubleRounded
        beneficialPowerStart 0 =
      (1 : ℝ) / (2 : ℝ) ^ 54 := by
  calc
    powerMethodStep 3 beneficialPowerMatrixIeeeDoubleRounded
        beneficialPowerStart 0
        = ∑ j : Fin 3, beneficialPowerMatrixIeeeDoubleRounded 0 j := by
          simp [powerMethodStep, matMulVec, beneficialPowerStart]
    _ = (1 : ℝ) / (2 : ℝ) ^ 54 :=
          beneficialPowerMatrixIeeeDoubleRounded_row_zero_sum_eq

/-- The second component of the IEEE-double stored §1.15 power-method step is
exactly `-2^-54`. -/
theorem beneficialPowerMatrixIeeeDoubleRounded_firstStep_one_component_eq :
    powerMethodStep 3 beneficialPowerMatrixIeeeDoubleRounded
        beneficialPowerStart 1 =
      -((1 : ℝ) / (2 : ℝ) ^ 54) := by
  calc
    powerMethodStep 3 beneficialPowerMatrixIeeeDoubleRounded
        beneficialPowerStart 1
        = ∑ j : Fin 3, beneficialPowerMatrixIeeeDoubleRounded 1 j := by
          simp [powerMethodStep, matMulVec, beneficialPowerStart]
    _ = -((1 : ℝ) / (2 : ℝ) ^ 54) :=
          beneficialPowerMatrixIeeeDoubleRounded_row_one_sum_eq

/-- The third component of the IEEE-double stored §1.15 power-method step is
exactly `-2^-55`. -/
theorem beneficialPowerMatrixIeeeDoubleRounded_firstStep_two_component_eq :
    powerMethodStep 3 beneficialPowerMatrixIeeeDoubleRounded
        beneficialPowerStart 2 =
      -((1 : ℝ) / (2 : ℝ) ^ 55) := by
  calc
    powerMethodStep 3 beneficialPowerMatrixIeeeDoubleRounded
        beneficialPowerStart 2
        = ∑ j : Fin 3, beneficialPowerMatrixIeeeDoubleRounded 2 j := by
          simp [powerMethodStep, matMulVec, beneficialPowerStart]
    _ = -((1 : ℝ) / (2 : ℝ) ^ 55) :=
          beneficialPowerMatrixIeeeDoubleRounded_row_two_sum_eq

/-- Full first-step vector produced by entrywise IEEE-double storage of the
displayed §1.15 matrix. -/
theorem beneficialPowerMatrixIeeeDoubleRounded_firstStep_eq :
    powerMethodStep 3 beneficialPowerMatrixIeeeDoubleRounded
        beneficialPowerStart =
      beneficialPowerMatrixIeeeDoubleRoundedFirstStep := by
  ext i
  fin_cases i
  · exact beneficialPowerMatrixIeeeDoubleRounded_firstStep_zero_component_eq
  · exact beneficialPowerMatrixIeeeDoubleRounded_firstStep_one_component_eq
  · exact beneficialPowerMatrixIeeeDoubleRounded_firstStep_two_component_eq

/-- Source-scale certificate for the §1.15 MATLAB sentence that the first
rounded power-method vector has entries of order `10^-16`: every component of
the concrete IEEE-double entrywise-storage first step has magnitude between
`10^-17` and `10^-16`. -/
theorem beneficialPowerMatrixIeeeDoubleRounded_firstStep_abs_between_one_e17_one_e16
    (i : Fin 3) :
    (1 : ℝ) / (10 : ℝ) ^ 17 ≤
        |powerMethodStep 3 beneficialPowerMatrixIeeeDoubleRounded
          beneficialPowerStart i| ∧
      |powerMethodStep 3 beneficialPowerMatrixIeeeDoubleRounded
          beneficialPowerStart i| ≤
        (1 : ℝ) / (10 : ℝ) ^ 16 := by
  rw [beneficialPowerMatrixIeeeDoubleRounded_firstStep_eq]
  fin_cases i <;>
    norm_num [beneficialPowerMatrixIeeeDoubleRoundedFirstStep]

/-- The characteristic matrix `lambda I - A` for the §1.15 power-method
example. -/
noncomputable def beneficialPowerCharMatrix (lambda : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (if i = j then lambda else 0) - beneficialPowerMatrix i j

/-- Every row of the §1.15 matrix sums to zero. -/
theorem beneficialPowerMatrix_row_sum_zero (i : Fin 3) :
    ∑ j : Fin 3, beneficialPowerMatrix i j = 0 := by
  fin_cases i <;> rw [Fin.sum_univ_three] <;> norm_num [beneficialPowerMatrix]

/-- The characteristic determinant of the displayed §1.15 matrix. -/
theorem beneficialPowerCharDet_eq (lambda : ℝ) :
    Matrix.det (beneficialPowerCharMatrix lambda) =
      lambda * (lambda ^ 2 - (8 / 5) * lambda + 51 / 100) := by
  rw [Matrix.det_fin_three]
  simp [beneficialPowerCharMatrix]
  norm_num [beneficialPowerMatrix]
  ring_nf

/-- The zero eigenvalue appears as a root of the characteristic determinant. -/
theorem beneficialPowerCharDet_root_zero :
    Matrix.det (beneficialPowerCharMatrix 0) = 0 := by
  rw [beneficialPowerCharDet_eq]
  ring

/-- The smaller nonzero exact eigenvalue in the §1.15 display. -/
theorem beneficialPowerCharDet_root_small :
    Matrix.det (beneficialPowerCharMatrix (4 / 5 - Real.sqrt 13 / 10)) = 0 := by
  rw [beneficialPowerCharDet_eq]
  have hsq : (Real.sqrt (13 : ℝ)) ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  nlinarith

/-- The dominant exact eigenvalue in the §1.15 display. -/
theorem beneficialPowerCharDet_root_dominant :
    Matrix.det (beneficialPowerCharMatrix (4 / 5 + Real.sqrt 13 / 10)) = 0 := by
  rw [beneficialPowerCharDet_eq]
  have hsq : (Real.sqrt (13 : ℝ)) ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  nlinarith

/-- The smaller nonzero eigenvalue is within one half-unit in the last
displayed decimal place of the source value `0.4394`. -/
theorem beneficialPowerEigenvalueSmall_display_accuracy :
    |(4 / 5 - Real.sqrt 13 / 10 : ℝ) - 4394 / 10000| < 1 / 20000 := by
  have hsqrt_lo : (36055 : ℝ) / 10000 < Real.sqrt 13 :=
    Real.lt_sqrt_of_sq_lt (by norm_num)
  have hsqrt_hi : Real.sqrt 13 < (3606 : ℝ) / 1000 := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  rw [abs_lt]
  constructor <;> nlinarith

/-- The dominant eigenvalue is within one half-unit in the last displayed
decimal place of the source value `1.161`. -/
theorem beneficialPowerEigenvalueDominant_display_accuracy :
    |(4 / 5 + Real.sqrt 13 / 10 : ℝ) - 1161 / 1000| < 1 / 2000 := by
  have hsqrt_lo : (36055 : ℝ) / 10000 < Real.sqrt 13 :=
    Real.lt_sqrt_of_sq_lt (by norm_num)
  have hsqrt_hi : Real.sqrt 13 < (3606 : ℝ) / 1000 := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  rw [abs_lt]
  constructor <;> nlinarith

/-- The displayed starting vector is a right eigenvector for eigenvalue zero. -/
theorem beneficialPowerStart_isRightEigenpair_zero :
    IsRightEigenpair 3 beneficialPowerMatrix 0 beneficialPowerStart := by
  refine ⟨?_, ?_⟩
  · exact ⟨0, by norm_num [beneficialPowerStart]⟩
  · intro i
    calc matMulVec 3 beneficialPowerMatrix beneficialPowerStart i
        = ∑ j : Fin 3, beneficialPowerMatrix i j := by
            unfold matMulVec beneficialPowerStart
            simp
      _ = 0 := beneficialPowerMatrix_row_sum_zero i
      _ = 0 * beneficialPowerStart i := by simp

/-- In exact arithmetic the first unnormalized power-method step is zero. -/
theorem beneficialPowerFirstStep_zero :
    powerMethodStep 3 beneficialPowerMatrix beneficialPowerStart =
      fun _ : Fin 3 => 0 := by
  ext i
  unfold powerMethodStep
  simpa [beneficialPowerStart] using (beneficialPowerStart_isRightEigenpair_zero).2 i

/-- For the displayed zero-eigenvector start, the shifted matrix maps the start
vector to `-mu` times the same vector. -/
theorem beneficialPowerShiftedMatrix_mul_start (mu : ℝ) (i : Fin 3) :
    matMulVec 3 (inverseIterationShiftedMatrix 3 beneficialPowerMatrix mu)
        beneficialPowerStart i =
      (-mu) * beneficialPowerStart i := by
  simpa using
    (inverseIteration_shiftedMatrix_mul_eigenvector
      (n := 3) (A := beneficialPowerMatrix) (lambda := 0) (mu := mu)
      (x := beneficialPowerStart) beneficialPowerStart_isRightEigenpair_zero i)

/-- Concrete exact inverse-iteration shifted solve for the displayed §1.15
start vector and the zero eigenvalue. -/
theorem beneficialPower_inverseIteration_shiftedSystem_solution_start
    {mu : ℝ} (hmu : mu ≠ 0) :
    SolvesInverseIterationShiftedSystem 3 beneficialPowerMatrix mu
      beneficialPowerStart (fun i => (-mu)⁻¹ * beneficialPowerStart i) := by
  have hshift : (0 : ℝ) - mu ≠ 0 := by
    simpa using neg_ne_zero.mpr hmu
  simpa using
    (inverseIteration_shiftedSystem_solution_on_eigenvector
      (n := 3) (A := beneficialPowerMatrix) (lambda := 0) (mu := mu)
      (x := beneficialPowerStart) beneficialPowerStart_isRightEigenpair_zero
      hshift)

/-- Any left inverse of the displayed shifted matrix acts on the displayed start
vector by the exact scalar `(-mu)^{-1}`. -/
theorem beneficialPower_shiftedInverse_mul_start_of_leftInverse
    {mu : ℝ} {B : Fin 3 → Fin 3 → ℝ} (hmu : mu ≠ 0)
    (hB : IsLeftInverse 3
      (inverseIterationShiftedMatrix 3 beneficialPowerMatrix mu) B) :
    matMulVec 3 B beneficialPowerStart =
      fun i => (-mu)⁻¹ * beneficialPowerStart i := by
  have hshift : (0 : ℝ) - mu ≠ 0 := by
    simpa using neg_ne_zero.mpr hmu
  simpa using
    (inverseIteration_shiftedInverse_mul_eigenvector_of_leftInverse
      (n := 3) (A := beneficialPowerMatrix) (B := B)
      (lambda := 0) (mu := mu) (x := beneficialPowerStart)
      beneficialPowerStart_isRightEigenpair_zero hshift hB)

/-- Displayed §1.15 near-parallel inverse-iteration bridge: for Higham's
matrix and start vector, the eigen-residual of the shifted inverse-iteration
output depends only on the nonparallel residual component. -/
theorem beneficialPower_inverseIteration_near_parallel_error_eigenResidual_eq
    {mu eta : ℝ} {err r : Fin 3 → ℝ}
    (herr : err = fun i => eta * beneficialPowerStart i + r i) :
    eigenResidualVec 3 beneficialPowerMatrix 0
        (fun i => (-mu)⁻¹ * beneficialPowerStart i + err i) =
      eigenResidualVec 3 beneficialPowerMatrix 0 r := by
  simpa using
    (inverseIteration_near_parallel_error_eigenResidual_eq
      (n := 3) (A := beneficialPowerMatrix) (lambda := 0) (mu := mu)
      (x := beneficialPowerStart) (err := err) (r := r)
      beneficialPowerStart_isRightEigenpair_zero eta herr)

/-- Displayed §1.15 quantitative near-parallel bridge: for Higham's matrix and
start vector, only the nonparallel residual component contributes to the
eigen-residual norm. -/
theorem beneficialPower_inverseIteration_near_parallel_error_eigenResidual_norm_le
    {mu eta A_norm : ℝ} {err r : Fin 3 → ℝ}
    (herr : err = fun i => eta * beneficialPowerStart i + r i)
    (hA : opNorm2Le beneficialPowerMatrix A_norm) :
    vecNorm2
        (eigenResidualVec 3 beneficialPowerMatrix 0
          (fun i => (-mu)⁻¹ * beneficialPowerStart i + err i)) ≤
      A_norm * vecNorm2 r := by
  simpa using
    (inverseIteration_near_parallel_error_eigenResidual_norm_le
      (n := 3) (A := beneficialPowerMatrix) (lambda := 0) (mu := mu)
      (A_norm := A_norm) (x := beneficialPowerStart) (err := err) (r := r)
      beneficialPowerStart_isRightEigenpair_zero eta herr hA)

/-- Residual-budget form of the displayed §1.15 near-parallel bridge. -/
theorem beneficialPower_inverseIteration_near_parallel_error_eigenResidual_norm_le_of_residual_norm_le
    {mu eta A_norm eps : ℝ} {err r : Fin 3 → ℝ}
    (herr : err = fun i => eta * beneficialPowerStart i + r i)
    (hA : opNorm2Le beneficialPowerMatrix A_norm) (hA_nonneg : 0 ≤ A_norm)
    (hr : vecNorm2 r ≤ eps) :
    vecNorm2
        (eigenResidualVec 3 beneficialPowerMatrix 0
          (fun i => (-mu)⁻¹ * beneficialPowerStart i + err i)) ≤
      A_norm * eps := by
  exact le_trans
    (beneficialPower_inverseIteration_near_parallel_error_eigenResidual_norm_le
      (mu := mu) (eta := eta) (A_norm := A_norm) (err := err) (r := r)
      herr hA)
    (mul_le_mul_of_nonneg_left hr hA_nonneg)

/-- Componentwise near-parallel certificate for the displayed §1.15 inverse
iteration example.  If every shifted-solve error component is within `eps` of
one common scalar `eta`, then the error splits into a harmless multiple of the
displayed eigenvector plus a residual of norm at most `sqrt 3 * eps`, and the
existing near-parallel residual bound applies. -/
theorem
    beneficialPower_inverseIteration_near_parallel_error_eigenResidual_norm_le_of_componentwise_common_scalar
    {mu eta A_norm eps : ℝ} {err : Fin 3 → ℝ}
    (hA : opNorm2Le beneficialPowerMatrix A_norm) (hA_nonneg : 0 ≤ A_norm)
    (heps_nonneg : 0 ≤ eps)
    (herr : ∀ i : Fin 3, |err i - eta| ≤ eps) :
    vecNorm2
        (eigenResidualVec 3 beneficialPowerMatrix 0
          (fun i => (-mu)⁻¹ * beneficialPowerStart i + err i)) ≤
      A_norm * (Real.sqrt (3 : ℝ) * eps) := by
  let r : Fin 3 → ℝ := fun i => err i - eta * beneficialPowerStart i
  have hdecomp : err = fun i => eta * beneficialPowerStart i + r i := by
    ext i
    dsimp [r]
    ring
  have hr_abs : ∀ i : Fin 3, |r i| ≤ eps := by
    intro i
    simpa [r, beneficialPowerStart] using herr i
  have hr_norm : vecNorm2 r ≤ Real.sqrt (3 : ℝ) * eps := by
    simpa using
      (vecNorm2_le_sqrt_card_mul_of_abs_le (n := 3) r heps_nonneg hr_abs)
  exact
    beneficialPower_inverseIteration_near_parallel_error_eigenResidual_norm_le_of_residual_norm_le
      (mu := mu) (eta := eta) (A_norm := A_norm)
      (eps := Real.sqrt (3 : ℝ) * eps) (err := err) (r := r)
      hdecomp hA hA_nonneg hr_norm

/-- A first power-method step with a perturbed stored matrix splits into the
exact step plus the perturbation action. -/
theorem powerMethodStep_add_matrix (n : ℕ) (A ΔA : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) :
    powerMethodStep n (fun i j => A i j + ΔA i j) x =
      fun i => powerMethodStep n A x i + matMulVec n ΔA x i := by
  ext i
  unfold powerMethodStep matMulVec
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- For the displayed example, the first step with a stored perturbation is
exactly the action of the perturbation on `[1,1,1]^T`. -/
theorem beneficialPowerFirstStep_perturbed_eq_delta
    (ΔA : Fin 3 → Fin 3 → ℝ) :
    powerMethodStep 3 (fun i j => beneficialPowerMatrix i j + ΔA i j)
        beneficialPowerStart =
      matMulVec 3 ΔA beneficialPowerStart := by
  rw [powerMethodStep_add_matrix]
  ext i
  rw [beneficialPowerFirstStep_zero]
  simp

/-- Exact zero-characterization for the displayed §1.15 perturbed first
power-method step: row sums of the stored perturbation are the whole
first-step obstruction. -/
theorem beneficialPowerFirstStep_perturbed_eq_zero_iff_row_sums_zero
    (ΔA : Fin 3 → Fin 3 → ℝ) :
    powerMethodStep 3 (fun i j => beneficialPowerMatrix i j + ΔA i j)
        beneficialPowerStart = (fun _ => 0) ↔
      ∀ i : Fin 3, ∑ j : Fin 3, ΔA i j = 0 := by
  rw [beneficialPowerFirstStep_perturbed_eq_delta]
  constructor
  · intro h i
    have hi := congrFun h i
    simpa [matMulVec, beneficialPowerStart] using hi
  · intro h
    funext i
    simpa [matMulVec, beneficialPowerStart] using h i

/-- If the stored perturbation has a nonzero row sum, then the first perturbed
power-method step is nonzero in that component. -/
theorem beneficialPowerFirstStep_perturbed_nonzero_of_delta_row_sum_ne_zero
    (ΔA : Fin 3 → Fin 3 → ℝ) {i : Fin 3}
    (hi : (∑ j : Fin 3, ΔA i j) ≠ 0) :
    ∃ i : Fin 3,
      powerMethodStep 3 (fun i j => beneficialPowerMatrix i j + ΔA i j)
        beneficialPowerStart i ≠ 0 := by
  refine ⟨i, ?_⟩
  rw [beneficialPowerFirstStep_perturbed_eq_delta]
  simpa [matMulVec, beneficialPowerStart] using hi

/-- A vector with a nonzero component has positive Euclidean norm. -/
theorem vecNorm2_pos_of_exists_ne {n : ℕ} {x : Fin n → ℝ}
    (h : ∃ i : Fin n, x i ≠ 0) :
    0 < vecNorm2 x := by
  have hnonneg : 0 ≤ vecNorm2 x := vecNorm2_nonneg x
  exact lt_of_le_of_ne hnonneg (by
    intro hzero
    rcases h with ⟨i, hi⟩
    exact hi ((vecNorm2_eq_zero_iff x).mp hzero.symm i))

/-- The IEEE-double stored §1.15 matrix restarts the first power-method step:
the first-step vector has positive Euclidean norm because its first component
is exactly `2^-54`. -/
theorem beneficialPowerMatrixIeeeDoubleRounded_firstStep_vecNorm2_pos :
    0 < vecNorm2
      (powerMethodStep 3 beneficialPowerMatrixIeeeDoubleRounded
        beneficialPowerStart) := by
  exact vecNorm2_pos_of_exists_ne
    ⟨0, by
      rw [beneficialPowerMatrixIeeeDoubleRounded_firstStep_zero_component_eq]
      positivity⟩

/-- Concrete lower bound for the IEEE-double stored §1.15 first-step norm. -/
theorem beneficialPowerMatrixIeeeDoubleRounded_firstStep_vecNorm2_ge_two_pow_neg54 :
    (1 : ℝ) / (2 : ℝ) ^ 54 ≤
      vecNorm2
        (powerMethodStep 3 beneficialPowerMatrixIeeeDoubleRounded
          beneficialPowerStart) := by
  have hcoord :=
    abs_coord_le_vecNorm2
      (powerMethodStep 3 beneficialPowerMatrixIeeeDoubleRounded
        beneficialPowerStart) 0
  have hcomponent :
      |powerMethodStep 3 beneficialPowerMatrixIeeeDoubleRounded
          beneficialPowerStart 0| =
        (1 : ℝ) / (2 : ℝ) ^ 54 := by
    rw [beneficialPowerMatrixIeeeDoubleRounded_firstStep_zero_component_eq]
    exact abs_of_pos (by positivity)
  simpa [hcomponent] using hcoord

/-- Norm-level version of the §1.15 perturbation restart: if the stored
matrix perturbation has a nonzero row sum, then the first perturbed power
method step is not merely componentwise nonzero; it has positive Euclidean
norm. -/
theorem beneficialPowerFirstStep_perturbed_vecNorm2_pos_of_delta_row_sum_ne_zero
    (ΔA : Fin 3 → Fin 3 → ℝ) {i : Fin 3}
    (hi : (∑ j : Fin 3, ΔA i j) ≠ 0) :
    0 < vecNorm2
      (powerMethodStep 3 (fun i j => beneficialPowerMatrix i j + ΔA i j)
        beneficialPowerStart) := by
  exact vecNorm2_pos_of_exists_ne
    (beneficialPowerFirstStep_perturbed_nonzero_of_delta_row_sum_ne_zero
      ΔA hi)

/-- Norm-level zero-characterization for the displayed §1.15 perturbed first
step.  The Euclidean norm of the first perturbed vector vanishes exactly when
every stored-perturbation row sum vanishes. -/
theorem beneficialPowerFirstStep_perturbed_vecNorm2_eq_zero_iff_row_sums_zero
    (ΔA : Fin 3 → Fin 3 → ℝ) :
    vecNorm2
      (powerMethodStep 3 (fun i j => beneficialPowerMatrix i j + ΔA i j)
        beneficialPowerStart) = 0 ↔
      ∀ i : Fin 3, ∑ j : Fin 3, ΔA i j = 0 := by
  constructor
  · intro hnorm i
    rw [beneficialPowerFirstStep_perturbed_eq_delta] at hnorm
    have hzero :
        matMulVec 3 ΔA beneficialPowerStart i = 0 :=
      (vecNorm2_eq_zero_iff _).mp hnorm i
    simpa [matMulVec, beneficialPowerStart] using hzero
  · intro hrow
    apply (vecNorm2_eq_zero_iff _).mpr
    intro i
    rw [beneficialPowerFirstStep_perturbed_eq_delta]
    simpa [matMulVec, beneficialPowerStart] using hrow i

/-- Lower-bound certificate for the displayed §1.15 perturbed first step:
any row-sum magnitude of the stored perturbation is bounded above by the
Euclidean norm of the first perturbed power-method vector. -/
theorem beneficialPowerFirstStep_perturbed_vecNorm2_ge_of_row_sum_abs_ge
    (ΔA : Fin 3 → Fin 3 → ℝ) {i : Fin 3} {rho : ℝ}
    (hi : rho ≤ |∑ j : Fin 3, ΔA i j|) :
    rho ≤ vecNorm2
      (powerMethodStep 3 (fun i j => beneficialPowerMatrix i j + ΔA i j)
        beneficialPowerStart) := by
  rw [beneficialPowerFirstStep_perturbed_eq_delta]
  exact hi.trans (by
    simpa [matMulVec, beneficialPowerStart] using
      (abs_coord_le_vecNorm2 (matMulVec 3 ΔA beneficialPowerStart) i))

/-- Row-sum perturbation budget for the displayed §1.15 first power-method
step.  If every stored-perturbation row sum is bounded by `eps`, then the
first perturbed vector has Euclidean norm at most `sqrt 3 * eps`. -/
theorem beneficialPowerFirstStep_perturbed_vecNorm2_le_of_row_sum_abs_le
    (ΔA : Fin 3 → Fin 3 → ℝ) {eps : ℝ}
    (heps_nonneg : 0 ≤ eps)
    (hrow : ∀ i : Fin 3, |∑ j : Fin 3, ΔA i j| ≤ eps) :
    vecNorm2
      (powerMethodStep 3 (fun i j => beneficialPowerMatrix i j + ΔA i j)
        beneficialPowerStart) ≤ Real.sqrt (3 : ℝ) * eps := by
  rw [beneficialPowerFirstStep_perturbed_eq_delta]
  exact
    vecNorm2_le_sqrt_card_mul_of_abs_le
      (n := 3) (fun i => matMulVec 3 ΔA beneficialPowerStart i)
      heps_nonneg (by
        intro i
        simpa [matMulVec, beneficialPowerStart] using hrow i)

/-- Entrywise perturbation budget for the displayed §1.15 first power-method
step.  A uniform entrywise perturbation radius `eps` bounds each row sum by
`3*eps`, hence bounds the first perturbed vector by `sqrt 3 * (3*eps)`. -/
theorem beneficialPowerFirstStep_perturbed_vecNorm2_le_of_entry_abs_le
    (ΔA : Fin 3 → Fin 3 → ℝ) {eps : ℝ}
    (heps_nonneg : 0 ≤ eps)
    (hentry : ∀ i j : Fin 3, |ΔA i j| ≤ eps) :
    vecNorm2
      (powerMethodStep 3 (fun i j => beneficialPowerMatrix i j + ΔA i j)
        beneficialPowerStart) ≤ Real.sqrt (3 : ℝ) * (3 * eps) := by
  have hrow : ∀ i : Fin 3, |∑ j : Fin 3, ΔA i j| ≤ 3 * eps := by
    intro i
    calc
      |∑ j : Fin 3, ΔA i j| ≤ ∑ j : Fin 3, |ΔA i j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin 3, eps := by
        apply Finset.sum_le_sum
        intro j _hj
        exact hentry i j
      _ = 3 * eps := by
        simp
  exact
    beneficialPowerFirstStep_perturbed_vecNorm2_le_of_row_sum_abs_le
      ΔA (by nlinarith) hrow

/-- Concrete stored-matrix instance of the §1.15 entrywise perturbation budget:
the first power-method vector for the entrywise IEEE-double stored matrix has
Euclidean norm at most `sqrt 3 * (3 * 2^-53)` by the uniform stored-entry
perturbation radius. -/
theorem beneficialPowerMatrixIeeeDoubleRounded_firstStep_vecNorm2_le_sqrt_three_mul_three_two_pow_neg53 :
    vecNorm2
      (powerMethodStep 3 beneficialPowerMatrixIeeeDoubleRounded
        beneficialPowerStart) ≤
      Real.sqrt (3 : ℝ) * (3 * ((1 : ℝ) / (2 : ℝ) ^ 53)) := by
  have h :=
    beneficialPowerFirstStep_perturbed_vecNorm2_le_of_entry_abs_le
      (fun i j : Fin 3 =>
        beneficialPowerMatrixIeeeDoubleRounded i j - beneficialPowerMatrix i j)
      (eps := (1 : ℝ) / (2 : ℝ) ^ 53)
      (by norm_num)
      beneficialPowerMatrixIeeeDoubleRounded_entrywise_abs_error_le_two_pow_neg53
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

end NumStability
