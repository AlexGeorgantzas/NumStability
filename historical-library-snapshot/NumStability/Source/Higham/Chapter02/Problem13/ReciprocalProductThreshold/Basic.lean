import Mathlib.Data.Nat.Factorization.Basic
import NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError

/-!
# Chapter02 Problem13 ReciprocalProductThreshold Basic

Canonical destination for material split out of
`NumStability.Analysis.Problem2_13` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

namespace FloatingPointFormat

def problem2_13_candidateJ : ℕ := 257736490

def problem2_13_candidateX : ℝ :=
  (1 : ℝ) + (problem2_13_candidateJ : ℝ) * (2 : ℝ) ^ (-52 : ℤ)

def problem2_13_predecessorJ : ℕ := 257736489

def problem2_13_predecessorX : ℝ :=
  (1 : ℝ) + (problem2_13_predecessorJ : ℝ) * (2 : ℝ) ^ (-52 : ℤ)

/-- Source family for Problem 2.13: `x_j = 1 + j*eps` with
`eps = 2^-52`. -/
def problem2_13_sourceX (j : ℕ) : ℝ :=
  (1 : ℝ) + (j : ℝ) * (2 : ℝ) ^ (-52 : ℤ)

/-- Exact product formed after the rounded reciprocal in Problem 2.13's
source-family computation. -/
def problem2_13_sourceProduct (j : ℕ) : ℝ :=
  problem2_13_sourceX j *
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
      (1 : ℝ) (problem2_13_sourceX j)

def problem2_13_reciprocalCellQuotient (j : ℕ) : ℕ :=
  (2 ^ 105 : ℕ) / (2 ^ 52 + j)

def problem2_13_quadraticRemainderQuotient (j : ℕ) : ℕ :=
  (2 * j * j) / (2 ^ 52 + j)

theorem problem2_13_quadraticRemainderQuotient_le_29_of_lt_candidateJ
    {j : ℕ} (hj : j < problem2_13_candidateJ) :
    problem2_13_quadraticRemainderQuotient j ≤ 29 := by
  rw [problem2_13_quadraticRemainderQuotient]
  have hnpos : 0 < 2 ^ 52 + j := by
    positivity
  have hlt : (2 * j * j) / (2 ^ 52 + j) < 30 := by
    exact (Nat.div_lt_iff_lt_mul hnpos).2 (by
      have hj' : j < 257736490 := by
        simpa [problem2_13_candidateJ] using hj
      norm_num at hj' ⊢
      nlinarith)
  omega

theorem
    problem2_13_reciprocalCellQuotient_remainder_eq_quadratic_remainder_of_lt_candidateJ
    {j : ℕ} (hj : j < problem2_13_candidateJ) :
    (2 ^ 105 : ℕ) % (2 ^ 52 + j) = (2 * j * j) % (2 ^ 52 + j) := by
  have hA :
      (2 ^ 105 : ℕ) = (2 * j * j) + (2 ^ 53 - 2 * j) * (2 ^ 52 + j) := by
    have hj' : j < 257736490 := by
      simpa [problem2_13_candidateJ] using hj
    have hjB : 2 * j ≤ 2 ^ 53 := by
      norm_num at hj' ⊢
      omega
    nlinarith [Nat.sub_add_cancel hjB]
  rw [hA]
  simp [Nat.add_mul_mod_self_left, Nat.mul_comm]

theorem problem2_13_reciprocalCellQuotient_normalizedMantissas_of_pos_lt_candidateJ
    {j : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ) :
    ieeeDoubleFormat.normalizedMantissa
        (problem2_13_reciprocalCellQuotient j) ∧
      ieeeDoubleFormat.normalizedMantissa
        (problem2_13_reciprocalCellQuotient j + 1) := by
  have hnpos : 0 < 2 ^ 52 + j := by
    positivity
  have hqlo : 2 ^ 52 ≤ problem2_13_reciprocalCellQuotient j := by
    rw [problem2_13_reciprocalCellQuotient]
    exact (Nat.le_div_iff_mul_le hnpos).2 (by
      have hj' : j < 257736490 := by
        simpa [problem2_13_candidateJ] using hj
      norm_num at hj' ⊢
      omega)
  have hqsucc_hi : problem2_13_reciprocalCellQuotient j + 1 < 2 ^ 53 := by
    rw [problem2_13_reciprocalCellQuotient]
    have hq_lt : (2 ^ 105 : ℕ) / (2 ^ 52 + j) < 2 ^ 53 - 1 := by
      exact (Nat.div_lt_iff_lt_mul hnpos).2 (by
        norm_num at hjpos ⊢
        omega)
    omega
  have hqhi : problem2_13_reciprocalCellQuotient j < 2 ^ 53 := by
    omega
  constructor
  · constructor
    · simpa [ieeeDoubleFormat, minNormalMantissa] using hqlo
    · simpa [ieeeDoubleFormat, mantissaInRange] using hqhi
  · constructor
    · have : 2 ^ 52 ≤ problem2_13_reciprocalCellQuotient j + 1 := by
        omega
      simpa [ieeeDoubleFormat, minNormalMantissa] using this
    · simpa [ieeeDoubleFormat, mantissaInRange] using hqsucc_hi

theorem problem2_13_sourceX_eq_scaled (j : ℕ) :
    problem2_13_sourceX j =
      ((2 ^ 52 + j : ℕ) : ℝ) * (2 : ℝ) ^ (-52 : ℤ) := by
  unfold problem2_13_sourceX
  norm_num [zpow_neg]
  ring

theorem problem2_13_sourceX_candidateJ :
    problem2_13_sourceX problem2_13_candidateJ =
      problem2_13_candidateX := rfl

theorem problem2_13_sourceX_predecessorJ :
    problem2_13_sourceX problem2_13_predecessorJ =
      problem2_13_predecessorX := rfl

theorem problem2_13_predecessorJ_succ_eq_candidateJ :
    problem2_13_predecessorJ + 1 = problem2_13_candidateJ := by
  norm_num [problem2_13_predecessorJ, problem2_13_candidateJ]

theorem problem2_13_candidateX_sub_predecessorX_eq_ulp :
    problem2_13_candidateX - problem2_13_predecessorX =
      (2 : ℝ) ^ (-52 : ℤ) := by
  norm_num [problem2_13_candidateX, problem2_13_predecessorX,
    problem2_13_candidateJ, problem2_13_predecessorJ, zpow_neg]

theorem problem2_13_predecessorX_add_ulp_eq_candidateX :
    problem2_13_predecessorX + (2 : ℝ) ^ (-52 : ℤ) =
      problem2_13_candidateX := by
  norm_num [problem2_13_candidateX, problem2_13_predecessorX,
    problem2_13_candidateJ, problem2_13_predecessorJ, zpow_neg]

theorem problem2_13_sourceX_le_sourceX {j k : ℕ} (hjk : j ≤ k) :
    problem2_13_sourceX j ≤ problem2_13_sourceX k := by
  have hcast : (j : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hjk
  have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (-52 : ℤ) := by
    positivity
  unfold problem2_13_sourceX
  have hmul := mul_le_mul_of_nonneg_right hcast hpow_nonneg
  linarith

theorem problem2_13_sourceX_le_predecessorX_of_lt_candidateJ {j : ℕ}
    (hj : j < problem2_13_candidateJ) :
    problem2_13_sourceX j ≤ problem2_13_predecessorX := by
  have hsucc :
      problem2_13_candidateJ = problem2_13_predecessorJ + 1 := by
    rw [← problem2_13_predecessorJ_succ_eq_candidateJ]
  rw [hsucc] at hj
  have hjpred : j ≤ problem2_13_predecessorJ := Nat.lt_succ_iff.mp hj
  have hmono := problem2_13_sourceX_le_sourceX hjpred
  simpa [problem2_13_sourceX_predecessorJ] using hmono

theorem problem2_13_sourceX_lt_candidateX_of_lt_candidateJ {j : ℕ}
    (hj : j < problem2_13_candidateJ) :
    problem2_13_sourceX j < problem2_13_candidateX := by
  have hle := problem2_13_sourceX_le_predecessorX_of_lt_candidateJ hj
  have hlt : problem2_13_predecessorX < problem2_13_candidateX := by
    norm_num [problem2_13_predecessorX, problem2_13_candidateX,
      problem2_13_predecessorJ, problem2_13_candidateJ, zpow_neg]
  exact lt_of_le_of_lt hle hlt

theorem problem2_13_sourceX_finiteSystem_of_lt_two_pow_52 {j : ℕ}
    (hj : j < 2 ^ 52) :
    ieeeDoubleFormat.finiteSystem (problem2_13_sourceX j) := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 2 ^ 52 + j, (1 : ℤ), ?_, ?_, ?_⟩
  · constructor
    · norm_num [ieeeDoubleFormat, minNormalMantissa]
    · have hj' : j < 4503599627370496 := by
        simpa using hj
      norm_num [ieeeDoubleFormat, mantissaInRange]
      omega
  · norm_num [ieeeDoubleFormat, exponentInRange]
  · unfold problem2_13_sourceX
    norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR, zpow_neg]
    ring

theorem problem2_13_sourceX_finiteSystem_of_lt_candidateJ {j : ℕ}
    (hj : j < problem2_13_candidateJ) :
    ieeeDoubleFormat.finiteSystem (problem2_13_sourceX j) := by
  exact problem2_13_sourceX_finiteSystem_of_lt_two_pow_52 (by
    have hj' : j < 257736490 := by
      simpa [problem2_13_candidateJ] using hj
    norm_num
    omega)

theorem problem2_13_candidateX_eq_scaled :
    problem2_13_candidateX =
      (4503599885106986 : ℝ) * (2 : ℝ) ^ (-52 : ℤ) := by
  norm_num [problem2_13_candidateX, problem2_13_candidateJ, zpow_neg]

theorem problem2_13_candidateX_finiteSystem :
    ieeeDoubleFormat.finiteSystem problem2_13_candidateX := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 4503599885106986, (1 : ℤ), ?_, ?_, ?_⟩
  · norm_num [ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  · norm_num [ieeeDoubleFormat, exponentInRange]
  · rw [problem2_13_candidateX_eq_scaled]
    norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR, zpow_neg]

theorem problem2_13_candidateX_between_one_two :
    (1 : ℝ) < problem2_13_candidateX ∧
      problem2_13_candidateX < (2 : ℝ) := by
  norm_num [problem2_13_candidateX, problem2_13_candidateJ, zpow_neg]

theorem problem2_13_sourceX_between_one_two_of_pos_lt_candidateJ {j : ℕ}
    (hjpos : 0 < j) (hj : j < problem2_13_candidateJ) :
    (1 : ℝ) < problem2_13_sourceX j ∧
      problem2_13_sourceX j < (2 : ℝ) := by
  constructor
  · unfold problem2_13_sourceX
    have hjpos_real : (0 : ℝ) < (j : ℝ) := by
      exact_mod_cast hjpos
    have hpow_pos : 0 < (2 : ℝ) ^ (-52 : ℤ) := by
      positivity
    nlinarith [mul_pos hjpos_real hpow_pos]
  · exact lt_trans (problem2_13_sourceX_lt_candidateX_of_lt_candidateJ hj)
      problem2_13_candidateX_between_one_two.2

theorem problem2_13_sourceX_reciprocal_strict_between_of_scaled_interval
    {j k : ℕ}
    (hlo :
      (k : ℝ) * ((2 ^ 52 + j : ℕ) : ℝ) < (2 : ℝ) ^ (105 : ℕ))
    (hhi :
      (2 : ℝ) ^ (105 : ℕ) <
        ((k + 1 : ℕ) : ℝ) * ((2 ^ 52 + j : ℕ) : ℝ)) :
    (k : ℝ) * (2 : ℝ) ^ (-53 : ℤ) <
        (1 : ℝ) / problem2_13_sourceX j ∧
      (1 : ℝ) / problem2_13_sourceX j <
        ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
  let n : ℝ := ((2 ^ 52 + j : ℕ) : ℝ)
  have hnpos : 0 < n := by
    positivity
  have hsource :
      problem2_13_sourceX j = n * (2 : ℝ) ^ (-52 : ℤ) := by
    simpa [n] using problem2_13_sourceX_eq_scaled j
  have hrecip :
      (1 : ℝ) / problem2_13_sourceX j = (2 : ℝ) ^ (52 : ℕ) / n := by
    rw [hsource]
    field_simp [hnpos.ne']
  constructor
  · have hdiv : (k : ℝ) < (2 : ℝ) ^ (105 : ℕ) / n := by
      exact (lt_div_iff₀ hnpos).2 (by simpa [n] using hlo)
    have hscaled :
        (k : ℝ) / (2 : ℝ) ^ (53 : ℕ) <
          ((2 : ℝ) ^ (105 : ℕ) / n) / (2 : ℝ) ^ (53 : ℕ) := by
      exact div_lt_div_of_pos_right hdiv (by positivity)
    rw [hrecip]
    calc
      (k : ℝ) * (2 : ℝ) ^ (-53 : ℤ)
          = (k : ℝ) / (2 : ℝ) ^ (53 : ℕ) := by
            rw [zpow_neg, div_eq_mul_inv]
            rfl
      _ < ((2 : ℝ) ^ (105 : ℕ) / n) / (2 : ℝ) ^ (53 : ℕ) := hscaled
      _ = (2 : ℝ) ^ (52 : ℕ) / n := by
            field_simp [hnpos.ne']
  · have hdiv : (2 : ℝ) ^ (105 : ℕ) / n < ((k + 1 : ℕ) : ℝ) := by
      exact (div_lt_iff₀ hnpos).2 (by simpa [n] using hhi)
    have hscaled :
        ((2 : ℝ) ^ (105 : ℕ) / n) / (2 : ℝ) ^ (53 : ℕ) <
          ((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (53 : ℕ) := by
      exact div_lt_div_of_pos_right hdiv (by positivity)
    rw [hrecip]
    calc
      (2 : ℝ) ^ (52 : ℕ) / n
          = ((2 : ℝ) ^ (105 : ℕ) / n) / (2 : ℝ) ^ (53 : ℕ) := by
            field_simp [hnpos.ne']
      _ < ((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (53 : ℕ) := hscaled
      _ = ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
            rw [zpow_neg, div_eq_mul_inv]
            rfl

theorem problem2_13_sourceX_reciprocal_strict_between_of_nat_scaled_interval
    {j k : ℕ}
    (hlo : k * (2 ^ 52 + j) < (2 ^ 105 : ℕ))
    (hhi : (2 ^ 105 : ℕ) < (k + 1) * (2 ^ 52 + j)) :
    (k : ℝ) * (2 : ℝ) ^ (-53 : ℤ) <
        (1 : ℝ) / problem2_13_sourceX j ∧
      (1 : ℝ) / problem2_13_sourceX j <
        ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
  refine problem2_13_sourceX_reciprocal_strict_between_of_scaled_interval
    (j := j) (k := k) ?_ ?_
  · have hloR :
        (((k * (2 ^ 52 + j) : ℕ) : ℝ) < ((2 ^ 105 : ℕ) : ℝ)) := by
      exact_mod_cast hlo
    norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_pow] at hloR ⊢
    exact hloR
  · have hhiR :
        (((2 ^ 105 : ℕ) : ℝ) <
          (((k + 1) * (2 ^ 52 + j) : ℕ) : ℝ)) := by
      exact_mod_cast hhi
    norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_pow] at hhiR ⊢
    exact hhiR

theorem problem2_13_reciprocalCellQuotient_nat_scaled_interval
    {j : ℕ}
    (hrem : (2 ^ 105 : ℕ) % (2 ^ 52 + j) ≠ 0) :
    problem2_13_reciprocalCellQuotient j * (2 ^ 52 + j) <
        (2 ^ 105 : ℕ) ∧
      (2 ^ 105 : ℕ) <
        (problem2_13_reciprocalCellQuotient j + 1) * (2 ^ 52 + j) := by
  let n := 2 ^ 52 + j
  let a := (2 ^ 105 : ℕ)
  have hnpos : 0 < n := by
    positivity
  have hle : a / n * n ≤ a := Nat.div_mul_le_self a n
  have hlt_lower : a / n * n < a := by
    exact Nat.lt_of_le_of_ne hle (by
      intro heq
      have hdivmod : n * (a / n) + a % n = a := Nat.div_add_mod a n
      have heq' : n * (a / n) = a := by
        simpa [Nat.mul_comm] using heq
      have hmod_zero : a % n = 0 := by
        omega
      exact hrem (by simpa [a, n] using hmod_zero))
  have hlt_upper : a < (a / n + 1) * n := by
    exact Nat.lt_mul_of_div_lt (Nat.lt_succ_self (a / n)) hnpos
  simpa [problem2_13_reciprocalCellQuotient, a, n] using
    And.intro hlt_lower hlt_upper

theorem problem2_13_sourceX_reciprocal_strict_between_of_quotient_remainder
    {j : ℕ}
    (hrem : (2 ^ 105 : ℕ) % (2 ^ 52 + j) ≠ 0) :
    (problem2_13_reciprocalCellQuotient j : ℝ) *
        (2 : ℝ) ^ (-53 : ℤ) <
        (1 : ℝ) / problem2_13_sourceX j ∧
      (1 : ℝ) / problem2_13_sourceX j <
        ((problem2_13_reciprocalCellQuotient j + 1 : ℕ) : ℝ) *
          (2 : ℝ) ^ (-53 : ℤ) := by
  rcases problem2_13_reciprocalCellQuotient_nat_scaled_interval
      (j := j) hrem with ⟨hlo, hhi⟩
  exact
    problem2_13_sourceX_reciprocal_strict_between_of_nat_scaled_interval
      (j := j) (k := problem2_13_reciprocalCellQuotient j) hlo hhi

theorem problem2_13_sourceX_reciprocal_left_closer_of_scaled_midpoint
    {j k : ℕ}
    (hstrict :
      (k : ℝ) * (2 : ℝ) ^ (-53 : ℤ) <
          (1 : ℝ) / problem2_13_sourceX j ∧
        (1 : ℝ) / problem2_13_sourceX j <
          ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-53 : ℤ))
    (hmid : (2 ^ 106 : ℕ) < (2 * k + 1) * (2 ^ 52 + j)) :
    |(1 : ℝ) / problem2_13_sourceX j -
        (k : ℝ) * (2 : ℝ) ^ (-53 : ℤ)| <
      |(1 : ℝ) / problem2_13_sourceX j -
        ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-53 : ℤ)| := by
  let n : ℝ := ((2 ^ 52 + j : ℕ) : ℝ)
  have hnpos : 0 < n := by
    positivity
  have hsource :
      problem2_13_sourceX j = n * (2 : ℝ) ^ (-52 : ℤ) := by
    simpa [n] using problem2_13_sourceX_eq_scaled j
  have hrecip :
      (1 : ℝ) / problem2_13_sourceX j = (2 : ℝ) ^ (52 : ℕ) / n := by
    rw [hsource]
    field_simp [hnpos.ne']
  have hmidR :
      (((2 ^ 106 : ℕ) : ℝ) <
        (((2 * k + 1) * (2 ^ 52 + j) : ℕ) : ℝ)) := by
    exact_mod_cast hmid
  have hmidR2 :
      (2 : ℝ) ^ (106 : ℕ) < (2 * (k : ℝ) + 1) * n := by
    norm_num [n, Nat.cast_mul, Nat.cast_add, Nat.cast_pow] at hmidR ⊢
    exact hmidR
  have hx_left_nonneg :
      0 ≤ (1 : ℝ) / problem2_13_sourceX j -
        (k : ℝ) * (2 : ℝ) ^ (-53 : ℤ) :=
    sub_nonneg.mpr (le_of_lt hstrict.1)
  have hx_right_nonpos :
      (1 : ℝ) / problem2_13_sourceX j -
        ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-53 : ℤ) ≤ 0 :=
    sub_nonpos.mpr (le_of_lt hstrict.2)
  rw [abs_of_nonneg hx_left_nonneg, abs_of_nonpos hx_right_nonpos]
  rw [hrecip]
  have hgoal :
      (2 : ℝ) ^ (52 : ℕ) / n -
          (k : ℝ) * (2 : ℝ) ^ (-53 : ℤ) <
        ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-53 : ℤ) -
          (2 : ℝ) ^ (52 : ℕ) / n := by
    rw [zpow_neg]
    field_simp [hnpos.ne']
    ring_nf at hmidR2 ⊢
    have hk1 : ((1 + k : ℕ) : ℝ) = 1 + (k : ℝ) := by norm_num
    nlinarith [hmidR2, hk1]
  linarith

theorem problem2_13_sourceX_reciprocal_right_closer_of_scaled_midpoint
    {j k : ℕ}
    (hstrict :
      (k : ℝ) * (2 : ℝ) ^ (-53 : ℤ) <
          (1 : ℝ) / problem2_13_sourceX j ∧
        (1 : ℝ) / problem2_13_sourceX j <
          ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-53 : ℤ))
    (hmid : (2 * k + 1) * (2 ^ 52 + j) < (2 ^ 106 : ℕ)) :
    |(1 : ℝ) / problem2_13_sourceX j -
        ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-53 : ℤ)| <
      |(1 : ℝ) / problem2_13_sourceX j -
        (k : ℝ) * (2 : ℝ) ^ (-53 : ℤ)| := by
  let n : ℝ := ((2 ^ 52 + j : ℕ) : ℝ)
  have hnpos : 0 < n := by
    positivity
  have hsource :
      problem2_13_sourceX j = n * (2 : ℝ) ^ (-52 : ℤ) := by
    simpa [n] using problem2_13_sourceX_eq_scaled j
  have hrecip :
      (1 : ℝ) / problem2_13_sourceX j = (2 : ℝ) ^ (52 : ℕ) / n := by
    rw [hsource]
    field_simp [hnpos.ne']
  have hmidR :
      ((((2 * k + 1) * (2 ^ 52 + j) : ℕ) : ℝ) <
        ((2 ^ 106 : ℕ) : ℝ)) := by
    exact_mod_cast hmid
  have hmidR2 :
      (2 * (k : ℝ) + 1) * n < (2 : ℝ) ^ (106 : ℕ) := by
    norm_num [n, Nat.cast_mul, Nat.cast_add, Nat.cast_pow] at hmidR ⊢
    exact hmidR
  have hx_left_nonneg :
      0 ≤ (1 : ℝ) / problem2_13_sourceX j -
        (k : ℝ) * (2 : ℝ) ^ (-53 : ℤ) :=
    sub_nonneg.mpr (le_of_lt hstrict.1)
  have hx_right_nonpos :
      (1 : ℝ) / problem2_13_sourceX j -
        ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-53 : ℤ) ≤ 0 :=
    sub_nonpos.mpr (le_of_lt hstrict.2)
  rw [abs_of_nonpos hx_right_nonpos, abs_of_nonneg hx_left_nonneg]
  rw [hrecip]
  have hgoal :
      ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-53 : ℤ) -
          (2 : ℝ) ^ (52 : ℕ) / n <
        (2 : ℝ) ^ (52 : ℕ) / n -
          (k : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
    rw [zpow_neg]
    field_simp [hnpos.ne']
    ring_nf at hmidR2 ⊢
    have hk1 : ((1 + k : ℕ) : ℝ) = 1 + (k : ℝ) := by norm_num
    nlinarith [hmidR2, hk1]
  linarith

theorem problem2_13_sourceProduct_eq_scaled_of_reciprocal_rounds {j k : ℕ}
    (hround :
      ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j) =
        (k : ℝ) * (2 : ℝ) ^ (-53 : ℤ)) :
    problem2_13_sourceProduct j =
      ((2 ^ 52 + j : ℕ) : ℝ) * (k : ℝ) *
        (2 : ℝ) ^ (-105 : ℤ) := by
  rw [problem2_13_sourceProduct, hround]
  unfold problem2_13_sourceX
  norm_num [zpow_neg]
  ring

theorem problem2_13_sourceProduct_lower_midpoint_le_of_scaled_product_ge
    {j k : ℕ}
    (hround :
      ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j) =
        (k : ℝ) * (2 : ℝ) ^ (-53 : ℤ))
    (hscaled :
      (2 ^ 105 - 2 ^ 51 : ℕ) ≤ (2 ^ 52 + j) * k) :
    (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) ≤ problem2_13_sourceProduct j := by
  rw [problem2_13_sourceProduct_eq_scaled_of_reciprocal_rounds hround]
  have hscaled_real :
      (((2 ^ 105 - 2 ^ 51 : ℕ) : ℝ) ≤
        (((2 ^ 52 + j) * k : ℕ) : ℝ)) := by
    exact_mod_cast hscaled
  norm_num [zpow_neg] at hscaled_real ⊢
  nlinarith

theorem problem2_13_sourceProduct_lt_lower_midpoint_of_scaled_product_lt
    {j k : ℕ}
    (hround :
      ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j) =
        (k : ℝ) * (2 : ℝ) ^ (-53 : ℤ))
    (hscaled :
      (2 ^ 52 + j) * k < (2 ^ 105 - 2 ^ 51 : ℕ)) :
    problem2_13_sourceProduct j < (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) := by
  rw [problem2_13_sourceProduct_eq_scaled_of_reciprocal_rounds hround]
  have hscaled_real :
      ((((2 ^ 52 + j) * k : ℕ) : ℝ) <
        ((2 ^ 105 - 2 ^ 51 : ℕ) : ℝ)) := by
    exact_mod_cast hscaled
  norm_num [zpow_neg] at hscaled_real ⊢
  nlinarith

theorem problem2_13_predecessorX_eq_scaled :
    problem2_13_predecessorX =
      (4503599885106985 : ℝ) * (2 : ℝ) ^ (-52 : ℤ) := by
  norm_num [problem2_13_predecessorX, problem2_13_predecessorJ, zpow_neg]

theorem problem2_13_predecessorX_finiteSystem :
    ieeeDoubleFormat.finiteSystem problem2_13_predecessorX := by
  refine Or.inr (Or.inl ?_)
  refine ⟨false, 4503599885106985, (1 : ℤ), ?_, ?_, ?_⟩
  · norm_num [ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  · norm_num [ieeeDoubleFormat, exponentInRange]
  · rw [problem2_13_predecessorX_eq_scaled]
    norm_num [ieeeDoubleFormat, normalizedValue, signValue, betaR, zpow_neg]

theorem problem2_13_predecessorX_between_one_two :
    (1 : ℝ) < problem2_13_predecessorX ∧
      problem2_13_predecessorX < (2 : ℝ) := by
  norm_num [problem2_13_predecessorX, problem2_13_predecessorJ, zpow_neg]

/-- The previous source integer gives the immediately adjacent IEEE-double
input gridpoint below the failing candidate. -/
theorem problem2_13_predecessor_candidate_adjacentNormalized :
    ieeeDoubleFormat.realOrderAdjacentNormalized
      problem2_13_predecessorX problem2_13_candidateX := by
  let fmt := ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false 4503599885106985 1
  let b : ℝ := fmt.normalizedValue false 4503599885106986 1
  have hm : fmt.normalizedMantissa 4503599885106985 := by
    norm_num [fmt, ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (4503599885106985 + 1) := by
    norm_num [fmt, ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 4503599885106985, (1 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value : a = problem2_13_predecessorX := by
    rw [problem2_13_predecessorX_eq_scaled]
    norm_num [a, fmt, ieeeDoubleFormat, normalizedValue, signValue, betaR,
      zpow_neg]
  have hb_value : b = problem2_13_candidateX := by
    rw [problem2_13_candidateX_eq_scaled]
    norm_num [b, fmt, ieeeDoubleFormat, normalizedValue, signValue, betaR,
      zpow_neg]
  simpa [ha_value, hb_value] using hadj

theorem problem2_13_predecessorX_lt_candidateX :
    problem2_13_predecessorX < problem2_13_candidateX := by
  norm_num [problem2_13_predecessorX, problem2_13_candidateX,
    problem2_13_predecessorJ, problem2_13_candidateJ, zpow_neg]

theorem problem2_13_candidate_scaled_product_lt_lower_midpoint_threshold :
    (2 ^ 52 + problem2_13_candidateJ) * 9007198739268041 <
      (2 ^ 105 - 2 ^ 51 : ℕ) := by
  norm_num [problem2_13_candidateJ]

theorem problem2_13_predecessor_scaled_product_ge_lower_midpoint_threshold :
    (2 ^ 105 - 2 ^ 51 : ℕ) ≤
      (2 ^ 52 + problem2_13_predecessorJ) * 9007198739268043 := by
  norm_num [problem2_13_predecessorJ]

end FloatingPointFormat
end NumStability

end
