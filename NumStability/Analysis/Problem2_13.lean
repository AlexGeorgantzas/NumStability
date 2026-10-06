-- Analysis/Problem2_13.lean
--
-- Problem-specific theorem surface for Higham Chapter 2, Problem 2.13.

import Mathlib.Data.Nat.Factorization.Basic
import NumStability.Analysis.Problem2_12

namespace NumStability

noncomputable section

namespace FloatingPointFormat

/-!
# Higham Chapter 2, Problem 2.13

Problem 2.13 asks for the smallest positive integer `j` for which Edelman's
Problem 2.12 reciprocal-product computation stops returning `1`, with
`x = 1 + j*eps` and `eps = 2^-52`.

This file records the exact finite-wrapper certificate for that search:
the candidate `j = 257736490` does fail, and the rounded computation returns
the predecessor of `1`, while every positive `j < 257736490` still rounds back
to `1` in the modeled finite real-valued IEEE-double operation wrapper.
-/

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

private theorem problem2_13_eq_two_pow_of_dvd_two_pow
    {n k : ℕ} (hn0 : n ≠ 0) (hdvd : n ∣ 2 ^ k) :
    ∃ e, n = 2 ^ e := by
  have hpow0 : (2 ^ k : ℕ) ≠ 0 := by
    exact pow_ne_zero k (by decide : (2 : ℕ) ≠ 0)
  have hle : n.factorization ≤ (2 ^ k : ℕ).factorization :=
    (Nat.factorization_le_iff_dvd hn0 hpow0).2 hdvd
  let e := n.factorization 2
  have hfac : n.factorization = Finsupp.single 2 e := by
    apply Finsupp.ext
    intro p
    by_cases hp2 : p = 2
    · subst p
      simp [e]
    · have hlep : n.factorization p ≤ (2 ^ k : ℕ).factorization p := hle p
      have hpowfac : (2 ^ k : ℕ).factorization p = 0 := by
        simp [Nat.Prime.factorization_pow Nat.prime_two, hp2]
      rw [hpowfac] at hlep
      have hz : n.factorization p = 0 := Nat.eq_zero_of_le_zero hlep
      simpa [Finsupp.single_eq_of_ne hp2] using hz
  exact ⟨e, Nat.eq_pow_of_factorization_eq_single hn0 hfac⟩

private theorem problem2_13_no_two_pow_between_2_52_2_53 {e : ℕ}
    (hlo : 2 ^ 52 < 2 ^ e) (hhi : 2 ^ e < 2 ^ 53) : False := by
  have helo : 52 < e :=
    (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : ℕ))).1 hlo
  have hehi : e < 53 :=
    (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : ℕ))).1 hhi
  omega

theorem problem2_13_reciprocalCellQuotient_remainder_ne_zero_of_pos_lt_candidateJ
    {j : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ) :
    (2 ^ 105 : ℕ) % (2 ^ 52 + j) ≠ 0 := by
  intro hzero
  have hnpos : 0 < 2 ^ 52 + j := by
    positivity
  have hn0 : 2 ^ 52 + j ≠ 0 := Nat.ne_of_gt hnpos
  have hdvd : 2 ^ 52 + j ∣ (2 ^ 105 : ℕ) := Nat.dvd_of_mod_eq_zero hzero
  rcases problem2_13_eq_two_pow_of_dvd_two_pow hn0 hdvd with ⟨e, he⟩
  have hn_gt : 2 ^ 52 < 2 ^ 52 + j := by
    exact Nat.lt_add_of_pos_right hjpos
  have hn_lt : 2 ^ 52 + j < 2 ^ 53 := by
    have hj' : j < 257736490 := by
      simpa [problem2_13_candidateJ] using hj
    norm_num at hj' ⊢
    omega
  rw [he] at hn_gt
  rw [he] at hn_lt
  exact problem2_13_no_two_pow_between_2_52_2_53 hn_gt hn_lt

theorem
    problem2_13_reciprocalCellQuotient_remainder_not_half_of_pos_lt_candidateJ
    {j : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ) :
    2 * ((2 ^ 105 : ℕ) % (2 ^ 52 + j)) ≠ 2 ^ 52 + j := by
  intro htie
  let n := 2 ^ 52 + j
  let a := (2 ^ 105 : ℕ)
  let q := a / n
  let r := a % n
  have hnpos : 0 < n := by
    positivity
  have hn0 : n ≠ 0 := Nat.ne_of_gt hnpos
  have hdivmod : q * n + r = a := by
    simpa [q, r, Nat.mul_comm] using Nat.div_add_mod a n
  have htie' : 2 * r = n := by
    simpa [n, a, r] using htie
  have hdvd : n ∣ (2 ^ 106 : ℕ) := by
    refine ⟨2 * q + 1, ?_⟩
    have h2a : 2 * a = (2 * q + 1) * n := by
      nlinarith
    have hpow : 2 * a = (2 ^ 106 : ℕ) := by
      norm_num [a]
    rw [← hpow, h2a]
    ring
  rcases problem2_13_eq_two_pow_of_dvd_two_pow hn0 hdvd with ⟨e, he⟩
  have hn_gt : 2 ^ 52 < n := by
    simpa [n] using Nat.lt_add_of_pos_right (n := 2 ^ 52) hjpos
  have hn_lt : n < 2 ^ 53 := by
    have hj' : j < 257736490 := by
      simpa [problem2_13_candidateJ] using hj
    norm_num [n] at hj' ⊢
    omega
  rw [he] at hn_gt
  rw [he] at hn_lt
  exact problem2_13_no_two_pow_between_2_52_2_53 hn_gt hn_lt

theorem
    problem2_13_reciprocalCellQuotient_remainder_half_trichotomy_of_pos_lt_candidateJ
    {j : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ) :
    2 * ((2 ^ 105 : ℕ) % (2 ^ 52 + j)) < 2 ^ 52 + j ∨
      2 ^ 52 + j < 2 * ((2 ^ 105 : ℕ) % (2 ^ 52 + j)) := by
  exact lt_or_gt_of_ne
    (problem2_13_reciprocalCellQuotient_remainder_not_half_of_pos_lt_candidateJ
      hjpos hj)

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

private theorem problem2_13_s29_quadratic_remainder_le_threshold_aux
    {j r : ℕ}
    (hj : j < problem2_13_candidateJ)
    (hdiv : 29 * (2 ^ 52 + j) + r = 2 * j * j) :
    r ≤ 2 ^ 51 := by
  by_contra hnot
  have hgt : 2 ^ 51 < r := by
    omega
  have hj' : j < 257736490 := by
    simpa [problem2_13_candidateJ] using hj
  norm_num at hdiv hgt hj' ⊢
  nlinarith

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

theorem
    problem2_13_reciprocalCellQuotient_remainder_le_threshold_of_quadraticQuotient_eq_29
    {j : ℕ} (hj : j < problem2_13_candidateJ)
    (hs : problem2_13_quadraticRemainderQuotient j = 29) :
    (2 ^ 105 : ℕ) % (2 ^ 52 + j) ≤ 2 ^ 51 := by
  rw [problem2_13_reciprocalCellQuotient_remainder_eq_quadratic_remainder_of_lt_candidateJ
    hj]
  have hdivmod :
      (2 ^ 52 + j) * problem2_13_quadraticRemainderQuotient j +
          (2 * j * j) % (2 ^ 52 + j) = 2 * j * j := by
    simpa [problem2_13_quadraticRemainderQuotient] using
      Nat.div_add_mod (2 * j * j) (2 ^ 52 + j)
  rw [hs] at hdivmod
  have hdiv29 :
      29 * (2 ^ 52 + j) + (2 * j * j) % (2 ^ 52 + j) = 2 * j * j := by
    simpa [Nat.mul_comm] using hdivmod
  exact problem2_13_s29_quadratic_remainder_le_threshold_aux hj hdiv29

private theorem problem2_13_lower_quadratic_remainder_left_threshold_aux
    {j s r : ℕ} (hs : s ≤ 28)
    (hdiv : s * (2 ^ 52 + j) + r = 2 * j * j)
    (hrem_gt : 2 ^ 51 < r)
    (hrem_left : 2 * r < 2 ^ 52 + j) : False := by
  interval_cases s
  · have hjlo : 33554433 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 33554432 := by omega
      have hjsq : j * j ≤ 33554432 * 33554432 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 58117982 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 58117981 := by omega
      have hjsq : j * j ≤ 58117981 * 58117981 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 75029992 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 75029991 := by omega
      have hjsq : j * j ≤ 75029991 * 75029991 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 88776684 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 88776683 := by omega
      have hjsq : j * j ≤ 88776683 * 88776683 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 100663298 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 100663297 := by omega
      have hjsq : j * j ≤ 100663297 * 100663297 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 111287463 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 111287462 := by omega
      have hjsq : j * j ≤ 111287462 * 111287462 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 120982227 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 120982226 := by omega
      have hjsq : j * j ≤ 120982226 * 120982226 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 129955759 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 129955758 := by omega
      have hjsq : j * j ≤ 129955758 * 129955758 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 138348470 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 138348469 := by omega
      have hjsq : j * j ≤ 138348469 * 138348469 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 146260381 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 146260380 := by omega
      have hjsq : j * j ≤ 146260380 * 146260380 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 153765728 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 153765727 := by omega
      have hjsq : j * j ≤ 153765727 * 153765727 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 160921406 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 160921405 := by omega
      have hjsq : j * j ≤ 160921405 * 160921405 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 167772164 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 167772163 := by omega
      have hjsq : j * j ≤ 167772163 * 167772163 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 174353947 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 174353946 := by omega
      have hjsq : j * j ≤ 174353946 * 174353946 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 180696150 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 180696149 := by omega
      have hjsq : j * j ≤ 180696149 * 180696149 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 186823175 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 186823174 := by omega
      have hjsq : j * j ≤ 186823174 * 186823174 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 192755541 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 192755540 := by omega
      have hjsq : j * j ≤ 192755540 * 192755540 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 198510702 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 198510701 := by omega
      have hjsq : j * j ≤ 198510701 * 198510701 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 204103647 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 204103646 := by omega
      have hjsq : j * j ≤ 204103646 * 204103646 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 209547366 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 209547365 := by omega
      have hjsq : j * j ≤ 209547365 * 209547365 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 214853202 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 214853201 := by omega
      have hjsq : j * j ≤ 214853201 * 214853201 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 220031131 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 220031130 := by omega
      have hjsq : j * j ≤ 220031130 * 220031130 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 225089979 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 225089978 := by omega
      have hjsq : j * j ≤ 225089978 * 225089978 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 230037602 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 230037601 := by omega
      have hjsq : j * j ≤ 230037601 * 230037601 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 234881031 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 234881030 := by omega
      have hjsq : j * j ≤ 234881030 * 234881030 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 239626581 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 239626580 := by omega
      have hjsq : j * j ≤ 239626580 * 239626580 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 244279959 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 244279958 := by omega
      have hjsq : j * j ≤ 244279958 * 244279958 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 248846335 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 248846334 := by omega
      have hjsq : j * j ≤ 248846334 * 248846334 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith
  · have hjlo : 253330414 ≤ j := by
      by_contra hnot
      have hjle : j ≤ 253330413 := by omega
      have hjsq : j * j ≤ 253330413 * 253330413 :=
        Nat.mul_le_mul hjle hjle
      norm_num at hdiv hrem_gt hrem_left hjsq ⊢
      nlinarith
    norm_num at hdiv hrem_gt hrem_left hjlo ⊢
    nlinarith

theorem
    problem2_13_reciprocalCellQuotient_remainder_le_threshold_of_quadraticQuotient_le_28_of_left
    {j : ℕ} (hj : j < problem2_13_candidateJ)
    (hs : problem2_13_quadraticRemainderQuotient j ≤ 28)
    (hrem_left :
      2 * ((2 ^ 105 : ℕ) % (2 ^ 52 + j)) < 2 ^ 52 + j) :
    (2 ^ 105 : ℕ) % (2 ^ 52 + j) ≤ 2 ^ 51 := by
  by_contra hnot
  have hrem_gt_orig : 2 ^ 51 < (2 ^ 105 : ℕ) % (2 ^ 52 + j) := by
    omega
  have hrem_eq :=
    problem2_13_reciprocalCellQuotient_remainder_eq_quadratic_remainder_of_lt_candidateJ
      (j := j) hj
  rw [hrem_eq] at hrem_gt_orig hrem_left
  have hdivmod :
      (2 ^ 52 + j) * problem2_13_quadraticRemainderQuotient j +
          (2 * j * j) % (2 ^ 52 + j) = 2 * j * j := by
    simpa [problem2_13_quadraticRemainderQuotient] using
      Nat.div_add_mod (2 * j * j) (2 ^ 52 + j)
  have hdiv :
      problem2_13_quadraticRemainderQuotient j * (2 ^ 52 + j) +
          (2 * j * j) % (2 ^ 52 + j) = 2 * j * j := by
    simpa [Nat.mul_comm] using hdivmod
  exact problem2_13_lower_quadratic_remainder_left_threshold_aux hs hdiv
    hrem_gt_orig hrem_left

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

private theorem problem2_13_ieeeDoubleFormat_minNormalMagnitude_le_half :
    ieeeDoubleFormat.minNormalMagnitude ≤ (1 / 2 : ℝ) := by
  norm_num [ieeeDoubleFormat, minNormalMagnitude, betaR, zpow_neg]
  have hden : (2 : ℝ) ≤ (2 : ℝ) ^ (1022 : ℕ) := by
    exact le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (1022 : ℕ) ≠ 0)
  simpa [one_div] using
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hden

private theorem problem2_13_four_le_ieeeDoubleFormat_maxFiniteMagnitude :
    (4 : ℝ) ≤ ieeeDoubleFormat.maxFiniteMagnitude := by
  rw [maxFiniteMagnitude, ieeeDoubleFormat, betaR]
  norm_num [zpow_neg]
  change (4 : ℝ) ≤ (2 : ℝ) ^ (1024 : ℕ) *
    (9007199254740991 / 9007199254740992 : ℝ)
  have hfactor :
      (1 / 2 : ℝ) ≤ (9007199254740991 / 9007199254740992 : ℝ) := by
    norm_num
  have hpow_nat : (8 : ℝ) ≤ (2 : ℝ) ^ (1024 : ℕ) := by
    calc
      (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ (1024 : ℕ) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num)
  have hmul := mul_le_mul hpow_nat hfactor
    (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
    (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (1024 : ℕ))
  norm_num at hmul
  exact hmul

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

private theorem problem2_13_midpoint_left_aux {a n q r : ℕ}
    (hdiv : q * n + r = a) (hr : 2 * r < n) :
    2 * a < (2 * q + 1) * n := by
  nlinarith

private theorem problem2_13_midpoint_right_aux {a n q r : ℕ}
    (hdiv : q * n + r = a) (hr : n < 2 * r) :
    (2 * q + 1) * n < 2 * a := by
  nlinarith

private theorem problem2_13_scaled_product_left_aux {a n q r t : ℕ}
    (hdiv : q * n + r = a) (hr : r ≤ t) :
    a - t ≤ n * q := by
  rw [Nat.mul_comm n q]
  omega

private theorem problem2_13_scaled_product_right_aux {a n q r t : ℕ}
    (hdiv : q * n + r = a) (hr : r < n) :
    a - t ≤ n * (q + 1) := by
  have ha_le : a ≤ n * (q + 1) := by
    nlinarith
  exact le_trans (Nat.sub_le a t) ha_le

theorem
    problem2_13_reciprocalCellQuotient_midpoint_left_of_twice_remainder_lt
    {j : ℕ}
    (hrem_lt :
      2 * ((2 ^ 105 : ℕ) % (2 ^ 52 + j)) < 2 ^ 52 + j) :
    (2 ^ 106 : ℕ) <
      (2 * problem2_13_reciprocalCellQuotient j + 1) *
        (2 ^ 52 + j) := by
  let n := 2 ^ 52 + j
  let a := (2 ^ 105 : ℕ)
  let q := a / n
  let r := a % n
  have hdivmod : q * n + r = a := by
    simpa [q, r, Nat.mul_comm] using Nat.div_add_mod a n
  have hrem_lt' : 2 * r < n := by
    simpa [n, a, r] using hrem_lt
  have hgoal_aux : 2 * a < (2 * q + 1) * n :=
    problem2_13_midpoint_left_aux hdivmod hrem_lt'
  change 2 * (2 ^ 105 : ℕ) <
    (2 * problem2_13_reciprocalCellQuotient j + 1) * (2 ^ 52 + j)
  simpa [problem2_13_reciprocalCellQuotient, n, a, q] using hgoal_aux

theorem
    problem2_13_reciprocalCellQuotient_midpoint_right_of_denominator_lt_twice_remainder
    {j : ℕ}
    (hrem_gt :
      2 ^ 52 + j < 2 * ((2 ^ 105 : ℕ) % (2 ^ 52 + j))) :
    (2 * problem2_13_reciprocalCellQuotient j + 1) *
        (2 ^ 52 + j) <
      (2 ^ 106 : ℕ) := by
  let n := 2 ^ 52 + j
  let a := (2 ^ 105 : ℕ)
  let q := a / n
  let r := a % n
  have hdivmod : q * n + r = a := by
    simpa [q, r, Nat.mul_comm] using Nat.div_add_mod a n
  have hrem_gt' : n < 2 * r := by
    simpa [n, a, r] using hrem_gt
  have hgoal_aux : (2 * q + 1) * n < 2 * a :=
    problem2_13_midpoint_right_aux hdivmod hrem_gt'
  change (2 * problem2_13_reciprocalCellQuotient j + 1) *
      (2 ^ 52 + j) <
    2 * (2 ^ 105 : ℕ)
  simpa [problem2_13_reciprocalCellQuotient, n, a, q] using hgoal_aux

theorem
    problem2_13_reciprocalCellQuotient_scaled_product_left_ge_of_remainder_le
    {j : ℕ}
    (hrem_le : ((2 ^ 105 : ℕ) % (2 ^ 52 + j)) ≤ 2 ^ 51) :
    (2 ^ 105 - 2 ^ 51 : ℕ) ≤
      (2 ^ 52 + j) * problem2_13_reciprocalCellQuotient j := by
  let n := 2 ^ 52 + j
  let a := (2 ^ 105 : ℕ)
  let q := a / n
  let r := a % n
  have hdivmod : q * n + r = a := by
    simpa [q, r, Nat.mul_comm] using Nat.div_add_mod a n
  have hrem_le' : r ≤ 2 ^ 51 := by
    simpa [n, a, r] using hrem_le
  have hgoal_aux : a - 2 ^ 51 ≤ n * q :=
    problem2_13_scaled_product_left_aux hdivmod hrem_le'
  change (2 ^ 105 : ℕ) - 2 ^ 51 ≤ n * q
  exact hgoal_aux

theorem problem2_13_reciprocalCellQuotient_scaled_product_right_ge
    {j : ℕ} :
    (2 ^ 105 - 2 ^ 51 : ℕ) ≤
      (2 ^ 52 + j) * (problem2_13_reciprocalCellQuotient j + 1) := by
  let n := 2 ^ 52 + j
  let a := (2 ^ 105 : ℕ)
  let q := a / n
  let r := a % n
  have hnpos : 0 < n := by
    positivity
  have hdivmod : q * n + r = a := by
    simpa [q, r, Nat.mul_comm] using Nat.div_add_mod a n
  have hrem_lt : r < n := by
    simpa [r, n] using Nat.mod_lt a hnpos
  have hgoal_aux : a - 2 ^ 51 ≤ n * (q + 1) :=
    problem2_13_scaled_product_right_aux hdivmod hrem_lt
  change (2 ^ 105 : ℕ) - 2 ^ 51 ≤ n * (q + 1)
  exact hgoal_aux

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

theorem problem2_13_sourceX_reciprocal_rounds_to_left_of_adjacent_scaled
    {j k : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hm : ieeeDoubleFormat.normalizedMantissa k)
    (hmnext : ieeeDoubleFormat.normalizedMantissa (k + 1))
    (hstrict :
      (k : ℝ) * (2 : ℝ) ^ (-53 : ℤ) <
          (1 : ℝ) / problem2_13_sourceX j ∧
        (1 : ℝ) / problem2_13_sourceX j <
          ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-53 : ℤ))
    (hleftCloser :
      |(1 : ℝ) / problem2_13_sourceX j -
          (k : ℝ) * (2 : ℝ) ^ (-53 : ℤ)| <
        |(1 : ℝ) / problem2_13_sourceX j -
          ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-53 : ℤ)|) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
        (1 : ℝ) (problem2_13_sourceX j) =
      (k : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
  let fmt := ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false k 0
  let b : ℝ := fmt.normalizedValue false (k + 1) 0
  let x : ℝ := (1 : ℝ) / problem2_13_sourceX j
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, k, (0 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value :
      a = (k : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [a, fmt, ieeeDoubleFormat, normalizedValue, signValue, betaR,
      zpow_neg]
  have hb_value :
      b = ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, ieeeDoubleFormat, normalizedValue, signValue, betaR,
      zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rcases problem2_13_sourceX_between_one_two_of_pos_lt_candidateJ hjpos hj
      with ⟨hxlo, hxhi⟩
    simpa [x, fmt] using
      (problem2_12_ieeeDouble_reciprocal_finiteNormalRange_of_one_lt_x_lt_two
        hxlo hxhi)
  have hstrict' : a < x ∧ x < b := by
    simpa [x, ha_value, hb_value] using hstrict
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hxrange
  have hleftCloser' : |x - a| < |x - b| := by
    simpa [x, ha_value, hb_value] using hleftCloser
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict' hleftCloser'
  change fmt.finiteRoundToEven ((1 : ℝ) / problem2_13_sourceX j) =
    (k : ℝ) * (2 : ℝ) ^ (-53 : ℤ)
  simpa [x, fmt, ha_value] using hround

theorem problem2_13_sourceX_reciprocal_rounds_to_right_of_adjacent_scaled
    {j k : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hm : ieeeDoubleFormat.normalizedMantissa k)
    (hmnext : ieeeDoubleFormat.normalizedMantissa (k + 1))
    (hstrict :
      (k : ℝ) * (2 : ℝ) ^ (-53 : ℤ) <
          (1 : ℝ) / problem2_13_sourceX j ∧
        (1 : ℝ) / problem2_13_sourceX j <
          ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-53 : ℤ))
    (hrightCloser :
      |(1 : ℝ) / problem2_13_sourceX j -
          ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-53 : ℤ)| <
        |(1 : ℝ) / problem2_13_sourceX j -
          (k : ℝ) * (2 : ℝ) ^ (-53 : ℤ)|) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
        (1 : ℝ) (problem2_13_sourceX j) =
      ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
  let fmt := ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false k 0
  let b : ℝ := fmt.normalizedValue false (k + 1) 0
  let x : ℝ := (1 : ℝ) / problem2_13_sourceX j
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, k, (0 : ℤ), hm, hmnext, Or.inl ⟨rfl, rfl⟩⟩
  have ha_value :
      a = (k : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [a, fmt, ieeeDoubleFormat, normalizedValue, signValue, betaR,
      zpow_neg]
  have hb_value :
      b = ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, ieeeDoubleFormat, normalizedValue, signValue, betaR,
      zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rcases problem2_13_sourceX_between_one_two_of_pos_lt_candidateJ hjpos hj
      with ⟨hxlo, hxhi⟩
    simpa [x, fmt] using
      (problem2_12_ieeeDouble_reciprocal_finiteNormalRange_of_one_lt_x_lt_two
        hxlo hxhi)
  have hstrict' : a < x ∧ x < b := by
    simpa [x, ha_value, hb_value] using hstrict
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hxrange
  have hrightCloser' : |x - b| < |x - a| := by
    simpa [x, ha_value, hb_value] using hrightCloser
  have hround : fmt.finiteRoundToEven x = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict' hrightCloser'
  change fmt.finiteRoundToEven ((1 : ℝ) / problem2_13_sourceX j) =
    ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-53 : ℤ)
  simpa [x, fmt, hb_value] using hround

theorem problem2_13_sourceX_reciprocal_rounds_to_left_of_scaled_interval_midpoint
    {j k : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hm : ieeeDoubleFormat.normalizedMantissa k)
    (hmnext : ieeeDoubleFormat.normalizedMantissa (k + 1))
    (hlo :
      (k : ℝ) * ((2 ^ 52 + j : ℕ) : ℝ) < (2 : ℝ) ^ (105 : ℕ))
    (hhi :
      (2 : ℝ) ^ (105 : ℕ) <
        ((k + 1 : ℕ) : ℝ) * ((2 ^ 52 + j : ℕ) : ℝ))
    (hmid : (2 ^ 106 : ℕ) < (2 * k + 1) * (2 ^ 52 + j)) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
        (1 : ℝ) (problem2_13_sourceX j) =
      (k : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
  have hstrict :=
    problem2_13_sourceX_reciprocal_strict_between_of_scaled_interval
      (j := j) (k := k) hlo hhi
  exact
    problem2_13_sourceX_reciprocal_rounds_to_left_of_adjacent_scaled
      hjpos hj hm hmnext hstrict
      (problem2_13_sourceX_reciprocal_left_closer_of_scaled_midpoint
        hstrict hmid)

theorem problem2_13_sourceX_reciprocal_rounds_to_right_of_scaled_interval_midpoint
    {j k : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hm : ieeeDoubleFormat.normalizedMantissa k)
    (hmnext : ieeeDoubleFormat.normalizedMantissa (k + 1))
    (hlo :
      (k : ℝ) * ((2 ^ 52 + j : ℕ) : ℝ) < (2 : ℝ) ^ (105 : ℕ))
    (hhi :
      (2 : ℝ) ^ (105 : ℕ) <
        ((k + 1 : ℕ) : ℝ) * ((2 ^ 52 + j : ℕ) : ℝ))
    (hmid : (2 * k + 1) * (2 ^ 52 + j) < (2 ^ 106 : ℕ)) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
        (1 : ℝ) (problem2_13_sourceX j) =
      ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
  have hstrict :=
    problem2_13_sourceX_reciprocal_strict_between_of_scaled_interval
      (j := j) (k := k) hlo hhi
  exact
    problem2_13_sourceX_reciprocal_rounds_to_right_of_adjacent_scaled
      hjpos hj hm hmnext hstrict
      (problem2_13_sourceX_reciprocal_right_closer_of_scaled_midpoint
        hstrict hmid)

theorem problem2_13_sourceX_reciprocal_rounds_to_left_of_nat_interval_midpoint
    {j k : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hm : ieeeDoubleFormat.normalizedMantissa k)
    (hmnext : ieeeDoubleFormat.normalizedMantissa (k + 1))
    (hlo : k * (2 ^ 52 + j) < (2 ^ 105 : ℕ))
    (hhi : (2 ^ 105 : ℕ) < (k + 1) * (2 ^ 52 + j))
    (hmid : (2 ^ 106 : ℕ) < (2 * k + 1) * (2 ^ 52 + j)) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
        (1 : ℝ) (problem2_13_sourceX j) =
      (k : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
  have hstrict :=
    problem2_13_sourceX_reciprocal_strict_between_of_nat_scaled_interval
      (j := j) (k := k) hlo hhi
  exact
    problem2_13_sourceX_reciprocal_rounds_to_left_of_adjacent_scaled
      hjpos hj hm hmnext hstrict
      (problem2_13_sourceX_reciprocal_left_closer_of_scaled_midpoint
        hstrict hmid)

theorem problem2_13_sourceX_reciprocal_rounds_to_right_of_nat_interval_midpoint
    {j k : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hm : ieeeDoubleFormat.normalizedMantissa k)
    (hmnext : ieeeDoubleFormat.normalizedMantissa (k + 1))
    (hlo : k * (2 ^ 52 + j) < (2 ^ 105 : ℕ))
    (hhi : (2 ^ 105 : ℕ) < (k + 1) * (2 ^ 52 + j))
    (hmid : (2 * k + 1) * (2 ^ 52 + j) < (2 ^ 106 : ℕ)) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
        (1 : ℝ) (problem2_13_sourceX j) =
      ((k + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
  have hstrict :=
    problem2_13_sourceX_reciprocal_strict_between_of_nat_scaled_interval
      (j := j) (k := k) hlo hhi
  exact
    problem2_13_sourceX_reciprocal_rounds_to_right_of_adjacent_scaled
      hjpos hj hm hmnext hstrict
      (problem2_13_sourceX_reciprocal_right_closer_of_scaled_midpoint
        hstrict hmid)

theorem problem2_13_sourceX_reciprocal_rounds_to_left_of_quotient_midpoint
    {j : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hrem : (2 ^ 105 : ℕ) % (2 ^ 52 + j) ≠ 0)
    (hm :
      ieeeDoubleFormat.normalizedMantissa
        (problem2_13_reciprocalCellQuotient j))
    (hmnext :
      ieeeDoubleFormat.normalizedMantissa
        (problem2_13_reciprocalCellQuotient j + 1))
    (hmid :
      (2 ^ 106 : ℕ) <
        (2 * problem2_13_reciprocalCellQuotient j + 1) *
          (2 ^ 52 + j)) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
        (1 : ℝ) (problem2_13_sourceX j) =
      (problem2_13_reciprocalCellQuotient j : ℝ) *
        (2 : ℝ) ^ (-53 : ℤ) := by
  rcases problem2_13_reciprocalCellQuotient_nat_scaled_interval
      (j := j) hrem with ⟨hlo, hhi⟩
  exact
    problem2_13_sourceX_reciprocal_rounds_to_left_of_nat_interval_midpoint
      hjpos hj hm hmnext hlo hhi hmid

theorem problem2_13_sourceX_reciprocal_rounds_to_right_of_quotient_midpoint
    {j : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hrem : (2 ^ 105 : ℕ) % (2 ^ 52 + j) ≠ 0)
    (hm :
      ieeeDoubleFormat.normalizedMantissa
        (problem2_13_reciprocalCellQuotient j))
    (hmnext :
      ieeeDoubleFormat.normalizedMantissa
        (problem2_13_reciprocalCellQuotient j + 1))
    (hmid :
      (2 * problem2_13_reciprocalCellQuotient j + 1) *
          (2 ^ 52 + j) <
        (2 ^ 106 : ℕ)) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
        (1 : ℝ) (problem2_13_sourceX j) =
      ((problem2_13_reciprocalCellQuotient j + 1 : ℕ) : ℝ) *
        (2 : ℝ) ^ (-53 : ℤ) := by
  rcases problem2_13_reciprocalCellQuotient_nat_scaled_interval
      (j := j) hrem with ⟨hlo, hhi⟩
  exact
    problem2_13_sourceX_reciprocal_rounds_to_right_of_nat_interval_midpoint
      hjpos hj hm hmnext hlo hhi hmid

theorem
    problem2_13_sourceX_reciprocal_rounds_to_left_of_quotient_midpoint_of_pos_lt_candidateJ
    {j : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hrem : (2 ^ 105 : ℕ) % (2 ^ 52 + j) ≠ 0)
    (hmid :
      (2 ^ 106 : ℕ) <
        (2 * problem2_13_reciprocalCellQuotient j + 1) *
          (2 ^ 52 + j)) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
        (1 : ℝ) (problem2_13_sourceX j) =
      (problem2_13_reciprocalCellQuotient j : ℝ) *
        (2 : ℝ) ^ (-53 : ℤ) := by
  rcases
      problem2_13_reciprocalCellQuotient_normalizedMantissas_of_pos_lt_candidateJ
        hjpos hj with ⟨hm, hmnext⟩
  exact
    problem2_13_sourceX_reciprocal_rounds_to_left_of_quotient_midpoint
      hjpos hj hrem hm hmnext hmid

theorem
    problem2_13_sourceX_reciprocal_rounds_to_right_of_quotient_midpoint_of_pos_lt_candidateJ
    {j : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hrem : (2 ^ 105 : ℕ) % (2 ^ 52 + j) ≠ 0)
    (hmid :
      (2 * problem2_13_reciprocalCellQuotient j + 1) *
          (2 ^ 52 + j) <
        (2 ^ 106 : ℕ)) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
        (1 : ℝ) (problem2_13_sourceX j) =
      ((problem2_13_reciprocalCellQuotient j + 1 : ℕ) : ℝ) *
        (2 : ℝ) ^ (-53 : ℤ) := by
  rcases
      problem2_13_reciprocalCellQuotient_normalizedMantissas_of_pos_lt_candidateJ
        hjpos hj with ⟨hm, hmnext⟩
  exact
    problem2_13_sourceX_reciprocal_rounds_to_right_of_quotient_midpoint
      hjpos hj hrem hm hmnext hmid

theorem
    problem2_13_sourceX_reciprocal_rounds_to_left_of_quotient_remainder_lt_half
    {j : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hrem : (2 ^ 105 : ℕ) % (2 ^ 52 + j) ≠ 0)
    (hrem_lt :
      2 * ((2 ^ 105 : ℕ) % (2 ^ 52 + j)) < 2 ^ 52 + j) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
        (1 : ℝ) (problem2_13_sourceX j) =
      (problem2_13_reciprocalCellQuotient j : ℝ) *
        (2 : ℝ) ^ (-53 : ℤ) := by
  exact
    problem2_13_sourceX_reciprocal_rounds_to_left_of_quotient_midpoint_of_pos_lt_candidateJ
      hjpos hj hrem
      (problem2_13_reciprocalCellQuotient_midpoint_left_of_twice_remainder_lt
        hrem_lt)

theorem
    problem2_13_sourceX_reciprocal_rounds_to_right_of_quotient_remainder_gt_half
    {j : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hrem : (2 ^ 105 : ℕ) % (2 ^ 52 + j) ≠ 0)
    (hrem_gt :
      2 ^ 52 + j < 2 * ((2 ^ 105 : ℕ) % (2 ^ 52 + j))) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
        (1 : ℝ) (problem2_13_sourceX j) =
      ((problem2_13_reciprocalCellQuotient j + 1 : ℕ) : ℝ) *
        (2 : ℝ) ^ (-53 : ℤ) := by
  exact
    problem2_13_sourceX_reciprocal_rounds_to_right_of_quotient_midpoint_of_pos_lt_candidateJ
      hjpos hj hrem
      (problem2_13_reciprocalCellQuotient_midpoint_right_of_denominator_lt_twice_remainder
        hrem_gt)

theorem problem2_13_sourceX_rounding_options_of_pos_lt_candidateJ {j : ℕ}
    (hjpos : 0 < j) (hj : j < problem2_13_candidateJ) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (problem2_13_sourceX j)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j)) =
          (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) ∨
      ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (problem2_13_sourceX j)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j)) =
          (1 : ℝ) := by
  rcases problem2_13_sourceX_between_one_two_of_pos_lt_candidateJ hjpos hj
    with ⟨hxlo, hxhi⟩
  exact problem2_12_ieeeDouble_reciprocal_product_rounding_options hxlo hxhi

theorem problem2_13_sourceProduct_mem_window_of_pos_lt_candidateJ {j : ℕ}
    (hjpos : 0 < j) (hj : j < problem2_13_candidateJ) :
    ieeeDoubleFormat.finiteNormalRange (problem2_13_sourceProduct j) ∧
      (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) ≤ problem2_13_sourceProduct j ∧
      problem2_13_sourceProduct j ≤ (1 : ℝ) + (2 : ℝ) ^ (-53 : ℤ) := by
  rcases problem2_13_sourceX_between_one_two_of_pos_lt_candidateJ hjpos hj
    with ⟨hxlo, hxhi⟩
  simpa [problem2_13_sourceProduct] using
    problem2_12_ieeeDouble_reciprocal_product_mem_window_of_one_lt_x_lt_two
      hxlo hxhi

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

theorem problem2_13_sourceX_rounds_to_predecessor_of_sourceProduct_lt_lower_midpoint
    {j : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hlt : problem2_13_sourceProduct j <
      (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ)) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (problem2_13_sourceX j)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j)) =
      (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) := by
  rcases problem2_13_sourceProduct_mem_window_of_pos_lt_candidateJ hjpos hj
    with ⟨hzrange, hzlo, _hzhi⟩
  have hround :
      ieeeDoubleFormat.finiteRoundToEven (problem2_13_sourceProduct j) =
        (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) :=
    problem2_12_ieeeDouble_rounds_to_predecessor_of_mem_lower_half_cell
      hzrange hzlo hlt
  simpa [problem2_13_sourceProduct, finiteRoundToEvenOp] using hround

theorem problem2_13_sourceX_rounds_to_one_of_lower_midpoint_le {j : ℕ}
    (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hmid :
      (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) ≤ problem2_13_sourceProduct j) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (problem2_13_sourceX j)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j)) =
      (1 : ℝ) := by
  rcases problem2_13_sourceProduct_mem_window_of_pos_lt_candidateJ hjpos hj
    with ⟨hzrange, _hzlo, hzhi⟩
  have hround :
      ieeeDoubleFormat.finiteRoundToEven (problem2_13_sourceProduct j) =
        (1 : ℝ) := by
    by_cases hle_one : problem2_13_sourceProduct j ≤ (1 : ℝ)
    · exact problem2_12_ieeeDouble_rounds_to_one_of_mem_lower_middle_half_cell
        hzrange hmid hle_one
    · have hone_le : (1 : ℝ) ≤ problem2_13_sourceProduct j :=
        le_of_lt (lt_of_not_ge hle_one)
      exact problem2_12_ieeeDouble_rounds_to_one_of_mem_upper_half_cell
        hzrange hone_le hzhi
  simpa [problem2_13_sourceProduct, finiteRoundToEvenOp] using hround

theorem problem2_13_sourceX_rounds_to_one_iff_lower_midpoint_le {j : ℕ}
    (hjpos : 0 < j) (hj : j < problem2_13_candidateJ) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (problem2_13_sourceX j)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j)) =
        (1 : ℝ) ↔
      (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) ≤ problem2_13_sourceProduct j := by
  constructor
  · intro hround
    by_contra hnot
    have hlt :
        problem2_13_sourceProduct j <
          (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) := lt_of_not_ge hnot
    have hpred :=
      problem2_13_sourceX_rounds_to_predecessor_of_sourceProduct_lt_lower_midpoint
        hjpos hj hlt
    have hpred_ne_one :
        (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) ≠ (1 : ℝ) := by
      norm_num [zpow_neg]
    have hpred_eq_one :
        (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) = (1 : ℝ) := by
      rw [← hpred, hround]
    exact hpred_ne_one hpred_eq_one
  · exact problem2_13_sourceX_rounds_to_one_of_lower_midpoint_le hjpos hj

theorem problem2_13_sourceX_rounds_to_one_of_reciprocal_scaled_product_ge
    {j k : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hround :
      ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j) =
        (k : ℝ) * (2 : ℝ) ^ (-53 : ℤ))
    (hscaled :
      (2 ^ 105 - 2 ^ 51 : ℕ) ≤ (2 ^ 52 + j) * k) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (problem2_13_sourceX j)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j)) =
      (1 : ℝ) :=
  problem2_13_sourceX_rounds_to_one_of_lower_midpoint_le hjpos hj
    (problem2_13_sourceProduct_lower_midpoint_le_of_scaled_product_ge
      hround hscaled)

theorem problem2_13_sourceX_rounds_to_predecessor_of_reciprocal_scaled_product_lt
    {j k : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hround :
      ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j) =
        (k : ℝ) * (2 : ℝ) ^ (-53 : ℤ))
    (hscaled :
      (2 ^ 52 + j) * k < (2 ^ 105 - 2 ^ 51 : ℕ)) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (problem2_13_sourceX j)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j)) =
      (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) :=
  problem2_13_sourceX_rounds_to_predecessor_of_sourceProduct_lt_lower_midpoint
    hjpos hj
    (problem2_13_sourceProduct_lt_lower_midpoint_of_scaled_product_lt
      hround hscaled)

theorem problem2_13_sourceX_rounds_to_one_iff_reciprocal_scaled_product_ge
    {j k : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hround :
      ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j) =
        (k : ℝ) * (2 : ℝ) ^ (-53 : ℤ)) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (problem2_13_sourceX j)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j)) =
        (1 : ℝ) ↔
      (2 ^ 105 - 2 ^ 51 : ℕ) ≤ (2 ^ 52 + j) * k := by
  constructor
  · intro hone
    by_contra hnot
    have hlt : (2 ^ 52 + j) * k < (2 ^ 105 - 2 ^ 51 : ℕ) :=
      Nat.lt_of_not_ge hnot
    have hpred :=
      problem2_13_sourceX_rounds_to_predecessor_of_reciprocal_scaled_product_lt
        hjpos hj hround hlt
    have hpred_ne_one :
        (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) ≠ (1 : ℝ) := by
      norm_num [zpow_neg]
    have hpred_eq_one :
        (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) = (1 : ℝ) := by
      rw [← hpred, hone]
    exact hpred_ne_one hpred_eq_one
  · exact
      problem2_13_sourceX_rounds_to_one_of_reciprocal_scaled_product_ge
        hjpos hj hround

theorem problem2_13_sourceX_rounds_to_one_of_left_reciprocal_nat_certificate
    {j k : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hm : ieeeDoubleFormat.normalizedMantissa k)
    (hmnext : ieeeDoubleFormat.normalizedMantissa (k + 1))
    (hlo : k * (2 ^ 52 + j) < (2 ^ 105 : ℕ))
    (hhi : (2 ^ 105 : ℕ) < (k + 1) * (2 ^ 52 + j))
    (hmid : (2 ^ 106 : ℕ) < (2 * k + 1) * (2 ^ 52 + j))
    (hscaled : (2 ^ 105 - 2 ^ 51 : ℕ) ≤ (2 ^ 52 + j) * k) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (problem2_13_sourceX j)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j)) =
      (1 : ℝ) := by
  have hround :=
    problem2_13_sourceX_reciprocal_rounds_to_left_of_nat_interval_midpoint
      hjpos hj hm hmnext hlo hhi hmid
  exact
    problem2_13_sourceX_rounds_to_one_of_reciprocal_scaled_product_ge
      hjpos hj hround hscaled

theorem problem2_13_sourceX_rounds_to_one_of_right_reciprocal_nat_certificate
    {j k : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hm : ieeeDoubleFormat.normalizedMantissa k)
    (hmnext : ieeeDoubleFormat.normalizedMantissa (k + 1))
    (hlo : k * (2 ^ 52 + j) < (2 ^ 105 : ℕ))
    (hhi : (2 ^ 105 : ℕ) < (k + 1) * (2 ^ 52 + j))
    (hmid : (2 * k + 1) * (2 ^ 52 + j) < (2 ^ 106 : ℕ))
    (hscaled : (2 ^ 105 - 2 ^ 51 : ℕ) ≤ (2 ^ 52 + j) * (k + 1)) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (problem2_13_sourceX j)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j)) =
      (1 : ℝ) := by
  have hround :=
    problem2_13_sourceX_reciprocal_rounds_to_right_of_nat_interval_midpoint
      hjpos hj hm hmnext hlo hhi hmid
  exact
    problem2_13_sourceX_rounds_to_one_of_reciprocal_scaled_product_ge
      (j := j) (k := k + 1) hjpos hj hround hscaled

theorem problem2_13_sourceX_rounds_to_predecessor_of_left_reciprocal_nat_certificate
    {j k : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hm : ieeeDoubleFormat.normalizedMantissa k)
    (hmnext : ieeeDoubleFormat.normalizedMantissa (k + 1))
    (hlo : k * (2 ^ 52 + j) < (2 ^ 105 : ℕ))
    (hhi : (2 ^ 105 : ℕ) < (k + 1) * (2 ^ 52 + j))
    (hmid : (2 ^ 106 : ℕ) < (2 * k + 1) * (2 ^ 52 + j))
    (hscaled : (2 ^ 52 + j) * k < (2 ^ 105 - 2 ^ 51 : ℕ)) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (problem2_13_sourceX j)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j)) =
      (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) := by
  have hround :=
    problem2_13_sourceX_reciprocal_rounds_to_left_of_nat_interval_midpoint
      hjpos hj hm hmnext hlo hhi hmid
  exact
    problem2_13_sourceX_rounds_to_predecessor_of_reciprocal_scaled_product_lt
      hjpos hj hround hscaled

theorem problem2_13_sourceX_rounds_to_predecessor_of_right_reciprocal_nat_certificate
    {j k : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hm : ieeeDoubleFormat.normalizedMantissa k)
    (hmnext : ieeeDoubleFormat.normalizedMantissa (k + 1))
    (hlo : k * (2 ^ 52 + j) < (2 ^ 105 : ℕ))
    (hhi : (2 ^ 105 : ℕ) < (k + 1) * (2 ^ 52 + j))
    (hmid : (2 * k + 1) * (2 ^ 52 + j) < (2 ^ 106 : ℕ))
    (hscaled : (2 ^ 52 + j) * (k + 1) < (2 ^ 105 - 2 ^ 51 : ℕ)) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (problem2_13_sourceX j)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j)) =
      (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) := by
  have hround :=
    problem2_13_sourceX_reciprocal_rounds_to_right_of_nat_interval_midpoint
      hjpos hj hm hmnext hlo hhi hmid
  exact
    problem2_13_sourceX_rounds_to_predecessor_of_reciprocal_scaled_product_lt
      (j := j) (k := k + 1) hjpos hj hround hscaled

theorem problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quotient_certificate
    {j : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hrem : (2 ^ 105 : ℕ) % (2 ^ 52 + j) ≠ 0)
    (hm :
      ieeeDoubleFormat.normalizedMantissa
        (problem2_13_reciprocalCellQuotient j))
    (hmnext :
      ieeeDoubleFormat.normalizedMantissa
        (problem2_13_reciprocalCellQuotient j + 1))
    (hmid :
      (2 ^ 106 : ℕ) <
        (2 * problem2_13_reciprocalCellQuotient j + 1) *
          (2 ^ 52 + j))
    (hscaled :
      (2 ^ 105 - 2 ^ 51 : ℕ) ≤
        (2 ^ 52 + j) * problem2_13_reciprocalCellQuotient j) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (problem2_13_sourceX j)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j)) =
      (1 : ℝ) := by
  have hround :=
    problem2_13_sourceX_reciprocal_rounds_to_left_of_quotient_midpoint
      hjpos hj hrem hm hmnext hmid
  exact
    problem2_13_sourceX_rounds_to_one_of_reciprocal_scaled_product_ge
      hjpos hj hround hscaled

theorem problem2_13_sourceX_rounds_to_one_of_right_reciprocal_quotient_certificate
    {j : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hrem : (2 ^ 105 : ℕ) % (2 ^ 52 + j) ≠ 0)
    (hm :
      ieeeDoubleFormat.normalizedMantissa
        (problem2_13_reciprocalCellQuotient j))
    (hmnext :
      ieeeDoubleFormat.normalizedMantissa
        (problem2_13_reciprocalCellQuotient j + 1))
    (hmid :
      (2 * problem2_13_reciprocalCellQuotient j + 1) *
          (2 ^ 52 + j) <
        (2 ^ 106 : ℕ))
    (hscaled :
      (2 ^ 105 - 2 ^ 51 : ℕ) ≤
        (2 ^ 52 + j) * (problem2_13_reciprocalCellQuotient j + 1)) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (problem2_13_sourceX j)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j)) =
      (1 : ℝ) := by
  have hround :=
    problem2_13_sourceX_reciprocal_rounds_to_right_of_quotient_midpoint
      hjpos hj hrem hm hmnext hmid
  exact
    problem2_13_sourceX_rounds_to_one_of_reciprocal_scaled_product_ge
      (j := j) (k := problem2_13_reciprocalCellQuotient j + 1)
      hjpos hj hround hscaled

theorem
    problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quotient_integer_certificate
    {j : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hrem : (2 ^ 105 : ℕ) % (2 ^ 52 + j) ≠ 0)
    (hmid :
      (2 ^ 106 : ℕ) <
        (2 * problem2_13_reciprocalCellQuotient j + 1) *
          (2 ^ 52 + j))
    (hscaled :
      (2 ^ 105 - 2 ^ 51 : ℕ) ≤
        (2 ^ 52 + j) * problem2_13_reciprocalCellQuotient j) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (problem2_13_sourceX j)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j)) =
      (1 : ℝ) := by
  rcases
      problem2_13_reciprocalCellQuotient_normalizedMantissas_of_pos_lt_candidateJ
        hjpos hj with ⟨hm, hmnext⟩
  exact
    problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quotient_certificate
      hjpos hj hrem hm hmnext hmid hscaled

theorem
    problem2_13_sourceX_rounds_to_one_of_right_reciprocal_quotient_integer_certificate
    {j : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hrem : (2 ^ 105 : ℕ) % (2 ^ 52 + j) ≠ 0)
    (hmid :
      (2 * problem2_13_reciprocalCellQuotient j + 1) *
          (2 ^ 52 + j) <
        (2 ^ 106 : ℕ))
    (hscaled :
      (2 ^ 105 - 2 ^ 51 : ℕ) ≤
        (2 ^ 52 + j) * (problem2_13_reciprocalCellQuotient j + 1)) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (problem2_13_sourceX j)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j)) =
      (1 : ℝ) := by
  rcases
      problem2_13_reciprocalCellQuotient_normalizedMantissas_of_pos_lt_candidateJ
        hjpos hj with ⟨hm, hmnext⟩
  exact
    problem2_13_sourceX_rounds_to_one_of_right_reciprocal_quotient_certificate
      hjpos hj hrem hm hmnext hmid hscaled

theorem
    problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quotient_remainder_certificate
    {j : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hrem : (2 ^ 105 : ℕ) % (2 ^ 52 + j) ≠ 0)
    (hrem_lt :
      2 * ((2 ^ 105 : ℕ) % (2 ^ 52 + j)) < 2 ^ 52 + j)
    (hscaled :
      (2 ^ 105 - 2 ^ 51 : ℕ) ≤
        (2 ^ 52 + j) * problem2_13_reciprocalCellQuotient j) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (problem2_13_sourceX j)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j)) =
      (1 : ℝ) := by
  exact
    problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quotient_integer_certificate
      hjpos hj hrem
      (problem2_13_reciprocalCellQuotient_midpoint_left_of_twice_remainder_lt
        hrem_lt)
      hscaled

theorem
    problem2_13_sourceX_rounds_to_one_of_right_reciprocal_quotient_remainder_certificate
    {j : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hrem : (2 ^ 105 : ℕ) % (2 ^ 52 + j) ≠ 0)
    (hrem_gt :
      2 ^ 52 + j < 2 * ((2 ^ 105 : ℕ) % (2 ^ 52 + j)))
    (hscaled :
      (2 ^ 105 - 2 ^ 51 : ℕ) ≤
        (2 ^ 52 + j) * (problem2_13_reciprocalCellQuotient j + 1)) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (problem2_13_sourceX j)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j)) =
      (1 : ℝ) := by
  exact
    problem2_13_sourceX_rounds_to_one_of_right_reciprocal_quotient_integer_certificate
      hjpos hj hrem
      (problem2_13_reciprocalCellQuotient_midpoint_right_of_denominator_lt_twice_remainder
        hrem_gt)
      hscaled

theorem
    problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quotient_remainder_le_threshold
    {j : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hrem : (2 ^ 105 : ℕ) % (2 ^ 52 + j) ≠ 0)
    (hrem_lt :
      2 * ((2 ^ 105 : ℕ) % (2 ^ 52 + j)) < 2 ^ 52 + j)
    (hrem_le : ((2 ^ 105 : ℕ) % (2 ^ 52 + j)) ≤ 2 ^ 51) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (problem2_13_sourceX j)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j)) =
      (1 : ℝ) := by
  exact
    problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quotient_remainder_certificate
      hjpos hj hrem hrem_lt
      (problem2_13_reciprocalCellQuotient_scaled_product_left_ge_of_remainder_le
        hrem_le)

theorem
    problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quotient_remainder_lt_half_le_threshold
    {j : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hrem_lt :
      2 * ((2 ^ 105 : ℕ) % (2 ^ 52 + j)) < 2 ^ 52 + j)
    (hrem_le : ((2 ^ 105 : ℕ) % (2 ^ 52 + j)) ≤ 2 ^ 51) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (problem2_13_sourceX j)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j)) =
      (1 : ℝ) := by
  exact
    problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quotient_remainder_le_threshold
      hjpos hj
      (problem2_13_reciprocalCellQuotient_remainder_ne_zero_of_pos_lt_candidateJ
        hjpos hj)
      hrem_lt hrem_le

theorem
    problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quadraticQuotient_eq_29
    {j : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hrem_lt :
      2 * ((2 ^ 105 : ℕ) % (2 ^ 52 + j)) < 2 ^ 52 + j)
    (hs : problem2_13_quadraticRemainderQuotient j = 29) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (problem2_13_sourceX j)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j)) =
      (1 : ℝ) := by
  exact
    problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quotient_remainder_lt_half_le_threshold
      hjpos hj hrem_lt
      (problem2_13_reciprocalCellQuotient_remainder_le_threshold_of_quadraticQuotient_eq_29
        hj hs)

theorem
    problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quadraticQuotient_le_28
    {j : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hrem_lt :
      2 * ((2 ^ 105 : ℕ) % (2 ^ 52 + j)) < 2 ^ 52 + j)
    (hs : problem2_13_quadraticRemainderQuotient j ≤ 28) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (problem2_13_sourceX j)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j)) =
      (1 : ℝ) := by
  exact
    problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quotient_remainder_lt_half_le_threshold
      hjpos hj hrem_lt
      (problem2_13_reciprocalCellQuotient_remainder_le_threshold_of_quadraticQuotient_le_28_of_left
        hj hs hrem_lt)

theorem
    problem2_13_sourceX_rounds_to_one_of_right_reciprocal_quotient_remainder_gt_half
    {j : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hrem_gt :
      2 ^ 52 + j < 2 * ((2 ^ 105 : ℕ) % (2 ^ 52 + j))) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (problem2_13_sourceX j)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j)) =
      (1 : ℝ) := by
  have hrem : (2 ^ 105 : ℕ) % (2 ^ 52 + j) ≠ 0 := by
    intro hzero
    omega
  exact
    problem2_13_sourceX_rounds_to_one_of_right_reciprocal_quotient_remainder_certificate
      hjpos hj hrem hrem_gt
      problem2_13_reciprocalCellQuotient_scaled_product_right_ge

theorem problem2_13_sourceX_rounds_to_one_of_quadraticQuotient_le_28
    {j : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hs : problem2_13_quadraticRemainderQuotient j ≤ 28) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (problem2_13_sourceX j)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j)) =
      (1 : ℝ) := by
  rcases
      problem2_13_reciprocalCellQuotient_remainder_half_trichotomy_of_pos_lt_candidateJ
        hjpos hj with hrem_lt | hrem_gt
  · exact
      problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quadraticQuotient_le_28
        hjpos hj hrem_lt hs
  · exact
      problem2_13_sourceX_rounds_to_one_of_right_reciprocal_quotient_remainder_gt_half
        hjpos hj hrem_gt

theorem problem2_13_sourceX_rounds_to_one_of_quadraticQuotient_eq_29
    {j : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ)
    (hs : problem2_13_quadraticRemainderQuotient j = 29) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (problem2_13_sourceX j)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j)) =
      (1 : ℝ) := by
  rcases
      problem2_13_reciprocalCellQuotient_remainder_half_trichotomy_of_pos_lt_candidateJ
        hjpos hj with hrem_lt | hrem_gt
  · exact
      problem2_13_sourceX_rounds_to_one_of_left_reciprocal_quadraticQuotient_eq_29
        hjpos hj hrem_lt hs
  · exact
      problem2_13_sourceX_rounds_to_one_of_right_reciprocal_quotient_remainder_gt_half
        hjpos hj hrem_gt

theorem problem2_13_sourceX_rounds_to_one_of_pos_lt_candidateJ
    {j : ℕ} (hjpos : 0 < j) (hj : j < problem2_13_candidateJ) :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul (problem2_13_sourceX j)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX j)) =
      (1 : ℝ) := by
  have hsle29 :=
    problem2_13_quadraticRemainderQuotient_le_29_of_lt_candidateJ
      (j := j) hj
  by_cases hsle28 : problem2_13_quadraticRemainderQuotient j ≤ 28
  · exact problem2_13_sourceX_rounds_to_one_of_quadraticQuotient_le_28
      hjpos hj hsle28
  · have hs29 : problem2_13_quadraticRemainderQuotient j = 29 := by
      omega
    exact problem2_13_sourceX_rounds_to_one_of_quadraticQuotient_eq_29
      hjpos hj hs29

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

/-- For the Problem 2.13 candidate, the rounded reciprocal is the lower
IEEE-double endpoint with mantissa `9007198739268041`. -/
theorem problem2_13_candidate_reciprocal_rounds_to_lower :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
        (1 : ℝ) problem2_13_candidateX =
      (9007198739268041 : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
  let fmt := ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false 9007198739268041 0
  let b : ℝ := fmt.normalizedValue false 9007198739268042 0
  let x : ℝ := (1 : ℝ) / problem2_13_candidateX
  have hmx : fmt.normalizedMantissa 9007198739268041 := by
    norm_num [fmt, ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (9007198739268041 + 1) := by
    norm_num [fmt, ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 9007198739268041, (0 : ℤ), hmx, hmnext,
        Or.inl ⟨rfl, rfl⟩⟩
  have ha_value :
      a = (9007198739268041 : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [a, fmt, ieeeDoubleFormat, normalizedValue, signValue, betaR,
      zpow_neg]
  have hb_value :
      b = (9007198739268042 : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, ieeeDoubleFormat, normalizedValue, signValue, betaR,
      zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rcases problem2_13_candidateX_between_one_two with ⟨hxlo, hxhi⟩
    simpa [x, fmt] using
      (problem2_12_ieeeDouble_reciprocal_finiteNormalRange_of_one_lt_x_lt_two
        hxlo hxhi)
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, problem2_13_candidateX, problem2_13_candidateJ, zpow_neg]
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value]
    norm_num [x, problem2_13_candidateX, problem2_13_candidateJ, zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  change fmt.finiteRoundToEven ((1 : ℝ) / problem2_13_candidateX) =
    (9007198739268041 : ℝ) * (2 : ℝ) ^ (-53 : ℤ)
  simpa [x, fmt, ha_value] using hround

theorem problem2_13_candidate_reciprocal_product_eq :
    problem2_13_candidateX *
        ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) problem2_13_candidateX =
      (1 : ℝ) - (2251799886937606 : ℝ) * (2 : ℝ) ^ (-105 : ℤ) := by
  rw [problem2_13_candidate_reciprocal_rounds_to_lower]
  norm_num [problem2_13_candidateX, problem2_13_candidateJ, zpow_neg]

theorem problem2_13_sourceProduct_candidateJ :
    problem2_13_sourceProduct problem2_13_candidateJ =
      (1 : ℝ) - (2251799886937606 : ℝ) * (2 : ℝ) ^ (-105 : ℤ) := by
  simpa [problem2_13_sourceProduct, problem2_13_sourceX_candidateJ] using
    problem2_13_candidate_reciprocal_product_eq

theorem problem2_13_sourceProduct_candidateJ_mem_window :
    ieeeDoubleFormat.finiteNormalRange (problem2_13_sourceProduct problem2_13_candidateJ) ∧
      (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) ≤
        problem2_13_sourceProduct problem2_13_candidateJ ∧
      problem2_13_sourceProduct problem2_13_candidateJ ≤
        (1 : ℝ) + (2 : ℝ) ^ (-53 : ℤ) := by
  rcases problem2_13_candidateX_between_one_two with ⟨hxlo, hxhi⟩
  simpa [problem2_13_sourceProduct, problem2_13_sourceX_candidateJ] using
    problem2_12_ieeeDouble_reciprocal_product_mem_window_of_one_lt_x_lt_two
      hxlo hxhi

theorem problem2_13_candidate_sourceProduct_lt_lower_midpoint :
    problem2_13_sourceProduct problem2_13_candidateJ <
      (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) := by
  rw [problem2_13_sourceProduct_candidateJ]
  norm_num [zpow_neg]

theorem problem2_13_candidate_scaled_product_lt_lower_midpoint_threshold :
    (2 ^ 52 + problem2_13_candidateJ) * 9007198739268041 <
      (2 ^ 105 - 2 ^ 51 : ℕ) := by
  norm_num [problem2_13_candidateJ]

theorem problem2_13_candidate_rounds_to_predecessor_of_sourceProduct_lower_midpoint :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul
        (problem2_13_sourceX problem2_13_candidateJ)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX problem2_13_candidateJ)) =
      (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) := by
  rcases problem2_13_sourceProduct_candidateJ_mem_window with
    ⟨hzrange, hzlo, _hzhi⟩
  have hround :
      ieeeDoubleFormat.finiteRoundToEven
          (problem2_13_sourceProduct problem2_13_candidateJ) =
        (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) :=
    problem2_12_ieeeDouble_rounds_to_predecessor_of_mem_lower_half_cell
      hzrange hzlo problem2_13_candidate_sourceProduct_lt_lower_midpoint
  simpa [problem2_13_sourceProduct, finiteRoundToEvenOp] using hround

/-- The immediately preceding `j` still rounds its reciprocal downward, but
not far enough to make the final product leave `1`'s round-to-even cell. -/
theorem problem2_13_predecessor_reciprocal_rounds_to_lower :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
        (1 : ℝ) problem2_13_predecessorX =
      (9007198739268043 : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
  let fmt := ieeeDoubleFormat
  let a : ℝ := fmt.normalizedValue false 9007198739268043 0
  let b : ℝ := fmt.normalizedValue false 9007198739268044 0
  let x : ℝ := (1 : ℝ) / problem2_13_predecessorX
  have hmx : fmt.normalizedMantissa 9007198739268043 := by
    norm_num [fmt, ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  have hmnext : fmt.normalizedMantissa (9007198739268043 + 1) := by
    norm_num [fmt, ieeeDoubleFormat, normalizedMantissa, mantissaInRange,
      minNormalMantissa]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
      ⟨false, 9007198739268043, (0 : ℤ), hmx, hmnext,
        Or.inl ⟨rfl, rfl⟩⟩
  have ha_value :
      a = (9007198739268043 : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [a, fmt, ieeeDoubleFormat, normalizedValue, signValue, betaR,
      zpow_neg]
  have hb_value :
      b = (9007198739268044 : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
    norm_num [b, fmt, ieeeDoubleFormat, normalizedValue, signValue, betaR,
      zpow_neg]
  have hxrange : fmt.finiteNormalRange x := by
    rcases problem2_13_predecessorX_between_one_two with ⟨hxlo, hxhi⟩
    simpa [x, fmt] using
      (problem2_12_ieeeDouble_reciprocal_finiteNormalRange_of_one_lt_x_lt_two
        hxlo hxhi)
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, problem2_13_predecessorX, problem2_13_predecessorJ, zpow_neg]
  have hpolicy :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hxrange
  have hleftCloser : |x - a| < |x - b| := by
    rw [ha_value, hb_value]
    norm_num [x, problem2_13_predecessorX, problem2_13_predecessorJ, zpow_neg]
  have hround : fmt.finiteRoundToEven x = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  change fmt.finiteRoundToEven ((1 : ℝ) / problem2_13_predecessorX) =
    (9007198739268043 : ℝ) * (2 : ℝ) ^ (-53 : ℤ)
  simpa [x, fmt, ha_value] using hround

theorem problem2_13_predecessor_scaled_product_ge_lower_midpoint_threshold :
    (2 ^ 105 - 2 ^ 51 : ℕ) ≤
      (2 ^ 52 + problem2_13_predecessorJ) * 9007198739268043 := by
  norm_num [problem2_13_predecessorJ]

theorem problem2_13_predecessor_reciprocal_product_eq :
    problem2_13_predecessorX *
        ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) problem2_13_predecessorX =
      (1 : ℝ) - (2251798855991677 : ℝ) * (2 : ℝ) ^ (-105 : ℤ) := by
  rw [problem2_13_predecessor_reciprocal_rounds_to_lower]
  norm_num [problem2_13_predecessorX, problem2_13_predecessorJ, zpow_neg]

theorem problem2_13_sourceProduct_predecessorJ :
    problem2_13_sourceProduct problem2_13_predecessorJ =
      (1 : ℝ) - (2251798855991677 : ℝ) * (2 : ℝ) ^ (-105 : ℤ) := by
  simpa [problem2_13_sourceProduct, problem2_13_sourceX_predecessorJ] using
    problem2_13_predecessor_reciprocal_product_eq

theorem problem2_13_predecessor_sourceProduct_lower_midpoint_le :
    (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) ≤
      problem2_13_sourceProduct problem2_13_predecessorJ := by
  rw [problem2_13_sourceProduct_predecessorJ]
  norm_num [zpow_neg]

theorem problem2_13_predecessor_rounds_to_one_of_sourceProduct_lower_midpoint :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul
        (problem2_13_sourceX problem2_13_predecessorJ)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX problem2_13_predecessorJ)) =
      (1 : ℝ) :=
  problem2_13_sourceX_rounds_to_one_of_lower_midpoint_le
    (by norm_num [problem2_13_predecessorJ])
    (by norm_num [problem2_13_predecessorJ, problem2_13_candidateJ])
    problem2_13_predecessor_sourceProduct_lower_midpoint_le

theorem problem2_13_predecessor_rounds_to_one_of_scaled_product_certificate :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul
        (problem2_13_sourceX problem2_13_predecessorJ)
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX problem2_13_predecessorJ)) =
      (1 : ℝ) := by
  have hround :
      ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) (problem2_13_sourceX problem2_13_predecessorJ) =
        (9007198739268043 : ℝ) * (2 : ℝ) ^ (-53 : ℤ) := by
    simpa [problem2_13_sourceX_predecessorJ] using
      problem2_13_predecessor_reciprocal_rounds_to_lower
  exact
    problem2_13_sourceX_rounds_to_one_of_reciprocal_scaled_product_ge
      (by norm_num [problem2_13_predecessorJ])
      (by norm_num [problem2_13_predecessorJ, problem2_13_candidateJ])
      hround
      problem2_13_predecessor_scaled_product_ge_lower_midpoint_threshold

/-- The Problem 2.13 candidate product is in the lower half-cell below `1`,
so the final round-to-even result is the predecessor of `1`. -/
theorem problem2_13_candidate_rounds_to_predecessor :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul problem2_13_candidateX
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) problem2_13_candidateX) =
      (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) := by
  let z : ℝ :=
    problem2_13_candidateX *
      ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
        (1 : ℝ) problem2_13_candidateX
  have hz_eq :
      z =
        (1 : ℝ) - (2251799886937606 : ℝ) * (2 : ℝ) ^ (-105 : ℤ) := by
    simpa [z] using problem2_13_candidate_reciprocal_product_eq
  have hzrange : ieeeDoubleFormat.finiteNormalRange z := by
    have hzpos : 0 < z := by
      rw [hz_eq]
      norm_num [zpow_neg]
    rw [finiteNormalRange, abs_of_pos hzpos]
    constructor
    · have hhalf : (1 / 2 : ℝ) ≤ z := by
        rw [hz_eq]
        norm_num [zpow_neg]
      exact le_trans problem2_13_ieeeDoubleFormat_minNormalMagnitude_le_half
        hhalf
    · have hle_two : z ≤ (2 : ℝ) := by
        rw [hz_eq]
        norm_num [zpow_neg]
      exact le_trans hle_two
        (le_trans (by norm_num : (2 : ℝ) ≤ 4)
          problem2_13_four_le_ieeeDoubleFormat_maxFiniteMagnitude)
  have hlo : (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ) ≤ z := by
    rw [hz_eq]
    norm_num [zpow_neg]
  have hhi : z < (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) := by
    rw [hz_eq]
    norm_num [zpow_neg]
  change ieeeDoubleFormat.finiteRoundToEven z =
    (1 : ℝ) - (2 : ℝ) ^ (-53 : ℤ)
  exact
    problem2_12_ieeeDouble_rounds_to_predecessor_of_mem_lower_half_cell
      hzrange hlo hhi

theorem problem2_13_candidate_rounds_ne_one :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul problem2_13_candidateX
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) problem2_13_candidateX) ≠ (1 : ℝ) := by
  rw [problem2_13_candidate_rounds_to_predecessor]
  norm_num [zpow_neg]

theorem problem2_13_predecessor_rounds_to_one :
    ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul problem2_13_predecessorX
        (ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
          (1 : ℝ) problem2_13_predecessorX) =
      (1 : ℝ) := by
  let z : ℝ :=
    problem2_13_predecessorX *
      ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
        (1 : ℝ) problem2_13_predecessorX
  have hz_eq :
      z =
        (1 : ℝ) - (2251798855991677 : ℝ) * (2 : ℝ) ^ (-105 : ℤ) := by
    simpa [z] using problem2_13_predecessor_reciprocal_product_eq
  have hzrange : ieeeDoubleFormat.finiteNormalRange z := by
    have hzpos : 0 < z := by
      rw [hz_eq]
      norm_num [zpow_neg]
    rw [finiteNormalRange, abs_of_pos hzpos]
    constructor
    · have hhalf : (1 / 2 : ℝ) ≤ z := by
        rw [hz_eq]
        norm_num [zpow_neg]
      exact le_trans problem2_13_ieeeDoubleFormat_minNormalMagnitude_le_half
        hhalf
    · have hle_two : z ≤ (2 : ℝ) := by
        rw [hz_eq]
        norm_num [zpow_neg]
      exact le_trans hle_two
        (le_trans (by norm_num : (2 : ℝ) ≤ 4)
          problem2_13_four_le_ieeeDoubleFormat_maxFiniteMagnitude)
  have hlo : (1 : ℝ) - (2 : ℝ) ^ (-54 : ℤ) ≤ z := by
    rw [hz_eq]
    norm_num [zpow_neg]
  have hhi : z ≤ (1 : ℝ) := by
    rw [hz_eq]
    norm_num [zpow_neg]
  change ieeeDoubleFormat.finiteRoundToEven z = (1 : ℝ)
  exact
    problem2_12_ieeeDouble_rounds_to_one_of_mem_lower_middle_half_cell
      hzrange hlo hhi

end FloatingPointFormat

end

end NumStability
