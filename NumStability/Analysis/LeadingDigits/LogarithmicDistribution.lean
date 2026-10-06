/-
SPDX-License-Identifier: MIT
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import NumStability.Analysis.FiniteProbability

namespace NumStability

open scoped BigOperators

/-!
# Logarithmic leading-digit distribution

Higham Chapter 2, Section 2.5 defines the logarithmic distribution by the
property that the proportion of base `beta` numbers with leading significant
digit `n` is `log_beta ((n+1)/n)`.  This file records that source-facing law as
a reusable finite probability distribution on the leading digits
`1, ..., beta-1`. Exact Higham source conclusions live below
`NumStability.Source.Higham`.
-/

noncomputable section

/-- The leading digit represented by an index in `Fin (beta - 1)`. -/
def leadingDigitOfIndex (beta : ℕ) (i : Fin (beta - 1)) : ℕ :=
  i.val + 1

/-- Higham §2.5's logarithmic mass for leading digit `n` in base `beta`.

The definition uses the telescoping form `log(n+1)-log(n)`, while
`logarithmicLeadingDigitMass_eq_log_div` exposes the displayed
`log_beta((n+1)/n)` form. -/
def logarithmicLeadingDigitMass (beta n : ℕ) : ℝ :=
  (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) / Real.log (beta : ℝ)

/-- Logarithmic mass of a positive interval `[lo, hi]` in base `beta`.

This is the interval form behind the leading-digit atoms. -/
def logarithmicIntervalMass (beta : ℕ) (lo hi : ℝ) : ℝ :=
  (Real.log hi - Real.log lo) / Real.log (beta : ℝ)

theorem leadingDigitOfIndex_pos {beta : ℕ} (i : Fin (beta - 1)) :
    0 < leadingDigitOfIndex beta i := by
  simp [leadingDigitOfIndex]

theorem leadingDigitOfIndex_lt_base {beta : ℕ} (hbeta : 1 < beta)
    (i : Fin (beta - 1)) :
    leadingDigitOfIndex beta i < beta := by
  have hsucc : i.val + 1 < beta - 1 + 1 := Nat.succ_lt_succ i.isLt
  have hbase : beta - 1 + 1 = beta := Nat.sub_add_cancel (le_of_lt hbeta)
  unfold leadingDigitOfIndex
  rwa [hbase] at hsucc

theorem logarithmicLeadingDigitMass_eq_log_div {beta n : ℕ} (hn : 0 < n) :
    logarithmicLeadingDigitMass beta n =
      Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) / Real.log (beta : ℝ) := by
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hn1_ne : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero n)
  unfold logarithmicLeadingDigitMass
  rw [Real.log_div hn1_ne hn_ne]

/-- Source-facing form of the logarithmic leading-digit mass:
`log_beta (1 + 1/n)`. -/
theorem logarithmicLeadingDigitMass_eq_log_one_add_inv {beta n : ℕ}
    (hn : 0 < n) :
    logarithmicLeadingDigitMass beta n =
      Real.log (1 + (1 : ℝ) / (n : ℝ)) / Real.log (beta : ℝ) := by
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hratio :
      (((n + 1 : ℕ) : ℝ) / (n : ℝ)) =
        1 + (1 : ℝ) / (n : ℝ) := by
    calc
      (((n + 1 : ℕ) : ℝ) / (n : ℝ))
          = ((n : ℝ) + 1) / (n : ℝ) := by norm_num
      _ = (n : ℝ) / (n : ℝ) + (1 : ℝ) / (n : ℝ) := by
            rw [add_div]
      _ = 1 + (1 : ℝ) / (n : ℝ) := by
            rw [div_self hn_ne]
  rw [logarithmicLeadingDigitMass_eq_log_div hn, hratio]

theorem logarithmicLeadingDigitMass_eq_intervalMass {beta n : ℕ} :
    logarithmicLeadingDigitMass beta n =
      logarithmicIntervalMass beta (n : ℝ) ((n + 1 : ℕ) : ℝ) := by
  rfl

/-- Logarithmic interval mass is invariant under multiplication by a natural
power of the base.  This is the algebraic scale-invariance surface used in
Higham's discussion of logarithmic leading-digit laws. -/
theorem logarithmicIntervalMass_mul_base_pow {beta : ℕ}
    (hbeta : 1 < beta) (k : ℕ) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 < hi) :
    logarithmicIntervalMass beta (((beta : ℝ) ^ k) * lo)
        (((beta : ℝ) ^ k) * hi) =
      logarithmicIntervalMass beta lo hi := by
  have hbeta_pos : (0 : ℝ) < beta := by
    exact_mod_cast (Nat.lt_trans Nat.zero_lt_one hbeta)
  have hscale_ne : ((beta : ℝ) ^ k) ≠ 0 :=
    pow_ne_zero k (ne_of_gt hbeta_pos)
  have hlo_ne : lo ≠ 0 := ne_of_gt hlo
  have hhi_ne : hi ≠ 0 := ne_of_gt hhi
  unfold logarithmicIntervalMass
  rw [Real.log_mul hscale_ne hhi_ne, Real.log_mul hscale_ne hlo_ne]
  ring

/-- Logarithmic interval mass is invariant under multiplication by any integer
power of the base. -/
theorem logarithmicIntervalMass_mul_base_zpow {beta : ℕ}
    (hbeta : 1 < beta) (k : ℤ) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 < hi) :
    logarithmicIntervalMass beta (((beta : ℝ) ^ k) * lo)
        (((beta : ℝ) ^ k) * hi) =
      logarithmicIntervalMass beta lo hi := by
  have hbeta_pos : (0 : ℝ) < beta := by
    exact_mod_cast (Nat.lt_trans Nat.zero_lt_one hbeta)
  have hscale_pos : 0 < ((beta : ℝ) ^ k) := zpow_pos hbeta_pos k
  have hscale_ne : ((beta : ℝ) ^ k) ≠ 0 := ne_of_gt hscale_pos
  have hlo_ne : lo ≠ 0 := ne_of_gt hlo
  have hhi_ne : hi ≠ 0 := ne_of_gt hhi
  unfold logarithmicIntervalMass
  rw [Real.log_mul hscale_ne hhi_ne, Real.log_mul hscale_ne hlo_ne]
  ring

theorem logarithmicLeadingDigitMass_scaled_bin {beta n : ℕ}
    (hbeta : 1 < beta) (hn : 0 < n) (k : ℕ) :
    logarithmicIntervalMass beta (((beta : ℝ) ^ k) * (n : ℝ))
        (((beta : ℝ) ^ k) * ((n + 1 : ℕ) : ℝ)) =
      logarithmicLeadingDigitMass beta n := by
  rw [logarithmicIntervalMass_mul_base_pow hbeta k
    (by exact_mod_cast hn)
    (by exact_mod_cast (Nat.succ_pos n))]
  exact (logarithmicLeadingDigitMass_eq_intervalMass (beta := beta) (n := n)).symm

theorem logarithmicLeadingDigitMass_scaled_bin_zpow {beta n : ℕ}
    (hbeta : 1 < beta) (hn : 0 < n) (k : ℤ) :
    logarithmicIntervalMass beta (((beta : ℝ) ^ k) * (n : ℝ))
        (((beta : ℝ) ^ k) * ((n + 1 : ℕ) : ℝ)) =
      logarithmicLeadingDigitMass beta n := by
  rw [logarithmicIntervalMass_mul_base_zpow hbeta k
    (by exact_mod_cast hn)
    (by exact_mod_cast (Nat.succ_pos n))]
  exact (logarithmicLeadingDigitMass_eq_intervalMass (beta := beta) (n := n)).symm

theorem logarithmicLeadingDigitMass_nonneg {beta n : ℕ}
    (hbeta : 1 < beta) (hn : 0 < n) :
    0 ≤ logarithmicLeadingDigitMass beta n := by
  have hnum_nonneg :
      0 ≤ Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    have hle_nat : n ≤ n + 1 := Nat.le_succ n
    have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hle_nat
    exact sub_nonneg.mpr (Real.log_le_log hn_pos hle)
  have hden_pos : 0 < Real.log (beta : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hbeta)
  exact div_nonneg hnum_nonneg hden_pos.le

/-- The logarithmic leading-digit masses strictly decrease as the leading digit
increases.  This formalizes the source observation that the leading digits are
not equally likely under the logarithmic law. -/
theorem logarithmicLeadingDigitMass_succ_lt {beta n : ℕ}
    (hbeta : 1 < beta) (hn : 0 < n) :
    logarithmicLeadingDigitMass beta (n + 1) <
      logarithmicLeadingDigitMass beta n := by
  have hden_pos : 0 < Real.log (beta : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hbeta)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos n
  have hn2_pos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos (n + 1)
  have hratio :
      (((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) <
        (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
    rw [div_lt_div_iff₀ hn1_pos hn_pos]
    norm_num
    nlinarith
  have hlog :
      Real.log (((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) <
        Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
    exact Real.log_lt_log (div_pos hn2_pos hn1_pos) hratio
  rw [logarithmicLeadingDigitMass_eq_log_div (Nat.succ_pos n),
    logarithmicLeadingDigitMass_eq_log_div hn]
  exact div_lt_div_of_pos_right hlog hden_pos

theorem sum_logarithmicLeadingDigitMass_eq_one {beta : ℕ}
    (hbeta : 1 < beta) :
    (∑ i : Fin (beta - 1),
        logarithmicLeadingDigitMass beta (leadingDigitOfIndex beta i)) = 1 := by
  classical
  have hbeta_sub_pos : 0 < beta - 1 := Nat.sub_pos_of_lt hbeta
  have hden_ne : Real.log (beta : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by exact_mod_cast hbeta))
  have hsum_range :
      (Finset.range (beta - 1)).sum (fun k =>
          (Real.log (((k + 1) + 1 : ℕ) : ℝ) -
            Real.log ((k + 1 : ℕ) : ℝ))) =
        Real.log (beta : ℝ) := by
    calc
      (Finset.range (beta - 1)).sum (fun k =>
          (Real.log (((k + 1) + 1 : ℕ) : ℝ) -
            Real.log ((k + 1 : ℕ) : ℝ)))
          = Real.log (((beta - 1) + 1 : ℕ) : ℝ) - Real.log ((1 : ℕ) : ℝ) := by
              simpa [Nat.succ_eq_add_one] using
                (Finset.sum_range_sub (fun k : ℕ => Real.log ((k + 1 : ℕ) : ℝ)) (beta - 1))
      _ = Real.log (beta : ℝ) := by
              rw [Nat.sub_add_cancel (le_of_lt hbeta), Nat.cast_one, Real.log_one,
                sub_zero]
  calc
    (∑ i : Fin (beta - 1),
        logarithmicLeadingDigitMass beta (leadingDigitOfIndex beta i))
        = (Finset.range (beta - 1)).sum (fun k =>
            logarithmicLeadingDigitMass beta (k + 1)) := by
            simpa [leadingDigitOfIndex] using
              (Fin.sum_univ_eq_sum_range
                (fun k => logarithmicLeadingDigitMass beta (k + 1)) (beta - 1))
    _ = (Finset.range (beta - 1)).sum (fun k =>
          (Real.log (((k + 1) + 1 : ℕ) : ℝ) -
            Real.log ((k + 1 : ℕ) : ℝ)) / Real.log (beta : ℝ)) := by
            apply Finset.sum_congr rfl
            intro k hk
            rfl
    _ = Real.log (beta : ℝ) / Real.log (beta : ℝ) := by
            simp_rw [div_eq_mul_inv]
            rw [← Finset.sum_mul, hsum_range]
    _ = 1 := div_self hden_ne

/-- The finite probability law on leading digits `1, ..., beta-1` whose atom
at digit `n` is `log_beta((n+1)/n)`. -/
def logarithmicLeadingDigitProbability (beta : ℕ) (hbeta : 1 < beta) :
    FiniteProbability (Fin (beta - 1)) where
  prob i := logarithmicLeadingDigitMass beta (leadingDigitOfIndex beta i)
  prob_nonneg i :=
    logarithmicLeadingDigitMass_nonneg hbeta (leadingDigitOfIndex_pos i)
  prob_sum := sum_logarithmicLeadingDigitMass_eq_one hbeta

theorem logarithmicLeadingDigitProbability_prob_eq_log_div {beta : ℕ}
    (hbeta : 1 < beta) (i : Fin (beta - 1)) :
    (logarithmicLeadingDigitProbability beta hbeta).prob i =
      Real.log ((((leadingDigitOfIndex beta i + 1 : ℕ) : ℝ) /
          (leadingDigitOfIndex beta i : ℝ))) / Real.log (beta : ℝ) := by
  simp [logarithmicLeadingDigitProbability,
    logarithmicLeadingDigitMass_eq_log_div (leadingDigitOfIndex_pos i)]

theorem logarithmicLeadingDigitProbability_prob_eq_log_one_add_inv {beta : ℕ}
    (hbeta : 1 < beta) (i : Fin (beta - 1)) :
    (logarithmicLeadingDigitProbability beta hbeta).prob i =
      Real.log (1 + (1 : ℝ) / (leadingDigitOfIndex beta i : ℝ)) /
        Real.log (beta : ℝ) := by
  simp [logarithmicLeadingDigitProbability,
    logarithmicLeadingDigitMass_eq_log_one_add_inv (leadingDigitOfIndex_pos i)]

theorem decimalLogarithmicLeadingDigitProbability_prob_eq (i : Fin 9) :
    (logarithmicLeadingDigitProbability 10 (by norm_num)).prob i =
      Real.log (((((i.val + 1) + 1 : ℕ) : ℝ) / ((i.val + 1 : ℕ) : ℝ))) /
        Real.log (10 : ℝ) := by
  simpa [leadingDigitOfIndex] using
    logarithmicLeadingDigitProbability_prob_eq_log_div (beta := 10) (by norm_num) i

theorem decimalLogarithmicLeadingDigitProbability_prob_eq_log_one_add_inv
    (i : Fin 9) :
    (logarithmicLeadingDigitProbability 10 (by norm_num)).prob i =
      Real.log (1 + (1 : ℝ) / ((i.val + 1 : ℕ) : ℝ)) /
        Real.log (10 : ℝ) := by
  simpa [leadingDigitOfIndex] using
    logarithmicLeadingDigitProbability_prob_eq_log_one_add_inv
      (beta := 10) (by norm_num) i

/-- In decimal, the logarithmic leading-digit law assigns a strictly larger
probability to leading digit `1` than to leading digit `9`. -/
theorem decimalLogarithmicLeadingDigitProbability_first_gt_last :
    (logarithmicLeadingDigitProbability 10 (by norm_num)).prob
        (⟨0, by norm_num⟩ : Fin 9) >
      (logarithmicLeadingDigitProbability 10 (by norm_num)).prob
        (⟨8, by norm_num⟩ : Fin 9) := by
  change logarithmicLeadingDigitMass 10 1 >
    logarithmicLeadingDigitMass 10 9
  have hden_pos : 0 < Real.log (10 : ℝ) := by
    exact Real.log_pos (by norm_num)
  have hlog :
      Real.log (((10 : ℕ) : ℝ) / (9 : ℝ)) <
        Real.log (((2 : ℕ) : ℝ) / (1 : ℝ)) := by
    exact Real.log_lt_log (by norm_num) (by norm_num)
  rw [logarithmicLeadingDigitMass_eq_log_div (by norm_num : 0 < 1),
    logarithmicLeadingDigitMass_eq_log_div (by norm_num : 0 < 9)]
  simpa using div_lt_div_of_pos_right hlog hden_pos

/-- The decimal logarithmic leading-digit law is not uniform. -/
theorem decimalLogarithmicLeadingDigitProbability_nonuniform :
    (logarithmicLeadingDigitProbability 10 (by norm_num)).prob
        (⟨0, by norm_num⟩ : Fin 9) ≠
      (logarithmicLeadingDigitProbability 10 (by norm_num)).prob
        (⟨8, by norm_num⟩ : Fin 9) := by
  exact ne_of_gt decimalLogarithmicLeadingDigitProbability_first_gt_last

end

end NumStability
