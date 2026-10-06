/-
SPDX-License-Identifier: MIT
-/

import NumStability.Analysis.FiniteProbability

namespace NumStability

open scoped BigOperators

noncomputable section

/-!
# Empirical leading-digit distributions

Reusable counts, frequencies, and finite probability distributions induced by
a digit classifier on a finite sample. Historical declaration names are
preserved.
-/

/-- Count of sample points classified as a given decimal leading digit. -/
def problem2_11_digitCount {sampleSize : ℕ}
    (digitOf : Fin sampleSize → Fin 9) (d : Fin 9) : ℕ :=
  ((Finset.univ : Finset (Fin sampleSize)).filter
    (fun i => digitOf i = d)).card

theorem problem2_11_digitCount_le_sampleSize {sampleSize : ℕ}
    (digitOf : Fin sampleSize → Fin 9) (d : Fin 9) :
    problem2_11_digitCount digitOf d ≤ sampleSize := by
  classical
  have hle :
      ((Finset.univ : Finset (Fin sampleSize)).filter
        (fun i => digitOf i = d)).card ≤
        (Finset.univ : Finset (Fin sampleSize)).card :=
    Finset.card_filter_le _ _
  simpa [problem2_11_digitCount] using hle

/-- Empirical frequency of a decimal leading digit in a nonempty finite sample. -/
def problem2_11_digitFrequency {sampleSize : ℕ} (_hsize : 0 < sampleSize)
    (digitOf : Fin sampleSize → Fin 9) (d : Fin 9) : ℝ :=
  (problem2_11_digitCount digitOf d : ℝ) / (sampleSize : ℝ)

theorem problem2_11_digitFrequency_nonneg {sampleSize : ℕ}
    (hsize : 0 < sampleSize)
    (digitOf : Fin sampleSize → Fin 9) (d : Fin 9) :
    0 ≤ problem2_11_digitFrequency hsize digitOf d := by
  exact div_nonneg (Nat.cast_nonneg _)
    (le_of_lt (Nat.cast_pos.mpr hsize : (0 : ℝ) < sampleSize))

theorem problem2_11_digitFrequency_le_one {sampleSize : ℕ}
    (hsize : 0 < sampleSize)
    (digitOf : Fin sampleSize → Fin 9) (d : Fin 9) :
    problem2_11_digitFrequency hsize digitOf d ≤ 1 := by
  have hden_pos : (0 : ℝ) < sampleSize := Nat.cast_pos.mpr hsize
  rw [problem2_11_digitFrequency, div_le_one hden_pos]
  exact_mod_cast problem2_11_digitCount_le_sampleSize digitOf d

theorem problem2_11_sum_digitCount_eq_sampleSize {sampleSize : ℕ}
    (digitOf : Fin sampleSize → Fin 9) :
    (∑ d : Fin 9, problem2_11_digitCount digitOf d) = sampleSize := by
  classical
  have hfiber :
      (Finset.univ : Finset (Fin sampleSize)).card =
        ∑ d ∈ (Finset.univ : Finset (Fin 9)),
          ((Finset.univ : Finset (Fin sampleSize)).filter
            (fun i => digitOf i = d)).card :=
    Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin sampleSize)))
      (t := (Finset.univ : Finset (Fin 9)))
      (f := digitOf)
      (by intro i hi; simp)
  simpa [problem2_11_digitCount] using hfiber.symm

theorem problem2_11_sum_digitFrequency_eq_one {sampleSize : ℕ}
    (hsize : 0 < sampleSize)
    (digitOf : Fin sampleSize → Fin 9) :
    (∑ d : Fin 9, problem2_11_digitFrequency hsize digitOf d) = 1 := by
  classical
  have hcount := problem2_11_sum_digitCount_eq_sampleSize digitOf
  have hsize_ne : (sampleSize : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hsize)
  calc
    (∑ d : Fin 9, problem2_11_digitFrequency hsize digitOf d)
        = (∑ d : Fin 9, (problem2_11_digitCount digitOf d : ℝ)) /
            (sampleSize : ℝ) := by
            simp [problem2_11_digitFrequency, div_eq_mul_inv, Finset.sum_mul]
    _ = (sampleSize : ℝ) / (sampleSize : ℝ) := by
            rw [← Nat.cast_sum, hcount]
    _ = 1 := by
            exact div_self hsize_ne

/-- The finite empirical digit distribution induced by any nonempty classified
sample. -/
def problem2_11_empiricalDigitProbability {sampleSize : ℕ}
    (hsize : 0 < sampleSize)
    (digitOf : Fin sampleSize → Fin 9) : FiniteProbability (Fin 9) where
  prob d := problem2_11_digitFrequency hsize digitOf d
  prob_nonneg d := problem2_11_digitFrequency_nonneg hsize digitOf d
  prob_sum := problem2_11_sum_digitFrequency_eq_one hsize digitOf

theorem problem2_11_empiricalDigitProbability_prob_eq_frequency
    {sampleSize : ℕ} (hsize : 0 < sampleSize)
    (digitOf : Fin sampleSize → Fin 9) (d : Fin 9) :
    (problem2_11_empiricalDigitProbability hsize digitOf).prob d =
      problem2_11_digitFrequency hsize digitOf d :=
  rfl

theorem problem2_11_empiricalDigitProbability_prob_le_one
    {sampleSize : ℕ} (hsize : 0 < sampleSize)
    (digitOf : Fin sampleSize → Fin 9) (d : Fin 9) :
    (problem2_11_empiricalDigitProbability hsize digitOf).prob d ≤ 1 := by
  simpa [problem2_11_empiricalDigitProbability_prob_eq_frequency]
    using problem2_11_digitFrequency_le_one hsize digitOf d

end

end NumStability
