/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GinibreRecurrence

/-! # Higham Chapter 28: the finite real-Ginibre parity formula

The scalar hypergeometric closed form has a two-step recurrence, so its even
and odd subsequences are determined by their first terms.  This file evaluates
the remaining two-dimensional base term from the binomial series for
`(1 + x)^(3/2)` and iterates the recurrence into finite Gamma sums.  The final
parity theorems contain no hypergeometric function.

These are identities for `realGinibreExpectedCountClosedForm`.  Identifying
that scalar closed form with the random-matrix expectation in every dimension
still requires the separate finite-expectation producer.
-/

namespace NumStability

open Filter Asymptotics Polynomial MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

private theorem hasSum_real_binomialSeries
    (a x : ℝ) (hx : |x| < 1) :
    HasSum (fun k : ℕ => Ring.choose a k * x ^ k) ((1 + x) ^ a) := by
  have hs := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := a)).hasSum
    (show x ∈ Metric.eball (0 : ℝ) 1 by
      simpa [enorm_eq_nnnorm, Real.norm_eq_abs] using hx)
  simpa [binomialSeries, mul_comm] using hs

private theorem ringChoose_succ_mul (a : ℝ) (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) * Ring.choose a (k + 1) =
      (a - k) * Ring.choose a k := by
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul]
  simp only [smul_eq_mul]
  rw [descPochhammer_succ_right, Polynomial.smeval_mul]
  simp only [Polynomial.smeval_sub, Polynomial.smeval_X,
    Polynomial.smeval_natCast]
  rw [Nat.factorial_succ]
  push_cast
  have hk : ((k.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  simp [nsmul_eq_mul]

/-- The `n = 2` hypergeometric coefficient is a shifted coefficient of the
binomial series with exponent `3/2`. -/
theorem ginibreHypergeometricTerm_two_eq_binomialTail (k : ℕ) :
    ginibreHypergeometricTerm 2 k =
      -(4 / 3 : ℝ) *
        (Ring.choose (3 / 2 : ℝ) (k + 1) * (-1 / 2 : ℝ) ^ (k + 1)) := by
  induction k with
  | zero =>
      simp [ginibreHypergeometricTerm_zero]
      norm_num
  | succ k ih =>
      rw [ginibreHypergeometricTerm_succ, ih]
      rw [show k + 1 + 1 = k + 2 by omega]
      rw [pow_succ]
      have hchoose := ringChoose_succ_mul (3 / 2 : ℝ) (k + 1)
      push_cast at hchoose ⊢
      have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
      have hchoose' :
          Ring.choose (3 / 2 : ℝ) (k + 2) =
            ((1 / 2 : ℝ) - k) * Ring.choose (3 / 2 : ℝ) (k + 1) /
              ((k : ℝ) + 2) := by
        apply (eq_div_iff hk2).2
        rw [mul_comm]
        convert hchoose using 1 <;> ring
      rw [hchoose']
      rw [show (-1 / 2 : ℝ) ^ (k + 2) =
        (-1 / 2 : ℝ) ^ k * (-1 / 2 : ℝ) ^ 2 by rw [pow_add]]
      field_simp
      ring

/-- Exact scalar hypergeometric value in dimension two. -/
theorem realGinibre_hypergeometric_two :
    ₂F₁ (1 : ℝ) (-1 / 2 : ℝ) (2 : ℝ) (1 / 2 : ℝ) =
      (4 / 3 : ℝ) * (1 - (1 / 2 : ℝ) ^ (3 / 2 : ℝ)) := by
  let b : ℕ → ℝ := fun k =>
    Ring.choose (3 / 2 : ℝ) k * (-1 / 2 : ℝ) ^ k
  have hb : HasSum b ((1 + (-1 / 2 : ℝ)) ^ (3 / 2 : ℝ)) := by
    simpa only [b] using
      hasSum_real_binomialSeries (3 / 2 : ℝ) (-1 / 2 : ℝ) (by norm_num)
  have hsplit :
      (∑' k : ℕ, b k) = b 0 + ∑' k : ℕ, b (k + 1) := by
    simpa using (hb.summable.sum_add_tsum_nat_add 1).symm
  have htail :
      (∑' k : ℕ, b (k + 1)) =
        (1 / 2 : ℝ) ^ (3 / 2 : ℝ) - 1 := by
    rw [hb.tsum_eq] at hsplit
    have hb0 : b 0 = 1 := by simp [b]
    rw [hb0] at hsplit
    norm_num at hsplit ⊢
    linarith
  calc
    ₂F₁ (1 : ℝ) (-1 / 2 : ℝ) (2 : ℝ) (1 / 2 : ℝ) =
        ∑' k : ℕ, ginibreHypergeometricTerm 2 k := by
          convert realGinibre_hypergeometric_eq_tsum 2 using 1
    _ = ∑' k : ℕ, -(4 / 3 : ℝ) * b (k + 1) := by
      apply tsum_congr
      intro k
      simpa only [b] using ginibreHypergeometricTerm_two_eq_binomialTail k
    _ = -(4 / 3 : ℝ) * ∑' k : ℕ, b (k + 1) := by
      rw [tsum_mul_left]
    _ = (4 / 3 : ℝ) * (1 - (1 / 2 : ℝ) ^ (3 / 2 : ℝ)) := by
      rw [htail]
      ring

private theorem one_half_rpow_three_halves :
    (1 / 2 : ℝ) ^ (3 / 2 : ℝ) =
      (1 / 2 : ℝ) * Real.sqrt (1 / 2 : ℝ) := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2)]
  rw [Real.rpow_one, ← Real.sqrt_eq_rpow]

private theorem sqrt_two_mul_sqrt_one_half :
    Real.sqrt 2 * Real.sqrt (1 / 2 : ℝ) = 1 := by
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num
  rfl

private theorem sqrt_two_mul_one_half_rpow_three_halves :
    Real.sqrt 2 * (1 / 2 : ℝ) ^ (3 / 2 : ℝ) = 1 / 2 := by
  rw [one_half_rpow_three_halves]
  calc
    Real.sqrt 2 * ((1 / 2 : ℝ) * Real.sqrt (1 / 2 : ℝ)) =
        (1 / 2 : ℝ) * (Real.sqrt 2 * Real.sqrt (1 / 2 : ℝ)) := by ring
    _ = 1 / 2 := by rw [sqrt_two_mul_sqrt_one_half]; ring

private theorem sqrt_two_div_pi_mul_sqrt_pi :
    Real.sqrt (2 / Real.pi) * Real.sqrt Real.pi = Real.sqrt 2 := by
  rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 / Real.pi)]
  congr 1
  field_simp [ne_of_gt Real.pi_pos]

private theorem realGamma_five_halves_div_two :
    Real.Gamma (2 + 1 / 2 : ℝ) / Real.Gamma 2 =
      (3 / 4 : ℝ) * Real.sqrt Real.pi := by
  rw [show (2 + 1 / 2 : ℝ) = (1 / 2 + 1) + 1 by ring]
  rw [Real.Gamma_add_one (by norm_num : (1 / 2 + 1 : ℝ) ≠ 0)]
  rw [Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  rw [Real.Gamma_one_half_eq]
  have hgammaTwo : Real.Gamma (2 : ℝ) = 1 := by
    simpa using Real.Gamma_nat_eq_factorial 1
  rw [hgammaTwo]
  ring

/-- Exact two-dimensional base value for the finite real-Ginibre closed form. -/
theorem realGinibreExpectedCountClosedForm_two :
    realGinibreExpectedCountClosedForm 2 = Real.sqrt 2 := by
  unfold realGinibreExpectedCountClosedForm
  norm_num only [Nat.cast_ofNat]
  rw [show (-(1 / 2) : ℝ) = (-1 / 2 : ℝ) by ring]
  rw [realGinibre_hypergeometric_two]
  rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by ring]
  rw [realGamma_five_halves_div_two]
  rw [show Real.sqrt (2 / Real.pi) * ((3 / 4 : ℝ) * Real.sqrt Real.pi) *
      ((4 / 3 : ℝ) * (1 - (1 / 2 : ℝ) ^ (3 / 2 : ℝ))) =
      (Real.sqrt (2 / Real.pi) * Real.sqrt Real.pi) *
        (1 - (1 / 2 : ℝ) ^ (3 / 2 : ℝ)) by ring]
  rw [sqrt_two_div_pi_mul_sqrt_pi]
  rw [mul_sub, mul_one, sqrt_two_mul_one_half_rpow_three_halves]
  ring

/-- The explicit Gamma increment in the two-step parity recurrence. -/
noncomputable def realGinibreParityIncrement (m : ℕ) : ℝ :=
  Real.sqrt (2 / Real.pi) *
    (Real.Gamma ((m : ℝ) + 1 / 2) / Real.Gamma ((m : ℝ) + 1))

@[simp]
theorem realGinibreParityIncrement_zero :
    realGinibreParityIncrement 0 = Real.sqrt 2 := by
  rw [realGinibreParityIncrement]
  norm_num only [Nat.cast_zero, zero_add]
  rw [Real.Gamma_one_half_eq]
  have hgammaOne : Real.Gamma (1 : ℝ) = 1 := by
    simpa using Real.Gamma_nat_eq_factorial 0
  rw [hgammaOne, div_one, sqrt_two_div_pi_mul_sqrt_pi]

private theorem realGinibreExpectedCountClosedForm_add_increment
    (m : ℕ) (hm : 0 < m) :
    realGinibreExpectedCountClosedForm (m + 2) =
      realGinibreExpectedCountClosedForm m + realGinibreParityIncrement m := by
  have h := realGinibreExpectedCountClosedForm_shift_two m hm
  rw [realGinibreParityIncrement]
  linarith

/-- Hypergeometric-free finite sum for every odd dimension. -/
theorem realGinibreExpectedCountClosedForm_odd_finiteSum (r : ℕ) :
    realGinibreExpectedCountClosedForm (2 * r + 1) =
      1 + ∑ j ∈ Finset.range r, realGinibreParityIncrement (2 * j + 1) := by
  induction r with
  | zero =>
      simpa using realGinibreExpectedCountClosedForm_one
  | succ r ih =>
      rw [show 2 * (r + 1) + 1 = (2 * r + 1) + 2 by omega]
      rw [realGinibreExpectedCountClosedForm_add_increment (2 * r + 1) (by omega)]
      rw [ih, Finset.sum_range_succ]
      ring

/-- Hypergeometric-free finite sum for every positive even dimension.  The
`j = 0` summand is the exact two-dimensional base value `sqrt 2`. -/
theorem realGinibreExpectedCountClosedForm_even_finiteSum (r : ℕ) :
    realGinibreExpectedCountClosedForm (2 * r + 2) =
      ∑ j ∈ Finset.range (r + 1), realGinibreParityIncrement (2 * j) := by
  induction r with
  | zero =>
      simp [realGinibreExpectedCountClosedForm_two]
  | succ r ih =>
      calc
        realGinibreExpectedCountClosedForm (2 * (r + 1) + 2) =
            realGinibreExpectedCountClosedForm (2 * r + 2) +
              realGinibreParityIncrement (2 * r + 2) := by
                rw [show 2 * (r + 1) + 2 = (2 * r + 2) + 2 by omega]
                exact realGinibreExpectedCountClosedForm_add_increment
                  (2 * r + 2) (by omega)
        _ = (∑ j ∈ Finset.range (r + 1), realGinibreParityIncrement (2 * j)) +
              realGinibreParityIncrement (2 * r + 2) := by rw [ih]
        _ = ∑ j ∈ Finset.range ((r + 1) + 1),
              realGinibreParityIncrement (2 * j) := by
                conv_rhs => rw [Finset.sum_range_succ]
                congr 2

/-- Expanded odd-parity Gamma sum, with no auxiliary recurrence notation. -/
theorem realGinibreExpectedCountClosedForm_odd_gammaSum (r : ℕ) :
    realGinibreExpectedCountClosedForm (2 * r + 1) =
      1 + ∑ j ∈ Finset.range r,
        Real.sqrt (2 / Real.pi) *
          (Real.Gamma (((2 * j + 1 : ℕ) : ℝ) + 1 / 2) /
            Real.Gamma (((2 * j + 1 : ℕ) : ℝ) + 1)) := by
  simpa only [realGinibreParityIncrement] using
    realGinibreExpectedCountClosedForm_odd_finiteSum r

/-- Expanded positive even-parity Gamma sum, with no auxiliary recurrence
notation. -/
theorem realGinibreExpectedCountClosedForm_even_gammaSum (r : ℕ) :
    realGinibreExpectedCountClosedForm (2 * r + 2) =
      ∑ j ∈ Finset.range (r + 1),
        Real.sqrt (2 / Real.pi) *
          (Real.Gamma (((2 * j : ℕ) : ℝ) + 1 / 2) /
            Real.Gamma (((2 * j : ℕ) : ℝ) + 1)) := by
  simpa only [realGinibreParityIncrement] using
    realGinibreExpectedCountClosedForm_even_finiteSum r

end NumStability
