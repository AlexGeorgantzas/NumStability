import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Scalar exponential bounds

Power-series bounds for the real exponential used in rounding-product analysis.
-/

namespace NumStability

/-- The exponential series tail beginning at degree two. -/
theorem real_exp_tail_two_hasSum (a : ℝ) :
    HasSum (fun n : ℕ => a ^ (n + 2) / ((n + 2).factorial : ℝ))
      (Real.exp a - 1 - a) := by
  have hexp : HasSum (fun n : ℕ => a ^ n / (n.factorial : ℝ)) (Real.exp a) := by
    simpa [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) a)
  have htail :=
    (hasSum_nat_add_iff'
      (f := fun n : ℕ => a ^ n / (n.factorial : ℝ)) 2).2 hexp
  convert htail using 1
  simp [Finset.sum_range_succ, Nat.factorial]
  ring

/-- Scalar Bernstein parabola for `0 ≤ x ≤ 1`.

This is the power-series part of Tropp's matrix Bernstein scalar inequality:
all degree-`≥ 2` tail terms are bounded by replacing `x^k` with `x^2`. -/
theorem real_exp_mul_le_quadratic_of_nonneg_of_nonneg_of_le_one
    {a x : ℝ} (ha : 0 ≤ a) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (a * x) ≤ 1 + a * x + (Real.exp a - a - 1) * x ^ 2 := by
  have htail_ax := real_exp_tail_two_hasSum (a * x)
  have htail_a := real_exp_tail_two_hasSum a
  have hsumm_ax := htail_ax.summable
  have hsumm_a := htail_a.summable
  have hsumm_scaled :
      Summable (fun n : ℕ =>
        x ^ 2 * (a ^ (n + 2) / ((n + 2).factorial : ℝ))) :=
    hsumm_a.mul_left (x ^ 2)
  have hterm : ∀ n : ℕ,
      (a * x) ^ (n + 2) / ((n + 2).factorial : ℝ) ≤
        x ^ 2 * (a ^ (n + 2) / ((n + 2).factorial : ℝ)) := by
    intro n
    have hfact_pos : 0 < (((n + 2).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (n + 2)
    have hxpow : x ^ (n + 2) ≤ x ^ 2 := by
      have hxn : x ^ n ≤ 1 := pow_le_one₀ hx0 hx1
      calc
        x ^ (n + 2) = x ^ n * x ^ 2 := by ring_nf
        _ ≤ 1 * x ^ 2 := mul_le_mul_of_nonneg_right hxn (sq_nonneg x)
        _ = x ^ 2 := one_mul _
    have hapow_nonneg : 0 ≤ a ^ (n + 2) := pow_nonneg ha _
    have hnum : (a * x) ^ (n + 2) ≤ x ^ 2 * a ^ (n + 2) := by
      calc
        (a * x) ^ (n + 2) = a ^ (n + 2) * x ^ (n + 2) := by
          rw [mul_pow]
        _ ≤ a ^ (n + 2) * x ^ 2 :=
          mul_le_mul_of_nonneg_left hxpow hapow_nonneg
        _ = x ^ 2 * a ^ (n + 2) := by ring
    calc
      (a * x) ^ (n + 2) / ((n + 2).factorial : ℝ) ≤
          (x ^ 2 * a ^ (n + 2)) / ((n + 2).factorial : ℝ) := by
        exact div_le_div_of_nonneg_right hnum hfact_pos.le
      _ = x ^ 2 * (a ^ (n + 2) / ((n + 2).factorial : ℝ)) := by ring
  have htail_le := Summable.tsum_le_tsum hterm hsumm_ax hsumm_scaled
  rw [htail_ax.tsum_eq, hsumm_a.tsum_mul_left] at htail_le
  rw [htail_a.tsum_eq] at htail_le
  nlinarith

end NumStability
