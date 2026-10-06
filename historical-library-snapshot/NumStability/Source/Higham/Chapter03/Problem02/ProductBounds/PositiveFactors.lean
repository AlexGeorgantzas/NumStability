import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.Rounding

-- Analysis/RoundingProductBounds.lean
--
-- Sharper small-unit product bounds from Higham Chapter 3, Lemma 3.4.








namespace NumStability

open scoped BigOperators

/-!
# Small-`nu` Product Bounds

Higham Chapter 3, Lemma 3.4 proves that if `|delta_i| < u` and `n*u < 0.01`,
then the product of factors `1 + delta_i` can be written as `1 + eta_n` with
`|eta_n| < 1.01*n*u`.  This module records that sharper small-`nu` product
bound, separate from the more general `gamma` machinery in `Rounding.lean`.
-/






































































































































































































































































































































































/-- Higham Chapter 3, Problem 3.2, all-positive-factor product form.

If every exponent in Lemma 3.1 is `+1`, the product admits the stronger
Kielbasinski--Schwetlick radius `n*u/(1 - n*u/2)` under the larger guard
`n*u < 2`.  This non-strict local-error variant matches the repository
`FPModel` convention `|delta_i| <= u`; strictness of the final radius comes
from `0 < u`. -/
theorem prod_one_add_delta_eq_one_add_phi_bound_problem32 (n : ℕ) {u : ℝ}
    (hnpos : 0 < n) (hu_pos : 0 < u) (delta : Fin n → ℝ)
    (hdelta : ∀ i : Fin n, |delta i| ≤ u)
    (hnu : (n : ℝ) * u < (2 : ℝ)) :
    ∃ phi : ℝ,
      |phi| < ((n : ℝ) * u) / (1 - (1 / 2 : ℝ) * ((n : ℝ) * u)) ∧
        (∏ i : Fin n, (1 + delta i)) = 1 + phi := by
  set P : ℝ := ∏ i : Fin n, (1 + delta i)
  set x : ℝ := (n : ℝ) * u
  refine ⟨P - 1, ?_, by ring⟩
  have hnposR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hxpos : 0 < x := by
    exact mul_pos hnposR hu_pos
  have hxsmall : x < 2 := by simpa [x] using hnu
  have hden_pos : 0 < 1 - (1 / 2 : ℝ) * x := by nlinarith
  have hx_lt_radius : x < x / (1 - (1 / 2 : ℝ) * x) := by
    have hden2_ne : 2 - x ≠ 0 := by nlinarith
    have hdiff :
        x / (1 - (1 / 2 : ℝ) * x) - x =
          ((1 / 2 : ℝ) * x ^ 2) / (1 - (1 / 2 : ℝ) * x) := by
      field_simp [hden_pos.ne', hden2_ne]
      norm_num
    have hdiff_pos : 0 < x / (1 - (1 / 2 : ℝ) * x) - x := by
      rw [hdiff]
      positivity
    linarith
  have hexp_lt :
      Real.exp x - 1 < x / (1 - (1 / 2 : ℝ) * x) := by
    have h := real_exp_sub_one_lt_div_one_sub_half_of_pos_of_lt_two hxpos hxsmall
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  by_cases hnone : n = 1
  · subst n
    have hP : |P - 1| ≤ u := by
      simpa [P] using hdelta 0
    have hx_eq_u : x = u := by simp [x]
    exact lt_of_le_of_lt hP (by simpa [x, hx_eq_u] using hx_lt_radius)
  · have hn2 : 2 ≤ n := by
      cases n with
      | zero => cases hnpos
      | succ m =>
          cases m with
          | zero => exact False.elim (hnone rfl)
          | succ k => simp
    have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hu_lt_one : u < 1 := by
      have htwou_le : (2 : ℝ) * u ≤ (n : ℝ) * u :=
        mul_le_mul_of_nonneg_right hn2R (le_of_lt hu_pos)
      nlinarith
    have hprod_exp :
        |P - 1| ≤ Real.exp x - 1 := by
      simpa [P, x] using
        prod_one_add_delta_abs_sub_one_le_exp_sub_one n (le_of_lt hu_pos)
          (le_of_lt hu_lt_one) delta hdelta
    exact lt_of_le_of_lt hprod_exp hexp_lt

end NumStability
