-- Analysis/RoundingProductBounds.lean
--
-- Sharper small-unit product bounds from Higham Chapter 3, Lemma 3.4.

import NumStability.Analysis.Rounding
import NumStability.Analysis.LiebTrace
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Pow

namespace NumStability

open scoped BigOperators

/-!
# Small-`nu` Product Bounds

Higham Chapter 3, Lemma 3.4 proves that if `|delta_i| < u` and `n*u < 0.01`,
then the product of factors `1 + delta_i` can be written as `1 + eta_n` with
`|eta_n| < 1.01*n*u`.  This module records that sharper small-`nu` product
bound, separate from the more general `gamma` machinery in `Rounding.lean`.
-/

/-- Scalar relative-factor bridge used by perturbation reductions:
    if every positive base value is approximated with additive error at most
    `eps * base_i`, then the perturbed values can be written with
    multiplicative factors `1 + theta_i` satisfying `|theta_i| <= eps`.

This is only scalar algebra; matrix-specific work must still prove the
additive relative bound, for example from singular-value perturbation
inequalities. -/
theorem exists_relative_theta_of_abs_sub_le_mul_pos {n : ℕ}
    (base perturbed : Fin n → ℝ) {eps : ℝ}
    (hpos : ∀ i : Fin n, 0 < base i)
    (hrel : ∀ i : Fin n, |perturbed i - base i| ≤ eps * base i) :
    ∃ theta : Fin n → ℝ,
      (∀ i : Fin n, perturbed i = base i * (1 + theta i)) ∧
        ∀ i : Fin n, |theta i| ≤ eps := by
  refine ⟨fun i => (perturbed i - base i) / base i, ?_, ?_⟩
  · intro i
    field_simp [ne_of_gt (hpos i)]
    ring
  · intro i
    rw [abs_div, abs_of_pos (hpos i)]
    rw [div_le_iff₀ (hpos i)]
    simpa [mul_comm] using hrel i

/-- A product of factors `1 + delta_i`, with `|delta_i| <= u` and `u <= 1`,
is squeezed between `(1-u)^n` and `(1+u)^n`. -/
theorem prod_one_add_delta_bounds (n : ℕ) {u : ℝ}
    (_hu0 : 0 ≤ u) (hu1 : u ≤ 1) (delta : Fin n → ℝ)
    (hdelta : ∀ i : Fin n, |delta i| ≤ u) :
    (1 - u) ^ n ≤ (∏ i : Fin n, (1 + delta i)) ∧
      (∏ i : Fin n, (1 + delta i)) ≤ (1 + u) ^ n := by
  constructor
  · have hbase_nonneg : 0 ≤ 1 - u := by linarith
    have hle : ∀ i ∈ (Finset.univ : Finset (Fin n)), 1 - u ≤ 1 + delta i := by
      intro i _hi
      have hlower : -u ≤ delta i := (abs_le.mp (hdelta i)).1
      linarith
    simpa using
      (Finset.prod_le_prod
        (s := (Finset.univ : Finset (Fin n)))
        (f := fun _i : Fin n => 1 - u)
        (g := fun i : Fin n => 1 + delta i)
        (fun _i _hi => hbase_nonneg) hle)
  · have hfactor_nonneg :
        ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ 1 + delta i := by
      intro i _hi
      have hlower : -u ≤ delta i := (abs_le.mp (hdelta i)).1
      linarith
    have hle : ∀ i ∈ (Finset.univ : Finset (Fin n)), 1 + delta i ≤ 1 + u := by
      intro i _hi
      have hupper : delta i ≤ u := (abs_le.mp (hdelta i)).2
      linarith
    simpa using
      (Finset.prod_le_prod
        (s := (Finset.univ : Finset (Fin n)))
        (f := fun i : Fin n => 1 + delta i)
        (g := fun _i : Fin n => 1 + u)
        hfactor_nonneg hle)

/-- Exponential envelope for products of factors `1 + delta_i`. -/
theorem prod_one_add_delta_abs_sub_one_le_exp_sub_one (n : ℕ) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (delta : Fin n → ℝ)
    (hdelta : ∀ i : Fin n, |delta i| ≤ u) :
    |(∏ i : Fin n, (1 + delta i)) - 1| ≤
      Real.exp ((n : ℝ) * u) - 1 := by
  set P : ℝ := ∏ i : Fin n, (1 + delta i)
  set x : ℝ := (n : ℝ) * u
  have hx0 : 0 ≤ x := by
    exact mul_nonneg (by exact_mod_cast n.zero_le) hu0
  have hbounds := prod_one_add_delta_bounds n hu0 hu1 delta hdelta
  have hbern :
      1 - x ≤ (1 - u) ^ n := by
    have hpow := one_add_mul_le_pow (a := -u) (n := n) (by linarith)
    simpa [x] using hpow
  have hP_lower : 1 - x ≤ P := by
    exact hbern.trans (by simpa [P] using hbounds.1)
  have hone_add_le_exp : 1 + u ≤ Real.exp u := by
    simpa [add_comm] using Real.add_one_le_exp u
  have hpow_le_exp :
      (1 + u) ^ n ≤ Real.exp ((n : ℝ) * u) := by
    have hpow :
        (1 + u) ^ n ≤ (Real.exp u) ^ n :=
      pow_le_pow_left₀ (by linarith) hone_add_le_exp n
    have hexp_pow : (Real.exp u) ^ n = Real.exp ((n : ℝ) * u) := by
      rw [← Real.exp_nat_mul]
    exact hpow.trans_eq hexp_pow
  have hP_upper : P ≤ Real.exp x := by
    have hP_le_pow : P ≤ (1 + u) ^ n := by
      simpa [P] using hbounds.2
    have hpow_le_exp_x : (1 + u) ^ n ≤ Real.exp x := by
      simpa [x] using hpow_le_exp
    exact hP_le_pow.trans hpow_le_exp_x
  have hx_le_exp_sub_one : x ≤ Real.exp x - 1 := by
    have h := Real.add_one_le_exp x
    linarith
  refine abs_le.mpr ⟨?_, ?_⟩
  · have hleft : -x ≤ P - 1 := by linarith
    have hcompare : -(Real.exp x - 1) ≤ -x := by linarith
    simpa [P, x] using hcompare.trans hleft
  · have hright : P - 1 ≤ Real.exp x - 1 := by linarith
    simpa [P, x] using hright

/-- Numerical exponential cap used in Higham Lemma 3.4:
for `0 < x < 0.01`, `exp(x)-1 < 1.01*x`. -/
theorem real_exp_sub_one_lt_101_mul_of_pos_of_lt_cent {x : ℝ}
    (hx0 : 0 < x) (hxsmall : x < (1 / 100 : ℝ)) :
    Real.exp x - 1 < (101 / 100 : ℝ) * x := by
  have hx0le : 0 ≤ x := le_of_lt hx0
  have hx1 : x ≤ 1 := by nlinarith
  have hquad :=
    real_exp_mul_le_quadratic_of_nonneg_of_nonneg_of_le_one
      (a := 1) (x := x) zero_le_one hx0le hx1
  have hquad' :
      Real.exp x ≤ 1 + x + (Real.exp 1 - 1 - 1) * x ^ 2 := by
    simpa [one_mul] using hquad
  have hcoeff : Real.exp 1 - 1 - 1 ≤ 1 := by
    have h := Real.exp_one_lt_three
    linarith
  have htail_le : (Real.exp 1 - 1 - 1) * x ^ 2 ≤ x ^ 2 := by
    simpa [one_mul] using
      mul_le_mul_of_nonneg_right hcoeff (sq_nonneg x)
  have hx_sq_lt : x ^ 2 < (1 / 100 : ℝ) * x := by
    nlinarith
  calc
    Real.exp x - 1 ≤ x + (Real.exp 1 - 1 - 1) * x ^ 2 := by linarith
    _ ≤ x + x ^ 2 := by linarith
    _ < x + (1 / 100 : ℝ) * x := by linarith
    _ = (101 / 100 : ℝ) * x := by ring

/-- Padé-type exponential cap used in Higham Problem 3.2:
for `0 < x < 2`, `exp(x)-1 < x/(1-x/2)`. -/
theorem real_exp_sub_one_lt_div_one_sub_half_of_pos_of_lt_two {x : ℝ}
    (hx0 : 0 < x) (hxsmall : x < (2 : ℝ)) :
    Real.exp x - 1 < x / (1 - x / 2) := by
  set t : ℝ := x / 2
  have ht_def : t = x / 2 := rfl
  have ht0 : 0 ≤ t := by nlinarith [ht_def]
  have htpos : 0 < t := by nlinarith [ht_def]
  have ht1 : t < 1 := by nlinarith [ht_def]
  have hseries := Real.sum_range_le_log_div ht0 ht1 2
  have hterm_lt :
      t < ∑ i ∈ Finset.range 2, t ^ (2 * i + 1) / (2 * i + 1 : ℝ) := by
    calc
      t < t + t ^ 3 / (3 : ℝ) := by
        exact lt_add_of_pos_right t (by positivity)
      _ = ∑ i ∈ Finset.range 2, t ^ (2 * i + 1) / (2 * i + 1 : ℝ) := by
        norm_num [Finset.sum_range_succ, pow_succ, pow_two, pow_three]
  have ht_lt_half_log :
      t < (1 / 2 : ℝ) * Real.log ((1 + t) / (1 - t)) :=
    hterm_lt.trans_le hseries
  have hlog : x < Real.log ((1 + t) / (1 - t)) := by nlinarith [ht_def]
  have hratio_pos : 0 < (1 + t) / (1 - t) := by
    exact div_pos (by nlinarith) (by nlinarith)
  have hexp_lt : Real.exp x < (1 + t) / (1 - t) :=
    (Real.lt_log_iff_exp_lt hratio_pos).mp hlog
  have hden_pos : 0 < 1 - x / 2 := by nlinarith
  have hden2_ne : 2 - x ≠ 0 := by nlinarith
  calc
    Real.exp x - 1 < (1 + t) / (1 - t) - 1 := sub_lt_sub_right hexp_lt 1
    _ = x / (1 - x / 2) := by
      rw [ht_def]
      field_simp [hden_pos.ne', hden2_ne]
      norm_num
      ring

/-- Higham Chapter 3, Lemma 3.1, all-positive-factor product radius.

If `|delta_i| <= u` and `n*u < 1`, the relative perturbation in
`prod_i (1 + delta_i)` is bounded by the usual `gamma_n = n*u/(1-n*u)`.
This non-strict form is useful when a later chapter has already reduced a
matrix perturbation estimate to scalar factors `1 + delta_i`. -/
theorem prod_one_add_delta_abs_sub_one_le_gamma_radius (n : ℕ) {u : ℝ}
    (hnpos : 0 < n) (hu0 : 0 ≤ u)
    (hnu : (n : ℝ) * u < (1 : ℝ)) (delta : Fin n → ℝ)
    (hdelta : ∀ i : Fin n, |delta i| ≤ u) :
    |(∏ i : Fin n, (1 + delta i)) - 1| ≤
      ((n : ℝ) * u) / (1 - (n : ℝ) * u) := by
  by_cases hu_zero : u = 0
  · have hdelta_zero : ∀ i : Fin n, delta i = 0 := by
      intro i
      have hle : |delta i| ≤ 0 := by
        simpa [hu_zero] using hdelta i
      exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
    have hprod_one : (∏ i : Fin n, (1 + delta i)) = 1 := by
      simp [hdelta_zero]
    rw [hprod_one]
    simp [hu_zero]
  · set x : ℝ := (n : ℝ) * u
    have hnposR : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hu_pos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu_zero)
    have hxpos : 0 < x := by
      exact mul_pos hnposR hu_pos
    have hxlt1 : x < 1 := by
      simpa [x] using hnu
    have hn_one_le : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hnpos)
    have hu_le_x : u ≤ x := by
      simpa [x, one_mul] using
        mul_le_mul_of_nonneg_right hn_one_le hu0
    have hu1 : u ≤ 1 := hu_le_x.trans (le_of_lt hxlt1)
    have hprod_exp :
        |(∏ i : Fin n, (1 + delta i)) - 1| ≤ Real.exp x - 1 := by
      simpa [x] using
        prod_one_add_delta_abs_sub_one_le_exp_sub_one n hu0 hu1 delta hdelta
    have hexp_lt_half :
        Real.exp x - 1 < x / (1 - x / 2) :=
      real_exp_sub_one_lt_div_one_sub_half_of_pos_of_lt_two hxpos (by nlinarith)
    have hden_half_pos : 0 < 1 - x / 2 := by nlinarith
    have hden_pos : 0 < 1 - x := by nlinarith
    have hden_le : 1 - x ≤ 1 - x / 2 := by nlinarith
    have hinv_le : (1 - x / 2)⁻¹ ≤ (1 - x)⁻¹ :=
      inv_anti₀ hden_pos hden_le
    have hhalf_le : x / (1 - x / 2) ≤ x / (1 - x) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left hinv_le (le_of_lt hxpos)
    calc
      |(∏ i : Fin n, (1 + delta i)) - 1| ≤ Real.exp x - 1 := hprod_exp
      _ ≤ x / (1 - x / 2) := le_of_lt hexp_lt_half
      _ ≤ x / (1 - x) := hhalf_le
      _ = ((n : ℝ) * u) / (1 - (n : ℝ) * u) := by
        simp [x]

/-- Higham Chapter 3, Lemma 3.4, in scalar product form. -/
theorem prod_one_add_delta_eq_one_add_eta_bound_101 (n : ℕ) {u : ℝ}
    (hnpos : 0 < n) (delta : Fin n → ℝ)
    (hdelta : ∀ i : Fin n, |delta i| < u)
    (hnu : (n : ℝ) * u < (1 / 100 : ℝ)) :
    ∃ eta : ℝ,
      |eta| < (101 / 100 : ℝ) * (n : ℝ) * u ∧
        (∏ i : Fin n, (1 + delta i)) = 1 + eta := by
  set P : ℝ := ∏ i : Fin n, (1 + delta i)
  refine ⟨P - 1, ?_, by ring⟩
  have hnposR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hu_pos : 0 < u := by
    have hfirst := hdelta ⟨0, hnpos⟩
    exact lt_of_le_of_lt (abs_nonneg _) hfirst
  have hu0 : 0 ≤ u := le_of_lt hu_pos
  have hxpos : 0 < (n : ℝ) * u := mul_pos hnposR hu_pos
  have hn_one_le : (1 : ℝ) ≤ n := by
    exact_mod_cast (Nat.succ_le_iff.mpr hnpos)
  have hu_le_nu : u ≤ (n : ℝ) * u := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hn_one_le hu0
  have hu1 : u ≤ 1 := by nlinarith
  have hprod_exp :
      |P - 1| ≤ Real.exp ((n : ℝ) * u) - 1 := by
    simpa [P] using
      prod_one_add_delta_abs_sub_one_le_exp_sub_one n hu0 hu1 delta
        (fun i => le_of_lt (hdelta i))
  have hexp_lt :
      Real.exp ((n : ℝ) * u) - 1 <
        (101 / 100 : ℝ) * ((n : ℝ) * u) :=
    real_exp_sub_one_lt_101_mul_of_pos_of_lt_cent hxpos hnu
  calc
    |P - 1| ≤ Real.exp ((n : ℝ) * u) - 1 := hprod_exp
    _ < (101 / 100 : ℝ) * ((n : ℝ) * u) := hexp_lt
    _ = (101 / 100 : ℝ) * (n : ℝ) * u := by ring

/-- Non-strict local-error variant of Higham Chapter 3, Lemma 3.4.

The repository's `FPModel` uses `|delta_i| <= u` rather than Higham's usual
strict local bound.  With the explicit nonzero-radius hypothesis `0 < u`, the
same exponential-envelope proof still gives the strict product radius
`|eta| < 1.01*n*u`. -/
theorem prod_one_add_delta_eq_one_add_eta_bound_101_le (n : ℕ) {u : ℝ}
    (hnpos : 0 < n) (hu_pos : 0 < u) (delta : Fin n → ℝ)
    (hdelta : ∀ i : Fin n, |delta i| ≤ u)
    (hnu : (n : ℝ) * u < (1 / 100 : ℝ)) :
    ∃ eta : ℝ,
      |eta| < (101 / 100 : ℝ) * (n : ℝ) * u ∧
        (∏ i : Fin n, (1 + delta i)) = 1 + eta := by
  set P : ℝ := ∏ i : Fin n, (1 + delta i)
  refine ⟨P - 1, ?_, by ring⟩
  have hnposR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hu0 : 0 ≤ u := le_of_lt hu_pos
  have hxpos : 0 < (n : ℝ) * u := mul_pos hnposR hu_pos
  have hn_one_le : (1 : ℝ) ≤ n := by
    exact_mod_cast (Nat.succ_le_iff.mpr hnpos)
  have hu_le_nu : u ≤ (n : ℝ) * u := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hn_one_le hu0
  have hu1 : u ≤ 1 := by nlinarith
  have hprod_exp :
      |P - 1| ≤ Real.exp ((n : ℝ) * u) - 1 := by
    simpa [P] using
      prod_one_add_delta_abs_sub_one_le_exp_sub_one n hu0 hu1 delta hdelta
  have hexp_lt :
      Real.exp ((n : ℝ) * u) - 1 <
        (101 / 100 : ℝ) * ((n : ℝ) * u) :=
    real_exp_sub_one_lt_101_mul_of_pos_of_lt_cent hxpos hnu
  calc
    |P - 1| ≤ Real.exp ((n : ℝ) * u) - 1 := hprod_exp
    _ < (101 / 100 : ℝ) * ((n : ℝ) * u) := hexp_lt
    _ = (101 / 100 : ℝ) * (n : ℝ) * u := by ring

/-- Numerical exponential cap for the Wilkinson variant quoted in Higham's
Chapter 3 notes: for `0 < x < 0.1`, `exp(x) - 1 < 1.06*x`.

The proof uses the already checked Padé envelope
`exp(x) - 1 < x / (1 - x/2)`.  On `x < 0.1`, its multiplicative factor is
strictly smaller than `1 / 0.95 < 1.06`. -/
theorem real_exp_sub_one_lt_106_mul_of_pos_of_lt_tenth {x : ℝ}
    (hx0 : 0 < x) (hxsmall : x < (1 / 10 : ℝ)) :
    Real.exp x - 1 < (53 / 50 : ℝ) * x := by
  have hpade : Real.exp x - 1 < x / (1 - x / 2) :=
    real_exp_sub_one_lt_div_one_sub_half_of_pos_of_lt_two hx0 (by nlinarith)
  have hden_pos : 0 < 1 - x / 2 := by nlinarith
  have hratio : x / (1 - x / 2) < (53 / 50 : ℝ) * x := by
    rw [div_lt_iff₀ hden_pos]
    nlinarith
  exact hpade.trans hratio

/-- Wilkinson's slightly different version of Higham Chapter 3, Lemma 3.4,
quoted in the chapter notes: if `|delta_i| <= u` and `n*u < 0.1`, then
the product is `1 + eta` with `|eta| <= 1.06*n*u`.

Unlike a wrapper around the generic `gamma_n` bound, this theorem derives the
printed constant from the proved product/exponential envelope.  The zero-`u`
case is handled separately so that the source's non-strict conclusion holds
without an unnecessary positivity assumption. -/
theorem prod_one_add_delta_eq_one_add_eta_bound_106 (n : ℕ) {u : ℝ}
    (hnpos : 0 < n) (delta : Fin n → ℝ)
    (hdelta : ∀ i : Fin n, |delta i| ≤ u)
    (hnu : (n : ℝ) * u < (1 / 10 : ℝ)) :
    ∃ eta : ℝ,
      |eta| ≤ (53 / 50 : ℝ) * (n : ℝ) * u ∧
        (∏ i : Fin n, (1 + delta i)) = 1 + eta := by
  by_cases hu_zero : u = 0
  · subst u
    have hdelta_zero : ∀ i : Fin n, delta i = 0 := by
      intro i
      exact abs_eq_zero.mp (le_antisymm (hdelta i) (abs_nonneg _))
    refine ⟨0, by norm_num, ?_⟩
    simp [hdelta_zero]
  · set P : ℝ := ∏ i : Fin n, (1 + delta i)
    refine ⟨P - 1, ?_, by ring⟩
    have hnposR : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hu0 : 0 ≤ u :=
      (abs_nonneg (delta ⟨0, hnpos⟩)).trans (hdelta ⟨0, hnpos⟩)
    have hu_pos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu_zero)
    have hxpos : 0 < (n : ℝ) * u := mul_pos hnposR hu_pos
    have hn_one_le : (1 : ℝ) ≤ n := by
      exact_mod_cast (Nat.succ_le_iff.mpr hnpos)
    have hu_le_nu : u ≤ (n : ℝ) * u := by
      simpa [one_mul] using mul_le_mul_of_nonneg_right hn_one_le hu0
    have hu1 : u ≤ 1 := by nlinarith
    have hprod_exp :
        |P - 1| ≤ Real.exp ((n : ℝ) * u) - 1 := by
      simpa [P] using
        prod_one_add_delta_abs_sub_one_le_exp_sub_one n hu0 hu1 delta hdelta
    have hexp_lt :
        Real.exp ((n : ℝ) * u) - 1 <
          (53 / 50 : ℝ) * ((n : ℝ) * u) :=
      real_exp_sub_one_lt_106_mul_of_pos_of_lt_tenth hxpos hnu
    calc
      |P - 1| ≤ Real.exp ((n : ℝ) * u) - 1 := hprod_exp
      _ ≤ (53 / 50 : ℝ) * ((n : ℝ) * u) := le_of_lt hexp_lt
      _ = (53 / 50 : ℝ) * (n : ℝ) * u := by ring

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
