import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Fixed-precision first-order bounds

Reusable algebra for `FirstOrderLe u leading value`, the pointwise envelope
`value ≤ leading + K * u ^ 2` for some nonnegative coefficient `K` at one fixed
precision. The API supplies monotonicity, maximum, addition, product,
finite-supremum, scaling, and `FPModel.gamma` constructors.

`FirstOrderLe` is bookkeeping for an explicit fixed-precision remainder; it
does not by itself express a uniform `O(u²)` statement. Source-facing uniform
asymptotics use `FamilyFirstOrderLe` from
`NumStability.Analysis.FirstOrder.AsymptoticFamilies`.
-/

namespace NumStability

open scoped BigOperators

/-- Legacy pointwise second-order envelope at one fixed `u`.

This predicate is useful for algebraically tracking an explicit `K * u^2`
term inside a fixed-precision proof.  It is **not** by itself an interpretation
of the source's uniform `O(u^2)`: when `u ≠ 0`, the existential `K` can be
chosen after seeing `value`.  Source-facing asymptotic conclusions use
`FamilyFirstOrderLe` from `NumStability.Analysis.FirstOrder.AsymptoticFamilies`
and the actual-norm family contracts in `BlockLUFirstOrderFamilies`. -/
def FirstOrderLe (u leading value : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ value ≤ leading + K * u ^ 2

lemma FirstOrderLe.of_le {u leading value : ℝ} (h : value ≤ leading) :
    FirstOrderLe u leading value := by
  exact ⟨0, le_rfl, by simpa using h⟩

lemma FirstOrderLe.mono_leading {u leading₁ leading₂ value : ℝ}
    (h : FirstOrderLe u leading₁ value) (hle : leading₁ ≤ leading₂) :
    FirstOrderLe u leading₂ value := by
  rcases h with ⟨K, hK, hvalue⟩
  exact ⟨K, hK, by linarith⟩

lemma FirstOrderLe.mono_value {u leading value₁ value₂ : ℝ}
    (h : FirstOrderLe u leading value₂) (hle : value₁ ≤ value₂) :
    FirstOrderLe u leading value₁ := by
  rcases h with ⟨K, hK, hvalue⟩
  exact ⟨K, hK, by linarith⟩

lemma FirstOrderLe.max_same {u leading value₁ value₂ : ℝ}
    (h₁ : FirstOrderLe u leading value₁)
    (h₂ : FirstOrderLe u leading value₂) :
    FirstOrderLe u leading (max value₁ value₂) := by
  rcases h₁ with ⟨K₁, hK₁, hvalue₁⟩
  rcases h₂ with ⟨K₂, hK₂, hvalue₂⟩
  refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, ?_⟩
  have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
  apply max_le
  · calc value₁
        ≤ leading + K₁ * u ^ 2 := hvalue₁
      _ ≤ leading + (K₁ + K₂) * u ^ 2 := by
        have hK₁le : K₁ ≤ K₁ + K₂ := by linarith
        nlinarith [mul_le_mul_of_nonneg_right hK₁le hu2]
  · calc value₂
        ≤ leading + K₂ * u ^ 2 := hvalue₂
      _ ≤ leading + (K₁ + K₂) * u ^ 2 := by
        have hK₂le : K₂ ≤ K₁ + K₂ := by linarith
        nlinarith [mul_le_mul_of_nonneg_right hK₂le hu2]

lemma FirstOrderLe.max {u leading₁ leading₂ value₁ value₂ : ℝ}
    (h₁ : FirstOrderLe u leading₁ value₁)
    (h₂ : FirstOrderLe u leading₂ value₂) :
    FirstOrderLe u (max leading₁ leading₂) (max value₁ value₂) :=
  FirstOrderLe.max_same
    (h₁.mono_leading (le_max_left leading₁ leading₂))
    (h₂.mono_leading (le_max_right leading₁ leading₂))

lemma FirstOrderLe.add {u leading₁ leading₂ value₁ value₂ value : ℝ}
    (h₁ : FirstOrderLe u leading₁ value₁)
    (h₂ : FirstOrderLe u leading₂ value₂)
    (hvalue : value ≤ value₁ + value₂) :
    FirstOrderLe u (leading₁ + leading₂) value := by
  rcases h₁ with ⟨K₁, hK₁, hvalue₁⟩
  rcases h₂ with ⟨K₂, hK₂, hvalue₂⟩
  refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, ?_⟩
  linarith

/-- The product of two first-order quantities is a pure second-order term.

    Writing each leading term as `cᵢ*u`, the explicit `FirstOrderLe`
    witnesses factor both upper bounds by `u`.  Their product is therefore a
    nonnegative multiple of `u^2`, exactly the remainder shape used in the
    DHS solve aggregation. -/
lemma FirstOrderLe.mul_is_secondOrder
    {u c₁ c₂ value₁ value₂ value : ℝ}
    (hu : 0 ≤ u) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hvalue₂ : 0 ≤ value₂)
    (h₁ : FirstOrderLe u (c₁ * u) value₁)
    (h₂ : FirstOrderLe u (c₂ * u) value₂)
    (hvalue : value ≤ value₁ * value₂) :
    FirstOrderLe u 0 value := by
  rcases h₁ with ⟨K₁, hK₁, h₁⟩
  rcases h₂ with ⟨K₂, hK₂, h₂⟩
  let C₁ := c₁ + K₁ * u
  let C₂ := c₂ + K₂ * u
  have hC₁ : 0 ≤ C₁ := add_nonneg hc₁ (mul_nonneg hK₁ hu)
  have hC₂ : 0 ≤ C₂ := add_nonneg hc₂ (mul_nonneg hK₂ hu)
  have hv₁ : value₁ ≤ u * C₁ := by
    calc
      value₁ ≤ c₁ * u + K₁ * u ^ 2 := h₁
      _ = u * C₁ := by simp only [C₁]; ring
  have hv₂ : value₂ ≤ u * C₂ := by
    calc
      value₂ ≤ c₂ * u + K₂ * u ^ 2 := h₂
      _ = u * C₂ := by simp only [C₂]; ring
  refine ⟨C₁ * C₂, mul_nonneg hC₁ hC₂, ?_⟩
  calc
    value ≤ value₁ * value₂ := hvalue
    _ ≤ (u * C₁) * (u * C₂) :=
      mul_le_mul hv₁ hv₂ hvalue₂ (mul_nonneg hu hC₁)
    _ = 0 + (C₁ * C₂) * u ^ 2 := by ring

/-- A finite supremum of quantities with the same first-order leading term
    retains that leading term.  The hidden second-order witnesses are bounded
    by their finite sum. -/
theorem FirstOrderLe.finset_univ_sup' {ι : Type*} [Fintype ι]
    (hne : (Finset.univ : Finset ι).Nonempty)
    {u leading : ℝ} (value : ι → ℝ)
    (h : ∀ i : ι, FirstOrderLe u leading (value i)) :
    FirstOrderLe u leading (Finset.univ.sup' hne value) := by
  classical
  choose K hK hvalue using h
  refine ⟨∑ i : ι, K i, Finset.sum_nonneg (fun i _hi => hK i), ?_⟩
  apply Finset.sup'_le
  intro i hi
  have hKi : K i ≤ ∑ j : ι, K j :=
    Finset.single_le_sum (fun j _hj => hK j) hi
  calc
    value i ≤ leading + K i * u ^ 2 := hvalue i
    _ ≤ leading + (∑ j : ι, K j) * u ^ 2 := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_right hKi (sq_nonneg u))

lemma FirstOrderLe.bound_mul_nonneg_right {u leading value c target : ℝ}
    (h : FirstOrderLe u leading value) (hc : 0 ≤ c)
    (htarget : target ≤ value * c) :
    FirstOrderLe u (leading * c) target := by
  rcases h with ⟨K, hK, hvalue⟩
  refine ⟨K * c, mul_nonneg hK hc, ?_⟩
  calc
    target ≤ value * c := htarget
    _ ≤ (leading + K * u ^ 2) * c := mul_le_mul_of_nonneg_right hvalue hc
    _ = leading * c + (K * c) * u ^ 2 := by ring

lemma FirstOrderLe.of_gamma_dim_mul (fp : FPModel) (d : ℕ)
    (hγ : gammaValid fp d) {x y value : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hvalue : value ≤ gamma fp d * (d : ℝ) * x * y) :
    FirstOrderLe fp.u (((d : ℝ) ^ 2) * fp.u * x * y) value := by
  refine ⟨((d : ℝ) ^ 3 * x * y) / (1 - (d : ℝ) * fp.u), ?_, ?_⟩
  · have hden_pos : 0 < 1 - (d : ℝ) * fp.u := by
      unfold gammaValid at hγ
      linarith
    have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast d.zero_le
    have hd3_nonneg : 0 ≤ (d : ℝ) ^ 3 := pow_nonneg hd_nonneg 3
    exact div_nonneg (mul_nonneg (mul_nonneg hd3_nonneg hx) hy)
      (le_of_lt hden_pos)
  · calc
      value ≤ gamma fp d * (d : ℝ) * x * y := hvalue
      _ = ((d : ℝ) ^ 2) * fp.u * x * y +
            (((d : ℝ) ^ 3 * x * y) / (1 - (d : ℝ) * fp.u)) * fp.u ^ 2 := by
            have hγeq := gamma_eq_linear_plus_quadratic_remainder fp d hγ
            have hden_ne : 1 - (d : ℝ) * fp.u ≠ 0 := by
              unfold gammaValid at hγ
              linarith
            rw [hγeq]
            field_simp [hden_ne]

/-- A product carrying two componentwise `gamma d` perturbations is purely
    second order.  This is the scalar remainder estimate used by the concrete
    DHS single-right-hand-side solve route for `DeltaL * DeltaU`. -/
lemma FirstOrderLe.of_gamma_sq_dim_mul (fp : FPModel) (d : ℕ)
    (hγ : gammaValid fp d) {x y value : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hvalue : value ≤ (d : ℝ) * gamma fp d ^ 2 * x * y) :
    FirstOrderLe fp.u 0 value := by
  refine ⟨((d : ℝ) ^ 3 * x * y) /
      (1 - (d : ℝ) * fp.u) ^ 2, ?_, ?_⟩
  · exact div_nonneg
      (mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg d) 3) hx) hy)
      (sq_nonneg (1 - (d : ℝ) * fp.u))
  · have hden_ne : 1 - (d : ℝ) * fp.u ≠ 0 := by
      unfold gammaValid at hγ
      linarith
    calc
      value ≤ (d : ℝ) * gamma fp d ^ 2 * x * y := hvalue
      _ = 0 + (((d : ℝ) ^ 3 * x * y) /
            (1 - (d : ℝ) * fp.u) ^ 2) * fp.u ^ 2 := by
        unfold gamma
        field_simp [hden_ne]
        ring

end NumStability
