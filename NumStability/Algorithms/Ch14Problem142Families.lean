/-
Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
Chapter 14, Problem 14.2 (p. 283; Appendix A, p. 558).

The pointwise predicate `FirstOrderLe u leading value` permits its hidden
constant to depend on `u`.  It therefore cannot, by itself, express the
uniform `O(u^2)` remainder used in the source's first-order analysis.  This
module supplies filter-indexed versions of the Chapter 13 (13.4)/(13.5)
operation specifications and proves that the Method 1B and Method 2C binary
block recursions preserve a genuinely uniform quadratic remainder.

The Method 2B analysis is also lifted to families.  Its exact two-product
equation is operation-derived, and the resulting residual estimate retains
the source's uncontrolled `norm(X11) * norm(L11)` factor.  Every transport
through a matrix product carries an explicit `O(1)` contract for the data
being multiplied; no final residual estimate is assumed.
-/

import NumStability.Algorithms.Ch14Problem142
import NumStability.Algorithms.Ch14Problem142Method2B
import NumStability.Algorithms.Ch14AsymptoticFamilies

namespace NumStability.Ch14Ext

open Filter Asymptotics
open scoped BigOperators Topology

/-! ### Uniform family vocabulary -/

/-- A unit-roundoff family tending to zero.  The global range assumptions are
the usual floating-point side conditions and are useful for pointwise
specializations, although the Landau composition below only needs the limit. -/
structure Ch14RoundoffFamily (ι : Type*) (l : Filter ι) where
  unit : ι → ℝ
  unit_tendsto_zero : Tendsto unit l (𝓝 0)
  unit_nonneg : ∀ t, 0 ≤ unit t
  unit_le_one : ∀ t, unit t ≤ 1

/-- Scalar local boundedness along a filter. -/
def Ch14ScalarFamilyIsBigOOne {ι : Type*} (l : Filter ι)
    (f : ι → ℝ) : Prop :=
  f =O[l] (fun _ : ι => (1 : ℝ))

/-- A genuine family-level interpretation of `value ≤ leading + O(u²)`.
The existential remainder is nonnegative, and its `O(u²)` constant is uniform
along the filter. -/
def Ch14FamilyFirstOrderLe {ι : Type*} (l : Filter ι)
    (u leading value : ι → ℝ) : Prop :=
  ∃ remainder : ι → ℝ,
    (∀ t, 0 ≤ remainder t) ∧
    (∀ t, value t ≤ leading t + remainder t) ∧
    remainder =O[l] (fun t => u t ^ 2)

theorem Ch14FamilyFirstOrderLe.mono_leading {ι : Type*} {l : Filter ι}
    {u leading₁ leading₂ value : ι → ℝ}
    (h : Ch14FamilyFirstOrderLe l u leading₁ value)
    (hle : ∀ t, leading₁ t ≤ leading₂ t) :
    Ch14FamilyFirstOrderLe l u leading₂ value := by
  rcases h with ⟨remainder, hremainder, hbound, hO⟩
  refine ⟨remainder, hremainder, ?_, hO⟩
  intro t
  exact le_trans (hbound t) (add_le_add (hle t) le_rfl)

theorem Ch14FamilyFirstOrderLe.mono_value {ι : Type*} {l : Filter ι}
    {u leading value₁ value₂ : ι → ℝ}
    (h : Ch14FamilyFirstOrderLe l u leading value₂)
    (hle : ∀ t, value₁ t ≤ value₂ t) :
    Ch14FamilyFirstOrderLe l u leading value₁ := by
  rcases h with ⟨remainder, hremainder, hbound, hO⟩
  refine ⟨remainder, hremainder, ?_, hO⟩
  intro t
  exact le_trans (hle t) (hbound t)

theorem Ch14FamilyFirstOrderLe.add {ι : Type*} {l : Filter ι}
    {u leading₁ leading₂ value₁ value₂ value : ι → ℝ}
    (h₁ : Ch14FamilyFirstOrderLe l u leading₁ value₁)
    (h₂ : Ch14FamilyFirstOrderLe l u leading₂ value₂)
    (hvalue : ∀ t, value t ≤ value₁ t + value₂ t) :
    Ch14FamilyFirstOrderLe l u
      (fun t => leading₁ t + leading₂ t) value := by
  rcases h₁ with ⟨remainder₁, hremainder₁, hbound₁, hO₁⟩
  rcases h₂ with ⟨remainder₂, hremainder₂, hbound₂, hO₂⟩
  refine ⟨fun t => remainder₁ t + remainder₂ t, ?_, ?_, ?_⟩
  · intro t
    exact add_nonneg (hremainder₁ t) (hremainder₂ t)
  · intro t
    calc
      value t ≤ value₁ t + value₂ t := hvalue t
      _ ≤ (leading₁ t + remainder₁ t) +
          (leading₂ t + remainder₂ t) :=
        add_le_add (hbound₁ t) (hbound₂ t)
      _ = (leading₁ t + leading₂ t) +
          (remainder₁ t + remainder₂ t) := by ring
  · exact hO₁.add hO₂

theorem Ch14FamilyFirstOrderLe.combineMax {ι : Type*} {l : Filter ι}
    {u leading₁ leading₂ value₁ value₂ : ι → ℝ}
    (h₁ : Ch14FamilyFirstOrderLe l u leading₁ value₁)
    (h₂ : Ch14FamilyFirstOrderLe l u leading₂ value₂) :
    Ch14FamilyFirstOrderLe l u
      (fun t => max (leading₁ t) (leading₂ t))
      (fun t => max (value₁ t) (value₂ t)) := by
  rcases h₁ with ⟨remainder₁, hremainder₁, hbound₁, hO₁⟩
  rcases h₂ with ⟨remainder₂, hremainder₂, hbound₂, hO₂⟩
  refine ⟨fun t => remainder₁ t + remainder₂ t, ?_, ?_, ?_⟩
  · intro t
    exact add_nonneg (hremainder₁ t) (hremainder₂ t)
  · intro t
    apply max_le
    · calc
        value₁ t ≤ leading₁ t + remainder₁ t := hbound₁ t
        _ ≤ max (leading₁ t) (leading₂ t) +
            (remainder₁ t + remainder₂ t) := by
          gcongr
          · exact le_max_left _ _
          · exact le_add_of_nonneg_right (hremainder₂ t)
    · calc
        value₂ t ≤ leading₂ t + remainder₂ t := hbound₂ t
        _ ≤ max (leading₁ t) (leading₂ t) +
            (remainder₁ t + remainder₂ t) := by
          gcongr
          · exact le_max_right _ _
          · exact le_add_of_nonneg_left (hremainder₁ t)
  · exact hO₁.add hO₂

/-- Multiplying a first-order family by nonnegative `O(1)` data preserves the
uniform quadratic remainder.  This is the family-level replacement for the
pointwise `FirstOrderLe.bound_mul_nonneg_right` helper. -/
theorem Ch14FamilyFirstOrderLe.mul_bounded {ι : Type*} {l : Filter ι}
    {u leading value scale target : ι → ℝ}
    (h : Ch14FamilyFirstOrderLe l u leading value)
    (hscale_nonneg : ∀ t, 0 ≤ scale t)
    (hscale : Ch14ScalarFamilyIsBigOOne l scale)
    (htarget : ∀ t, target t ≤ value t * scale t) :
    Ch14FamilyFirstOrderLe l u
      (fun t => leading t * scale t) target := by
  rcases h with ⟨remainder, hremainder, hbound, hO⟩
  refine ⟨fun t => remainder t * scale t, ?_, ?_, ?_⟩
  · intro t
    exact mul_nonneg (hremainder t) (hscale_nonneg t)
  · intro t
    calc
      target t ≤ value t * scale t := htarget t
      _ ≤ (leading t + remainder t) * scale t :=
        mul_le_mul_of_nonneg_right (hbound t) (hscale_nonneg t)
      _ = leading t * scale t + remainder t * scale t := by ring
  · simpa [Ch14ScalarFamilyIsBigOOne] using
      hO.mul hscale

/-- An exact pointwise upper bound is itself an `O` comparison when both
sides are nonnegative. -/
theorem ch14ext_isBigO_of_nonneg_le {ι : Type*} {l : Filter ι}
    {f g : ι → ℝ} (hf : ∀ t, 0 ≤ f t) (hg : ∀ t, 0 ≤ g t)
    (hfg : ∀ t, f t ≤ g t) :
    f =O[l] g := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [] with t
  simpa [Real.norm_eq_abs, abs_of_nonneg (hf t), abs_of_nonneg (hg t)]
    using hfg t

/-! ### Filter-indexed forms of (13.4) and (13.5) -/

/-- Family-level equation (13.4).  The exact computed-product equation and
the uniform first-order norm estimate are operation contracts.  The two
operand norms are explicitly `O(1)`. -/
structure Ch14MatMulFamilySpec {ι : Type*} {l : Filter ι}
    (U : Ch14RoundoffFamily ι l) {m n p : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hp : 0 < p) (cMul : ℝ)
    (A : ι → Matrix (Fin m) (Fin n) ℝ)
    (B : ι → Matrix (Fin n) (Fin p) ℝ)
    (Chat Delta : ι → Matrix (Fin m) (Fin p) ℝ) where
  equation : ∀ t, Chat t = A t * B t + Delta t
  left_norm_isBigO_one : Ch14ScalarFamilyIsBigOOne l
    (fun t => maxEntryNormRect hm hn (A t))
  right_norm_isBigO_one : Ch14ScalarFamilyIsBigOOne l
    (fun t => maxEntryNormRect hn hp (B t))
  norm_bound : Ch14FamilyFirstOrderLe l U.unit
    (fun t => cMul * U.unit t * maxEntryNormRect hm hn (A t) *
      maxEntryNormRect hn hp (B t))
    (fun t => maxEntryNormRect hm hp (Delta t))

/-- Family-level left-oriented triangular-solve equation (13.5). -/
structure Ch14TriangularSolveFamilySpec {ι : Type*} {l : Filter ι}
    (U : Ch14RoundoffFamily ι l) {m p : ℕ}
    (hm : 0 < m) (hp : 0 < p) (cSolve : ℝ)
    (T : ι → Matrix (Fin m) (Fin m) ℝ)
    (B Delta Xhat : ι → Matrix (Fin m) (Fin p) ℝ) where
  equation : ∀ t, T t * Xhat t = B t + Delta t
  triangular_norm_isBigO_one : Ch14ScalarFamilyIsBigOOne l
    (fun t => maxEntryNormRect hm hm (T t))
  solution_norm_isBigO_one : Ch14ScalarFamilyIsBigOOne l
    (fun t => maxEntryNormRect hm hp (Xhat t))
  norm_bound : Ch14FamilyFirstOrderLe l U.unit
    (fun t => cSolve * U.unit t * maxEntryNormRect hm hm (T t) *
      maxEntryNormRect hm hp (Xhat t))
    (fun t => maxEntryNormRect hm hp (Delta t))

/-- Family-level right-oriented triangular-solve equation (13.5). -/
structure Ch14RightTriangularSolveFamilySpec {ι : Type*} {l : Filter ι}
    (U : Ch14RoundoffFamily ι l) {m p : ℕ}
    (hm : 0 < m) (hp : 0 < p) (cSolve : ℝ)
    (T : ι → Matrix (Fin p) (Fin p) ℝ)
    (B Delta Xhat : ι → Matrix (Fin m) (Fin p) ℝ) where
  equation : ∀ t, Xhat t * T t = B t + Delta t
  triangular_norm_isBigO_one : Ch14ScalarFamilyIsBigOOne l
    (fun t => maxEntryNormRect hp hp (T t))
  solution_norm_isBigO_one : Ch14ScalarFamilyIsBigOOne l
    (fun t => maxEntryNormRect hm hp (Xhat t))
  norm_bound : Ch14FamilyFirstOrderLe l U.unit
    (fun t => cSolve * U.unit t * maxEntryNormRect hp hp (T t) *
      maxEntryNormRect hm hp (Xhat t))
    (fun t => maxEntryNormRect hm hp (Delta t))

/-! ### Uniform block composition -/

theorem ch14ext_problem14_2_lowerBlock_residual_family {ι : Type*}
    {l : Filter ι} {U : Ch14RoundoffFamily ι l} {r m : ℕ}
    (hr : 0 < r) (hm : 0 < m)
    (leading11 leading21 leading22 : ι → ℝ)
    (R11 : ι → Matrix (Fin r) (Fin r) ℝ)
    (R21 : ι → Matrix (Fin m) (Fin r) ℝ)
    (R22 : ι → Matrix (Fin m) (Fin m) ℝ)
    (h11 : Ch14FamilyFirstOrderLe l U.unit leading11
      (fun t => maxEntryNormRect hr hr (R11 t)))
    (h21 : Ch14FamilyFirstOrderLe l U.unit leading21
      (fun t => maxEntryNormRect hm hr (R21 t)))
    (h22 : Ch14FamilyFirstOrderLe l U.unit leading22
      (fun t => maxEntryNormRect hm hm (R22 t))) :
    Ch14FamilyFirstOrderLe l U.unit
      (fun t => max (leading11 t) (max (leading21 t) (leading22 t)))
      (fun t => maxEntryNormRect (Nat.add_pos_left hr m)
        (Nat.add_pos_left hr m)
        (higham14_problem14_2_lowerBlock (R11 t) (R21 t) (R22 t))) := by
  have hblocks := h11.combineMax (h21.combineMax h22)
  exact hblocks.mono_value (fun t =>
    higham14_problem14_2_lowerBlock_maxEntryNorm_le hr hm
      (R11 t) (R21 t) (R22 t))

/-! ### Method 1B -/

structure Ch14Problem142Method1BStepFamily {ι : Type*} {l : Filter ι}
    (U : Ch14RoundoffFamily ι l) {r m : ℕ}
    (hr : 0 < r) (hm : 0 < m) (cMul cSolve : ℝ)
    (L21 : ι → Matrix (Fin m) (Fin r) ℝ)
    (L22 : ι → Matrix (Fin m) (Fin m) ℝ)
    (X11 : ι → Matrix (Fin r) (Fin r) ℝ)
    (X21 That DeltaMul DeltaSolve :
      ι → Matrix (Fin m) (Fin r) ℝ) where
  product : Ch14MatMulFamilySpec U hm hr hr cMul
    L21 X11 That DeltaMul
  solve : Ch14TriangularSolveFamilySpec U hm hr cSolve
    L22 (fun t => -(That t)) DeltaSolve X21

theorem Ch14Problem142Method1BStepFamily.offdiag_equation
    {ι : Type*} {l : Filter ι} {U : Ch14RoundoffFamily ι l}
    {r m : ℕ} {hr : 0 < r} {hm : 0 < m} {cMul cSolve : ℝ}
    {L21 : ι → Matrix (Fin m) (Fin r) ℝ}
    {L22 : ι → Matrix (Fin m) (Fin m) ℝ}
    {X11 : ι → Matrix (Fin r) (Fin r) ℝ}
    {X21 That DeltaMul DeltaSolve :
      ι → Matrix (Fin m) (Fin r) ℝ}
    (h : Ch14Problem142Method1BStepFamily U hr hm cMul cSolve
      L21 L22 X11 X21 That DeltaMul DeltaSolve) (t : ι) :
    L21 t * X11 t + L22 t * X21 t = -DeltaMul t + DeltaSolve t := by
  rw [h.solve.equation t, h.product.equation t]
  abel

theorem Ch14Problem142Method1BStepFamily.offdiag_family
    {ι : Type*} {l : Filter ι} {U : Ch14RoundoffFamily ι l}
    {r m : ℕ} {hr : 0 < r} {hm : 0 < m} {cMul cSolve : ℝ}
    {L21 : ι → Matrix (Fin m) (Fin r) ℝ}
    {L22 : ι → Matrix (Fin m) (Fin m) ℝ}
    {X11 : ι → Matrix (Fin r) (Fin r) ℝ}
    {X21 That DeltaMul DeltaSolve :
      ι → Matrix (Fin m) (Fin r) ℝ}
    (h : Ch14Problem142Method1BStepFamily U hr hm cMul cSolve
      L21 L22 X11 X21 That DeltaMul DeltaSolve) :
    Ch14FamilyFirstOrderLe l U.unit
      (fun t =>
        cMul * U.unit t * maxEntryNormRect hm hr (L21 t) *
            maxEntryNormRect hr hr (X11 t) +
          cSolve * U.unit t * maxEntryNormRect hm hm (L22 t) *
            maxEntryNormRect hm hr (X21 t))
      (fun t => maxEntryNormRect hm hr
        (L21 t * X11 t + L22 t * X21 t)) := by
  apply h.product.norm_bound.add h.solve.norm_bound
  intro t
  rw [h.offdiag_equation t]
  exact higham14_problem14_2_maxEntryNormRect_neg_add_le hm hr
    (DeltaMul t) (DeltaSolve t)

theorem ch14ext_problem14_2_method1B_twoBlock_right_family
    {ι : Type*} {l : Filter ι} {U : Ch14RoundoffFamily ι l}
    {r m : ℕ} (hr : 0 < r) (hm : 0 < m) (cMul cSolve : ℝ)
    (leading11 leading22 : ι → ℝ)
    (L11 X11 : ι → Matrix (Fin r) (Fin r) ℝ)
    (L21 X21 : ι → Matrix (Fin m) (Fin r) ℝ)
    (L22 X22 : ι → Matrix (Fin m) (Fin m) ℝ)
    (That DeltaMul DeltaSolve : ι → Matrix (Fin m) (Fin r) ℝ)
    (h11 : Ch14FamilyFirstOrderLe l U.unit leading11
      (fun t => maxEntryNormRect hr hr
        (L11 t * X11 t - (1 : Matrix (Fin r) (Fin r) ℝ))))
    (h22 : Ch14FamilyFirstOrderLe l U.unit leading22
      (fun t => maxEntryNormRect hm hm
        (L22 t * X22 t - (1 : Matrix (Fin m) (Fin m) ℝ))))
    (hstep : Ch14Problem142Method1BStepFamily U hr hm cMul cSolve
      L21 L22 X11 X21 That DeltaMul DeltaSolve) :
    Ch14FamilyFirstOrderLe l U.unit
      (fun t => max (leading11 t)
        (max
          (cMul * U.unit t * maxEntryNormRect hm hr (L21 t) *
              maxEntryNormRect hr hr (X11 t) +
            cSolve * U.unit t * maxEntryNormRect hm hm (L22 t) *
              maxEntryNormRect hm hr (X21 t))
          (leading22 t)))
      (fun t => maxEntryNormRect (Nat.add_pos_left hr m)
        (Nat.add_pos_left hr m)
        (higham14_problem14_2_lowerBlock (L11 t) (L21 t) (L22 t) *
          higham14_problem14_2_lowerBlock (X11 t) (X21 t) (X22 t) -
            (1 : Matrix (Fin (r + m)) (Fin (r + m)) ℝ))) := by
  have hblocks := ch14ext_problem14_2_lowerBlock_residual_family hr hm
    leading11
    (fun t =>
      cMul * U.unit t * maxEntryNormRect hm hr (L21 t) *
          maxEntryNormRect hr hr (X11 t) +
        cSolve * U.unit t * maxEntryNormRect hm hm (L22 t) *
          maxEntryNormRect hm hr (X21 t))
    leading22
    (fun t => L11 t * X11 t - (1 : Matrix (Fin r) (Fin r) ℝ))
    (fun t => L21 t * X11 t + L22 t * X21 t)
    (fun t => L22 t * X22 t - (1 : Matrix (Fin m) (Fin m) ℝ))
    h11 hstep.offdiag_family h22
  exact hblocks.mono_value (fun t => by
    rw [higham14_problem14_2_lowerBlock_mul_sub_one])

/-! ### Method 2C -/

structure Ch14Problem142Method2CStepFamily {ι : Type*} {l : Filter ι}
    (U : Ch14RoundoffFamily ι l) {r m : ℕ}
    (hr : 0 < r) (hm : 0 < m) (cMul cSolve : ℝ)
    (L11 : ι → Matrix (Fin r) (Fin r) ℝ)
    (L21 X21 : ι → Matrix (Fin m) (Fin r) ℝ)
    (X22 : ι → Matrix (Fin m) (Fin m) ℝ)
    (That DeltaMul DeltaSolve : ι → Matrix (Fin m) (Fin r) ℝ) where
  product : Ch14MatMulFamilySpec U hm hm hr cMul
    X22 L21 That DeltaMul
  solve : Ch14RightTriangularSolveFamilySpec U hm hr cSolve
    L11 (fun t => -(That t)) DeltaSolve X21

theorem Ch14Problem142Method2CStepFamily.offdiag_equation
    {ι : Type*} {l : Filter ι} {U : Ch14RoundoffFamily ι l}
    {r m : ℕ} {hr : 0 < r} {hm : 0 < m} {cMul cSolve : ℝ}
    {L11 : ι → Matrix (Fin r) (Fin r) ℝ}
    {L21 X21 : ι → Matrix (Fin m) (Fin r) ℝ}
    {X22 : ι → Matrix (Fin m) (Fin m) ℝ}
    {That DeltaMul DeltaSolve : ι → Matrix (Fin m) (Fin r) ℝ}
    (h : Ch14Problem142Method2CStepFamily U hr hm cMul cSolve
      L11 L21 X21 X22 That DeltaMul DeltaSolve) (t : ι) :
    X21 t * L11 t + X22 t * L21 t = -DeltaMul t + DeltaSolve t := by
  rw [h.solve.equation t, h.product.equation t]
  abel

theorem Ch14Problem142Method2CStepFamily.offdiag_family
    {ι : Type*} {l : Filter ι} {U : Ch14RoundoffFamily ι l}
    {r m : ℕ} {hr : 0 < r} {hm : 0 < m} {cMul cSolve : ℝ}
    {L11 : ι → Matrix (Fin r) (Fin r) ℝ}
    {L21 X21 : ι → Matrix (Fin m) (Fin r) ℝ}
    {X22 : ι → Matrix (Fin m) (Fin m) ℝ}
    {That DeltaMul DeltaSolve : ι → Matrix (Fin m) (Fin r) ℝ}
    (h : Ch14Problem142Method2CStepFamily U hr hm cMul cSolve
      L11 L21 X21 X22 That DeltaMul DeltaSolve) :
    Ch14FamilyFirstOrderLe l U.unit
      (fun t =>
        cMul * U.unit t * maxEntryNormRect hm hm (X22 t) *
            maxEntryNormRect hm hr (L21 t) +
          cSolve * U.unit t * maxEntryNormRect hr hr (L11 t) *
            maxEntryNormRect hm hr (X21 t))
      (fun t => maxEntryNormRect hm hr
        (X21 t * L11 t + X22 t * L21 t)) := by
  apply h.product.norm_bound.add h.solve.norm_bound
  intro t
  rw [h.offdiag_equation t]
  exact higham14_problem14_2_maxEntryNormRect_neg_add_le hm hr
    (DeltaMul t) (DeltaSolve t)

theorem ch14ext_problem14_2_method2C_twoBlock_left_family
    {ι : Type*} {l : Filter ι} {U : Ch14RoundoffFamily ι l}
    {r m : ℕ} (hr : 0 < r) (hm : 0 < m) (cMul cSolve : ℝ)
    (leading11 leading22 : ι → ℝ)
    (L11 X11 : ι → Matrix (Fin r) (Fin r) ℝ)
    (L21 X21 : ι → Matrix (Fin m) (Fin r) ℝ)
    (L22 X22 : ι → Matrix (Fin m) (Fin m) ℝ)
    (That DeltaMul DeltaSolve : ι → Matrix (Fin m) (Fin r) ℝ)
    (h11 : Ch14FamilyFirstOrderLe l U.unit leading11
      (fun t => maxEntryNormRect hr hr
        (X11 t * L11 t - (1 : Matrix (Fin r) (Fin r) ℝ))))
    (h22 : Ch14FamilyFirstOrderLe l U.unit leading22
      (fun t => maxEntryNormRect hm hm
        (X22 t * L22 t - (1 : Matrix (Fin m) (Fin m) ℝ))))
    (hstep : Ch14Problem142Method2CStepFamily U hr hm cMul cSolve
      L11 L21 X21 X22 That DeltaMul DeltaSolve) :
    Ch14FamilyFirstOrderLe l U.unit
      (fun t => max (leading11 t)
        (max
          (cMul * U.unit t * maxEntryNormRect hm hm (X22 t) *
              maxEntryNormRect hm hr (L21 t) +
            cSolve * U.unit t * maxEntryNormRect hr hr (L11 t) *
              maxEntryNormRect hm hr (X21 t))
          (leading22 t)))
      (fun t => maxEntryNormRect (Nat.add_pos_left hr m)
        (Nat.add_pos_left hr m)
        (higham14_problem14_2_lowerBlock (X11 t) (X21 t) (X22 t) *
          higham14_problem14_2_lowerBlock (L11 t) (L21 t) (L22 t) -
            (1 : Matrix (Fin (r + m)) (Fin (r + m)) ℝ))) := by
  have hblocks := ch14ext_problem14_2_lowerBlock_residual_family hr hm
    leading11
    (fun t =>
      cMul * U.unit t * maxEntryNormRect hm hm (X22 t) *
          maxEntryNormRect hm hr (L21 t) +
        cSolve * U.unit t * maxEntryNormRect hr hr (L11 t) *
          maxEntryNormRect hm hr (X21 t))
    leading22
    (fun t => X11 t * L11 t - (1 : Matrix (Fin r) (Fin r) ℝ))
    (fun t => X21 t * L11 t + X22 t * L21 t)
    (fun t => X22 t * L22 t - (1 : Matrix (Fin m) (Fin m) ℝ))
    h11 hstep.offdiag_family h22
  exact hblocks.mono_value (fun t => by
    rw [higham14_problem14_2_lowerBlock_mul_sub_one])

/-! ### Arbitrary binary block partitions -/

/-- An operation-level Method 1B derivation over any finite binary block
partition.  Every leaf is a family of (13.5) solves and every internal node
contains only a family of (13.4)/(13.5) operations. -/
inductive Ch14Problem142Method1BFamilyDerivation {ι : Type*} {l : Filter ι}
    (U : Ch14RoundoffFamily ι l) :
    {n : ℕ} → (ι → Matrix (Fin n) (Fin n) ℝ) →
      (ι → Matrix (Fin n) (Fin n) ℝ) → (ι → ℝ) → Prop where
  | leaf {n : ℕ} (hn : 0 < n) (cSolve : ℝ)
      (L X Delta : ι → Matrix (Fin n) (Fin n) ℝ)
      (solve : Ch14TriangularSolveFamilySpec U hn hn cSolve
        L (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) Delta X) :
      Ch14Problem142Method1BFamilyDerivation U L X
        (fun t => cSolve * U.unit t * maxEntryNormRect hn hn (L t) *
          maxEntryNormRect hn hn (X t))
  | split {r m : ℕ} (hr : 0 < r) (hm : 0 < m)
      (cMul cSolve : ℝ) (leading11 leading22 : ι → ℝ)
      (L11 X11 : ι → Matrix (Fin r) (Fin r) ℝ)
      (L21 X21 : ι → Matrix (Fin m) (Fin r) ℝ)
      (L22 X22 : ι → Matrix (Fin m) (Fin m) ℝ)
      (That DeltaMul DeltaSolve : ι → Matrix (Fin m) (Fin r) ℝ)
      (head : Ch14Problem142Method1BFamilyDerivation U L11 X11 leading11)
      (tail : Ch14Problem142Method1BFamilyDerivation U L22 X22 leading22)
      (step : Ch14Problem142Method1BStepFamily U hr hm cMul cSolve
        L21 L22 X11 X21 That DeltaMul DeltaSolve) :
      Ch14Problem142Method1BFamilyDerivation U
        (fun t => higham14_problem14_2_lowerBlock (L11 t) (L21 t) (L22 t))
        (fun t => higham14_problem14_2_lowerBlock (X11 t) (X21 t) (X22 t))
        (fun t => max (leading11 t)
          (max
            (cMul * U.unit t * maxEntryNormRect hm hr (L21 t) *
                maxEntryNormRect hr hr (X11 t) +
              cSolve * U.unit t * maxEntryNormRect hm hm (L22 t) *
                maxEntryNormRect hm hr (X21 t))
            (leading22 t)))

/-- Method 1B recursive closure with one filter-uniform `O(u²)` remainder.
No residual bound appears in the derivation constructors. -/
theorem Ch14Problem142Method1BFamilyDerivation.right_residual_family
    {ι : Type*} {l : Filter ι} [NeBot l] {U : Ch14RoundoffFamily ι l}
    {n : ℕ} {L X : ι → Matrix (Fin n) (Fin n) ℝ}
    {leading : ι → ℝ}
    (h : Ch14Problem142Method1BFamilyDerivation U L X leading) :
    ∀ hn : 0 < n,
      Ch14FamilyFirstOrderLe l U.unit leading
        (fun t => maxEntryNormRect hn hn
          (L t * X t - (1 : Matrix (Fin n) (Fin n) ℝ))) := by
  induction h with
  | leaf hn cSolve L X Delta solve =>
      intro _hn'
      exact solve.norm_bound.mono_value (fun t => by
        have heq : L t * X t - (1 : Matrix (Fin _ ) (Fin _) ℝ) = Delta t := by
          rw [solve.equation t]
          abel
        rw [heq])
  | split hr hm cMul cSolve leading11 leading22 L11 X11 L21 X21 L22 X22
      That DeltaMul DeltaSolve head tail step ihHead ihTail =>
      intro _hsum
      exact ch14ext_problem14_2_method1B_twoBlock_right_family
        hr hm cMul cSolve leading11 leading22
        L11 X11 L21 X21 L22 X22 That DeltaMul DeltaSolve
        (ihHead hr) (ihTail hm) step

/-- The analogous operation-level family derivation for Method 2C. -/
inductive Ch14Problem142Method2CFamilyDerivation {ι : Type*} {l : Filter ι}
    (U : Ch14RoundoffFamily ι l) :
    {n : ℕ} → (ι → Matrix (Fin n) (Fin n) ℝ) →
      (ι → Matrix (Fin n) (Fin n) ℝ) → (ι → ℝ) → Prop where
  | leaf {n : ℕ} (hn : 0 < n) (cSolve : ℝ)
      (L X Delta : ι → Matrix (Fin n) (Fin n) ℝ)
      (solve : Ch14RightTriangularSolveFamilySpec U hn hn cSolve
        L (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) Delta X) :
      Ch14Problem142Method2CFamilyDerivation U L X
        (fun t => cSolve * U.unit t * maxEntryNormRect hn hn (L t) *
          maxEntryNormRect hn hn (X t))
  | split {r m : ℕ} (hr : 0 < r) (hm : 0 < m)
      (cMul cSolve : ℝ) (leading11 leading22 : ι → ℝ)
      (L11 X11 : ι → Matrix (Fin r) (Fin r) ℝ)
      (L21 X21 : ι → Matrix (Fin m) (Fin r) ℝ)
      (L22 X22 : ι → Matrix (Fin m) (Fin m) ℝ)
      (That DeltaMul DeltaSolve : ι → Matrix (Fin m) (Fin r) ℝ)
      (head : Ch14Problem142Method2CFamilyDerivation U L11 X11 leading11)
      (tail : Ch14Problem142Method2CFamilyDerivation U L22 X22 leading22)
      (step : Ch14Problem142Method2CStepFamily U hr hm cMul cSolve
        L11 L21 X21 X22 That DeltaMul DeltaSolve) :
      Ch14Problem142Method2CFamilyDerivation U
        (fun t => higham14_problem14_2_lowerBlock (L11 t) (L21 t) (L22 t))
        (fun t => higham14_problem14_2_lowerBlock (X11 t) (X21 t) (X22 t))
        (fun t => max (leading11 t)
          (max
            (cMul * U.unit t * maxEntryNormRect hm hm (X22 t) *
                maxEntryNormRect hm hr (L21 t) +
              cSolve * U.unit t * maxEntryNormRect hr hr (L11 t) *
                maxEntryNormRect hm hr (X21 t))
            (leading22 t)))

/-- Method 2C recursive closure with a uniform quadratic remainder. -/
theorem Ch14Problem142Method2CFamilyDerivation.left_residual_family
    {ι : Type*} {l : Filter ι} [NeBot l] {U : Ch14RoundoffFamily ι l}
    {n : ℕ} {L X : ι → Matrix (Fin n) (Fin n) ℝ}
    {leading : ι → ℝ}
    (h : Ch14Problem142Method2CFamilyDerivation U L X leading) :
    ∀ hn : 0 < n,
      Ch14FamilyFirstOrderLe l U.unit leading
        (fun t => maxEntryNormRect hn hn
          (X t * L t - (1 : Matrix (Fin n) (Fin n) ℝ))) := by
  induction h with
  | leaf hn cSolve L X Delta solve =>
      intro _hn'
      exact solve.norm_bound.mono_value (fun t => by
        have heq : X t * L t - (1 : Matrix (Fin _) (Fin _) ℝ) = Delta t := by
          rw [solve.equation t]
          abel
        rw [heq])
  | split hr hm cMul cSolve leading11 leading22 L11 X11 L21 X21 L22 X22
      That DeltaMul DeltaSolve head tail step ihHead ihTail =>
      intro _hsum
      exact ch14ext_problem14_2_method2C_twoBlock_left_family
        hr hm cMul cSolve leading11 leading22
        L11 X11 L21 X21 L22 X22 That DeltaMul DeltaSolve
        (ihHead hr) (ihTail hm) step

/-! ### Method 2B: uniform two-product obstruction -/

/-- Products of two explicitly bounded matrix families have bounded max-entry
norm. -/
theorem ch14ext_maxEntryNorm_mul_family_isBigO_one {ι : Type*}
    {l : Filter ι} {m n p : ℕ} (hm : 0 < m) (hn : 0 < n) (hp : 0 < p)
    (A : ι → Matrix (Fin m) (Fin n) ℝ)
    (B : ι → Matrix (Fin n) (Fin p) ℝ)
    (hA : Ch14ScalarFamilyIsBigOOne l
      (fun t => maxEntryNormRect hm hn (A t)))
    (hB : Ch14ScalarFamilyIsBigOOne l
      (fun t => maxEntryNormRect hn hp (B t))) :
    Ch14ScalarFamilyIsBigOOne l
      (fun t => maxEntryNormRect hm hp (A t * B t)) := by
  let productBound : ι → ℝ := fun t =>
    (n : ℝ) * maxEntryNormRect hm hn (A t) *
      maxEntryNormRect hn hp (B t)
  have hproductBound : Ch14ScalarFamilyIsBigOOne l productBound := by
    have hmul := hA.mul hB
    simpa [Ch14ScalarFamilyIsBigOOne, productBound, mul_assoc] using
      hmul.const_mul_left (n : ℝ)
  have hdom :
      (fun t => maxEntryNormRect hm hp (A t * B t)) =O[l] productBound := by
    apply ch14ext_isBigO_of_nonneg_le
    · intro t
      exact maxEntryNormRect_nonneg hm hp (A t * B t)
    · intro t
      exact mul_nonneg
        (mul_nonneg (Nat.cast_nonneg n)
          (maxEntryNormRect_nonneg hm hn (A t)))
        (maxEntryNormRect_nonneg hn hp (B t))
    · intro t
      simpa [productBound, rectMatMul, Matrix.mul_apply] using
        maxEntryNormRect_rectMatMul_le hm hn hp (A t) (B t)
  exact hdom.trans hproductBound

/-- A family of Method 2B off-diagonal updates.  `That` and `Phat` are the two
independently rounded products; `X21 = -Phat` is the actual update. -/
structure Ch14Problem142Method2BStepFamily {ι : Type*} {l : Filter ι}
    (U : Ch14RoundoffFamily ι l) {r m : ℕ}
    (hr : 0 < r) (hm : 0 < m) (cFirst cSecond : ℝ)
    (X22 : ι → Matrix (Fin m) (Fin m) ℝ)
    (L21 : ι → Matrix (Fin m) (Fin r) ℝ)
    (X11 : ι → Matrix (Fin r) (Fin r) ℝ)
    (That Phat X21 DeltaFirst DeltaSecond :
      ι → Matrix (Fin m) (Fin r) ℝ) where
  first_product : Ch14MatMulFamilySpec U hm hm hr cFirst
    X22 L21 That DeltaFirst
  second_product : Ch14MatMulFamilySpec U hm hr hr cSecond
    That X11 Phat DeltaSecond
  update : ∀ t, X21 t = -(Phat t)

/-- The two exact operation equations imply equation (14.14) memberwise. -/
theorem Ch14Problem142Method2BStepFamily.update_equation
    {ι : Type*} {l : Filter ι} {U : Ch14RoundoffFamily ι l}
    {r m : ℕ} {hr : 0 < r} {hm : 0 < m} {cFirst cSecond : ℝ}
    {X22 : ι → Matrix (Fin m) (Fin m) ℝ}
    {L21 : ι → Matrix (Fin m) (Fin r) ℝ}
    {X11 : ι → Matrix (Fin r) (Fin r) ℝ}
    {That Phat X21 DeltaFirst DeltaSecond :
      ι → Matrix (Fin m) (Fin r) ℝ}
    (h : Ch14Problem142Method2BStepFamily U hr hm cFirst cSecond
      X22 L21 X11 That Phat X21 DeltaFirst DeltaSecond) (t : ι) :
    X21 t = -(X22 t * L21 t * X11 t) +
      higham14_problem14_2_method2B_updateDelta
        (DeltaFirst t) (X11 t) (DeltaSecond t) := by
  rw [h.update t, h.second_product.equation t,
    h.first_product.equation t]
  simp only [higham14_problem14_2_method2B_updateDelta]
  rw [Matrix.add_mul]
  abel

/-- Direct family-level composition of the two product errors.  The computed
intermediate remains in the first-order coefficient, while every propagated
remainder is still uniformly `O(u²)` because `X11` is explicitly `O(1)`. -/
theorem Ch14Problem142Method2BStepFamily.updateDelta_family
    {ι : Type*} {l : Filter ι} {U : Ch14RoundoffFamily ι l}
    {r m : ℕ} {hr : 0 < r} {hm : 0 < m} {cFirst cSecond : ℝ}
    {X22 : ι → Matrix (Fin m) (Fin m) ℝ}
    {L21 : ι → Matrix (Fin m) (Fin r) ℝ}
    {X11 : ι → Matrix (Fin r) (Fin r) ℝ}
    {That Phat X21 DeltaFirst DeltaSecond :
      ι → Matrix (Fin m) (Fin r) ℝ}
    (h : Ch14Problem142Method2BStepFamily U hr hm cFirst cSecond
      X22 L21 X11 That Phat X21 DeltaFirst DeltaSecond) :
    Ch14FamilyFirstOrderLe l U.unit
      (fun t =>
        (cFirst * U.unit t * maxEntryNormRect hm hm (X22 t) *
            maxEntryNormRect hm hr (L21 t)) *
            ((r : ℝ) * maxEntryNormRect hr hr (X11 t)) +
          cSecond * U.unit t * maxEntryNormRect hm hr (That t) *
            maxEntryNormRect hr hr (X11 t))
      (fun t => maxEntryNormRect hm hr
        (higham14_problem14_2_method2B_updateDelta
          (DeltaFirst t) (X11 t) (DeltaSecond t))) := by
  have hFirst := h.first_product.norm_bound.mul_bounded
    (scale := fun t => (r : ℝ) * maxEntryNormRect hr hr (X11 t))
    (target := fun t => maxEntryNormRect hm hr (DeltaFirst t * X11 t))
    (fun t => mul_nonneg (Nat.cast_nonneg r)
      (maxEntryNormRect_nonneg hr hr (X11 t)))
    (by
      simpa [Ch14ScalarFamilyIsBigOOne] using
        h.second_product.right_norm_isBigO_one.const_mul_left (r : ℝ))
    (fun t => by
      calc
        maxEntryNormRect hm hr (DeltaFirst t * X11 t) ≤
            (r : ℝ) * maxEntryNormRect hm hr (DeltaFirst t) *
              maxEntryNormRect hr hr (X11 t) := by
          simpa [rectMatMul, Matrix.mul_apply] using
            maxEntryNormRect_rectMatMul_le hm hr hr
              (DeltaFirst t) (X11 t)
        _ = maxEntryNormRect hm hr (DeltaFirst t) *
            ((r : ℝ) * maxEntryNormRect hr hr (X11 t)) := by ring)
  apply hFirst.add h.second_product.norm_bound
  intro t
  simp only [higham14_problem14_2_method2B_updateDelta]
  calc
    maxEntryNormRect hm hr (-(DeltaFirst t * X11 t + DeltaSecond t)) =
        maxEntryNormRect hm hr (DeltaFirst t * X11 t + DeltaSecond t) :=
      higham14_problem14_2_maxEntryNormRect_neg hm hr _
    _ ≤ maxEntryNormRect hm hr (DeltaFirst t * X11 t) +
        maxEntryNormRect hm hr (DeltaSecond t) :=
      higham14_problem14_2_maxEntryNormRect_add_le hm hr _ _

/-- The Method 2B first-order coefficient, factored to display the
uncontrolled `norm(X11) * norm(L11)` multiplier.  The bracketed coefficient
contains only explicitly `O(1)` families. -/
noncomputable def ch14ext_problem14_2_method2B_familyUncontrolledLeading
    {ι : Type*} {r m : ℕ} (Uunit : ι → ℝ) (cFirst cSecond cDiag : ℝ)
    (hm : 0 < m) (hr : 0 < r)
    (X22 : ι → Matrix (Fin m) (Fin m) ℝ)
    (L21 That : ι → Matrix (Fin m) (Fin r) ℝ)
    (X11 L11 : ι → Matrix (Fin r) (Fin r) ℝ) : ι → ℝ :=
  fun t => Uunit t *
    (maxEntryNormRect hr hr (X11 t) * maxEntryNormRect hr hr (L11 t)) *
    (((r : ℝ) ^ 2 * cFirst * maxEntryNormRect hm hm (X22 t) *
        maxEntryNormRect hm hr (L21 t)) +
      (r : ℝ) * cSecond * maxEntryNormRect hm hr (That t) +
      (r : ℝ) * cDiag * maxEntryNormRect hm hr (X22 t * L21 t))

/-- The exact off-diagonal residual identity follows only from the two product
equations and the diagonal right-solve equation. -/
theorem Ch14Problem142Method2BStepFamily.offdiag_residual_equation
    {ι : Type*} {l : Filter ι} {U : Ch14RoundoffFamily ι l}
    {r m : ℕ} {hr : 0 < r} {hm : 0 < m}
    {cFirst cSecond cDiag : ℝ}
    {L11 X11 Delta11 : ι → Matrix (Fin r) (Fin r) ℝ}
    {X22 : ι → Matrix (Fin m) (Fin m) ℝ}
    {L21 : ι → Matrix (Fin m) (Fin r) ℝ}
    {That Phat X21 DeltaFirst DeltaSecond :
      ι → Matrix (Fin m) (Fin r) ℝ}
    (h : Ch14Problem142Method2BStepFamily U hr hm cFirst cSecond
      X22 L21 X11 That Phat X21 DeltaFirst DeltaSecond)
    (hDiag : Ch14RightTriangularSolveFamilySpec U hr hr cDiag
      L11 (fun _ => (1 : Matrix (Fin r) (Fin r) ℝ)) Delta11 X11)
    (t : ι) :
    X21 t * L11 t + X22 t * L21 t =
      higham14_problem14_2_method2B_updateDelta
          (DeltaFirst t) (X11 t) (DeltaSecond t) * L11 t -
        (X22 t * L21 t) * Delta11 t := by
  rw [h.update_equation t]
  rw [Matrix.add_mul, Matrix.neg_mul, Matrix.mul_assoc,
    hDiag.equation t, Matrix.mul_add, Matrix.mul_one]
  abel

/-- Uniform Method 2B obstruction.  Its exact equations are operation-derived;
the displayed first-order coefficient necessarily contains
`norm(X11) * norm(L11)`, and all propagated remainders are uniformly
`O(u²)`. -/
theorem Ch14Problem142Method2BStepFamily.offdiag_residual_family
    {ι : Type*} {l : Filter ι} {U : Ch14RoundoffFamily ι l}
    {r m : ℕ} {hr : 0 < r} {hm : 0 < m}
    {cFirst cSecond cDiag : ℝ}
    {L11 X11 Delta11 : ι → Matrix (Fin r) (Fin r) ℝ}
    {X22 : ι → Matrix (Fin m) (Fin m) ℝ}
    {L21 : ι → Matrix (Fin m) (Fin r) ℝ}
    {That Phat X21 DeltaFirst DeltaSecond :
      ι → Matrix (Fin m) (Fin r) ℝ}
    (h : Ch14Problem142Method2BStepFamily U hr hm cFirst cSecond
      X22 L21 X11 That Phat X21 DeltaFirst DeltaSecond)
    (hDiag : Ch14RightTriangularSolveFamilySpec U hr hr cDiag
      L11 (fun _ => (1 : Matrix (Fin r) (Fin r) ℝ)) Delta11 X11) :
    Ch14FamilyFirstOrderLe l U.unit
      (ch14ext_problem14_2_method2B_familyUncontrolledLeading
        (r := r) (m := m) U.unit cFirst cSecond cDiag hm hr
        X22 L21 That X11 L11)
      (fun t => maxEntryNormRect hm hr
        (X21 t * L11 t + X22 t * L21 t)) := by
  have hUpdate := h.updateDelta_family
  have hUpdatePropagated := hUpdate.mul_bounded
    (scale := fun t => (r : ℝ) * maxEntryNormRect hr hr (L11 t))
    (target := fun t => maxEntryNormRect hm hr
      (higham14_problem14_2_method2B_updateDelta
        (DeltaFirst t) (X11 t) (DeltaSecond t) * L11 t))
    (fun t => mul_nonneg (Nat.cast_nonneg r)
      (maxEntryNormRect_nonneg hr hr (L11 t)))
    (by
      simpa [Ch14ScalarFamilyIsBigOOne] using
        hDiag.triangular_norm_isBigO_one.const_mul_left (r : ℝ))
    (fun t => by
      calc
        maxEntryNormRect hm hr
            (higham14_problem14_2_method2B_updateDelta
              (DeltaFirst t) (X11 t) (DeltaSecond t) * L11 t) ≤
            (r : ℝ) * maxEntryNormRect hm hr
              (higham14_problem14_2_method2B_updateDelta
                (DeltaFirst t) (X11 t) (DeltaSecond t)) *
              maxEntryNormRect hr hr (L11 t) := by
          simpa [rectMatMul, Matrix.mul_apply] using
            maxEntryNormRect_rectMatMul_le hm hr hr
              (higham14_problem14_2_method2B_updateDelta
                (DeltaFirst t) (X11 t) (DeltaSecond t)) (L11 t)
        _ = maxEntryNormRect hm hr
              (higham14_problem14_2_method2B_updateDelta
                (DeltaFirst t) (X11 t) (DeltaSecond t)) *
            ((r : ℝ) * maxEntryNormRect hr hr (L11 t)) := by ring)
  have hProductO := ch14ext_maxEntryNorm_mul_family_isBigO_one
    hm hm hr X22 L21
    h.first_product.left_norm_isBigO_one
    h.first_product.right_norm_isBigO_one
  have hDiagPropagated := hDiag.norm_bound.mul_bounded
    (scale := fun t => (r : ℝ) * maxEntryNormRect hm hr (X22 t * L21 t))
    (target := fun t => maxEntryNormRect hm hr
      ((X22 t * L21 t) * Delta11 t))
    (fun t => mul_nonneg (Nat.cast_nonneg r)
      (maxEntryNormRect_nonneg hm hr (X22 t * L21 t)))
    (by
      simpa [Ch14ScalarFamilyIsBigOOne] using
        hProductO.const_mul_left (r : ℝ))
    (fun t => by
      calc
        maxEntryNormRect hm hr ((X22 t * L21 t) * Delta11 t) ≤
            (r : ℝ) * maxEntryNormRect hm hr (X22 t * L21 t) *
              maxEntryNormRect hr hr (Delta11 t) := by
          simpa [rectMatMul, Matrix.mul_apply] using
            maxEntryNormRect_rectMatMul_le hm hr hr
              (X22 t * L21 t) (Delta11 t)
        _ = maxEntryNormRect hr hr (Delta11 t) *
            ((r : ℝ) * maxEntryNormRect hm hr (X22 t * L21 t)) := by ring)
  have hCombined := Ch14FamilyFirstOrderLe.add
    (value := fun t => maxEntryNormRect hm hr
      (X21 t * L11 t + X22 t * L21 t))
    hUpdatePropagated hDiagPropagated (fun t => by
    change maxEntryNormRect hm hr (X21 t * L11 t + X22 t * L21 t) ≤ _
    rw [h.offdiag_residual_equation hDiag t]
    calc
      maxEntryNormRect hm hr
          (higham14_problem14_2_method2B_updateDelta
              (DeltaFirst t) (X11 t) (DeltaSecond t) * L11 t -
            (X22 t * L21 t) * Delta11 t) =
          maxEntryNormRect hm hr
            (higham14_problem14_2_method2B_updateDelta
                (DeltaFirst t) (X11 t) (DeltaSecond t) * L11 t +
              -((X22 t * L21 t) * Delta11 t)) := by rw [sub_eq_add_neg]
      _ ≤ maxEntryNormRect hm hr
            (higham14_problem14_2_method2B_updateDelta
              (DeltaFirst t) (X11 t) (DeltaSecond t) * L11 t) +
          maxEntryNormRect hm hr (-((X22 t * L21 t) * Delta11 t)) :=
        higham14_problem14_2_maxEntryNormRect_add_le hm hr _ _
      _ = maxEntryNormRect hm hr
            (higham14_problem14_2_method2B_updateDelta
              (DeltaFirst t) (X11 t) (DeltaSecond t) * L11 t) +
          maxEntryNormRect hm hr ((X22 t * L21 t) * Delta11 t) := by
        exact congrArg
          (fun z => maxEntryNormRect hm hr
            (higham14_problem14_2_method2B_updateDelta
              (DeltaFirst t) (X11 t) (DeltaSecond t) * L11 t) + z)
          (higham14_problem14_2_maxEntryNormRect_neg hm hr
            ((X22 t * L21 t) * Delta11 t)))
  exact hCombined.mono_leading (fun t => by
    simp only [ch14ext_problem14_2_method2B_familyUncontrolledLeading]
    ring_nf
    rfl)

/-- Two-block integration of the Method 2B family obstruction with a
recursively obtained trailing-block estimate. -/
theorem ch14ext_problem14_2_method2B_twoBlock_left_family
    {ι : Type*} {l : Filter ι} [NeBot l] {U : Ch14RoundoffFamily ι l}
    {r m : ℕ} (hr : 0 < r) (hm : 0 < m)
    (cFirst cSecond cDiag : ℝ) (leading22 : ι → ℝ)
    (L11 X11 Delta11 : ι → Matrix (Fin r) (Fin r) ℝ)
    (L21 X21 : ι → Matrix (Fin m) (Fin r) ℝ)
    (L22 X22 : ι → Matrix (Fin m) (Fin m) ℝ)
    (That Phat DeltaFirst DeltaSecond : ι → Matrix (Fin m) (Fin r) ℝ)
    (hStep : Ch14Problem142Method2BStepFamily U hr hm cFirst cSecond
      X22 L21 X11 That Phat X21 DeltaFirst DeltaSecond)
    (hDiag : Ch14RightTriangularSolveFamilySpec U hr hr cDiag
      L11 (fun _ => (1 : Matrix (Fin r) (Fin r) ℝ)) Delta11 X11)
    (h22 : Ch14FamilyFirstOrderLe l U.unit leading22
      (fun t => maxEntryNormRect hm hm
        (X22 t * L22 t - (1 : Matrix (Fin m) (Fin m) ℝ)))) :
    Ch14FamilyFirstOrderLe l U.unit
      (fun t => max
        (cDiag * U.unit t * maxEntryNormRect hr hr (L11 t) *
          maxEntryNormRect hr hr (X11 t))
        (max
          (ch14ext_problem14_2_method2B_familyUncontrolledLeading
            (r := r) (m := m) U.unit cFirst cSecond cDiag hm hr
            X22 L21 That X11 L11 t)
          (leading22 t)))
      (fun t => maxEntryNormRect (Nat.add_pos_left hr m)
        (Nat.add_pos_left hr m)
        (higham14_problem14_2_lowerBlock (X11 t) (X21 t) (X22 t) *
          higham14_problem14_2_lowerBlock (L11 t) (L21 t) (L22 t) -
            (1 : Matrix (Fin (r + m)) (Fin (r + m)) ℝ))) := by
  have h11 := Ch14FamilyFirstOrderLe.mono_value
    (value₁ := fun t => maxEntryNormRect hr hr
      (X11 t * L11 t - (1 : Matrix (Fin r) (Fin r) ℝ)))
    hDiag.norm_bound (fun t => by
    have heq : X11 t * L11 t - (1 : Matrix (Fin r) (Fin r) ℝ) =
        Delta11 t := by
      rw [hDiag.equation t]
      abel
    change maxEntryNormRect hr hr
      (X11 t * L11 t - (1 : Matrix (Fin r) (Fin r) ℝ)) ≤ _
    rw [heq])
  have h21 := hStep.offdiag_residual_family hDiag
  have hblocks := ch14ext_problem14_2_lowerBlock_residual_family hr hm
    (fun t => cDiag * U.unit t * maxEntryNormRect hr hr (L11 t) *
      maxEntryNormRect hr hr (X11 t))
    (ch14ext_problem14_2_method2B_familyUncontrolledLeading
      (r := r) (m := m) U.unit cFirst cSecond cDiag hm hr
      X22 L21 That X11 L11)
    leading22
    (fun t => X11 t * L11 t - (1 : Matrix (Fin r) (Fin r) ℝ))
    (fun t => X21 t * L11 t + X22 t * L21 t)
    (fun t => X22 t * L22 t - (1 : Matrix (Fin m) (Fin m) ℝ))
    h11 h21 h22
  exact hblocks.mono_value (fun t => by
    rw [higham14_problem14_2_lowerBlock_mul_sub_one])

end NumStability.Ch14Ext
