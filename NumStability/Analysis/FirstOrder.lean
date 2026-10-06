/-
  NumStability/Analysis/FirstOrder.lean

  Uniform first-order asymptotic vocabulary shared by source formalizations.

  A pointwise assertion at one fixed nonzero unit roundoff cannot express a
  uniform `O(u^2)` remainder: its hidden constant can always be chosen after
  seeing that value of `u`.  The definitions below instead index the complete
  computation by a filter and require one Landau constant along that filter.
-/

import Mathlib.Analysis.Asymptotics.Lemmas

namespace NumStability

open Filter Asymptotics
open scoped Topology

/-- A family of unit roundoffs converging to zero along `l`. -/
structure RoundoffFamily (ι : Type*) (l : Filter ι) where
  unit : ι → ℝ
  unit_tendsto_zero : Tendsto unit l (𝓝 0)
  unit_nonneg : ∀ t, 0 ≤ unit t
  unit_le_one : ∀ t, unit t ≤ 1

/-- Scalar local boundedness (`O(1)`) along a filter. -/
def ScalarFamilyIsBigOOne {ι : Type*} (l : Filter ι)
    (f : ι → ℝ) : Prop :=
  f =O[l] (fun _ : ι => (1 : ℝ))

/-- A pointwise comparison of nonnegative scalar families is an asymptotic
comparison with constant one. -/
theorem scalarFamily_isBigO_of_nonneg_le {ι : Type*} {l : Filter ι}
    {f g : ι → ℝ} (hf : ∀ t, 0 ≤ f t) (hg : ∀ t, 0 ≤ g t)
    (hfg : ∀ t, f t ≤ g t) :
    f =O[l] g := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [] with t
  simpa [Real.norm_eq_abs, abs_of_nonneg (hf t), abs_of_nonneg (hg t)]
    using hfg t

namespace ScalarFamilyIsBigOOne

theorem const {ι : Type*} {l : Filter ι} (c : ℝ) :
    ScalarFamilyIsBigOOne l (fun _ : ι => c) := by
  simpa [ScalarFamilyIsBigOOne] using
    (Asymptotics.isBigO_refl (fun _ : ι => (1 : ℝ)) l).const_mul_left c

theorem add {ι : Type*} {l : Filter ι} {f g : ι → ℝ}
    (hf : ScalarFamilyIsBigOOne l f)
    (hg : ScalarFamilyIsBigOOne l g) :
    ScalarFamilyIsBigOOne l (fun t => f t + g t) := by
  simpa [ScalarFamilyIsBigOOne] using Asymptotics.IsBigO.add hf hg

theorem mul {ι : Type*} {l : Filter ι} {f g : ι → ℝ}
    (hf : ScalarFamilyIsBigOOne l f)
    (hg : ScalarFamilyIsBigOOne l g) :
    ScalarFamilyIsBigOOne l (fun t => f t * g t) := by
  simpa [ScalarFamilyIsBigOOne] using Asymptotics.IsBigO.mul hf hg

theorem mono {ι : Type*} {l : Filter ι} {f g : ι → ℝ}
    (hf : ∀ t, 0 ≤ f t) (hg : ∀ t, 0 ≤ g t)
    (hfg : ∀ t, f t ≤ g t)
    (hgO : ScalarFamilyIsBigOOne l g) :
    ScalarFamilyIsBigOOne l f := by
  exact (scalarFamily_isBigO_of_nonneg_le hf hg hfg).trans hgO

end ScalarFamilyIsBigOOne

namespace RoundoffFamily

/-- A globally bounded unit-roundoff family is `O(1)`. -/
theorem unit_isBigO_one {ι : Type*} {l : Filter ι}
    (U : RoundoffFamily ι l) :
    ScalarFamilyIsBigOOne l U.unit := by
  apply ScalarFamilyIsBigOOne.mono U.unit_nonneg (fun _ => zero_le_one)
  · exact U.unit_le_one
  · exact ScalarFamilyIsBigOOne.const 1

/-- Since unit roundoff is globally at most one, `u² = O(u)`. -/
theorem unit_sq_isBigO_unit {ι : Type*} {l : Filter ι}
    (U : RoundoffFamily ι l) :
    (fun t => U.unit t ^ 2) =O[l] U.unit := by
  apply scalarFamily_isBigO_of_nonneg_le
  · intro t
    exact sq_nonneg _
  · exact U.unit_nonneg
  · intro t
    nlinarith [U.unit_nonneg t, U.unit_le_one t]

end RoundoffFamily

/-- A genuine family-level interpretation of `value ≤ leading + O(u²)`.

The nonnegative remainder and its Landau constant are uniform along `l`.
Unlike a pointwise existential coefficient at a fixed nonzero `u`, this
predicate is not automatically true for arbitrary `leading` and `value`.
-/
def FamilyFirstOrderLe {ι : Type*} (l : Filter ι)
    (u leading value : ι → ℝ) : Prop :=
  ∃ remainder : ι → ℝ,
    (∀ t, 0 ≤ remainder t) ∧
    (∀ t, value t ≤ leading t + remainder t) ∧
    remainder =O[l] (fun t => u t ^ 2)

/-- A family-level `value ≤ base + O(u)` comparison.  This is the natural
contract for source phrases such as two computed factor products being equal
"to first order"; multiplying its remainder by `u` produces `O(u²)`. -/
def FamilyLinearRemainderLe {ι : Type*} (l : Filter ι)
    (u base value : ι → ℝ) : Prop :=
  ∃ remainder : ι → ℝ,
    (∀ t, 0 ≤ remainder t) ∧
    (∀ t, value t ≤ base t + remainder t) ∧
    remainder =O[l] u

namespace FamilyLinearRemainderLe

theorem of_le {ι : Type*} {l : Filter ι}
    {u base value : ι → ℝ} (h : ∀ t, value t ≤ base t) :
    FamilyLinearRemainderLe l u base value := by
  refine ⟨fun _ => 0, fun _ => le_rfl, ?_,
    Asymptotics.isBigO_zero u l⟩
  intro t
  simpa using h t

theorem mono_base {ι : Type*} {l : Filter ι}
    {u base₁ base₂ value : ι → ℝ}
    (h : FamilyLinearRemainderLe l u base₁ value)
    (hle : ∀ t, base₁ t ≤ base₂ t) :
    FamilyLinearRemainderLe l u base₂ value := by
  rcases h with ⟨remainder, hremainder, hbound, hO⟩
  refine ⟨remainder, hremainder, ?_, hO⟩
  intro t
  exact le_trans (hbound t) (add_le_add (hle t) le_rfl)

end FamilyLinearRemainderLe

namespace FamilyFirstOrderLe

theorem of_le {ι : Type*} {l : Filter ι}
    {u leading value : ι → ℝ}
    (h : ∀ t, value t ≤ leading t) :
    FamilyFirstOrderLe l u leading value := by
  refine ⟨fun _ => 0, fun _ => le_rfl, ?_,
    Asymptotics.isBigO_zero (fun t => u t ^ 2) l⟩
  intro t
  simpa using h t

/-- A single quadratic coefficient, chosen independently of the family
index, gives a uniform first-order bound. -/
theorem of_uniform_quadratic {ι : Type*} {l : Filter ι}
    {u leading value : ι → ℝ} {K : ℝ}
    (hK : 0 ≤ K)
    (h : ∀ t, value t ≤ leading t + K * u t ^ 2) :
    FamilyFirstOrderLe l u leading value := by
  refine ⟨fun t => K * u t ^ 2, fun t => mul_nonneg hK (sq_nonneg _), h, ?_⟩
  simpa using
    (Asymptotics.isBigO_refl (fun t => u t ^ 2) l).const_mul_left K

/-- Regression theorem excluding the pointwise-vacuity bug: when `u` tends
to zero along a nontrivial filter, the constant value `1` is not bounded by
`0 + O(u²)`. -/
theorem not_const_one_zero {ι : Type*} {l : Filter ι} [NeBot l]
    {u : ι → ℝ} (hu : Tendsto u l (𝓝 0)) :
    ¬ FamilyFirstOrderLe l u (fun _ => 0) (fun _ => 1) := by
  rintro ⟨remainder, _hremainder, hbound, hO⟩
  have huSq : Tendsto (fun t => u t ^ 2) l (𝓝 0) := by
    simpa using hu.pow 2
  have hrem : Tendsto remainder l (𝓝 0) := hO.trans_tendsto huSq
  have hsmall : ∀ᶠ t in l, remainder t < 1 :=
    (tendsto_order.mp hrem).2 1 zero_lt_one
  obtain ⟨t, ht⟩ := hsmall.exists
  have hlarge : 1 ≤ remainder t := by
    simpa using hbound t
  exact (not_lt_of_ge hlarge) ht

theorem mono_leading {ι : Type*} {l : Filter ι}
    {u leading₁ leading₂ value : ι → ℝ}
    (h : FamilyFirstOrderLe l u leading₁ value)
    (hle : ∀ t, leading₁ t ≤ leading₂ t) :
    FamilyFirstOrderLe l u leading₂ value := by
  rcases h with ⟨remainder, hremainder, hbound, hO⟩
  refine ⟨remainder, hremainder, ?_, hO⟩
  intro t
  exact le_trans (hbound t) (add_le_add (hle t) le_rfl)

theorem mono_value {ι : Type*} {l : Filter ι}
    {u leading value₁ value₂ : ι → ℝ}
    (h : FamilyFirstOrderLe l u leading value₂)
    (hle : ∀ t, value₁ t ≤ value₂ t) :
    FamilyFirstOrderLe l u leading value₁ := by
  rcases h with ⟨remainder, hremainder, hbound, hO⟩
  refine ⟨remainder, hremainder, ?_, hO⟩
  intro t
  exact le_trans (hle t) (hbound t)

theorem add {ι : Type*} {l : Filter ι}
    {u leading₁ leading₂ value₁ value₂ value : ι → ℝ}
    (h₁ : FamilyFirstOrderLe l u leading₁ value₁)
    (h₂ : FamilyFirstOrderLe l u leading₂ value₂)
    (hvalue : ∀ t, value t ≤ value₁ t + value₂ t) :
    FamilyFirstOrderLe l u
      (fun t => leading₁ t + leading₂ t) value := by
  rcases h₁ with ⟨remainder₁, hremainder₁, hbound₁, hO₁⟩
  rcases h₂ with ⟨remainder₂, hremainder₂, hbound₂, hO₂⟩
  refine ⟨fun t => remainder₁ t + remainder₂ t, ?_, ?_, hO₁.add hO₂⟩
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

theorem combineMax {ι : Type*} {l : Filter ι}
    {u leading₁ leading₂ value₁ value₂ : ι → ℝ}
    (h₁ : FamilyFirstOrderLe l u leading₁ value₁)
    (h₂ : FamilyFirstOrderLe l u leading₂ value₂) :
    FamilyFirstOrderLe l u
      (fun t => max (leading₁ t) (leading₂ t))
      (fun t => max (value₁ t) (value₂ t)) := by
  rcases h₁ with ⟨remainder₁, hremainder₁, hbound₁, hO₁⟩
  rcases h₂ with ⟨remainder₂, hremainder₂, hbound₂, hO₂⟩
  refine ⟨fun t => remainder₁ t + remainder₂ t, ?_, ?_, hO₁.add hO₂⟩
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

/-- Multiplication by nonnegative `O(1)` data preserves a uniform quadratic
remainder. -/
theorem mul_bounded {ι : Type*} {l : Filter ι}
    {u leading value scale target : ι → ℝ}
    (h : FamilyFirstOrderLe l u leading value)
    (hscale_nonneg : ∀ t, 0 ≤ scale t)
    (hscale : ScalarFamilyIsBigOOne l scale)
    (htarget : ∀ t, target t ≤ value t * scale t) :
    FamilyFirstOrderLe l u
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
  · simpa [ScalarFamilyIsBigOOne] using hO.mul hscale

/-- Replace a varying coefficient by a first-order-close upper coefficient.
The outer factor `c*u` turns the transfer's `O(u)` remainder into `O(u²)`. -/
theorem coefficient_of_linear_transfer_to {ι : Type*} {l : Filter ι}
    {u fixed oldCoefficient newCoefficient value : ι → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hu : ∀ t, 0 ≤ u t)
    (h : FamilyFirstOrderLe l u
      (fun t => c * u t * (fixed t + oldCoefficient t)) value)
    (htransfer : FamilyLinearRemainderLe l u newCoefficient oldCoefficient) :
    FamilyFirstOrderLe l u
      (fun t => c * u t * (fixed t + newCoefficient t)) value := by
  rcases h with ⟨remainder, hremainder, hbound, hO⟩
  rcases htransfer with ⟨transfer, htransfer_nonneg, hcoefficient, htransferO⟩
  refine ⟨fun t => remainder t + c * u t * transfer t, ?_, ?_, ?_⟩
  · intro t
    exact add_nonneg (hremainder t)
      (mul_nonneg (mul_nonneg hc (hu t)) (htransfer_nonneg t))
  · intro t
    calc
      value t ≤ c * u t * (fixed t + oldCoefficient t) + remainder t := hbound t
      _ = c * u t * fixed t + c * u t * oldCoefficient t +
          remainder t := by ring
      _ ≤ c * u t * fixed t +
          c * u t * (newCoefficient t + transfer t) + remainder t := by
        have hmul := mul_le_mul_of_nonneg_left (hcoefficient t)
          (mul_nonneg hc (hu t))
        linarith
      _ = c * u t * (fixed t + (newCoefficient t + transfer t)) +
          remainder t := by ring
      _ = c * u t * (fixed t + newCoefficient t) +
          (remainder t + c * u t * transfer t) := by ring
  · have hcu : (fun t => c * u t) =O[l] u :=
      (Asymptotics.isBigO_refl u l).const_mul_left c
    have hproduct : (fun t => c * u t * transfer t) =O[l]
        (fun t => u t ^ 2) := by
      simpa [pow_two] using hcu.mul htransferO
    exact hO.add hproduct

end FamilyFirstOrderLe

end NumStability
