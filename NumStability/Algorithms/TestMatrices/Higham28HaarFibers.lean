/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Prod

namespace MeasureTheory

open Set Measure
open scoped ENNReal

/-! # Two finite homogeneous-space uniqueness principles

These lemmas isolate the measure theory used in Stewart's orthogonal-matrix
producer.  The first says that a probability law on a group is determined by
its quotient coordinate and a Haar-distributed right fiber.  The second is
uniqueness of an invariant probability law for a transitive group action.
Both arguments are direct applications of Tonelli's theorem.
-/

/-- Two probability measures on `G` agree when they have the same `π`
push-forward, are invariant along the same right `H`-fibers, and every fiber
has a measurable representative.  The measure `ν` supplies the normalized
left-Haar average on a fiber. -/
theorem measure_eq_of_right_fiber_average
    {G H X : Type*}
    [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    [Group H] [MeasurableSpace H] [MeasurableMul₂ H]
    [MeasurableSpace X]
    (ι : H →* G) (hι : Measurable ι)
    (π : G → X) (hπ : Measurable π)
    (s : X → G) (hs : Measurable s)
    (hfiber : ∀ g : G, ∃ k : H, g = s (π g) * ι k)
    (ν : Measure H) [SFinite ν] [IsProbabilityMeasure ν]
    [ν.IsMulLeftInvariant]
    (μ μ' : Measure G) [SFinite μ] [SFinite μ']
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hμ : ∀ k : H, Measure.map (fun g : G => g * ι k) μ = μ)
    (hμ' : ∀ k : H, Measure.map (fun g : G => g * ι k) μ' = μ')
    (hquot : Measure.map π μ = Measure.map π μ') :
    μ = μ' := by
  apply Measure.ext
  intro A hA
  let e : G → ℝ≥0∞ := A.indicator (fun _ => 1)
  let F : G → ℝ≥0∞ := fun g => ∫⁻ k : H, e (g * ι k) ∂ν
  let φ : X → ℝ≥0∞ := fun x => F (s x)
  have he : Measurable e := measurable_const.indicator hA
  have hmul : Measurable (fun p : G × H => p.1 * ι p.2) :=
    measurable_fst.mul (hι.comp measurable_snd)
  have huncurry : Measurable (Function.uncurry fun g k => e (g * ι k)) :=
    he.comp hmul
  have hF : Measurable F := huncurry.lintegral_prod_right
  have hφ : Measurable φ := hF.comp hs
  have hF_fiber : ∀ g : G, F g = φ (π g) := by
    intro g
    obtain ⟨k, hk⟩ := hfiber g
    unfold F φ
    conv_lhs => rw [hk]
    change (∫⁻ h : H, e ((s (π g) * ι k) * ι h) ∂ν) =
      ∫⁻ h : H, e (s (π g) * ι h) ∂ν
    simpa only [mul_assoc, map_mul] using
      (lintegral_mul_left_eq_self
        (μ := ν) (fun h : H => e (s (π g) * ι h)) k)
  have havg (m : Measure G) [SFinite m] [IsProbabilityMeasure m]
      (hm : ∀ k : H, Measure.map (fun g : G => g * ι k) m = m) :
      m A = ∫⁻ g, F g ∂m := by
    have hright (k : H) : Measurable (fun g : G => g * ι k) :=
      measurable_id.mul measurable_const
    have hinner (k : H) : (∫⁻ g : G, e (g * ι k) ∂m) = m A := by
      rw [← lintegral_map he (hright k), hm k]
      exact lintegral_indicator_one hA
    calc
      m A = ∫⁻ k : H, m A ∂ν := by simp
      _ = ∫⁻ k : H, ∫⁻ g : G, e (g * ι k) ∂m ∂ν := by
        apply lintegral_congr
        intro k
        exact (hinner k).symm
      _ = ∫⁻ g : G, ∫⁻ k : H, e (g * ι k) ∂ν ∂m := by
        exact lintegral_lintegral_swap
          (huncurry.comp measurable_swap).aemeasurable
      _ = ∫⁻ g : G, F g ∂m := rfl
  rw [havg μ hμ, havg μ' hμ']
  simp_rw [hF_fiber]
  rw [← lintegral_map hφ hπ, ← lintegral_map hφ hπ, hquot]

/-- Left-fiber counterpart of `measure_eq_of_right_fiber_average`.  Two
probability measures on `G` agree when they have the same quotient law, are
invariant along the same left `H`-fibers, and every fiber has a measurable
representative.  Here `ν` supplies the normalized right-Haar average on a
fiber. -/
theorem measure_eq_of_left_fiber_average
    {G H X : Type*}
    [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    [Group H] [MeasurableSpace H] [MeasurableMul₂ H]
    [MeasurableSpace X]
    (ι : H →* G) (hι : Measurable ι)
    (π : G → X) (hπ : Measurable π)
    (s : X → G) (hs : Measurable s)
    (hfiber : ∀ g : G, ∃ k : H, g = ι k * s (π g))
    (ν : Measure H) [SFinite ν] [IsProbabilityMeasure ν]
    [ν.IsMulRightInvariant]
    (μ μ' : Measure G) [SFinite μ] [SFinite μ']
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hμ : ∀ k : H, Measure.map (fun g : G => ι k * g) μ = μ)
    (hμ' : ∀ k : H, Measure.map (fun g : G => ι k * g) μ' = μ')
    (hquot : Measure.map π μ = Measure.map π μ') :
    μ = μ' := by
  apply Measure.ext
  intro A hA
  let e : G → ℝ≥0∞ := A.indicator (fun _ => 1)
  let F : G → ℝ≥0∞ := fun g => ∫⁻ k : H, e (ι k * g) ∂ν
  let φ : X → ℝ≥0∞ := fun x => F (s x)
  have he : Measurable e := measurable_const.indicator hA
  have hmul : Measurable (fun p : H × G => ι p.1 * p.2) :=
    (hι.comp measurable_fst).mul measurable_snd
  have huncurry : Measurable (Function.uncurry fun k g => e (ι k * g)) :=
    he.comp hmul
  have hF : Measurable F := huncurry.lintegral_prod_left
  have hφ : Measurable φ := hF.comp hs
  have hF_fiber : ∀ g : G, F g = φ (π g) := by
    intro g
    obtain ⟨k, hk⟩ := hfiber g
    unfold F φ
    conv_lhs => rw [hk]
    change (∫⁻ h : H, e (ι h * (ι k * s (π g))) ∂ν) =
      ∫⁻ h : H, e (ι h * s (π g)) ∂ν
    simpa only [← mul_assoc, map_mul] using
      (lintegral_mul_right_eq_self
        (μ := ν) (fun h : H => e (ι h * s (π g))) k)
  have havg (m : Measure G) [SFinite m] [IsProbabilityMeasure m]
      (hm : ∀ k : H, Measure.map (fun g : G => ι k * g) m = m) :
      m A = ∫⁻ g, F g ∂m := by
    have hleft (k : H) : Measurable (fun g : G => ι k * g) :=
      measurable_const.mul measurable_id
    have hinner (k : H) : (∫⁻ g : G, e (ι k * g) ∂m) = m A := by
      rw [← lintegral_map he (hleft k), hm k]
      exact lintegral_indicator_one hA
    calc
      m A = ∫⁻ k : H, m A ∂ν := by simp
      _ = ∫⁻ k : H, ∫⁻ g : G, e (ι k * g) ∂m ∂ν := by
        apply lintegral_congr
        intro k
        exact (hinner k).symm
      _ = ∫⁻ g : G, ∫⁻ k : H, e (ι k * g) ∂ν ∂m := by
        exact lintegral_lintegral_swap huncurry.aemeasurable
      _ = ∫⁻ g : G, F g ∂m := rfl
  rw [havg μ hμ, havg μ' hμ']
  simp_rw [hF_fiber]
  rw [← lintegral_map hφ hπ, ← lintegral_map hφ hπ, hquot]

/-- A transitive measurable action has at most one invariant probability
measure.  The proof averages an indicator over a normalized right-Haar law on
the acting group and uses transitivity to show that the average is constant. -/
theorem measure_eq_of_invariant_probability_of_pretransitive
    {G X : Type*}
    [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    [MeasurableSpace X] [Nonempty X] [MulAction G X]
    [MeasurableSMul₂ G X]
    (htrans : ∀ x y : X, ∃ g : G, y = g • x)
    (ρ : Measure G) [SFinite ρ] [IsProbabilityMeasure ρ]
    [ρ.IsMulRightInvariant]
    (μ μ' : Measure X) [SFinite μ] [SFinite μ']
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hμ : ∀ g : G, Measure.map (fun x : X => g • x) μ = μ)
    (hμ' : ∀ g : G, Measure.map (fun x : X => g • x) μ' = μ') :
    μ = μ' := by
  apply Measure.ext
  intro A hA
  let e : X → ℝ≥0∞ := A.indicator (fun _ => 1)
  let F : X → ℝ≥0∞ := fun x => ∫⁻ g : G, e (g • x) ∂ρ
  have he : Measurable e := measurable_const.indicator hA
  have hact : Measurable (fun p : G × X => p.1 • p.2) :=
    measurable_fst.smul measurable_snd
  have huncurry : Measurable (Function.uncurry fun g x => e (g • x)) :=
    he.comp hact
  have hF_const : ∀ x y : X, F x = F y := by
    intro x y
    obtain ⟨k, hk⟩ := htrans x y
    unfold F
    conv_rhs => rw [hk]
    simpa only [mul_smul] using
      (lintegral_mul_right_eq_self
        (μ := ρ) (fun g : G => e (g • x)) k).symm
  let x₀ : X := Classical.choice ‹Nonempty X›
  have havg (m : Measure X) [SFinite m] [IsProbabilityMeasure m]
      (hm : ∀ g : G, Measure.map (fun x : X => g • x) m = m) :
      m A = F x₀ := by
    have hsmul (g : G) : Measurable (fun x : X => g • x) :=
      measurable_const.smul measurable_id
    have hinner (g : G) : (∫⁻ x : X, e (g • x) ∂m) = m A := by
      rw [← lintegral_map he (hsmul g), hm g]
      exact lintegral_indicator_one hA
    calc
      m A = ∫⁻ g : G, m A ∂ρ := by simp
      _ = ∫⁻ g : G, ∫⁻ x : X, e (g • x) ∂m ∂ρ := by
        apply lintegral_congr
        intro g
        exact (hinner g).symm
      _ = ∫⁻ x : X, ∫⁻ g : G, e (g • x) ∂ρ ∂m := by
        exact lintegral_lintegral_swap huncurry.aemeasurable
      _ = ∫⁻ x : X, F x ∂m := rfl
      _ = ∫⁻ _x : X, F x₀ ∂m := by
        apply lintegral_congr
        intro x
        exact hF_const x x₀
      _ = F x₀ := by simp
  exact (havg μ hμ).trans (havg μ' hμ').symm

end MeasureTheory
