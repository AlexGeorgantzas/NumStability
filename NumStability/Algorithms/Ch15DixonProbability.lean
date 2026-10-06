/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.Ch15CondEstimators
import NumStability.Algorithms.TestMatrices.Higham28OrthogonalCoordinates
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! Gaussian-direction small-ball estimates used by Higham Theorem 15.6 (Dixon). -/

namespace NumStability

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

theorem ch15_inv_sqrt_two_pi_le :
    1 / Real.sqrt (2 * Real.pi) ≤ (399 : ℝ) / 1000 := by
  have hsq : ((1000 : ℝ) / 399) ^ 2 ≤ 2 * Real.pi := by
    have hpi := Real.pi_gt_d20
    norm_num at hpi ⊢
    nlinarith
  have hsqrt : (1000 : ℝ) / 399 ≤ Real.sqrt (2 * Real.pi) := by
    have hnonneg : 0 ≤ 2 * Real.pi := by positivity
    nlinarith [Real.sq_sqrt hnonneg, Real.sqrt_nonneg (2 * Real.pi)]
  calc
    1 / Real.sqrt (2 * Real.pi) ≤ 1 / ((1000 : ℝ) / 399) :=
      one_div_le_one_div_of_le (by norm_num) hsqrt
    _ = (399 : ℝ) / 1000 := by norm_num

theorem ch15_standardGaussian_pdf_le (x : ℝ) :
    gaussianPDFReal 0 1 x ≤ (399 : ℝ) / 1000 := by
  rw [gaussianPDFReal]
  norm_num only [NNReal.coe_one, sub_zero, mul_one]
  have hexp : Real.exp (-(x ^ 2) / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg x]
  have hinv : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ :=
    inv_nonneg.mpr (Real.sqrt_nonneg _)
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) ≤
        (Real.sqrt (2 * Real.pi))⁻¹ := by nlinarith
    _ ≤ (399 : ℝ) / 1000 := by
      simpa [one_div] using ch15_inv_sqrt_two_pi_le

theorem ch15_standardGaussian_abs_le (a : ℝ) (ha : 0 ≤ a) :
    gaussianReal 0 1 {x : ℝ | |x| ≤ a} ≤
      ENNReal.ofReal (((399 : ℝ) / 500) * a) := by
  have hset : {x : ℝ | |x| ≤ a} = Set.Icc (-a) a := by
    ext x
    simp [abs_le]
  rw [hset, gaussianReal_apply_eq_integral 0 one_ne_zero]
  apply ENNReal.ofReal_le_ofReal
  calc
    ∫ x in Set.Icc (-a) a, gaussianPDFReal 0 1 x ≤
        ∫ _x in Set.Icc (-a) a, ((399 : ℝ) / 1000) := by
      apply setIntegral_mono_on
      · exact (integrable_gaussianPDFReal 0 1).integrableOn
      · exact integrableOn_const (by simp [Real.volume_Icc])
      · exact measurableSet_Icc
      · intro x _
        exact ch15_standardGaussian_pdf_le x
    _ = ((399 : ℝ) / 500) * a := by
      rw [setIntegral_const]
      simp [Real.volume_Icc, ha]
      ring

theorem ch15_standardGaussian_coordinate_sq_integral
    (d : ℕ) (i : Fin d) :
    ∫ z, (z i) ^ 2 ∂standardGaussianVectorMeasure d = 1 := by
  have hmean : (∫ z, z i ∂standardGaussianVectorMeasure d) = 0 := by
    simpa using (standardGaussianVectorCoordinate_hasLaw d i).integral_eq
  have hvar := (standardGaussianVectorCoordinate_hasLaw d i).variance_eq
  rw [variance_eq_integral (measurable_pi_apply i).aemeasurable] at hvar
  simp [hmean] at hvar
  exact hvar

theorem ch15_standardGaussian_norm_sq_integral (d : ℕ) :
    ∫ z, ‖WithLp.toLp 2 z‖ ^ 2 ∂standardGaussianVectorMeasure d = d := by
  simp_rw [EuclideanSpace.norm_sq_eq]
  rw [integral_finset_sum]
  · calc
      ∑ i, ∫ z, ‖z i‖ ^ 2 ∂standardGaussianVectorMeasure d =
          ∑ _i : Fin d, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        simpa [Real.norm_eq_abs, sq_abs] using
          ch15_standardGaussian_coordinate_sq_integral d i
      _ = d := by simp
  · intro i _
    have hi := (standardGaussianVectorCoordinate_memLp_two d i).integrable_norm_pow
      (by norm_num)
    simpa [Real.norm_eq_abs, sq_abs, pow_two] using hi

theorem ch15_standardGaussian_norm_integral_le_sqrt (d : ℕ) :
    ∫ z, ‖WithLp.toLp 2 z‖ ∂standardGaussianVectorMeasure d ≤
      Real.sqrt d := by
  have hvec : MemLp (fun z : Fin d → ℝ => WithLp.toLp 2 z) 2
      (standardGaussianVectorMeasure d) := by
    apply MemLp.of_eval_piLp
    intro i
    exact standardGaussianVectorCoordinate_memLp_two d i
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hf : MemLp (fun z : Fin d → ℝ => ‖WithLp.toLp 2 z‖)
      (ENNReal.ofReal (2 : ℝ)) (standardGaussianVectorMeasure d) := by
    simpa using hvec.norm
  have hg : MemLp (fun _z : Fin d → ℝ => (1 : ℝ))
      (ENNReal.ofReal (2 : ℝ)) (standardGaussianVectorMeasure d) :=
    memLp_const (1 : ℝ)
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := standardGaussianVectorMeasure d) hpq
    (f := fun z : Fin d → ℝ => ‖WithLp.toLp 2 z‖) (g := fun _ => 1)
    (ae_of_all _ fun _ => norm_nonneg _)
    (ae_of_all _ fun _ => by norm_num)
    hf hg
  have hcs' :
      ∫ z, ‖WithLp.toLp 2 z‖ ∂standardGaussianVectorMeasure d ≤
        (∫ z, ‖WithLp.toLp 2 z‖ ^ (2 : ℝ)
            ∂standardGaussianVectorMeasure d) ^ ((1 : ℝ) / 2) *
          (∫ _z : Fin d → ℝ, (1 : ℝ) ^ (2 : ℝ)
            ∂standardGaussianVectorMeasure d) ^ ((1 : ℝ) / 2) := by
    simpa using hcs
  norm_num only [Real.rpow_two] at hcs'
  rw [ch15_standardGaussian_norm_sq_integral] at hcs'
  have huniv : (∫ _z : Fin d → ℝ, (1 : ℝ)
      ∂standardGaussianVectorMeasure d) = 1 := by simp
  rw [huniv] at hcs'
  simpa [Real.sqrt_eq_rpow] using hcs'

theorem ch15_standardGaussian_product_strip_bound
    (d : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    ((gaussianReal 0 1).prod (standardGaussianVectorMeasure d))
        {p : ℝ × (Fin d → ℝ) |
          |p.1| ≤ c * ‖WithLp.toLp 2 p.2‖} ≤
      ENNReal.ofReal (((399 : ℝ) / 500) * c * Real.sqrt d) := by
  let S : Set (ℝ × (Fin d → ℝ)) :=
    {p | |p.1| ≤ c * ‖WithLp.toLp 2 p.2‖}
  have hS : MeasurableSet S := by
    apply measurableSet_le
    · fun_prop
    · fun_prop
  change ((gaussianReal 0 1).prod (standardGaussianVectorMeasure d)) S ≤ _
  rw [Measure.prod_apply_symm hS]
  have hpoint : ∀ y : Fin d → ℝ,
      gaussianReal 0 1 ((fun x : ℝ => (x, y)) ⁻¹' S) ≤
        ENNReal.ofReal (((399 : ℝ) / 500) *
          (c * ‖WithLp.toLp 2 y‖)) := by
    intro y
    change gaussianReal 0 1 {x : ℝ | |x| ≤ c * ‖WithLp.toLp 2 y‖} ≤ _
    exact ch15_standardGaussian_abs_le _
      (mul_nonneg hc (norm_nonneg _))
  refine (lintegral_mono hpoint).trans ?_
  let C : ℝ := ((399 : ℝ) / 500) * c
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have heq : ∀ y : Fin d → ℝ,
      ENNReal.ofReal (((399 : ℝ) / 500) *
          (c * ‖WithLp.toLp 2 y‖)) =
        ENNReal.ofReal C * ENNReal.ofReal ‖WithLp.toLp 2 y‖ := by
    intro y
    rw [← ENNReal.ofReal_mul hC]
    congr 1
    simp [C]
    ring
  simp_rw [heq]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hvec : MemLp (fun z : Fin d → ℝ => WithLp.toLp 2 z) 2
      (standardGaussianVectorMeasure d) := by
    apply MemLp.of_eval_piLp
    intro i
    exact standardGaussianVectorCoordinate_memLp_two d i
  have hint : Integrable (fun z : Fin d → ℝ => ‖WithLp.toLp 2 z‖)
      (standardGaussianVectorMeasure d) :=
    hvec.norm.integrable (by norm_num)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun _ => norm_nonneg _)]
  rw [← ENNReal.ofReal_mul hC]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left
    (ch15_standardGaussian_norm_integral_le_sqrt d) hC

theorem ch15_piFinSuccAbove_norm_sq (d : ℕ)
    (z : Fin (d + 1) → ℝ) :
    ‖WithLp.toLp 2 z‖ ^ 2 =
      z ⟨0, by omega⟩ ^ 2 +
        ‖WithLp.toLp 2 (fun j : Fin d => z (Fin.succAbove ⟨0, by omega⟩ j))‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq]
  rw [Fin.sum_univ_succAbove
    (fun i : Fin (d + 1) => ‖z i‖ ^ 2) ⟨0, by omega⟩]
  simp [Real.norm_eq_abs, sq_abs]

theorem ch15_ratio_implies_strip
    (a b δ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (h : a / Real.sqrt (a ^ 2 + b ^ 2) ≤ δ) :
    a ≤ δ / Real.sqrt (1 - δ ^ 2) * b := by
  have hsarg : 0 < 1 - δ ^ 2 := by nlinarith
  have hs : 0 < Real.sqrt (1 - δ ^ 2) := Real.sqrt_pos.2 hsarg
  have hs2 : Real.sqrt (1 - δ ^ 2) ^ 2 = 1 - δ ^ 2 :=
    Real.sq_sqrt hsarg.le
  by_cases hab : a = 0 ∧ b = 0
  · rcases hab with ⟨rfl, rfl⟩
    simp
  · have htarg : 0 < a ^ 2 + b ^ 2 := by
      rcases not_and_or.mp hab with ha0 | hb0
      · nlinarith [sq_pos_of_ne_zero ha0, sq_nonneg b]
      · nlinarith [sq_nonneg a, sq_pos_of_ne_zero hb0]
    have ht : 0 < Real.sqrt (a ^ 2 + b ^ 2) := Real.sqrt_pos.2 htarg
    have ht2 : Real.sqrt (a ^ 2 + b ^ 2) ^ 2 = a ^ 2 + b ^ 2 :=
      Real.sq_sqrt htarg.le
    have hale : a ≤ δ * Real.sqrt (a ^ 2 + b ^ 2) := by
      exact (div_le_iff₀ ht).mp h
    have hsquare : a ^ 2 ≤ δ ^ 2 * (a ^ 2 + b ^ 2) := by
      nlinarith [sq_nonneg (δ * Real.sqrt (a ^ 2 + b ^ 2) - a)]
    have hprod_sq :
        (Real.sqrt (1 - δ ^ 2) * a) ^ 2 ≤ (δ * b) ^ 2 := by
      nlinarith
    have hprod : Real.sqrt (1 - δ ^ 2) * a ≤ δ * b := by
      exact (sq_le_sq₀ (mul_nonneg hs.le ha) (mul_nonneg hδ0 hb)).mp hprod_sq
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hs).2 (by simpa [mul_comm, mul_left_comm] using hprod)

noncomputable def ch15SphereFirstCoordinate (d : ℕ)
    (x : OrthogonalSphere (d + 1)) : ℝ :=
  WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1))) ⟨0, by omega⟩

theorem ch15_measurable_sphereFirstCoordinate (d : ℕ) :
    Measurable (ch15SphereFirstCoordinate d) := by
  exact ((PiLp.continuous_apply 2 (fun _ : Fin (d + 1) => ℝ)
    ⟨0, by omega⟩).comp continuous_subtype_val).measurable

theorem ch15_standardGaussianDirection_firstCoordinate_small
    (d : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    standardGaussianDirectionMeasure d
        {x | |ch15SphereFirstCoordinate d x| ≤ δ} ≤
      ENNReal.ofReal (((399 : ℝ) / 500) *
        (δ / Real.sqrt (1 - δ ^ 2)) * Real.sqrt d) := by
  let i : Fin (d + 1) := ⟨0, by omega⟩
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (d + 1) => ℝ) i
  let c : ℝ := δ / Real.sqrt (1 - δ ^ 2)
  let S : Set (ℝ × (Fin d → ℝ)) :=
    {p | |p.1| ≤ c * ‖WithLp.toLp 2 p.2‖}
  have hc : 0 ≤ c := div_nonneg hδ0 (Real.sqrt_nonneg _)
  have hS : MeasurableSet S := by
    apply measurableSet_le
    · fun_prop
    · fun_prop
  have hcoord : MeasurableSet
      {x : OrthogonalSphere (d + 1) |
        |ch15SphereFirstCoordinate d x| ≤ δ} := by
    exact measurableSet_le (ch15_measurable_sphereFirstCoordinate d).norm
      measurable_const
  rw [standardGaussianDirectionMeasure,
    Measure.map_apply (measurable_gaussianUnitDirection d) hcoord]
  let E : Set (Fin (d + 1) → ℝ) :=
    (gaussianUnitDirection d) ⁻¹'
      {x | |ch15SphereFirstCoordinate d x| ≤ δ}
  change standardGaussianVectorMeasure (d + 1) E ≤ _
  have hsubset : E ⊆ e ⁻¹' S ∪ ({0} : Set (Fin (d + 1) → ℝ)) := by
    intro z hz
    by_cases hz0 : z = 0
    · exact Or.inr (by simpa using hz0)
    · apply Or.inl
      have hz' : |z i| / ‖WithLp.toLp 2 z‖ ≤ δ := by
        simpa [E, ch15SphereFirstCoordinate, gaussianUnitDirection,
          gaussianUnitDirectionValue, hz0, i, div_eq_mul_inv, mul_comm,
          abs_mul] using hz
      let tail : Fin d → ℝ := fun j => z (Fin.succAbove i j)
      have hsq : ‖WithLp.toLp 2 z‖ ^ 2 =
          z i ^ 2 + ‖WithLp.toLp 2 tail‖ ^ 2 := by
        simpa [i, tail] using ch15_piFinSuccAbove_norm_sq d z
      have hroot : Real.sqrt (|z i| ^ 2 + ‖WithLp.toLp 2 tail‖ ^ 2) =
          ‖WithLp.toLp 2 z‖ := by
        rw [sq_abs, ← hsq]
        exact Real.sqrt_sq (norm_nonneg _)
      have hratio : |z i| /
          Real.sqrt (|z i| ^ 2 + ‖WithLp.toLp 2 tail‖ ^ 2) ≤ δ := by
        rw [hroot]
        exact hz'
      have hstrip := ch15_ratio_implies_strip
        |z i| ‖WithLp.toLp 2 tail‖ δ (abs_nonneg _)
        (norm_nonneg _) hδ0 hδ1 hratio
      change |z i| ≤ c * ‖WithLp.toLp 2 tail‖
      simpa [c] using hstrip
  calc
    standardGaussianVectorMeasure (d + 1) E ≤
        standardGaussianVectorMeasure (d + 1)
          (e ⁻¹' S ∪ ({0} : Set (Fin (d + 1) → ℝ))) :=
      measure_mono hsubset
    _ ≤ standardGaussianVectorMeasure (d + 1) (e ⁻¹' S) +
        standardGaussianVectorMeasure (d + 1)
          ({0} : Set (Fin (d + 1) → ℝ)) := measure_union_le _ _
    _ = ((gaussianReal 0 1).prod (standardGaussianVectorMeasure d)) S := by
      rw [standardGaussianVectorMeasure_singleton_zero d]
      simp only [add_zero]
      have hmp := measurePreserving_piFinSuccAbove
        (fun _ : Fin (d + 1) => gaussianReal 0 1) i
      have heq : MeasurePreserving e (standardGaussianVectorMeasure (d + 1))
          ((gaussianReal 0 1).prod (standardGaussianVectorMeasure d)) := by
        simpa [standardGaussianVectorMeasure, e, i] using hmp
      exact heq.measure_preimage hS.nullMeasurableSet
    _ ≤ ENNReal.ofReal (((399 : ℝ) / 500) * c * Real.sqrt d) :=
      ch15_standardGaussian_product_strip_bound d c hc
    _ = ENNReal.ofReal (((399 : ℝ) / 500) *
        (δ / Real.sqrt (1 - δ ^ 2)) * Real.sqrt d) := by rfl

theorem ch15_dixon_strip_coefficient_le
    (d : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hsmall : ((4 : ℝ) / 5) * Real.sqrt (d + 1) * Real.sqrt δ < 1) :
    ((399 : ℝ) / 500) * (δ / Real.sqrt (1 - δ ^ 2)) * Real.sqrt d ≤
      ((4 : ℝ) / 5) * Real.sqrt (d + 1) * Real.sqrt δ := by
  by_cases hd : d = 0
  · subst d
    simp [hδ0]
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hd)
  let N : ℝ := d + 1
  have hN2 : 2 ≤ N := by dsimp [N]; norm_num; linarith
  have hN0 : 0 ≤ N := hN2.trans' (by norm_num)
  have hδsq : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ0
  have hNsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0
  have hdeltaN : 16 * δ * N < 25 := by
    have hsmallN : ((4 : ℝ) / 5) * Real.sqrt N * Real.sqrt δ < 1 := by
      simpa [N] using hsmall
    have hX0 : 0 ≤ ((4 : ℝ) / 5) * Real.sqrt N * Real.sqrt δ := by positivity
    have hsquare :
        (((4 : ℝ) / 5) * Real.sqrt N * Real.sqrt δ) ^ 2 < 1 := by
      simpa using (sq_lt_sq₀ hX0 (by norm_num)).2 hsmallN
    nlinarith
  have hpoly : 4 * (d : ℝ) ≤ N ^ 2 := by
    dsimp [N]
    nlinarith [sq_nonneg ((d : ℝ) - 1)]
  have hdelta_d : δ * (d : ℝ) ≤ (25 / 64 : ℝ) * N := by
    have hmul1 := mul_le_mul_of_nonneg_left hpoly hδ0
    have hmul2 := mul_le_mul_of_nonneg_right (le_of_lt hdeltaN) hN0
    nlinarith
  have hdelta_sq : δ ^ 2 ≤ (625 / 1024 : ℝ) := by
    have hN4 : 4 ≤ N ^ 2 := by nlinarith [sq_nonneg (N - 2)]
    have hδN0 : 0 ≤ 16 * δ * N := by positivity
    have hsquare : (16 * δ * N) ^ 2 ≤ 25 ^ 2 :=
      (sq_le_sq₀ hδN0 (by norm_num)).2 (le_of_lt hdeltaN)
    have hmul := mul_le_mul_of_nonneg_left hN4 (sq_nonneg δ)
    nlinarith
  have hden : (399 / 1024 : ℝ) ≤ 1 - δ ^ 2 := by
    linarith
  have hcore :
      ((399 : ℝ) / 500) ^ 2 * δ * (d : ℝ) ≤
        ((4 : ℝ) / 5) ^ 2 * N * (1 - δ ^ 2) := by
    have hleft := mul_le_mul_of_nonneg_left hdelta_d
      (sq_nonneg ((399 : ℝ) / 500))
    have hright := mul_le_mul_of_nonneg_left hden
      (mul_nonneg (sq_nonneg ((4 : ℝ) / 5)) hN0)
    norm_num at hleft hright ⊢
    nlinarith
  have hsarg : 0 < 1 - δ ^ 2 := by nlinarith
  have hs : 0 < Real.sqrt (1 - δ ^ 2) := Real.sqrt_pos.2 hsarg
  have hs2 : Real.sqrt (1 - δ ^ 2) ^ 2 = 1 - δ ^ 2 :=
    Real.sq_sqrt hsarg.le
  have hdsq : Real.sqrt (d : ℝ) ^ 2 = d :=
    Real.sq_sqrt (Nat.cast_nonneg d)
  have hLsq :
      (((399 : ℝ) / 500) * (δ / Real.sqrt (1 - δ ^ 2)) *
          Real.sqrt d) ^ 2 =
        ((399 : ℝ) / 500) ^ 2 * δ ^ 2 * d / (1 - δ ^ 2) := by
    simp only [mul_pow, div_pow, hs2, hdsq]
    ring
  have hRsq :
      (((4 : ℝ) / 5) * Real.sqrt (d + 1) * Real.sqrt δ) ^ 2 =
        ((4 : ℝ) / 5) ^ 2 * N * δ := by
    change (((4 : ℝ) / 5) * Real.sqrt N * Real.sqrt δ) ^ 2 = _
    simp only [mul_pow, hNsq, hδsq]
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [hLsq, hRsq]
  rw [div_le_iff₀ hsarg]
  have hcored := mul_le_mul_of_nonneg_left hcore hδ0
  convert hcored using 1 <;> ring

theorem ch15_standardGaussianDirection_firstCoordinate_dixon_bound
    (d : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    standardGaussianDirectionMeasure d
        {x | |ch15SphereFirstCoordinate d x| ≤ δ} ≤
      ENNReal.ofReal (((4 : ℝ) / 5) *
        Real.sqrt (d + 1) * Real.sqrt δ) := by
  by_cases hsmall : ((4 : ℝ) / 5) *
      Real.sqrt (d + 1) * Real.sqrt δ < 1
  · exact (ch15_standardGaussianDirection_firstCoordinate_small
      d δ hδ0 hδ1).trans
        (ENNReal.ofReal_le_ofReal
          (ch15_dixon_strip_coefficient_le d δ hδ0 hδ1 hsmall))
  · calc
      standardGaussianDirectionMeasure d
          {x | |ch15SphereFirstCoordinate d x| ≤ δ} ≤
          standardGaussianDirectionMeasure d Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ ≤ ENNReal.ofReal (((4 : ℝ) / 5) *
          Real.sqrt (d + 1) * Real.sqrt δ) := by
        simpa only [← ENNReal.ofReal_one] using
          ENNReal.ofReal_le_ofReal (le_of_not_gt hsmall)

noncomputable def ch15SphereInner (d : ℕ)
    (u x : OrthogonalSphere (d + 1)) : ℝ :=
  @inner ℝ _ _ (u : EuclideanSpace ℝ (Fin (d + 1))) x

theorem ch15SphereInner_base (d : ℕ) (x : OrthogonalSphere (d + 1)) :
    ch15SphereInner d (orthogonalSphereBase d) x =
      ch15SphereFirstCoordinate d x := by
  have hscalar (a b : ℝ) : @inner ℝ ℝ _ a b = a * b := by
    calc
      @inner ℝ ℝ _ a b = @inner ℝ ℝ _ (a • (1 : ℝ)) (b • (1 : ℝ)) := by
        congr <;> simp
      _ = a * b * @inner ℝ ℝ _ (1 : ℝ) 1 := by
        rw [real_inner_smul_left, real_inner_smul_right]
        ring
      _ = a * b := by simp [real_inner_self_eq_norm_mul_norm]
  simp only [ch15SphereInner, ch15SphereFirstCoordinate,
    orthogonalSphereBase, PiLp.inner_apply]
  simp_rw [hscalar]
  classical
  rw [Finset.sum_eq_single ⟨0, by omega⟩]
  · simp [Pi.single_apply]
  · intro j _ hj
    have hj0 : j ≠ (0 : Fin (d + 1)) := by simpa using hj
    simp [Pi.single_apply, hj0]
  · simp

theorem ch15SphereInner_smul (d : ℕ)
    (Q : RealOrthogonalGroup (d + 1))
    (u x : OrthogonalSphere (d + 1)) :
    ch15SphereInner d (Q • u) (Q • x) = ch15SphereInner d u x := by
  change @inner ℝ _ _
      ((orthogonalGroupEuclideanLinearIsometryEquiv (d + 1) Q)
        (u : EuclideanSpace ℝ (Fin (d + 1))))
      ((orthogonalGroupEuclideanLinearIsometryEquiv (d + 1) Q)
        (x : EuclideanSpace ℝ (Fin (d + 1)))) =
    @inner ℝ _ _ (u : EuclideanSpace ℝ (Fin (d + 1))) x
  exact (orthogonalGroupEuclideanLinearIsometryEquiv (d + 1) Q).inner_map_map _ _

theorem ch15_standardGaussianDirection_inner_dixon_bound
    (d : ℕ) (u : OrthogonalSphere (d + 1))
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    standardGaussianDirectionMeasure d
        {x | |ch15SphereInner d u x| ≤ δ} ≤
      ENNReal.ofReal (((4 : ℝ) / 5) *
        Real.sqrt (d + 1) * Real.sqrt δ) := by
  obtain ⟨Q, hQ⟩ := orthogonalGroup_action_pretransitive
    (d + 1) (orthogonalSphereBase d) u
  let T : OrthogonalSphere (d + 1) → OrthogonalSphere (d + 1) :=
    fun x => Q • x
  have hT : Measurable T := (continuous_const.smul continuous_id).measurable
  have hE : MeasurableSet {x : OrthogonalSphere (d + 1) |
      |ch15SphereInner d u x| ≤ δ} := by
    have hinner : Measurable (fun x : OrthogonalSphere (d + 1) =>
        ch15SphereInner d u x) := by
      unfold ch15SphereInner
      fun_prop
    apply measurableSet_le
    · exact hinner.norm
    · exact measurable_const
  have hpre : T ⁻¹' {x : OrthogonalSphere (d + 1) |
      |ch15SphereInner d u x| ≤ δ} =
      {x | |ch15SphereFirstCoordinate d x| ≤ δ} := by
    ext x
    change |ch15SphereInner d u (Q • x)| ≤ δ ↔
      |ch15SphereFirstCoordinate d x| ≤ δ
    rw [hQ, ch15SphereInner_smul,
      ch15SphereInner_base]
  calc
    standardGaussianDirectionMeasure d
        {x | |ch15SphereInner d u x| ≤ δ} =
        Measure.map T (standardGaussianDirectionMeasure d)
          {x | |ch15SphereInner d u x| ≤ δ} := by
      rw [standardGaussianDirectionMeasure_invariant d Q]
    _ = standardGaussianDirectionMeasure d
        (T ⁻¹' {x | |ch15SphereInner d u x| ≤ δ}) := by
      rw [Measure.map_apply hT hE]
    _ = standardGaussianDirectionMeasure d
        {x | |ch15SphereFirstCoordinate d x| ≤ δ} := by rw [hpre]
    _ ≤ ENNReal.ofReal (((4 : ℝ) / 5) *
        Real.sqrt (d + 1) * Real.sqrt δ) :=
      ch15_standardGaussianDirection_firstCoordinate_dixon_bound
        d δ hδ0 hδ1

end NumStability
