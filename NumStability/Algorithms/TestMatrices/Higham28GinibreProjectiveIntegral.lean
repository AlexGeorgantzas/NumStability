/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Probability.Distributions.Beta

/-! # Higham Chapter 28: the affine projective-chart integral

The affine real-eigenvector chart contributes the radial weight

`(1 + ∑ i, y i ^ 2) ^ (-(n + 1) / 2)`.

This file evaluates its integral over `ℝⁿ` without assumptions.  The proof
uses the radial integration formula for additive Haar measure, the
substitution `t = r²`, and the Möbius substitution `u = t / (1 + t)` that
turns the remaining integral into a beta integral.
-/

namespace NumStability

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

noncomputable section

private lemma integral_betaKernel {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x : ℝ in Ioo 0 1, x ^ (a - 1) * (1 - x) ^ (b - 1)) =
      ProbabilityTheory.beta a b := by
  rw [ProbabilityTheory.beta_eq_betaIntegralReal a b ha hb,
    Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num),
    ← integral_Ioc_eq_integral_Ioo]
  have hint : Integrable
      (fun x : ℝ => (x : ℂ) ^ ((a : ℂ) - 1) *
        (1 - (x : ℂ)) ^ ((b : ℂ) - 1))
      (volume.restrict (Ioc 0 1)) := by
    convert Complex.betaIntegral_convergent
      (u := (a : ℂ)) (v := (b : ℂ)) (by simpa) (by simpa)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by simp), IntegrableOn]
  calc
    (∫ x : ℝ in Ioc 0 1, x ^ (a - 1) * (1 - x) ^ (b - 1)) =
        ∫ x : ℝ in Ioc 0 1,
          RCLike.re ((x : ℂ) ^ ((a : ℂ) - 1) *
            (1 - (x : ℂ)) ^ ((b : ℂ) - 1)) := by
      refine setIntegral_congr_fun measurableSet_Ioc fun x ⟨hx1, hx2⟩ => ?_
      norm_cast
      rw [← Complex.ofReal_cpow, ← Complex.ofReal_cpow,
        RCLike.re_to_complex, Complex.re_mul_ofReal, Complex.ofReal_re]
      all_goals linarith
    _ = RCLike.re (∫ x : ℝ in Ioc 0 1,
          (x : ℂ) ^ ((a : ℂ) - 1) *
            (1 - (x : ℂ)) ^ ((b : ℂ) - 1)) := integral_re hint

private lemma mobius_image_Ioo :
    (fun u : ℝ => u / (1 - u)) '' Ioo 0 1 = Ioi 0 := by
  ext t
  constructor
  · rintro ⟨u, ⟨hu0, hu1⟩, rfl⟩
    exact div_pos hu0 (sub_pos.mpr hu1)
  · intro ht
    have ht0 : 0 < t := ht
    refine ⟨t / (1 + t), ?_, ?_⟩
    · constructor
      · exact div_pos ht0 (by positivity)
      · exact (div_lt_one (by positivity)).2 (by linarith)
    · have hne : 1 + t ≠ 0 := by positivity
      field_simp [hne]
      ring_nf

private lemma mobius_hasDerivWithin (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivWithinAt (fun x : ℝ => x / (1 - x))
      (1 / (1 - u) ^ 2) (Ioo 0 1) u := by
  have hne : 1 - u ≠ 0 := by linarith [hu.2]
  have h := (hasDerivAt_id u).div
    ((hasDerivAt_const u 1).sub (hasDerivAt_id u)) hne
  convert h.hasDerivWithinAt using 1
  all_goals simp only [Function.id_def, Pi.sub_apply]
  all_goals field_simp [hne]
  all_goals ring

private lemma mobius_injOn :
    Set.InjOn (fun u : ℝ => u / (1 - u)) (Ioo 0 1) := by
  intro u hu v hv huv
  have hu' : 1 - u ≠ 0 := by linarith [hu.2]
  have hv' : 1 - v ≠ 0 := by linarith [hv.2]
  field_simp [hu', hv'] at huv
  linarith

private lemma mobius_betaKernel (a b : ℝ) (u : ℝ)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    |1 / (1 - u) ^ 2| *
        ((u / (1 - u)) ^ (a - 1) *
          (1 + u / (1 - u)) ^ (-(a + b))) =
      u ^ (a - 1) * (1 - u) ^ (b - 1) := by
  have hu0 : 0 < u := hu.1
  have hv : 0 < 1 - u := sub_pos.mpr hu.2
  have hv0 : 1 - u ≠ 0 := hv.ne'
  have hone : 1 + u / (1 - u) = 1 / (1 - u) := by
    field_simp
    ring
  have hinvneg : (1 / (1 - u)) ^ (-(a + b)) =
      (1 - u) ^ (a + b) := by
    rw [one_div, Real.inv_rpow hv.le, Real.rpow_neg hv.le]
    simp
  have hderiv : |1 / (1 - u) ^ 2| = (1 - u) ^ (-2 : ℝ) := by
    rw [abs_of_pos (div_pos zero_lt_one (sq_pos_of_pos hv)),
      Real.rpow_neg hv.le]
    norm_num [Real.rpow_two]
  rw [hderiv, Real.div_rpow hu0.le hv.le, hone, hinvneg]
  rw [div_eq_mul_inv, ← Real.rpow_neg hv.le]
  calc
    (1 - u) ^ (-2 : ℝ) *
          (u ^ (a - 1) * (1 - u) ^ (-(a - 1)) * (1 - u) ^ (a + b)) =
        u ^ (a - 1) *
          ((1 - u) ^ (-2 : ℝ) * (1 - u) ^ (-(a - 1)) *
            (1 - u) ^ (a + b)) := by ring
    _ = u ^ (a - 1) *
          (1 - u) ^ ((-2 : ℝ) + (-(a - 1)) + (a + b)) := by
      rw [← Real.rpow_add hv, ← Real.rpow_add hv]
    _ = u ^ (a - 1) * (1 - u) ^ (b - 1) := by
      congr 1
      ring_nf

private lemma integral_Ioi_betaKernel {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t : ℝ in Ioi 0, t ^ (a - 1) * (1 + t) ^ (-(a + b))) =
      ProbabilityTheory.beta a b := by
  rw [← mobius_image_Ioo]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    mobius_hasDerivWithin mobius_injOn]
  simp only [smul_eq_mul]
  rw [setIntegral_congr_fun measurableSet_Ioo
    (fun u hu => mobius_betaKernel a b u hu)]
  exact integral_betaKernel ha hb

/-- The radial integral arising from the affine projective chart. -/
theorem integral_ginibreProjectiveRadial (n : ℕ) (hn : 0 < n) :
    (∫ r : ℝ in Ioi 0,
        r ^ (n - 1) * (1 + r ^ 2) ^ (-(((n : ℝ) + 1) / 2))) =
      ProbabilityTheory.beta ((n : ℝ) / 2) (1 / 2) / 2 := by
  let a : ℝ := (n : ℝ) / 2
  let b : ℝ := 1 / 2
  let g : ℝ → ℝ := fun t =>
    (1 / 2) * (t ^ (a - 1) * (1 + t) ^ (-(a + b)))
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by norm_num [b]
  have hab : a + b = ((n : ℝ) + 1) / 2 := by simp [a, b]; ring
  have hnsub : (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  calc
    (∫ r : ℝ in Ioi 0,
        r ^ (n - 1) * (1 + r ^ 2) ^ (-(((n : ℝ) + 1) / 2))) =
      ∫ r : ℝ in Ioi 0,
        (2 * r ^ ((2 : ℝ) - 1)) • g (r ^ (2 : ℝ)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
      have hr0 : 0 < r := hr
      simp only [smul_eq_mul, g]
      rw [show r ^ (n - 1) = r ^ ((n : ℝ) - 1) by
        rw [hnsub.symm, Real.rpow_natCast]]
      rw [show r ^ 2 = r ^ (2 : ℝ) by norm_num [Real.rpow_two]]
      rw [← Real.rpow_mul hr0.le]
      rw [hab]
      have hexp : (1 : ℝ) + 2 * (a - 1) = (n : ℝ) - 1 := by
        simp [a]
        ring
      calc
        r ^ ((n : ℝ) - 1) *
              (1 + r ^ (2 : ℝ)) ^ (-(((n : ℝ) + 1) / 2)) =
            (r ^ (1 : ℝ) * r ^ (2 * (a - 1))) *
              (1 + r ^ (2 : ℝ)) ^ (-(((n : ℝ) + 1) / 2)) := by
          rw [← Real.rpow_add hr0, hexp]
        _ = 2 * r ^ ((2 : ℝ) - 1) *
              (1 / 2 * (r ^ (2 * (a - 1)) *
                (1 + r ^ (2 : ℝ)) ^ (-(((n : ℝ) + 1) / 2)))) := by
          rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
          ring
    _ = ∫ t : ℝ in Ioi 0, g t := by
      exact integral_comp_rpow_Ioi_of_pos (g := g) (p := 2)
        (by norm_num : (0 : ℝ) < 2)
    _ = (1 / 2) *
        ∫ t : ℝ in Ioi 0, t ^ (a - 1) * (1 + t) ^ (-(a + b)) := by
      rw [integral_const_mul]
    _ = ProbabilityTheory.beta a b / 2 := by
      rw [integral_Ioi_betaKernel ha hb]
      ring
    _ = ProbabilityTheory.beta ((n : ℝ) / 2) (1 / 2) / 2 := rfl

private lemma integral_ginibreProjectiveWeight_raw (n : ℕ) (hn : 0 < n) :
    (∫ y : EuclideanSpace ℝ (Fin n),
        (1 + ‖y‖ ^ 2) ^ (-(((n : ℝ) + 1) / 2))) =
      (n : ℝ) * (volume : Measure (EuclideanSpace ℝ (Fin n))).real
          (Metric.ball 0 1) *
        (ProbabilityTheory.beta ((n : ℝ) / 2) (1 / 2) / 2) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let f : ℝ → ℝ := fun r =>
    (1 + r ^ 2) ^ (-(((n : ℝ) + 1) / 2))
  have h := MeasureTheory.integral_fun_norm_addHaar
    (volume : Measure (EuclideanSpace ℝ (Fin n))) f
  rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n by simp] at h
  simpa [f, nsmul_eq_mul, integral_ginibreProjectiveRadial n hn, mul_assoc] using h

private lemma euclideanVolume_unitBall_real (n : ℕ) (hn : 0 < n) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) =
      Real.sqrt Real.pi ^ n /
        Real.Gamma ((n : ℝ) / 2 + 1) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rw [Measure.real, EuclideanSpace.volume_ball]
  simp only [ENNReal.ofReal_one, one_pow, one_mul, Fintype.card_fin]
  apply ENNReal.toReal_ofReal
  exact div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)
    (Real.Gamma_pos_of_pos (by positivity)).le

private lemma sqrtPi_pow_succ (n : ℕ) :
    Real.sqrt Real.pi ^ n * Real.sqrt Real.pi =
      Real.pi ^ (((n : ℝ) + 1) / 2) := by
  calc
    Real.sqrt Real.pi ^ n * Real.sqrt Real.pi =
        Real.sqrt Real.pi ^ (n + 1) := (pow_succ _ n).symm
    _ = (Real.pi ^ (1 / 2 : ℝ)) ^ (n + 1) := by
      rw [Real.sqrt_eq_rpow]
    _ = (Real.pi ^ (1 / 2 : ℝ)) ^ (((n + 1 : ℕ) : ℝ)) := by
      rw [Real.rpow_natCast]
    _ = Real.pi ^ ((1 / 2 : ℝ) * (((n + 1 : ℕ) : ℝ))) := by
      rw [Real.rpow_mul Real.pi_nonneg]
    _ = Real.pi ^ (((n : ℝ) + 1) / 2) := by
      congr 1
      push_cast
      ring

private lemma ginibreProjectiveConstant (n : ℕ) (hn : 0 < n) :
    (n : ℝ) *
          (Real.sqrt Real.pi ^ n /
            Real.Gamma ((n : ℝ) / 2 + 1)) *
        (ProbabilityTheory.beta ((n : ℝ) / 2) (1 / 2) / 2) =
      Real.pi ^ (((n : ℝ) + 1) / 2) /
        Real.Gamma (((n : ℝ) + 1) / 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : (n : ℝ) / 2 ≠ 0 := by positivity
  have hGx : Real.Gamma ((n : ℝ) / 2) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have hGhalf : Real.Gamma (1 / 2) = Real.sqrt Real.pi := by
    norm_num [Real.Gamma_one_half_eq]
  have hGsum : Real.Gamma ((n : ℝ) / 2 + 1 / 2) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have hGsucc : Real.Gamma ((n : ℝ) / 2 + 1) =
      ((n : ℝ) / 2) * Real.Gamma ((n : ℝ) / 2) := by
    exact Real.Gamma_add_one hx
  rw [ProbabilityTheory.beta, hGhalf, hGsucc]
  have harg : (n : ℝ) / 2 + 1 / 2 = ((n : ℝ) + 1) / 2 := by ring
  rw [harg] at hGsum ⊢
  rw [← sqrtPi_pow_succ n]
  field_simp [hx, hGx, hGsum]

/-- The affine projective weight integrated on Euclidean `ℝⁿ`. -/
theorem integral_ginibreProjectiveWeight_euclidean (n : ℕ) :
    (∫ y : EuclideanSpace ℝ (Fin n),
        (1 + ‖y‖ ^ 2) ^ (-(((n : ℝ) + 1) / 2))) =
      Real.pi ^ (((n : ℝ) + 1) / 2) /
        Real.Gamma (((n : ℝ) + 1) / 2) := by
  by_cases hn : n = 0
  · subst n
    rw [volume_euclideanSpace_eq_dirac]
    simp only [integral_dirac, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
      add_zero, Real.one_rpow]
    rw [show (((0 : ℕ) : ℝ) + 1) / 2 = 1 / 2 by norm_num,
      Real.Gamma_one_half_eq, Real.sqrt_eq_rpow]
    exact (div_self (ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos _))).symm
  · have hnpos := Nat.pos_of_ne_zero hn
    rw [integral_ginibreProjectiveWeight_raw n hnpos,
      euclideanVolume_unitBall_real n hnpos,
      ginibreProjectiveConstant n hnpos]

/-- The affine projective-chart integral in the raw coordinate type used by
the Ginibre incidence chart. -/
theorem integral_ginibreProjectiveWeight (n : ℕ) :
    (∫ y : Fin n → ℝ,
        (1 + ∑ i, y i ^ 2) ^ (-(((n : ℝ) + 1) / 2))) =
      Real.pi ^ (((n : ℝ) + 1) / 2) /
        Real.Gamma (((n : ℝ) + 1) / 2) := by
  let F : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
    (1 + ‖y‖ ^ 2) ^ (-(((n : ℝ) + 1) / 2))
  have h := (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding F
  rw [integral_ginibreProjectiveWeight_euclidean n] at h
  calc
    (∫ y : Fin n → ℝ,
        (1 + ∑ i, y i ^ 2) ^ (-(((n : ℝ) + 1) / 2))) =
        ∫ y : Fin n → ℝ, F (WithLp.toLp 2 y) := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [F, EuclideanSpace.norm_eq]
      rw [Real.sq_sqrt]
      · congr 2
        apply Finset.sum_congr rfl
        intro i hi
        simp [Real.norm_eq_abs, sq_abs]
      · exact Finset.sum_nonneg fun i hi => sq_nonneg ‖y i‖
    _ = _ := h

end
end NumStability
