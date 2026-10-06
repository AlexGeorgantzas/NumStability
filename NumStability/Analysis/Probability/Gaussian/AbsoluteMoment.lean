/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic

/-!
# Gaussian absolute moments

Scalar first absolute moments for real Gaussian measures, including the exact
moment of the difference of two independent standard Gaussians.
-/

namespace NumStability

open MeasureTheory ProbabilityTheory Set Real

/-- The unnormalized first absolute Gaussian moment. -/
theorem integral_abs_mul_exp_neg_mul_sq (b : ℝ) (hb : 0 < b) :
    (∫ x : ℝ, |x| * Real.exp (-b * x ^ 2)) = 1 / b := by
  let f : ℝ → ℝ := fun x => x * Real.exp (-b * x ^ 2)
  have hcomp : (fun x : ℝ => |x| * Real.exp (-b * x ^ 2)) =
      fun x => f |x| := by
    funext x
    simp only [f]
    rw [sq_abs]
  rw [hcomp, integral_comp_abs]
  have hgamma := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (1 : ℝ)) (b := b) (by norm_num) (by norm_num) hb
  have hIoi : (∫ x : ℝ in Ioi 0, f x) = b⁻¹ / 2 := by
    rw [show (∫ x : ℝ in Ioi 0, f x) =
        ∫ x : ℝ in Ioi 0, x ^ (1 : ℝ) * Real.exp (-b * x ^ (2 : ℝ)) by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp [f, Real.rpow_one]]
    rw [hgamma]
    have hG : Real.Gamma (((1 : ℝ) + 1) / 2) = 1 := by
      norm_num
      exact Real.Gamma_one
    rw [hG]
    norm_num [Real.rpow_neg_one]
    ring
  rw [hIoi]
  field_simp

/-- The first absolute moment of the standard real Gaussian, in the
normalization used by `gaussianPDFReal`. -/
theorem integral_abs_mul_standardGaussianPDF :
    (∫ x : ℝ, |x| * gaussianPDFReal 0 1 x) =
      2 / Real.sqrt (2 * Real.pi) := by
  have hpoint : (fun x : ℝ => |x| * gaussianPDFReal 0 1 x) =
      fun x => (1 / Real.sqrt (2 * Real.pi)) *
        (|x| * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
    funext x
    simp [gaussianPDFReal]
    ring_nf
  rw [hpoint, integral_const_mul,
    integral_abs_mul_exp_neg_mul_sq (1 / 2) (by norm_num)]
  ring

theorem two_div_sqrt_two_mul_pi :
    2 / Real.sqrt (2 * Real.pi) = Real.sqrt (2 / Real.pi) := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrtTwo : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hsqrtPi : Real.sqrt Real.pi ≠ 0 := by positivity
  have hsqrtTwoSq : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  field_simp
  nlinarith

/-- Familiar `sqrt (2 / π)` form of the standard Gaussian first absolute
moment. -/
theorem integral_abs_mul_standardGaussianPDF_eq_sqrt :
    (∫ x : ℝ, |x| * gaussianPDFReal 0 1 x) =
      Real.sqrt (2 / Real.pi) := by
  rw [integral_abs_mul_standardGaussianPDF, two_div_sqrt_two_mul_pi]

/-- First absolute moment of a centered Gaussian of variance two. -/
theorem integral_abs_mul_gaussianPDFReal_zero_two :
    (∫ x : ℝ, |x| * gaussianPDFReal 0 2 x) =
      4 / Real.sqrt (2 * Real.pi * 2) := by
  have hpoint : (fun x : ℝ => |x| * gaussianPDFReal 0 2 x) =
      fun x => (1 / Real.sqrt (2 * Real.pi * 2)) *
        (|x| * Real.exp (-(1 / 4 : ℝ) * x ^ 2)) := by
    funext x
    simp [gaussianPDFReal]
    ring_nf
  rw [hpoint, integral_const_mul,
    integral_abs_mul_exp_neg_mul_sq (1 / 4) (by norm_num)]
  ring

theorem integral_abs_mul_gaussianPDFReal_zero_two_eq :
    (∫ x : ℝ, |x| * gaussianPDFReal 0 2 x) =
      2 / Real.sqrt Real.pi := by
  rw [integral_abs_mul_gaussianPDFReal_zero_two]
  rw [show (2 : ℝ) * Real.pi * 2 = 4 * Real.pi by ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  have hsqrtFour : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  rw [hsqrtFour]
  ring

/-- The difference of two independent standard real Gaussians is centered
Gaussian with variance two. -/
theorem gaussianReal_prod_map_sub :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        (fun p : ℝ × ℝ => p.1 - p.2) = gaussianReal 0 2 := by
  let μ : Measure ℝ := gaussianReal 0 1
  have hInd : IndepFun (fun p : ℝ × ℝ => p.1) (fun p : ℝ × ℝ => p.2)
      (μ.prod μ) := indepFun_prod measurable_id measurable_id
  have hfst : (μ.prod μ).map (fun p : ℝ × ℝ => p.1) = gaussianReal 0 1 := by
    simp [μ]
  have hsndNeg :
      (μ.prod μ).map (fun p : ℝ × ℝ => -p.2) = gaussianReal 0 1 := by
    rw [show (fun p : ℝ × ℝ => -p.2) =
      (fun x : ℝ => -x) ∘ Prod.snd by rfl]
    rw [← Measure.map_map measurable_neg measurable_snd]
    simp [μ, gaussianReal_map_neg]
  have hadd := gaussianReal_add_gaussianReal_of_indepFun
    hInd.neg_right hfst hsndNeg
  change (μ.prod μ).map ((fun p : ℝ × ℝ => p.1) +
    -(fun p : ℝ × ℝ => p.2)) = gaussianReal 0 2
  convert hadd using 1
  all_goals norm_num

/-- Exact absolute first moment of the difference of two independent
standard real Gaussians. -/
theorem integral_abs_standardGaussian_difference :
    (∫ p : ℝ × ℝ, |p.1 - p.2|
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) =
      2 / Real.sqrt Real.pi := by
  let μ : Measure (ℝ × ℝ) :=
    (gaussianReal 0 1).prod (gaussianReal 0 1)
  let sub : ℝ × ℝ → ℝ := fun p => p.1 - p.2
  have hsub : AEMeasurable sub μ :=
    (measurable_fst.sub measurable_snd).aemeasurable
  calc
    (∫ p : ℝ × ℝ, |p.1 - p.2| ∂μ) =
        ∫ x : ℝ, |x| ∂μ.map sub := by
      rw [integral_map hsub measurable_abs.aestronglyMeasurable]
    _ = ∫ x : ℝ, |x| ∂gaussianReal 0 2 := by
      rw [show μ.map sub = gaussianReal 0 2 by
        simpa [μ, sub] using gaussianReal_prod_map_sub]
    _ = ∫ x : ℝ, gaussianPDFReal 0 2 x • |x| := by
      rw [integral_gaussianReal_eq_integral_smul
        (v := (2 : NNReal)) (by norm_num)]
    _ = 2 / Real.sqrt Real.pi := by
      simpa [smul_eq_mul, mul_comm] using
        integral_abs_mul_gaussianPDFReal_zero_two_eq

end NumStability
