/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GinibreCharacteristicProduct
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.MeasureTheory.Integral.Gamma

/-! # Higham Chapter 28: scalar identities for the signed Ginibre recurrence

This file records the finite characteristic-product kernel and the scalar
Gaussian boundary identity used after applying the signed eigenline incidence
formula twice.  Keeping these facts independent of the incidence geometry makes
the final dimension recurrence a short algebraic consequence.
-/

namespace NumStability

open MeasureTheory ProbabilityTheory Set Real Filter
open scoped BigOperators

noncomputable section

/-- The two-point real-Ginibre characteristic-product kernel. -/
def ginibreCharacteristicProductKernel (m : ℕ) (t : ℝ) : ℝ :=
  (m.factorial : ℝ) *
    ∑ k ∈ Finset.range (m + 1), t ^ k / (k.factorial : ℝ)

/-- The characteristic-product integral is the scalar kernel evaluated at
the product of its two spectral parameters. -/
theorem integral_realGinibre_characteristicProduct_eq_kernel
    (m : ℕ) (u x : ℝ) :
    (∫ A : RSqMat m,
        (u • (1 : RSqMat m) - A).det *
          (x • (1 : RSqMat m) - A).det
      ∂realGinibreMeasure m) =
      ginibreCharacteristicProductKernel m (u * x) := by
  exact integral_realGinibre_characteristicProduct m u x

/-- The finite kernel satisfies the exact two-step recurrence that remains
after removing the common lower-dimensional characteristic-product term. -/
theorem ginibreCharacteristicProductKernel_add_two
    (m : ℕ) (t : ℝ) :
    ginibreCharacteristicProductKernel (m + 2) t =
      ((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) *
          ginibreCharacteristicProductKernel m t +
        ((m + 2 : ℕ) : ℝ) * t ^ (m + 1) + t ^ (m + 2) := by
  unfold ginibreCharacteristicProductKernel
  rw [show m + 2 + 1 = (m + 1) + 2 by omega]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_ofNat]
  have hm1 : ((m + 1).factorial : ℝ) ≠ 0 := by positivity
  have hm2 : ((m + 2).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- Subtraction-index form of the same kernel recurrence, valid also in the
two base dimensions because the prefactor then vanishes. -/
theorem ginibreCharacteristicProductKernel_eq_sub_two_add_tail
    (m : ℕ) (t : ℝ) :
    ginibreCharacteristicProductKernel m t =
      (m : ℝ) * ((m - 1 : ℕ) : ℝ) *
          ginibreCharacteristicProductKernel (m - 2) t +
        (m : ℝ) * t ^ (m - 1) + t ^ m := by
  rcases m with (_ | _ | m)
  · simp [ginibreCharacteristicProductKernel]
  · norm_num [ginibreCharacteristicProductKernel, Finset.sum_range_succ]
  · convert ginibreCharacteristicProductKernel_add_two m t using 1 <;>
      push_cast <;> try omega <;> ring

/-! ## The one-dimensional Gaussian boundary identity -/

/-- Every polynomial moment is integrable against the unnormalized standard
Gaussian density. -/
theorem integrable_pow_mul_exp_neg_sq_div_two (r : ℕ) :
    Integrable (fun t : ℝ => t ^ r * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq
    (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (-1 : ℝ) < (r : ℝ) by
      have hr : (0 : ℝ) ≤ (r : ℝ) := by positivity
      linarith)
  simpa only [Real.rpow_natCast] using h

/-- Multiplying the Gaussian by a power of an affine quadratic still gives
an integrable function. -/
theorem integrable_pow_mul_exp_mul_sub_sq_pow
    (a : ℝ) (m r : ℕ) :
    Integrable (fun t : ℝ =>
      t ^ r * Real.exp (-(1 / 2 : ℝ) * t ^ 2) *
        (a - t ^ 2 / 2) ^ m) := by
  induction m generalizing r with
  | zero =>
      simpa using integrable_pow_mul_exp_neg_sq_div_two r
  | succ m ih =>
      have h0 := (ih r).const_mul a
      have h2 := (ih (r + 2)).const_mul (-(1 / 2 : ℝ))
      apply (h0.add h2).congr
      filter_upwards with t
      simp only [Pi.add_apply, pow_succ]
      ring

/-- The derivative appearing in the signed two-incidence calculation is
integrable on the positive half-line. -/
theorem integrableOn_ginibre_signed_boundary_derivative
    (a : ℝ) (m : ℕ) :
    IntegrableOn (fun t : ℝ =>
      t * Real.exp (-(1 / 2 : ℝ) * t ^ 2) *
        ((m : ℝ) * (a - t ^ 2 / 2) ^ (m - 1) +
          (a - t ^ 2 / 2) ^ m)) (Ioi 0) := by
  have hm := integrable_pow_mul_exp_mul_sub_sq_pow a m 1
  have hm1 := (integrable_pow_mul_exp_mul_sub_sq_pow a (m - 1) 1).const_mul (m : ℝ)
  have hsum := hm1.add hm
  apply hsum.integrableOn.congr_fun _ measurableSet_Ioi
  intro t ht
  simp only [Pi.add_apply, pow_one]
  ring

/-- A polynomial times a Gaussian tends to zero at positive infinity. -/
theorem tendsto_pow_mul_exp_neg_sq_div_two (r : ℕ) :
    Tendsto (fun t : ℝ =>
      t ^ r * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) atTop (nhds 0) := by
  have h := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
    (show (0 : ℝ) < 1 / 2 by norm_num) (r : ℝ)
  rw [cocompact_eq_atBot_atTop] at h
  have htop := h.mono_left le_sup_right
  apply htop.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  simp only [abs_of_pos ht, Real.rpow_natCast]

/-- The same boundary decay remains valid after multiplying by a power of
an affine quadratic. -/
theorem tendsto_pow_mul_exp_mul_sub_sq_pow
    (a : ℝ) (m r : ℕ) :
    Tendsto (fun t : ℝ =>
      t ^ r * Real.exp (-(1 / 2 : ℝ) * t ^ 2) *
        (a - t ^ 2 / 2) ^ m) atTop (nhds 0) := by
  induction m generalizing r with
  | zero =>
      simpa using tendsto_pow_mul_exp_neg_sq_div_two r
  | succ m ih =>
      have h0 := (ih r).const_mul a
      have h2 := (ih (r + 2)).const_mul (-(1 / 2 : ℝ))
      have hsum := h0.add h2
      have h : Tendsto (fun t : ℝ =>
          t ^ r * Real.exp (-(1 / 2 : ℝ) * t ^ 2) *
            (a - t ^ 2 / 2) ^ (m + 1)) atTop
          (nhds (a * 0 + -(1 / 2 : ℝ) * 0)) := hsum.congr' (by
        filter_upwards with t
        simp only [pow_succ]
        ring)
      simpa only [mul_zero, add_zero] using h

/-- The primitive used in the signed boundary calculation vanishes at
positive infinity. -/
theorem tendsto_ginibre_signed_boundary_primitive
    (a : ℝ) (m : ℕ) :
    Tendsto (fun t : ℝ =>
      Real.exp (-(1 / 2 : ℝ) * t ^ 2) *
        (a - t ^ 2 / 2) ^ m) atTop (nhds 0) := by
  simpa using tendsto_pow_mul_exp_mul_sub_sq_pow a m 0

/-- The pointwise derivative identity behind the scalar recurrence. -/
theorem hasDerivAt_ginibre_signed_boundary_primitive
    (a : ℝ) (m : ℕ) (t : ℝ) :
    HasDerivAt (fun y : ℝ =>
      Real.exp (-(1 / 2 : ℝ) * y ^ 2) *
        (a - y ^ 2 / 2) ^ m)
      (-t * Real.exp (-(1 / 2 : ℝ) * t ^ 2) *
        ((m : ℝ) * (a - t ^ 2 / 2) ^ (m - 1) +
          (a - t ^ 2 / 2) ^ m)) t := by
  have hexp : HasDerivAt (fun y : ℝ =>
      Real.exp (-(1 / 2 : ℝ) * y ^ 2))
      (-t * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) t := by
    convert (((hasDerivAt_pow 2 t).const_mul (-(1 / 2 : ℝ))).exp) using 1 <;>
      norm_num <;> ring
  have hquad : HasDerivAt (fun y : ℝ => a - y ^ 2 / 2) (-t) t := by
    convert (hasDerivAt_const t a).sub
      ((hasDerivAt_pow 2 t).div_const 2) using 1 <;>
      norm_num <;> ring
  convert hexp.mul (hquad.pow m) using 1 <;>
    norm_num <;> ring

/-- Exact half-line Gaussian boundary integral.  This is the analytic core
of the two-incidence dimension jump; it uses only the fundamental theorem
of calculus and Gaussian decay. -/
theorem integral_Ioi_ginibre_signed_boundary
    (a : ℝ) (m : ℕ) :
    (∫ t : ℝ in Ioi 0,
      t * Real.exp (-(1 / 2 : ℝ) * t ^ 2) *
        ((m : ℝ) * (a - t ^ 2 / 2) ^ (m - 1) +
          (a - t ^ 2 / 2) ^ m)) = a ^ m := by
  let F : ℝ → ℝ := fun t =>
    Real.exp (-(1 / 2 : ℝ) * t ^ 2) * (a - t ^ 2 / 2) ^ m
  let f : ℝ → ℝ := fun t =>
    -t * Real.exp (-(1 / 2 : ℝ) * t ^ 2) *
      ((m : ℝ) * (a - t ^ 2 / 2) ^ (m - 1) +
        (a - t ^ 2 / 2) ^ m)
  have hderiv : ∀ t : ℝ, HasDerivAt F (f t) t := by
    intro t
    simpa only [F, f] using
      hasDerivAt_ginibre_signed_boundary_primitive a m t
  have hint : IntegrableOn f (Ioi 0) := by
    change IntegrableOn (fun t : ℝ =>
      -t * Real.exp (-(1 / 2 : ℝ) * t ^ 2) *
        ((m : ℝ) * (a - t ^ 2 / 2) ^ (m - 1) +
          (a - t ^ 2 / 2) ^ m)) (Ioi 0)
    simpa only [neg_mul] using
      (integrableOn_ginibre_signed_boundary_derivative a m).neg
  have hlim : Tendsto F atTop (nhds 0) := by
    simpa only [F] using tendsto_ginibre_signed_boundary_primitive a m
  have hftc : (∫ t : ℝ in Ioi 0, f t) = 0 - F 0 :=
    integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun t _ => hderiv t) hint hlim
  calc
    (∫ t : ℝ in Ioi 0,
      t * Real.exp (-(1 / 2 : ℝ) * t ^ 2) *
        ((m : ℝ) * (a - t ^ 2 / 2) ^ (m - 1) +
          (a - t ^ 2 / 2) ^ m)) =
        -∫ t : ℝ in Ioi 0, f t := by
          rw [← integral_neg]
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          simp only [f]
          ring
    _ = a ^ m := by
      rw [hftc]
      simp [F]

/-! ## The remaining outer Gaussian moment -/

/-- The outer integral left after the boundary evaluation is an elementary
Gamma integral. -/
theorem integral_exp_neg_sq_div_two_mul_half_sq_pow
    (m : ℕ) :
    (∫ s : ℝ,
      Real.exp (-(1 / 2 : ℝ) * s ^ 2) * (s ^ 2 / 2) ^ m) =
      (2 : ℝ) ^ (1 / 2 : ℝ) * Real.Gamma ((m : ℝ) + 1 / 2) := by
  let f : ℝ → ℝ := fun s =>
    Real.exp (-(1 / 2 : ℝ) * s ^ 2) * (s ^ 2 / 2) ^ m
  have hcomp : (fun s : ℝ =>
      Real.exp (-(1 / 2 : ℝ) * s ^ 2) * (s ^ 2 / 2) ^ m) =
      fun s => f |s| := by
    funext s
    simp only [f, sq_abs]
  rw [hcomp, integral_comp_abs]
  have hgamma := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (2 * m : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by
      have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
      linarith) (by norm_num)
  have hIoi : (∫ s : ℝ in Ioi 0, f s) =
      ((2 : ℝ)⁻¹) ^ m *
        ((1 / 2 : ℝ) ^ (-((2 * m : ℝ) + 1) / 2) *
          (1 / 2 : ℝ) * Real.Gamma (((2 * m : ℝ) + 1) / 2)) := by
    rw [show (∫ s : ℝ in Ioi 0, f s) =
        ((2 : ℝ)⁻¹) ^ m *
          ∫ s : ℝ in Ioi 0,
            s ^ (2 * m : ℝ) * Real.exp (-(1 / 2 : ℝ) * s ^ (2 : ℝ)) by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      simp only [f]
      have hspow : s ^ (2 * (m : ℝ)) = (s ^ 2) ^ m := by
        rw [show (2 : ℝ) * (m : ℝ) = ((2 * m : ℕ) : ℝ) by norm_num]
        rw [Real.rpow_natCast, pow_mul]
      rw [hspow, div_pow]
      field_simp
      have hpow : (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ m = 1 := by
        rw [← mul_pow]
        norm_num
        exact one_pow m
      have hscaled := congrArg
        (fun q : ℝ => (s ^ 2) ^ m * q * Real.exp (-(s ^ 2 / 2)))
        hpow.symm
      calc
        Real.exp (-(s ^ 2 / 2)) * (s ^ 2) ^ m =
            (s ^ 2) ^ m * 1 * Real.exp (-(s ^ 2 / 2)) := by ring
        _ = (s ^ 2) ^ m *
            ((2 : ℝ) ^ m * (1 / 2 : ℝ) ^ m) *
              Real.exp (-(s ^ 2 / 2)) := hscaled
        _ = (s ^ 2) ^ m * (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ m *
              Real.exp (-(s ^ 2 / 2)) := by ac_rfl
      rw [Real.rpow_two]]
    rw [hgamma]
  rw [hIoi]
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have htwo : (0 : ℝ) < 2 := by norm_num
  calc
    2 * (((2 : ℝ)⁻¹) ^ m *
        ((1 / 2 : ℝ) ^ (-((2 * m : ℝ) + 1) / 2) *
          (1 / 2 : ℝ) * Real.Gamma (((2 * m : ℝ) + 1) / 2))) =
        ((1 / 2 : ℝ) ^ (m : ℝ) *
          (1 / 2 : ℝ) ^ (-((2 * m : ℝ) + 1) / 2)) *
            Real.Gamma (((2 * m : ℝ) + 1) / 2) := by
      rw [← Real.rpow_natCast ((2 : ℝ)⁻¹) m]
      rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
      ring
    _ = (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) *
          Real.Gamma ((m : ℝ) + 1 / 2) := by
      rw [← Real.rpow_add hhalf]
      have hexp : (m : ℝ) + (-((2 * m : ℝ) + 1) / 2) =
          -(1 / 2 : ℝ) := by ring
      have harg : ((2 * m : ℝ) + 1) / 2 = (m : ℝ) + 1 / 2 := by ring
      rw [hexp, harg]
    _ = (2 : ℝ) ^ (1 / 2 : ℝ) *
          Real.Gamma ((m : ℝ) + 1 / 2) := by
      rw [Real.rpow_neg hhalf.le]
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.inv_rpow htwo.le]
      rw [inv_inv]

/-- Fully evaluated nested integral in the rotated `(s,t)` coordinates.
The region `t > 0` is the image of the ordered-root region `u < x`. -/
theorem integral_integral_ginibre_signed_rotated
    (m : ℕ) :
    (∫ s : ℝ, ∫ t : ℝ in Ioi 0,
      (-Real.sqrt 2 / (2 * Real.pi)) *
        Real.exp (-(1 / 2 : ℝ) * s ^ 2) *
        (t * Real.exp (-(1 / 2 : ℝ) * t ^ 2) *
          ((m : ℝ) * (s ^ 2 / 2 - t ^ 2 / 2) ^ (m - 1) +
            (s ^ 2 / 2 - t ^ 2 / 2) ^ m))) =
      -Real.Gamma ((m : ℝ) + 1 / 2) / Real.pi := by
  have hinner : ∀ s : ℝ,
      (∫ t : ℝ in Ioi 0,
        (-Real.sqrt 2 / (2 * Real.pi)) *
          Real.exp (-(1 / 2 : ℝ) * s ^ 2) *
          (t * Real.exp (-(1 / 2 : ℝ) * t ^ 2) *
            ((m : ℝ) * (s ^ 2 / 2 - t ^ 2 / 2) ^ (m - 1) +
              (s ^ 2 / 2 - t ^ 2 / 2) ^ m))) =
        (-Real.sqrt 2 / (2 * Real.pi)) *
          Real.exp (-(1 / 2 : ℝ) * s ^ 2) * (s ^ 2 / 2) ^ m := by
    intro s
    rw [show (∫ t : ℝ in Ioi 0,
        (-Real.sqrt 2 / (2 * Real.pi)) *
          Real.exp (-(1 / 2 : ℝ) * s ^ 2) *
          (t * Real.exp (-(1 / 2 : ℝ) * t ^ 2) *
            ((m : ℝ) * (s ^ 2 / 2 - t ^ 2 / 2) ^ (m - 1) +
              (s ^ 2 / 2 - t ^ 2 / 2) ^ m))) =
        (-Real.sqrt 2 / (2 * Real.pi)) *
          Real.exp (-(1 / 2 : ℝ) * s ^ 2) *
            ∫ t : ℝ in Ioi 0,
              t * Real.exp (-(1 / 2 : ℝ) * t ^ 2) *
                ((m : ℝ) * (s ^ 2 / 2 - t ^ 2 / 2) ^ (m - 1) +
                  (s ^ 2 / 2 - t ^ 2 / 2) ^ m) by
      rw [← integral_const_mul]]
    rw [show (fun t : ℝ =>
        t * Real.exp (-(1 / 2 : ℝ) * t ^ 2) *
          ((m : ℝ) * (s ^ 2 / 2 - t ^ 2 / 2) ^ (m - 1) +
            (s ^ 2 / 2 - t ^ 2 / 2) ^ m)) =
        fun t : ℝ =>
          t * Real.exp (-(1 / 2 : ℝ) * t ^ 2) *
            ((m : ℝ) * (s ^ 2 / 2 - t ^ 2 / 2) ^ (m - 1) +
              (s ^ 2 / 2 - t ^ 2 / 2) ^ m) by rfl]
    rw [integral_Ioi_ginibre_signed_boundary (s ^ 2 / 2) m]
  rw [show (fun s : ℝ => ∫ t : ℝ in Ioi 0,
      (-Real.sqrt 2 / (2 * Real.pi)) *
        Real.exp (-(1 / 2 : ℝ) * s ^ 2) *
        (t * Real.exp (-(1 / 2 : ℝ) * t ^ 2) *
          ((m : ℝ) * (s ^ 2 / 2 - t ^ 2 / 2) ^ (m - 1) +
            (s ^ 2 / 2 - t ^ 2 / 2) ^ m))) =
      fun s : ℝ =>
        (-Real.sqrt 2 / (2 * Real.pi)) *
          Real.exp (-(1 / 2 : ℝ) * s ^ 2) * (s ^ 2 / 2) ^ m by
    funext s
    exact hinner s]
  rw [show (∫ s : ℝ,
      (-Real.sqrt 2 / (2 * Real.pi)) *
        Real.exp (-(1 / 2 : ℝ) * s ^ 2) * (s ^ 2 / 2) ^ m) =
      (-Real.sqrt 2 / (2 * Real.pi)) *
        ∫ s : ℝ,
          Real.exp (-(1 / 2 : ℝ) * s ^ 2) * (s ^ 2 / 2) ^ m by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with s
    ring]
  rw [integral_exp_neg_sq_div_two_mul_half_sq_pow m]
  rw [← Real.sqrt_eq_rpow]
  have hsqrt : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  nlinarith

end

end NumStability
