/-
# Scalar projection integrals used in Spijker's planar argument

This file isolates the elementary analytic identity behind the projection-
average step in Spijker's proof: the absolute real projection of one complex
vector, averaged over a full turn, is four times its Euclidean norm.
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace NumStability

open scoped Real
open Complex MeasureTheory

noncomputable section

/-- The absolute cosine has integral four over one full turn. -/
theorem intervalIntegral_abs_cos_zero_two_pi :
    (∫ θ in (0 : ℝ)..2 * Real.pi, |Real.cos θ|) = 4 := by
  have hperiodic : Function.Periodic (fun θ : ℝ ↦ |Real.cos θ|) (2 * Real.pi) :=
    by
      intro θ
      exact congrArg abs (Real.cos_periodic θ)
  have hshift := hperiodic.intervalIntegral_add_eq (0 : ℝ) (-(Real.pi / 2))
  have hend : -(Real.pi / 2) + 2 * Real.pi = Real.pi + Real.pi / 2 := by ring
  have hshift' :
      (∫ θ in (0 : ℝ)..2 * Real.pi, |Real.cos θ|) =
        ∫ θ in -(Real.pi / 2)..Real.pi + Real.pi / 2, |Real.cos θ| := by
    simpa only [zero_add, hend] using hshift
  rw [hshift']
  have hab : IntervalIntegrable (fun θ : ℝ ↦ |Real.cos θ|) volume
      (-(Real.pi / 2)) (Real.pi / 2) :=
    Real.continuous_cos.abs.intervalIntegrable _ _
  have hbc : IntervalIntegrable (fun θ : ℝ ↦ |Real.cos θ|) volume
      (Real.pi / 2) (Real.pi + Real.pi / 2) :=
    Real.continuous_cos.abs.intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    hab hbc]
  have hleft :
      (∫ θ in -(Real.pi / 2)..Real.pi / 2, |Real.cos θ|) =
        ∫ θ in -(Real.pi / 2)..Real.pi / 2, Real.cos θ := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    change |Real.cos θ| = Real.cos θ
    rw [abs_of_nonneg]
    apply Real.cos_nonneg_of_mem_Icc
    simpa [Set.uIcc_of_le (by linarith [Real.pi_pos.le] : -(Real.pi / 2) ≤ Real.pi / 2)]
      using hθ
  have hright :
      (∫ θ in Real.pi / 2..Real.pi + Real.pi / 2, |Real.cos θ|) =
        ∫ θ in Real.pi / 2..Real.pi + Real.pi / 2, -Real.cos θ := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    change |Real.cos θ| = -Real.cos θ
    rw [abs_of_nonpos]
    have hθ' : θ ∈ Set.Icc (Real.pi / 2) (Real.pi + Real.pi / 2) := by
      simpa [Set.uIcc_of_le
        (by linarith [Real.pi_pos.le] : Real.pi / 2 ≤ Real.pi + Real.pi / 2)] using hθ
    exact Real.cos_nonpos_of_pi_div_two_le_of_le hθ'.1 hθ'.2
  rw [hleft, hright]
  simp only [intervalIntegral.integral_neg, integral_cos]
  simp [Real.sin_add]
  norm_num

/-- Pointwise polar-coordinate form of an absolute real projection. -/
theorem abs_re_exp_neg_mul_I_mul (w : ℂ) (θ : ℝ) :
    |(Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) * w).re| =
      ‖w‖ * |Real.cos (Complex.arg w - θ)| := by
  have hprod :
      Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) * w =
        (‖w‖ : ℂ) *
          Complex.exp (((Complex.arg w - θ : ℝ) : ℂ) * Complex.I) := by
    calc
      Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) * w =
          Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) *
          ((‖w‖ : ℂ) * Complex.exp ((Complex.arg w : ℂ) * Complex.I)) := by
            rw [Complex.norm_mul_exp_arg_mul_I]
      _ =
          (‖w‖ : ℂ) *
            (Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) *
              Complex.exp ((Complex.arg w : ℂ) * Complex.I)) := by ring
      _ = (‖w‖ : ℂ) * Complex.exp
          (((-θ : ℝ) : ℂ) * Complex.I + (Complex.arg w : ℂ) * Complex.I) := by
            rw [Complex.exp_add]
      _ = (‖w‖ : ℂ) *
          Complex.exp (((Complex.arg w - θ : ℝ) : ℂ) * Complex.I) := by
            congr 2
            push_cast
            ring
  rw [hprod]
  rw [Complex.mul_re]
  simp only [ofReal_re, ofReal_im, zero_mul, sub_zero,
    Complex.exp_ofReal_mul_I_re]
  rw [abs_mul, abs_of_nonneg (norm_nonneg w)]

/-- Averaging the absolute real projection of `w` over a full turn gives
exactly four times `‖w‖`. -/
theorem intervalIntegral_abs_re_exp_neg_mul_I_mul (w : ℂ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      |(Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) * w).re|) = 4 * ‖w‖ := by
  rw [intervalIntegral.integral_congr (fun θ _ ↦ abs_re_exp_neg_mul_I_mul w θ)]
  rw [intervalIntegral.integral_const_mul]
  have hchange :
      (∫ θ in (0 : ℝ)..2 * Real.pi, |Real.cos (Complex.arg w - θ)|) =
        ∫ θ in Complex.arg w - 2 * Real.pi..Complex.arg w, |Real.cos θ| := by
    simpa only [sub_zero] using
      (intervalIntegral.integral_comp_sub_left
        (f := fun θ : ℝ ↦ |Real.cos θ|)
        (a := (0 : ℝ)) (b := 2 * Real.pi) (Complex.arg w))
  rw [hchange]
  have hperiodic : Function.Periodic (fun θ : ℝ ↦ |Real.cos θ|) (2 * Real.pi) := by
    intro θ
    exact congrArg abs (Real.cos_periodic θ)
  have hshift := hperiodic.intervalIntegral_add_eq
    (Complex.arg w - 2 * Real.pi) (0 : ℝ)
  have hend : Complex.arg w - 2 * Real.pi + 2 * Real.pi = Complex.arg w := by ring
  have hcos :
      (∫ θ in Complex.arg w - 2 * Real.pi..Complex.arg w, |Real.cos θ|) = 4 := by
    rw [hend, zero_add] at hshift
    exact hshift.trans intervalIntegral_abs_cos_zero_two_pi
  rw [hcos]
  ring

end

end NumStability
