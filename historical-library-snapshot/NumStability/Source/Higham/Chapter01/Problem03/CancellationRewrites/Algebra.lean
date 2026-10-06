import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Analysis.FloatingPointArithmetic.TrigonometricCancellation.Core

-- Analysis/TrigCancellation.lean
--
-- Exact trigonometric cancellation algebra for Higham Chapter 1, Section 1.7.










namespace NumStability

/-!
# Trigonometric Cancellation Algebra

Higham Chapter 1, Section 1.7 uses `1 - cos x` to illustrate cancellation and
the stable exact rewrite `2 * sin (x/2)^2`.  This file records the exact
real-arithmetic identity, the supplied-error comparison of the two evaluation
paths, and finite round-to-even wrappers for the trigonometric outputs under
finite-normal hypotheses.  It also records the exact cancellation-avoiding
rewrites from Problem 1.3.
-/














-- ============================================================
-- Higham §1.7 scaled target and cancellation-amplification bounds
-- ============================================================



























































































































































-- ============================================================
-- Higham §1.7 finite round-to-even trigonometric routine wrappers
-- ============================================================







































































































































-- ============================================================
-- Higham Problem 1.3 cancellation-avoiding rewrites
-- ============================================================
















/-- Problem 1.3(2): rewrite `sin x - sin y` when `x ≈ y`. -/
theorem problem_1_3_sin_sub_sin (x y : ℝ) :
    Real.sin x - Real.sin y =
      2 * Real.cos ((x + y) / 2) * Real.sin ((x - y) / 2) := by
  rw [Real.sin_sub_sin]
  ring

/-- Problem 1.3(3): factor `x^2-y^2` when `x ≈ y`. -/
theorem problem_1_3_sq_sub_sq (x y : ℝ) :
    x ^ 2 - y ^ 2 = (x - y) * (x + y) := by
  ring

/-- Problem 1.3(4): rewrite `(1-cos x)/sin x` near `x = 0`. -/
theorem problem_1_3_one_sub_cos_div_sin (x : ℝ)
    (hsin : Real.sin x ≠ 0) (hcos : 1 + Real.cos x ≠ 0) :
    (1 - Real.cos x) / Real.sin x = Real.sin x / (1 + Real.cos x) := by
  field_simp [hsin, hcos]
  have h : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
    have hmain := Real.sin_sq_add_cos_sq x
    linarith
  rw [h]
  ring

/-- Problem 1.3(5): first exact radicand rewrite for the law-of-cosines
expression when `a ≈ b` and `theta` is small. -/
theorem problem_1_3_lawOfCosines_radicand_sub_rewrite (a b theta : ℝ) :
    a ^ 2 + b ^ 2 - 2 * a * b * Real.cos theta =
      (a - b) ^ 2 + 2 * a * b * (1 - Real.cos theta) := by
  ring

/-- Problem 1.3(5): half-angle radicand rewrite for the law-of-cosines
expression when `a ≈ b` and `theta` is small. -/
theorem problem_1_3_lawOfCosines_radicand_halfAngle (a b theta : ℝ) :
    a ^ 2 + b ^ 2 - 2 * a * b * Real.cos theta =
      (a - b) ^ 2 + 4 * a * b * (Real.sin (theta / 2)) ^ 2 := by
  calc
    a ^ 2 + b ^ 2 - 2 * a * b * Real.cos theta
        = (a - b) ^ 2 + 2 * a * b * (1 - Real.cos theta) := by
      ring
    _ = (a - b) ^ 2 + 4 * a * b * (Real.sin (theta / 2)) ^ 2 := by
      rw [one_sub_cos_eq_two_sin_sq_half theta]
      ring

/-- Problem 1.3(5): square-root form of the law-of-cosines half-angle rewrite. -/
theorem problem_1_3_lawOfCosines_sqrt_halfAngle (a b theta : ℝ) :
    Real.sqrt (a ^ 2 + b ^ 2 - 2 * a * b * Real.cos theta) =
      Real.sqrt ((a - b) ^ 2 + 4 * a * b * (Real.sin (theta / 2)) ^ 2) := by
  congr 1
  exact problem_1_3_lawOfCosines_radicand_halfAngle a b theta

-- ============================================================
-- Higham §1.7 displayed ten-significant-figure example
-- ============================================================

/-- The input `x = 1.2 * 10^{-5}` from the Chapter 1 cancellation example. -/
noncomputable def trigCancellationExampleX : ℝ :=
  (12 : ℝ) / 1000000





































end NumStability
