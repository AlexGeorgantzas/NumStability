/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter23.WinogradInnerProduct

namespace NumStability

open scoped BigOperators Topology
open Filter

/-!
# Higham Chapter 23: Balanced scaling

The balanced-scaling estimates for Winograd inner products from Higham, Chapter 23.
-/

section BalancedScaling

/-- Scalar inequality used in the balanced-scaling consequence after Theorem
23.1.  It converts the sum-of-norms square in (23.12) to the displayed product
bound whenever the two nonzero norms differ by at most a factor `tau`. -/
theorem higham23_balanced_sum_sq_le
    {a b tau : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (htau : 0 < tau)
    (hlower : tau⁻¹ ≤ a / b) (hupper : a / b ≤ tau) :
    (a + b) ^ 2 ≤ 2 * (tau + 1) * a * b := by
  have hab : a ≤ tau * b := (div_le_iff₀ hb).mp hupper
  have hscaled : tau⁻¹ * b ≤ a := (le_div_iff₀ hb).mp hlower
  have htau0 : tau ≠ 0 := ne_of_gt htau
  have hba : b ≤ tau * a := by
    calc
      b = tau * (tau⁻¹ * b) := by field_simp
      _ ≤ tau * a := mul_le_mul_of_nonneg_left hscaled (le_of_lt htau)
  have haa : a * a ≤ tau * a * b := by
    have := mul_le_mul_of_nonneg_left hab ha
    nlinarith
  have hbb : b * b ≤ tau * a * b := by
    have := mul_le_mul_of_nonneg_left hba (le_of_lt hb)
    nlinarith
  nlinarith [sq_nonneg (a + b)]

/-- Balanced-scaling form of Theorem 23.1.  This is the displayed coefficient
after (23.13), specialized to one computed inner product; applying it uniformly
to rows and columns gives the matrix max-entry-norm statement. -/
theorem higham23_balanced_winograd_error (fp : FPModel) {m : ℕ}
    (xOdd xEven yOdd yEven : Fin m → ℝ) (X Y tau : ℝ)
    (hX : 0 ≤ X) (hY : 0 < Y) (htau : 0 < tau)
    (hxOdd : ∀ i, |xOdd i| ≤ X) (hxEven : ∀ i, |xEven i| ≤ X)
    (hyOdd : ∀ i, |yOdd i| ≤ Y) (hyEven : ∀ i, |yEven i| ≤ Y)
    (hlower : tau⁻¹ ≤ X / Y) (hupper : X / Y ≤ tau)
    (hvalid : gammaValid fp (m + 4)) :
    |(∑ i : Fin m, (xOdd i * yOdd i + xEven i * yEven i)) -
        higham23FlWinogradInnerProduct fp xOdd xEven yOdd yEven| ≤
      2 * (tau + 1) * ((2 * m : ℕ) : ℝ) * gamma fp (m + 4) * X * Y := by
  have hmain := higham23_theorem23_1_winograd_error fp
    xOdd xEven yOdd yEven X Y hX (le_of_lt hY)
    hxOdd hxEven hyOdd hyEven hvalid
  have hbalance := higham23_balanced_sum_sq_le hX hY htau hlower hupper
  have hcoeff : 0 ≤ ((2 * m : ℕ) : ℝ) * gamma fp (m + 4) :=
    mul_nonneg (by positivity) (gamma_nonneg fp hvalid)
  calc
    |(∑ i : Fin m, (xOdd i * yOdd i + xEven i * yEven i)) -
        higham23FlWinogradInnerProduct fp xOdd xEven yOdd yEven| ≤
      ((2 * m : ℕ) : ℝ) * gamma fp (m + 4) * (X + Y) ^ 2 := hmain
    _ ≤ ((2 * m : ℕ) : ℝ) * gamma fp (m + 4) *
        (2 * (tau + 1) * X * Y) :=
      mul_le_mul_of_nonneg_left hbalance hcoeff
    _ = _ := by ring

end BalancedScaling

end NumStability
