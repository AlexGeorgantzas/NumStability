/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GinibreDeterminantMoment
import NumStability.Algorithms.TestMatrices.Higham28GinibreProjectiveIntegral

/-! # Higham Chapter 28: normalization in Ginibre Corollary 3.1

This file combines the `n` transverse zero-coordinate Gaussian densities
with the affine projective-chart integral.  Their product is exactly the
universal normalization `ginibreCorollary31Factor (n + 1)`.
-/

namespace NumStability

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- The standard real Gaussian density at zero. -/
theorem gaussianPDFReal_zero_one_zero :
    gaussianPDFReal 0 1 0 = 1 / Real.sqrt (2 * Real.pi) := by
  simp [gaussianPDFReal]

/-- The transverse Gaussian normalization times the projective-chart
normalization is the universal Corollary 3.1 factor. -/
theorem gaussianZeroPow_mul_projectiveConstant (n : ℕ) :
    (gaussianPDFReal 0 1 0) ^ n *
        (Real.pi ^ (((n : ℝ) + 1) / 2) /
          Real.Gamma (((n : ℝ) + 1) / 2)) =
      ginibreCorollary31Factor (n + 1) := by
  rw [gaussianPDFReal_zero_one_zero]
  unfold ginibreCorollary31Factor
  push_cast
  have htwoPi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 htwoPi)
  have hden : Real.sqrt (2 * Real.pi) ^ n =
      (2 : ℝ) ^ ((n : ℝ) / 2) * Real.pi ^ ((n : ℝ) / 2) := by
    calc
      Real.sqrt (2 * Real.pi) ^ n =
          ((2 * Real.pi) ^ (1 / 2 : ℝ)) ^ n := by
        rw [Real.sqrt_eq_rpow]
      _ = ((2 * Real.pi) ^ (1 / 2 : ℝ)) ^ (n : ℝ) := by
        rw [Real.rpow_natCast]
      _ = (2 * Real.pi) ^ ((1 / 2 : ℝ) * (n : ℝ)) := by
        rw [Real.rpow_mul htwoPi.le]
      _ = (2 * Real.pi) ^ ((n : ℝ) / 2) := by
        congr 1
        ring
      _ = (2 : ℝ) ^ ((n : ℝ) / 2) *
          Real.pi ^ ((n : ℝ) / 2) := by
        rw [Real.mul_rpow (by norm_num) Real.pi_nonneg]
  have hnum : Real.pi ^ (((n : ℝ) + 1) / 2) =
      Real.pi ^ ((n : ℝ) / 2) * Real.sqrt Real.pi := by
    calc
      Real.pi ^ (((n : ℝ) + 1) / 2) =
          Real.pi ^ ((n : ℝ) / 2 + 1 / 2) := by
        congr 1
        ring
      _ = Real.pi ^ ((n : ℝ) / 2) * Real.pi ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_add Real.pi_pos]
      _ = _ := by rw [Real.sqrt_eq_rpow]
  rw [div_pow, one_pow, hden, hnum]
  have hpow2 : (2 : ℝ) ^ ((n : ℝ) / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hpowPi : Real.pi ^ ((n : ℝ) / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos _)
  have hG : Real.Gamma (((n : ℝ) + 1) / 2) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  field_simp [hpow2, hpowPi, hG, hsqrt]
  congr 1
  ring

/-- Integral form of the exact Corollary 3.1 normalization. -/
theorem gaussianZeroPow_mul_integral_ginibreProjectiveWeight (n : ℕ) :
    (gaussianPDFReal 0 1 0) ^ n *
        (∫ y : Fin n → ℝ,
          (1 + ∑ i, y i ^ 2) ^ (-(((n : ℝ) + 1) / 2))) =
      ginibreCorollary31Factor (n + 1) := by
  rw [integral_ginibreProjectiveWeight,
    gaussianZeroPow_mul_projectiveConstant]

end
end NumStability
