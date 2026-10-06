/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter26.Equation05.ComplexBranches
import Mathlib.Tactic

namespace NumStability

/-! # Higham Chapter 26, Equation 26.5: Zero-Branch Discrepancy

The counterexample showing that the sentence following equation (26.5) needs a nonzero-branch qualification.
-/

/-- The printed sentence after (26.5) needs a nonzero-branch qualification.
For `p = 0, q = 1`, one of its two signs is zero; its only cube root is zero,
and Vieta's division formula does not produce a depressed-cubic root. -/
theorem higham26_5_printed_eitherSign_zeroBranch_discrepancy :
    ∃ t : ℂ,
      (t = cubicWCubePlusComplex 0 1 ∨ t = cubicWCubeMinusComplex 0 1) ∧
      (0 : ℂ) ^ 3 = t ∧
      (0 - (0 : ℂ) / (3 * 0)) ^ 3 +
          0 * (0 - (0 : ℂ) / (3 * 0)) + 1 ≠ 0 := by
  have hs := algebraicComplexSqrt_sq (cubicRadicandComplex 0 1)
  have hs' : algebraicComplexSqrt (cubicRadicandComplex 0 1) ^ 2 =
      (1 : ℂ) / 4 := by
    simpa [cubicRadicandComplex] using hs
  have hprod : cubicWCubePlusComplex 0 1 *
      cubicWCubeMinusComplex 0 1 = 0 := by
    calc
      cubicWCubePlusComplex 0 1 * cubicWCubeMinusComplex 0 1 =
          (1 : ℂ) / 4 -
            algebraicComplexSqrt (cubicRadicandComplex 0 1) ^ 2 := by
              unfold cubicWCubePlusComplex cubicWCubeMinusComplex
              norm_num
              ring
      _ = 0 := by rw [hs']; ring
  rcases mul_eq_zero.mp hprod with hplus | hminus
  · refine ⟨0, Or.inl hplus.symm, by norm_num, ?_⟩
    intro hzero
    apply (one_ne_zero : (1 : ℂ) ≠ 0)
    calc
      (1 : ℂ) = (0 - (0 : ℂ) / (3 * 0)) ^ 3 +
          0 * (0 - (0 : ℂ) / (3 * 0)) + 1 := by norm_num; rfl
      _ = 0 := hzero
  · refine ⟨0, Or.inr hminus.symm, by norm_num, ?_⟩
    intro hzero
    apply (one_ne_zero : (1 : ℂ) ≠ 0)
    calc
      (1 : ℂ) = (0 - (0 : ℂ) / (3 * 0)) ^ 3 +
          0 * (0 - (0 : ℂ) / (3 * 0)) + 1 := by norm_num; rfl
      _ = 0 := hzero

end NumStability
