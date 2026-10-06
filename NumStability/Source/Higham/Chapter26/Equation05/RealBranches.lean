/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace NumStability

/-! # Higham Chapter 26, Equation 26.5: Real Branches

The real radicand and plus and minus branches of Cardano's quadratic in equation (26.5).
-/

/-- The radicand in the quadratic equation for `w^3`. -/
noncomputable def cubicRadicand (p q : ℝ) : ℝ :=
  q ^ 2 / 4 + p ^ 3 / 27

/-- Higham, 2nd ed., Section 26.3.3, p. 479, equation (26.5), plus branch. -/
noncomputable def cubicWCubePlus (p q : ℝ) : ℝ :=
  -q / 2 + Real.sqrt (cubicRadicand p q)

/-- Higham, 2nd ed., Section 26.3.3, p. 479, equation (26.5), minus branch. -/
noncomputable def cubicWCubeMinus (p q : ℝ) : ℝ :=
  -q / 2 - Real.sqrt (cubicRadicand p q)

/-- Each real branch in equation (26.5) solves the quadratic equation for
`w^3`, whenever the printed square root has a nonnegative radicand. -/
theorem cubicWCubePlus_quadratic (p q : ℝ) (h : 0 ≤ cubicRadicand p q) :
    cubicWCubePlus p q ^ 2 + q * cubicWCubePlus p q - p ^ 3 / 27 = 0 := by
  have hsqrt : (Real.sqrt (cubicRadicand p q)) ^ 2 = cubicRadicand p q :=
    Real.sq_sqrt h
  unfold cubicWCubePlus cubicRadicand at *
  nlinarith

/-- The minus branch of equation (26.5) satisfies the same quadratic. -/
theorem cubicWCubeMinus_quadratic (p q : ℝ) (h : 0 ≤ cubicRadicand p q) :
    cubicWCubeMinus p q ^ 2 + q * cubicWCubeMinus p q - p ^ 3 / 27 = 0 := by
  have hsqrt : (Real.sqrt (cubicRadicand p q)) ^ 2 = cubicRadicand p q :=
    Real.sq_sqrt h
  unfold cubicWCubeMinus cubicRadicand at *
  nlinarith

end NumStability
