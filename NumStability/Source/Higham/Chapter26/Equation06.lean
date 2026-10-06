/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter26.Equation05.ComplexBranches
import NumStability.Source.Higham.Chapter26.Equation05.RealBranches
import Mathlib.Tactic

namespace NumStability

/-! # Higham Chapter 26, Equation 26.6

The stable real and complex branch selections from equation (26.6), together with their exact branch identities.
-/

/-- A nonzero-at-zero sign convention, as required by the stable quadratic
choice in equation (26.6): zero is assigned sign `+1`. -/
noncomputable def stableSign (q : ℝ) : ℝ :=
  if 0 ≤ q then 1 else -1

/-- Higham, 2nd ed., Section 26.3.3, p. 480, equation (26.6): the branch that
avoids cancellation in the real subtraction. -/
noncomputable def stableCubicWCube (p q : ℝ) : ℝ :=
  -q / 2 - stableSign q * Real.sqrt (cubicRadicand p q)

/-- Equation (26.6) is one of the two exact branches in (26.5). -/
theorem stableCubicWCube_eq_branch (p q : ℝ) :
    stableCubicWCube p q =
      if 0 ≤ q then cubicWCubeMinus p q else cubicWCubePlus p q := by
  by_cases hq : 0 ≤ q <;>
    simp [stableCubicWCube, stableSign, cubicWCubeMinus, cubicWCubePlus, hq]

/-- Consequently, the stable branch in (26.6) solves the quadratic for `w^3`
when its radicand is nonnegative. -/
theorem stableCubicWCube_quadratic (p q : ℝ) (h : 0 ≤ cubicRadicand p q) :
    stableCubicWCube p q ^ 2 + q * stableCubicWCube p q - p ^ 3 / 27 = 0 := by
  rw [stableCubicWCube_eq_branch]
  split_ifs
  · exact cubicWCubeMinus_quadratic p q h
  · exact cubicWCubePlus_quadratic p q h

/-- Complex version of the cancellation-avoiding sign choice (26.6). -/
noncomputable def stableCubicWCubeComplex (p q : Real) : Complex :=
  -(q : Complex) / 2 - (stableSign q : Complex) *
    algebraicComplexSqrt (cubicRadicandComplex p q)

theorem stableCubicWCubeComplex_eq_branch (p q : Real) :
    stableCubicWCubeComplex p q =
      if 0 <= q then cubicWCubeMinusComplex p q else cubicWCubePlusComplex p q := by
  by_cases hq : 0 <= q <;>
    simp [stableCubicWCubeComplex, stableSign, cubicWCubeMinusComplex,
      cubicWCubePlusComplex, hq]

theorem stableCubicWCubeComplex_quadratic (p q : Real) :
    stableCubicWCubeComplex p q ^ 2 +
        (q : Complex) * stableCubicWCubeComplex p q -
        (p : Complex) ^ 3 / 27 = 0 := by
  rw [stableCubicWCubeComplex_eq_branch]
  split_ifs
  . exact cubicWCubeMinusComplex_quadratic p q
  . exact cubicWCubePlusComplex_quadratic p q

end NumStability
