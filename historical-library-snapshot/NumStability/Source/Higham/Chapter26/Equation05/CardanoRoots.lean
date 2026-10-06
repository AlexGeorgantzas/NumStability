/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter26.CubicRoots.MonicCubic
import NumStability.Source.Higham.Chapter26.Equation05.ComplexBranches
import Mathlib.Tactic

namespace NumStability

/-! # Higham Chapter 26, Equation 26.5: Cardano Roots

The cube-root and Vieta substitutions and the four nonzero-branch Cardano root endpoints.
-/

/-- A constructed complex cube root, available for every value of either
branch in (26.5). -/
noncomputable def algebraicComplexCubeRoot (z : Complex) : Complex :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq z (by norm_num : 0 < 3))

theorem algebraicComplexCubeRoot_cube (z : Complex) :
    algebraicComplexCubeRoot z ^ 3 = z :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq z (by norm_num : 0 < 3))

theorem algebraicComplexCubeRoot_ne_zero {z : Complex} (hz : z ≠ 0) :
    algebraicComplexCubeRoot z ≠ 0 := by
  intro hw
  apply hz
  rw [← algebraicComplexCubeRoot_cube z, hw]
  norm_num

/-- Vieta's substitution maps every nonzero cube root of either quadratic
branch back to a root of the depressed cubic. -/
theorem vietaSubstitution_complex_root
    (p q w t : Complex) (hw : Not (w = 0))
    (hcube : w ^ 3 = t)
    (hquad : t ^ 2 + q * t - p ^ 3 / 27 = 0) :
    (w - p / (3 * w)) ^ 3 + p * (w - p / (3 * w)) + q = 0 := by
  subst t
  field_simp [hw] at hquad
  field_simp [hw]
  ring_nf at hquad
  ring_nf
  exact hquad

/-- Every *nonzero* cube root of the plus branch of (26.5) yields a root of
the original cubic after both source substitutions.  The universal quantifier
over `w` covers all three cube roots when the branch is nonzero. -/
theorem higham26_5_plus_every_nonzeroCubeRoot_monicCubic
    (a b c : ℝ) (w : ℂ)
    (hcube : w ^ 3 = cubicWCubePlusComplex
      (depressedCubicP a b) (depressedCubicQ a b c))
    (hw : w ≠ 0) :
    monicCubic a b c
      (w - (depressedCubicP a b : ℂ) / (3 * w) - (a : ℂ) / 3) = 0 := by
  apply depressedCubic_complex_root_to_monicCubic
  exact vietaSubstitution_complex_root
    (depressedCubicP a b : ℂ) (depressedCubicQ a b c : ℂ) w
    (cubicWCubePlusComplex (depressedCubicP a b) (depressedCubicQ a b c))
    hw hcube
    (cubicWCubePlusComplex_quadratic
      (depressedCubicP a b) (depressedCubicQ a b c))

/-- The corresponding all-cube-roots theorem for the minus branch of (26.5). -/
theorem higham26_5_minus_every_nonzeroCubeRoot_monicCubic
    (a b c : ℝ) (w : ℂ)
    (hcube : w ^ 3 = cubicWCubeMinusComplex
      (depressedCubicP a b) (depressedCubicQ a b c))
    (hw : w ≠ 0) :
    monicCubic a b c
      (w - (depressedCubicP a b : ℂ) / (3 * w) - (a : ℂ) / 3) = 0 := by
  apply depressedCubic_complex_root_to_monicCubic
  exact vietaSubstitution_complex_root
    (depressedCubicP a b : ℂ) (depressedCubicQ a b c : ℂ) w
    (cubicWCubeMinusComplex (depressedCubicP a b) (depressedCubicQ a b c))
    hw hcube
    (cubicWCubeMinusComplex_quadratic
      (depressedCubicP a b) (depressedCubicQ a b c))

/-- Turnkey plus-branch Cardano endpoint: a cube root is constructed rather
than requested from the caller. -/
theorem higham26_5_plus_chosenCubeRoot_monicCubic
    (a b c : ℝ)
    (hbranch : cubicWCubePlusComplex
      (depressedCubicP a b) (depressedCubicQ a b c) ≠ 0) :
    let w := algebraicComplexCubeRoot (cubicWCubePlusComplex
      (depressedCubicP a b) (depressedCubicQ a b c))
    monicCubic a b c
      (w - (depressedCubicP a b : ℂ) / (3 * w) - (a : ℂ) / 3) = 0 := by
  dsimp only
  apply higham26_5_plus_every_nonzeroCubeRoot_monicCubic
  · exact algebraicComplexCubeRoot_cube _
  · exact algebraicComplexCubeRoot_ne_zero hbranch

/-- Turnkey minus-branch Cardano endpoint. -/
theorem higham26_5_minus_chosenCubeRoot_monicCubic
    (a b c : ℝ)
    (hbranch : cubicWCubeMinusComplex
      (depressedCubicP a b) (depressedCubicQ a b c) ≠ 0) :
    let w := algebraicComplexCubeRoot (cubicWCubeMinusComplex
      (depressedCubicP a b) (depressedCubicQ a b c))
    monicCubic a b c
      (w - (depressedCubicP a b : ℂ) / (3 * w) - (a : ℂ) / 3) = 0 := by
  dsimp only
  apply higham26_5_minus_every_nonzeroCubeRoot_monicCubic
  · exact algebraicComplexCubeRoot_cube _
  · exact algebraicComplexCubeRoot_ne_zero hbranch


end NumStability
