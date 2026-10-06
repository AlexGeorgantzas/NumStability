/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter26.CubicRoots.DepressedCubic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

namespace NumStability

/-! # Higham Chapter 26: Monic Cubics

The monic cubic used in equation (26.7) and the complex transfer from the depressed cubic.
-/

/-- The monic cubic used in the residual objective (26.7). -/
def monicCubic (a b c : ℝ) (z : ℂ) : ℂ :=
  z ^ 3 + a * z ^ 2 + b * z + c

/-- The complex version of the `x = y - a/3` handoff used immediately after
(26.5). -/
theorem depressedCubic_complex_root_to_monicCubic
    (a b c : ℝ) (y : ℂ)
    (hy : y ^ 3 + (depressedCubicP a b : ℂ) * y +
      (depressedCubicQ a b c : ℂ) = 0) :
    monicCubic a b c (y - (a : ℂ) / 3) = 0 := by
  calc
    monicCubic a b c (y - (a : ℂ) / 3) =
        y ^ 3 + (depressedCubicP a b : ℂ) * y +
          (depressedCubicQ a b c : ℂ) := by
            unfold monicCubic depressedCubicP depressedCubicQ
            push_cast
            ring
    _ = 0 := hy

end NumStability
