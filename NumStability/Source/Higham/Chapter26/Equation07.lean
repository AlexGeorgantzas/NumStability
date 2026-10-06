/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter26.CubicRoots.MonicCubic

namespace NumStability

open scoped BigOperators

/-! # Higham Chapter 26, Equation 26.7

The normalized backward-residual objective for three computed cubic roots.
-/

/-- Higham, 2nd ed., Section 26.3.3, p. 481, equation (26.7): normalized
backward-residual objective for three computed roots. -/
noncomputable def cubicRootResidualMeasure (a b c : ℝ) (z : Fin 3 → ℂ) : ℝ :=
  ‖fun i =>
    ‖monicCubic a b c (z i)‖ /
      (max (max (max |a| |b|) |c|) 1 *
        (∑ j : Fin 4, ‖z i ^ (j : ℕ)‖))‖

end NumStability
