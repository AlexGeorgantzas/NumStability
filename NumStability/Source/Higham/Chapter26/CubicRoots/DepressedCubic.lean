/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace NumStability

/-! # Higham Chapter 26: Depressed Cubics

The depressed-cubic coefficients and change-of-variable identity used in Section 26.3.3.
-/

/-- The depressed-cubic coefficient `p` from Section 26.3.3. -/
noncomputable def depressedCubicP (a b : ℝ) : ℝ :=
  -(a ^ 2) / 3 + b

/-- The depressed-cubic coefficient `q` from Section 26.3.3. -/
noncomputable def depressedCubicQ (a b c : ℝ) : ℝ :=
  2 * a ^ 3 / 27 - a * b / 3 + c

/-- The change of variable `x = y - a/3` exactly removes the quadratic term. -/
theorem depressedCubic_identity (a b c y : ℝ) :
    (y - a / 3) ^ 3 + a * (y - a / 3) ^ 2 + b * (y - a / 3) + c =
      y ^ 3 + depressedCubicP a b * y + depressedCubicQ a b c := by
  unfold depressedCubicP depressedCubicQ
  ring

end NumStability
