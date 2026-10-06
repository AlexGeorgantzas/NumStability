/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import Mathlib.Data.Real.Basic

namespace NumStability

/-! # Higham Chapter 26, Equation 26.2

The relative-increase stopping predicate for alternating-directions search.
-/

/-- Higham, 2nd ed., Section 26.2, p. 475, equation (26.2): the alternating-
directions relative-increase stopping test. -/
def adConverged (tol fPrev fNow : ℝ) : Prop :=
  fNow - fPrev ≤ tol * |fPrev|

end NumStability
