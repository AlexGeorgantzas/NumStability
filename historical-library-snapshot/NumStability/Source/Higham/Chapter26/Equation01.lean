/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import Mathlib.Data.Real.Basic

namespace NumStability

/-! # Higham Chapter 26, Equation 26.1

The global-maximizer vocabulary associated with Higham, second edition, equation (26.1).
-/

/-- Higham, 2nd ed., Section 26.1, p. 472, equation (26.1): a point is a
global maximizer of a real objective on the unconstrained search space. -/
def IsGlobalMax {α : Type*} (f : α → ℝ) (x : α) : Prop :=
  ∀ y, f y ≤ f x

/-- Optional global-optimality postcondition for equation (26.1), retained as
general vocabulary.  This is not an operational direct-search specification,
and no Chapter 26 algorithm assumes or produces this certificate. -/
def DirectSearchSpec {α : Type*} (search : (α → ℝ) → α) : Prop :=
  ∀ f, IsGlobalMax f (search f)

end NumStability
