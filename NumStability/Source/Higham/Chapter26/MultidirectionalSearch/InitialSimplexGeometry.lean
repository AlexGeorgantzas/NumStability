/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Analysis.MatrixAlgebra
import Mathlib.Tactic

namespace NumStability

open scoped BigOperators

/-! # Higham Chapter 26: Initial-Simplex Geometry

The common scale, squared-distance, and edge-dot-product definitions used by the page 476 simplex constructors.
-/

/-- Printed initial-simplex scale `max (‖x₀‖∞, 1)`. -/
noncomputable def higham26MDSInitialScale {n : Nat} (x0 : RVec n) : Real :=
  max ‖x0‖ 1

theorem higham26MDSInitialScale_nonneg {n : Nat} (x0 : RVec n) :
    0 ≤ higham26MDSInitialScale x0 := by
  exact le_trans (by norm_num : (0 : Real) ≤ 1)
    (le_max_right ‖x0‖ 1)

/-- Squared Euclidean distance, used to state the source's edge-length
normalization without conflating it with the function-space sup norm. -/
noncomputable def higham26SquaredDistance {n : Nat}
    (x y : RVec n) : Real :=
  ∑ j : Fin n, (x j - y j) ^ 2

/-- Dot product of two edges with a common base. -/
noncomputable def higham26EdgeDot {n : Nat}
    (base x y : RVec n) : Real :=
  ∑ j : Fin n, (x j - base j) * (y j - base j)

end NumStability
