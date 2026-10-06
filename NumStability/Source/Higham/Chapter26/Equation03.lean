/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Analysis.MatrixAlgebra

namespace NumStability

open scoped BigOperators

/-! # Higham Chapter 26, Equation 26.3

The one-norm relative-size stopping criterion for multidirectional search.
-/

/-- The finite-dimensional vector 1-norm used in equation (26.3). -/
noncomputable def vecOneNorm {n : ℕ} (x : RVec n) : ℝ :=
  ∑ i, |x i|

/-- Higham, 2nd ed., Section 26.2, p. 476, equation (26.3): relative size of
an MDS simplex.  The outer function norm is the maximum over the `n` non-base
vertices (and is zero in the vacuous zero-dimensional case). -/
noncomputable def mdsRelativeSize {n : ℕ} (v0 : RVec n)
    (v : Fin n → RVec n) : ℝ :=
  ‖fun i => vecOneNorm (fun j => v i j - v0 j)‖ / max 1 (vecOneNorm v0)

/-- Equation (26.3), exposed as the exact convergence predicate. -/
def mdsConverged {n : ℕ} (tol : ℝ) (v0 : RVec n)
    (v : Fin n → RVec n) : Prop :=
  mdsRelativeSize v0 v ≤ tol

end NumStability
