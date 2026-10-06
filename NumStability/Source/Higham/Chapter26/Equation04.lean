/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Analysis.MatrixAlgebra

namespace NumStability

/-! # Higham Chapter 26, Equation 26.4

The normalized inverse-residual stability measure from equation (26.4).
-/

/-- Higham, 2nd ed., Section 26.3.2, p. 478, equation (26.4): the normalized
minimum of the left and right inverse residuals, in the repository's exact
maximum-row-sum matrix norm. -/
noncomputable def inverseResidualStabilityMeasure {n : ℕ}
    (A X : Fin n → Fin n → ℝ) : ℝ :=
  let leftResidual := fun i j => matMul n A X i j - idMatrix n i j
  let rightResidual := fun i j => matMul n X A i j - idMatrix n i j
  min (infNorm leftResidual) (infNorm rightResidual) /
    (infNorm A * infNorm X)

end NumStability
