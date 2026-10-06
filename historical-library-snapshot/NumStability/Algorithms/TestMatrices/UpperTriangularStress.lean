import Mathlib.Data.Real.Basic

/-!
# Upper-triangular stress matrices

This module provides the reusable upper-triangular stress matrix used by
matrix-inversion and source-facing Chapter 8 results. The declaration keeps
its historical public name while its implementation lives below the source
layer.
-/

namespace NumStability

/-- The unit upper-triangular stress matrix with constant strict-upper entry
`-α`. This is the matrix labelled Equation (8.3) in Higham, 2nd ed. -/
noncomputable def higham8_3_stressUpper (n : ℕ) (α : ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if i = j then 1
    else if i.val < j.val then -α
    else 0

end NumStability
