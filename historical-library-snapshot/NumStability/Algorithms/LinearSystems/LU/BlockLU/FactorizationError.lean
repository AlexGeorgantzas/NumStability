import Mathlib.Data.Fintype.BigOperators
import NumStability.Algorithms.LinearSystems.LU.BlockLU.BlockMatrices

/-!
# Block LU factorization error

The reusable entrywise backward-error specification for computed block LU
factors.
-/

namespace NumStability

open scoped BigOperators

/-- **Block LU backward error** (Higham, 2nd ed., §§13.2--13.3).
    Computed block factors L̂, Û satisfy L̂Û = A + ΔA
    with entrywise bound ε on the error. -/
structure BlockLUBackwardError (m r : ℕ) (hm : 0 < m) (hr : 0 < r)
    (A L_hat U_hat : Fin m → Fin m → (Fin r → Fin r → ℝ)) (ε : ℝ) : Prop where
  L_diag : ∀ i : Fin m, L_hat i i = idBlock r
  L_upper_zero : ∀ i j : Fin m, i.val < j.val → L_hat i j = zeroBlock r
  U_lower_zero : ∀ i j : Fin m, j.val < i.val → U_hat i j = zeroBlock r
  backward_bound : ∀ (i j : Fin m) (s t : Fin r),
    |∑ k : Fin m, ∑ l : Fin r, L_hat i k s l * U_hat k j l t - A i j s t| ≤ ε

end NumStability
