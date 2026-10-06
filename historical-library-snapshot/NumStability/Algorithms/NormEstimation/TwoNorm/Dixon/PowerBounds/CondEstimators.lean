import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Analysis.MatrixAlgebra

/-!
# NumStability Algorithms NormEstimation TwoNorm Dixon PowerBounds CondEstimators

Canonical destination for material split out of
`NumStability.Algorithms.Ch15CondEstimators` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

open scoped Matrix

namespace Ch15

/-- **Dixon's left inequality always holds** (Higham §15.5, Theorem 15.6,
    the `k = 1` rewriting on p. 298).

    "Note that the left-hand inequality in (15.7) always holds" (p. 298).  For
    `k = 1`, (15.7) reads `‖A⁻¹x‖₂ ≤ ‖A⁻¹‖₂ ≤ θ‖A⁻¹x‖₂`, and the always-true left
    part is `‖A⁻¹x‖₂ ≤ ‖A⁻¹‖₂` for a unit vector `x`.  With `B = A⁻¹` this is
        `‖B x‖₂ ≤ ‖B‖₂`      for `‖x‖₂ = 1`.
    It is pure operator-norm submultiplicativity — no probability, no hypothesis
    on `x` beyond being a unit vector.  This is the deterministic core Dixon's
    theorem is built on: the estimate `‖A⁻¹x‖₂` is always a lower bound for
    `‖A⁻¹‖₂`. -/
theorem dixon_left_inequality {n : ℕ} (B : Fin n → Fin n → ℝ) {x : Fin n → ℝ}
    (hx : vecNorm2 x = 1) :
    vecNorm2 (matMulVec n B x) ≤ opNorm2 B := by
  have h := opNorm2Le_opNorm2 B x
  rwa [hx, mul_one] at h

end Ch15
end NumStability
