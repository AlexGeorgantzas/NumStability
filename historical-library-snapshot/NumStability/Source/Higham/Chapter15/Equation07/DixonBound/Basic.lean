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
import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.Algebra.CondEstimators
import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.PowerBounds.CondEstimators
import NumStability.Analysis.MatrixAlgebra

/-!
# Chapter15 Equation07 DixonBound Basic

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

/-- **Dixon's left inequality, quadratic-form form** (Higham §15.5, Theorem 15.6,
    eq. (15.7) with `k = 1`).

    Assembling `dixon_quadForm_gram_eq` (`xᵀ(BᵀB)x = ‖Bx‖₂²`) with
    `dixon_left_inequality`: for a unit vector `x` and `B = A⁻¹`,
        `√(xᵀ (Bᵀ B) x) ≤ ‖A⁻¹‖₂`.
    Via `gram_inv_of_isInverse` the matrix `Bᵀ B` is `(A Aᵀ)⁻¹`, so this is
    literally the left inequality of (15.7),
        `(xᵀ (A Aᵀ)⁻¹ x)^{1/2} ≤ ‖A⁻¹‖₂`,
    which the theorem asserts holds *with probability one* (it always holds). -/
theorem dixon_sqrt_quadForm_le_opNorm2 {n : ℕ} (B : Fin n → Fin n → ℝ)
    {x : Fin n → ℝ} (hx : vecNorm2 x = 1) :
    Real.sqrt (quadForm (matMul n (matTranspose B) B) x) ≤ opNorm2 B := by
  -- `√(xᵀ(BᵀB)x) = √(‖Bx‖²) = ‖Bx‖₂ ≤ ‖B‖₂`.
  rw [dixon_quadForm_gram_eq B x]
  have hsqrt : Real.sqrt (vecNorm2Sq (matMulVec n B x)) = vecNorm2 (matMulVec n B x) :=
    rfl
  rw [hsqrt]
  exact dixon_left_inequality B hx

end Ch15
end NumStability
