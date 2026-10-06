import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Analysis.ConditionEstimatorLowerBound
import NumStability.Analysis.MatrixAlgebra

/-!
# Chapter15 Section01 ConditionNumbers ConditionEstimators

Canonical destination for material split out of
`NumStability.Algorithms.Chapter15CondEst` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Higham15

open scoped BigOperators

/-- **1-norm condition number** (Higham §15.1, eq. (15.1) region, p. 306):
      `κ₁(A) = ‖A‖₁·‖A⁻¹‖₁`.

    Re-export of `condOneNumber` under a Chapter-15 label.  The inverse is
    supplied explicitly as `B` (the matrix the estimator actually samples,
    accessed through linear solves); `H15_kappaOne_eq_of_rightInverse` pins `B`
    to Mathlib's canonical inverse when `A * B = 1`. -/
noncomputable def H15_kappaOne {n : ℕ} (A B : Fin n → Fin n → ℝ) : ℝ :=
  condOneNumber A B

/-- `κ₁(A) ≥ 0` (Higham §15.1). -/
theorem H15_kappaOne_nonneg {n : ℕ} (A B : Fin n → Fin n → ℝ) :
    0 ≤ H15_kappaOne A B :=
  condOneNumber_nonneg A B

/-- **κ₁ at the genuine inverse** (Higham §15.1, eq. (15.1)).

    When `B` is an actual right inverse of `A` (`A * B = 1`), `H15_kappaOne A B`
    is the textbook `‖A‖₁·‖A⁻¹‖₁` with Mathlib's canonical inverse.  Re-export
    of `condOneNumber_eq_kappaOne_of_rightInverse`. -/
theorem H15_kappaOne_eq_of_rightInverse {n : ℕ}
    (A B : Fin n → Fin n → ℝ)
    (h : (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) *
         (Matrix.of B : Matrix (Fin n) (Fin n) ℝ) = 1) :
    H15_kappaOne A B =
      oneNorm A *
        oneNorm (fun i j => (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹ i j) :=
  condOneNumber_eq_kappaOne_of_rightInverse A B h

end Higham15
end NumStability
