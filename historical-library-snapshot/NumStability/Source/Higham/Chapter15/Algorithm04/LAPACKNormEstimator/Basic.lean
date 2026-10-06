import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.NormEstimation.OneNorm.LAPACK.Basic
import NumStability.Analysis.MatrixAlgebra

/-!
# Chapter15 Algorithm04 LAPACKNormEstimator Basic

Canonical destination for material split out of
`NumStability.Algorithms.Chapter15CondEst` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Higham15

open scoped BigOperators

/-- The scalar estimate γ returned by the LAPACK norm estimator (Higham §15.3,
    Algorithm 15.4, p. 293), obtained from the repository's
    `lapackNormEstimator`. -/
noncomputable def H15_Algorithm15_4_gamma {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) : ℝ :=
  lapackNormEstimator hn A

end Higham15
end NumStability
