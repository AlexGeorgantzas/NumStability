import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.NormEstimation.OneNorm.PowerMethod.CondEstimation
import NumStability.Analysis.MatrixAlgebra

/-!
# NumStability Algorithms NormEstimation OneNorm LAPACK Basic

Canonical destination for material split out of
`NumStability.Algorithms.CondEstimation` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

/-- **Algorithm 14.4** (Higham §14.3, LAPACK 1-norm estimator).

    Enhanced version of Algorithm 14.3 with:
    - Alternating starting vector b with b_i = (−1)^{i+1}(1 + (i−1)/(n−1))
    - Extra column of A evaluated at b for comparison
    - Maximum 5 iterations

    Returns a lower bound γ ≤ ‖A‖₁. -/
noncomputable def lapackAltVec {n : ℕ} (_hn : 1 < n) : Fin n → ℝ :=
  fun i => (if Even i.val then 1 else -1) *
    (1 + (i.val : ℝ) / ((n : ℝ) - 1))

/-- LAPACK norm estimator (Algorithm 14.4): run Algorithm 14.3 up to 5 iterations,
    then compare against the alternating vector estimate. -/
noncomputable def lapackNormEstimator {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) : ℝ :=
  let power_est := (oneNormPowerMethod hn A 5).γ
  if h : 1 < n then
    let b := lapackAltVec h
    let alt_est := oneNormVec (fun i => ∑ j : Fin n, A i j * b j) /
                   oneNormVec b
    max power_est alt_est
  else
    power_est

end NumStability
