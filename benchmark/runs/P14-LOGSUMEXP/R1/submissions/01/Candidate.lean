import NumStability.Algorithms.Summation.Recursive.Core
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace HighamBenchCandidate

open NumStability

/-- The exact, unshifted log-sum-exp value. -/
noncomputable def exactLogSumExp (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  Real.log (∑ i : Fin n, Real.exp (x i))

/-- The log-sum-exp output of Algorithm 3.1, with one relative-error
witness for each exponential evaluation and one for the final logarithm.
The additions are performed by the actual left-to-right rounded sum. -/
noncomputable def basicLogSumExpOutput
    (fp : FPModel) (n : ℕ) (x : Fin n → ℝ)
    (expError : Fin n → ℝ) (logError : ℝ) : ℝ :=
  Real.log
    (fl_recursiveSum fp n
      (fun i => Real.exp (x i) * (1 + expError i))) *
    (1 + logError)

/-- Absolute forward-error bound immediately preceding Theorem 3.2. The
quadratic remainder is uniform over all admissible executions for fixed
dimension and input. -/
theorem target :
    ∀ (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ),
      ∃ C : ℝ, 0 < C ∧
        ∃ u0 : ℝ, 0 < u0 ∧
          ∀ (fp : FPModel) (expError : Fin n → ℝ) (logError : ℝ),
            0 < fp.u → fp.u ≤ u0 →
            (∀ i : Fin n, |expError i| ≤ fp.u) →
            |logError| ≤ fp.u →
            |exactLogSumExp n x -
                basicLogSumExpOutput fp n x expError logError| ≤
              fp.u * |exactLogSumExp n x| +
                ((n : ℝ) + 1) * fp.u + C * fp.u ^ 2 := by
  sorry

end HighamBenchCandidate
