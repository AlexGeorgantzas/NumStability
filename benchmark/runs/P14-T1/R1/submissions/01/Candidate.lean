import NumStability.Algorithms.Summation.Recursive.Core
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace HighamBenchCandidate

open NumStability
open scoped BigOperators

/-- The exact positive sum in the summation part of Algorithm 3.1. -/
noncomputable def exactExpSum {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, Real.exp (x i)

/-- The exact sum of the values returned by the exponential evaluations. -/
noncomputable def exactComputedExpSum {n : ℕ} (wHat : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, wHat i

/-- The computed sum uses Algorithm 3.1's left-to-right additions from zero. -/
noncomputable def roundedExpSum (fp : FPModel) {n : ℕ}
    (wHat : Fin n → ℝ) : ℝ :=
  fl_recursiveSum fp n wHat

/-- Equation (3.3) for the positive exponential sum in basic Algorithm 3.1.
The explicit quadratic coefficient is uniform over all permitted local errors
for fixed `n` and `x`. -/
theorem target
    (fp : FPModel) (hu : fp.u < 1)
    (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ)
    (wHat : Fin n → ℝ)
    (hExp : ∀ i : Fin n, ∃ δ : ℝ,
      |δ| ≤ fp.u ∧ wHat i = Real.exp (x i) * (1 + δ)) :
    let s := exactExpSum x
    let sTilde := exactComputedExpSum wHat
    let sHat := roundedExpSum fp wHat
    ∃ Δs : ℝ,
      sHat = s + Δs ∧
      |sTilde - s| ≤ fp.u * s ∧
      |Δs| ≤
        (((n : ℝ) + 1) * fp.u +
          ((2 : ℝ) ^ n - (n : ℝ) - 1) * fp.u ^ 2) * s := by
  sorry

end HighamBenchCandidate
