import Mathlib

namespace HighamBenchCandidate

/-- The exact log-sum-exp for an input vector of length `n`. -/
noncomputable def exactLogSumExp {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.log (∑ i : Fin n, Real.exp (x i))

/-- The result of evaluating each exponential with its own relative error. -/
noncomputable def computedExp {n : ℕ} (x : Fin n → ℝ) (expError : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  Real.exp (x i) * (1 + expError i)

/-- Recursive summation in the order `0, ..., n-1`. The target constrains
    the first addition's error to zero, since adding a computed value to zero
    is exact. -/
noncomputable def computedSum {n : ℕ} (x : Fin n → ℝ)
    (expError addError : Fin n → ℝ) : ℝ :=
  (List.finRange n).foldl
    (fun s i => (s + computedExp x expError i) * (1 + addError i)) 0

/-- The final logarithm is evaluated with one relative rounding error. -/
noncomputable def computedLogSumExp {n : ℕ} (x : Fin n → ℝ)
    (expError addError : Fin n → ℝ) (logError : ℝ) : ℝ :=
  Real.log (computedSum x expError addError) * (1 + logError)

/-- Absolute forward-error estimate immediately preceding Theorem 3.2 of
    Blanchard, Higham and Higham (2021), for basic Algorithm 3.1. -/
theorem target :
    ∀ (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ),
      ∃ C : ℝ, 0 < C ∧
      ∃ u₀ : ℝ, 0 < u₀ ∧
      ∀ (u : ℝ) (expError addError : Fin n → ℝ) (logError : ℝ),
        0 < u → u ≤ u₀ →
        (∀ i : Fin n, |expError i| ≤ u) →
        (addError ⟨0, hn⟩ = 0) →
        (∀ i : Fin n, |addError i| ≤ u) →
        |logError| ≤ u →
        |exactLogSumExp x - computedLogSumExp x expError addError logError| ≤
          u * |exactLogSumExp x| + ((n : ℝ) + 1) * u + C * u ^ 2 := by
  sorry

end HighamBenchCandidate
