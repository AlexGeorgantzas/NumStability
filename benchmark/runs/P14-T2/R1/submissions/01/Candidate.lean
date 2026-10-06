import Mathlib

namespace HighamBenchCandidate

open scoped BigOperators

/-- Exact softmax (paper equation (1.2)) on a positive number of entries. -/
noncomputable def softmax (n : ℕ) (x : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun j => Real.exp (x j) / ∑ i : Fin (n + 1), Real.exp (x i)

/-- The stored exponential from line 3 of the basic Algorithm 3.1. -/
noncomputable def roundedExp (n : ℕ) (x : Fin (n + 1) → ℝ)
    (δexp : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun i => Real.exp (x i) * (1 + δexp i)

/-- Lines 1–5 of Algorithm 3.1. The addition from zero is exact, so there
are `n` rounded additions for `n + 1` stored exponentials. Each subsequent
addition has its own standard-model relative error. -/
noncomputable def roundedDenominator (n : ℕ) (x : Fin (n + 1) → ℝ)
    (δexp : Fin (n + 1) → ℝ) (δadd : Fin n → ℝ) : ℝ :=
  let w := roundedExp n x δexp
  Fin.foldl n (fun s i => (s + w i.succ) * (1 + δadd i)) (w 0)

/-- Lines 7–9 of Algorithm 3.1, with one rounded division per component. -/
noncomputable def roundedSoftmax (n : ℕ) (x : Fin (n + 1) → ℝ)
    (δexp : Fin (n + 1) → ℝ) (δadd : Fin n → ℝ)
    (δdiv : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun j =>
    (roundedExp n x δexp j / roundedDenominator n x δexp δadd) *
      (1 + δdiv j)

/-- Theorem 3.3 and the componentwise result immediately preceding it.
The standard relative-error laws for exponentiation, addition, and division
express the paper's no-overflow/no-underflow regime. The constants in the
quadratic remainder are fixed before choosing the unit roundoff or any local
rounding errors. -/
theorem target :
    ∀ (n : ℕ) (x : Fin (n + 1) → ℝ),
      ∃ C u₀ : ℝ, 0 < C ∧ 0 < u₀ ∧
        ∀ (u : ℝ), 0 < u → u ≤ u₀ →
          ∀ (δexp : Fin (n + 1) → ℝ) (δadd : Fin n → ℝ)
            (δdiv : Fin (n + 1) → ℝ),
            (∀ i, |δexp i| ≤ u) →
            (∀ i, |δadd i| ≤ u) →
            (∀ i, |δdiv i| ≤ u) →
              ∃ τ : Fin (n + 1) → ℝ,
                (∀ j,
                  |τ j| ≤ ((n + 1 : ℕ) + 3 : ℝ) * u + C * u ^ 2 ∧
                  roundedSoftmax n x δexp δadd δdiv j =
                    softmax n x j * (1 + τ j)) ∧
                ‖softmax n x - roundedSoftmax n x δexp δadd δdiv‖ /
                    ‖softmax n x‖ ≤
                  ((n + 1 : ℕ) + 3 : ℝ) * u + C * u ^ 2 := by
  sorry

end HighamBenchCandidate
