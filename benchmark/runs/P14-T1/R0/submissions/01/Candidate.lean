import Mathlib

namespace HighamBenchCandidate

/- The exact positive sum and the exponential values returned by the algorithm. -/
noncomputable def exactSum (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, Real.exp (x i)

noncomputable def computedExp (n : ℕ) (x δ : Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.exp (x i) * (1 + δ i)

/- The exact sum of the already computed exponential values. -/
noncomputable def exactComputedExpSum (n : ℕ) (x δ : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, computedExp n x δ i

/- Algorithm 3.1 accumulates the computed exponentials in increasing index
   order. Adding the first value to zero is exact; each subsequent addition
   has one relative rounding error. -/
noncomputable def computedSum (n : ℕ) (x δ ε : Fin n → ℝ) : ℝ :=
  (List.finRange n).foldl
    (fun acc i =>
      if i.val = 0 then computedExp n x δ i
      else (acc + computedExp n x δ i) * (1 + ε i)) 0

noncomputable def sumError (n : ℕ) (x δ ε : Fin n → ℝ) : ℝ :=
  (computedSum n x δ ε - exactComputedExpSum n x δ) +
    (exactComputedExpSum n x δ - exactSum n x)

theorem target
    (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (δ ε : Fin n → ℝ)
    (hδ : ∀ i, |δ i| ≤ u)
    (hε : ∀ i, |ε i| ≤ u) :
    computedSum n x δ ε = exactSum n x + sumError n x δ ε ∧
      |sumError n x δ ε| ≤
        (((n + 1 : ℕ) : ℝ) * u + (2 : ℝ) ^ (n + 1) * u ^ 2) * exactSum n x := by
  sorry

end HighamBenchCandidate
