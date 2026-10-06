import Mathlib

namespace HighamBenchCandidate

noncomputable section

/- The exact denominator and componentwise softmax of (1.2). -/
def exactDenominator {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, Real.exp (x j)

def softmax {n : ℕ} (x : Fin n → ℝ) (j : Fin n) : ℝ :=
  Real.exp (x j) / exactDenominator x

/- Algorithm 3.1 starts with zero and adds exponentials in index order. The
   addition of the first computed exponential to zero is exact; every later
   addition has the relative error of the standard model (1.7). -/
def roundedDenominator {n : ℕ} (w : Fin n → ℝ) (addErr : Fin n → ℝ) : ℝ :=
  (List.finRange n).foldl
    (fun s j => if j.val = 0 then w j else (s + w j) * (1 + addErr j)) 0

def infinityNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  (List.finRange n).foldl (fun m j => max m |v j|) 0

/- Relative models for exponential evaluation (3.1), recursive summation,
   and the final divisions. These models apply in the stipulated absence of
   overflow and underflow. -/
def computedExp {n : ℕ} (x : Fin n → ℝ) (expErr : Fin n → ℝ) (j : Fin n) : ℝ :=
  Real.exp (x j) * (1 + expErr j)

def computedSoftmax {n : ℕ} (x : Fin n → ℝ)
    (expErr addErr divErr : Fin n → ℝ) (j : Fin n) : ℝ :=
  (computedExp x expErr j /
    roundedDenominator (computedExp x expErr) addErr) * (1 + divErr j)

theorem target :
    ∀ (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ),
      ∃ C : ℝ, 0 < C ∧ ∃ u₀ : ℝ, 0 < u₀ ∧
        ∀ (u : ℝ), 0 < u → u ≤ u₀ →
          ∀ (expErr addErr divErr : Fin n → ℝ),
            (∀ j, |expErr j| ≤ u) →
            (∀ j, |addErr j| ≤ u) →
            (∀ j, |divErr j| ≤ u) →
              (∀ j, ∃ τ : ℝ,
                computedSoftmax x expErr addErr divErr j = softmax x j * (1 + τ) ∧
                |τ| ≤ ((n : ℝ) + 3) * u + C * u ^ 2) ∧
              infinityNorm (fun j =>
                softmax x j - computedSoftmax x expErr addErr divErr j) /
                infinityNorm (softmax x) ≤ ((n : ℝ) + 3) * u + C * u ^ 2 := by
  sorry

end

end HighamBenchCandidate
