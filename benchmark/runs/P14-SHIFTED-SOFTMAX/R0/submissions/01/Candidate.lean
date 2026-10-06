import Mathlib

namespace HighamBenchCandidate

/-- The exact shifted exponential at each input entry. -/
noncomputable def exactWeight {n : ℕ} (x : Fin n → ℝ) (k i : Fin n) : ℝ :=
  Real.exp (x i - x k)

/-- The exponential after a rounded subtraction and a relative error in `exp`. -/
noncomputable def computedWeight {n : ℕ} (x : Fin n → ℝ) (k : Fin n)
    (subError expError : Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.exp ((x i - x k) * (1 + subError i)) * (1 + expError i)

/-- Sum the nonmaximal weights in the supplied order. The first term is copied
exactly; every subsequent addition has one relative rounding error. -/
def roundedSum {n : ℕ} (w addError : Fin n → ℝ) : List (Fin n) → ℝ
  | [] => 0
  | i :: is => is.foldl (fun s j => (s + w j) * (1 + addError j)) (w i)

/-- Exact softmax, using the selected maximum as the shift. -/
noncomputable def exactSoftmax {n : ℕ} (x : Fin n → ℝ) (k : Fin n)
    (order : List (Fin n)) (i : Fin n) : ℝ :=
  exactWeight x k i / (1 + (order.map (exactWeight x k)).sum)

/-- Shifted softmax with rounded exponentials, recursively summed nonmaximal
weights, and one rounded division per output. -/
noncomputable def computedSoftmax {n : ℕ} (x : Fin n → ℝ) (k : Fin n)
    (order : List (Fin n)) (subError expError addError divError : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  let w := computedWeight x k subError expError
  (w i / (1 + roundedSum w addError order)) * (1 + divError i)

/-- The minimum input entry. -/
noncomputable def minimumEntry {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  sInf (Set.range x)

/-- Theorem 4.3, equation (4.11), of Blanchard, D. J. Higham, and N. J.
Higham. The quadratic remainder is uniform in all local rounding errors for
each fixed input, selected maximum, and summation order. -/
theorem target :
    ∀ (n : ℕ) (x : Fin n → ℝ) (k : Fin n) (order : List (Fin n)),
      2 ≤ n →
      (∀ i, x i ≤ x k) →
      order.Nodup →
      (∀ i, i ∈ order ↔ i ≠ k) →
      ∃ (C ε : ℝ), 0 ≤ C ∧ 0 < ε ∧
        ∀ (u : ℝ), 0 < u → u < ε →
          ∀ (subError expError addError divError : Fin n → ℝ),
            (∀ i, |subError i| ≤ u) →
            (∀ i, |expError i| ≤ u) →
            (∀ i, |addError i| ≤ u) →
            (∀ i, |divError i| ≤ u) →
            ‖(fun i : Fin n =>
                computedSoftmax x k order subError expError addError divError i -
                  exactSoftmax x k order i)‖ /
                ‖(fun i : Fin n => exactSoftmax x k order i)‖ ≤
              ((n : ℝ) + 2 + 2 * (x k - minimumEntry x)) * u + C * u ^ 2 := by
  sorry

end HighamBenchCandidate
