import NumStability.Analysis.MatrixAlgebra

namespace HighamBenchCandidate

open NumStability

/-- The nonmaximal indices, in the input order used by Algorithm 4.1. -/
def nonmaxIndices {n : ℕ} (k : Fin n) : List (Fin n) :=
  (List.finRange n).filter (fun i => i ≠ k)

/-- Exact shifted exponential, before any local rounding. -/
noncomputable def exactWeight {n : ℕ} (x : Fin n → ℝ) (k i : Fin n) : ℝ :=
  Real.exp (x i - x k)

/-- Shifted exponentials after one rounded subtraction and one exponential evaluation. -/
noncomputable def computedWeight {n : ℕ} (x : Fin n → ℝ) (k i : Fin n)
    (δsub δexp : Fin n → ℝ) : ℝ :=
  Real.exp ((x i - x k) * (1 + δsub i)) * (1 + δexp i)

/-- Sum the computed nonmaximal exponentials from the first term onward.
The first term is loaded without an addition; each later term has one rounded
addition, as in the summation analysis preceding (4.6). -/
noncomputable def computedNonmaxSum {n : ℕ} (x : Fin n → ℝ) (k : Fin n)
    (δsub δexp δadd : Fin n → ℝ) : ℝ :=
  match nonmaxIndices k with
  | [] => 0
  | i :: rest =>
      rest.foldl
        (fun acc j => (acc + computedWeight x k j δsub δexp) * (1 + δadd j))
        (computedWeight x k i δsub δexp)

noncomputable def exactNonmaxSum {n : ℕ} (x : Fin n → ℝ) (k : Fin n) : ℝ :=
  ((nonmaxIndices k).map (exactWeight x k)).sum

/-- The full exact shifted softmax vector, including the maximal component. -/
noncomputable def exactSoftmax {n : ℕ} (x : Fin n → ℝ) (k : Fin n) :
    Fin n → ℝ :=
  fun i => exactWeight x k i / (1 + exactNonmaxSum x k)

/-- The full computed shifted softmax vector. The final denominator is exactly
`1 +` the computed nonmaximal sum; only the division is rounded. -/
noncomputable def computedSoftmax {n : ℕ} (x : Fin n → ℝ) (k : Fin n)
    (δsub δexp δadd δdiv : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    (computedWeight x k i δsub δexp /
      (1 + computedNonmaxSum x k δsub δexp δadd)) * (1 + δdiv i)

/-- The local relative-error model for the subtraction, exponential,
recursive additions, and final divisions. Errors are indexed separately, so
two calls with equal operands may have different admissible local errors. -/
def AdmissibleErrors {n : ℕ} (u : ℝ)
    (δsub δexp δadd δdiv : Fin n → ℝ) : Prop :=
  (∀ i, |δsub i| ≤ u) ∧
  (∀ i, |δexp i| ≤ u) ∧
  (∀ i, |δadd i| ≤ u) ∧
  (∀ i, |δdiv i| ≤ u)

/-- Theorem 4.3, equation (4.11). The quadratic constant and neighborhood
depend on the fixed input and order, and are uniform over every admissible
choice of local rounding errors. -/
theorem target {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (k : Fin n)
    (hk : ∀ i, x i ≤ x k) :
    ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧
      ∀ (u : ℝ) (δsub δexp δadd δdiv : Fin n → ℝ),
        0 ≤ u → u ≤ ε →
        AdmissibleErrors u δsub δexp δadd δdiv →
        infNormVec (fun i =>
          computedSoftmax x k δsub δexp δadd δdiv i - exactSoftmax x k i) /
            infNormVec (exactSoftmax x k) ≤
          ((n : ℝ) + 2 +
            2 * (x k - Finset.univ.inf' ⟨k, Finset.mem_univ k⟩ x)) * u + C * u ^ 2 := by
  sorry

end HighamBenchCandidate
