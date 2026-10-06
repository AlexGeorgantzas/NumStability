import NumStability.Algorithms.Summation.Tree.Core

namespace HighamBenchCandidate

open NumStability

/-- One relative rounding error for each addition in a binary summation tree. -/
inductive LocalErrors : {n : ℕ} → SumTree n → Type where
  | leaf : LocalErrors .leaf
  | node {m n : ℕ} {l : SumTree m} {r : SumTree n}
      (left : LocalErrors l) (right : LocalErrors r) (delta : ℝ) :
      LocalErrors (.node l r)

/-- The actual execution: each addition acts on the computed child sums. -/
noncomputable def computed : {n : ℕ} → {t : SumTree n} →
    LocalErrors t → (Fin n → ℝ) → ℝ
  | _, _, .leaf, v => v 0
  | _, _, @LocalErrors.node m n l r left right delta, v =>
      (computed left (fun i => v (Fin.castAdd _ i)) +
        computed right (fun i => v (Fin.natAdd _ i))) * (1 + delta)

/-- Standard relative-error bound at every addition. -/
def Bounded : {n : ℕ} → {t : SumTree n} → LocalErrors t → ℝ → Prop
  | _, _, .leaf, _ => True
  | _, _, .node left right delta, u =>
      Bounded left u ∧ Bounded right u ∧ |delta| ≤ u

/-- Contributions from all internal nodes. `ancestorFactor` is the product of
    `(1 + delta)` over strict ancestors of the current subtree. -/
noncomputable def contributions (ancestorFactor : ℝ) :
    {n : ℕ} → {t : SumTree n} → LocalErrors t →
      (Fin n → ℝ) → List ℝ
  | _, _, .leaf, _ => []
  | _, _, @LocalErrors.node m n l r left right delta, v =>
      contributions (ancestorFactor * (1 + delta)) left
          (fun i => v (Fin.castAdd _ i)) ++
        contributions (ancestorFactor * (1 + delta)) right
          (fun i => v (Fin.natAdd _ i)) ++
        [ancestorFactor * SumTree.exactSum (.node l r) v * delta]

private theorem contributions_sum_eq {n : ℕ} {t : SumTree n}
    (errors : LocalErrors t) (v : Fin n → ℝ) (ancestorFactor : ℝ) :
    (contributions ancestorFactor errors v).sum =
      ancestorFactor * (computed errors v - SumTree.exactSum t v) := by
  induction errors generalizing ancestorFactor with
  | leaf =>
      simp [contributions, computed, SumTree.exactSum]
  | @node m k l r left right delta ihl ihr =>
      simp only [contributions, List.sum_append, List.sum_singleton,
        computed, SumTree.exactSum]
      rw [ihl, ihr]
      ring

/-- Hallman--Ipsen, Lemma 2.2, equation (2.3): the first explicit
    forward-error expression for general binary-tree summation. -/
theorem target :
    ∀ {n : ℕ} (t : SumTree n) (v : Fin n → ℝ)
      (errors : LocalErrors t) (u : ℝ),
      Bounded errors u →
      computed errors v - SumTree.exactSum t v =
        (contributions 1 errors v).sum := by
  intro n t v errors u _
  simpa using (contributions_sum_eq errors v 1).symm

end HighamBenchCandidate
