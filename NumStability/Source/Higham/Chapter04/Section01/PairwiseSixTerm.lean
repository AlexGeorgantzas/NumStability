import NumStability.Algorithms.Summation.Tree.Core

namespace NumStability

open scoped BigOperators

/-!
# Higham §4.1: six-term pairwise-summation example

Source correspondence for the unnumbered six-term pairwise-summation example
in §4.1 (printed p. 80) of Nicholas J. Higham, *Accuracy and Stability of
Numerical Algorithms*, 2nd ed. (SIAM, 2002). The generic summation-tree
infrastructure used to state and prove its error bounds lives in
`NumStability.Algorithms.Summation.Tree.Core`.
-/

/-- The six-leaf pairwise summation tree displayed in Higham Chapter 4:
`((x₁ + x₂) + (x₃ + x₄)) + (x₅ + x₆)`. -/
def pairwiseSixTree : SumTree 6 :=
  SumTree.node
    (SumTree.node
      (SumTree.node SumTree.leaf SumTree.leaf)
      (SumTree.node SumTree.leaf SumTree.leaf))
    (SumTree.node SumTree.leaf SumTree.leaf)

/-- The displayed six-term pairwise schedule has three addition stages. -/
lemma pairwiseSixTree_depth : pairwiseSixTree.depth = 3 := by
  norm_num [pairwiseSixTree, SumTree.depth]

/-- Floating-point evaluation of the displayed six-term pairwise schedule. -/
noncomputable def fl_pairwiseSumSixDisplayed (fp : FPModel)
    (v : Fin 6 → ℝ) : ℝ :=
  pairwiseSixTree.eval fp v

/-- The explicit parenthesization of the displayed six-term pairwise schedule. -/
theorem fl_pairwiseSumSixDisplayed_eq (fp : FPModel) (v : Fin 6 → ℝ) :
    fl_pairwiseSumSixDisplayed fp v =
      fp.fl_add
        (fp.fl_add
          (fp.fl_add (v ⟨0, by norm_num⟩) (v ⟨1, by norm_num⟩))
          (fp.fl_add (v ⟨2, by norm_num⟩) (v ⟨3, by norm_num⟩)))
        (fp.fl_add (v ⟨4, by norm_num⟩) (v ⟨5, by norm_num⟩)) := by
  norm_num [fl_pairwiseSumSixDisplayed, pairwiseSixTree, SumTree.eval]
  congr 1

/-- Backward-error bound for the displayed six-term pairwise schedule. -/
theorem pairwiseSumSixDisplayed_backward_error (fp : FPModel)
    (v : Fin 6 → ℝ) (hγ : gammaValid fp 3) :
    ∃ η : Fin 6 → ℝ,
      (∀ i, |η i| ≤ gamma fp 3) ∧
      fl_pairwiseSumSixDisplayed fp v =
        ∑ i : Fin 6, v i * (1 + η i) := by
  have ht : gammaValid fp pairwiseSixTree.depth := by
    simpa [pairwiseSixTree_depth] using hγ
  obtain ⟨η, hη, hsum⟩ := SumTree.backward_error fp pairwiseSixTree ht v
  rw [pairwiseSixTree_depth] at hη
  exact ⟨η, hη, by simpa [fl_pairwiseSumSixDisplayed] using hsum⟩

/-- Forward-error bound for the displayed six-term pairwise schedule. -/
theorem pairwiseSumSixDisplayed_forward_error_bound (fp : FPModel)
    (v : Fin 6 → ℝ) (hγ : gammaValid fp 3) :
    |fl_pairwiseSumSixDisplayed fp v - ∑ i : Fin 6, v i| ≤
      gamma fp 3 * ∑ i : Fin 6, |v i| := by
  have ht : gammaValid fp pairwiseSixTree.depth := by
    simpa [pairwiseSixTree_depth] using hγ
  have hbound := SumTree.forward_error fp pairwiseSixTree ht v
  simpa [fl_pairwiseSumSixDisplayed, pairwiseSixTree_depth] using hbound

end NumStability
