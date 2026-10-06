import NumStability.Algorithms.Summation.Tree.Core

namespace NumStability

open scoped BigOperators

namespace SumTree

/-!
# Balanced summation trees
-/

-- ============================================================
-- Balanced tree (pairwise summation, depth r)
-- ============================================================

/-- Perfectly balanced binary tree for `2^r` summands.
    Depth = `r = log₂n`.  This is the tree underlying pairwise summation. -/
def balancedTree : ∀ (r : ℕ), SumTree (2 ^ r)
  | 0     => .leaf
  | r + 1 => (show 2 ^ r + 2 ^ r = 2 ^ (r + 1) from by ring) ▸
               .node (balancedTree r) (balancedTree r)

/-- The balanced tree has depth `r`. -/
lemma balancedTree_depth : ∀ r, (balancedTree r).depth = r := by
  intro r; induction r with
  | zero => simp [balancedTree, depth]
  | succ r ih =>
    simp only [balancedTree]
    rw [depth_cast]
    simp only [depth, ih]
    omega

/-- **Balanced tree backward error** (Higham §4.2, eq. 4.6 backward form).

    The balanced tree for `2^r` summands has depth `r`, giving the tight
    backward error bound `γ(r)` per summand (much smaller than `γ(n−1)`). -/
theorem balancedTree_backward_error (fp : FPModel) (r : ℕ)
    (h : gammaValid fp r) (v : Fin (2 ^ r) → ℝ) :
    ∃ η : Fin (2 ^ r) → ℝ,
      (∀ i, |η i| ≤ gamma fp r) ∧
      (balancedTree r).eval fp v = ∑ i : Fin (2 ^ r), v i * (1 + η i) := by
  have hd : (balancedTree r).depth = r := balancedTree_depth r
  have hd' : gammaValid fp (balancedTree r).depth := by rw [hd]; exact h
  obtain ⟨η, hη, heq⟩ := backward_error fp (balancedTree r) hd' v
  rw [hd] at hη
  exact ⟨η, hη, heq⟩

/-- **Balanced tree forward error bound** (Higham §4.2, eq. 4.6). -/
theorem balancedTree_forward_error (fp : FPModel) (r : ℕ)
    (h : gammaValid fp r) (v : Fin (2 ^ r) → ℝ) :
    |(balancedTree r).eval fp v - ∑ i : Fin (2 ^ r), v i| ≤
      gamma fp r * ∑ i : Fin (2 ^ r), |v i| := by
  have hd : (balancedTree r).depth = r := balancedTree_depth r
  have hd' : gammaValid fp (balancedTree r).depth := by rw [hd]; exact h
  have hfe := forward_error fp (balancedTree r) hd' v
  rw [hd] at hfe
  exact hfe

end SumTree

end NumStability
