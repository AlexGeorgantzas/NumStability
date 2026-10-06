import NumStability.Algorithms.Summation.Recursive.Core
import NumStability.Algorithms.Summation.Tree.Core

/-!
# Chain trees

Reusable chain-shaped summation trees and their equivalence with left-to-right
recursive summation.
-/

namespace NumStability

open scoped BigOperators

namespace SumTree

-- ============================================================
-- Chain tree (recursive summation, depth n−1)
-- ============================================================

-- Private structural-recursion helper: `chainTree' n : SumTree (n + 1)`.
-- Uses bare constructor names (no `SumTree.` prefix) to avoid dot-notation ambiguity.
private def chainTree' : ∀ n : ℕ, SumTree (n + 1)
  | 0     => leaf
  | n + 1 => node (chainTree' n) leaf

private lemma chainTree'_depth : ∀ n : ℕ, (chainTree' n).depth = n
  | 0     => rfl
  | n + 1 => by
      simp only [chainTree', depth, chainTree'_depth n]
      omega

/-- Successor-indexed left-chain tree, avoiding casts when the number of leaves
is syntactically `n + 1`. -/
def chainTreeSucc (n : ℕ) : SumTree (n + 1) :=
  chainTree' n

/-- The successor-indexed chain tree has depth `n`. -/
lemma chainTreeSucc_depth (n : ℕ) : (chainTreeSucc n).depth = n := by
  exact chainTree'_depth n

/-- The successor-indexed chain tree is the Algorithm 4.1 value-level
specialization of the literal recursive summation loop.  The loop starts from
zero, but the first addition is exact by `FPModel.fl_add_zero`, so both
evaluations agree on `n + 1` inputs. -/
theorem chainTreeSucc_eval_eq_recursiveSum (fp : FPModel) :
    ∀ (n : ℕ) (v : Fin (n + 1) → ℝ),
      (chainTreeSucc n).eval fp v = fl_recursiveSum fp (n + 1) v
  | 0, v => by
      simp [chainTreeSucc, chainTree', eval, fl_recursiveSum, Fin.foldl_succ,
        fp.fl_add_zero]
  | n + 1, v => by
      have hfold :
          fl_recursiveSum fp (n + 2) v =
            fp.fl_add
              (fl_recursiveSum fp (n + 1)
                (fun i : Fin (n + 1) => v i.castSucc))
              (v (Fin.last (n + 1))) :=
        Fin.foldl_succ_last _ _
      rw [hfold]
      simp only [chainTreeSucc, chainTree', eval]
      change
        fp.fl_add
            (eval fp (chainTree' n)
              (fun i : Fin (n + 1) => v i.castSucc))
            (v (Fin.last (n + 1))) =
          fp.fl_add
            (fl_recursiveSum fp (n + 1)
              (fun i : Fin (n + 1) => v i.castSucc))
            (v (Fin.last (n + 1)))
      rw [show
          eval fp (chainTree' n)
              (fun i : Fin (n + 1) => v i.castSucc) =
            fl_recursiveSum fp (n + 1)
              (fun i : Fin (n + 1) => v i.castSucc) by
        simpa [chainTreeSucc] using
          chainTreeSucc_eval_eq_recursiveSum fp n
            (fun i : Fin (n + 1) => v i.castSucc)]

/-- Right-skewed chain tree: `(⋯((v₀ + v₁) + v₂)⋯ + vₙ₋₁)`.
    Depth = `n − 1` — the worst case.  This is the tree underlying
    recursive summation. -/
def chainTree (n : ℕ) (h : 0 < n) : SumTree n :=
  Nat.sub_add_cancel h ▸ chainTree' (n - 1)

/-- The chain tree has depth `n − 1`. -/
lemma chainTree_depth (n : ℕ) (h : 0 < n) : (chainTree n h).depth = n - 1 := by
  unfold chainTree
  rw [depth_cast, chainTree'_depth]

/-- **Chain tree backward error** (Higham §4.2, eq. 4.4 backward form).

    The chain tree for `n` summands has depth `n − 1`, giving the tight
    backward error bound γ(n−1) per summand. -/
theorem chainTree_backward_error (fp : FPModel) (n : ℕ) (hn : 0 < n)
    (h : gammaValid fp (n - 1)) (v : Fin n → ℝ) :
    ∃ η : Fin n → ℝ,
      (∀ i, |η i| ≤ gamma fp (n - 1)) ∧
      (chainTree n hn).eval fp v = ∑ i : Fin n, v i * (1 + η i) := by
  have hd : (chainTree n hn).depth = n - 1 := chainTree_depth n hn
  have hd' : gammaValid fp (chainTree n hn).depth := by rw [hd]; exact h
  obtain ⟨η, hη, heq⟩ := backward_error fp (chainTree n hn) hd' v
  rw [hd] at hη
  exact ⟨η, hη, heq⟩

/-- **Chain tree forward error bound** (Higham §4.2, eq. 4.4). -/
theorem chainTree_forward_error (fp : FPModel) (n : ℕ) (hn : 0 < n)
    (h : gammaValid fp (n - 1)) (v : Fin n → ℝ) :
    |(chainTree n hn).eval fp v - ∑ i : Fin n, v i| ≤
      gamma fp (n - 1) * ∑ i : Fin n, |v i| := by
  have hd : (chainTree n hn).depth = n - 1 := chainTree_depth n hn
  have hd' : gammaValid fp (chainTree n hn).depth := by rw [hd]; exact h
  have hfe := forward_error fp (chainTree n hn) hd' v
  rw [hd] at hfe
  exact hfe

end SumTree

end NumStability
