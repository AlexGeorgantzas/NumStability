-- Algorithms/Summation/Insertion/RunningError.lean

import Mathlib.Tactic.NormNum
import NumStability.Algorithms.Summation.Insertion.Schedule
import NumStability.Algorithms.Summation.Tree.Core

namespace NumStability

/-!
# Running-error bridge for insertion schedules

This reusable layer materializes dependent `SumTree` values as insertion
schedules and identifies exact-unit-roundoff running-error budgets with exact
merge costs, culminating in the Algorithm 4.1-facing greedy bound.
-/

namespace SumTree

/-- Materialize a dependent `SumTree n` with its source vector as a
list-shaped insertion schedule tree.  This is the bridge from arbitrary
Algorithm 4.1 instances into the explicit leaf-list/weighted-cost layer used
for the printed p. 83 insertion-optimality objective. -/
noncomputable def toInsertionScheduleTree :
    (t : SumTree n) → (Fin n → ℝ) → InsertionScheduleTree
  | .leaf, v => InsertionScheduleTree.leaf (v ⟨0, by norm_num⟩)
  | .node left right, v =>
      InsertionScheduleTree.node
        (toInsertionScheduleTree left (fun i => v (Fin.castAdd _ i)))
        (toInsertionScheduleTree right (fun i => v (Fin.natAdd _ i)))

/-- The materialized list-shaped schedule evaluates exactly like the original
dependent `SumTree`. -/
theorem toInsertionScheduleTree_eval (fp : FPModel) :
    (t : SumTree n) → (v : Fin n → ℝ) →
      (toInsertionScheduleTree t v).eval fp = t.eval fp v
  | .leaf, v => by
      simp [toInsertionScheduleTree, eval]
  | .node left right, v => by
      simp [toInsertionScheduleTree, eval,
        toInsertionScheduleTree_eval fp left,
        toInsertionScheduleTree_eval fp right]

/-- Exact evaluation is preserved by materializing a dependent `SumTree` as a
list-shaped schedule. -/
theorem toInsertionScheduleTree_exactEval :
    (t : SumTree n) → (v : Fin n → ℝ) →
      (toInsertionScheduleTree t v).exactEval = t.exactSum v
  | .leaf, v => by
      simp [toInsertionScheduleTree, exactSum]
  | .node left right, v => by
      simp [toInsertionScheduleTree, exactSum,
        toInsertionScheduleTree_exactEval left,
        toInsertionScheduleTree_exactEval right]

/-- Materializing a dependent `SumTree` preserves the number of source leaves. -/
theorem toInsertionScheduleTree_leafCount :
    (t : SumTree n) → (v : Fin n → ℝ) →
      (toInsertionScheduleTree t v).leafCount = n
  | .leaf, v => by
      simp [toInsertionScheduleTree]
  | .node left right, v => by
      simp [toInsertionScheduleTree,
        toInsertionScheduleTree_leafCount left,
        toInsertionScheduleTree_leafCount right]

/-- Nonnegative source vectors materialize as insertion-schedule trees with
nonnegative leaves. -/
theorem toInsertionScheduleTree_leaves_nonnegative :
    (t : SumTree n) → (v : Fin n → ℝ) →
      (∀ i, 0 ≤ v i) →
        ∀ x ∈ (toInsertionScheduleTree t v).leaves, 0 ≤ x
  | .leaf, v, hv, x, hx => by
      have hx' : x = v ⟨0, by norm_num⟩ := by
        simpa [toInsertionScheduleTree, InsertionScheduleTree.leaves] using hx
      rw [hx']
      exact hv ⟨0, by norm_num⟩
  | .node left right, v, hv, x, hx => by
      have hleft_nonneg :
          ∀ i, 0 ≤ v (Fin.castAdd _ i) := fun i => hv (Fin.castAdd _ i)
      have hright_nonneg :
          ∀ i, 0 ≤ v (Fin.natAdd _ i) := fun i => hv (Fin.natAdd _ i)
      have hleft :=
        toInsertionScheduleTree_leaves_nonnegative left
          (fun i => v (Fin.castAdd _ i)) hleft_nonneg
      have hright :=
        toInsertionScheduleTree_leaves_nonnegative right
          (fun i => v (Fin.natAdd _ i)) hright_nonneg
      simp [toInsertionScheduleTree] at hx
      rcases hx with hx | hx
      · exact hleft x hx
      · exact hright x hx

/-- Under exact arithmetic, dependent `SumTree` evaluation is its exact real
sum. -/
theorem eval_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 ≤ u0) :
    (t : SumTree n) → (v : Fin n → ℝ) →
      eval (FPModel.exactWithUnitRoundoff u0 hu0) t v = t.exactSum v
  | .leaf, v => by
      simp [eval, exactSum]
  | .node left right, v => by
      have hleft :=
        eval_exactWithUnitRoundoff u0 hu0 left
          (fun i => v (Fin.castAdd _ i))
      have hright :=
        eval_exactWithUnitRoundoff u0 hu0 right
          (fun i => v (Fin.natAdd _ i))
      simp [eval, exactSum]
      rw [hleft, hright]
      simp [FPModel.exactWithUnitRoundoff]

/-- Under exact arithmetic, the Algorithm 4.1 running-error budget of an
arbitrary dependent `SumTree` is the exact merge cost of its materialized
list-shaped schedule. -/
theorem runningErrorBudget_exactWithUnitRoundoff_eq_toInsertionScheduleTree_exactMergeCost
    (u0 : ℝ) (hu0 : 0 ≤ u0) :
    (t : SumTree n) → (v : Fin n → ℝ) →
      runningErrorBudget (FPModel.exactWithUnitRoundoff u0 hu0) t v =
        (toInsertionScheduleTree t v).exactMergeCost
  | .leaf, v => by
      simp [runningErrorBudget, toInsertionScheduleTree]
  | .node left right, v => by
      have hbudget_left :=
        runningErrorBudget_exactWithUnitRoundoff_eq_toInsertionScheduleTree_exactMergeCost
          u0 hu0 left (fun i => v (Fin.castAdd _ i))
      have hbudget_right :=
        runningErrorBudget_exactWithUnitRoundoff_eq_toInsertionScheduleTree_exactMergeCost
          u0 hu0 right (fun i => v (Fin.natAdd _ i))
      have heval_left :=
        eval_exactWithUnitRoundoff u0 hu0 left
          (fun i => v (Fin.castAdd _ i))
      have heval_right :=
        eval_exactWithUnitRoundoff u0 hu0 right
          (fun i => v (Fin.natAdd _ i))
      have hexact_left :=
        toInsertionScheduleTree_exactEval left
          (fun i => v (Fin.castAdd _ i))
      have hexact_right :=
        toInsertionScheduleTree_exactEval right
          (fun i => v (Fin.natAdd _ i))
      simp [runningErrorBudget, toInsertionScheduleTree, eval]
      rw [hbudget_left, hbudget_right, heval_left, heval_right,
        hexact_left, hexact_right]
      simp [FPModel.exactWithUnitRoundoff]

/-- For nonnegative source vectors, the exact-arithmetic running-error budget
of an arbitrary Algorithm 4.1 tree is the weighted external path length of its
materialized insertion schedule. -/
theorem runningErrorBudget_exactWithUnitRoundoff_eq_weightedLeafDepthCost_of_nonnegative
    (u0 : ℝ) (hu0 : 0 ≤ u0)
    (t : SumTree n) (v : Fin n → ℝ)
    (hv : ∀ i, 0 ≤ v i) :
    runningErrorBudget (FPModel.exactWithUnitRoundoff u0 hu0) t v =
      InsertionScheduleTree.weightedLeafDepthCost 0
        (toInsertionScheduleTree t v) := by
  rw [runningErrorBudget_exactWithUnitRoundoff_eq_toInsertionScheduleTree_exactMergeCost
    u0 hu0 t v]
  exact
    InsertionScheduleTree.exactMergeCost_eq_weightedLeafDepthCost_of_leaves_nonnegative
      (toInsertionScheduleTree t v)
      (toInsertionScheduleTree_leaves_nonnegative t v hv)

/-- Exact-arithmetic Algorithm 4.1-facing insertion optimality bridge.  Any
supplied greedy insertion schedule whose leaves match the materialized
Algorithm 4.1 tree has exact merge cost no larger than that tree's exact
running-error budget. -/
theorem runningErrorBudget_exactWithUnitRoundoff_greedyInsertion_le
    (u0 : ℝ) (hu0 : 0 ≤ u0)
    (insertion : InsertionScheduleTree)
    (other : SumTree n) (v : Fin n → ℝ)
    (hv : ∀ i, 0 ≤ v i)
    (hperm :
      insertion.leaves.Perm
        (toInsertionScheduleTree other v).leaves)
    (hgreedy : insertion.GreedyInsertionTree) :
    insertion.exactMergeCost ≤
      runningErrorBudget (FPModel.exactWithUnitRoundoff u0 hu0) other v := by
  have hmaterializedNonneg :
      ∀ x ∈ (toInsertionScheduleTree other v).leaves, 0 ≤ x :=
    toInsertionScheduleTree_leaves_nonnegative other v hv
  have hinsertionNonneg : ∀ x ∈ insertion.leaves, 0 ≤ x := by
    intro x hx
    exact hmaterializedNonneg x ((hperm.mem_iff).1 hx)
  rw [runningErrorBudget_exactWithUnitRoundoff_eq_toInsertionScheduleTree_exactMergeCost
    u0 hu0 other v]
  exact
    InsertionScheduleTree.GreedyInsertionTree.exactMergeCost_le
      hgreedy hperm hinsertionNonneg

end SumTree

end NumStability
