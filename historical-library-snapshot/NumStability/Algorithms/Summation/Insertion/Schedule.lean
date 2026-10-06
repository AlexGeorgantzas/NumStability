-- Algorithms/Summation/Insertion/Schedule.lean

import Mathlib.Data.List.Permutation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.Summation.Tree.Core

namespace NumStability

/-!
# Insertion schedules and greedy optimality

This reusable layer defines list-shaped insertion schedules, their exact merge
and weighted-depth costs, contraction and exchange machinery, and the greedy
optimality theorem. The long exchange proof remains cohesive because private
helpers in its middle are reused by later branches.
-/

/-! ## List-shaped insertion schedules -/

/-- A list-shaped binary summation schedule with real source leaves.  This is
an intermediate bridge between the source active-list insertion loop and the
dependent `SumTree` model of Algorithm 4.1. -/
inductive InsertionScheduleTree where
  | leaf (x : ℝ) : InsertionScheduleTree
  | node (left right : InsertionScheduleTree) : InsertionScheduleTree

namespace InsertionScheduleTree

/-- Evaluate a list-shaped schedule using floating-point addition. -/
noncomputable def eval : InsertionScheduleTree → FPModel → ℝ
  | leaf x, _ => x
  | node left right, fp => fp.fl_add (eval left fp) (eval right fp)

/-- Source leaves of a list-shaped schedule, in the schedule's left-to-right
order. -/
def leaves : InsertionScheduleTree → List ℝ
  | leaf x => [x]
  | node left right => leaves left ++ leaves right

@[simp] theorem eval_leaf (fp : FPModel) (x : ℝ) :
    (leaf x).eval fp = x := by
  rfl

@[simp] theorem eval_node (fp : FPModel)
    (left right : InsertionScheduleTree) :
    (node left right).eval fp =
      fp.fl_add (left.eval fp) (right.eval fp) := by
  rfl

@[simp] theorem leaves_leaf (x : ℝ) :
    (leaf x).leaves = [x] := by
  rfl

@[simp] theorem leaves_node (left right : InsertionScheduleTree) :
    (node left right).leaves = left.leaves ++ right.leaves := by
  rfl

/-- Number of source leaves in a list-shaped schedule. -/
def leafCount : InsertionScheduleTree → ℕ
  | leaf _ => 1
  | node left right => left.leafCount + right.leafCount

/-- Maximum leaf depth of a list-shaped schedule, starting from a supplied root
depth. -/
def maxLeafDepth : ℕ → InsertionScheduleTree → ℕ
  | depth, leaf _ => depth
  | depth, node left right =>
      max (maxLeafDepth (depth + 1) left)
        (maxLeafDepth (depth + 1) right)

@[simp] theorem leafCount_leaf (x : ℝ) :
    (leaf x).leafCount = 1 := by
  rfl

@[simp] theorem leafCount_node (left right : InsertionScheduleTree) :
    (node left right).leafCount =
      left.leafCount + right.leafCount := by
  rfl

@[simp] theorem maxLeafDepth_leaf (depth : ℕ) (x : ℝ) :
    maxLeafDepth depth (leaf x) = depth := by
  rfl

@[simp] theorem maxLeafDepth_node (depth : ℕ)
    (left right : InsertionScheduleTree) :
    maxLeafDepth depth (node left right) =
      max (maxLeafDepth (depth + 1) left)
        (maxLeafDepth (depth + 1) right) := by
  rfl

/-- Every list-shaped schedule has at least one leaf. -/
theorem leafCount_pos (tree : InsertionScheduleTree) :
    0 < tree.leafCount := by
  induction tree with
  | leaf x =>
      simp [leafCount]
  | node left right ihl ihr =>
      have hle : left.leafCount ≤ left.leafCount + right.leafCount :=
        Nat.le_add_right left.leafCount right.leafCount
      exact Nat.lt_of_lt_of_le ihl hle

/-- Every node has at least two leaves. -/
theorem one_lt_leafCount_node (left right : InsertionScheduleTree) :
    1 < (node left right).leafCount := by
  have hl : 1 ≤ left.leafCount := leafCount_pos left
  have hr : 1 ≤ right.leafCount := leafCount_pos right
  have htwo : 1 + 1 ≤ left.leafCount + right.leafCount :=
    Nat.add_le_add hl hr
  simpa [leafCount] using Nat.lt_of_succ_le htwo

/-- The concrete source-leaf list has the same length as the structural leaf
count used by the dependent `SumTree`. -/
theorem leaves_length (tree : InsertionScheduleTree) :
    tree.leaves.length = tree.leafCount := by
  induction tree with
  | leaf x =>
      simp [leaves, leafCount]
  | node left right ihl ihr =>
      simp [leaves, leafCount, ihl, ihr]

/-- Convert a list-shaped schedule into the dependent `SumTree` shape with
the same number of source leaves. -/
def toSumTree : (tree : InsertionScheduleTree) →
    SumTree tree.leafCount
  | leaf _ => SumTree.leaf
  | node left right =>
      SumTree.node (toSumTree left) (toSumTree right)

/-- The `Fin`-indexed source vector obtained by reading a list-shaped
schedule's leaves from left to right. -/
def leafVector : (tree : InsertionScheduleTree) →
    Fin tree.leafCount → ℝ
  | leaf x, _ => x
  | node left right, i =>
      Fin.addCases left.leafVector right.leafVector i

/-- The recursive `leafVector` agrees with indexing the concrete source-leaf
list. -/
theorem leafVector_eq_leaves_get (tree : InsertionScheduleTree)
    (i : Fin tree.leafCount) :
    tree.leafVector i =
      tree.leaves.get (Fin.cast (InsertionScheduleTree.leaves_length tree).symm i) := by
  induction tree with
  | leaf x =>
      fin_cases i
      simp [leafVector, leaves, leafCount]
  | node left right ihl ihr =>
      cases i using Fin.addCases with
      | left i =>
          simp [leafVector, leaves, leafCount, leaves_length, ihl i]
      | right i =>
          simp [leafVector, leaves, leafCount, leaves_length, ihr i]

/-- The dependent `SumTree` converted from a list-shaped insertion schedule
evaluates to the same floating-point value when fed the schedule's ordered
leaf vector. -/
theorem toSumTree_eval (fp : FPModel) :
    (tree : InsertionScheduleTree) →
      SumTree.eval fp tree.toSumTree tree.leafVector = tree.eval fp
  | leaf x => by
      simp [toSumTree, leafVector, eval, SumTree.eval]
  | node left right => by
      simp [toSumTree, leafVector, eval, SumTree.eval,
        toSumTree_eval fp left, toSumTree_eval fp right]

/-- Exact real evaluation of a list-shaped insertion schedule. -/
noncomputable def exactEval : InsertionScheduleTree → ℝ
  | leaf x => x
  | node left right => left.exactEval + right.exactEval

/-- Sum of exact absolute intermediate sums for a list-shaped insertion
schedule.  This is the exact-tree counterpart of Higham's running-error
budget in Chapter 4 equation (4.3). -/
noncomputable def exactMergeCost : InsertionScheduleTree → ℝ
  | leaf _ => 0
  | node left right =>
      left.exactMergeCost + right.exactMergeCost +
        |left.exactEval + right.exactEval|

/-- Weighted external path length of a list-shaped insertion schedule, starting
from a supplied depth.  For nonnegative leaves, this is the exact merge-cost
objective in a form suited to optimal-merge/Huffman-style arguments. -/
noncomputable def weightedLeafDepthCost :
    ℕ → InsertionScheduleTree → ℝ
  | depth, leaf x => (depth : ℝ) * x
  | depth, node left right =>
      weightedLeafDepthCost (depth + 1) left +
        weightedLeafDepthCost (depth + 1) right

/-- Leaf depths paired with their leaf weights, starting from a supplied root
depth.  This list form is the rearrangement surface for the printed p. 83 nonnegative
insertion-optimality argument. -/
def leafDepthWeights :
    ℕ → InsertionScheduleTree → List (ℕ × ℝ)
  | depth, leaf x => [(depth, x)]
  | depth, node left right =>
      leafDepthWeights (depth + 1) left ++
        leafDepthWeights (depth + 1) right

/-- Same-shape relabeling of a schedule tree by a left-to-right list of leaf
weights.  If the list has the tree's leaf count, the relabeled tree has exactly
those leaves and the original depth sequence. -/
def relabelLeaves : InsertionScheduleTree → List ℝ → InsertionScheduleTree
  | leaf _, weights => leaf (weights.headD 0)
  | node left right, weights =>
      node (relabelLeaves left (weights.take left.leafCount))
        (relabelLeaves right (weights.drop left.leafCount))

/-- Weighted cost of an explicit list of `(depth, weight)` leaf pairs. -/
noncomputable def weightedDepthPairsCost (pairs : List (ℕ × ℝ)) : ℝ :=
  (pairs.map (fun pair => (pair.1 : ℝ) * pair.2)).sum

@[simp] theorem exactEval_leaf (x : ℝ) :
    (leaf x).exactEval = x := by
  rfl

@[simp] theorem exactEval_node (left right : InsertionScheduleTree) :
    (node left right).exactEval = left.exactEval + right.exactEval := by
  rfl

@[simp] theorem exactMergeCost_leaf (x : ℝ) :
    (leaf x).exactMergeCost = 0 := by
  rfl

@[simp] theorem exactMergeCost_node (left right : InsertionScheduleTree) :
    (node left right).exactMergeCost =
      left.exactMergeCost + right.exactMergeCost +
        |left.exactEval + right.exactEval| := by
  rfl

@[simp] theorem weightedLeafDepthCost_leaf (depth : ℕ) (x : ℝ) :
    weightedLeafDepthCost depth (leaf x) = (depth : ℝ) * x := by
  rfl

@[simp] theorem weightedLeafDepthCost_node (depth : ℕ)
    (left right : InsertionScheduleTree) :
    weightedLeafDepthCost depth (node left right) =
      weightedLeafDepthCost (depth + 1) left +
        weightedLeafDepthCost (depth + 1) right := by
  rfl

@[simp] theorem leafDepthWeights_leaf (depth : ℕ) (x : ℝ) :
    leafDepthWeights depth (leaf x) = [(depth, x)] := by
  rfl

@[simp] theorem leafDepthWeights_node (depth : ℕ)
    (left right : InsertionScheduleTree) :
    leafDepthWeights depth (node left right) =
      leafDepthWeights (depth + 1) left ++
        leafDepthWeights (depth + 1) right := by
  rfl

@[simp] theorem weightedDepthPairsCost_nil :
    weightedDepthPairsCost [] = 0 := by
  rfl

@[simp] theorem weightedDepthPairsCost_cons (pair : ℕ × ℝ)
    (pairs : List (ℕ × ℝ)) :
    weightedDepthPairsCost (pair :: pairs) =
      (pair.1 : ℝ) * pair.2 + weightedDepthPairsCost pairs := by
  rfl

@[simp] theorem weightedDepthPairsCost_append
    (left right : List (ℕ × ℝ)) :
    weightedDepthPairsCost (left ++ right) =
      weightedDepthPairsCost left + weightedDepthPairsCost right := by
  simp [weightedDepthPairsCost, List.map_append, List.sum_append]

/-- The explicit weighted-depth-pair cost is invariant under permutation of the
depth/weight pairs. -/
theorem weightedDepthPairsCost_eq_of_perm
    {left right : List (ℕ × ℝ)}
    (hperm : left.Perm right) :
    weightedDepthPairsCost left = weightedDepthPairsCost right := by
  unfold weightedDepthPairsCost
  exact (hperm.map (fun pair => (pair.1 : ℝ) * pair.2)).sum_eq

/-- If two explicit leaf-depth lists are permutations, the weighted-depth cost
is unchanged and the leaf-weight multiset is preserved.  This is the no-op
branch for exchange arguments. -/
theorem weightedDepthPairsCost_of_perm_le_and_weights_perm
    {pairs swapped : List (ℕ × ℝ)}
    (hperm : swapped.Perm pairs) :
    weightedDepthPairsCost swapped ≤ weightedDepthPairsCost pairs ∧
      (swapped.map Prod.snd).Perm (pairs.map Prod.snd) := by
  constructor
  · rw [weightedDepthPairsCost_eq_of_perm hperm]
  · exact hperm.map Prod.snd

/-- Every explicit leaf-depth list with at least two entries can be permuted
so that the first two entries have the two smallest weights, in nondecreasing
order, and every residual weight is at least the second selected weight. -/
theorem exists_two_smallest_weight_decomposition :
    ∀ pairs : List (ℕ × ℝ),
      2 ≤ pairs.length →
        ∃ first second : ℕ × ℝ, ∃ rest : List (ℕ × ℝ),
          pairs.Perm (first :: second :: rest) ∧
            first.2 ≤ second.2 ∧
              ∀ pair ∈ rest, second.2 ≤ pair.2 := by
  intro pairs
  induction pairs with
  | nil =>
      intro hlen
      simp at hlen
  | cons x xs ih =>
      intro hlen
      cases xs with
      | nil =>
          simp at hlen
      | cons y ys =>
          cases ys with
          | nil =>
              by_cases hxy : x.2 ≤ y.2
              · refine ⟨x, y, [], ?_, hxy, ?_⟩
                · rfl
                · simp
              · refine ⟨y, x, [], ?_, ?_, ?_⟩
                · exact (List.Perm.swap x y []).symm
                · exact le_of_lt (lt_of_not_ge hxy)
                · simp
          | cons z zs =>
              obtain ⟨first, second, rest, hperm, hle, hrest⟩ :=
                ih (by simp)
              by_cases hxf : x.2 ≤ first.2
              · refine ⟨x, first, second :: rest, ?_, hxf, ?_⟩
                · exact List.Perm.cons x hperm
                · intro pair hmem
                  simp at hmem
                  rcases hmem with rfl | hmem
                  · exact hle
                  · exact le_trans hle (hrest pair hmem)
              · have hfirst_x : first.2 ≤ x.2 :=
                  le_of_lt (lt_of_not_ge hxf)
                by_cases hxs : x.2 ≤ second.2
                · refine ⟨first, x, second :: rest, ?_, hfirst_x, ?_⟩
                  · exact (List.Perm.cons x hperm).trans
                      (List.Perm.swap x first (second :: rest)).symm
                  · intro pair hmem
                    simp at hmem
                    rcases hmem with rfl | hmem
                    · exact hxs
                    · exact le_trans hxs (hrest pair hmem)
                · have hsecond_x : second.2 ≤ x.2 :=
                    le_of_lt (lt_of_not_ge hxs)
                  refine ⟨first, second, x :: rest, ?_, hle, ?_⟩
                  · have hmove1 :
                        (x :: y :: z :: zs).Perm
                      (first :: x :: second :: rest) :=
                      (List.Perm.cons x hperm).trans
                        (List.Perm.swap x first (second :: rest)).symm
                    have hmove2 :
                        (first :: x :: second :: rest).Perm
                          (first :: second :: x :: rest) :=
                      List.Perm.cons first (List.Perm.swap x second rest).symm
                    exact hmove1.trans hmove2
                  · intro pair hmem
                    simp at hmem
                    rcases hmem with rfl | hmem
                    · exact hsecond_x
                    · exact hrest pair hmem

/-- Component form of `exists_two_smallest_weight_decomposition`, exposing the
two selected entries as depths and weights. -/
theorem exists_two_smallest_weight_decomposition_components
    (pairs : List (ℕ × ℝ)) (hlen : 2 ≤ pairs.length) :
    ∃ depth₁ : ℕ, ∃ a : ℝ, ∃ depth₂ : ℕ, ∃ b : ℝ,
      ∃ rest : List (ℕ × ℝ),
        pairs.Perm ((depth₁, a) :: (depth₂, b) :: rest) ∧
          a ≤ b ∧
            ∀ pair ∈ rest, b ≤ pair.2 := by
  obtain ⟨first, second, rest, hperm, hle, hrest⟩ :=
    exists_two_smallest_weight_decomposition pairs hlen
  rcases first with ⟨depth₁, a⟩
  rcases second with ⟨depth₂, b⟩
  exact ⟨depth₁, a, depth₂, b, rest, hperm, hle, hrest⟩

/-- Move a member of a list to the front, preserving the remaining elements up
to permutation. -/
private theorem exists_perm_cons_of_mem {α : Type*} [DecidableEq α]
    {x : α} :
    ∀ {xs : List α}, x ∈ xs → ∃ rest : List α, xs.Perm (x :: rest)
  | [], hmem => by
      simp at hmem
  | y :: ys, hmem => by
      simp at hmem
      rcases hmem with rfl | hmem
      · exact ⟨ys, List.Perm.refl (x :: ys)⟩
      · obtain ⟨rest, hperm⟩ := exists_perm_cons_of_mem hmem
        exact ⟨y :: rest,
          (List.Perm.cons y hperm).trans
            (List.Perm.swap y x rest).symm⟩

/-- If the weights of an explicit leaf-depth list permute `a :: b :: rest`,
then the pair list itself can be permuted so that actual entries with weights
`a` and `b` appear first, with residual weights permuting `rest`. -/
theorem exists_pair_decomposition_of_weights_perm_cons_cons
    {pairs : List (ℕ × ℝ)} {a b : ℝ} {restWeights : List ℝ}
    (hweights : (pairs.map Prod.snd).Perm (a :: b :: restWeights)) :
    ∃ depth₁ depth₂ : ℕ, ∃ restPairs : List (ℕ × ℝ),
      pairs.Perm ((depth₁, a) :: (depth₂, b) :: restPairs) ∧
        (restPairs.map Prod.snd).Perm restWeights := by
  classical
  have ha_mem_weights : a ∈ pairs.map Prod.snd :=
    (hweights.mem_iff).2 (by simp)
  rcases List.mem_map.mp ha_mem_weights with ⟨firstPair, hfirst_mem,
    hfirst_snd⟩
  obtain ⟨remainingPairs, hfront⟩ :=
    exists_perm_cons_of_mem (x := firstPair) hfirst_mem
  rcases firstPair with ⟨depth₁, firstWeight⟩
  dsimp at hfirst_snd
  subst firstWeight
  have hfrontWeights :
      (pairs.map Prod.snd).Perm (a :: remainingPairs.map Prod.snd) := by
    simpa [List.map_cons] using hfront.map Prod.snd
  have hremainingWeights :
      (remainingPairs.map Prod.snd).Perm (b :: restWeights) :=
    List.Perm.cons_inv (hfrontWeights.symm.trans hweights)
  have hb_mem_weights : b ∈ remainingPairs.map Prod.snd :=
    (hremainingWeights.mem_iff).2 (by simp)
  rcases List.mem_map.mp hb_mem_weights with ⟨secondPair, hsecond_mem,
    hsecond_snd⟩
  obtain ⟨restPairs, hsecondFront⟩ :=
    exists_perm_cons_of_mem (x := secondPair) hsecond_mem
  rcases secondPair with ⟨depth₂, secondWeight⟩
  dsimp at hsecond_snd
  subst secondWeight
  have hsecondFrontWeights :
      (remainingPairs.map Prod.snd).Perm
        (b :: restPairs.map Prod.snd) := by
    simpa [List.map_cons] using hsecondFront.map Prod.snd
  have hrestWeights :
      (restPairs.map Prod.snd).Perm restWeights :=
    List.Perm.cons_inv (hsecondFrontWeights.symm.trans hremainingWeights)
  exact ⟨depth₁, depth₂, restPairs,
    hfront.trans (List.Perm.cons (depth₁, a) hsecondFront),
    hrestWeights⟩

/-- Exact merge cost is nonnegative for every insertion schedule. -/
theorem exactMergeCost_nonneg (tree : InsertionScheduleTree) :
    0 ≤ tree.exactMergeCost := by
  induction tree with
  | leaf x =>
      simp [exactMergeCost]
  | node left right ihl ihr =>
      exact add_nonneg (add_nonneg ihl ihr) (abs_nonneg _)

/-- Exact real evaluation of a list-shaped schedule is the sum of its leaves. -/
theorem exactEval_eq_leaves_sum (tree : InsertionScheduleTree) :
    tree.exactEval = tree.leaves.sum := by
  induction tree with
  | leaf x =>
      simp [exactEval, leaves]
  | node left right ihl ihr =>
      simp [exactEval, leaves, ihl, ihr]

/-- Exact real evaluation is invariant under permutation of the source leaves. -/
theorem exactEval_eq_of_leaves_perm
    {left right : InsertionScheduleTree}
    (hperm : left.leaves.Perm right.leaves) :
    left.exactEval = right.exactEval := by
  rw [exactEval_eq_leaves_sum left, exactEval_eq_leaves_sum right]
  exact hperm.sum_eq

/-- The second components of the leaf-depth list recover the schedule leaves. -/
theorem leafDepthWeights_weights_eq_leaves
    (depth : ℕ) :
    (tree : InsertionScheduleTree) →
      (leafDepthWeights depth tree).map (fun pair => pair.2) = tree.leaves
  | leaf x => by
      simp [leafDepthWeights, leaves]
  | node left right => by
      simp [leafDepthWeights, leaves,
        leafDepthWeights_weights_eq_leaves (depth + 1) left,
        leafDepthWeights_weights_eq_leaves (depth + 1) right]

/-- A displayed adjacent pair in the explicit leaf-depth list induces the
corresponding displayed adjacent pair in the plain leaf list. -/
theorem leaves_eq_of_leafDepthWeights_pair_display
    {tree : InsertionScheduleTree} {depth pairDepth : ℕ}
    {pre suffix : List (ℕ × ℝ)} {a b : ℝ}
    (hpairs :
      leafDepthWeights depth tree =
        pre ++ [(pairDepth, a), (pairDepth, b)] ++ suffix) :
    tree.leaves = pre.map Prod.snd ++ [a, b] ++ suffix.map Prod.snd := by
  have hweights :=
    congrArg (fun pairs : List (ℕ × ℝ) =>
      pairs.map (fun pair => pair.2)) hpairs
  change (leafDepthWeights depth tree).map (fun pair => pair.2) =
    (pre ++ [(pairDepth, a), (pairDepth, b)] ++ suffix).map
      (fun pair => pair.2) at hweights
  rw [leafDepthWeights_weights_eq_leaves depth tree] at hweights
  simpa [List.map_append] using hweights

/-- A displayed single entry in the explicit leaf-depth list induces the
corresponding displayed single entry in the plain leaf list. -/
theorem leaves_eq_of_leafDepthWeights_single_display
    {tree : InsertionScheduleTree} {depth pairDepth : ℕ}
    {pre suffix : List (ℕ × ℝ)} {a : ℝ}
    (hpairs :
      leafDepthWeights depth tree =
        pre ++ [(pairDepth, a)] ++ suffix) :
    tree.leaves = pre.map Prod.snd ++ [a] ++ suffix.map Prod.snd := by
  have hweights :=
    congrArg (fun pairs : List (ℕ × ℝ) =>
      pairs.map (fun pair => pair.2)) hpairs
  change (leafDepthWeights depth tree).map (fun pair => pair.2) =
    (pre ++ [(pairDepth, a)] ++ suffix).map (fun pair => pair.2) at hweights
  rw [leafDepthWeights_weights_eq_leaves depth tree] at hweights
  simpa [List.map_append] using hweights

/-- The leaf-depth list has one entry for each schedule leaf. -/
theorem leafDepthWeights_length
    (depth : ℕ) (tree : InsertionScheduleTree) :
    (leafDepthWeights depth tree).length = tree.leafCount := by
  induction tree generalizing depth with
  | leaf x =>
      simp [leafDepthWeights, leafCount]
  | node left right ihl ihr =>
      simp [leafDepthWeights, leafCount, ihl (depth + 1), ihr (depth + 1)]

private theorem list_zip_map_fst_snd {α β : Type*} :
    ∀ pairs : List (α × β),
      (pairs.map Prod.fst).zip (pairs.map Prod.snd) = pairs
  | [] => by
      simp
  | pair :: pairs => by
      cases pair
      simp [list_zip_map_fst_snd pairs]

/-- Same-shape relabeling has the requested leaves when the supplied weight
list has the original leaf count. -/
theorem relabelLeaves_leaves_eq
    (tree : InsertionScheduleTree) (weights : List ℝ)
    (hlen : weights.length = tree.leafCount) :
    (relabelLeaves tree weights).leaves = weights := by
  induction tree generalizing weights with
  | leaf x =>
      cases weights with
      | nil =>
          simp [leafCount] at hlen
      | cons w ws =>
          cases ws with
          | nil =>
              simp [relabelLeaves]
          | cons w₂ ws =>
              simp [leafCount] at hlen
  | node left right ihl ihr =>
      have htake :
          (weights.take left.leafCount).length = left.leafCount := by
        rw [List.length_take, hlen, leafCount]
        exact Nat.min_eq_left
          (Nat.le_add_right left.leafCount right.leafCount)
      have hdrop :
          (weights.drop left.leafCount).length = right.leafCount := by
        rw [List.length_drop, hlen, leafCount,
          Nat.add_sub_cancel_left left.leafCount right.leafCount]
      simp [relabelLeaves, ihl _ htake, ihr _ hdrop,
        List.take_append_drop left.leafCount weights]

/-- Same-shape relabeling keeps the original depth sequence and replaces only
the leaf weights. -/
theorem relabelLeaves_leafDepthWeights_eq_zip
    (depth : ℕ) (tree : InsertionScheduleTree) (weights : List ℝ)
    (hlen : weights.length = tree.leafCount) :
    leafDepthWeights depth (relabelLeaves tree weights) =
      ((leafDepthWeights depth tree).map Prod.fst).zip weights := by
  induction tree generalizing depth weights with
  | leaf x =>
      cases weights with
      | nil =>
          simp [leafCount] at hlen
      | cons w ws =>
          cases ws with
          | nil =>
              simp [relabelLeaves, leafDepthWeights]
          | cons w₂ ws =>
              simp [leafCount] at hlen
  | node left right ihl ihr =>
      have htake :
          (weights.take left.leafCount).length = left.leafCount := by
        rw [List.length_take, hlen, leafCount]
        exact Nat.min_eq_left
          (Nat.le_add_right left.leafCount right.leafCount)
      have hdrop :
          (weights.drop left.leafCount).length = right.leafCount := by
        rw [List.length_drop, hlen, leafCount,
          Nat.add_sub_cancel_left left.leafCount right.leafCount]
      have hziplen :
          ((leafDepthWeights (depth + 1) left).map Prod.fst).length =
            (weights.take left.leafCount).length := by
        rw [List.length_map, leafDepthWeights_length, htake]
      rw [relabelLeaves, leafDepthWeights_node,
        ihl (depth + 1) _ htake, ihr (depth + 1) _ hdrop,
        leafDepthWeights_node, List.map_append]
      rw [← List.zip_append hziplen]
      simp [List.take_append_drop left.leafCount weights]

/-- Concrete same-shape realization of an explicit leaf-depth/weight list: if
the target pair list has the same depth sequence as `tree`, then relabeling
`tree` by the target weights realizes that exact pair list. -/
theorem relabelLeaves_leafDepthWeights_eq_pairs_of_depths_eq
    (depth : ℕ) (tree : InsertionScheduleTree)
    (pairs : List (ℕ × ℝ))
    (hdepths :
      pairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst) :
    leafDepthWeights depth (relabelLeaves tree (pairs.map Prod.snd)) =
      pairs := by
  have hlenPairs : pairs.length = tree.leafCount := by
    have hlenDepths := congrArg List.length hdepths
    simpa [List.length_map, leafDepthWeights_length] using hlenDepths
  have hlen : (pairs.map Prod.snd).length = tree.leafCount := by
    simpa [List.length_map] using hlenPairs
  rw [relabelLeaves_leafDepthWeights_eq_zip depth tree (pairs.map Prod.snd)
    hlen]
  simpa [hdepths] using list_zip_map_fst_snd pairs

/-- Concrete same-shape relabeling has exactly the requested target weights
when the target pair list preserves the original depth sequence. -/
theorem relabelLeaves_leaves_eq_pairs_of_depths_eq
    (depth : ℕ) (tree : InsertionScheduleTree)
    (pairs : List (ℕ × ℝ))
    (hdepths :
      pairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst) :
    (relabelLeaves tree (pairs.map Prod.snd)).leaves =
      pairs.map Prod.snd := by
  have hlenPairs : pairs.length = tree.leafCount := by
    have hlenDepths := congrArg List.length hdepths
    simpa [List.length_map, leafDepthWeights_length] using hlenDepths
  have hlen : (pairs.map Prod.snd).length = tree.leafCount := by
    simpa [List.length_map] using hlenPairs
  exact relabelLeaves_leaves_eq tree (pairs.map Prod.snd) hlen

/-- If a target explicit leaf-depth/weight list has the same depth sequence as
a tree, then it is realized by relabeling that tree's leaves. -/
theorem exists_relabelLeaves_leafDepthWeights_eq_of_depths_eq
    (depth : ℕ) (tree : InsertionScheduleTree)
    (pairs : List (ℕ × ℝ))
    (hdepths :
      pairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst) :
    ∃ relabeledTree : InsertionScheduleTree,
      leafDepthWeights depth relabeledTree = pairs ∧
        relabeledTree.leaves = pairs.map Prod.snd := by
  exact ⟨relabelLeaves tree (pairs.map Prod.snd),
    relabelLeaves_leafDepthWeights_eq_pairs_of_depths_eq depth tree pairs
      hdepths,
    relabelLeaves_leaves_eq_pairs_of_depths_eq depth tree pairs hdepths⟩

/-- The starting depth is always bounded by the maximum leaf depth. -/
theorem depth_le_maxLeafDepth
    (depth : ℕ) :
    (tree : InsertionScheduleTree) →
      depth ≤ maxLeafDepth depth tree
  | leaf x => by
      simp [maxLeafDepth]
  | node left right => by
      have hleft :
          depth + 1 ≤ maxLeafDepth (depth + 1) left :=
        depth_le_maxLeafDepth (depth + 1) left
      have hdepth_left : depth ≤ maxLeafDepth (depth + 1) left :=
        Nat.le_trans (Nat.le_succ depth) hleft
      exact Nat.le_trans hdepth_left
        (Nat.le_max_left
          (maxLeafDepth (depth + 1) left)
          (maxLeafDepth (depth + 1) right))

/-- A non-leaf schedule has some leaf strictly below the supplied root depth,
so the maximum leaf depth is at least `depth + 1`. -/
theorem succ_depth_le_maxLeafDepth_of_one_lt_leafCount
    (depth : ℕ) :
    (tree : InsertionScheduleTree) →
      1 < tree.leafCount → depth + 1 ≤ maxLeafDepth depth tree
  | leaf x, hcount => by
      simp [leafCount] at hcount
  | node left right, _hcount => by
      have hleft :
          depth + 1 ≤ maxLeafDepth (depth + 1) left :=
        depth_le_maxLeafDepth (depth + 1) left
      exact Nat.le_trans hleft
        (Nat.le_max_left
          (maxLeafDepth (depth + 1) left)
          (maxLeafDepth (depth + 1) right))

/-- Every entry in the explicit leaf-depth list is bounded by the schedule's
maximum leaf depth. -/
theorem leafDepthWeights_depth_le_maxLeafDepth
    (depth : ℕ) :
    (tree : InsertionScheduleTree) →
      ∀ pair ∈ leafDepthWeights depth tree,
        pair.1 ≤ maxLeafDepth depth tree
  | leaf x => by
      intro pair hmem
      simp [leafDepthWeights] at hmem
      rcases hmem with rfl
      rfl
  | node left right => by
      intro pair hmem
      simp [leafDepthWeights] at hmem
      rcases hmem with hleft | hright
      · have hpair :=
          leafDepthWeights_depth_le_maxLeafDepth (depth + 1) left
            pair hleft
        exact Nat.le_trans hpair
          (by
            simp [maxLeafDepth])
      · have hpair :=
          leafDepthWeights_depth_le_maxLeafDepth (depth + 1) right
            pair hright
        exact Nat.le_trans hpair
          (by
            simp [maxLeafDepth])

/-- If a deepest sibling context is displayed at `parentDepth + 1`, then any
two selected entries in the leaf-depth list have depths no larger than that
displayed deepest depth. -/
theorem two_smallest_depths_le_deepest_parent_context
    {tree : InsertionScheduleTree} {depth parentDepth : ℕ}
    {rest : List (ℕ × ℝ)} {a b : ℝ} {shallow₁ shallow₂ : ℕ}
    (hparent : parentDepth + 1 = maxLeafDepth depth tree)
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((shallow₁, a) :: (shallow₂, b) :: rest)) :
    shallow₁ ≤ parentDepth + 1 ∧ shallow₂ ≤ parentDepth + 1 := by
  have hfirst_mem : (shallow₁, a) ∈ leafDepthWeights depth tree :=
    (htwoSmallest.mem_iff).2 (by simp)
  have hsecond_mem : (shallow₂, b) ∈ leafDepthWeights depth tree :=
    (htwoSmallest.mem_iff).2 (by simp)
  have hdepth₁ :=
    leafDepthWeights_depth_le_maxLeafDepth depth tree
      (shallow₁, a) hfirst_mem
  have hdepth₂ :=
    leafDepthWeights_depth_le_maxLeafDepth depth tree
      (shallow₂, b) hsecond_mem
  rw [← hparent] at hdepth₁ hdepth₂
  exact ⟨hdepth₁, hdepth₂⟩

/-- Every non-leaf schedule has a sibling pair of leaves at maximum depth,
appearing as adjacent entries in the explicit leaf-depth/weight list. -/
theorem exists_deepest_sibling_leaf_pair
    (depth : ℕ) :
    (tree : InsertionScheduleTree) →
      1 < tree.leafCount →
        ∃ pre suffix : List (ℕ × ℝ), ∃ a b : ℝ,
          leafDepthWeights depth tree =
            pre ++
              [(maxLeafDepth depth tree, a),
                (maxLeafDepth depth tree, b)] ++
              suffix := by
  intro tree
  induction tree generalizing depth with
  | leaf x =>
      intro hcount
      simp [leafCount] at hcount
  | node left right ihl ihr =>
      intro _hcount
      cases left with
      | leaf x =>
          cases right with
          | leaf y =>
              refine ⟨[], [], x, y, ?_⟩
              simp [leafDepthWeights, maxLeafDepth]
          | node rightLeft rightRight =>
              obtain ⟨pre, suffix, a, b, hpair⟩ :=
                ihr (depth + 1)
                  (one_lt_leafCount_node rightLeft rightRight)
              have hmax :
                  maxLeafDepth depth
                      (node (leaf x) (node rightLeft rightRight)) =
                    maxLeafDepth (depth + 1)
                      (node rightLeft rightRight) := by
                change
                  max (depth + 1)
                      (maxLeafDepth (depth + 1)
                        (node rightLeft rightRight)) =
                    maxLeafDepth (depth + 1)
                      (node rightLeft rightRight)
                exact Nat.max_eq_right
                  (depth_le_maxLeafDepth (depth + 1)
                    (node rightLeft rightRight))
              refine ⟨[(depth + 1, x)] ++ pre, suffix, a, b, ?_⟩
              have hpair' :=
                congrArg (fun pairs => [(depth + 1, x)] ++ pairs) hpair
              simpa [leafDepthWeights, hmax, List.append_assoc] using hpair'
      | node leftLeft leftRight =>
          cases right with
          | leaf y =>
              obtain ⟨pre, suffix, a, b, hpair⟩ :=
                ihl (depth + 1)
                  (one_lt_leafCount_node leftLeft leftRight)
              have hmax :
                  maxLeafDepth depth
                      (node (node leftLeft leftRight) (leaf y)) =
                    maxLeafDepth (depth + 1)
                      (node leftLeft leftRight) := by
                change
                  max (maxLeafDepth (depth + 1)
                        (node leftLeft leftRight))
                      (depth + 1) =
                    maxLeafDepth (depth + 1)
                      (node leftLeft leftRight)
                exact Nat.max_eq_left
                  (depth_le_maxLeafDepth (depth + 1)
                    (node leftLeft leftRight))
              refine ⟨pre, suffix ++ [(depth + 1, y)], a, b, ?_⟩
              have hpair' :=
                congrArg (fun pairs => pairs ++ [(depth + 1, y)]) hpair
              simpa [leafDepthWeights, hmax, List.append_assoc] using hpair'
          | node rightLeft rightRight =>
              let leftTree := node leftLeft leftRight
              let rightTree := node rightLeft rightRight
              let leftMax := maxLeafDepth (depth + 1) leftTree
              let rightMax := maxLeafDepth (depth + 1) rightTree
              by_cases hle : rightMax ≤ leftMax
              · obtain ⟨pre, suffix, a, b, hpair⟩ :=
                  ihl (depth + 1)
                    (one_lt_leafCount_node leftLeft leftRight)
                have hmax :
                    maxLeafDepth depth (node leftTree rightTree) =
                      leftMax := by
                  change max leftMax rightMax = leftMax
                  exact Nat.max_eq_left hle
                refine ⟨pre,
                  suffix ++ leafDepthWeights (depth + 1) rightTree,
                  a, b, ?_⟩
                have hpair' :=
                  congrArg
                    (fun pairs =>
                      pairs ++ leafDepthWeights (depth + 1) rightTree)
                    hpair
                simpa [leafDepthWeights, hmax, leftTree, rightTree,
                  leftMax, List.append_assoc] using hpair'
              · have hleft_le_right : leftMax ≤ rightMax :=
                  Nat.le_of_lt (Nat.lt_of_not_ge hle)
                obtain ⟨pre, suffix, a, b, hpair⟩ :=
                  ihr (depth + 1)
                    (one_lt_leafCount_node rightLeft rightRight)
                have hmax :
                    maxLeafDepth depth (node leftTree rightTree) =
                      rightMax := by
                  change max leftMax rightMax = rightMax
                  exact Nat.max_eq_right hleft_le_right
                refine ⟨leafDepthWeights (depth + 1) leftTree ++ pre,
                  suffix, a, b, ?_⟩
                have hpair' :=
                  congrArg
                    (fun pairs =>
                      leafDepthWeights (depth + 1) leftTree ++ pairs)
                    hpair
                simpa [leafDepthWeights, hmax, leftTree, rightTree,
                  rightMax, List.append_assoc] using hpair'

/-- Weighted external path length is exactly the explicit weighted sum over the
schedule's `(depth, weight)` leaf list. -/
theorem weightedLeafDepthCost_eq_weightedDepthPairsCost
    (depth : ℕ) :
    (tree : InsertionScheduleTree) →
      weightedLeafDepthCost depth tree =
        weightedDepthPairsCost (leafDepthWeights depth tree)
  | leaf x => by
      simp [weightedLeafDepthCost, leafDepthWeights, weightedDepthPairsCost]
  | node left right => by
      simp [weightedLeafDepthCost, leafDepthWeights,
        weightedLeafDepthCost_eq_weightedDepthPairsCost (depth + 1) left,
        weightedLeafDepthCost_eq_weightedDepthPairsCost (depth + 1) right]

/-- Weighted external path length is invariant under permutation of the explicit
leaf-depth/weight pairs. -/
theorem weightedLeafDepthCost_eq_of_leafDepthWeights_perm
    {left right : InsertionScheduleTree} {depth : ℕ}
    (hperm :
      (leafDepthWeights depth left).Perm (leafDepthWeights depth right)) :
    weightedLeafDepthCost depth left = weightedLeafDepthCost depth right := by
  rw [weightedLeafDepthCost_eq_weightedDepthPairsCost depth left,
    weightedLeafDepthCost_eq_weightedDepthPairsCost depth right]
  exact weightedDepthPairsCost_eq_of_perm hperm

/-- Increasing the starting depth by one adds exactly one copy of every leaf's
exact value to the weighted external path length. -/
theorem weightedLeafDepthCost_succ_eq_add_exactEval
    (depth : ℕ) :
    (tree : InsertionScheduleTree) →
      weightedLeafDepthCost (depth + 1) tree =
        weightedLeafDepthCost depth tree + tree.exactEval
  | leaf x => by
      simp [weightedLeafDepthCost, exactEval]
      ring
  | node left right => by
      simp [weightedLeafDepthCost, exactEval,
        weightedLeafDepthCost_succ_eq_add_exactEval (depth + 1) left,
        weightedLeafDepthCost_succ_eq_add_exactEval (depth + 1) right]
      ring

/-- Expanding a node at depth `depth` is the same as keeping its two children at
that depth and adding one copy of the exact value of each child. -/
theorem weightedLeafDepthCost_node_eq_children_at_depth_add_exactEval
    (depth : ℕ) (left right : InsertionScheduleTree) :
    weightedLeafDepthCost depth (node left right) =
      weightedLeafDepthCost depth left + weightedLeafDepthCost depth right +
        (left.exactEval + right.exactEval) := by
  simp [weightedLeafDepthCost,
    weightedLeafDepthCost_succ_eq_add_exactEval depth left,
    weightedLeafDepthCost_succ_eq_add_exactEval depth right]
  ring

/-- Contracting two sibling leaves at depth `depth + 1` into their parent leaf
at depth `depth` lowers weighted external path length by exactly their merged
weight. -/
theorem weightedLeafDepthCost_node_leaf_leaf_eq_contract
    (depth : ℕ) (a b : ℝ) :
    weightedLeafDepthCost depth (node (leaf a) (leaf b)) =
      weightedLeafDepthCost depth (leaf (a + b)) + (a + b) := by
  simp [weightedLeafDepthCost]
  ring

/-- Explicit pair-list form of sibling contraction: replacing two sibling
leaves at depth `depth + 1` by their contracted parent at depth `depth`
removes exactly one copy of the merged weight from the weighted-depth cost. -/
theorem weightedDepthPairsCost_pair_contract_eq
    (pre suffix : List (ℕ × ℝ)) (depth : ℕ) (a b : ℝ) :
    weightedDepthPairsCost
        (pre ++ [(depth + 1, a), (depth + 1, b)] ++ suffix) =
      weightedDepthPairsCost
        (pre ++ [(depth, a + b)] ++ suffix) + (a + b) := by
  simp [weightedDepthPairsCost]
  ring

/-- Structural contraction of one sibling leaf pair into its parent leaf.  This
is the tree-level relation needed by the Huffman-style induction behind the
printed p. 83 insertion-optimality claim. -/
inductive SiblingLeafContract :
    InsertionScheduleTree → InsertionScheduleTree → ℝ → ℝ → Prop
  | here (a b : ℝ) :
      SiblingLeafContract (node (leaf a) (leaf b)) (leaf (a + b)) a b
  | inLeft {left contractedLeft right : InsertionScheduleTree} {a b : ℝ}
      (hcontract : SiblingLeafContract left contractedLeft a b) :
      SiblingLeafContract (node left right) (node contractedLeft right) a b
  | inRight {left right contractedRight : InsertionScheduleTree} {a b : ℝ}
      (hcontract : SiblingLeafContract right contractedRight a b) :
      SiblingLeafContract (node left right) (node left contractedRight) a b

namespace SiblingLeafContract

/-- Contracting a sibling leaf pair preserves exact evaluation. -/
theorem exactEval_eq
    {tree contracted : InsertionScheduleTree} {a b : ℝ}
    (hcontract : SiblingLeafContract tree contracted a b) :
    contracted.exactEval = tree.exactEval := by
  induction hcontract with
  | here a b =>
      simp [exactEval]
  | inLeft hcontract ih =>
      simp [exactEval, ih]
  | inRight hcontract ih =>
      simp [exactEval, ih]

/-- Contracting a sibling leaf pair removes exactly one leaf. -/
theorem leafCount_eq_succ
    {tree contracted : InsertionScheduleTree} {a b : ℝ}
    (hcontract : SiblingLeafContract tree contracted a b) :
    tree.leafCount = contracted.leafCount + 1 := by
  induction hcontract with
  | here a b =>
      simp [leafCount]
  | inLeft hcontract ih =>
      simp [leafCount, ih]
      omega
  | inRight hcontract ih =>
      simp [leafCount, ih]
      omega

/-- Contracting a sibling leaf pair strictly decreases the leaf count. -/
theorem contracted_leafCount_lt
    {tree contracted : InsertionScheduleTree} {a b : ℝ}
    (hcontract : SiblingLeafContract tree contracted a b) :
    contracted.leafCount < tree.leafCount := by
  rw [leafCount_eq_succ hcontract]
  exact Nat.lt_succ_self contracted.leafCount

/-- The leaves of a contracted tree are obtained by replacing one adjacent
`a, b` leaf pair by the single parent weight `a + b`. -/
theorem exists_leaves_context
    {tree contracted : InsertionScheduleTree} {a b : ℝ}
    (hcontract : SiblingLeafContract tree contracted a b) :
    ∃ pre suffix : List ℝ,
      tree.leaves = pre ++ [a, b] ++ suffix ∧
        contracted.leaves = pre ++ [a + b] ++ suffix := by
  induction hcontract with
  | here a b =>
      exact ⟨[], [], by simp [leaves]⟩
  | inLeft hcontract ih =>
      rename_i _ _ rightTree _ _
      obtain ⟨pre, suffix, htree, hcontracted⟩ := ih
      refine ⟨pre, suffix ++ rightTree.leaves, ?_, ?_⟩
      · rw [leaves_node, htree]
        simp [List.append_assoc]
      · rw [leaves_node, hcontracted]
        simp [List.append_assoc]
  | inRight hcontract ih =>
      rename_i leftTree _ _ _ _
      obtain ⟨pre, suffix, htree, hcontracted⟩ := ih
      refine ⟨leftTree.leaves ++ pre, suffix, ?_, ?_⟩
      · rw [leaves_node, htree]
        simp [List.append_assoc]
      · rw [leaves_node, hcontracted]
        simp [List.append_assoc]

/-- The explicit leaf-depth lists of a structural sibling contraction differ
by replacing two sibling leaves at `parentDepth + 1` with their parent leaf at
`parentDepth`. -/
theorem exists_leafDepthWeights_context
    {tree contracted : InsertionScheduleTree} {a b : ℝ} (depth : ℕ)
    (hcontract : SiblingLeafContract tree contracted a b) :
    ∃ parentDepth : ℕ, ∃ pre suffix : List (ℕ × ℝ),
      leafDepthWeights depth tree =
        pre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++ suffix ∧
        leafDepthWeights depth contracted =
          pre ++ [(parentDepth, a + b)] ++ suffix := by
  induction hcontract generalizing depth with
  | here a b =>
      exact ⟨depth, [], [], by simp [leafDepthWeights]⟩
  | inLeft hcontract ih =>
      rename_i _ _ rightTree _ _
      obtain ⟨parentDepth, pre, suffix, htree, hcontracted⟩ :=
        ih (depth + 1)
      refine ⟨parentDepth, pre,
        suffix ++ leafDepthWeights (depth + 1) rightTree, ?_, ?_⟩
      · rw [leafDepthWeights_node, htree]
        simp [List.append_assoc]
      · rw [leafDepthWeights_node, hcontracted]
        simp [List.append_assoc]
  | inRight hcontract ih =>
      rename_i leftTree _ _ _ _
      obtain ⟨parentDepth, pre, suffix, htree, hcontracted⟩ :=
        ih (depth + 1)
      refine ⟨parentDepth, leafDepthWeights (depth + 1) leftTree ++ pre,
        suffix, ?_, ?_⟩
      · rw [leafDepthWeights_node, htree]
        simp [List.append_assoc]
      · rw [leafDepthWeights_node, hcontracted]
        simp [List.append_assoc]

/-- Combined explicit-depth and plain-leaf context for a structural sibling
contraction.  The same `pre` and `suffix` describe both the leaf-depth display
and the plain leaf-list display, avoiding any ambiguity from repeated weights. -/
theorem exists_leafDepthWeights_and_leaves_context
    {tree contracted : InsertionScheduleTree} {a b : ℝ} (depth : ℕ)
    (hcontract : SiblingLeafContract tree contracted a b) :
    ∃ parentDepth : ℕ, ∃ pre suffix : List (ℕ × ℝ),
      leafDepthWeights depth tree =
        pre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++ suffix ∧
        leafDepthWeights depth contracted =
          pre ++ [(parentDepth, a + b)] ++ suffix ∧
          tree.leaves = pre.map Prod.snd ++ [a, b] ++ suffix.map Prod.snd ∧
            contracted.leaves =
              pre.map Prod.snd ++ [a + b] ++ suffix.map Prod.snd := by
  obtain ⟨parentDepth, pre, suffix, htree, hcontracted⟩ :=
    exists_leafDepthWeights_context depth hcontract
  refine ⟨parentDepth, pre, suffix, htree, hcontracted, ?_, ?_⟩
  · exact leaves_eq_of_leafDepthWeights_pair_display htree
  · exact leaves_eq_of_leafDepthWeights_single_display hcontracted

private theorem list_take_append_context {α : Type*}
    (pre middle suffix tail : List α) :
    (pre ++ middle ++ suffix ++ tail).take
        (pre.length + middle.length + suffix.length) =
      pre ++ middle ++ suffix := by
  have hsplit :
      pre ++ middle ++ suffix ++ tail =
        (pre ++ middle ++ suffix) ++ tail := by
    simp [List.append_assoc]
  rw [hsplit]
  rw [List.take_append_of_le_length
    (by simp [List.length_append, Nat.add_assoc])]
  simp [List.length_append, Nat.add_assoc]

private theorem list_drop_append_context {α : Type*}
    (pre middle suffix tail : List α) :
    (pre ++ middle ++ suffix ++ tail).drop
        (pre.length + middle.length + suffix.length) =
      tail := by
  have hsplit :
      pre ++ middle ++ suffix ++ tail =
        (pre ++ middle ++ suffix) ++ tail := by
    simp [List.append_assoc]
  rw [hsplit]
  rw [List.drop_append_of_le_length
    (by simp [List.length_append, Nat.add_assoc])]
  simp [Nat.add_assoc]

/-- Branch-ready form of `exists_leafDepthWeights_and_leaves_context`: the
same explicit leaf-depth `pre`/`suffix` context also controls same-shape
relabeling.  Replacing the two contracted slots by any new weights `a, b`, and
the contracted slot by `a + b`, preserves the structural contraction. -/
theorem exists_leafDepthWeights_context_with_relabel_contract
    {tree contracted : InsertionScheduleTree} {oldA oldB : ℝ} (depth : ℕ)
    (hcontract : SiblingLeafContract tree contracted oldA oldB) :
    ∃ parentDepth : ℕ, ∃ pre suffix : List (ℕ × ℝ),
      leafDepthWeights depth tree =
        pre ++ [(parentDepth + 1, oldA), (parentDepth + 1, oldB)] ++
          suffix ∧
        leafDepthWeights depth contracted =
          pre ++ [(parentDepth, oldA + oldB)] ++ suffix ∧
          tree.leaves =
            pre.map Prod.snd ++ [oldA, oldB] ++ suffix.map Prod.snd ∧
            contracted.leaves =
              pre.map Prod.snd ++ [oldA + oldB] ++ suffix.map Prod.snd ∧
              ∀ {newPre newSuffix : List (ℕ × ℝ)} {a b : ℝ},
                newPre.length = pre.length →
                newSuffix.length = suffix.length →
                SiblingLeafContract
                  (relabelLeaves tree
                    (newPre.map Prod.snd ++ [a, b] ++
                      newSuffix.map Prod.snd))
                  (relabelLeaves contracted
                    (newPre.map Prod.snd ++ [a + b] ++
                      newSuffix.map Prod.snd))
                  a b := by
  induction hcontract generalizing depth with
  | here oldA oldB =>
      refine ⟨depth, [], [], by simp [leafDepthWeights],
        by simp [leafDepthWeights], by simp [leaves], by simp [leaves],
        ?_⟩
      intro newPre newSuffix a b hpre hsuffix
      have hpre_nil : newPre = [] := List.length_eq_zero_iff.mp hpre
      have hsuffix_nil : newSuffix = [] :=
        List.length_eq_zero_iff.mp hsuffix
      subst newPre
      subst newSuffix
      simp [relabelLeaves]
      exact SiblingLeafContract.here a b
  | inLeft hcontract ih =>
      rename_i left contractedLeft right oldA oldB
      obtain ⟨parentDepth, pre, suffix, hleftDepth,
        hcontractedLeftDepth, hleftLeaves, hcontractedLeftLeaves,
        hrelabeled⟩ := ih (depth + 1)
      let rightPairs := leafDepthWeights (depth + 1) right
      refine ⟨parentDepth, pre, suffix ++ rightPairs, ?_, ?_, ?_, ?_,
        ?_⟩
      · rw [leafDepthWeights_node, hleftDepth]
        simp [rightPairs, List.append_assoc]
      · rw [leafDepthWeights_node, hcontractedLeftDepth]
        simp [rightPairs, List.append_assoc]
      · rw [leaves_node, hleftLeaves]
        simp [rightPairs, leafDepthWeights_weights_eq_leaves,
          List.map_append, List.append_assoc]
      · rw [leaves_node, hcontractedLeftLeaves]
        simp [rightPairs, leafDepthWeights_weights_eq_leaves,
          List.map_append, List.append_assoc]
      · intro newPre newSuffix a b hpre hsuffix
        let newLeftSuffix := newSuffix.take suffix.length
        let newRightPairs := newSuffix.drop suffix.length
        have hsuffix_split :
            newSuffix = newLeftSuffix ++ newRightPairs := by
          simp [newLeftSuffix, newRightPairs, List.take_append_drop]
        have hleftSuffixLen : newLeftSuffix.length = suffix.length := by
          change (newSuffix.take suffix.length).length = suffix.length
          rw [List.length_take]
          have hle : suffix.length ≤ newSuffix.length := by
            rw [hsuffix, List.length_append]
            simp [rightPairs, leafDepthWeights_length]
          exact Nat.min_eq_left hle
        have hrightPairsLen : newRightPairs.length = right.leafCount := by
          change (newSuffix.drop suffix.length).length = right.leafCount
          rw [List.length_drop, hsuffix, List.length_append]
          simp [rightPairs, leafDepthWeights_length]
        have hleftCount :
            left.leafCount =
              (newPre.map Prod.snd).length + [a, b].length +
                (newLeftSuffix.map Prod.snd).length := by
          have hlen := congrArg List.length hleftLeaves
          rw [leaves_length] at hlen
          simp [List.length_append] at hlen
          simp [List.length_map, hpre, hleftSuffixLen]
          omega
        have hcontractedLeftCount :
            contractedLeft.leafCount =
              (newPre.map Prod.snd).length + [a + b].length +
                (newLeftSuffix.map Prod.snd).length := by
          have hlen := congrArg List.length hcontractedLeftLeaves
          rw [leaves_length] at hlen
          simp [List.length_append] at hlen
          simp [List.length_map, hpre, hleftSuffixLen]
          omega
        have hsuffixMap :
            newSuffix.map Prod.snd =
              newLeftSuffix.map Prod.snd ++ newRightPairs.map Prod.snd := by
          rw [hsuffix_split]
          simp [List.map_append]
        have htakeTree :
            (newPre.map Prod.snd ++ [a, b] ++
                newSuffix.map Prod.snd).take left.leafCount =
              newPre.map Prod.snd ++ [a, b] ++
                newLeftSuffix.map Prod.snd := by
          rw [hleftCount, hsuffixMap]
          simpa [List.append_assoc] using
            list_take_append_context (newPre.map Prod.snd) [a, b]
              (newLeftSuffix.map Prod.snd) (newRightPairs.map Prod.snd)
        have hdropTree :
            (newPre.map Prod.snd ++ [a, b] ++
                newSuffix.map Prod.snd).drop left.leafCount =
              newRightPairs.map Prod.snd := by
          rw [hleftCount, hsuffixMap]
          simpa [List.append_assoc] using
            list_drop_append_context (newPre.map Prod.snd) [a, b]
              (newLeftSuffix.map Prod.snd) (newRightPairs.map Prod.snd)
        have htakeContracted :
            (newPre.map Prod.snd ++ [a + b] ++
                newSuffix.map Prod.snd).take contractedLeft.leafCount =
              newPre.map Prod.snd ++ [a + b] ++
                newLeftSuffix.map Prod.snd := by
          rw [hcontractedLeftCount, hsuffixMap]
          simpa [List.append_assoc] using
            list_take_append_context (newPre.map Prod.snd) [a + b]
              (newLeftSuffix.map Prod.snd) (newRightPairs.map Prod.snd)
        have hdropContracted :
            (newPre.map Prod.snd ++ [a + b] ++
                newSuffix.map Prod.snd).drop contractedLeft.leafCount =
              newRightPairs.map Prod.snd := by
          rw [hcontractedLeftCount, hsuffixMap]
          simpa [List.append_assoc] using
            list_drop_append_context (newPre.map Prod.snd) [a + b]
              (newLeftSuffix.map Prod.snd) (newRightPairs.map Prod.snd)
        rw [relabelLeaves, relabelLeaves, htakeTree, hdropTree,
          htakeContracted, hdropContracted]
        exact SiblingLeafContract.inLeft
          (hrelabeled hpre hleftSuffixLen)
  | inRight hcontract ih =>
      rename_i left right contractedRight oldA oldB
      obtain ⟨parentDepth, pre, suffix, hrightDepth,
        hcontractedRightDepth, hrightLeaves, hcontractedRightLeaves,
        hrelabeled⟩ := ih (depth + 1)
      let leftPairs := leafDepthWeights (depth + 1) left
      refine ⟨parentDepth, leftPairs ++ pre, suffix, ?_, ?_, ?_, ?_,
        ?_⟩
      · rw [leafDepthWeights_node, hrightDepth]
        simp [leftPairs, List.append_assoc]
      · rw [leafDepthWeights_node, hcontractedRightDepth]
        simp [leftPairs, List.append_assoc]
      · rw [leaves_node, hrightLeaves]
        simp [leftPairs, leafDepthWeights_weights_eq_leaves,
          List.map_append, List.append_assoc]
      · rw [leaves_node, hcontractedRightLeaves]
        simp [leftPairs, leafDepthWeights_weights_eq_leaves,
          List.map_append, List.append_assoc]
      · intro newPre newSuffix a b hpre hsuffix
        let newLeftPairs := newPre.take leftPairs.length
        let newRightPre := newPre.drop leftPairs.length
        have hpre_split :
            newPre = newLeftPairs ++ newRightPre := by
          simp [newLeftPairs, newRightPre, List.take_append_drop]
        have hleftPairsLen : newLeftPairs.length = leftPairs.length := by
          change (newPre.take leftPairs.length).length = leftPairs.length
          rw [List.length_take]
          have hle : leftPairs.length ≤ newPre.length := by
            rw [hpre, List.length_append]
            exact Nat.le_add_right leftPairs.length pre.length
          exact Nat.min_eq_left hle
        have hrightPreLen : newRightPre.length = pre.length := by
          change (newPre.drop leftPairs.length).length = pre.length
          rw [List.length_drop, hpre, List.length_append]
          exact Nat.add_sub_cancel_left leftPairs.length pre.length
        have hleftWeightsLen :
            (newLeftPairs.map Prod.snd).length = left.leafCount := by
          rw [List.length_map, hleftPairsLen]
          simp [leftPairs, leafDepthWeights_length]
        have hpreMap :
            newPre.map Prod.snd =
              newLeftPairs.map Prod.snd ++ newRightPre.map Prod.snd := by
          rw [hpre_split]
          simp [List.map_append]
        have htreeWeights :
            newPre.map Prod.snd ++ [a, b] ++ newSuffix.map Prod.snd =
              newLeftPairs.map Prod.snd ++
                (newRightPre.map Prod.snd ++ [a, b] ++
                  newSuffix.map Prod.snd) := by
          rw [hpreMap]
          simp [List.append_assoc]
        have hcontractedWeights :
            newPre.map Prod.snd ++ [a + b] ++ newSuffix.map Prod.snd =
              newLeftPairs.map Prod.snd ++
                (newRightPre.map Prod.snd ++ [a + b] ++
                  newSuffix.map Prod.snd) := by
          rw [hpreMap]
          simp [List.append_assoc]
        have htakeTree :
            (newPre.map Prod.snd ++ [a, b] ++
                newSuffix.map Prod.snd).take left.leafCount =
              newLeftPairs.map Prod.snd := by
          rw [htreeWeights, ← hleftWeightsLen]
          simp
        have hdropTree :
            (newPre.map Prod.snd ++ [a, b] ++
                newSuffix.map Prod.snd).drop left.leafCount =
              newRightPre.map Prod.snd ++ [a, b] ++
                newSuffix.map Prod.snd := by
          rw [htreeWeights, ← hleftWeightsLen]
          simp
        have htakeContracted :
            (newPre.map Prod.snd ++ [a + b] ++
                newSuffix.map Prod.snd).take left.leafCount =
              newLeftPairs.map Prod.snd := by
          rw [hcontractedWeights, ← hleftWeightsLen]
          simp
        have hdropContracted :
            (newPre.map Prod.snd ++ [a + b] ++
                newSuffix.map Prod.snd).drop left.leafCount =
              newRightPre.map Prod.snd ++ [a + b] ++
                newSuffix.map Prod.snd := by
          rw [hcontractedWeights, ← hleftWeightsLen]
          simp
        rw [relabelLeaves, relabelLeaves, htakeTree, hdropTree,
          htakeContracted, hdropContracted]
        exact SiblingLeafContract.inRight
          (hrelabeled hrightPreLen hsuffix)

/-- Extend a same-shape relabeling proof through a parent node when the
contracted sibling pair lies in the left child. -/
theorem relabelLeaves_contract_node_inLeft_of_context_lengths
    {left contractedLeft right : InsertionScheduleTree}
    {pre suffix rightPairs : List (ℕ × ℝ)} {oldA oldB : ℝ}
    (hrightPairsLen : rightPairs.length = right.leafCount)
    (hleftLeaves :
      left.leaves =
        pre.map Prod.snd ++ [oldA, oldB] ++ suffix.map Prod.snd)
    (hcontractedLeftLeaves :
      contractedLeft.leaves =
        pre.map Prod.snd ++ [oldA + oldB] ++ suffix.map Prod.snd)
    (hrelabeled :
      ∀ {newPre newSuffix : List (ℕ × ℝ)} {a b : ℝ},
        newPre.length = pre.length →
        newSuffix.length = suffix.length →
        SiblingLeafContract
          (relabelLeaves left
            (newPre.map Prod.snd ++ [a, b] ++
              newSuffix.map Prod.snd))
          (relabelLeaves contractedLeft
            (newPre.map Prod.snd ++ [a + b] ++
              newSuffix.map Prod.snd))
          a b) :
    ∀ {newPre newSuffix : List (ℕ × ℝ)} {a b : ℝ},
      newPre.length = pre.length →
      newSuffix.length = (suffix ++ rightPairs).length →
      SiblingLeafContract
        (relabelLeaves (node left right)
          (newPre.map Prod.snd ++ [a, b] ++ newSuffix.map Prod.snd))
        (relabelLeaves (node contractedLeft right)
          (newPre.map Prod.snd ++ [a + b] ++
            newSuffix.map Prod.snd))
        a b := by
  intro newPre newSuffix a b hpre hsuffix
  let newLeftSuffix := newSuffix.take suffix.length
  let newRightPairs := newSuffix.drop suffix.length
  have hsuffix_split :
      newSuffix = newLeftSuffix ++ newRightPairs := by
    simp [newLeftSuffix, newRightPairs, List.take_append_drop]
  have hleftSuffixLen : newLeftSuffix.length = suffix.length := by
    change (newSuffix.take suffix.length).length = suffix.length
    rw [List.length_take]
    have hle : suffix.length ≤ newSuffix.length := by
      rw [hsuffix, List.length_append]
      exact Nat.le_add_right suffix.length rightPairs.length
    exact Nat.min_eq_left hle
  have hrightPairsLen' : newRightPairs.length = right.leafCount := by
    change (newSuffix.drop suffix.length).length = right.leafCount
    rw [List.length_drop, hsuffix, List.length_append]
    exact hrightPairsLen ▸ Nat.add_sub_cancel_left suffix.length
      rightPairs.length
  have hleftCount :
      left.leafCount =
        (newPre.map Prod.snd).length + [a, b].length +
          (newLeftSuffix.map Prod.snd).length := by
    have hlen := congrArg List.length hleftLeaves
    rw [leaves_length] at hlen
    simp [List.length_append] at hlen
    simp [List.length_map, hpre, hleftSuffixLen]
    omega
  have hcontractedLeftCount :
      contractedLeft.leafCount =
        (newPre.map Prod.snd).length + [a + b].length +
          (newLeftSuffix.map Prod.snd).length := by
    have hlen := congrArg List.length hcontractedLeftLeaves
    rw [leaves_length] at hlen
    simp [List.length_append] at hlen
    simp [List.length_map, hpre, hleftSuffixLen]
    omega
  have hsuffixMap :
      newSuffix.map Prod.snd =
        newLeftSuffix.map Prod.snd ++ newRightPairs.map Prod.snd := by
    rw [hsuffix_split]
    simp [List.map_append]
  have htakeTree :
      (newPre.map Prod.snd ++ [a, b] ++
          newSuffix.map Prod.snd).take left.leafCount =
        newPre.map Prod.snd ++ [a, b] ++
          newLeftSuffix.map Prod.snd := by
    rw [hleftCount, hsuffixMap]
    simpa [List.append_assoc] using
      list_take_append_context (newPre.map Prod.snd) [a, b]
        (newLeftSuffix.map Prod.snd) (newRightPairs.map Prod.snd)
  have hdropTree :
      (newPre.map Prod.snd ++ [a, b] ++
          newSuffix.map Prod.snd).drop left.leafCount =
        newRightPairs.map Prod.snd := by
    rw [hleftCount, hsuffixMap]
    simpa [List.append_assoc] using
      list_drop_append_context (newPre.map Prod.snd) [a, b]
        (newLeftSuffix.map Prod.snd) (newRightPairs.map Prod.snd)
  have htakeContracted :
      (newPre.map Prod.snd ++ [a + b] ++
          newSuffix.map Prod.snd).take contractedLeft.leafCount =
        newPre.map Prod.snd ++ [a + b] ++
          newLeftSuffix.map Prod.snd := by
    rw [hcontractedLeftCount, hsuffixMap]
    simpa [List.append_assoc] using
      list_take_append_context (newPre.map Prod.snd) [a + b]
        (newLeftSuffix.map Prod.snd) (newRightPairs.map Prod.snd)
  have hdropContracted :
      (newPre.map Prod.snd ++ [a + b] ++
          newSuffix.map Prod.snd).drop contractedLeft.leafCount =
        newRightPairs.map Prod.snd := by
    rw [hcontractedLeftCount, hsuffixMap]
    simpa [List.append_assoc] using
      list_drop_append_context (newPre.map Prod.snd) [a + b]
        (newLeftSuffix.map Prod.snd) (newRightPairs.map Prod.snd)
  rw [relabelLeaves, relabelLeaves, htakeTree, hdropTree,
    htakeContracted, hdropContracted]
  exact SiblingLeafContract.inLeft (hrelabeled hpre hleftSuffixLen)

/-- Extend a same-shape relabeling proof through a parent node when the
contracted sibling pair lies in the right child. -/
theorem relabelLeaves_contract_node_inRight_of_context_lengths
    {left right contractedRight : InsertionScheduleTree}
    {leftPairs pre suffix : List (ℕ × ℝ)}
    (hleftPairsLen : leftPairs.length = left.leafCount)
    (hrelabeled :
      ∀ {newPre newSuffix : List (ℕ × ℝ)} {a b : ℝ},
        newPre.length = pre.length →
        newSuffix.length = suffix.length →
        SiblingLeafContract
          (relabelLeaves right
            (newPre.map Prod.snd ++ [a, b] ++
              newSuffix.map Prod.snd))
          (relabelLeaves contractedRight
            (newPre.map Prod.snd ++ [a + b] ++
              newSuffix.map Prod.snd))
          a b) :
    ∀ {newPre newSuffix : List (ℕ × ℝ)} {a b : ℝ},
      newPre.length = (leftPairs ++ pre).length →
      newSuffix.length = suffix.length →
      SiblingLeafContract
        (relabelLeaves (node left right)
          (newPre.map Prod.snd ++ [a, b] ++ newSuffix.map Prod.snd))
        (relabelLeaves (node left contractedRight)
          (newPre.map Prod.snd ++ [a + b] ++
            newSuffix.map Prod.snd))
        a b := by
  intro newPre newSuffix a b hpre hsuffix
  let newLeftPairs := newPre.take leftPairs.length
  let newRightPre := newPre.drop leftPairs.length
  have hpre_split :
      newPre = newLeftPairs ++ newRightPre := by
    simp [newLeftPairs, newRightPre, List.take_append_drop]
  have hleftPairsLen' : newLeftPairs.length = leftPairs.length := by
    change (newPre.take leftPairs.length).length = leftPairs.length
    rw [List.length_take]
    have hle : leftPairs.length ≤ newPre.length := by
      rw [hpre, List.length_append]
      exact Nat.le_add_right leftPairs.length pre.length
    exact Nat.min_eq_left hle
  have hrightPreLen : newRightPre.length = pre.length := by
    change (newPre.drop leftPairs.length).length = pre.length
    rw [List.length_drop, hpre, List.length_append]
    exact Nat.add_sub_cancel_left leftPairs.length pre.length
  have hleftWeightsLen :
      (newLeftPairs.map Prod.snd).length = left.leafCount := by
    rw [List.length_map, hleftPairsLen']
    exact hleftPairsLen
  have hpreMap :
      newPre.map Prod.snd =
        newLeftPairs.map Prod.snd ++ newRightPre.map Prod.snd := by
    rw [hpre_split]
    simp [List.map_append]
  have htreeWeights :
      newPre.map Prod.snd ++ [a, b] ++ newSuffix.map Prod.snd =
        newLeftPairs.map Prod.snd ++
          (newRightPre.map Prod.snd ++ [a, b] ++
            newSuffix.map Prod.snd) := by
    rw [hpreMap]
    simp [List.append_assoc]
  have hcontractedWeights :
      newPre.map Prod.snd ++ [a + b] ++ newSuffix.map Prod.snd =
        newLeftPairs.map Prod.snd ++
          (newRightPre.map Prod.snd ++ [a + b] ++
            newSuffix.map Prod.snd) := by
    rw [hpreMap]
    simp [List.append_assoc]
  have htakeTree :
      (newPre.map Prod.snd ++ [a, b] ++
          newSuffix.map Prod.snd).take left.leafCount =
        newLeftPairs.map Prod.snd := by
    rw [htreeWeights, ← hleftWeightsLen]
    simp
  have hdropTree :
      (newPre.map Prod.snd ++ [a, b] ++
          newSuffix.map Prod.snd).drop left.leafCount =
        newRightPre.map Prod.snd ++ [a, b] ++
          newSuffix.map Prod.snd := by
    rw [htreeWeights, ← hleftWeightsLen]
    simp
  have htakeContracted :
      (newPre.map Prod.snd ++ [a + b] ++
          newSuffix.map Prod.snd).take left.leafCount =
        newLeftPairs.map Prod.snd := by
    rw [hcontractedWeights, ← hleftWeightsLen]
    simp
  have hdropContracted :
      (newPre.map Prod.snd ++ [a + b] ++
          newSuffix.map Prod.snd).drop left.leafCount =
        newRightPre.map Prod.snd ++ [a + b] ++
          newSuffix.map Prod.snd := by
    rw [hcontractedWeights, ← hleftWeightsLen]
    simp
  rw [relabelLeaves, relabelLeaves, htakeTree, hdropTree,
    htakeContracted, hdropContracted]
  exact SiblingLeafContract.inRight (hrelabeled hrightPreLen hsuffix)

/-- Same-shape relabeling preserves a displayed sibling-leaf contraction.  The
returned old context identifies the contracted leaf positions; any replacement
prefix/suffix of the same lengths keeps the structural contraction at those
positions. -/
theorem relabelLeaves_contract_of_context_lengths
    {tree contracted : InsertionScheduleTree} {oldA oldB : ℝ}
    (hcontract : SiblingLeafContract tree contracted oldA oldB) :
    ∃ oldPre oldSuffix : List ℝ,
      tree.leaves = oldPre ++ [oldA, oldB] ++ oldSuffix ∧
        contracted.leaves = oldPre ++ [oldA + oldB] ++ oldSuffix ∧
          ∀ {newPre newSuffix : List ℝ} {a b : ℝ},
            newPre.length = oldPre.length →
            newSuffix.length = oldSuffix.length →
            SiblingLeafContract
              (relabelLeaves tree (newPre ++ [a, b] ++ newSuffix))
              (relabelLeaves contracted (newPre ++ [a + b] ++ newSuffix))
              a b := by
  induction hcontract with
  | here oldA oldB =>
      refine ⟨[], [], by simp [leaves], by simp [leaves], ?_⟩
      intro newPre newSuffix a b hpre hsuffix
      have hpre_nil : newPre = [] := List.length_eq_zero_iff.mp hpre
      have hsuffix_nil : newSuffix = [] :=
        List.length_eq_zero_iff.mp hsuffix
      subst newPre
      subst newSuffix
      simp [relabelLeaves]
      exact SiblingLeafContract.here a b
  | inLeft hcontract ih =>
      rename_i left contractedLeft right oldA oldB
      obtain ⟨oldPre, oldSuffix, hleftLeaves, hcontractedLeftLeaves,
        hrelabeled⟩ := ih
      refine ⟨oldPre, oldSuffix ++ right.leaves, ?_, ?_, ?_⟩
      · rw [leaves_node, hleftLeaves]
        simp [List.append_assoc]
      · rw [leaves_node, hcontractedLeftLeaves]
        simp [List.append_assoc]
      · intro newPre newSuffix a b hpre hsuffix
        let newLeftSuffix := newSuffix.take oldSuffix.length
        let rightWeights := newSuffix.drop oldSuffix.length
        have hsuffix_split :
            newSuffix = newLeftSuffix ++ rightWeights := by
          simp [newLeftSuffix, rightWeights, List.take_append_drop]
        have hleftSuffixLen : newLeftSuffix.length = oldSuffix.length := by
          change (newSuffix.take oldSuffix.length).length = oldSuffix.length
          rw [List.length_take]
          have hle : oldSuffix.length ≤ newSuffix.length := by
            rw [hsuffix, List.length_append, leaves_length]
            exact Nat.le_add_right oldSuffix.length right.leafCount
          exact Nat.min_eq_left hle
        have hrightWeightsLen : rightWeights.length = right.leafCount := by
          change (newSuffix.drop oldSuffix.length).length = right.leafCount
          rw [List.length_drop, hsuffix, List.length_append, leaves_length]
          exact Nat.add_sub_cancel_left oldSuffix.length right.leafCount
        have hleftOldCount :
            left.leafCount =
              oldPre.length + [oldA, oldB].length + oldSuffix.length := by
          have hlen := congrArg List.length hleftLeaves
          rw [leaves_length] at hlen
          simp [List.length_append] at hlen
          simp
          omega
        have hcontractedLeftOldCount :
            contractedLeft.leafCount =
              oldPre.length + [oldA + oldB].length + oldSuffix.length := by
          have hlen := congrArg List.length hcontractedLeftLeaves
          rw [leaves_length] at hlen
          simp [List.length_append] at hlen
          simp
          omega
        have hleftCount :
            left.leafCount =
              newPre.length + [a, b].length + newLeftSuffix.length := by
          calc
            left.leafCount =
                oldPre.length + [oldA, oldB].length + oldSuffix.length :=
              hleftOldCount
            _ = newPre.length + [a, b].length + newLeftSuffix.length := by
              simp [hpre, hleftSuffixLen]
        have hcontractedLeftCount :
            contractedLeft.leafCount =
              newPre.length + [a + b].length + newLeftSuffix.length := by
          calc
            contractedLeft.leafCount =
                oldPre.length + [oldA + oldB].length + oldSuffix.length :=
              hcontractedLeftOldCount
            _ = newPre.length + [a + b].length + newLeftSuffix.length := by
              simp [hpre, hleftSuffixLen]
        have htakeTree :
            (newPre ++ [a, b] ++ newSuffix).take left.leafCount =
              newPre ++ [a, b] ++ newLeftSuffix := by
          rw [hleftCount, hsuffix_split]
          simpa [List.append_assoc] using
            list_take_append_context newPre [a, b] newLeftSuffix
              rightWeights
        have hdropTree :
            (newPre ++ [a, b] ++ newSuffix).drop left.leafCount =
              rightWeights := by
          rw [hleftCount, hsuffix_split]
          simpa [List.append_assoc] using
            list_drop_append_context newPre [a, b] newLeftSuffix
              rightWeights
        have htakeContracted :
            (newPre ++ [a + b] ++ newSuffix).take contractedLeft.leafCount =
              newPre ++ [a + b] ++ newLeftSuffix := by
          rw [hcontractedLeftCount, hsuffix_split]
          simpa [List.append_assoc] using
            list_take_append_context newPre [a + b] newLeftSuffix
              rightWeights
        have hdropContracted :
            (newPre ++ [a + b] ++ newSuffix).drop
                contractedLeft.leafCount =
              rightWeights := by
          rw [hcontractedLeftCount, hsuffix_split]
          simpa [List.append_assoc] using
            list_drop_append_context newPre [a + b] newLeftSuffix
              rightWeights
        rw [relabelLeaves, relabelLeaves, htakeTree, hdropTree,
          htakeContracted, hdropContracted]
        exact SiblingLeafContract.inLeft
          (hrelabeled hpre hleftSuffixLen)
  | inRight hcontract ih =>
      rename_i left right contractedRight oldA oldB
      obtain ⟨oldPre, oldSuffix, hrightLeaves, hcontractedRightLeaves,
        hrelabeled⟩ := ih
      refine ⟨left.leaves ++ oldPre, oldSuffix, ?_, ?_, ?_⟩
      · rw [leaves_node, hrightLeaves]
        simp [List.append_assoc]
      · rw [leaves_node, hcontractedRightLeaves]
        simp [List.append_assoc]
      · intro newPre newSuffix a b hpre hsuffix
        let leftWeights := newPre.take left.leafCount
        let newRightPre := newPre.drop left.leafCount
        have hpre_split :
            newPre = leftWeights ++ newRightPre := by
          simp [leftWeights, newRightPre, List.take_append_drop]
        have hleftWeightsLen : leftWeights.length = left.leafCount := by
          change (newPre.take left.leafCount).length = left.leafCount
          rw [List.length_take]
          have hle : left.leafCount ≤ newPre.length := by
            rw [hpre, List.length_append, leaves_length]
            exact Nat.le_add_right left.leafCount oldPre.length
          exact Nat.min_eq_left hle
        have hrightPreLen : newRightPre.length = oldPre.length := by
          change (newPre.drop left.leafCount).length = oldPre.length
          rw [List.length_drop, hpre, List.length_append, leaves_length]
          exact Nat.add_sub_cancel_left left.leafCount oldPre.length
        have htreeWeights :
            newPre ++ [a, b] ++ newSuffix =
              leftWeights ++ newRightPre ++ [a, b] ++ newSuffix := by
          rw [hpre_split]
        have hcontractedWeights :
            newPre ++ [a + b] ++ newSuffix =
              leftWeights ++ newRightPre ++ [a + b] ++ newSuffix := by
          rw [hpre_split]
        have htakeTree :
            (newPre ++ [a, b] ++ newSuffix).take left.leafCount =
              leftWeights := by
          rw [htreeWeights]
          have hsplit :
              leftWeights ++ newRightPre ++ [a, b] ++ newSuffix =
                leftWeights ++ (newRightPre ++ [a, b] ++ newSuffix) := by
            simp [List.append_assoc]
          rw [hsplit, ← hleftWeightsLen]
          simp
        have hdropTree :
            (newPre ++ [a, b] ++ newSuffix).drop left.leafCount =
              newRightPre ++ [a, b] ++ newSuffix := by
          rw [htreeWeights]
          have hsplit :
              leftWeights ++ newRightPre ++ [a, b] ++ newSuffix =
                leftWeights ++ (newRightPre ++ [a, b] ++ newSuffix) := by
            simp [List.append_assoc]
          rw [hsplit, ← hleftWeightsLen]
          simp
        have htakeContracted :
            (newPre ++ [a + b] ++ newSuffix).take left.leafCount =
              leftWeights := by
          rw [hcontractedWeights]
          have hsplit :
              leftWeights ++ newRightPre ++ [a + b] ++ newSuffix =
                leftWeights ++ (newRightPre ++ [a + b] ++ newSuffix) := by
            simp [List.append_assoc]
          rw [hsplit, ← hleftWeightsLen]
          simp
        have hdropContracted :
            (newPre ++ [a + b] ++ newSuffix).drop left.leafCount =
              newRightPre ++ [a + b] ++ newSuffix := by
          rw [hcontractedWeights]
          have hsplit :
              leftWeights ++ newRightPre ++ [a + b] ++ newSuffix =
                leftWeights ++ (newRightPre ++ [a + b] ++ newSuffix) := by
            simp [List.append_assoc]
          rw [hsplit, ← hleftWeightsLen]
          simp
        rw [relabelLeaves, relabelLeaves, htakeTree, hdropTree,
          htakeContracted, hdropContracted]
        exact SiblingLeafContract.inRight
          (hrelabeled hrightPreLen hsuffix)

/-- Expand a permutation of the contracted leaves back to the original leaves
by replacing the contracted parent weight with the sibling pair. -/
theorem leaves_perm_of_contracted_perm
    {tree contracted : InsertionScheduleTree} {a b : ℝ} {rest : List ℝ}
    (hcontract : SiblingLeafContract tree contracted a b)
    (hperm : contracted.leaves.Perm ((a + b) :: rest)) :
    tree.leaves.Perm (a :: b :: rest) := by
  obtain ⟨pre, suffix, htree, hcontracted⟩ :=
    exists_leaves_context hcontract
  have hcontractedContext :
      (pre ++ [a + b] ++ suffix).Perm ((a + b) :: rest) := by
    simpa [hcontracted] using hperm
  have hmergedFront :
      (pre ++ [a + b] ++ suffix).Perm ((a + b) :: pre ++ suffix) := by
    simp [List.append_assoc]
  have hcontext : (pre ++ suffix).Perm rest :=
    List.Perm.cons_inv (hmergedFront.symm.trans hcontractedContext)
  have hfrontAB :
      (pre ++ [a, b] ++ suffix).Perm (a :: b :: pre ++ suffix) := by
    have ha :
        (pre ++ a :: b :: suffix).Perm (a :: pre ++ b :: suffix) :=
      List.perm_middle (a := a) (l₁ := pre) (l₂ := b :: suffix)
    have hb :
        (pre ++ b :: suffix).Perm (b :: pre ++ suffix) :=
      List.perm_middle (a := b) (l₁ := pre) (l₂ := suffix)
    simpa [List.append_assoc] using ha.trans (List.Perm.cons a hb)
  rw [htree]
  exact hfrontAB.trans (List.Perm.cons a (List.Perm.cons b hcontext))

/-- Contract a permutation of the original leaves forward by replacing the
displayed sibling pair with its parent weight. -/
theorem contracted_perm_of_leaves_perm
    {tree contracted : InsertionScheduleTree} {a b : ℝ} {rest : List ℝ}
    (hcontract : SiblingLeafContract tree contracted a b)
    (hperm : tree.leaves.Perm (a :: b :: rest)) :
    contracted.leaves.Perm ((a + b) :: rest) := by
  obtain ⟨pre, suffix, htree, hcontracted⟩ :=
    exists_leaves_context hcontract
  have htreeContext :
      (pre ++ [a, b] ++ suffix).Perm (a :: b :: rest) := by
    simpa [htree] using hperm
  have hfrontAB :
      (pre ++ [a, b] ++ suffix).Perm (a :: b :: pre ++ suffix) := by
    have ha :
        (pre ++ a :: b :: suffix).Perm (a :: pre ++ b :: suffix) :=
      List.perm_middle (a := a) (l₁ := pre) (l₂ := b :: suffix)
    have hb :
        (pre ++ b :: suffix).Perm (b :: pre ++ suffix) :=
      List.perm_middle (a := b) (l₁ := pre) (l₂ := suffix)
    simpa [List.append_assoc] using ha.trans (List.Perm.cons a hb)
  have hcontext : (pre ++ suffix).Perm rest :=
    List.Perm.cons_inv (List.Perm.cons_inv (hfrontAB.symm.trans htreeContext))
  have hmergedFront :
      (pre ++ [a + b] ++ suffix).Perm ((a + b) :: pre ++ suffix) := by
    simp [List.append_assoc]
  rw [hcontracted]
  exact hmergedFront.trans (List.Perm.cons (a + b) hcontext)

/-- If the contracted tree contains the merged weight `a + b`, that leaf can
be expanded into sibling leaves `a` and `b`. -/
theorem exists_expansion_of_mem
    (contracted : InsertionScheduleTree) {a b : ℝ}
    (hmem : a + b ∈ contracted.leaves) :
    ∃ tree : InsertionScheduleTree,
      SiblingLeafContract tree contracted a b := by
  induction contracted with
  | leaf x =>
      simp [leaves] at hmem
      subst x
      exact ⟨node (leaf a) (leaf b), SiblingLeafContract.here a b⟩
  | node left right ihl ihr =>
      simp [leaves] at hmem
      rcases hmem with hleft | hright
      · obtain ⟨expandedLeft, hcontract⟩ := ihl hleft
        exact ⟨node expandedLeft right,
          SiblingLeafContract.inLeft hcontract⟩
      · obtain ⟨expandedRight, hcontract⟩ := ihr hright
        exact ⟨node left expandedRight,
          SiblingLeafContract.inRight hcontract⟩

/-- Contracting a sibling leaf pair preserves leaf nonnegativity. -/
theorem contracted_leaves_nonnegative
    {tree contracted : InsertionScheduleTree} {a b : ℝ}
    (hcontract : SiblingLeafContract tree contracted a b)
    (hnonneg : ∀ x ∈ tree.leaves, 0 ≤ x) :
    ∀ x ∈ contracted.leaves, 0 ≤ x := by
  obtain ⟨pre, suffix, htree, hcontracted⟩ :=
    exists_leaves_context hcontract
  intro x hx
  rw [hcontracted] at hx
  simp [List.mem_append] at hx
  rcases hx with hpre | hmerged | hsuffix
  · exact hnonneg x (by
      rw [htree]
      simp [List.mem_append, hpre])
  · have ha : 0 ≤ a := hnonneg a (by
      rw [htree]
      simp)
    have hb : 0 ≤ b := hnonneg b (by
      rw [htree]
      simp)
    simpa [hmerged] using add_nonneg ha hb
  · exact hnonneg x (by
      rw [htree]
      simp [List.mem_append, hsuffix])

/-- Structural sibling contraction removes exactly one copy of the merged
weight from weighted external path length, at any starting depth. -/
theorem weightedLeafDepthCost_eq
    {tree contracted : InsertionScheduleTree} {a b : ℝ} (depth : ℕ)
    (hcontract : SiblingLeafContract tree contracted a b) :
    weightedLeafDepthCost depth tree =
      weightedLeafDepthCost depth contracted + (a + b) := by
  induction hcontract generalizing depth with
  | here a b =>
      exact weightedLeafDepthCost_node_leaf_leaf_eq_contract depth a b
  | inLeft hcontract ih =>
      simp [weightedLeafDepthCost, ih (depth + 1)]
      ring
  | inRight hcontract ih =>
      simp [weightedLeafDepthCost, ih (depth + 1)]
      ring

end SiblingLeafContract

/-- Every non-leaf schedule has a maximum-depth sibling leaf pair that can be
structurally contracted.  This couples the explicit deepest-pair display with
the tree-level contraction relation used in the Huffman induction. -/
theorem exists_deepest_sibling_leaf_contract
    (depth : ℕ) :
    (tree : InsertionScheduleTree) →
      1 < tree.leafCount →
        ∃ contractedTree : InsertionScheduleTree,
          ∃ pre suffix : List (ℕ × ℝ), ∃ a b : ℝ,
            SiblingLeafContract tree contractedTree a b ∧
              leafDepthWeights depth tree =
                pre ++
                  [(maxLeafDepth depth tree, a),
                    (maxLeafDepth depth tree, b)] ++
                  suffix ∧
                weightedLeafDepthCost depth tree =
                  weightedLeafDepthCost depth contractedTree + (a + b) ∧
                  tree.leafCount = contractedTree.leafCount + 1 := by
  intro tree
  induction tree generalizing depth with
  | leaf x =>
      intro hcount
      simp [leafCount] at hcount
  | node left right ihl ihr =>
      intro _hcount
      cases left with
      | leaf x =>
          cases right with
          | leaf y =>
              let hcontract :=
                SiblingLeafContract.here x y
              refine ⟨leaf (x + y), [], [], x, y, hcontract, ?_, ?_, ?_⟩
              · simp [leafDepthWeights, maxLeafDepth]
              · exact SiblingLeafContract.weightedLeafDepthCost_eq depth hcontract
              · exact SiblingLeafContract.leafCount_eq_succ hcontract
          | node rightLeft rightRight =>
              obtain ⟨contractedRight, pre, suffix, a, b,
                  hcontractRight, hpair, _hcost, _hcount⟩ :=
                ihr (depth + 1)
                  (one_lt_leafCount_node rightLeft rightRight)
              let hcontract :=
                SiblingLeafContract.inRight
                  (left := leaf x) hcontractRight
              have hmax :
                  maxLeafDepth depth
                      (node (leaf x) (node rightLeft rightRight)) =
                    maxLeafDepth (depth + 1)
                      (node rightLeft rightRight) := by
                change
                  max (depth + 1)
                      (maxLeafDepth (depth + 1)
                        (node rightLeft rightRight)) =
                    maxLeafDepth (depth + 1)
                      (node rightLeft rightRight)
                exact Nat.max_eq_right
                  (depth_le_maxLeafDepth (depth + 1)
                    (node rightLeft rightRight))
              refine ⟨node (leaf x) contractedRight,
                [(depth + 1, x)] ++ pre, suffix, a, b, hcontract,
                ?_, ?_, ?_⟩
              · have hpair' :=
                  congrArg (fun pairs => [(depth + 1, x)] ++ pairs) hpair
                simpa [leafDepthWeights, hmax, List.append_assoc] using hpair'
              · exact SiblingLeafContract.weightedLeafDepthCost_eq depth hcontract
              · exact SiblingLeafContract.leafCount_eq_succ hcontract
      | node leftLeft leftRight =>
          cases right with
          | leaf y =>
              obtain ⟨contractedLeft, pre, suffix, a, b,
                  hcontractLeft, hpair, _hcost, _hcount⟩ :=
                ihl (depth + 1)
                  (one_lt_leafCount_node leftLeft leftRight)
              let hcontract :=
                SiblingLeafContract.inLeft
                  (right := leaf y) hcontractLeft
              have hmax :
                  maxLeafDepth depth
                      (node (node leftLeft leftRight) (leaf y)) =
                    maxLeafDepth (depth + 1)
                      (node leftLeft leftRight) := by
                change
                  max (maxLeafDepth (depth + 1)
                        (node leftLeft leftRight))
                      (depth + 1) =
                    maxLeafDepth (depth + 1)
                      (node leftLeft leftRight)
                exact Nat.max_eq_left
                  (depth_le_maxLeafDepth (depth + 1)
                    (node leftLeft leftRight))
              refine ⟨node contractedLeft (leaf y),
                pre, suffix ++ [(depth + 1, y)], a, b, hcontract,
                ?_, ?_, ?_⟩
              · have hpair' :=
                  congrArg (fun pairs => pairs ++ [(depth + 1, y)]) hpair
                simpa [leafDepthWeights, hmax, List.append_assoc] using hpair'
              · exact SiblingLeafContract.weightedLeafDepthCost_eq depth hcontract
              · exact SiblingLeafContract.leafCount_eq_succ hcontract
          | node rightLeft rightRight =>
              let leftTree := node leftLeft leftRight
              let rightTree := node rightLeft rightRight
              let leftMax := maxLeafDepth (depth + 1) leftTree
              let rightMax := maxLeafDepth (depth + 1) rightTree
              by_cases hle : rightMax ≤ leftMax
              · obtain ⟨contractedLeft, pre, suffix, a, b,
                    hcontractLeft, hpair, _hcost, _hcount⟩ :=
                  ihl (depth + 1)
                    (one_lt_leafCount_node leftLeft leftRight)
                let hcontract :=
                  SiblingLeafContract.inLeft
                    (right := rightTree) hcontractLeft
                have hmax :
                    maxLeafDepth depth (node leftTree rightTree) =
                      leftMax := by
                  change max leftMax rightMax = leftMax
                  exact Nat.max_eq_left hle
                refine ⟨node contractedLeft rightTree,
                  pre,
                  suffix ++ leafDepthWeights (depth + 1) rightTree,
                  a, b, hcontract, ?_, ?_, ?_⟩
                · have hpair' :=
                    congrArg
                      (fun pairs =>
                        pairs ++ leafDepthWeights (depth + 1) rightTree)
                      hpair
                  simpa [leafDepthWeights, hmax, leftTree, rightTree,
                    leftMax, List.append_assoc] using hpair'
                · exact SiblingLeafContract.weightedLeafDepthCost_eq depth hcontract
                · exact SiblingLeafContract.leafCount_eq_succ hcontract
              · have hleft_le_right : leftMax ≤ rightMax :=
                  Nat.le_of_lt (Nat.lt_of_not_ge hle)
                obtain ⟨contractedRight, pre, suffix, a, b,
                    hcontractRight, hpair, _hcost, _hcount⟩ :=
                  ihr (depth + 1)
                    (one_lt_leafCount_node rightLeft rightRight)
                let hcontract :=
                  SiblingLeafContract.inRight
                    (left := leftTree) hcontractRight
                have hmax :
                    maxLeafDepth depth (node leftTree rightTree) =
                      rightMax := by
                  change max leftMax rightMax = rightMax
                  exact Nat.max_eq_right hleft_le_right
                refine ⟨node leftTree contractedRight,
                  leafDepthWeights (depth + 1) leftTree ++ pre,
                  suffix, a, b, hcontract, ?_, ?_, ?_⟩
                · have hpair' :=
                    congrArg
                      (fun pairs =>
                        leafDepthWeights (depth + 1) leftTree ++ pairs)
                      hpair
                  simpa [leafDepthWeights, hmax, leftTree, rightTree,
                    rightMax, List.append_assoc] using hpair'
                · exact SiblingLeafContract.weightedLeafDepthCost_eq depth hcontract
                · exact SiblingLeafContract.leafCount_eq_succ hcontract

/-- Parent-depth form of the maximum-depth sibling contraction package.  This
is the depth shape required by the contraction-normalization bridge: the
deepest sibling pair is displayed at `parentDepth + 1`, and that depth is the
tree's maximum leaf depth. -/
theorem exists_deepest_sibling_leaf_contract_with_parent_context
    (depth : ℕ) (tree : InsertionScheduleTree)
    (hcount : 1 < tree.leafCount) :
    ∃ contractedTree : InsertionScheduleTree,
      ∃ parentDepth : ℕ, ∃ pre suffix : List (ℕ × ℝ), ∃ a b : ℝ,
        SiblingLeafContract tree contractedTree a b ∧
          leafDepthWeights depth tree =
            pre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
              suffix ∧
            parentDepth + 1 = maxLeafDepth depth tree ∧
              weightedLeafDepthCost depth tree =
                weightedLeafDepthCost depth contractedTree + (a + b) ∧
                tree.leafCount = contractedTree.leafCount + 1 := by
  obtain ⟨contractedTree, pre, suffix, a, b, hcontract, hpairs,
      hcost, hcountEq⟩ :=
    exists_deepest_sibling_leaf_contract depth tree hcount
  let parentDepth := maxLeafDepth depth tree - 1
  have hmax_pos : 0 < maxLeafDepth depth tree := by
    have hsucc :=
      succ_depth_le_maxLeafDepth_of_one_lt_leafCount depth tree hcount
    exact Nat.lt_of_lt_of_le (Nat.succ_pos depth) hsucc
  have hparent : parentDepth + 1 = maxLeafDepth depth tree := by
    dsimp [parentDepth]
    exact Nat.sub_add_cancel hmax_pos
  refine ⟨contractedTree, parentDepth, pre, suffix, a, b, hcontract, ?_,
    hparent, hcost, hcountEq⟩
  simpa [hparent] using hpairs

/-- Parent-depth form of the maximum-depth sibling contraction package, with
the same-length relabeling invariant needed by the contraction normalizer.
Unlike the generic structural-context theorem, this packages the relabel proof
for the exact deepest context selected by the recursive deepest-pair search. -/
theorem exists_deepest_sibling_leaf_contract_with_relabel_parent_context
    (depth : ℕ) :
    (tree : InsertionScheduleTree) →
      1 < tree.leafCount →
        ∃ contractedTree : InsertionScheduleTree,
          ∃ parentDepth : ℕ, ∃ pre suffix : List (ℕ × ℝ), ∃ a b : ℝ,
            SiblingLeafContract tree contractedTree a b ∧
              leafDepthWeights depth tree =
                pre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                  suffix ∧
                leafDepthWeights depth contractedTree =
                  pre ++ [(parentDepth, a + b)] ++ suffix ∧
                  parentDepth + 1 = maxLeafDepth depth tree ∧
                    weightedLeafDepthCost depth tree =
                      weightedLeafDepthCost depth contractedTree + (a + b) ∧
                      tree.leafCount = contractedTree.leafCount + 1 ∧
                        ∀ {newPre newSuffix : List (ℕ × ℝ)} {a b : ℝ},
                          newPre.length = pre.length →
                          newSuffix.length = suffix.length →
                          SiblingLeafContract
                            (relabelLeaves tree
                              (newPre.map Prod.snd ++ [a, b] ++
                                newSuffix.map Prod.snd))
                            (relabelLeaves contractedTree
                              (newPre.map Prod.snd ++ [a + b] ++
                                newSuffix.map Prod.snd))
                            a b := by
  intro tree
  induction tree generalizing depth with
  | leaf x =>
      intro hcount
      simp [leafCount] at hcount
  | node left right ihl ihr =>
      intro _hcount
      cases left with
      | leaf x =>
          cases right with
          | leaf y =>
              let hcontract := SiblingLeafContract.here x y
              refine ⟨leaf (x + y), depth, [], [], x, y, hcontract,
                ?_, ?_, ?_, ?_, ?_, ?_⟩
              · simp [leafDepthWeights]
              · simp [leafDepthWeights]
              · simp [maxLeafDepth]
              · exact SiblingLeafContract.weightedLeafDepthCost_eq depth hcontract
              · exact SiblingLeafContract.leafCount_eq_succ hcontract
              · intro newPre newSuffix a b hpre hsuffix
                have hpre_nil : newPre = [] :=
                  List.length_eq_zero_iff.mp hpre
                have hsuffix_nil : newSuffix = [] :=
                  List.length_eq_zero_iff.mp hsuffix
                subst newPre
                subst newSuffix
                simp [relabelLeaves]
                exact SiblingLeafContract.here a b
          | node rightLeft rightRight =>
              let rightTree := node rightLeft rightRight
              obtain ⟨contractedRight, parentDepth, pre, suffix, a, b,
                  hcontractRight, hrightDepth, hcontractedRightDepth,
                  hparent, _hcost, _hcountEq, hrelabeled⟩ :=
                ihr (depth + 1)
                  (one_lt_leafCount_node rightLeft rightRight)
              let hcontract :=
                SiblingLeafContract.inRight
                  (left := leaf x) hcontractRight
              let leftPairs := leafDepthWeights (depth + 1) (leaf x)
              have hleftPairsLen :
                  leftPairs.length = (leaf x).leafCount := by
                simp [leftPairs]
              have hmax :
                  maxLeafDepth depth
                      (node (leaf x) (node rightLeft rightRight)) =
                    maxLeafDepth (depth + 1)
                      (node rightLeft rightRight) := by
                change
                  max (depth + 1)
                      (maxLeafDepth (depth + 1)
                        (node rightLeft rightRight)) =
                    maxLeafDepth (depth + 1)
                      (node rightLeft rightRight)
                exact Nat.max_eq_right
                  (depth_le_maxLeafDepth (depth + 1)
                    (node rightLeft rightRight))
              refine ⟨node (leaf x) contractedRight, parentDepth,
                leftPairs ++ pre, suffix, a, b, hcontract, ?_, ?_, ?_,
                ?_, ?_, ?_⟩
              · rw [leafDepthWeights_node, hrightDepth]
                simp [leftPairs, List.append_assoc]
              · rw [leafDepthWeights_node, hcontractedRightDepth]
                simp [leftPairs, List.append_assoc]
              · simpa [hmax] using hparent
              · exact SiblingLeafContract.weightedLeafDepthCost_eq depth hcontract
              · exact SiblingLeafContract.leafCount_eq_succ hcontract
              · exact
                  SiblingLeafContract.relabelLeaves_contract_node_inRight_of_context_lengths
                    (left := leaf x) (right := rightTree)
                    (contractedRight := contractedRight)
                    (leftPairs := leftPairs) (pre := pre)
                    (suffix := suffix) hleftPairsLen hrelabeled
      | node leftLeft leftRight =>
          cases right with
          | leaf y =>
              let leftTree := node leftLeft leftRight
              obtain ⟨contractedLeft, parentDepth, pre, suffix, a, b,
                  hcontractLeft, hleftDepth, hcontractedLeftDepth,
                  hparent, _hcost, _hcountEq, hrelabeled⟩ :=
                ihl (depth + 1)
                  (one_lt_leafCount_node leftLeft leftRight)
              let hcontract :=
                SiblingLeafContract.inLeft
                  (right := leaf y) hcontractLeft
              let rightPairs := leafDepthWeights (depth + 1) (leaf y)
              have hrightPairsLen :
                  rightPairs.length = (leaf y).leafCount := by
                simp [rightPairs]
              have hleftLeaves :
                  leftTree.leaves =
                    pre.map Prod.snd ++ [a, b] ++ suffix.map Prod.snd :=
                leaves_eq_of_leafDepthWeights_pair_display hleftDepth
              have hcontractedLeftLeaves :
                  contractedLeft.leaves =
                    pre.map Prod.snd ++ [a + b] ++ suffix.map Prod.snd :=
                leaves_eq_of_leafDepthWeights_single_display
                  hcontractedLeftDepth
              have hmax :
                  maxLeafDepth depth
                      (node (node leftLeft leftRight) (leaf y)) =
                    maxLeafDepth (depth + 1)
                      (node leftLeft leftRight) := by
                change
                  max (maxLeafDepth (depth + 1)
                        (node leftLeft leftRight))
                      (depth + 1) =
                    maxLeafDepth (depth + 1)
                      (node leftLeft leftRight)
                exact Nat.max_eq_left
                  (depth_le_maxLeafDepth (depth + 1)
                    (node leftLeft leftRight))
              refine ⟨node contractedLeft (leaf y), parentDepth, pre,
                suffix ++ rightPairs, a, b, hcontract, ?_, ?_, ?_,
                ?_, ?_, ?_⟩
              · rw [leafDepthWeights_node, hleftDepth]
                simp [rightPairs, List.append_assoc]
              · rw [leafDepthWeights_node, hcontractedLeftDepth]
                simp [rightPairs, List.append_assoc]
              · simpa [hmax] using hparent
              · exact SiblingLeafContract.weightedLeafDepthCost_eq depth hcontract
              · exact SiblingLeafContract.leafCount_eq_succ hcontract
              · exact
                  SiblingLeafContract.relabelLeaves_contract_node_inLeft_of_context_lengths
                    (left := leftTree) (contractedLeft := contractedLeft)
                    (right := leaf y) (pre := pre) (suffix := suffix)
                    (rightPairs := rightPairs) hrightPairsLen
                    hleftLeaves hcontractedLeftLeaves hrelabeled
          | node rightLeft rightRight =>
              let leftTree := node leftLeft leftRight
              let rightTree := node rightLeft rightRight
              let leftMax := maxLeafDepth (depth + 1) leftTree
              let rightMax := maxLeafDepth (depth + 1) rightTree
              by_cases hle : rightMax ≤ leftMax
              · obtain ⟨contractedLeft, parentDepth, pre, suffix, a, b,
                    hcontractLeft, hleftDepth, hcontractedLeftDepth,
                    hparent, _hcost, _hcountEq, hrelabeled⟩ :=
                  ihl (depth + 1)
                    (one_lt_leafCount_node leftLeft leftRight)
                let hcontract :=
                  SiblingLeafContract.inLeft
                    (right := rightTree) hcontractLeft
                let rightPairs := leafDepthWeights (depth + 1) rightTree
                have hrightPairsLen :
                    rightPairs.length = rightTree.leafCount := by
                  simp [rightPairs, leafDepthWeights_length]
                have hleftLeaves :
                    leftTree.leaves =
                      pre.map Prod.snd ++ [a, b] ++ suffix.map Prod.snd :=
                  leaves_eq_of_leafDepthWeights_pair_display hleftDepth
                have hcontractedLeftLeaves :
                    contractedLeft.leaves =
                      pre.map Prod.snd ++ [a + b] ++ suffix.map Prod.snd :=
                  leaves_eq_of_leafDepthWeights_single_display
                    hcontractedLeftDepth
                have hmax :
                    maxLeafDepth depth (node leftTree rightTree) =
                      leftMax := by
                  change max leftMax rightMax = leftMax
                  exact Nat.max_eq_left hle
                refine ⟨node contractedLeft rightTree, parentDepth, pre,
                  suffix ++ rightPairs, a, b, hcontract, ?_, ?_, ?_,
                  ?_, ?_, ?_⟩
                · rw [leafDepthWeights_node, hleftDepth]
                  simp [rightTree, rightPairs, List.append_assoc]
                · rw [leafDepthWeights_node, hcontractedLeftDepth]
                  simp [rightTree, rightPairs, List.append_assoc]
                · rw [hmax]
                  exact hparent
                · exact SiblingLeafContract.weightedLeafDepthCost_eq depth hcontract
                · exact SiblingLeafContract.leafCount_eq_succ hcontract
                · exact
                    SiblingLeafContract.relabelLeaves_contract_node_inLeft_of_context_lengths
                      (left := leftTree) (contractedLeft := contractedLeft)
                      (right := rightTree) (pre := pre) (suffix := suffix)
                      (rightPairs := rightPairs) hrightPairsLen
                      hleftLeaves hcontractedLeftLeaves hrelabeled
              · have hleft_le_right : leftMax ≤ rightMax :=
                  Nat.le_of_lt (Nat.lt_of_not_ge hle)
                obtain ⟨contractedRight, parentDepth, pre, suffix, a, b,
                    hcontractRight, hrightDepth, hcontractedRightDepth,
                    hparent, _hcost, _hcountEq, hrelabeled⟩ :=
                  ihr (depth + 1)
                    (one_lt_leafCount_node rightLeft rightRight)
                let hcontract :=
                  SiblingLeafContract.inRight
                    (left := leftTree) hcontractRight
                let leftPairs := leafDepthWeights (depth + 1) leftTree
                have hleftPairsLen :
                    leftPairs.length = leftTree.leafCount := by
                  simp [leftPairs, leafDepthWeights_length]
                have hmax :
                    maxLeafDepth depth (node leftTree rightTree) =
                      rightMax := by
                  change max leftMax rightMax = rightMax
                  exact Nat.max_eq_right hleft_le_right
                refine ⟨node leftTree contractedRight, parentDepth,
                  leftPairs ++ pre, suffix, a, b, hcontract, ?_, ?_, ?_,
                  ?_, ?_, ?_⟩
                · rw [leafDepthWeights_node, hrightDepth]
                  simp [leftTree, leftPairs, List.append_assoc]
                · rw [leafDepthWeights_node, hcontractedRightDepth]
                  simp [leftTree, leftPairs, List.append_assoc]
                · rw [hmax]
                  exact hparent
                · exact SiblingLeafContract.weightedLeafDepthCost_eq depth hcontract
                · exact SiblingLeafContract.leafCount_eq_succ hcontract
                · exact
                    SiblingLeafContract.relabelLeaves_contract_node_inRight_of_context_lengths
                      (left := leftTree) (right := rightTree)
                      (contractedRight := contractedRight)
                      (leftPairs := leftPairs) (pre := pre)
                      (suffix := suffix) hleftPairsLen hrelabeled

/-- Leaf-context form of the maximum-depth sibling contraction package.  This
adds the plain leaf-list display corresponding to the explicit leaf-depth
display returned by `exists_deepest_sibling_leaf_contract`. -/
theorem exists_deepest_sibling_leaf_contract_with_leaf_context
    (depth : ℕ) (tree : InsertionScheduleTree)
    (hcount : 1 < tree.leafCount) :
    ∃ contractedTree : InsertionScheduleTree,
      ∃ pre suffix : List (ℕ × ℝ), ∃ a b : ℝ,
        SiblingLeafContract tree contractedTree a b ∧
          leafDepthWeights depth tree =
            pre ++
              [(maxLeafDepth depth tree, a),
                (maxLeafDepth depth tree, b)] ++
              suffix ∧
            tree.leaves =
              pre.map Prod.snd ++ [a, b] ++ suffix.map Prod.snd ∧
              weightedLeafDepthCost depth tree =
                weightedLeafDepthCost depth contractedTree + (a + b) ∧
                tree.leafCount = contractedTree.leafCount + 1 := by
  obtain ⟨contractedTree, pre, suffix, a, b, hcontract, hpairs,
    hcost, hcountEq⟩ :=
    exists_deepest_sibling_leaf_contract depth tree hcount
  refine ⟨contractedTree, pre, suffix, a, b, hcontract, hpairs, ?_,
    hcost, hcountEq⟩
  exact leaves_eq_of_leafDepthWeights_pair_display hpairs

/-- Weighted external path length is nonnegative for nonnegative leaves. -/
theorem weightedLeafDepthCost_nonneg_of_leaves_nonnegative
    (depth : ℕ) (tree : InsertionScheduleTree)
    (hnonneg : ∀ x ∈ tree.leaves, 0 ≤ x) :
    0 ≤ weightedLeafDepthCost depth tree := by
  induction tree generalizing depth with
  | leaf x =>
      have hx : 0 ≤ x := hnonneg x (by simp [leaves])
      have hdepth : 0 ≤ (depth : ℝ) := by
        exact_mod_cast (Nat.zero_le depth)
      simpa [weightedLeafDepthCost] using mul_nonneg hdepth hx
  | node left right ihl ihr =>
      have hleft : ∀ x ∈ left.leaves, 0 ≤ x := by
        intro x hx
        exact hnonneg x (by simp [leaves, hx])
      have hright : ∀ x ∈ right.leaves, 0 ≤ x := by
        intro x hx
        exact hnonneg x (by simp [leaves, hx])
      exact add_nonneg (ihl (depth + 1) hleft) (ihr (depth + 1) hright)

/-- Increasing the starting depth cannot decrease weighted external path
length when all leaves are nonnegative. -/
theorem weightedLeafDepthCost_mono_startDepth_of_leaves_nonnegative
    (tree : InsertionScheduleTree) {depth₁ depth₂ : ℕ}
    (hdepth : depth₁ ≤ depth₂)
    (hnonneg : ∀ x ∈ tree.leaves, 0 ≤ x) :
    weightedLeafDepthCost depth₁ tree ≤
      weightedLeafDepthCost depth₂ tree := by
  induction tree generalizing depth₁ depth₂ with
  | leaf x =>
      have hx : 0 ≤ x := hnonneg x (by simp [leaves])
      have hdepth_real : (depth₁ : ℝ) ≤ depth₂ := by
        exact_mod_cast hdepth
      simpa [weightedLeafDepthCost] using
        mul_le_mul_of_nonneg_right hdepth_real hx
  | node left right ihl ihr =>
      have hleft : ∀ x ∈ left.leaves, 0 ≤ x := by
        intro x hx
        exact hnonneg x (by simp [leaves, hx])
      have hright : ∀ x ∈ right.leaves, 0 ≤ x := by
        intro x hx
        exact hnonneg x (by simp [leaves, hx])
      have hdepth_succ : depth₁ + 1 ≤ depth₂ + 1 :=
        Nat.succ_le_succ hdepth
      exact add_le_add (ihl hdepth_succ hleft) (ihr hdepth_succ hright)

/-- Weighted-path exchange lemma: if `a <= b`, assigning `a` to the deeper
leaf and `b` to the shallower leaf cannot increase weighted external path
cost. -/
theorem weightedLeafDepthCost_leaf_pair_exchange_le
    {a b : ℝ} {deep shallow : ℕ}
    (hab : a ≤ b) (hdepth : shallow ≤ deep) :
    weightedLeafDepthCost deep (leaf a) +
        weightedLeafDepthCost shallow (leaf b) ≤
      weightedLeafDepthCost deep (leaf b) +
        weightedLeafDepthCost shallow (leaf a) := by
  have hdepth_real : (shallow : ℝ) ≤ deep := by
    exact_mod_cast hdepth
  have hdepth_nonneg : 0 ≤ (deep : ℝ) - shallow := sub_nonneg.mpr hdepth_real
  have hweight_nonneg : 0 ≤ b - a := sub_nonneg.mpr hab
  have hprod :
      0 ≤ ((deep : ℝ) - shallow) * (b - a) :=
    mul_nonneg hdepth_nonneg hweight_nonneg
  have hdiff :
      weightedLeafDepthCost deep (leaf b) +
          weightedLeafDepthCost shallow (leaf a) -
        (weightedLeafDepthCost deep (leaf a) +
          weightedLeafDepthCost shallow (leaf b)) =
        ((deep : ℝ) - shallow) * (b - a) := by
    simp [weightedLeafDepthCost]
    ring
  have hnonneg :
      0 ≤
        weightedLeafDepthCost deep (leaf b) +
            weightedLeafDepthCost shallow (leaf a) -
          (weightedLeafDepthCost deep (leaf a) +
            weightedLeafDepthCost shallow (leaf b)) := by
    rw [hdiff]
    exact hprod
  linarith

/-- Weighted-depth exchange inside an arbitrary explicit leaf-depth context:
if `a <= b` and the first position is no shallower, placing `a` at that deeper
position cannot increase the explicit weighted path cost. -/
theorem weightedDepthPairsCost_pair_exchange_le
    (pre suffix : List (ℕ × ℝ))
    {a b : ℝ} {deep shallow : ℕ}
    (hab : a ≤ b) (hdepth : shallow ≤ deep) :
    weightedDepthPairsCost
        (pre ++ [(deep, a), (shallow, b)] ++ suffix) ≤
      weightedDepthPairsCost
        (pre ++ [(deep, b), (shallow, a)] ++ suffix) := by
  have hexchange :=
    weightedLeafDepthCost_leaf_pair_exchange_le
      (a := a) (b := b) (deep := deep) (shallow := shallow)
      hab hdepth
  simp [weightedDepthPairsCost_append, weightedLeafDepthCost] at hexchange ⊢
  linarith

/-- Weighted-depth exchange for two separated positions in an explicit
leaf-depth context.  If `a <= b` and the first selected position is no
shallower, swapping the weights so that `a` occupies the deeper position cannot
increase the explicit weighted path cost. -/
theorem weightedDepthPairsCost_pair_exchange_separated_le
    (pre middle suffix : List (ℕ × ℝ))
    {a b : ℝ} {deep shallow : ℕ}
    (hab : a ≤ b) (hdepth : shallow ≤ deep) :
    weightedDepthPairsCost
        (pre ++ [(deep, a)] ++ middle ++ [(shallow, b)] ++ suffix) ≤
      weightedDepthPairsCost
        (pre ++ [(deep, b)] ++ middle ++ [(shallow, a)] ++ suffix) := by
  have hexchange :=
    weightedLeafDepthCost_leaf_pair_exchange_le
      (a := a) (b := b) (deep := deep) (shallow := shallow)
      hab hdepth
  simp [weightedDepthPairsCost_append, weightedLeafDepthCost] at hexchange ⊢
  linarith

/-- The one-slot exchange preserves the list of weights. -/
private theorem weightListPerm_pair_exchange {α : Type*}
    (pre middle suffix : List α) (a b : α) :
    (pre ++ [a] ++ middle ++ [b] ++ suffix).Perm
      (pre ++ [b] ++ middle ++ [a] ++ suffix) := by
  have hb :
      (middle ++ b :: suffix).Perm (b :: middle ++ suffix) := by
    exact List.perm_middle (a := b) (l₁ := middle) (l₂ := suffix)
  have hab :
      (a :: b :: middle ++ suffix).Perm
        (b :: a :: middle ++ suffix) := by
    exact (List.Perm.swap a b (middle ++ suffix)).symm
  have ha :
      (a :: middle ++ suffix).Perm (middle ++ a :: suffix) := by
    exact (List.perm_middle (a := a) (l₁ := middle) (l₂ := suffix)).symm
  have htail :
      ([a] ++ middle ++ [b] ++ suffix).Perm
        ([b] ++ middle ++ [a] ++ suffix) := by
    simpa [List.append_assoc] using
      ((List.Perm.cons a hb).trans (hab.trans (List.Perm.cons b ha)))
  simpa [List.append_assoc] using List.Perm.append_left pre htail

/-- Permutation wrapper for the one-slot weighted-depth exchange, bundled with
the leaf-weight multiset invariant. -/
theorem weightedDepthPairsCost_pair_exchange_separated_of_perm_le_and_weights_perm
    {pairs swapped : List (ℕ × ℝ)}
    (pre middle suffix : List (ℕ × ℝ))
    {a b : ℝ} {deep shallow : ℕ}
    (hpairs :
      pairs.Perm (pre ++ [(deep, b)] ++ middle ++ [(shallow, a)] ++ suffix))
    (hswapped :
      swapped.Perm (pre ++ [(deep, a)] ++ middle ++ [(shallow, b)] ++ suffix))
    (hab : a ≤ b) (hdepth : shallow ≤ deep) :
    weightedDepthPairsCost swapped ≤ weightedDepthPairsCost pairs ∧
      (swapped.map Prod.snd).Perm (pairs.map Prod.snd) := by
  constructor
  · rw [weightedDepthPairsCost_eq_of_perm hswapped,
      weightedDepthPairsCost_eq_of_perm hpairs]
    exact weightedDepthPairsCost_pair_exchange_separated_le
      pre middle suffix hab hdepth
  · have hcanonical :
        ((pre ++ [(deep, a)] ++ middle ++
            [(shallow, b)] ++ suffix).map Prod.snd).Perm
          ((pre ++ [(deep, b)] ++ middle ++
            [(shallow, a)] ++ suffix).map Prod.snd) := by
      simpa [List.map_append] using
        (weightListPerm_pair_exchange
          (pre.map Prod.snd) (middle.map Prod.snd)
          (suffix.map Prod.snd) a b)
    exact (hswapped.map Prod.snd).trans (hcanonical.trans (hpairs.map Prod.snd).symm)

/-- Located one-slot exchange.  If a selected small weight `a` is separated
from a deeper context weight `b`, and every residual context weight is at
least `a`, moving `a` into the deeper slot cannot increase weighted-depth cost
and preserves the leaf-weight multiset. -/
theorem weightedDepthPairsCost_pair_exchange_of_context_min_le_and_weights_perm
    {pairs swapped : List (ℕ × ℝ)}
    (pre middle suffix : List (ℕ × ℝ))
    {a b : ℝ} {deep shallow : ℕ}
    (hpairs :
      pairs.Perm (pre ++ [(deep, b)] ++ middle ++ [(shallow, a)] ++ suffix))
    (hswapped :
      swapped.Perm (pre ++ [(deep, a)] ++ middle ++ [(shallow, b)] ++ suffix))
    (hcontext :
      ∀ pair ∈ pre ++ [(deep, b)] ++ middle ++ suffix,
        a ≤ pair.2)
    (hdepth : shallow ≤ deep) :
    weightedDepthPairsCost swapped ≤ weightedDepthPairsCost pairs ∧
      (swapped.map Prod.snd).Perm (pairs.map Prod.snd) := by
  have hab : a ≤ b := hcontext (deep, b) (by simp)
  exact weightedDepthPairsCost_pair_exchange_separated_of_perm_le_and_weights_perm
    pre middle suffix hpairs hswapped hab hdepth

/-- Two-position weighted-depth exchange into adjacent deepest slots.  If
`a <= c` and `b <= d`, and both selected source slots are no deeper than the
adjacent deepest slots, replacing the deepest weights `c, d` by `a, b` cannot
increase explicit weighted-depth cost. -/
theorem weightedDepthPairsCost_two_pair_exchange_separated_le
    (pre middle₁ middle₂ suffix : List (ℕ × ℝ))
    {a b c d : ℝ} {deep shallow₁ shallow₂ : ℕ}
    (hac : a ≤ c) (hbd : b ≤ d)
    (hdepth₁ : shallow₁ ≤ deep) (hdepth₂ : shallow₂ ≤ deep) :
    weightedDepthPairsCost
        (pre ++ [(deep, a), (deep, b)] ++ middle₁ ++
          [(shallow₁, c)] ++ middle₂ ++ [(shallow₂, d)] ++ suffix) ≤
      weightedDepthPairsCost
        (pre ++ [(deep, c), (deep, d)] ++ middle₁ ++
          [(shallow₁, a)] ++ middle₂ ++ [(shallow₂, b)] ++ suffix) := by
  have hdepth₁_real : (shallow₁ : ℝ) ≤ deep := by
    exact_mod_cast hdepth₁
  have hdepth₂_real : (shallow₂ : ℝ) ≤ deep := by
    exact_mod_cast hdepth₂
  have hprod₁ :
      0 ≤ ((deep : ℝ) - shallow₁) * (c - a) :=
    mul_nonneg (sub_nonneg.mpr hdepth₁_real) (sub_nonneg.mpr hac)
  have hprod₂ :
      0 ≤ ((deep : ℝ) - shallow₂) * (d - b) :=
    mul_nonneg (sub_nonneg.mpr hdepth₂_real) (sub_nonneg.mpr hbd)
  have hdiff :
      weightedDepthPairsCost
          (pre ++ [(deep, c), (deep, d)] ++ middle₁ ++
            [(shallow₁, a)] ++ middle₂ ++ [(shallow₂, b)] ++ suffix) -
        weightedDepthPairsCost
          (pre ++ [(deep, a), (deep, b)] ++ middle₁ ++
            [(shallow₁, c)] ++ middle₂ ++ [(shallow₂, d)] ++ suffix) =
        ((deep : ℝ) - shallow₁) * (c - a) +
          ((deep : ℝ) - shallow₂) * (d - b) := by
    simp [weightedDepthPairsCost]
    ring
  have hnonneg :
      0 ≤
        weightedDepthPairsCost
            (pre ++ [(deep, c), (deep, d)] ++ middle₁ ++
              [(shallow₁, a)] ++ middle₂ ++ [(shallow₂, b)] ++ suffix) -
          weightedDepthPairsCost
            (pre ++ [(deep, a), (deep, b)] ++ middle₁ ++
              [(shallow₁, c)] ++ middle₂ ++ [(shallow₂, d)] ++ suffix) := by
    rw [hdiff]
    exact add_nonneg hprod₁ hprod₂
  linarith

/-- Permutation wrapper for the two-slot weighted-depth exchange.  This lets a
later proof arrange an explicit leaf-depth list into a convenient order, apply
the adjacent-deepest-slots exchange, and transfer the result back by cost
invariance under pair permutations. -/
theorem weightedDepthPairsCost_two_pair_exchange_separated_of_perm_le
    {pairs swapped : List (ℕ × ℝ)}
    (pre middle₁ middle₂ suffix : List (ℕ × ℝ))
    {a b c d : ℝ} {deep shallow₁ shallow₂ : ℕ}
    (hpairs :
      pairs.Perm
        (pre ++ [(deep, c), (deep, d)] ++ middle₁ ++
          [(shallow₁, a)] ++ middle₂ ++ [(shallow₂, b)] ++ suffix))
    (hswapped :
      swapped.Perm
        (pre ++ [(deep, a), (deep, b)] ++ middle₁ ++
          [(shallow₁, c)] ++ middle₂ ++ [(shallow₂, d)] ++ suffix))
    (hac : a ≤ c) (hbd : b ≤ d)
    (hdepth₁ : shallow₁ ≤ deep) (hdepth₂ : shallow₂ ≤ deep) :
    weightedDepthPairsCost swapped ≤ weightedDepthPairsCost pairs := by
  rw [weightedDepthPairsCost_eq_of_perm hswapped,
    weightedDepthPairsCost_eq_of_perm hpairs]
  exact weightedDepthPairsCost_two_pair_exchange_separated_le
    pre middle₁ middle₂ suffix hac hbd hdepth₁ hdepth₂

/-- Located two-smallest handoff for the deepest-pair exchange.  Once an
explicit leaf-depth list has been decomposed into a deepest sibling pair, two
selected smallest weights `a, b`, and a residual context whose weights are all
at least `b`, replacing the deepest pair by `a, b` cannot increase the
weighted-depth cost. -/
theorem weightedDepthPairsCost_two_pair_exchange_of_context_min_le
    {pairs swapped : List (ℕ × ℝ)}
    (pre middle₁ middle₂ suffix : List (ℕ × ℝ))
    {a b c d : ℝ} {deep shallow₁ shallow₂ : ℕ}
    (hpairs :
      pairs.Perm
        (pre ++ [(deep, c), (deep, d)] ++ middle₁ ++
          [(shallow₁, a)] ++ middle₂ ++ [(shallow₂, b)] ++ suffix))
    (hswapped :
      swapped.Perm
        (pre ++ [(deep, a), (deep, b)] ++ middle₁ ++
          [(shallow₁, c)] ++ middle₂ ++ [(shallow₂, d)] ++ suffix))
    (hab : a ≤ b)
    (hcontext :
      ∀ pair ∈ pre ++ [(deep, c), (deep, d)] ++ middle₁ ++
          middle₂ ++ suffix,
        b ≤ pair.2)
    (hdepth₁ : shallow₁ ≤ deep) (hdepth₂ : shallow₂ ≤ deep) :
    weightedDepthPairsCost swapped ≤ weightedDepthPairsCost pairs := by
  have hbc : b ≤ c := hcontext (deep, c) (by simp)
  have hbd : b ≤ d := hcontext (deep, d) (by simp)
  exact weightedDepthPairsCost_two_pair_exchange_separated_of_perm_le
    pre middle₁ middle₂ suffix hpairs hswapped
    (le_trans hab hbc) hbd hdepth₁ hdepth₂

/-- The distinguished-weight permutation used by the two-slot exchange keeps
the list of weights unchanged. -/
private theorem weightListPerm_two_pair_exchange {α : Type*}
    (pre middle₁ middle₂ suffix : List α) (a b c d : α) :
    (pre ++ [a, b] ++ middle₁ ++ [c] ++ middle₂ ++ [d] ++ suffix).Perm
      (pre ++ [c, d] ++ middle₁ ++ [a] ++ middle₂ ++ [b] ++ suffix) := by
  have hc :
      (middle₁ ++ c :: middle₂ ++ d :: suffix).Perm
        (c :: middle₁ ++ middle₂ ++ d :: suffix) := by
    simp [List.append_assoc]
  have hd :
      (middle₁ ++ middle₂ ++ d :: suffix).Perm
        (d :: middle₁ ++ middle₂ ++ suffix) := by
    simpa [List.append_assoc] using
      (List.perm_middle (a := d) (l₁ := middle₁ ++ middle₂)
        (l₂ := suffix))
  have hleft :
      ([a, b] ++ middle₁ ++ [c] ++ middle₂ ++ [d] ++ suffix).Perm
        (a :: b :: c :: d :: middle₁ ++ middle₂ ++ suffix) := by
    simpa [List.append_assoc] using
      ((List.Perm.cons a (List.Perm.cons b hc)).trans
        (List.Perm.cons a (List.Perm.cons b (List.Perm.cons c hd))))
  have ha :
      (middle₁ ++ a :: middle₂ ++ b :: suffix).Perm
        (a :: middle₁ ++ middle₂ ++ b :: suffix) := by
    simp [List.append_assoc]
  have hb :
      (middle₁ ++ middle₂ ++ b :: suffix).Perm
        (b :: middle₁ ++ middle₂ ++ suffix) := by
    simpa [List.append_assoc] using
      (List.perm_middle (a := b) (l₁ := middle₁ ++ middle₂)
        (l₂ := suffix))
  have hright_to_cdab :
      ([c, d] ++ middle₁ ++ [a] ++ middle₂ ++ [b] ++ suffix).Perm
        (c :: d :: a :: b :: middle₁ ++ middle₂ ++ suffix) := by
    simpa [List.append_assoc] using
      ((List.Perm.cons c (List.Perm.cons d ha)).trans
        (List.Perm.cons c (List.Perm.cons d (List.Perm.cons a hb))))
  have hcdab_to_acdb :
      (c :: d :: a :: b :: middle₁ ++ middle₂ ++ suffix).Perm
        (a :: c :: d :: b :: middle₁ ++ middle₂ ++ suffix) := by
    exact List.perm_middle (a := a) (l₁ := [c, d])
      (l₂ := b :: middle₁ ++ middle₂ ++ suffix)
  have hacdb_to_abcd :
      (a :: c :: d :: b :: middle₁ ++ middle₂ ++ suffix).Perm
        (a :: b :: c :: d :: middle₁ ++ middle₂ ++ suffix) := by
    exact List.Perm.cons a (by
      exact List.perm_middle (a := b) (l₁ := [c, d])
        (l₂ := middle₁ ++ middle₂ ++ suffix))
  have hright :
      ([c, d] ++ middle₁ ++ [a] ++ middle₂ ++ [b] ++ suffix).Perm
        (a :: b :: c :: d :: middle₁ ++ middle₂ ++ suffix) :=
    (hright_to_cdab.trans hcdab_to_acdb).trans hacdb_to_abcd
  simpa [List.append_assoc] using
    (List.Perm.append_left pre (hleft.trans hright.symm))

/-- Move two selected entries from a displayed context to the front, leaving
the residual context behind them. -/
private theorem listPerm_two_selected_to_front {α : Type*}
    (pre middle₁ middle₂ suffix : List α)
    (deep₁ deep₂ selected₁ selected₂ : α) :
    (pre ++ [deep₁, deep₂] ++ middle₁ ++ [selected₁] ++
        middle₂ ++ [selected₂] ++ suffix).Perm
      (selected₁ :: selected₂ ::
        pre ++ [deep₁, deep₂] ++ middle₁ ++ middle₂ ++ suffix) := by
  have hselected₁ :
      ((pre ++ [deep₁, deep₂] ++ middle₁) ++
          selected₁ :: (middle₂ ++ selected₂ :: suffix)).Perm
        (selected₁ ::
          ((pre ++ [deep₁, deep₂] ++ middle₁) ++
            (middle₂ ++ selected₂ :: suffix))) := by
    exact List.perm_middle (a := selected₁)
      (l₁ := pre ++ [deep₁, deep₂] ++ middle₁)
      (l₂ := middle₂ ++ selected₂ :: suffix)
  have hselected₂ :
      (pre ++ [deep₁, deep₂] ++ middle₁ ++ middle₂ ++
          selected₂ :: suffix).Perm
        (selected₂ :: pre ++ [deep₁, deep₂] ++ middle₁ ++
          middle₂ ++ suffix) := by
    simpa [List.append_assoc] using
      (List.perm_middle (a := selected₂)
        (l₁ := pre ++ [deep₁, deep₂] ++ middle₁ ++ middle₂)
        (l₂ := suffix))
  have hselected₂' :
      ((pre ++ [deep₁, deep₂] ++ middle₁) ++
          (middle₂ ++ selected₂ :: suffix)).Perm
        (selected₂ ::
          ((pre ++ [deep₁, deep₂] ++ middle₁) ++ middle₂ ++ suffix)) := by
    simpa [List.append_assoc] using hselected₂
  simpa [List.append_assoc] using
    (hselected₁.trans (List.Perm.cons selected₁ hselected₂'))

/-- Reorder the orientation where two selected slots appear before the
displayed deepest pair into the canonical deepest-pair-first order. -/
private theorem listPerm_two_selected_before_deepest_to_canonical {α : Type*}
    (pre middle₁ middle₂ suffix : List α)
    (deep₁ deep₂ selected₁ selected₂ : α) :
    (pre ++ [selected₁] ++ middle₁ ++ [selected₂] ++ middle₂ ++
        [deep₁, deep₂] ++ suffix).Perm
      (pre ++ [deep₁, deep₂] ++ middle₁ ++ [selected₁] ++
        middle₂ ++ [selected₂] ++ suffix) := by
  have hdeep₁ :
      ([selected₁] ++ middle₁ ++ [selected₂] ++ middle₂ ++
          [deep₁, deep₂] ++ suffix).Perm
        (deep₁ ::
          ([selected₁] ++ middle₁ ++ [selected₂] ++ middle₂ ++
            [deep₂] ++ suffix)) := by
    simpa [List.append_assoc] using
      (List.perm_middle (a := deep₁)
        (l₁ := [selected₁] ++ middle₁ ++ [selected₂] ++ middle₂)
        (l₂ := deep₂ :: suffix))
  have hdeep₂ :
      ([selected₁] ++ middle₁ ++ [selected₂] ++ middle₂ ++
          [deep₂] ++ suffix).Perm
        (deep₂ ::
          ([selected₁] ++ middle₁ ++ [selected₂] ++ middle₂ ++
            suffix)) := by
    simpa [List.append_assoc] using
      (List.perm_middle (a := deep₂)
        (l₁ := [selected₁] ++ middle₁ ++ [selected₂] ++ middle₂)
        (l₂ := suffix))
  have hselected₁ :
      (selected₁ :: (middle₁ ++ selected₂ :: middle₂ ++ suffix)).Perm
        (middle₁ ++ selected₁ :: selected₂ :: middle₂ ++ suffix) := by
    simpa [List.append_assoc] using
      (List.perm_middle (a := selected₁)
        (l₁ := middle₁)
        (l₂ := selected₂ :: middle₂ ++ suffix)).symm
  have hselected₂ :
      (selected₂ :: middle₂ ++ suffix).Perm
        (middle₂ ++ selected₂ :: suffix) := by
    simpa [List.append_assoc] using
      (List.perm_middle (a := selected₂)
        (l₁ := middle₂) (l₂ := suffix)).symm
  have hrest :
      ([selected₁] ++ middle₁ ++ [selected₂] ++ middle₂ ++
          suffix).Perm
        (middle₁ ++ [selected₁] ++ middle₂ ++ [selected₂] ++
          suffix) := by
    have hselected₂' :
        (middle₁ ++ selected₁ :: selected₂ :: middle₂ ++ suffix).Perm
          (middle₁ ++ [selected₁] ++ middle₂ ++ [selected₂] ++
            suffix) := by
      simpa [List.append_assoc] using
        List.Perm.append_left (middle₁ ++ [selected₁]) hselected₂
    simpa [List.append_assoc] using hselected₁.trans hselected₂'
  have htail :
      ([selected₁] ++ middle₁ ++ [selected₂] ++ middle₂ ++
          [deep₁, deep₂] ++ suffix).Perm
        (deep₁ :: deep₂ ::
          (middle₁ ++ [selected₁] ++ middle₂ ++ [selected₂] ++
            suffix)) :=
    hdeep₁.trans ((List.Perm.cons deep₁ hdeep₂).trans
      (List.Perm.cons deep₁ (List.Perm.cons deep₂ hrest)))
  simpa [List.append_assoc] using List.Perm.append_left pre htail

/-- Reorder the mixed orientation where the first selected slot appears before
the displayed deepest pair and the second selected slot appears after it into
the canonical deepest-pair-first order. -/
private theorem listPerm_selected_before_deepest_before_selected_to_canonical
    {α : Type*}
    (pre middle₁ middle₂ suffix : List α)
    (deep₁ deep₂ selected₁ selected₂ : α) :
    (pre ++ [selected₁] ++ middle₁ ++ [deep₁, deep₂] ++ middle₂ ++
        [selected₂] ++ suffix).Perm
      (pre ++ [deep₁, deep₂] ++ middle₁ ++ [selected₁] ++
        middle₂ ++ [selected₂] ++ suffix) := by
  have hdeep₁ :
      ([selected₁] ++ middle₁ ++ [deep₁, deep₂] ++ middle₂ ++
          [selected₂] ++ suffix).Perm
        (deep₁ ::
          ([selected₁] ++ middle₁ ++ [deep₂] ++ middle₂ ++
            [selected₂] ++ suffix)) := by
    simpa [List.append_assoc] using
      (List.perm_middle (a := deep₁)
        (l₁ := [selected₁] ++ middle₁)
        (l₂ := deep₂ :: middle₂ ++ selected₂ :: suffix))
  have hdeep₂ :
      ([selected₁] ++ middle₁ ++ [deep₂] ++ middle₂ ++
          [selected₂] ++ suffix).Perm
        (deep₂ ::
          ([selected₁] ++ middle₁ ++ middle₂ ++ [selected₂] ++
            suffix)) := by
    simpa [List.append_assoc] using
      (List.perm_middle (a := deep₂)
        (l₁ := [selected₁] ++ middle₁)
        (l₂ := middle₂ ++ selected₂ :: suffix))
  have hselected₁ :
      ([selected₁] ++ middle₁ ++ middle₂ ++ [selected₂] ++
          suffix).Perm
        (middle₁ ++ [selected₁] ++ middle₂ ++ [selected₂] ++
          suffix) := by
    have hmove :
        (selected₁ ::
            (middle₁ ++ middle₂ ++ selected₂ :: suffix)).Perm
          (middle₁ ++ selected₁ :: middle₂ ++ selected₂ :: suffix) := by
      simpa [List.append_assoc] using
        (List.perm_middle (a := selected₁)
          (l₁ := middle₁)
          (l₂ := middle₂ ++ selected₂ :: suffix)).symm
    simpa [List.append_assoc] using hmove
  have htail :
      ([selected₁] ++ middle₁ ++ [deep₁, deep₂] ++ middle₂ ++
          [selected₂] ++ suffix).Perm
        (deep₁ :: deep₂ ::
          (middle₁ ++ [selected₁] ++ middle₂ ++ [selected₂] ++
            suffix)) :=
    hdeep₁.trans ((List.Perm.cons deep₁ hdeep₂).trans
      (List.Perm.cons deep₁ (List.Perm.cons deep₂ hselected₁)))
  simpa [List.append_assoc] using List.Perm.append_left pre htail

/-- Move two displayed selected slots to the front, leaving their residual
context in order. -/
private theorem listPerm_two_selected_slots_to_front {α : Type*}
    (pre middle suffix : List α) (selected later : α) :
    (pre ++ [selected] ++ middle ++ [later] ++ suffix).Perm
      (selected :: later :: pre ++ middle ++ suffix) := by
  have hselected :
      (pre ++ selected :: (middle ++ later :: suffix)).Perm
        (selected :: (pre ++ (middle ++ later :: suffix))) := by
    exact List.perm_middle (a := selected) (l₁ := pre)
      (l₂ := middle ++ later :: suffix)
  have hlater :
      (pre ++ middle ++ later :: suffix).Perm
        (later :: pre ++ middle ++ suffix) := by
    simpa [List.append_assoc] using
      (List.perm_middle (a := later) (l₁ := pre ++ middle)
        (l₂ := suffix))
  have hlater' :
      (pre ++ (middle ++ later :: suffix)).Perm
        (later :: (pre ++ middle ++ suffix)) := by
    simpa [List.append_assoc] using hlater
  simpa [List.append_assoc] using
    (hselected.trans (List.Perm.cons selected hlater'))

/-- Move two displayed selected slots to the front in reverse order. -/
private theorem listPerm_two_selected_slots_to_front_reverse {α : Type*}
    (pre middle suffix : List α) (selected later : α) :
    (pre ++ [selected] ++ middle ++ [later] ++ suffix).Perm
      (later :: selected :: pre ++ middle ++ suffix) := by
  have hfront :=
    listPerm_two_selected_slots_to_front pre middle suffix selected later
  exact hfront.trans (List.Perm.swap later selected (pre ++ middle ++ suffix))

/-- Move a selected entry that appears before a displayed adjacent pair to the
matching context where the adjacent pair appears first. -/
private theorem listPerm_selected_before_adjacent_to_after {α : Type*}
    (pre middle suffix : List α) (selected left right : α) :
    (pre ++ [selected] ++ middle ++ [left, right] ++ suffix).Perm
      (pre ++ [left, right] ++ middle ++ [selected] ++ suffix) := by
  have hleft :
      ([selected] ++ middle ++ [left, right] ++ suffix).Perm
        (left :: ([selected] ++ middle ++ [right] ++ suffix)) := by
    simpa [List.append_assoc] using
      (List.perm_middle (a := left) (l₁ := [selected] ++ middle)
        (l₂ := right :: suffix))
  have hright :
      ([selected] ++ middle ++ [right] ++ suffix).Perm
        (right :: ([selected] ++ middle ++ suffix)) := by
    simpa [List.append_assoc] using
      (List.perm_middle (a := right) (l₁ := [selected] ++ middle)
        (l₂ := suffix))
  have hselected :
      ([selected] ++ middle ++ suffix).Perm
        (middle ++ [selected] ++ suffix) := by
    simpa [List.append_assoc] using
      (List.perm_middle (a := selected) (l₁ := middle)
        (l₂ := suffix)).symm
  have htail :
      ([selected] ++ middle ++ [left, right] ++ suffix).Perm
        (left :: right :: middle ++ [selected] ++ suffix) :=
    hleft.trans
      ((List.Perm.cons left hright).trans
        (List.Perm.cons left (List.Perm.cons right hselected)))
  simpa [List.append_assoc] using List.Perm.append_left pre htail

/-- Display an occurrence of an element known to be in a list. -/
private theorem exists_split_of_mem {α : Type*} {a : α} :
    ∀ xs : List α, a ∈ xs → ∃ pre suffix : List α,
      xs = pre ++ a :: suffix
  | [], h => by
      simp at h
  | x :: xs, h => by
      simp at h
      rcases h with rfl | hx
      · exact ⟨[], xs, rfl⟩
      · obtain ⟨pre, suffix, hsplit⟩ :=
          exists_split_of_mem xs hx
        exact ⟨x :: pre, suffix, by simp [hsplit]⟩

/-- Locate a selected entry relative to a displayed adjacent pair. -/
theorem exists_selected_relative_to_adjacent_pair {α : Type*}
    (pre suffix : List α) (left right selected : α)
    (hmem : selected ∈ pre ++ [left, right] ++ suffix) :
    (∃ before middle : List α,
        pre = before ++ selected :: middle ∧
          pre ++ [left, right] ++ suffix =
            before ++ [selected] ++ middle ++ [left, right] ++ suffix) ∨
      selected = left ∨ selected = right ∨
        ∃ middle after : List α,
          suffix = middle ++ selected :: after ∧
            pre ++ [left, right] ++ suffix =
              pre ++ [left, right] ++ middle ++ [selected] ++ after := by
  have hcases :
      selected ∈ pre ∨ selected = left ∨ selected = right ∨
        selected ∈ suffix := by
    simpa [List.mem_append] using hmem
  rcases hcases with hpre | hleft | hright | hsuffix
  · obtain ⟨before, middle, hsplit⟩ :=
      exists_split_of_mem pre hpre
    left
    refine ⟨before, middle, hsplit, ?_⟩
    rw [hsplit]
    simp [List.append_assoc]
  · right
    left
    exact hleft
  · right
    right
    left
    exact hright
  · obtain ⟨middle, after, hsplit⟩ :=
      exists_split_of_mem suffix hsuffix
    right
    right
    right
    refine ⟨middle, after, hsplit, ?_⟩
    rw [hsplit]
    simp [List.append_assoc]

/-- Locate the two distinguished head elements of a permutation as two
displayed slots of the original list, in either occurrence order.  The residual
context is permuted with the remaining tail. -/
theorem exists_two_selected_slots_of_perm_cons_cons {α : Type*}
    {pairs rest : List α} {first second : α}
    (hperm : pairs.Perm (first :: second :: rest)) :
    (∃ pre middle suffix : List α,
        pairs = pre ++ [first] ++ middle ++ [second] ++ suffix ∧
          rest.Perm (pre ++ middle ++ suffix)) ∨
      ∃ pre middle suffix : List α,
        pairs = pre ++ [second] ++ middle ++ [first] ++ suffix ∧
          rest.Perm (pre ++ middle ++ suffix) := by
  have hfirst : first ∈ pairs := (hperm.mem_iff).2 (by simp)
  obtain ⟨pre, tail, hpairs⟩ :=
    exists_split_of_mem pairs hfirst
  have hpairsFront : pairs.Perm (first :: pre ++ tail) := by
    rw [hpairs]
    exact List.perm_middle (a := first) (l₁ := pre) (l₂ := tail)
  have htailPerm : (pre ++ tail).Perm (second :: rest) :=
    List.Perm.cons_inv (hpairsFront.symm.trans hperm)
  have hsecond : second ∈ pre ∨ second ∈ tail := by
    have hmem : second ∈ pre ++ tail :=
      (htailPerm.mem_iff).2 (by simp)
    simpa [List.mem_append] using hmem
  rcases hsecond with hsecondPre | hsecondTail
  · obtain ⟨pre₂, middle, hpre⟩ :=
      exists_split_of_mem pre hsecondPre
    right
    refine ⟨pre₂, middle, tail, ?_, ?_⟩
    · rw [hpairs, hpre]
      simp [List.append_assoc]
    · have htailPerm' :
          (pre₂ ++ second :: middle ++ tail).Perm (second :: rest) := by
        simpa [hpre, List.append_assoc] using htailPerm
      have hmove :
          (pre₂ ++ second :: middle ++ tail).Perm
            (second :: pre₂ ++ middle ++ tail) := by
        simp [List.append_assoc]
      have hfrontRest :
          (second :: pre₂ ++ middle ++ tail).Perm (second :: rest) :=
        hmove.symm.trans htailPerm'
      exact (List.Perm.cons_inv hfrontRest).symm
  · obtain ⟨middle, suffix, htail⟩ :=
      exists_split_of_mem tail hsecondTail
    left
    refine ⟨pre, middle, suffix, ?_, ?_⟩
    · rw [hpairs, htail]
      simp [List.append_assoc]
    · have htailPerm' :
          (pre ++ middle ++ second :: suffix).Perm (second :: rest) := by
        simpa [htail, List.append_assoc] using htailPerm
      have hmove :
          (pre ++ middle ++ second :: suffix).Perm
            (second :: pre ++ middle ++ suffix) := by
        simpa [List.append_assoc] using
          (List.perm_middle (a := second) (l₁ := pre ++ middle)
            (l₂ := suffix))
      have hfrontRest :
          (second :: pre ++ middle ++ suffix).Perm (second :: rest) :=
        hmove.symm.trans htailPerm'
      exact (List.Perm.cons_inv hfrontRest).symm

/-- If the first distinguished occurrence is displayed before an adjacent
pair, then the second distinguished occurrence is either before the first,
between the first and the adjacent pair, or after the adjacent pair. -/
theorem exists_second_position_of_first_before_adjacent_pair
    {α : Type*} {pairs rest : List α} {first second left right : α}
    (before middle suffix : List α)
    (hpairs :
      pairs = before ++ [first] ++ middle ++ [left, right] ++ suffix)
    (hperm : pairs.Perm (first :: second :: rest))
    (hsecond_ne_left : second ≠ left)
    (hsecond_ne_right : second ≠ right) :
    (∃ pre gap : List α,
        before = pre ++ second :: gap ∧
          pairs =
            pre ++ [second] ++ gap ++ [first] ++ middle ++
              [left, right] ++ suffix) ∨
      (∃ gap tail : List α,
        middle = gap ++ second :: tail ∧
          pairs =
            before ++ [first] ++ gap ++ [second] ++ tail ++
              [left, right] ++ suffix) ∨
        ∃ gap tail : List α,
          suffix = gap ++ second :: tail ∧
            pairs =
              before ++ [first] ++ middle ++ [left, right] ++
                gap ++ [second] ++ tail := by
  have hpairsFront :
      pairs.Perm
        (first :: before ++ middle ++ [left, right] ++ suffix) := by
    rw [hpairs]
    simp [List.append_assoc]
  have htailPerm :
      (before ++ middle ++ [left, right] ++ suffix).Perm
        (second :: rest) :=
    List.Perm.cons_inv (hpairsFront.symm.trans hperm)
  have hsecond_mem :
      second ∈ before ++ middle ++ [left, right] ++ suffix :=
    (htailPerm.mem_iff).2 (by simp)
  simp [List.mem_append] at hsecond_mem
  rcases hsecond_mem with
    hbefore | hmiddle | hleft | hright | hsuffix
  · obtain ⟨pre, gap, hsplit⟩ :=
      exists_split_of_mem before hbefore
    left
    refine ⟨pre, gap, hsplit, ?_⟩
    rw [hpairs, hsplit]
    simp [List.append_assoc]
  · obtain ⟨gap, tail, hsplit⟩ :=
      exists_split_of_mem middle hmiddle
    right
    left
    refine ⟨gap, tail, hsplit, ?_⟩
    rw [hpairs, hsplit]
    simp [List.append_assoc]
  · exact False.elim (hsecond_ne_left hleft)
  · exact False.elim (hsecond_ne_right hright)
  · obtain ⟨gap, tail, hsplit⟩ :=
      exists_split_of_mem suffix hsuffix
    right
    right
    refine ⟨gap, tail, hsplit, ?_⟩
    rw [hpairs, hsplit]
    simp [List.append_assoc]

/-- If the first distinguished occurrence is displayed after an adjacent pair,
then the second distinguished occurrence is either before the adjacent pair,
between the adjacent pair and the first, or after the first. -/
theorem exists_second_position_of_first_after_adjacent_pair
    {α : Type*} {pairs rest : List α} {first second left right : α}
    (before middle suffix : List α)
    (hpairs :
      pairs = before ++ [left, right] ++ middle ++ [first] ++ suffix)
    (hperm : pairs.Perm (first :: second :: rest))
    (hsecond_ne_left : second ≠ left)
    (hsecond_ne_right : second ≠ right) :
    (∃ pre gap : List α,
        before = pre ++ second :: gap ∧
          pairs =
            pre ++ [second] ++ gap ++ [left, right] ++ middle ++
              [first] ++ suffix) ∨
      (∃ gap tail : List α,
        middle = gap ++ second :: tail ∧
          pairs =
            before ++ [left, right] ++ gap ++ [second] ++ tail ++
              [first] ++ suffix) ∨
        ∃ gap tail : List α,
          suffix = gap ++ second :: tail ∧
            pairs =
              before ++ [left, right] ++ middle ++ [first] ++
                gap ++ [second] ++ tail := by
  have hpairsFront :
      pairs.Perm
        (first :: before ++ [left, right] ++ middle ++ suffix) := by
    rw [hpairs]
    simpa [List.append_assoc] using
      (List.perm_middle (a := first)
        (l₁ := before ++ [left, right] ++ middle) (l₂ := suffix))
  have htailPerm :
      (before ++ [left, right] ++ middle ++ suffix).Perm
        (second :: rest) :=
    List.Perm.cons_inv (hpairsFront.symm.trans hperm)
  have hsecond_mem :
      second ∈ before ++ [left, right] ++ middle ++ suffix :=
    (htailPerm.mem_iff).2 (by simp)
  simp [List.mem_append] at hsecond_mem
  rcases hsecond_mem with
    hbefore | hleft | hright | hmiddle | hsuffix
  · obtain ⟨pre, gap, hsplit⟩ :=
      exists_split_of_mem before hbefore
    left
    refine ⟨pre, gap, hsplit, ?_⟩
    rw [hpairs, hsplit]
    simp [List.append_assoc]
  · exact False.elim (hsecond_ne_left hleft)
  · exact False.elim (hsecond_ne_right hright)
  · obtain ⟨gap, tail, hsplit⟩ :=
      exists_split_of_mem middle hmiddle
    right
    left
    refine ⟨gap, tail, hsplit, ?_⟩
    rw [hpairs, hsplit]
    simp [List.append_assoc]
  · obtain ⟨gap, tail, hsplit⟩ :=
      exists_split_of_mem suffix hsuffix
    right
    right
    refine ⟨gap, tail, hsplit, ?_⟩
    rw [hpairs, hsplit]
    simp [List.append_assoc]

/-- Located two-smallest deepest-pair exchange, bundled with the leaf-weight
multiset invariant needed by the subsequent tree-assembly step. -/
theorem weightedDepthPairsCost_two_pair_exchange_of_context_min_le_and_weights_perm
    {pairs swapped : List (ℕ × ℝ)}
    (pre middle₁ middle₂ suffix : List (ℕ × ℝ))
    {a b c d : ℝ} {deep shallow₁ shallow₂ : ℕ}
    (hpairs :
      pairs.Perm
        (pre ++ [(deep, c), (deep, d)] ++ middle₁ ++
          [(shallow₁, a)] ++ middle₂ ++ [(shallow₂, b)] ++ suffix))
    (hswapped :
      swapped.Perm
        (pre ++ [(deep, a), (deep, b)] ++ middle₁ ++
          [(shallow₁, c)] ++ middle₂ ++ [(shallow₂, d)] ++ suffix))
    (hab : a ≤ b)
    (hcontext :
      ∀ pair ∈ pre ++ [(deep, c), (deep, d)] ++ middle₁ ++
          middle₂ ++ suffix,
        b ≤ pair.2)
    (hdepth₁ : shallow₁ ≤ deep) (hdepth₂ : shallow₂ ≤ deep) :
    weightedDepthPairsCost swapped ≤ weightedDepthPairsCost pairs ∧
      (swapped.map Prod.snd).Perm (pairs.map Prod.snd) := by
  constructor
  · exact weightedDepthPairsCost_two_pair_exchange_of_context_min_le
      pre middle₁ middle₂ suffix hpairs hswapped hab hcontext hdepth₁ hdepth₂
  · have hcanonical :
        ((pre ++ [(deep, a), (deep, b)] ++ middle₁ ++
            [(shallow₁, c)] ++ middle₂ ++
              [(shallow₂, d)] ++ suffix).map Prod.snd).Perm
          ((pre ++ [(deep, c), (deep, d)] ++ middle₁ ++
            [(shallow₁, a)] ++ middle₂ ++
              [(shallow₂, b)] ++ suffix).map Prod.snd) := by
      simpa [List.map_append] using
        (weightListPerm_two_pair_exchange
          (pre.map Prod.snd) (middle₁.map Prod.snd)
          (middle₂.map Prod.snd) (suffix.map Prod.snd) a b c d)
    exact (hswapped.map Prod.snd).trans (hcanonical.trans (hpairs.map Prod.snd).symm)

/-- Nondegenerate two-smallest deepest-pair exchange.  If a fixed deepest
sibling pair has been displayed and the finite two-smallest decomposition has
selected two other displayed slots with residual weights all at least `b`,
then the located exchange both preserves the leaf-weight multiset and does not
increase explicit weighted-depth cost. -/
theorem
    weightedDepthPairsCost_two_pair_exchange_of_two_smallest_decomposition_le_and_weights_perm
    {pairs swapped rest : List (ℕ × ℝ)}
    (pre middle₁ middle₂ suffix : List (ℕ × ℝ))
    {a b c d : ℝ} {deep shallow₁ shallow₂ : ℕ}
    (hpairs :
      pairs.Perm
        (pre ++ [(deep, c), (deep, d)] ++ middle₁ ++
          [(shallow₁, a)] ++ middle₂ ++ [(shallow₂, b)] ++ suffix))
    (hswapped :
      swapped.Perm
        (pre ++ [(deep, a), (deep, b)] ++ middle₁ ++
          [(shallow₁, c)] ++ middle₂ ++ [(shallow₂, d)] ++ suffix))
    (htwoSmallest :
      pairs.Perm ((shallow₁, a) :: (shallow₂, b) :: rest))
    (hab : a ≤ b)
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth₁ : shallow₁ ≤ deep) (hdepth₂ : shallow₂ ≤ deep) :
    weightedDepthPairsCost swapped ≤ weightedDepthPairsCost pairs ∧
      (swapped.map Prod.snd).Perm (pairs.map Prod.snd) := by
  let context :=
    pre ++ [(deep, c), (deep, d)] ++ middle₁ ++ middle₂ ++ suffix
  have hfront :
      (pre ++ [(deep, c), (deep, d)] ++ middle₁ ++
          [(shallow₁, a)] ++ middle₂ ++ [(shallow₂, b)] ++ suffix).Perm
        ((shallow₁, a) :: (shallow₂, b) :: context) := by
    simpa [context, List.append_assoc] using
      (listPerm_two_selected_to_front
        (pre := pre) (middle₁ := middle₁) (middle₂ := middle₂)
        (suffix := suffix)
        (deep₁ := (deep, c)) (deep₂ := (deep, d))
        (selected₁ := (shallow₁, a)) (selected₂ := (shallow₂, b)))
  have hrest_context : rest.Perm context := by
    have hfront_from_rest :
        ((shallow₁, a) :: (shallow₂, b) :: rest).Perm
          ((shallow₁, a) :: (shallow₂, b) :: context) :=
      (htwoSmallest.symm.trans hpairs).trans hfront
    exact List.Perm.cons_inv (List.Perm.cons_inv hfront_from_rest)
  have hcontext :
      ∀ pair ∈ pre ++ [(deep, c), (deep, d)] ++ middle₁ ++
          middle₂ ++ suffix,
        b ≤ pair.2 := by
    intro pair hmem
    exact hrest pair ((hrest_context.mem_iff).2 (by simpa [context] using hmem))
  exact weightedDepthPairsCost_two_pair_exchange_of_context_min_le_and_weights_perm
    pre middle₁ middle₂ suffix hpairs hswapped hab hcontext hdepth₁ hdepth₂

/-- Overlap branch for the deepest-pair exchange: the first two-smallest entry
is already the left deepest sibling, so only the second two-smallest entry is
moved into the right deepest slot. -/
theorem
    weightedDepthPairsCost_pair_exchange_of_left_deepest_two_smallest_decomposition_le_and_weights_perm
    {pairs swapped rest : List (ℕ × ℝ)}
    (pre middle suffix : List (ℕ × ℝ))
    {a b c : ℝ} {deep shallow : ℕ}
    (hpairs :
      pairs.Perm
        (pre ++ [(deep, a), (deep, c)] ++ middle ++
          [(shallow, b)] ++ suffix))
    (hswapped :
      swapped.Perm
        (pre ++ [(deep, a), (deep, b)] ++ middle ++
          [(shallow, c)] ++ suffix))
    (htwoSmallest : pairs.Perm ((deep, a) :: (shallow, b) :: rest))
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth : shallow ≤ deep) :
    weightedDepthPairsCost swapped ≤ weightedDepthPairsCost pairs ∧
      (swapped.map Prod.snd).Perm (pairs.map Prod.snd) := by
  let context := pre ++ [(deep, c)] ++ middle ++ suffix
  have hfront :
      (pre ++ [(deep, a), (deep, c)] ++ middle ++
          [(shallow, b)] ++ suffix).Perm
        ((deep, a) :: (shallow, b) :: context) := by
    simpa [context, List.append_assoc] using
      (listPerm_two_selected_slots_to_front
        (pre := pre) (middle := [(deep, c)] ++ middle)
        (suffix := suffix) (selected := (deep, a))
        (later := (shallow, b)))
  have hrest_context : rest.Perm context := by
    have hfront_from_rest :
        ((deep, a) :: (shallow, b) :: rest).Perm
          ((deep, a) :: (shallow, b) :: context) :=
      (htwoSmallest.symm.trans hpairs).trans hfront
    exact List.Perm.cons_inv (List.Perm.cons_inv hfront_from_rest)
  have hbc : b ≤ c :=
    hrest (deep, c) ((hrest_context.mem_iff).2 (by simp [context]))
  have hpairs' :
      pairs.Perm
        ((pre ++ [(deep, a)]) ++ [(deep, c)] ++ middle ++
          [(shallow, b)] ++ suffix) := by
    simpa [List.append_assoc] using hpairs
  have hswapped' :
      swapped.Perm
        ((pre ++ [(deep, a)]) ++ [(deep, b)] ++ middle ++
          [(shallow, c)] ++ suffix) := by
    simpa [List.append_assoc] using hswapped
  exact weightedDepthPairsCost_pair_exchange_separated_of_perm_le_and_weights_perm
    (pre ++ [(deep, a)]) middle suffix hpairs' hswapped' hbc hdepth

/-- Overlap branch for the deepest-pair exchange: the first two-smallest entry
is already the right deepest sibling, so only the second two-smallest entry is
moved into the left deepest slot. -/
theorem
    weightedDepthPairsCost_pair_exchange_of_right_deepest_two_smallest_decomposition_le_and_weights_perm
    {pairs swapped rest : List (ℕ × ℝ)}
    (pre middle suffix : List (ℕ × ℝ))
    {a b c : ℝ} {deep shallow : ℕ}
    (hpairs :
      pairs.Perm
        (pre ++ [(deep, c), (deep, a)] ++ middle ++
          [(shallow, b)] ++ suffix))
    (hswapped :
      swapped.Perm
        (pre ++ [(deep, b), (deep, a)] ++ middle ++
          [(shallow, c)] ++ suffix))
    (htwoSmallest : pairs.Perm ((deep, a) :: (shallow, b) :: rest))
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth : shallow ≤ deep) :
    weightedDepthPairsCost swapped ≤ weightedDepthPairsCost pairs ∧
      (swapped.map Prod.snd).Perm (pairs.map Prod.snd) := by
  let context := pre ++ [(deep, c)] ++ middle ++ suffix
  have hfront :
      (pre ++ [(deep, c), (deep, a)] ++ middle ++
          [(shallow, b)] ++ suffix).Perm
        ((deep, a) :: (shallow, b) :: context) := by
    simpa [context, List.append_assoc] using
      (listPerm_two_selected_slots_to_front
        (pre := pre ++ [(deep, c)]) (middle := middle)
        (suffix := suffix) (selected := (deep, a))
        (later := (shallow, b)))
  have hrest_context : rest.Perm context := by
    have hfront_from_rest :
        ((deep, a) :: (shallow, b) :: rest).Perm
          ((deep, a) :: (shallow, b) :: context) :=
      (htwoSmallest.symm.trans hpairs).trans hfront
    exact List.Perm.cons_inv (List.Perm.cons_inv hfront_from_rest)
  have hbc : b ≤ c :=
    hrest (deep, c) ((hrest_context.mem_iff).2 (by simp [context]))
  have hpairs' :
      pairs.Perm
        (pre ++ [(deep, c)] ++ ([(deep, a)] ++ middle) ++
          [(shallow, b)] ++ suffix) := by
    simpa [List.append_assoc] using hpairs
  have hswapped' :
      swapped.Perm
        (pre ++ [(deep, b)] ++ ([(deep, a)] ++ middle) ++
          [(shallow, c)] ++ suffix) := by
    simpa [List.append_assoc] using hswapped
  exact weightedDepthPairsCost_pair_exchange_separated_of_perm_le_and_weights_perm
    pre ([(deep, a)] ++ middle) suffix hpairs' hswapped' hbc hdepth

/-- Overlap branch for the deepest-pair exchange: the second two-smallest entry
is already the left deepest sibling, so the first two-smallest entry is moved
into the right deepest slot. -/
theorem
    weightedDepthPairsCost_pair_exchange_of_left_deepest_second_two_smallest_decomposition_le_and_weights_perm
    {pairs swapped rest : List (ℕ × ℝ)}
    (pre middle suffix : List (ℕ × ℝ))
    {a b c : ℝ} {deep shallow : ℕ}
    (hpairs :
      pairs.Perm
        (pre ++ [(deep, b), (deep, c)] ++ middle ++
          [(shallow, a)] ++ suffix))
    (hswapped :
      swapped.Perm
        (pre ++ [(deep, b), (deep, a)] ++ middle ++
          [(shallow, c)] ++ suffix))
    (htwoSmallest : pairs.Perm ((shallow, a) :: (deep, b) :: rest))
    (hab : a ≤ b)
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth : shallow ≤ deep) :
    weightedDepthPairsCost swapped ≤ weightedDepthPairsCost pairs ∧
      (swapped.map Prod.snd).Perm (pairs.map Prod.snd) := by
  let context := pre ++ [(deep, c)] ++ middle ++ suffix
  have hfront :
      (pre ++ [(deep, b), (deep, c)] ++ middle ++
          [(shallow, a)] ++ suffix).Perm
        ((shallow, a) :: (deep, b) :: context) := by
    simpa [context, List.append_assoc] using
      (listPerm_two_selected_slots_to_front_reverse
        (pre := pre) (middle := [(deep, c)] ++ middle)
        (suffix := suffix) (selected := (deep, b))
        (later := (shallow, a)))
  have hrest_context : rest.Perm context := by
    have hfront_from_rest :
        ((shallow, a) :: (deep, b) :: rest).Perm
          ((shallow, a) :: (deep, b) :: context) :=
      (htwoSmallest.symm.trans hpairs).trans hfront
    exact List.Perm.cons_inv (List.Perm.cons_inv hfront_from_rest)
  have hbc : b ≤ c :=
    hrest (deep, c) ((hrest_context.mem_iff).2 (by simp [context]))
  have hac : a ≤ c := le_trans hab hbc
  have hpairs' :
      pairs.Perm
        ((pre ++ [(deep, b)]) ++ [(deep, c)] ++ middle ++
          [(shallow, a)] ++ suffix) := by
    simpa [List.append_assoc] using hpairs
  have hswapped' :
      swapped.Perm
        ((pre ++ [(deep, b)]) ++ [(deep, a)] ++ middle ++
          [(shallow, c)] ++ suffix) := by
    simpa [List.append_assoc] using hswapped
  exact weightedDepthPairsCost_pair_exchange_separated_of_perm_le_and_weights_perm
    (pre ++ [(deep, b)]) middle suffix hpairs' hswapped' hac hdepth

/-- Overlap branch for the deepest-pair exchange: the second two-smallest entry
is already the right deepest sibling, so the first two-smallest entry is moved
into the left deepest slot. -/
theorem
    weightedDepthPairsCost_pair_exchange_of_right_deepest_second_two_smallest_decomposition_le_and_weights_perm
    {pairs swapped rest : List (ℕ × ℝ)}
    (pre middle suffix : List (ℕ × ℝ))
    {a b c : ℝ} {deep shallow : ℕ}
    (hpairs :
      pairs.Perm
        (pre ++ [(deep, c), (deep, b)] ++ middle ++
          [(shallow, a)] ++ suffix))
    (hswapped :
      swapped.Perm
        (pre ++ [(deep, a), (deep, b)] ++ middle ++
          [(shallow, c)] ++ suffix))
    (htwoSmallest : pairs.Perm ((shallow, a) :: (deep, b) :: rest))
    (hab : a ≤ b)
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth : shallow ≤ deep) :
    weightedDepthPairsCost swapped ≤ weightedDepthPairsCost pairs ∧
      (swapped.map Prod.snd).Perm (pairs.map Prod.snd) := by
  let context := pre ++ [(deep, c)] ++ middle ++ suffix
  have hfront :
      (pre ++ [(deep, c), (deep, b)] ++ middle ++
          [(shallow, a)] ++ suffix).Perm
        ((shallow, a) :: (deep, b) :: context) := by
    simpa [context, List.append_assoc] using
      (listPerm_two_selected_slots_to_front_reverse
        (pre := pre ++ [(deep, c)]) (middle := middle)
        (suffix := suffix) (selected := (deep, b))
        (later := (shallow, a)))
  have hrest_context : rest.Perm context := by
    have hfront_from_rest :
        ((shallow, a) :: (deep, b) :: rest).Perm
          ((shallow, a) :: (deep, b) :: context) :=
      (htwoSmallest.symm.trans hpairs).trans hfront
    exact List.Perm.cons_inv (List.Perm.cons_inv hfront_from_rest)
  have hbc : b ≤ c :=
    hrest (deep, c) ((hrest_context.mem_iff).2 (by simp [context]))
  have hac : a ≤ c := le_trans hab hbc
  have hpairs' :
      pairs.Perm
        (pre ++ [(deep, c)] ++ ([(deep, b)] ++ middle) ++
          [(shallow, a)] ++ suffix) := by
    simpa [List.append_assoc] using hpairs
  have hswapped' :
      swapped.Perm
        (pre ++ [(deep, a)] ++ ([(deep, b)] ++ middle) ++
          [(shallow, c)] ++ suffix) := by
    simpa [List.append_assoc] using hswapped
  exact weightedDepthPairsCost_pair_exchange_separated_of_perm_le_and_weights_perm
    pre ([(deep, b)] ++ middle) suffix hpairs' hswapped' hac hdepth

/-- Explicit branch predicate for the pair-list step that moves the two
smallest weights into a displayed deepest sibling pair.  The constructors cover
the already-arranged branch, the nonoverlap two-slot branch, and all one-slot
overlap orientations. -/
inductive TwoSmallestDeepestExchangeBranch
    (pairs swapped : List (ℕ × ℝ)) : Prop
  | noop (hperm : swapped.Perm pairs)
  | nondegenerate
      (pre middle₁ middle₂ suffix rest : List (ℕ × ℝ))
      {a b c d : ℝ} {deep shallow₁ shallow₂ : ℕ}
      (hpairs :
        pairs.Perm
          (pre ++ [(deep, c), (deep, d)] ++ middle₁ ++
            [(shallow₁, a)] ++ middle₂ ++ [(shallow₂, b)] ++ suffix))
      (hswapped :
        swapped.Perm
          (pre ++ [(deep, a), (deep, b)] ++ middle₁ ++
            [(shallow₁, c)] ++ middle₂ ++ [(shallow₂, d)] ++ suffix))
      (htwoSmallest :
        pairs.Perm ((shallow₁, a) :: (shallow₂, b) :: rest))
      (hab : a ≤ b)
      (hrest : ∀ pair ∈ rest, b ≤ pair.2)
      (hdepth₁ : shallow₁ ≤ deep) (hdepth₂ : shallow₂ ≤ deep)
  | leftDeepestFirstSmallest
      (pre middle suffix rest : List (ℕ × ℝ))
      {a b c : ℝ} {deep shallow : ℕ}
      (hpairs :
        pairs.Perm
          (pre ++ [(deep, a), (deep, c)] ++ middle ++
            [(shallow, b)] ++ suffix))
      (hswapped :
        swapped.Perm
          (pre ++ [(deep, a), (deep, b)] ++ middle ++
            [(shallow, c)] ++ suffix))
      (htwoSmallest : pairs.Perm ((deep, a) :: (shallow, b) :: rest))
      (hrest : ∀ pair ∈ rest, b ≤ pair.2)
      (hdepth : shallow ≤ deep)
  | rightDeepestFirstSmallest
      (pre middle suffix rest : List (ℕ × ℝ))
      {a b c : ℝ} {deep shallow : ℕ}
      (hpairs :
        pairs.Perm
          (pre ++ [(deep, c), (deep, a)] ++ middle ++
            [(shallow, b)] ++ suffix))
      (hswapped :
        swapped.Perm
          (pre ++ [(deep, b), (deep, a)] ++ middle ++
            [(shallow, c)] ++ suffix))
      (htwoSmallest : pairs.Perm ((deep, a) :: (shallow, b) :: rest))
      (hrest : ∀ pair ∈ rest, b ≤ pair.2)
      (hdepth : shallow ≤ deep)
  | leftDeepestSecondSmallest
      (pre middle suffix rest : List (ℕ × ℝ))
      {a b c : ℝ} {deep shallow : ℕ}
      (hpairs :
        pairs.Perm
          (pre ++ [(deep, b), (deep, c)] ++ middle ++
            [(shallow, a)] ++ suffix))
      (hswapped :
        swapped.Perm
          (pre ++ [(deep, b), (deep, a)] ++ middle ++
            [(shallow, c)] ++ suffix))
      (htwoSmallest : pairs.Perm ((shallow, a) :: (deep, b) :: rest))
      (hab : a ≤ b)
      (hrest : ∀ pair ∈ rest, b ≤ pair.2)
      (hdepth : shallow ≤ deep)
  | rightDeepestSecondSmallest
      (pre middle suffix rest : List (ℕ × ℝ))
      {a b c : ℝ} {deep shallow : ℕ}
      (hpairs :
        pairs.Perm
          (pre ++ [(deep, c), (deep, b)] ++ middle ++
            [(shallow, a)] ++ suffix))
      (hswapped :
        swapped.Perm
          (pre ++ [(deep, a), (deep, b)] ++ middle ++
            [(shallow, c)] ++ suffix))
      (htwoSmallest : pairs.Perm ((shallow, a) :: (deep, b) :: rest))
      (hab : a ≤ b)
      (hrest : ∀ pair ∈ rest, b ≤ pair.2)
      (hdepth : shallow ≤ deep)

/-- Dispatcher theorem for the explicit pair-list step that moves two
two-smallest weights into a deepest sibling pair.  It packages the no-op,
nonoverlap, and one-slot-overlap branches behind a single reusable surface for
the later tree assembly. -/
theorem weightedDepthPairsCost_two_smallest_deepest_exchange_branch_le_and_weights_perm
    {pairs swapped : List (ℕ × ℝ)}
    (hbranch : TwoSmallestDeepestExchangeBranch pairs swapped) :
    weightedDepthPairsCost swapped ≤ weightedDepthPairsCost pairs ∧
      (swapped.map Prod.snd).Perm (pairs.map Prod.snd) := by
  cases hbranch with
  | noop hperm =>
      exact weightedDepthPairsCost_of_perm_le_and_weights_perm hperm
  | nondegenerate pre middle₁ middle₂ suffix rest hpairs hswapped
      htwoSmallest hab hrest hdepth₁ hdepth₂ =>
      exact
        weightedDepthPairsCost_two_pair_exchange_of_two_smallest_decomposition_le_and_weights_perm
          pre middle₁ middle₂ suffix hpairs hswapped htwoSmallest
          hab hrest hdepth₁ hdepth₂
  | leftDeepestFirstSmallest pre middle suffix rest hpairs hswapped
      htwoSmallest hrest hdepth =>
      exact
        weightedDepthPairsCost_pair_exchange_of_left_deepest_two_smallest_decomposition_le_and_weights_perm
          pre middle suffix hpairs hswapped htwoSmallest hrest hdepth
  | rightDeepestFirstSmallest pre middle suffix rest hpairs hswapped
      htwoSmallest hrest hdepth =>
      exact
        weightedDepthPairsCost_pair_exchange_of_right_deepest_two_smallest_decomposition_le_and_weights_perm
          pre middle suffix hpairs hswapped htwoSmallest hrest hdepth
  | leftDeepestSecondSmallest pre middle suffix rest hpairs hswapped
      htwoSmallest hab hrest hdepth =>
      exact
        weightedDepthPairsCost_pair_exchange_of_left_deepest_second_two_smallest_decomposition_le_and_weights_perm
          pre middle suffix hpairs hswapped htwoSmallest hab hrest hdepth
  | rightDeepestSecondSmallest pre middle suffix rest hpairs hswapped
      htwoSmallest hab hrest hdepth =>
      exact
        weightedDepthPairsCost_pair_exchange_of_right_deepest_second_two_smallest_decomposition_le_and_weights_perm
          pre middle suffix hpairs hswapped htwoSmallest hab hrest hdepth

/-- Tree-realization bridge for the two-smallest/deepest pair-list dispatcher.
If the dispatcher output is realized by an actual schedule tree's explicit
leaf-depth list, then the realized tree has no larger weighted external path
length and preserves the original leaf multiset. -/
theorem weightedLeafDepthCost_two_smallest_deepest_exchange_branch_realized_le_and_leaves_perm
    {tree swappedTree : InsertionScheduleTree} {depth : ℕ}
    {swappedPairs : List (ℕ × ℝ)}
    (hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs)
    (hrealized : (leafDepthWeights depth swappedTree).Perm swappedPairs) :
    weightedLeafDepthCost depth swappedTree ≤ weightedLeafDepthCost depth tree ∧
      swappedTree.leaves.Perm tree.leaves := by
  obtain ⟨hcost, hweights⟩ :=
    weightedDepthPairsCost_two_smallest_deepest_exchange_branch_le_and_weights_perm
      hbranch
  constructor
  · rw [weightedLeafDepthCost_eq_weightedDepthPairsCost depth swappedTree,
      weightedLeafDepthCost_eq_weightedDepthPairsCost depth tree,
      weightedDepthPairsCost_eq_of_perm hrealized]
    exact hcost
  · have hrealizedWeights :=
      hrealized.map Prod.snd
    have hleafWeights :
        ((leafDepthWeights depth swappedTree).map Prod.snd).Perm
        ((leafDepthWeights depth tree).map Prod.snd) :=
      hrealizedWeights.trans hweights
    simpa [leafDepthWeights_weights_eq_leaves] using hleafWeights

/-- Constructive same-shape realization of a two-smallest/deepest dispatcher
output.  When the dispatched pair list preserves the original depth order, a
leaf relabeling of the original schedule tree realizes it, has no larger
weighted external path length, and preserves the leaf multiset. -/
theorem exists_relabelLeaves_for_two_smallest_deepest_exchange_branch_of_depths_eq
    {tree : InsertionScheduleTree} {depth : ℕ}
    {swappedPairs : List (ℕ × ℝ)}
    (hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs)
    (hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst) :
    ∃ swappedTree : InsertionScheduleTree,
      weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
        swappedTree.leaves.Perm tree.leaves ∧
          leafDepthWeights depth swappedTree = swappedPairs := by
  obtain ⟨swappedTree, hrealizedEq, _hleavesEq⟩ :=
    exists_relabelLeaves_leafDepthWeights_eq_of_depths_eq
      depth tree swappedPairs hdepths
  have hrealized : (leafDepthWeights depth swappedTree).Perm swappedPairs := by
    rw [hrealizedEq]
  obtain ⟨hcost, hleavesPerm⟩ :=
    weightedLeafDepthCost_two_smallest_deepest_exchange_branch_realized_le_and_leaves_perm
      hbranch hrealized
  exact ⟨swappedTree, hcost, hleavesPerm, hrealizedEq⟩

/-- Contraction-aware same-shape realization of a two-smallest/deepest
dispatcher output.  The structural contraction supplies the old sibling-pair
context; if the dispatched output places replacement weights in a context of
the same lengths, the relabeled tree and the correspondingly relabeled
contracted tree are still connected by `SiblingLeafContract`. -/
theorem
    exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_context_lengths
    {tree contracted : InsertionScheduleTree} {depth : ℕ}
    {oldA oldB : ℝ}
    (hcontract : SiblingLeafContract tree contracted oldA oldB) :
    ∃ parentDepth : ℕ, ∃ oldPre oldSuffix : List (ℕ × ℝ),
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, oldA), (parentDepth + 1, oldB)] ++
          oldSuffix ∧
        leafDepthWeights depth contracted =
          oldPre ++ [(parentDepth, oldA + oldB)] ++ oldSuffix ∧
          ∀ {swappedPairs newPre newSuffix : List (ℕ × ℝ)} {a b : ℝ},
            TwoSmallestDeepestExchangeBranch
              (leafDepthWeights depth tree) swappedPairs →
            swappedPairs.map Prod.fst =
              (leafDepthWeights depth tree).map Prod.fst →
            swappedPairs =
              newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                newSuffix →
            newPre.length = oldPre.length →
            newSuffix.length = oldSuffix.length →
            ∃ swappedTree swappedContracted : InsertionScheduleTree,
              SiblingLeafContract swappedTree swappedContracted a b ∧
                weightedLeafDepthCost depth swappedTree ≤
                  weightedLeafDepthCost depth tree ∧
                  swappedTree.leaves.Perm tree.leaves ∧
                    leafDepthWeights depth swappedTree = swappedPairs := by
  obtain ⟨parentDepth, oldPre, oldSuffix, htreeDepth,
    hcontractedDepth, _htreeLeaves, _hcontractedLeaves, hrelabeled⟩ :=
    SiblingLeafContract.exists_leafDepthWeights_context_with_relabel_contract
      depth hcontract
  refine ⟨parentDepth, oldPre, oldSuffix, htreeDepth, hcontractedDepth, ?_⟩
  intro swappedPairs newPre newSuffix a b hbranch hdepths hdisplay
    hpreLen hsuffixLen
  let replacementWeights :=
    newPre.map Prod.snd ++ [a, b] ++ newSuffix.map Prod.snd
  let swappedTree := relabelLeaves tree replacementWeights
  let swappedContracted :=
    relabelLeaves contracted
      (newPre.map Prod.snd ++ [a + b] ++ newSuffix.map Prod.snd)
  have hreplacementWeights :
      replacementWeights = swappedPairs.map Prod.snd := by
    rw [hdisplay]
    simp [replacementWeights, List.map_append]
  have hrealizedEq :
      leafDepthWeights depth swappedTree = swappedPairs := by
    dsimp [swappedTree]
    rw [hreplacementWeights]
    exact relabelLeaves_leafDepthWeights_eq_pairs_of_depths_eq
      depth tree swappedPairs hdepths
  have hrealized : (leafDepthWeights depth swappedTree).Perm swappedPairs := by
    rw [hrealizedEq]
  obtain ⟨hcost, hleavesPerm⟩ :=
    weightedLeafDepthCost_two_smallest_deepest_exchange_branch_realized_le_and_leaves_perm
      hbranch hrealized
  have hcontractedRelabel :
      SiblingLeafContract swappedTree swappedContracted a b := by
    dsimp [swappedTree, swappedContracted, replacementWeights]
    exact hrelabeled hpreLen hsuffixLen
  exact ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
    hleavesPerm, hrealizedEq⟩

/-- Explicit-context version of the contraction-aware branch bridge.  Once a
same-shape relabeling proof has been established for a particular displayed
sibling-pair context, any two-smallest/deepest branch output that preserves the
depth list and keeps that context length is realized by a relabeled tree and
contracted companion. -/
theorem
    exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_explicit_context_lengths
    {tree contracted : InsertionScheduleTree} {depth parentDepth : ℕ}
    {oldPre oldSuffix : List (ℕ × ℝ)}
    (hrelabeled :
      ∀ {newPre newSuffix : List (ℕ × ℝ)} {a b : ℝ},
        newPre.length = oldPre.length →
        newSuffix.length = oldSuffix.length →
        SiblingLeafContract
          (relabelLeaves tree
            (newPre.map Prod.snd ++ [a, b] ++
              newSuffix.map Prod.snd))
          (relabelLeaves contracted
            (newPre.map Prod.snd ++ [a + b] ++
              newSuffix.map Prod.snd))
          a b) :
    ∀ {swappedPairs newPre newSuffix : List (ℕ × ℝ)} {a b : ℝ},
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs →
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst →
      swappedPairs =
        newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
          newSuffix →
      newPre.length = oldPre.length →
      newSuffix.length = oldSuffix.length →
      ∃ swappedTree swappedContracted : InsertionScheduleTree,
        SiblingLeafContract swappedTree swappedContracted a b ∧
          weightedLeafDepthCost depth swappedTree ≤
            weightedLeafDepthCost depth tree ∧
            swappedTree.leaves.Perm tree.leaves ∧
              leafDepthWeights depth swappedTree = swappedPairs := by
  intro swappedPairs newPre newSuffix a b hbranch hdepths hdisplay
    hpreLen hsuffixLen
  let replacementWeights :=
    newPre.map Prod.snd ++ [a, b] ++ newSuffix.map Prod.snd
  let swappedTree := relabelLeaves tree replacementWeights
  let swappedContracted :=
    relabelLeaves contracted
      (newPre.map Prod.snd ++ [a + b] ++ newSuffix.map Prod.snd)
  have hreplacementWeights :
      replacementWeights = swappedPairs.map Prod.snd := by
    rw [hdisplay]
    simp [replacementWeights, List.map_append]
  have hrealizedEq :
      leafDepthWeights depth swappedTree = swappedPairs := by
    dsimp [swappedTree]
    rw [hreplacementWeights]
    exact relabelLeaves_leafDepthWeights_eq_pairs_of_depths_eq
      depth tree swappedPairs hdepths
  have hrealized : (leafDepthWeights depth swappedTree).Perm swappedPairs := by
    rw [hrealizedEq]
  obtain ⟨hcost, hleavesPerm⟩ :=
    weightedLeafDepthCost_two_smallest_deepest_exchange_branch_realized_le_and_leaves_perm
      hbranch hrealized
  have hcontractedRelabel :
      SiblingLeafContract swappedTree swappedContracted a b := by
    dsimp [swappedTree, swappedContracted, replacementWeights]
    exact hrelabeled hpreLen hsuffixLen
  exact ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
    hleavesPerm, hrealizedEq⟩

/-- Deepest-context branch bridge for a non-leaf tree.  This combines the
recursive deepest sibling-pair search with the explicit-context relabel bridge,
so downstream normalization can work with a context known to sit at maximum
leaf depth. -/
theorem exists_deepest_sibling_leaf_contract_with_branch_bridge
    (depth : ℕ) (tree : InsertionScheduleTree)
    (hcount : 1 < tree.leafCount) :
    ∃ contractedTree : InsertionScheduleTree,
      ∃ parentDepth : ℕ, ∃ oldPre oldSuffix : List (ℕ × ℝ), ∃ c d : ℝ,
        SiblingLeafContract tree contractedTree c d ∧
          leafDepthWeights depth tree =
            oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
              oldSuffix ∧
            leafDepthWeights depth contractedTree =
              oldPre ++ [(parentDepth, c + d)] ++ oldSuffix ∧
              parentDepth + 1 = maxLeafDepth depth tree ∧
                weightedLeafDepthCost depth tree =
                  weightedLeafDepthCost depth contractedTree + (c + d) ∧
                  tree.leafCount = contractedTree.leafCount + 1 ∧
                    ∀ {swappedPairs newPre newSuffix : List (ℕ × ℝ)}
                        {a b : ℝ},
                      TwoSmallestDeepestExchangeBranch
                        (leafDepthWeights depth tree) swappedPairs →
                      swappedPairs.map Prod.fst =
                        (leafDepthWeights depth tree).map Prod.fst →
                      swappedPairs =
                        newPre ++
                          [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                          newSuffix →
                      newPre.length = oldPre.length →
                      newSuffix.length = oldSuffix.length →
                      ∃ swappedTree swappedContracted :
                          InsertionScheduleTree,
                        SiblingLeafContract swappedTree swappedContracted
                          a b ∧
                          weightedLeafDepthCost depth swappedTree ≤
                            weightedLeafDepthCost depth tree ∧
                            swappedTree.leaves.Perm tree.leaves ∧
                              leafDepthWeights depth swappedTree =
                                swappedPairs := by
  obtain ⟨contractedTree, parentDepth, oldPre, oldSuffix, c, d,
      hcontract, htreeDepth, hcontractedDepth, hparent, hcost, hcountEq,
      hrelabeled⟩ :=
    exists_deepest_sibling_leaf_contract_with_relabel_parent_context
      depth tree hcount
  have hbridge :
      ∀ {swappedPairs newPre newSuffix : List (ℕ × ℝ)} {a b : ℝ},
        TwoSmallestDeepestExchangeBranch
          (leafDepthWeights depth tree) swappedPairs →
        swappedPairs.map Prod.fst =
          (leafDepthWeights depth tree).map Prod.fst →
        swappedPairs =
          newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            newSuffix →
        newPre.length = oldPre.length →
        newSuffix.length = oldSuffix.length →
        ∃ swappedTree swappedContracted : InsertionScheduleTree,
          SiblingLeafContract swappedTree swappedContracted a b ∧
            weightedLeafDepthCost depth swappedTree ≤
              weightedLeafDepthCost depth tree ∧
              swappedTree.leaves.Perm tree.leaves ∧
                leafDepthWeights depth swappedTree = swappedPairs := by
    intro swappedPairs newPre newSuffix a b hbranch hdepths hdisplay
      hpreLen hsuffixLen
    exact
      exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_explicit_context_lengths
        (tree := tree) (contracted := contractedTree) (depth := depth)
        (parentDepth := parentDepth) (oldPre := oldPre)
        (oldSuffix := oldSuffix) hrelabeled
        (swappedPairs := swappedPairs) (newPre := newPre)
        (newSuffix := newSuffix) (a := a) (b := b)
        hbranch hdepths hdisplay hpreLen hsuffixLen
  exact ⟨contractedTree, parentDepth, oldPre, oldSuffix, c, d, hcontract,
    htreeDepth, hcontractedDepth, hparent, hcost, hcountEq, hbridge⟩

/-- Canonical nonoverlap consumer for the contraction-aware branch bridge.
If the structural contraction identifies a displayed sibling pair and the two
selected smallest weights occur later in that contraction suffix, relabeling
moves those two weights into the contracted sibling slots and simultaneously
produces the contracted companion tree. -/
theorem
    exists_relabelLeaves_contract_for_two_pair_exchange_after_contracted_pair
    {tree contracted : InsertionScheduleTree} {depth : ℕ} {c d : ℝ}
    (hcontract : SiblingLeafContract tree contracted c d) :
    ∃ parentDepth : ℕ, ∃ oldPre oldSuffix : List (ℕ × ℝ),
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          oldSuffix ∧
        leafDepthWeights depth contracted =
          oldPre ++ [(parentDepth, c + d)] ++ oldSuffix ∧
          ∀ {middle₁ middle₂ suffix rest : List (ℕ × ℝ)}
              {a b : ℝ} {shallow₁ shallow₂ : ℕ},
            oldSuffix =
              middle₁ ++ [(shallow₁, a)] ++ middle₂ ++
                [(shallow₂, b)] ++ suffix →
            (leafDepthWeights depth tree).Perm
              ((shallow₁, a) :: (shallow₂, b) :: rest) →
            a ≤ b →
            (∀ pair ∈ rest, b ≤ pair.2) →
            shallow₁ ≤ parentDepth + 1 →
            shallow₂ ≤ parentDepth + 1 →
            ∃ swappedTree swappedContracted : InsertionScheduleTree,
              SiblingLeafContract swappedTree swappedContracted a b ∧
                weightedLeafDepthCost depth swappedTree ≤
                  weightedLeafDepthCost depth tree ∧
                  swappedTree.leaves.Perm tree.leaves ∧
                    leafDepthWeights depth swappedTree =
                      oldPre ++
                        [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                          middle₁ ++ [(shallow₁, c)] ++ middle₂ ++
                            [(shallow₂, d)] ++ suffix := by
  obtain ⟨parentDepth, oldPre, oldSuffix, htreeDepth,
    hcontractedDepth, hbridge⟩ :=
    exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_context_lengths
      hcontract
  refine ⟨parentDepth, oldPre, oldSuffix, htreeDepth, hcontractedDepth, ?_⟩
  intro middle₁ middle₂ suffix rest a b shallow₁ shallow₂ hsuffix
    htwoSmallest hab hrest hdepth₁ hdepth₂
  let newSuffix :=
    middle₁ ++ [(shallow₁, c)] ++ middle₂ ++ [(shallow₂, d)] ++ suffix
  let swappedPairs :=
    oldPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
      newSuffix
  have hpairsPerm :
      (leafDepthWeights depth tree).Perm
        (oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          middle₁ ++ [(shallow₁, a)] ++ middle₂ ++
            [(shallow₂, b)] ++ suffix) := by
    rw [htreeDepth, hsuffix]
    simp [List.append_assoc]
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.nondegenerate
      oldPre middle₁ middle₂ suffix rest hpairsPerm
      (by simp [swappedPairs, newSuffix, List.append_assoc])
      htwoSmallest hab hrest hdepth₁ hdepth₂
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [htreeDepth, hsuffix]
    simp [swappedPairs, newSuffix, List.map_append]
  have hdisplay :
      swappedPairs =
        oldPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
          newSuffix := by
    rfl
  have hsuffixLen : newSuffix.length = oldSuffix.length := by
    rw [hsuffix]
    simp [newSuffix, List.length_append]
  obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
      hleavesPerm, hrealizedEq⟩ :=
    hbridge (swappedPairs := swappedPairs) (newPre := oldPre)
      (newSuffix := newSuffix) hbranch hdepths hdisplay rfl hsuffixLen
  refine ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
    hleavesPerm, ?_⟩
  simpa [swappedPairs, newSuffix, List.append_assoc] using hrealizedEq

/-- Reverse selected-order variant of
`exists_relabelLeaves_contract_for_two_pair_exchange_after_contracted_pair`.
The old contracted sibling pair precedes both selected slots, but the displayed
selected slots occur in `b, a` order. -/
theorem
    exists_relabelLeaves_contract_for_two_pair_exchange_reverse_after_contracted_pair
    {tree contracted : InsertionScheduleTree} {depth : ℕ} {c d : ℝ}
    (hcontract : SiblingLeafContract tree contracted c d) :
    ∃ parentDepth : ℕ, ∃ oldPre oldSuffix : List (ℕ × ℝ),
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          oldSuffix ∧
        leafDepthWeights depth contracted =
          oldPre ++ [(parentDepth, c + d)] ++ oldSuffix ∧
          ∀ {middle₁ middle₂ suffix rest : List (ℕ × ℝ)}
              {a b : ℝ} {shallow₁ shallow₂ : ℕ},
            oldSuffix =
              middle₁ ++ [(shallow₂, b)] ++ middle₂ ++
                [(shallow₁, a)] ++ suffix →
            (leafDepthWeights depth tree).Perm
              ((shallow₁, a) :: (shallow₂, b) :: rest) →
            a ≤ b →
            (∀ pair ∈ rest, b ≤ pair.2) →
            shallow₁ ≤ parentDepth + 1 →
            shallow₂ ≤ parentDepth + 1 →
            ∃ swappedTree swappedContracted : InsertionScheduleTree,
              SiblingLeafContract swappedTree swappedContracted a b ∧
                weightedLeafDepthCost depth swappedTree ≤
                  weightedLeafDepthCost depth tree ∧
                  swappedTree.leaves.Perm tree.leaves ∧
                    leafDepthWeights depth swappedTree =
                      oldPre ++
                        [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                          middle₁ ++ [(shallow₂, d)] ++ middle₂ ++
                            [(shallow₁, c)] ++ suffix := by
  obtain ⟨parentDepth, oldPre, oldSuffix, htreeDepth,
    hcontractedDepth, hbridge⟩ :=
    exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_context_lengths
      hcontract
  refine ⟨parentDepth, oldPre, oldSuffix, htreeDepth, hcontractedDepth, ?_⟩
  intro middle₁ middle₂ suffix rest a b shallow₁ shallow₂ hsuffix
    htwoSmallest hab hrest hdepth₁ hdepth₂
  let newSuffix :=
    middle₁ ++ [(shallow₂, d)] ++ middle₂ ++ [(shallow₁, c)] ++ suffix
  let swappedPairs :=
    oldPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
      newSuffix
  have hpairsPerm :
      (leafDepthWeights depth tree).Perm
        (oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          middle₁ ++ [(shallow₁, a)] ++ middle₂ ++
            [(shallow₂, b)] ++ suffix) := by
    rw [htreeDepth, hsuffix]
    simpa [List.append_assoc] using
      (weightListPerm_pair_exchange
        (oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          middle₁)
        middle₂ suffix (shallow₂, b) (shallow₁, a))
  have hswappedPerm :
      swappedPairs.Perm
        (oldPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
          middle₁ ++ [(shallow₁, c)] ++ middle₂ ++
            [(shallow₂, d)] ++ suffix) := by
    simpa [swappedPairs, newSuffix, List.append_assoc] using
      (weightListPerm_pair_exchange
        (oldPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
          middle₁)
        middle₂ suffix (shallow₂, d) (shallow₁, c))
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.nondegenerate
      oldPre middle₁ middle₂ suffix rest hpairsPerm hswappedPerm
      htwoSmallest hab hrest hdepth₁ hdepth₂
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [htreeDepth, hsuffix]
    simp [swappedPairs, newSuffix, List.map_append]
  have hdisplay :
      swappedPairs =
        oldPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
          newSuffix := by
    rfl
  have hsuffixLen : newSuffix.length = oldSuffix.length := by
    rw [hsuffix]
    simp [newSuffix, List.length_append]
  obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
      hleavesPerm, hrealizedEq⟩ :=
    hbridge (swappedPairs := swappedPairs) (newPre := oldPre)
      (newSuffix := newSuffix) hbranch hdepths hdisplay rfl hsuffixLen
  refine ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
    hleavesPerm, ?_⟩
  simpa [swappedPairs, newSuffix, List.append_assoc] using hrealizedEq

/-- Symmetric nonoverlap consumer for the contraction-aware branch bridge.
If the two selected smallest weights occur before the contracted sibling pair,
same-shape relabeling keeps the original contraction position and still
produces a normalized `SiblingLeafContract` for the selected pair. -/
theorem
    exists_relabelLeaves_contract_for_two_pair_exchange_before_contracted_pair
    {tree contracted : InsertionScheduleTree} {depth : ℕ} {c d : ℝ}
    (hcontract : SiblingLeafContract tree contracted c d) :
    ∃ parentDepth : ℕ, ∃ oldPre oldSuffix : List (ℕ × ℝ),
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          oldSuffix ∧
        leafDepthWeights depth contracted =
          oldPre ++ [(parentDepth, c + d)] ++ oldSuffix ∧
          ∀ {pre₀ middle₁ middle₂ rest : List (ℕ × ℝ)}
              {a b : ℝ} {shallow₁ shallow₂ : ℕ},
            oldPre =
              pre₀ ++ [(shallow₁, a)] ++ middle₁ ++
                [(shallow₂, b)] ++ middle₂ →
            (leafDepthWeights depth tree).Perm
              ((shallow₁, a) :: (shallow₂, b) :: rest) →
            a ≤ b →
            (∀ pair ∈ rest, b ≤ pair.2) →
            shallow₁ ≤ parentDepth + 1 →
            shallow₂ ≤ parentDepth + 1 →
            ∃ swappedTree swappedContracted : InsertionScheduleTree,
              SiblingLeafContract swappedTree swappedContracted a b ∧
                weightedLeafDepthCost depth swappedTree ≤
                  weightedLeafDepthCost depth tree ∧
                  swappedTree.leaves.Perm tree.leaves ∧
                    leafDepthWeights depth swappedTree =
                      pre₀ ++ [(shallow₁, c)] ++ middle₁ ++
                        [(shallow₂, d)] ++ middle₂ ++
                          [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                            oldSuffix := by
  obtain ⟨parentDepth, oldPre, oldSuffix, htreeDepth,
    hcontractedDepth, hbridge⟩ :=
    exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_context_lengths
      hcontract
  refine ⟨parentDepth, oldPre, oldSuffix, htreeDepth, hcontractedDepth, ?_⟩
  intro pre₀ middle₁ middle₂ rest a b shallow₁ shallow₂ hpre
    htwoSmallest hab hrest hdepth₁ hdepth₂
  let newPre :=
    pre₀ ++ [(shallow₁, c)] ++ middle₁ ++ [(shallow₂, d)] ++ middle₂
  let swappedPairs :=
    newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
      oldSuffix
  have hpairsPerm :
      (leafDepthWeights depth tree).Perm
        (pre₀ ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          middle₁ ++ [(shallow₁, a)] ++ middle₂ ++
            [(shallow₂, b)] ++ oldSuffix) := by
    rw [htreeDepth, hpre]
    simpa [List.append_assoc] using
      (listPerm_two_selected_before_deepest_to_canonical
        pre₀ middle₁ middle₂ oldSuffix
        (parentDepth + 1, c) (parentDepth + 1, d)
        (shallow₁, a) (shallow₂, b))
  have hswappedPerm :
      swappedPairs.Perm
        (pre₀ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
          middle₁ ++ [(shallow₁, c)] ++ middle₂ ++
            [(shallow₂, d)] ++ oldSuffix) := by
    simpa [swappedPairs, newPre, List.append_assoc] using
      (listPerm_two_selected_before_deepest_to_canonical
        pre₀ middle₁ middle₂ oldSuffix
        (parentDepth + 1, a) (parentDepth + 1, b)
        (shallow₁, c) (shallow₂, d))
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.nondegenerate
      pre₀ middle₁ middle₂ oldSuffix rest hpairsPerm hswappedPerm
      htwoSmallest hab hrest hdepth₁ hdepth₂
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [htreeDepth, hpre]
    simp [swappedPairs, newPre, List.map_append]
  have hdisplay :
      swappedPairs =
        newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
          oldSuffix := by
    rfl
  have hpreLen : newPre.length = oldPre.length := by
    rw [hpre]
    simp [newPre, List.length_append]
  obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
      hleavesPerm, hrealizedEq⟩ :=
    hbridge (swappedPairs := swappedPairs) (newPre := newPre)
      (newSuffix := oldSuffix) hbranch hdepths hdisplay hpreLen rfl
  refine ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
    hleavesPerm, ?_⟩
  simpa [swappedPairs, newPre, List.append_assoc] using hrealizedEq

/-- Reverse selected-order variant of
`exists_relabelLeaves_contract_for_two_pair_exchange_before_contracted_pair`.
Both selected slots precede the old contracted sibling pair, but they occur in
`b, a` order. -/
theorem
    exists_relabelLeaves_contract_for_two_pair_exchange_reverse_before_contracted_pair
    {tree contracted : InsertionScheduleTree} {depth : ℕ} {c d : ℝ}
    (hcontract : SiblingLeafContract tree contracted c d) :
    ∃ parentDepth : ℕ, ∃ oldPre oldSuffix : List (ℕ × ℝ),
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          oldSuffix ∧
        leafDepthWeights depth contracted =
          oldPre ++ [(parentDepth, c + d)] ++ oldSuffix ∧
          ∀ {pre₀ middle₁ middle₂ rest : List (ℕ × ℝ)}
              {a b : ℝ} {shallow₁ shallow₂ : ℕ},
            oldPre =
              pre₀ ++ [(shallow₂, b)] ++ middle₁ ++
                [(shallow₁, a)] ++ middle₂ →
            (leafDepthWeights depth tree).Perm
              ((shallow₁, a) :: (shallow₂, b) :: rest) →
            a ≤ b →
            (∀ pair ∈ rest, b ≤ pair.2) →
            shallow₁ ≤ parentDepth + 1 →
            shallow₂ ≤ parentDepth + 1 →
            ∃ swappedTree swappedContracted : InsertionScheduleTree,
              SiblingLeafContract swappedTree swappedContracted a b ∧
                weightedLeafDepthCost depth swappedTree ≤
                  weightedLeafDepthCost depth tree ∧
                  swappedTree.leaves.Perm tree.leaves ∧
                    leafDepthWeights depth swappedTree =
                      pre₀ ++ [(shallow₂, d)] ++ middle₁ ++
                        [(shallow₁, c)] ++ middle₂ ++
                          [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                            oldSuffix := by
  obtain ⟨parentDepth, oldPre, oldSuffix, htreeDepth,
    hcontractedDepth, hbridge⟩ :=
    exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_context_lengths
      hcontract
  refine ⟨parentDepth, oldPre, oldSuffix, htreeDepth, hcontractedDepth, ?_⟩
  intro pre₀ middle₁ middle₂ rest a b shallow₁ shallow₂ hpre
    htwoSmallest hab hrest hdepth₁ hdepth₂
  let newPre :=
    pre₀ ++ [(shallow₂, d)] ++ middle₁ ++ [(shallow₁, c)] ++ middle₂
  let swappedPairs :=
    newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
      oldSuffix
  have hpairsToReverseCanonical :
      (leafDepthWeights depth tree).Perm
        (pre₀ ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          middle₁ ++ [(shallow₂, b)] ++ middle₂ ++
            [(shallow₁, a)] ++ oldSuffix) := by
    rw [htreeDepth, hpre]
    simpa [List.append_assoc] using
      (listPerm_two_selected_before_deepest_to_canonical
        pre₀ middle₁ middle₂ oldSuffix
        (parentDepth + 1, c) (parentDepth + 1, d)
        (shallow₂, b) (shallow₁, a))
  have hpairsPerm :
      (leafDepthWeights depth tree).Perm
        (pre₀ ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          middle₁ ++ [(shallow₁, a)] ++ middle₂ ++
            [(shallow₂, b)] ++ oldSuffix) := by
    exact hpairsToReverseCanonical.trans
      (weightListPerm_pair_exchange
        (pre₀ ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          middle₁)
        middle₂ oldSuffix (shallow₂, b) (shallow₁, a))
  have hswappedToReverseCanonical :
      swappedPairs.Perm
        (pre₀ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
          middle₁ ++ [(shallow₂, d)] ++ middle₂ ++
            [(shallow₁, c)] ++ oldSuffix) := by
    simpa [swappedPairs, newPre, List.append_assoc] using
      (listPerm_two_selected_before_deepest_to_canonical
        pre₀ middle₁ middle₂ oldSuffix
        (parentDepth + 1, a) (parentDepth + 1, b)
        (shallow₂, d) (shallow₁, c))
  have hswappedPerm :
      swappedPairs.Perm
        (pre₀ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
          middle₁ ++ [(shallow₁, c)] ++ middle₂ ++
            [(shallow₂, d)] ++ oldSuffix) := by
    exact hswappedToReverseCanonical.trans
      (weightListPerm_pair_exchange
        (pre₀ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
          middle₁)
        middle₂ oldSuffix (shallow₂, d) (shallow₁, c))
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.nondegenerate
      pre₀ middle₁ middle₂ oldSuffix rest hpairsPerm hswappedPerm
      htwoSmallest hab hrest hdepth₁ hdepth₂
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [htreeDepth, hpre]
    simp [swappedPairs, newPre, List.map_append]
  have hdisplay :
      swappedPairs =
        newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
          oldSuffix := by
    rfl
  have hpreLen : newPre.length = oldPre.length := by
    rw [hpre]
    simp [newPre, List.length_append]
  obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
      hleavesPerm, hrealizedEq⟩ :=
    hbridge (swappedPairs := swappedPairs) (newPre := newPre)
      (newSuffix := oldSuffix) hbranch hdepths hdisplay hpreLen rfl
  refine ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
    hleavesPerm, ?_⟩
  simpa [swappedPairs, newPre, List.append_assoc] using hrealizedEq

/-- Mixed nonoverlap consumer for the contraction-aware branch bridge.  This
covers the branch where the first selected smallest slot is before the old
contracted sibling pair and the second selected smallest slot is after it. -/
theorem
    exists_relabelLeaves_contract_for_two_pair_exchange_around_contracted_pair
    {tree contracted : InsertionScheduleTree} {depth : ℕ} {c d : ℝ}
    (hcontract : SiblingLeafContract tree contracted c d) :
    ∃ parentDepth : ℕ, ∃ oldPre oldSuffix : List (ℕ × ℝ),
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          oldSuffix ∧
        leafDepthWeights depth contracted =
          oldPre ++ [(parentDepth, c + d)] ++ oldSuffix ∧
          ∀ {pre₀ middle₁ middle₂ suffix rest : List (ℕ × ℝ)}
              {a b : ℝ} {shallow₁ shallow₂ : ℕ},
            oldPre = pre₀ ++ [(shallow₁, a)] ++ middle₁ →
            oldSuffix = middle₂ ++ [(shallow₂, b)] ++ suffix →
            (leafDepthWeights depth tree).Perm
              ((shallow₁, a) :: (shallow₂, b) :: rest) →
            a ≤ b →
            (∀ pair ∈ rest, b ≤ pair.2) →
            shallow₁ ≤ parentDepth + 1 →
            shallow₂ ≤ parentDepth + 1 →
            ∃ swappedTree swappedContracted : InsertionScheduleTree,
              SiblingLeafContract swappedTree swappedContracted a b ∧
                weightedLeafDepthCost depth swappedTree ≤
                  weightedLeafDepthCost depth tree ∧
                  swappedTree.leaves.Perm tree.leaves ∧
                    leafDepthWeights depth swappedTree =
                      pre₀ ++ [(shallow₁, c)] ++ middle₁ ++
                        [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                          middle₂ ++ [(shallow₂, d)] ++ suffix := by
  obtain ⟨parentDepth, oldPre, oldSuffix, htreeDepth,
    hcontractedDepth, hbridge⟩ :=
    exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_context_lengths
      hcontract
  refine ⟨parentDepth, oldPre, oldSuffix, htreeDepth, hcontractedDepth, ?_⟩
  intro pre₀ middle₁ middle₂ suffix rest a b shallow₁ shallow₂
    hpre hsuffix htwoSmallest hab hrest hdepth₁ hdepth₂
  let newPre := pre₀ ++ [(shallow₁, c)] ++ middle₁
  let newSuffix := middle₂ ++ [(shallow₂, d)] ++ suffix
  let swappedPairs :=
    newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
      newSuffix
  have hpairsPerm :
      (leafDepthWeights depth tree).Perm
        (pre₀ ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          middle₁ ++ [(shallow₁, a)] ++ middle₂ ++
            [(shallow₂, b)] ++ suffix) := by
    rw [htreeDepth, hpre, hsuffix]
    simpa [List.append_assoc] using
      (listPerm_selected_before_deepest_before_selected_to_canonical
        pre₀ middle₁ middle₂ suffix
        (parentDepth + 1, c) (parentDepth + 1, d)
        (shallow₁, a) (shallow₂, b))
  have hswappedPerm :
      swappedPairs.Perm
        (pre₀ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
          middle₁ ++ [(shallow₁, c)] ++ middle₂ ++
            [(shallow₂, d)] ++ suffix) := by
    simpa [swappedPairs, newPre, newSuffix, List.append_assoc] using
      (listPerm_selected_before_deepest_before_selected_to_canonical
        pre₀ middle₁ middle₂ suffix
        (parentDepth + 1, a) (parentDepth + 1, b)
        (shallow₁, c) (shallow₂, d))
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.nondegenerate
      pre₀ middle₁ middle₂ suffix rest hpairsPerm hswappedPerm
      htwoSmallest hab hrest hdepth₁ hdepth₂
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [htreeDepth, hpre, hsuffix]
    simp [swappedPairs, newPre, newSuffix, List.map_append]
  have hdisplay :
      swappedPairs =
        newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
          newSuffix := by
    rfl
  have hpreLen : newPre.length = oldPre.length := by
    rw [hpre]
    simp [newPre, List.length_append]
  have hsuffixLen : newSuffix.length = oldSuffix.length := by
    rw [hsuffix]
    simp [newSuffix, List.length_append]
  obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
      hleavesPerm, hrealizedEq⟩ :=
    hbridge (swappedPairs := swappedPairs) (newPre := newPre)
      (newSuffix := newSuffix) hbranch hdepths hdisplay hpreLen hsuffixLen
  refine ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
    hleavesPerm, ?_⟩
  simpa [swappedPairs, newPre, newSuffix, List.append_assoc] using
    hrealizedEq

/-- Reverse mixed nonoverlap consumer for the contraction-aware branch bridge.
This covers the branch where the `b` slot occurs before the old contracted
sibling pair and the `a` slot occurs after it. -/
theorem
    exists_relabelLeaves_contract_for_two_pair_exchange_reverse_around_contracted_pair
    {tree contracted : InsertionScheduleTree} {depth : ℕ} {c d : ℝ}
    (hcontract : SiblingLeafContract tree contracted c d) :
    ∃ parentDepth : ℕ, ∃ oldPre oldSuffix : List (ℕ × ℝ),
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          oldSuffix ∧
        leafDepthWeights depth contracted =
          oldPre ++ [(parentDepth, c + d)] ++ oldSuffix ∧
          ∀ {pre₀ middle₁ middle₂ suffix rest : List (ℕ × ℝ)}
              {a b : ℝ} {shallow₁ shallow₂ : ℕ},
            oldPre = pre₀ ++ [(shallow₂, b)] ++ middle₁ →
            oldSuffix = middle₂ ++ [(shallow₁, a)] ++ suffix →
            (leafDepthWeights depth tree).Perm
              ((shallow₁, a) :: (shallow₂, b) :: rest) →
            a ≤ b →
            (∀ pair ∈ rest, b ≤ pair.2) →
            shallow₁ ≤ parentDepth + 1 →
            shallow₂ ≤ parentDepth + 1 →
            ∃ swappedTree swappedContracted : InsertionScheduleTree,
              SiblingLeafContract swappedTree swappedContracted a b ∧
                weightedLeafDepthCost depth swappedTree ≤
                  weightedLeafDepthCost depth tree ∧
                  swappedTree.leaves.Perm tree.leaves ∧
                    leafDepthWeights depth swappedTree =
                      pre₀ ++ [(shallow₂, d)] ++ middle₁ ++
                        [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                          middle₂ ++ [(shallow₁, c)] ++ suffix := by
  obtain ⟨parentDepth, oldPre, oldSuffix, htreeDepth,
    hcontractedDepth, hbridge⟩ :=
    exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_context_lengths
      hcontract
  refine ⟨parentDepth, oldPre, oldSuffix, htreeDepth, hcontractedDepth, ?_⟩
  intro pre₀ middle₁ middle₂ suffix rest a b shallow₁ shallow₂
    hpre hsuffix htwoSmallest hab hrest hdepth₁ hdepth₂
  let newPre := pre₀ ++ [(shallow₂, d)] ++ middle₁
  let newSuffix := middle₂ ++ [(shallow₁, c)] ++ suffix
  let swappedPairs :=
    newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
      newSuffix
  have hpairsToReverseCanonical :
      (leafDepthWeights depth tree).Perm
        (pre₀ ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          middle₁ ++ [(shallow₂, b)] ++ middle₂ ++
            [(shallow₁, a)] ++ suffix) := by
    rw [htreeDepth, hpre, hsuffix]
    simpa [List.append_assoc] using
      (listPerm_selected_before_deepest_before_selected_to_canonical
        pre₀ middle₁ middle₂ suffix
        (parentDepth + 1, c) (parentDepth + 1, d)
        (shallow₂, b) (shallow₁, a))
  have hpairsPerm :
      (leafDepthWeights depth tree).Perm
        (pre₀ ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          middle₁ ++ [(shallow₁, a)] ++ middle₂ ++
            [(shallow₂, b)] ++ suffix) := by
    exact hpairsToReverseCanonical.trans
      (weightListPerm_pair_exchange
        (pre₀ ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          middle₁)
        middle₂ suffix (shallow₂, b) (shallow₁, a))
  have hswappedToReverseCanonical :
      swappedPairs.Perm
        (pre₀ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
          middle₁ ++ [(shallow₂, d)] ++ middle₂ ++
            [(shallow₁, c)] ++ suffix) := by
    simpa [swappedPairs, newPre, newSuffix, List.append_assoc] using
      (listPerm_selected_before_deepest_before_selected_to_canonical
        pre₀ middle₁ middle₂ suffix
        (parentDepth + 1, a) (parentDepth + 1, b)
        (shallow₂, d) (shallow₁, c))
  have hswappedPerm :
      swappedPairs.Perm
        (pre₀ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
          middle₁ ++ [(shallow₁, c)] ++ middle₂ ++
            [(shallow₂, d)] ++ suffix) := by
    exact hswappedToReverseCanonical.trans
      (weightListPerm_pair_exchange
        (pre₀ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
          middle₁)
        middle₂ suffix (shallow₂, d) (shallow₁, c))
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.nondegenerate
      pre₀ middle₁ middle₂ suffix rest hpairsPerm hswappedPerm
      htwoSmallest hab hrest hdepth₁ hdepth₂
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [htreeDepth, hpre, hsuffix]
    simp [swappedPairs, newPre, newSuffix, List.map_append]
  have hdisplay :
      swappedPairs =
        newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
          newSuffix := by
    rfl
  have hpreLen : newPre.length = oldPre.length := by
    rw [hpre]
    simp [newPre, List.length_append]
  have hsuffixLen : newSuffix.length = oldSuffix.length := by
    rw [hsuffix]
    simp [newSuffix, List.length_append]
  obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
      hleavesPerm, hrealizedEq⟩ :=
    hbridge (swappedPairs := swappedPairs) (newPre := newPre)
      (newSuffix := newSuffix) hbranch hdepths hdisplay hpreLen hsuffixLen
  refine ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
    hleavesPerm, ?_⟩
  simpa [swappedPairs, newPre, newSuffix, List.append_assoc] using
    hrealizedEq

/-- One-slot overlap consumer for the contraction-aware branch bridge.  This
covers the branch where the left leaf of the old contracted pair is already
the first selected smallest weight, so only the second selected slot is moved
into the sibling pair. -/
theorem
    exists_relabelLeaves_contract_for_left_deepest_first_smallest_after_contracted_pair
    {tree contracted : InsertionScheduleTree} {depth : ℕ} {a c : ℝ}
    (hcontract : SiblingLeafContract tree contracted a c) :
    ∃ parentDepth : ℕ, ∃ oldPre oldSuffix : List (ℕ × ℝ),
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, a), (parentDepth + 1, c)] ++
          oldSuffix ∧
        leafDepthWeights depth contracted =
          oldPre ++ [(parentDepth, a + c)] ++ oldSuffix ∧
          ∀ {middle suffix rest : List (ℕ × ℝ)}
              {b : ℝ} {shallow : ℕ},
            oldSuffix = middle ++ [(shallow, b)] ++ suffix →
            (leafDepthWeights depth tree).Perm
              ((parentDepth + 1, a) :: (shallow, b) :: rest) →
            (∀ pair ∈ rest, b ≤ pair.2) →
            shallow ≤ parentDepth + 1 →
            ∃ swappedTree swappedContracted : InsertionScheduleTree,
              SiblingLeafContract swappedTree swappedContracted a b ∧
                weightedLeafDepthCost depth swappedTree ≤
                  weightedLeafDepthCost depth tree ∧
                  swappedTree.leaves.Perm tree.leaves ∧
                    leafDepthWeights depth swappedTree =
                      oldPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                        middle ++ [(shallow, c)] ++ suffix := by
  obtain ⟨parentDepth, oldPre, oldSuffix, htreeDepth,
    hcontractedDepth, hbridge⟩ :=
    exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_context_lengths
      hcontract
  refine ⟨parentDepth, oldPre, oldSuffix, htreeDepth, hcontractedDepth, ?_⟩
  intro middle suffix rest b shallow hsuffix htwoSmallest hrest hdepth
  let newSuffix := middle ++ [(shallow, c)] ++ suffix
  let swappedPairs :=
    oldPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
      newSuffix
  have hpairsPerm :
      (leafDepthWeights depth tree).Perm
        (oldPre ++ [(parentDepth + 1, a), (parentDepth + 1, c)] ++
          middle ++ [(shallow, b)] ++ suffix) := by
    rw [htreeDepth, hsuffix]
    simp [List.append_assoc]
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.leftDeepestFirstSmallest
      oldPre middle suffix rest hpairsPerm
      (by simp [swappedPairs, newSuffix, List.append_assoc])
      htwoSmallest hrest hdepth
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [htreeDepth, hsuffix]
    simp [swappedPairs, newSuffix, List.map_append]
  have hdisplay :
      swappedPairs =
        oldPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
          newSuffix := by
    rfl
  have hsuffixLen : newSuffix.length = oldSuffix.length := by
    rw [hsuffix]
    simp [newSuffix, List.length_append]
  obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
      hleavesPerm, hrealizedEq⟩ :=
    hbridge (swappedPairs := swappedPairs) (newPre := oldPre)
      (newSuffix := newSuffix) hbranch hdepths hdisplay rfl hsuffixLen
  refine ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
    hleavesPerm, ?_⟩
  simpa [swappedPairs, newSuffix, List.append_assoc] using hrealizedEq

/-- One-slot overlap consumer for the contraction-aware branch bridge where
the right leaf of the old contracted pair is already the first selected
smallest weight.  The normalized sibling orientation is `b, a`, matching the
tree-level right-deepest branch. -/
theorem
    exists_relabelLeaves_contract_for_right_deepest_first_smallest_after_contracted_pair
    {tree contracted : InsertionScheduleTree} {depth : ℕ} {a c : ℝ}
    (hcontract : SiblingLeafContract tree contracted c a) :
    ∃ parentDepth : ℕ, ∃ oldPre oldSuffix : List (ℕ × ℝ),
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, a)] ++
          oldSuffix ∧
        leafDepthWeights depth contracted =
          oldPre ++ [(parentDepth, c + a)] ++ oldSuffix ∧
          ∀ {middle suffix rest : List (ℕ × ℝ)}
              {b : ℝ} {shallow : ℕ},
            oldSuffix = middle ++ [(shallow, b)] ++ suffix →
            (leafDepthWeights depth tree).Perm
              ((parentDepth + 1, a) :: (shallow, b) :: rest) →
            (∀ pair ∈ rest, b ≤ pair.2) →
            shallow ≤ parentDepth + 1 →
            ∃ swappedTree swappedContracted : InsertionScheduleTree,
              SiblingLeafContract swappedTree swappedContracted b a ∧
                weightedLeafDepthCost depth swappedTree ≤
                  weightedLeafDepthCost depth tree ∧
                  swappedTree.leaves.Perm tree.leaves ∧
                    leafDepthWeights depth swappedTree =
                      oldPre ++ [(parentDepth + 1, b), (parentDepth + 1, a)] ++
                        middle ++ [(shallow, c)] ++ suffix := by
  obtain ⟨parentDepth, oldPre, oldSuffix, htreeDepth,
    hcontractedDepth, hbridge⟩ :=
    exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_context_lengths
      hcontract
  refine ⟨parentDepth, oldPre, oldSuffix, htreeDepth, hcontractedDepth, ?_⟩
  intro middle suffix rest b shallow hsuffix htwoSmallest hrest hdepth
  let newSuffix := middle ++ [(shallow, c)] ++ suffix
  let swappedPairs :=
    oldPre ++ [(parentDepth + 1, b), (parentDepth + 1, a)] ++
      newSuffix
  have hpairsPerm :
      (leafDepthWeights depth tree).Perm
        (oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, a)] ++
          middle ++ [(shallow, b)] ++ suffix) := by
    rw [htreeDepth, hsuffix]
    simp [List.append_assoc]
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.rightDeepestFirstSmallest
      oldPre middle suffix rest hpairsPerm
      (by simp [swappedPairs, newSuffix, List.append_assoc])
      htwoSmallest hrest hdepth
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [htreeDepth, hsuffix]
    simp [swappedPairs, newSuffix, List.map_append]
  have hdisplay :
      swappedPairs =
        oldPre ++ [(parentDepth + 1, b), (parentDepth + 1, a)] ++
          newSuffix := by
    rfl
  have hsuffixLen : newSuffix.length = oldSuffix.length := by
    rw [hsuffix]
    simp [newSuffix, List.length_append]
  obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
      hleavesPerm, hrealizedEq⟩ :=
    hbridge (swappedPairs := swappedPairs) (newPre := oldPre)
      (newSuffix := newSuffix) (a := b) (b := a)
      hbranch hdepths hdisplay rfl hsuffixLen
  refine ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
    hleavesPerm, ?_⟩
  simpa [swappedPairs, newSuffix, List.append_assoc] using hrealizedEq

/-- One-slot overlap consumer where the left leaf of the old contracted pair
is already the second selected smallest weight. -/
theorem
    exists_relabelLeaves_contract_for_left_deepest_second_smallest_after_contracted_pair
    {tree contracted : InsertionScheduleTree} {depth : ℕ} {b c : ℝ}
    (hcontract : SiblingLeafContract tree contracted b c) :
    ∃ parentDepth : ℕ, ∃ oldPre oldSuffix : List (ℕ × ℝ),
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, b), (parentDepth + 1, c)] ++
          oldSuffix ∧
        leafDepthWeights depth contracted =
          oldPre ++ [(parentDepth, b + c)] ++ oldSuffix ∧
          ∀ {middle suffix rest : List (ℕ × ℝ)}
              {a : ℝ} {shallow : ℕ},
            oldSuffix = middle ++ [(shallow, a)] ++ suffix →
            (leafDepthWeights depth tree).Perm
              ((shallow, a) :: (parentDepth + 1, b) :: rest) →
            a ≤ b →
            (∀ pair ∈ rest, b ≤ pair.2) →
            shallow ≤ parentDepth + 1 →
            ∃ swappedTree swappedContracted : InsertionScheduleTree,
              SiblingLeafContract swappedTree swappedContracted b a ∧
                weightedLeafDepthCost depth swappedTree ≤
                  weightedLeafDepthCost depth tree ∧
                  swappedTree.leaves.Perm tree.leaves ∧
                    leafDepthWeights depth swappedTree =
                      oldPre ++ [(parentDepth + 1, b), (parentDepth + 1, a)] ++
                        middle ++ [(shallow, c)] ++ suffix := by
  obtain ⟨parentDepth, oldPre, oldSuffix, htreeDepth,
    hcontractedDepth, hbridge⟩ :=
    exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_context_lengths
      hcontract
  refine ⟨parentDepth, oldPre, oldSuffix, htreeDepth, hcontractedDepth, ?_⟩
  intro middle suffix rest a shallow hsuffix htwoSmallest hab hrest hdepth
  let newSuffix := middle ++ [(shallow, c)] ++ suffix
  let swappedPairs :=
    oldPre ++ [(parentDepth + 1, b), (parentDepth + 1, a)] ++
      newSuffix
  have hpairsPerm :
      (leafDepthWeights depth tree).Perm
        (oldPre ++ [(parentDepth + 1, b), (parentDepth + 1, c)] ++
          middle ++ [(shallow, a)] ++ suffix) := by
    rw [htreeDepth, hsuffix]
    simp [List.append_assoc]
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.leftDeepestSecondSmallest
      oldPre middle suffix rest hpairsPerm
      (by simp [swappedPairs, newSuffix, List.append_assoc])
      htwoSmallest hab hrest hdepth
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [htreeDepth, hsuffix]
    simp [swappedPairs, newSuffix, List.map_append]
  have hdisplay :
      swappedPairs =
        oldPre ++ [(parentDepth + 1, b), (parentDepth + 1, a)] ++
          newSuffix := by
    rfl
  have hsuffixLen : newSuffix.length = oldSuffix.length := by
    rw [hsuffix]
    simp [newSuffix, List.length_append]
  obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
      hleavesPerm, hrealizedEq⟩ :=
    hbridge (swappedPairs := swappedPairs) (newPre := oldPre)
      (newSuffix := newSuffix) (a := b) (b := a)
      hbranch hdepths hdisplay rfl hsuffixLen
  refine ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
    hleavesPerm, ?_⟩
  simpa [swappedPairs, newSuffix, List.append_assoc] using hrealizedEq

/-- One-slot overlap consumer where the right leaf of the old contracted pair
is already the second selected smallest weight. -/
theorem
    exists_relabelLeaves_contract_for_right_deepest_second_smallest_after_contracted_pair
    {tree contracted : InsertionScheduleTree} {depth : ℕ} {b c : ℝ}
    (hcontract : SiblingLeafContract tree contracted c b) :
    ∃ parentDepth : ℕ, ∃ oldPre oldSuffix : List (ℕ × ℝ),
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, b)] ++
          oldSuffix ∧
        leafDepthWeights depth contracted =
          oldPre ++ [(parentDepth, c + b)] ++ oldSuffix ∧
          ∀ {middle suffix rest : List (ℕ × ℝ)}
              {a : ℝ} {shallow : ℕ},
            oldSuffix = middle ++ [(shallow, a)] ++ suffix →
            (leafDepthWeights depth tree).Perm
              ((shallow, a) :: (parentDepth + 1, b) :: rest) →
            a ≤ b →
            (∀ pair ∈ rest, b ≤ pair.2) →
            shallow ≤ parentDepth + 1 →
            ∃ swappedTree swappedContracted : InsertionScheduleTree,
              SiblingLeafContract swappedTree swappedContracted a b ∧
                weightedLeafDepthCost depth swappedTree ≤
                  weightedLeafDepthCost depth tree ∧
                  swappedTree.leaves.Perm tree.leaves ∧
                    leafDepthWeights depth swappedTree =
                      oldPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                        middle ++ [(shallow, c)] ++ suffix := by
  obtain ⟨parentDepth, oldPre, oldSuffix, htreeDepth,
    hcontractedDepth, hbridge⟩ :=
    exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_context_lengths
      hcontract
  refine ⟨parentDepth, oldPre, oldSuffix, htreeDepth, hcontractedDepth, ?_⟩
  intro middle suffix rest a shallow hsuffix htwoSmallest hab hrest hdepth
  let newSuffix := middle ++ [(shallow, c)] ++ suffix
  let swappedPairs :=
    oldPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
      newSuffix
  have hpairsPerm :
      (leafDepthWeights depth tree).Perm
        (oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, b)] ++
          middle ++ [(shallow, a)] ++ suffix) := by
    rw [htreeDepth, hsuffix]
    simp [List.append_assoc]
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.rightDeepestSecondSmallest
      oldPre middle suffix rest hpairsPerm
      (by simp [swappedPairs, newSuffix, List.append_assoc])
      htwoSmallest hab hrest hdepth
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [htreeDepth, hsuffix]
    simp [swappedPairs, newSuffix, List.map_append]
  have hdisplay :
      swappedPairs =
        oldPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
          newSuffix := by
    rfl
  have hsuffixLen : newSuffix.length = oldSuffix.length := by
    rw [hsuffix]
    simp [newSuffix, List.length_append]
  obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
      hleavesPerm, hrealizedEq⟩ :=
    hbridge (swappedPairs := swappedPairs) (newPre := oldPre)
      (newSuffix := newSuffix) hbranch hdepths hdisplay rfl hsuffixLen
  refine ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
    hleavesPerm, ?_⟩
  simpa [swappedPairs, newSuffix, List.append_assoc] using hrealizedEq

/-- One-slot overlap consumer where the left leaf of the old contracted pair
is already the first selected smallest weight and the other selected slot is
before the contracted pair. -/
theorem
    exists_relabelLeaves_contract_for_left_deepest_first_smallest_before_contracted_pair
    {tree contracted : InsertionScheduleTree} {depth : ℕ} {a c : ℝ}
    (hcontract : SiblingLeafContract tree contracted a c) :
    ∃ parentDepth : ℕ, ∃ oldPre oldSuffix : List (ℕ × ℝ),
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, a), (parentDepth + 1, c)] ++
          oldSuffix ∧
        leafDepthWeights depth contracted =
          oldPre ++ [(parentDepth, a + c)] ++ oldSuffix ∧
          ∀ {pre₀ middle rest : List (ℕ × ℝ)}
              {b : ℝ} {shallow : ℕ},
            oldPre = pre₀ ++ [(shallow, b)] ++ middle →
            (leafDepthWeights depth tree).Perm
              ((parentDepth + 1, a) :: (shallow, b) :: rest) →
            (∀ pair ∈ rest, b ≤ pair.2) →
            shallow ≤ parentDepth + 1 →
            ∃ swappedTree swappedContracted : InsertionScheduleTree,
              SiblingLeafContract swappedTree swappedContracted a b ∧
                weightedLeafDepthCost depth swappedTree ≤
                  weightedLeafDepthCost depth tree ∧
                  swappedTree.leaves.Perm tree.leaves ∧
                    leafDepthWeights depth swappedTree =
                      pre₀ ++ [(shallow, c)] ++ middle ++
                        [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                          oldSuffix := by
  obtain ⟨parentDepth, oldPre, oldSuffix, htreeDepth,
    hcontractedDepth, hbridge⟩ :=
    exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_context_lengths
      hcontract
  refine ⟨parentDepth, oldPre, oldSuffix, htreeDepth, hcontractedDepth, ?_⟩
  intro pre₀ middle rest b shallow hpre htwoSmallest hrest hdepth
  let newPre := pre₀ ++ [(shallow, c)] ++ middle
  let swappedPairs :=
    newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
      oldSuffix
  have hpairsPerm :
      (leafDepthWeights depth tree).Perm
        (pre₀ ++ [(parentDepth + 1, a), (parentDepth + 1, c)] ++
          middle ++ [(shallow, b)] ++ oldSuffix) := by
    rw [htreeDepth, hpre]
    simpa [List.append_assoc] using
      (listPerm_selected_before_adjacent_to_after
        pre₀ middle oldSuffix (shallow, b)
        (parentDepth + 1, a) (parentDepth + 1, c))
  have hswappedPerm :
      swappedPairs.Perm
        (pre₀ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
          middle ++ [(shallow, c)] ++ oldSuffix) := by
    simpa [swappedPairs, newPre, List.append_assoc] using
      (listPerm_selected_before_adjacent_to_after
        pre₀ middle oldSuffix (shallow, c)
        (parentDepth + 1, a) (parentDepth + 1, b))
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.leftDeepestFirstSmallest
      pre₀ middle oldSuffix rest hpairsPerm hswappedPerm
      htwoSmallest hrest hdepth
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [htreeDepth, hpre]
    simp [swappedPairs, newPre, List.map_append]
  have hdisplay :
      swappedPairs =
        newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
          oldSuffix := by
    rfl
  have hpreLen : newPre.length = oldPre.length := by
    rw [hpre]
    simp [newPre, List.length_append]
  obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
      hleavesPerm, hrealizedEq⟩ :=
    hbridge (swappedPairs := swappedPairs) (newPre := newPre)
      (newSuffix := oldSuffix) hbranch hdepths hdisplay hpreLen rfl
  refine ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
    hleavesPerm, ?_⟩
  simpa [swappedPairs, newPre, List.append_assoc] using hrealizedEq

/-- One-slot overlap consumer where the right leaf of the old contracted pair
is already the first selected smallest weight and the other selected slot is
before the contracted pair. -/
theorem
    exists_relabelLeaves_contract_for_right_deepest_first_smallest_before_contracted_pair
    {tree contracted : InsertionScheduleTree} {depth : ℕ} {a c : ℝ}
    (hcontract : SiblingLeafContract tree contracted c a) :
    ∃ parentDepth : ℕ, ∃ oldPre oldSuffix : List (ℕ × ℝ),
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, a)] ++
          oldSuffix ∧
        leafDepthWeights depth contracted =
          oldPre ++ [(parentDepth, c + a)] ++ oldSuffix ∧
          ∀ {pre₀ middle rest : List (ℕ × ℝ)}
              {b : ℝ} {shallow : ℕ},
            oldPre = pre₀ ++ [(shallow, b)] ++ middle →
            (leafDepthWeights depth tree).Perm
              ((parentDepth + 1, a) :: (shallow, b) :: rest) →
            (∀ pair ∈ rest, b ≤ pair.2) →
            shallow ≤ parentDepth + 1 →
            ∃ swappedTree swappedContracted : InsertionScheduleTree,
              SiblingLeafContract swappedTree swappedContracted b a ∧
                weightedLeafDepthCost depth swappedTree ≤
                  weightedLeafDepthCost depth tree ∧
                  swappedTree.leaves.Perm tree.leaves ∧
                    leafDepthWeights depth swappedTree =
                      pre₀ ++ [(shallow, c)] ++ middle ++
                        [(parentDepth + 1, b), (parentDepth + 1, a)] ++
                          oldSuffix := by
  obtain ⟨parentDepth, oldPre, oldSuffix, htreeDepth,
    hcontractedDepth, hbridge⟩ :=
    exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_context_lengths
      hcontract
  refine ⟨parentDepth, oldPre, oldSuffix, htreeDepth, hcontractedDepth, ?_⟩
  intro pre₀ middle rest b shallow hpre htwoSmallest hrest hdepth
  let newPre := pre₀ ++ [(shallow, c)] ++ middle
  let swappedPairs :=
    newPre ++ [(parentDepth + 1, b), (parentDepth + 1, a)] ++
      oldSuffix
  have hpairsPerm :
      (leafDepthWeights depth tree).Perm
        (pre₀ ++ [(parentDepth + 1, c), (parentDepth + 1, a)] ++
          middle ++ [(shallow, b)] ++ oldSuffix) := by
    rw [htreeDepth, hpre]
    simpa [List.append_assoc] using
      (listPerm_selected_before_adjacent_to_after
        pre₀ middle oldSuffix (shallow, b)
        (parentDepth + 1, c) (parentDepth + 1, a))
  have hswappedPerm :
      swappedPairs.Perm
        (pre₀ ++ [(parentDepth + 1, b), (parentDepth + 1, a)] ++
          middle ++ [(shallow, c)] ++ oldSuffix) := by
    simpa [swappedPairs, newPre, List.append_assoc] using
      (listPerm_selected_before_adjacent_to_after
        pre₀ middle oldSuffix (shallow, c)
        (parentDepth + 1, b) (parentDepth + 1, a))
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.rightDeepestFirstSmallest
      pre₀ middle oldSuffix rest hpairsPerm hswappedPerm
      htwoSmallest hrest hdepth
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [htreeDepth, hpre]
    simp [swappedPairs, newPre, List.map_append]
  have hdisplay :
      swappedPairs =
        newPre ++ [(parentDepth + 1, b), (parentDepth + 1, a)] ++
          oldSuffix := by
    rfl
  have hpreLen : newPre.length = oldPre.length := by
    rw [hpre]
    simp [newPre, List.length_append]
  obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
      hleavesPerm, hrealizedEq⟩ :=
    hbridge (swappedPairs := swappedPairs) (newPre := newPre)
      (newSuffix := oldSuffix) (a := b) (b := a)
      hbranch hdepths hdisplay hpreLen rfl
  refine ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
    hleavesPerm, ?_⟩
  simpa [swappedPairs, newPre, List.append_assoc] using hrealizedEq

/-- One-slot overlap consumer where the left leaf of the old contracted pair
is already the second selected smallest weight and the other selected slot is
before the contracted pair. -/
theorem
    exists_relabelLeaves_contract_for_left_deepest_second_smallest_before_contracted_pair
    {tree contracted : InsertionScheduleTree} {depth : ℕ} {b c : ℝ}
    (hcontract : SiblingLeafContract tree contracted b c) :
    ∃ parentDepth : ℕ, ∃ oldPre oldSuffix : List (ℕ × ℝ),
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, b), (parentDepth + 1, c)] ++
          oldSuffix ∧
        leafDepthWeights depth contracted =
          oldPre ++ [(parentDepth, b + c)] ++ oldSuffix ∧
          ∀ {pre₀ middle rest : List (ℕ × ℝ)}
              {a : ℝ} {shallow : ℕ},
            oldPre = pre₀ ++ [(shallow, a)] ++ middle →
            (leafDepthWeights depth tree).Perm
              ((shallow, a) :: (parentDepth + 1, b) :: rest) →
            a ≤ b →
            (∀ pair ∈ rest, b ≤ pair.2) →
            shallow ≤ parentDepth + 1 →
            ∃ swappedTree swappedContracted : InsertionScheduleTree,
              SiblingLeafContract swappedTree swappedContracted b a ∧
                weightedLeafDepthCost depth swappedTree ≤
                  weightedLeafDepthCost depth tree ∧
                  swappedTree.leaves.Perm tree.leaves ∧
                    leafDepthWeights depth swappedTree =
                      pre₀ ++ [(shallow, c)] ++ middle ++
                        [(parentDepth + 1, b), (parentDepth + 1, a)] ++
                          oldSuffix := by
  obtain ⟨parentDepth, oldPre, oldSuffix, htreeDepth,
    hcontractedDepth, hbridge⟩ :=
    exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_context_lengths
      hcontract
  refine ⟨parentDepth, oldPre, oldSuffix, htreeDepth, hcontractedDepth, ?_⟩
  intro pre₀ middle rest a shallow hpre htwoSmallest hab hrest hdepth
  let newPre := pre₀ ++ [(shallow, c)] ++ middle
  let swappedPairs :=
    newPre ++ [(parentDepth + 1, b), (parentDepth + 1, a)] ++
      oldSuffix
  have hpairsPerm :
      (leafDepthWeights depth tree).Perm
        (pre₀ ++ [(parentDepth + 1, b), (parentDepth + 1, c)] ++
          middle ++ [(shallow, a)] ++ oldSuffix) := by
    rw [htreeDepth, hpre]
    simpa [List.append_assoc] using
      (listPerm_selected_before_adjacent_to_after
        pre₀ middle oldSuffix (shallow, a)
        (parentDepth + 1, b) (parentDepth + 1, c))
  have hswappedPerm :
      swappedPairs.Perm
        (pre₀ ++ [(parentDepth + 1, b), (parentDepth + 1, a)] ++
          middle ++ [(shallow, c)] ++ oldSuffix) := by
    simpa [swappedPairs, newPre, List.append_assoc] using
      (listPerm_selected_before_adjacent_to_after
        pre₀ middle oldSuffix (shallow, c)
        (parentDepth + 1, b) (parentDepth + 1, a))
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.leftDeepestSecondSmallest
      pre₀ middle oldSuffix rest hpairsPerm hswappedPerm
      htwoSmallest hab hrest hdepth
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [htreeDepth, hpre]
    simp [swappedPairs, newPre, List.map_append]
  have hdisplay :
      swappedPairs =
        newPre ++ [(parentDepth + 1, b), (parentDepth + 1, a)] ++
          oldSuffix := by
    rfl
  have hpreLen : newPre.length = oldPre.length := by
    rw [hpre]
    simp [newPre, List.length_append]
  obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
      hleavesPerm, hrealizedEq⟩ :=
    hbridge (swappedPairs := swappedPairs) (newPre := newPre)
      (newSuffix := oldSuffix) (a := b) (b := a)
      hbranch hdepths hdisplay hpreLen rfl
  refine ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
    hleavesPerm, ?_⟩
  simpa [swappedPairs, newPre, List.append_assoc] using hrealizedEq

/-- One-slot overlap consumer where the right leaf of the old contracted pair
is already the second selected smallest weight and the other selected slot is
before the contracted pair. -/
theorem
    exists_relabelLeaves_contract_for_right_deepest_second_smallest_before_contracted_pair
    {tree contracted : InsertionScheduleTree} {depth : ℕ} {b c : ℝ}
    (hcontract : SiblingLeafContract tree contracted c b) :
    ∃ parentDepth : ℕ, ∃ oldPre oldSuffix : List (ℕ × ℝ),
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, b)] ++
          oldSuffix ∧
        leafDepthWeights depth contracted =
          oldPre ++ [(parentDepth, c + b)] ++ oldSuffix ∧
          ∀ {pre₀ middle rest : List (ℕ × ℝ)}
              {a : ℝ} {shallow : ℕ},
            oldPre = pre₀ ++ [(shallow, a)] ++ middle →
            (leafDepthWeights depth tree).Perm
              ((shallow, a) :: (parentDepth + 1, b) :: rest) →
            a ≤ b →
            (∀ pair ∈ rest, b ≤ pair.2) →
            shallow ≤ parentDepth + 1 →
            ∃ swappedTree swappedContracted : InsertionScheduleTree,
              SiblingLeafContract swappedTree swappedContracted a b ∧
                weightedLeafDepthCost depth swappedTree ≤
                  weightedLeafDepthCost depth tree ∧
                  swappedTree.leaves.Perm tree.leaves ∧
                    leafDepthWeights depth swappedTree =
                      pre₀ ++ [(shallow, c)] ++ middle ++
                        [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                          oldSuffix := by
  obtain ⟨parentDepth, oldPre, oldSuffix, htreeDepth,
    hcontractedDepth, hbridge⟩ :=
    exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_context_lengths
      hcontract
  refine ⟨parentDepth, oldPre, oldSuffix, htreeDepth, hcontractedDepth, ?_⟩
  intro pre₀ middle rest a shallow hpre htwoSmallest hab hrest hdepth
  let newPre := pre₀ ++ [(shallow, c)] ++ middle
  let swappedPairs :=
    newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
      oldSuffix
  have hpairsPerm :
      (leafDepthWeights depth tree).Perm
        (pre₀ ++ [(parentDepth + 1, c), (parentDepth + 1, b)] ++
          middle ++ [(shallow, a)] ++ oldSuffix) := by
    rw [htreeDepth, hpre]
    simpa [List.append_assoc] using
      (listPerm_selected_before_adjacent_to_after
        pre₀ middle oldSuffix (shallow, a)
        (parentDepth + 1, c) (parentDepth + 1, b))
  have hswappedPerm :
      swappedPairs.Perm
        (pre₀ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
          middle ++ [(shallow, c)] ++ oldSuffix) := by
    simpa [swappedPairs, newPre, List.append_assoc] using
      (listPerm_selected_before_adjacent_to_after
        pre₀ middle oldSuffix (shallow, c)
        (parentDepth + 1, a) (parentDepth + 1, b))
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.rightDeepestSecondSmallest
      pre₀ middle oldSuffix rest hpairsPerm hswappedPerm
      htwoSmallest hab hrest hdepth
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [htreeDepth, hpre]
    simp [swappedPairs, newPre, List.map_append]
  have hdisplay :
      swappedPairs =
        newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
          oldSuffix := by
    rfl
  have hpreLen : newPre.length = oldPre.length := by
    rw [hpre]
    simp [newPre, List.length_append]
  obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
      hleavesPerm, hrealizedEq⟩ :=
    hbridge (swappedPairs := swappedPairs) (newPre := newPre)
      (newSuffix := oldSuffix) hbranch hdepths hdisplay hpreLen rfl
  refine ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
    hleavesPerm, ?_⟩
  simpa [swappedPairs, newPre, List.append_assoc] using hrealizedEq

/-- No-op contraction-normalization branch.  If the old contracted sibling
pair is already the selected sibling pair, the original tree and contracted
tree are already a normalized `SiblingLeafContract` witness. -/
theorem exists_relabelLeaves_contract_for_deepest_pair_noop
    {tree contracted : InsertionScheduleTree} {depth : ℕ} {a b : ℝ}
    (hcontract : SiblingLeafContract tree contracted a b) :
    ∃ parentDepth : ℕ, ∃ oldPre oldSuffix : List (ℕ × ℝ),
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
          oldSuffix ∧
        leafDepthWeights depth contracted =
          oldPre ++ [(parentDepth, a + b)] ++ oldSuffix ∧
          ∃ swappedTree swappedContracted : InsertionScheduleTree,
            SiblingLeafContract swappedTree swappedContracted a b ∧
              weightedLeafDepthCost depth swappedTree ≤
                weightedLeafDepthCost depth tree ∧
                swappedTree.leaves.Perm tree.leaves ∧
                  leafDepthWeights depth swappedTree =
                    oldPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                      oldSuffix := by
  obtain ⟨parentDepth, oldPre, oldSuffix, htreeDepth,
    hcontractedDepth⟩ :=
    SiblingLeafContract.exists_leafDepthWeights_context depth hcontract
  refine ⟨parentDepth, oldPre, oldSuffix, htreeDepth, hcontractedDepth,
    tree, contracted, hcontract, le_rfl, List.Perm.refl tree.leaves, ?_⟩
  exact htreeDepth

/-- Combined contraction-aware nonoverlap classifier for the orientation where
the first selected two-smallest slot is before the old contracted sibling
pair.  If the second selected slot is not one of the contracted siblings, the
finite occurrence split selects the reverse-before, before, or around
normalization branch and returns an actual normalized `SiblingLeafContract`. -/
theorem
    exists_relabelLeaves_contract_for_first_before_contracted_pair_nonoverlap_anywhere
    {tree contracted : InsertionScheduleTree} {depth : ℕ} {c d : ℝ}
    (hcontract : SiblingLeafContract tree contracted c d) :
    ∃ parentDepth : ℕ, ∃ oldPre oldSuffix : List (ℕ × ℝ),
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          oldSuffix ∧
        leafDepthWeights depth contracted =
          oldPre ++ [(parentDepth, c + d)] ++ oldSuffix ∧
          ∀ {before middle suffix rest : List (ℕ × ℝ)}
              {a b : ℝ} {shallow₁ shallow₂ : ℕ},
            oldPre = before ++ [(shallow₁, a)] ++ middle →
            oldSuffix = suffix →
            (leafDepthWeights depth tree).Perm
              ((shallow₁, a) :: (shallow₂, b) :: rest) →
            a ≤ b →
            (∀ pair ∈ rest, b ≤ pair.2) →
            shallow₁ ≤ parentDepth + 1 →
            shallow₂ ≤ parentDepth + 1 →
            (shallow₂, b) ≠ (parentDepth + 1, c) →
            (shallow₂, b) ≠ (parentDepth + 1, d) →
            ∃ swappedTree swappedContracted : InsertionScheduleTree,
              SiblingLeafContract swappedTree swappedContracted a b ∧
                weightedLeafDepthCost depth swappedTree ≤
                  weightedLeafDepthCost depth tree ∧
                  swappedTree.leaves.Perm tree.leaves := by
  obtain ⟨parentDepth, oldPre, oldSuffix, htreeDepth,
    hcontractedDepth, hbridge⟩ :=
    exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_context_lengths
      hcontract
  refine ⟨parentDepth, oldPre, oldSuffix, htreeDepth, hcontractedDepth, ?_⟩
  intro before middle suffix rest a b shallow₁ shallow₂ hpre hsuffix
    htwoSmallest hab hrest hdepth₁ hdepth₂ hsecond_ne_left
    hsecond_ne_right
  have hpairsDisplay :
      leafDepthWeights depth tree =
        before ++ [(shallow₁, a)] ++ middle ++
          [(parentDepth + 1, c), (parentDepth + 1, d)] ++ suffix := by
    rw [htreeDepth, hpre, hsuffix]
  obtain hloc :=
    exists_second_position_of_first_before_adjacent_pair
      (pairs := leafDepthWeights depth tree) (rest := rest)
      (first := (shallow₁, a)) (second := (shallow₂, b))
      (left := (parentDepth + 1, c))
      (right := (parentDepth + 1, d))
      before middle suffix hpairsDisplay htwoSmallest
      hsecond_ne_left hsecond_ne_right
  rcases hloc with hsecondBefore | hsecondMiddle | hsecondAfter
  · obtain ⟨pre₂, gap, hbeforeSplit, hpairs'⟩ := hsecondBefore
    let newPre :=
      pre₂ ++ [(shallow₂, d)] ++ gap ++ [(shallow₁, c)] ++ middle
    let swappedPairs :=
      newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
        suffix
    have hpairsPerm :
        (leafDepthWeights depth tree).Perm
          (pre₂ ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
            gap ++ [(shallow₁, a)] ++ middle ++
              [(shallow₂, b)] ++ suffix) := by
      rw [hpairs']
      simpa [List.append_assoc] using
        (listPerm_two_selected_before_deepest_to_canonical
          pre₂ gap middle suffix
          (parentDepth + 1, c) (parentDepth + 1, d)
          (shallow₂, b) (shallow₁, a)).trans
          (weightListPerm_pair_exchange
            (pre₂ ++ [(parentDepth + 1, c),
              (parentDepth + 1, d)] ++ gap)
            middle suffix (shallow₂, b) (shallow₁, a))
    have hswappedToReverseCanonical :
        swappedPairs.Perm
          (pre₂ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            gap ++ [(shallow₂, d)] ++ middle ++
              [(shallow₁, c)] ++ suffix) := by
      simpa [swappedPairs, newPre, List.append_assoc] using
        (listPerm_two_selected_before_deepest_to_canonical
          pre₂ gap middle suffix
          (parentDepth + 1, a) (parentDepth + 1, b)
          (shallow₂, d) (shallow₁, c))
    have hswappedPerm :
        swappedPairs.Perm
          (pre₂ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            gap ++ [(shallow₁, c)] ++ middle ++
              [(shallow₂, d)] ++ suffix) := by
      exact hswappedToReverseCanonical.trans
        (weightListPerm_pair_exchange
          (pre₂ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            gap)
          middle suffix (shallow₂, d) (shallow₁, c))
    have hbranch :
        TwoSmallestDeepestExchangeBranch
          (leafDepthWeights depth tree) swappedPairs := by
      exact TwoSmallestDeepestExchangeBranch.nondegenerate
        pre₂ gap middle suffix rest hpairsPerm hswappedPerm
        htwoSmallest hab hrest hdepth₁ hdepth₂
    have hdepths :
        swappedPairs.map Prod.fst =
          (leafDepthWeights depth tree).map Prod.fst := by
      rw [hpairs']
      simp [swappedPairs, newPre, List.map_append]
    have hdisplay :
        swappedPairs =
          newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            suffix := by
      rfl
    have hpreLen : newPre.length = oldPre.length := by
      rw [hpre, hbeforeSplit]
      simp [newPre, List.length_append]
    obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
        hleavesPerm, _hrealizedEq⟩ :=
      hbridge (swappedPairs := swappedPairs) (newPre := newPre)
        (newSuffix := suffix) hbranch hdepths hdisplay hpreLen (by
          rw [hsuffix])
    exact ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
      hleavesPerm⟩
  · obtain ⟨gap, tail, hmiddleSplit, hpairs'⟩ := hsecondMiddle
    let newPre :=
      before ++ [(shallow₁, c)] ++ gap ++ [(shallow₂, d)] ++ tail
    let swappedPairs :=
      newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
        suffix
    have hpairsPerm :
        (leafDepthWeights depth tree).Perm
          (before ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
            gap ++ [(shallow₁, a)] ++ tail ++
              [(shallow₂, b)] ++ suffix) := by
      rw [hpairs']
      exact listPerm_two_selected_before_deepest_to_canonical
        before gap tail suffix
        (parentDepth + 1, c) (parentDepth + 1, d)
        (shallow₁, a) (shallow₂, b)
    have hswappedPerm :
        swappedPairs.Perm
          (before ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            gap ++ [(shallow₁, c)] ++ tail ++
              [(shallow₂, d)] ++ suffix) := by
      simpa [swappedPairs, newPre, List.append_assoc] using
        (listPerm_two_selected_before_deepest_to_canonical
          before gap tail suffix
          (parentDepth + 1, a) (parentDepth + 1, b)
          (shallow₁, c) (shallow₂, d))
    have hbranch :
        TwoSmallestDeepestExchangeBranch
          (leafDepthWeights depth tree) swappedPairs := by
      exact TwoSmallestDeepestExchangeBranch.nondegenerate
        before gap tail suffix rest hpairsPerm hswappedPerm
        htwoSmallest hab hrest hdepth₁ hdepth₂
    have hdepths :
        swappedPairs.map Prod.fst =
          (leafDepthWeights depth tree).map Prod.fst := by
      rw [hpairs']
      simp [swappedPairs, newPre, List.map_append]
    have hdisplay :
        swappedPairs =
          newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            suffix := by
      rfl
    have hpreLen : newPre.length = oldPre.length := by
      rw [hpre]
      rw [hmiddleSplit]
      simp [newPre, List.length_append]
    obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
        hleavesPerm, _hrealizedEq⟩ :=
      hbridge (swappedPairs := swappedPairs) (newPre := newPre)
        (newSuffix := suffix) hbranch hdepths hdisplay hpreLen (by
          rw [hsuffix])
    exact ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
      hleavesPerm⟩
  · obtain ⟨gap, tail, hsuffixSplit, hpairs'⟩ := hsecondAfter
    let newPre := before ++ [(shallow₁, c)] ++ middle
    let newSuffix := gap ++ [(shallow₂, d)] ++ tail
    let swappedPairs :=
      newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
        newSuffix
    have hpairsPerm :
        (leafDepthWeights depth tree).Perm
          (before ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
            middle ++ [(shallow₁, a)] ++ gap ++
              [(shallow₂, b)] ++ tail) := by
      rw [hpairs']
      exact listPerm_selected_before_deepest_before_selected_to_canonical
        before middle gap tail
        (parentDepth + 1, c) (parentDepth + 1, d)
        (shallow₁, a) (shallow₂, b)
    have hswappedPerm :
        swappedPairs.Perm
          (before ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            middle ++ [(shallow₁, c)] ++ gap ++
              [(shallow₂, d)] ++ tail) := by
      simpa [swappedPairs, newPre, newSuffix, List.append_assoc] using
        (listPerm_selected_before_deepest_before_selected_to_canonical
          before middle gap tail
          (parentDepth + 1, a) (parentDepth + 1, b)
          (shallow₁, c) (shallow₂, d))
    have hbranch :
        TwoSmallestDeepestExchangeBranch
          (leafDepthWeights depth tree) swappedPairs := by
      exact TwoSmallestDeepestExchangeBranch.nondegenerate
        before middle gap tail rest hpairsPerm hswappedPerm
        htwoSmallest hab hrest hdepth₁ hdepth₂
    have hdepths :
        swappedPairs.map Prod.fst =
          (leafDepthWeights depth tree).map Prod.fst := by
      rw [hpairs']
      simp [swappedPairs, newPre, newSuffix, List.map_append]
    have hdisplay :
        swappedPairs =
          newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            newSuffix := by
      rfl
    have hpreLen : newPre.length = oldPre.length := by
      rw [hpre]
      simp [newPre, List.length_append]
    have hsuffixLen : newSuffix.length = oldSuffix.length := by
      rw [hsuffix, hsuffixSplit]
      simp [newSuffix, List.length_append]
    obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
        hleavesPerm, _hrealizedEq⟩ :=
      hbridge (swappedPairs := swappedPairs) (newPre := newPre)
        (newSuffix := newSuffix) hbranch hdepths hdisplay hpreLen
        hsuffixLen
    exact ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
      hleavesPerm⟩

/-- Combined contraction-aware nonoverlap classifier for the orientation where
the first selected two-smallest slot is after the old contracted sibling pair.
If the second selected slot is not one of the contracted siblings, the finite
occurrence split selects the reverse-around, reverse-after, or after
normalization branch and returns an actual normalized `SiblingLeafContract`. -/
theorem
    exists_relabelLeaves_contract_for_first_after_contracted_pair_nonoverlap_anywhere
    {tree contracted : InsertionScheduleTree} {depth : ℕ} {c d : ℝ}
    (hcontract : SiblingLeafContract tree contracted c d) :
    ∃ parentDepth : ℕ, ∃ oldPre oldSuffix : List (ℕ × ℝ),
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          oldSuffix ∧
        leafDepthWeights depth contracted =
          oldPre ++ [(parentDepth, c + d)] ++ oldSuffix ∧
          ∀ {before middle suffix rest : List (ℕ × ℝ)}
              {a b : ℝ} {shallow₁ shallow₂ : ℕ},
            oldPre = before →
            oldSuffix = middle ++ [(shallow₁, a)] ++ suffix →
            (leafDepthWeights depth tree).Perm
              ((shallow₁, a) :: (shallow₂, b) :: rest) →
            a ≤ b →
            (∀ pair ∈ rest, b ≤ pair.2) →
            shallow₁ ≤ parentDepth + 1 →
            shallow₂ ≤ parentDepth + 1 →
            (shallow₂, b) ≠ (parentDepth + 1, c) →
            (shallow₂, b) ≠ (parentDepth + 1, d) →
            ∃ swappedTree swappedContracted : InsertionScheduleTree,
              SiblingLeafContract swappedTree swappedContracted a b ∧
                weightedLeafDepthCost depth swappedTree ≤
                  weightedLeafDepthCost depth tree ∧
                  swappedTree.leaves.Perm tree.leaves := by
  obtain ⟨parentDepth, oldPre, oldSuffix, htreeDepth,
    hcontractedDepth, hbridge⟩ :=
    exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_context_lengths
      hcontract
  refine ⟨parentDepth, oldPre, oldSuffix, htreeDepth, hcontractedDepth, ?_⟩
  intro before middle suffix rest a b shallow₁ shallow₂ hpre hsuffix
    htwoSmallest hab hrest hdepth₁ hdepth₂ hsecond_ne_left
    hsecond_ne_right
  have hpairsDisplay :
      leafDepthWeights depth tree =
        before ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          middle ++ [(shallow₁, a)] ++ suffix := by
    rw [htreeDepth, hpre, hsuffix]
    simp [List.append_assoc]
  obtain hloc :=
    exists_second_position_of_first_after_adjacent_pair
      (pairs := leafDepthWeights depth tree) (rest := rest)
      (first := (shallow₁, a)) (second := (shallow₂, b))
      (left := (parentDepth + 1, c))
      (right := (parentDepth + 1, d))
      before middle suffix hpairsDisplay htwoSmallest
      hsecond_ne_left hsecond_ne_right
  rcases hloc with hsecondBefore | hsecondMiddle | hsecondAfter
  · obtain ⟨pre₂, gap, hbeforeSplit, hpairs'⟩ := hsecondBefore
    let newPre := pre₂ ++ [(shallow₂, d)] ++ gap
    let newSuffix := middle ++ [(shallow₁, c)] ++ suffix
    let swappedPairs :=
      newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
        newSuffix
    have hpairsToReverseCanonical :
        (leafDepthWeights depth tree).Perm
          (pre₂ ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
            gap ++ [(shallow₂, b)] ++ middle ++
              [(shallow₁, a)] ++ suffix) := by
      rw [hpairs']
      simpa [List.append_assoc] using
        (listPerm_selected_before_deepest_before_selected_to_canonical
          pre₂ gap middle suffix
          (parentDepth + 1, c) (parentDepth + 1, d)
          (shallow₂, b) (shallow₁, a))
    have hpairsPerm :
        (leafDepthWeights depth tree).Perm
          (pre₂ ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
            gap ++ [(shallow₁, a)] ++ middle ++
              [(shallow₂, b)] ++ suffix) := by
      exact hpairsToReverseCanonical.trans
        (weightListPerm_pair_exchange
          (pre₂ ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
            gap)
          middle suffix (shallow₂, b) (shallow₁, a))
    have hswappedToReverseCanonical :
        swappedPairs.Perm
          (pre₂ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            gap ++ [(shallow₂, d)] ++ middle ++
              [(shallow₁, c)] ++ suffix) := by
      simpa [swappedPairs, newPre, newSuffix, List.append_assoc] using
        (listPerm_selected_before_deepest_before_selected_to_canonical
          pre₂ gap middle suffix
          (parentDepth + 1, a) (parentDepth + 1, b)
          (shallow₂, d) (shallow₁, c))
    have hswappedPerm :
        swappedPairs.Perm
          (pre₂ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            gap ++ [(shallow₁, c)] ++ middle ++
              [(shallow₂, d)] ++ suffix) := by
      exact hswappedToReverseCanonical.trans
        (weightListPerm_pair_exchange
          (pre₂ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            gap)
          middle suffix (shallow₂, d) (shallow₁, c))
    have hbranch :
        TwoSmallestDeepestExchangeBranch
          (leafDepthWeights depth tree) swappedPairs := by
      exact TwoSmallestDeepestExchangeBranch.nondegenerate
        pre₂ gap middle suffix rest hpairsPerm hswappedPerm
        htwoSmallest hab hrest hdepth₁ hdepth₂
    have hdepths :
        swappedPairs.map Prod.fst =
          (leafDepthWeights depth tree).map Prod.fst := by
      rw [hpairs']
      simp [swappedPairs, newPre, newSuffix, List.map_append]
    have hdisplay :
        swappedPairs =
          newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            newSuffix := by
      rfl
    have hpreLen : newPre.length = oldPre.length := by
      rw [hpre, hbeforeSplit]
      simp [newPre, List.length_append]
    have hsuffixLen : newSuffix.length = oldSuffix.length := by
      rw [hsuffix]
      simp [newSuffix, List.length_append]
    obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
        hleavesPerm, _hrealizedEq⟩ :=
      hbridge (swappedPairs := swappedPairs) (newPre := newPre)
        (newSuffix := newSuffix) hbranch hdepths hdisplay hpreLen
        hsuffixLen
    exact ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
      hleavesPerm⟩
  · obtain ⟨gap, tail, hmiddleSplit, hpairs'⟩ := hsecondMiddle
    let newPre := before
    let newSuffix :=
      gap ++ [(shallow₂, d)] ++ tail ++ [(shallow₁, c)] ++ suffix
    let swappedPairs :=
      newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
        newSuffix
    have hpairsPerm :
        (leafDepthWeights depth tree).Perm
          (before ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
            gap ++ [(shallow₁, a)] ++ tail ++
              [(shallow₂, b)] ++ suffix) := by
      rw [hpairs']
      simpa [List.append_assoc] using
        (weightListPerm_pair_exchange
          (before ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
            gap)
          tail suffix (shallow₂, b) (shallow₁, a))
    have hswappedPerm :
        swappedPairs.Perm
          (before ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            gap ++ [(shallow₁, c)] ++ tail ++
              [(shallow₂, d)] ++ suffix) := by
      simpa [swappedPairs, newPre, newSuffix, List.append_assoc] using
        (weightListPerm_pair_exchange
          (before ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            gap)
          tail suffix (shallow₂, d) (shallow₁, c))
    have hbranch :
        TwoSmallestDeepestExchangeBranch
          (leafDepthWeights depth tree) swappedPairs := by
      exact TwoSmallestDeepestExchangeBranch.nondegenerate
        before gap tail suffix rest hpairsPerm hswappedPerm
        htwoSmallest hab hrest hdepth₁ hdepth₂
    have hdepths :
        swappedPairs.map Prod.fst =
          (leafDepthWeights depth tree).map Prod.fst := by
      rw [hpairs']
      simp [swappedPairs, newPre, newSuffix, List.map_append]
    have hdisplay :
        swappedPairs =
          newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            newSuffix := by
      rfl
    have hpreLen : newPre.length = oldPre.length := by
      rw [hpre]
    have hsuffixLen : newSuffix.length = oldSuffix.length := by
      rw [hsuffix, hmiddleSplit]
      simp [newSuffix, List.length_append]
    obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
        hleavesPerm, _hrealizedEq⟩ :=
      hbridge (swappedPairs := swappedPairs) (newPre := newPre)
        (newSuffix := newSuffix) hbranch hdepths hdisplay hpreLen
        hsuffixLen
    exact ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
      hleavesPerm⟩
  · obtain ⟨gap, tail, hsuffixSplit, hpairs'⟩ := hsecondAfter
    let newPre := before
    let newSuffix :=
      middle ++ [(shallow₁, c)] ++ gap ++ [(shallow₂, d)] ++ tail
    let swappedPairs :=
      newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
        newSuffix
    have hpairsPerm :
        (leafDepthWeights depth tree).Perm
          (before ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
            middle ++ [(shallow₁, a)] ++ gap ++
              [(shallow₂, b)] ++ tail) := by
      rw [hpairs']
    have hbranch :
        TwoSmallestDeepestExchangeBranch
          (leafDepthWeights depth tree) swappedPairs := by
      exact TwoSmallestDeepestExchangeBranch.nondegenerate
        before middle gap tail rest hpairsPerm
        (by simp [swappedPairs, newPre, newSuffix, List.append_assoc])
        htwoSmallest hab hrest hdepth₁ hdepth₂
    have hdepths :
        swappedPairs.map Prod.fst =
          (leafDepthWeights depth tree).map Prod.fst := by
      rw [hpairs']
      simp [swappedPairs, newPre, newSuffix, List.map_append]
    have hdisplay :
        swappedPairs =
          newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            newSuffix := by
      rfl
    have hpreLen : newPre.length = oldPre.length := by
      rw [hpre]
    have hsuffixLen : newSuffix.length = oldSuffix.length := by
      rw [hsuffix, hsuffixSplit]
      simp [newSuffix, List.length_append]
    obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
        hleavesPerm, _hrealizedEq⟩ :=
      hbridge (swappedPairs := swappedPairs) (newPre := newPre)
        (newSuffix := newSuffix) hbranch hdepths hdisplay hpreLen
        hsuffixLen
    exact ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
      hleavesPerm⟩

  /-- Combined contraction-aware classifier for the orientation where the first
  selected two-smallest slot is before the old contracted sibling pair.  The
  second selected slot may be the left old sibling, the right old sibling, or a
  nonoverlapping occurrence elsewhere.  The returned contraction records either
  sibling orientation, matching the actual normalized tree branch. -/
  theorem
      exists_relabelLeaves_contract_for_first_before_contracted_pair_anywhere
      {tree contracted : InsertionScheduleTree} {depth : ℕ} {c d : ℝ}
      (hcontract : SiblingLeafContract tree contracted c d) :
      ∃ parentDepth : ℕ, ∃ oldPre oldSuffix : List (ℕ × ℝ),
        leafDepthWeights depth tree =
          oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
            oldSuffix ∧
          leafDepthWeights depth contracted =
            oldPre ++ [(parentDepth, c + d)] ++ oldSuffix ∧
            ∀ {before middle suffix rest : List (ℕ × ℝ)}
                {a b : ℝ} {shallow₁ shallow₂ : ℕ},
              oldPre = before ++ [(shallow₁, a)] ++ middle →
              oldSuffix = suffix →
              (leafDepthWeights depth tree).Perm
                ((shallow₁, a) :: (shallow₂, b) :: rest) →
              a ≤ b →
              (∀ pair ∈ rest, b ≤ pair.2) →
              shallow₁ ≤ parentDepth + 1 →
              shallow₂ ≤ parentDepth + 1 →
              ∃ swappedTree swappedContracted : InsertionScheduleTree,
                (SiblingLeafContract swappedTree swappedContracted a b ∨
                  SiblingLeafContract swappedTree swappedContracted b a) ∧
                  weightedLeafDepthCost depth swappedTree ≤
                    weightedLeafDepthCost depth tree ∧
                    swappedTree.leaves.Perm tree.leaves := by
    obtain ⟨parentDepth, oldPre, oldSuffix, htreeDepth,
      hcontractedDepth, hbridge⟩ :=
      exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_context_lengths
        hcontract
    refine ⟨parentDepth, oldPre, oldSuffix, htreeDepth, hcontractedDepth, ?_⟩
    intro before middle suffix rest a b shallow₁ shallow₂ hpre hsuffix
      htwoSmallest hab hrest hdepth₁ hdepth₂
    by_cases hleft : (shallow₂, b) = (parentDepth + 1, c)
    · cases hleft
      let newPre := before ++ [(shallow₁, d)] ++ middle
      let swappedPairs :=
        newPre ++ [(parentDepth + 1, c), (parentDepth + 1, a)] ++
          oldSuffix
      have hpairsPerm :
          (leafDepthWeights depth tree).Perm
            (before ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
              middle ++ [(shallow₁, a)] ++ oldSuffix) := by
        rw [htreeDepth, hpre]
        simpa [List.append_assoc] using
          (listPerm_selected_before_adjacent_to_after
            before middle oldSuffix (shallow₁, a)
            (parentDepth + 1, c) (parentDepth + 1, d))
      have hswappedPerm :
          swappedPairs.Perm
            (before ++ [(parentDepth + 1, c), (parentDepth + 1, a)] ++
              middle ++ [(shallow₁, d)] ++ oldSuffix) := by
        simpa [swappedPairs, newPre, List.append_assoc] using
          (listPerm_selected_before_adjacent_to_after
            before middle oldSuffix (shallow₁, d)
            (parentDepth + 1, c) (parentDepth + 1, a))
      have hbranch :
          TwoSmallestDeepestExchangeBranch
            (leafDepthWeights depth tree) swappedPairs := by
        exact TwoSmallestDeepestExchangeBranch.leftDeepestSecondSmallest
          before middle oldSuffix rest hpairsPerm hswappedPerm
          htwoSmallest hab hrest hdepth₁
      have hdepths :
          swappedPairs.map Prod.fst =
            (leafDepthWeights depth tree).map Prod.fst := by
        rw [htreeDepth, hpre]
        simp [swappedPairs, newPre, List.map_append]
      have hdisplay :
          swappedPairs =
            newPre ++ [(parentDepth + 1, c), (parentDepth + 1, a)] ++
              oldSuffix := by
        rfl
      have hpreLen : newPre.length = oldPre.length := by
        rw [hpre]
        simp [newPre, List.length_append]
      obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
          hleavesPerm, _hrealizedEq⟩ :=
        hbridge (swappedPairs := swappedPairs) (newPre := newPre)
          (newSuffix := oldSuffix) (a := c) (b := a)
          hbranch hdepths hdisplay hpreLen rfl
      exact ⟨swappedTree, swappedContracted, Or.inr hcontractedRelabel,
        hcost, hleavesPerm⟩
    · by_cases hright : (shallow₂, b) = (parentDepth + 1, d)
      · cases hright
        let newPre := before ++ [(shallow₁, c)] ++ middle
        let swappedPairs :=
          newPre ++ [(parentDepth + 1, a), (parentDepth + 1, d)] ++
            oldSuffix
        have hpairsPerm :
            (leafDepthWeights depth tree).Perm
              (before ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
                middle ++ [(shallow₁, a)] ++ oldSuffix) := by
          rw [htreeDepth, hpre]
          simpa [List.append_assoc] using
            (listPerm_selected_before_adjacent_to_after
              before middle oldSuffix (shallow₁, a)
              (parentDepth + 1, c) (parentDepth + 1, d))
        have hswappedPerm :
            swappedPairs.Perm
              (before ++ [(parentDepth + 1, a), (parentDepth + 1, d)] ++
                middle ++ [(shallow₁, c)] ++ oldSuffix) := by
          simpa [swappedPairs, newPre, List.append_assoc] using
            (listPerm_selected_before_adjacent_to_after
              before middle oldSuffix (shallow₁, c)
              (parentDepth + 1, a) (parentDepth + 1, d))
        have hbranch :
            TwoSmallestDeepestExchangeBranch
              (leafDepthWeights depth tree) swappedPairs := by
          exact TwoSmallestDeepestExchangeBranch.rightDeepestSecondSmallest
            before middle oldSuffix rest hpairsPerm hswappedPerm
            htwoSmallest hab hrest hdepth₁
        have hdepths :
            swappedPairs.map Prod.fst =
              (leafDepthWeights depth tree).map Prod.fst := by
          rw [htreeDepth, hpre]
          simp [swappedPairs, newPre, List.map_append]
        have hdisplay :
            swappedPairs =
              newPre ++ [(parentDepth + 1, a), (parentDepth + 1, d)] ++
                oldSuffix := by
          rfl
        have hpreLen : newPre.length = oldPre.length := by
          rw [hpre]
          simp [newPre, List.length_append]
        obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
            hleavesPerm, _hrealizedEq⟩ :=
          hbridge (swappedPairs := swappedPairs) (newPre := newPre)
            (newSuffix := oldSuffix) (a := a) (b := d)
            hbranch hdepths hdisplay hpreLen rfl
        exact ⟨swappedTree, swappedContracted, Or.inl hcontractedRelabel,
          hcost, hleavesPerm⟩
      · have hpairsDisplay :
            leafDepthWeights depth tree =
              before ++ [(shallow₁, a)] ++ middle ++
                [(parentDepth + 1, c), (parentDepth + 1, d)] ++ suffix := by
          rw [htreeDepth, hpre, hsuffix]
        obtain hloc :=
          exists_second_position_of_first_before_adjacent_pair
            (pairs := leafDepthWeights depth tree) (rest := rest)
            (first := (shallow₁, a)) (second := (shallow₂, b))
            (left := (parentDepth + 1, c))
            (right := (parentDepth + 1, d))
            before middle suffix hpairsDisplay htwoSmallest hleft hright
        rcases hloc with hsecondBefore | hsecondMiddle | hsecondAfter
        · obtain ⟨pre₂, gap, hbeforeSplit, hpairs'⟩ := hsecondBefore
          let newPre :=
            pre₂ ++ [(shallow₂, d)] ++ gap ++ [(shallow₁, c)] ++ middle
          let swappedPairs :=
            newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
              suffix
          have hpairsPerm :
              (leafDepthWeights depth tree).Perm
                (pre₂ ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
                  gap ++ [(shallow₁, a)] ++ middle ++
                    [(shallow₂, b)] ++ suffix) := by
            rw [hpairs']
            simpa [List.append_assoc] using
              (listPerm_two_selected_before_deepest_to_canonical
                pre₂ gap middle suffix
                (parentDepth + 1, c) (parentDepth + 1, d)
                (shallow₂, b) (shallow₁, a)).trans
                (weightListPerm_pair_exchange
                  (pre₂ ++ [(parentDepth + 1, c),
                    (parentDepth + 1, d)] ++ gap)
                  middle suffix (shallow₂, b) (shallow₁, a))
          have hswappedToReverseCanonical :
              swappedPairs.Perm
                (pre₂ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                  gap ++ [(shallow₂, d)] ++ middle ++
                    [(shallow₁, c)] ++ suffix) := by
            simpa [swappedPairs, newPre, List.append_assoc] using
              (listPerm_two_selected_before_deepest_to_canonical
                pre₂ gap middle suffix
                (parentDepth + 1, a) (parentDepth + 1, b)
                (shallow₂, d) (shallow₁, c))
          have hswappedPerm :
              swappedPairs.Perm
                (pre₂ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                  gap ++ [(shallow₁, c)] ++ middle ++
                    [(shallow₂, d)] ++ suffix) := by
            exact hswappedToReverseCanonical.trans
              (weightListPerm_pair_exchange
                (pre₂ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                  gap)
                middle suffix (shallow₂, d) (shallow₁, c))
          have hbranch :
              TwoSmallestDeepestExchangeBranch
                (leafDepthWeights depth tree) swappedPairs := by
            exact TwoSmallestDeepestExchangeBranch.nondegenerate
              pre₂ gap middle suffix rest hpairsPerm hswappedPerm
              htwoSmallest hab hrest hdepth₁ hdepth₂
          have hdepths :
              swappedPairs.map Prod.fst =
                (leafDepthWeights depth tree).map Prod.fst := by
            rw [hpairs']
            simp [swappedPairs, newPre, List.map_append]
          have hdisplay :
              swappedPairs =
                newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                  suffix := by
            rfl
          have hpreLen : newPre.length = oldPre.length := by
            rw [hpre, hbeforeSplit]
            simp [newPre, List.length_append]
          obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
              hleavesPerm, _hrealizedEq⟩ :=
            hbridge (swappedPairs := swappedPairs) (newPre := newPre)
              (newSuffix := suffix) hbranch hdepths hdisplay hpreLen (by
                rw [hsuffix])
          exact ⟨swappedTree, swappedContracted, Or.inl hcontractedRelabel,
            hcost, hleavesPerm⟩
        · obtain ⟨gap, tail, hmiddleSplit, hpairs'⟩ := hsecondMiddle
          let newPre :=
            before ++ [(shallow₁, c)] ++ gap ++ [(shallow₂, d)] ++ tail
          let swappedPairs :=
            newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
              suffix
          have hpairsPerm :
              (leafDepthWeights depth tree).Perm
                (before ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
                  gap ++ [(shallow₁, a)] ++ tail ++
                    [(shallow₂, b)] ++ suffix) := by
            rw [hpairs']
            exact listPerm_two_selected_before_deepest_to_canonical
              before gap tail suffix
              (parentDepth + 1, c) (parentDepth + 1, d)
              (shallow₁, a) (shallow₂, b)
          have hswappedPerm :
              swappedPairs.Perm
                (before ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                  gap ++ [(shallow₁, c)] ++ tail ++
                    [(shallow₂, d)] ++ suffix) := by
            simpa [swappedPairs, newPre, List.append_assoc] using
              (listPerm_two_selected_before_deepest_to_canonical
                before gap tail suffix
                (parentDepth + 1, a) (parentDepth + 1, b)
                (shallow₁, c) (shallow₂, d))
          have hbranch :
              TwoSmallestDeepestExchangeBranch
                (leafDepthWeights depth tree) swappedPairs := by
            exact TwoSmallestDeepestExchangeBranch.nondegenerate
              before gap tail suffix rest hpairsPerm hswappedPerm
              htwoSmallest hab hrest hdepth₁ hdepth₂
          have hdepths :
              swappedPairs.map Prod.fst =
                (leafDepthWeights depth tree).map Prod.fst := by
            rw [hpairs']
            simp [swappedPairs, newPre, List.map_append]
          have hdisplay :
              swappedPairs =
                newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                  suffix := by
            rfl
          have hpreLen : newPre.length = oldPre.length := by
            rw [hpre]
            rw [hmiddleSplit]
            simp [newPre, List.length_append]
          obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
              hleavesPerm, _hrealizedEq⟩ :=
            hbridge (swappedPairs := swappedPairs) (newPre := newPre)
              (newSuffix := suffix) hbranch hdepths hdisplay hpreLen (by
                rw [hsuffix])
          exact ⟨swappedTree, swappedContracted, Or.inl hcontractedRelabel,
            hcost, hleavesPerm⟩
        · obtain ⟨gap, tail, hsuffixSplit, hpairs'⟩ := hsecondAfter
          let newPre := before ++ [(shallow₁, c)] ++ middle
          let newSuffix := gap ++ [(shallow₂, d)] ++ tail
          let swappedPairs :=
            newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
              newSuffix
          have hpairsPerm :
              (leafDepthWeights depth tree).Perm
                (before ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
                  middle ++ [(shallow₁, a)] ++ gap ++
                    [(shallow₂, b)] ++ tail) := by
            rw [hpairs']
            exact listPerm_selected_before_deepest_before_selected_to_canonical
              before middle gap tail
              (parentDepth + 1, c) (parentDepth + 1, d)
              (shallow₁, a) (shallow₂, b)
          have hswappedPerm :
              swappedPairs.Perm
                (before ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                  middle ++ [(shallow₁, c)] ++ gap ++
                    [(shallow₂, d)] ++ tail) := by
            simpa [swappedPairs, newPre, newSuffix, List.append_assoc] using
              (listPerm_selected_before_deepest_before_selected_to_canonical
                before middle gap tail
                (parentDepth + 1, a) (parentDepth + 1, b)
                (shallow₁, c) (shallow₂, d))
          have hbranch :
              TwoSmallestDeepestExchangeBranch
                (leafDepthWeights depth tree) swappedPairs := by
            exact TwoSmallestDeepestExchangeBranch.nondegenerate
              before middle gap tail rest hpairsPerm hswappedPerm
              htwoSmallest hab hrest hdepth₁ hdepth₂
          have hdepths :
              swappedPairs.map Prod.fst =
                (leafDepthWeights depth tree).map Prod.fst := by
            rw [hpairs']
            simp [swappedPairs, newPre, newSuffix, List.map_append]
          have hdisplay :
              swappedPairs =
                newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                  newSuffix := by
            rfl
          have hpreLen : newPre.length = oldPre.length := by
            rw [hpre]
            simp [newPre, List.length_append]
          have hsuffixLen : newSuffix.length = oldSuffix.length := by
            rw [hsuffix, hsuffixSplit]
            simp [newSuffix, List.length_append]
          obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
              hleavesPerm, _hrealizedEq⟩ :=
            hbridge (swappedPairs := swappedPairs) (newPre := newPre)
              (newSuffix := newSuffix) hbranch hdepths hdisplay hpreLen
              hsuffixLen
          exact ⟨swappedTree, swappedContracted, Or.inl hcontractedRelabel,
            hcost, hleavesPerm⟩

/-- Combined contraction-aware classifier for the orientation where the first
selected two-smallest slot is after the old contracted sibling pair.  The
second selected slot may be the left old sibling, the right old sibling, or a
nonoverlapping occurrence elsewhere.  The returned contraction records either
sibling orientation, matching the actual normalized tree branch. -/
theorem
    exists_relabelLeaves_contract_for_first_after_contracted_pair_anywhere
    {tree contracted : InsertionScheduleTree} {depth : ℕ} {c d : ℝ}
    (hcontract : SiblingLeafContract tree contracted c d) :
    ∃ parentDepth : ℕ, ∃ oldPre oldSuffix : List (ℕ × ℝ),
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          oldSuffix ∧
        leafDepthWeights depth contracted =
          oldPre ++ [(parentDepth, c + d)] ++ oldSuffix ∧
          ∀ {before middle suffix rest : List (ℕ × ℝ)}
              {a b : ℝ} {shallow₁ shallow₂ : ℕ},
            oldPre = before →
            oldSuffix = middle ++ [(shallow₁, a)] ++ suffix →
            (leafDepthWeights depth tree).Perm
              ((shallow₁, a) :: (shallow₂, b) :: rest) →
            a ≤ b →
            (∀ pair ∈ rest, b ≤ pair.2) →
            shallow₁ ≤ parentDepth + 1 →
            shallow₂ ≤ parentDepth + 1 →
            ∃ swappedTree swappedContracted : InsertionScheduleTree,
              (SiblingLeafContract swappedTree swappedContracted a b ∨
                SiblingLeafContract swappedTree swappedContracted b a) ∧
                weightedLeafDepthCost depth swappedTree ≤
                  weightedLeafDepthCost depth tree ∧
                  swappedTree.leaves.Perm tree.leaves := by
  obtain ⟨parentDepth, oldPre, oldSuffix, htreeDepth,
    hcontractedDepth, hbridge⟩ :=
    exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_context_lengths
      hcontract
  refine ⟨parentDepth, oldPre, oldSuffix, htreeDepth, hcontractedDepth, ?_⟩
  intro before middle suffix rest a b shallow₁ shallow₂ hpre hsuffix
    htwoSmallest hab hrest hdepth₁ hdepth₂
  by_cases hleft : (shallow₂, b) = (parentDepth + 1, c)
  · cases hleft
    let newPre := before
    let newSuffix := middle ++ [(shallow₁, d)] ++ suffix
    let swappedPairs :=
      newPre ++ [(parentDepth + 1, c), (parentDepth + 1, a)] ++
        newSuffix
    have hpairsPerm :
        (leafDepthWeights depth tree).Perm
          (before ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
            middle ++ [(shallow₁, a)] ++ suffix) := by
      rw [htreeDepth, hpre, hsuffix]
      simp [List.append_assoc]
    have hbranch :
        TwoSmallestDeepestExchangeBranch
          (leafDepthWeights depth tree) swappedPairs := by
      exact TwoSmallestDeepestExchangeBranch.leftDeepestSecondSmallest
        before middle suffix rest hpairsPerm
        (by simp [swappedPairs, newPre, newSuffix, List.append_assoc])
        htwoSmallest hab hrest hdepth₁
    have hdepths :
        swappedPairs.map Prod.fst =
          (leafDepthWeights depth tree).map Prod.fst := by
      rw [htreeDepth, hpre, hsuffix]
      simp [swappedPairs, newPre, newSuffix, List.map_append]
    have hdisplay :
        swappedPairs =
          newPre ++ [(parentDepth + 1, c), (parentDepth + 1, a)] ++
            newSuffix := by
      rfl
    have hpreLen : newPre.length = oldPre.length := by
      rw [hpre]
    have hsuffixLen : newSuffix.length = oldSuffix.length := by
      rw [hsuffix]
      simp [newSuffix, List.length_append]
    obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
        hleavesPerm, _hrealizedEq⟩ :=
      hbridge (swappedPairs := swappedPairs) (newPre := newPre)
        (newSuffix := newSuffix) (a := c) (b := a)
        hbranch hdepths hdisplay hpreLen hsuffixLen
    exact ⟨swappedTree, swappedContracted, Or.inr hcontractedRelabel,
      hcost, hleavesPerm⟩
  · by_cases hright : (shallow₂, b) = (parentDepth + 1, d)
    · cases hright
      let newPre := before
      let newSuffix := middle ++ [(shallow₁, c)] ++ suffix
      let swappedPairs :=
        newPre ++ [(parentDepth + 1, a), (parentDepth + 1, d)] ++
          newSuffix
      have hpairsPerm :
          (leafDepthWeights depth tree).Perm
            (before ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
              middle ++ [(shallow₁, a)] ++ suffix) := by
        rw [htreeDepth, hpre, hsuffix]
        simp [List.append_assoc]
      have hbranch :
          TwoSmallestDeepestExchangeBranch
            (leafDepthWeights depth tree) swappedPairs := by
        exact TwoSmallestDeepestExchangeBranch.rightDeepestSecondSmallest
          before middle suffix rest hpairsPerm
          (by simp [swappedPairs, newPre, newSuffix, List.append_assoc])
          htwoSmallest hab hrest hdepth₁
      have hdepths :
          swappedPairs.map Prod.fst =
            (leafDepthWeights depth tree).map Prod.fst := by
        rw [htreeDepth, hpre, hsuffix]
        simp [swappedPairs, newPre, newSuffix, List.map_append]
      have hdisplay :
          swappedPairs =
            newPre ++ [(parentDepth + 1, a), (parentDepth + 1, d)] ++
              newSuffix := by
        rfl
      have hpreLen : newPre.length = oldPre.length := by
        rw [hpre]
      have hsuffixLen : newSuffix.length = oldSuffix.length := by
        rw [hsuffix]
        simp [newSuffix, List.length_append]
      obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
          hleavesPerm, _hrealizedEq⟩ :=
        hbridge (swappedPairs := swappedPairs) (newPre := newPre)
          (newSuffix := newSuffix) (a := a) (b := d)
          hbranch hdepths hdisplay hpreLen hsuffixLen
      exact ⟨swappedTree, swappedContracted, Or.inl hcontractedRelabel,
        hcost, hleavesPerm⟩
    · have hpairsDisplay :
          leafDepthWeights depth tree =
            before ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
              middle ++ [(shallow₁, a)] ++ suffix := by
        rw [htreeDepth, hpre, hsuffix]
        simp [List.append_assoc]
      obtain hloc :=
        exists_second_position_of_first_after_adjacent_pair
          (pairs := leafDepthWeights depth tree) (rest := rest)
          (first := (shallow₁, a)) (second := (shallow₂, b))
          (left := (parentDepth + 1, c))
          (right := (parentDepth + 1, d))
          before middle suffix hpairsDisplay htwoSmallest hleft hright
      rcases hloc with hsecondBefore | hsecondMiddle | hsecondAfter
      · obtain ⟨pre₂, gap, hbeforeSplit, hpairs'⟩ := hsecondBefore
        let newPre := pre₂ ++ [(shallow₂, d)] ++ gap
        let newSuffix := middle ++ [(shallow₁, c)] ++ suffix
        let swappedPairs :=
          newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            newSuffix
        have hpairsToReverseCanonical :
            (leafDepthWeights depth tree).Perm
              (pre₂ ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
                gap ++ [(shallow₂, b)] ++ middle ++
                  [(shallow₁, a)] ++ suffix) := by
          rw [hpairs']
          simpa [List.append_assoc] using
            (listPerm_selected_before_deepest_before_selected_to_canonical
              pre₂ gap middle suffix
              (parentDepth + 1, c) (parentDepth + 1, d)
              (shallow₂, b) (shallow₁, a))
        have hpairsPerm :
            (leafDepthWeights depth tree).Perm
              (pre₂ ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
                gap ++ [(shallow₁, a)] ++ middle ++
                  [(shallow₂, b)] ++ suffix) := by
          exact hpairsToReverseCanonical.trans
            (weightListPerm_pair_exchange
              (pre₂ ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
                gap)
              middle suffix (shallow₂, b) (shallow₁, a))
        have hswappedToReverseCanonical :
            swappedPairs.Perm
              (pre₂ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                gap ++ [(shallow₂, d)] ++ middle ++
                  [(shallow₁, c)] ++ suffix) := by
          simpa [swappedPairs, newPre, newSuffix, List.append_assoc] using
            (listPerm_selected_before_deepest_before_selected_to_canonical
              pre₂ gap middle suffix
              (parentDepth + 1, a) (parentDepth + 1, b)
              (shallow₂, d) (shallow₁, c))
        have hswappedPerm :
            swappedPairs.Perm
              (pre₂ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                gap ++ [(shallow₁, c)] ++ middle ++
                  [(shallow₂, d)] ++ suffix) := by
          exact hswappedToReverseCanonical.trans
            (weightListPerm_pair_exchange
              (pre₂ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                gap)
              middle suffix (shallow₂, d) (shallow₁, c))
        have hbranch :
            TwoSmallestDeepestExchangeBranch
              (leafDepthWeights depth tree) swappedPairs := by
          exact TwoSmallestDeepestExchangeBranch.nondegenerate
            pre₂ gap middle suffix rest hpairsPerm hswappedPerm
            htwoSmallest hab hrest hdepth₁ hdepth₂
        have hdepths :
            swappedPairs.map Prod.fst =
              (leafDepthWeights depth tree).map Prod.fst := by
          rw [hpairs']
          simp [swappedPairs, newPre, newSuffix, List.map_append]
        have hdisplay :
            swappedPairs =
              newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                newSuffix := by
          rfl
        have hpreLen : newPre.length = oldPre.length := by
          rw [hpre, hbeforeSplit]
          simp [newPre, List.length_append]
        have hsuffixLen : newSuffix.length = oldSuffix.length := by
          rw [hsuffix]
          simp [newSuffix, List.length_append]
        obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
            hleavesPerm, _hrealizedEq⟩ :=
          hbridge (swappedPairs := swappedPairs) (newPre := newPre)
            (newSuffix := newSuffix) hbranch hdepths hdisplay hpreLen
            hsuffixLen
        exact ⟨swappedTree, swappedContracted, Or.inl hcontractedRelabel,
          hcost, hleavesPerm⟩
      · obtain ⟨gap, tail, hmiddleSplit, hpairs'⟩ := hsecondMiddle
        let newPre := before
        let newSuffix :=
          gap ++ [(shallow₂, d)] ++ tail ++ [(shallow₁, c)] ++ suffix
        let swappedPairs :=
          newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            newSuffix
        have hpairsPerm :
            (leafDepthWeights depth tree).Perm
              (before ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
                gap ++ [(shallow₁, a)] ++ tail ++
                  [(shallow₂, b)] ++ suffix) := by
          rw [hpairs']
          simpa [List.append_assoc] using
            (weightListPerm_pair_exchange
              (before ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
                gap)
              tail suffix (shallow₂, b) (shallow₁, a))
        have hswappedPerm :
            swappedPairs.Perm
              (before ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                gap ++ [(shallow₁, c)] ++ tail ++
                  [(shallow₂, d)] ++ suffix) := by
          simpa [swappedPairs, newPre, newSuffix, List.append_assoc] using
            (weightListPerm_pair_exchange
              (before ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                gap)
              tail suffix (shallow₂, d) (shallow₁, c))
        have hbranch :
            TwoSmallestDeepestExchangeBranch
              (leafDepthWeights depth tree) swappedPairs := by
          exact TwoSmallestDeepestExchangeBranch.nondegenerate
            before gap tail suffix rest hpairsPerm hswappedPerm
            htwoSmallest hab hrest hdepth₁ hdepth₂
        have hdepths :
            swappedPairs.map Prod.fst =
              (leafDepthWeights depth tree).map Prod.fst := by
          rw [hpairs']
          simp [swappedPairs, newPre, newSuffix, List.map_append]
        have hdisplay :
            swappedPairs =
              newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                newSuffix := by
          rfl
        have hpreLen : newPre.length = oldPre.length := by
          rw [hpre]
        have hsuffixLen : newSuffix.length = oldSuffix.length := by
          rw [hsuffix, hmiddleSplit]
          simp [newSuffix, List.length_append]
        obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
            hleavesPerm, _hrealizedEq⟩ :=
          hbridge (swappedPairs := swappedPairs) (newPre := newPre)
            (newSuffix := newSuffix) hbranch hdepths hdisplay hpreLen
            hsuffixLen
        exact ⟨swappedTree, swappedContracted, Or.inl hcontractedRelabel,
          hcost, hleavesPerm⟩
      · obtain ⟨gap, tail, hsuffixSplit, hpairs'⟩ := hsecondAfter
        let newPre := before
        let newSuffix :=
          middle ++ [(shallow₁, c)] ++ gap ++ [(shallow₂, d)] ++ tail
        let swappedPairs :=
          newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            newSuffix
        have hpairsPerm :
            (leafDepthWeights depth tree).Perm
              (before ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
                middle ++ [(shallow₁, a)] ++ gap ++
                  [(shallow₂, b)] ++ tail) := by
          rw [hpairs']
        have hbranch :
            TwoSmallestDeepestExchangeBranch
              (leafDepthWeights depth tree) swappedPairs := by
          exact TwoSmallestDeepestExchangeBranch.nondegenerate
            before middle gap tail rest hpairsPerm
            (by simp [swappedPairs, newPre, newSuffix, List.append_assoc])
            htwoSmallest hab hrest hdepth₁ hdepth₂
        have hdepths :
            swappedPairs.map Prod.fst =
              (leafDepthWeights depth tree).map Prod.fst := by
          rw [hpairs']
          simp [swappedPairs, newPre, newSuffix, List.map_append]
        have hdisplay :
            swappedPairs =
              newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                newSuffix := by
          rfl
        have hpreLen : newPre.length = oldPre.length := by
          rw [hpre]
        have hsuffixLen : newSuffix.length = oldSuffix.length := by
          rw [hsuffix, hsuffixSplit]
          simp [newSuffix, List.length_append]
        obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
            hleavesPerm, _hrealizedEq⟩ :=
          hbridge (swappedPairs := swappedPairs) (newPre := newPre)
            (newSuffix := newSuffix) hbranch hdepths hdisplay hpreLen
            hsuffixLen
        exact ⟨swappedTree, swappedContracted, Or.inl hcontractedRelabel,
          hcost, hleavesPerm⟩

/-- Combined contraction-aware classifier for the orientation where the first
selected two-smallest entry is already the left member of the old contracted
sibling pair.  The second selected entry may be before the pair, the right old
sibling, or after the pair. -/
theorem
    exists_relabelLeaves_contract_for_left_deepest_first_two_smallest_anywhere
    {tree contracted : InsertionScheduleTree} {depth : ℕ} {a c : ℝ}
    (hcontract : SiblingLeafContract tree contracted a c) :
    ∃ parentDepth : ℕ, ∃ oldPre oldSuffix : List (ℕ × ℝ),
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, a), (parentDepth + 1, c)] ++
          oldSuffix ∧
        leafDepthWeights depth contracted =
          oldPre ++ [(parentDepth, a + c)] ++ oldSuffix ∧
          ∀ {rest : List (ℕ × ℝ)} {b : ℝ} {shallow : ℕ},
            (leafDepthWeights depth tree).Perm
              ((parentDepth + 1, a) :: (shallow, b) :: rest) →
            (∀ pair ∈ rest, b ≤ pair.2) →
            shallow ≤ parentDepth + 1 →
            ∃ swappedTree swappedContracted : InsertionScheduleTree,
              (SiblingLeafContract swappedTree swappedContracted a b ∨
                SiblingLeafContract swappedTree swappedContracted b a) ∧
                weightedLeafDepthCost depth swappedTree ≤
                  weightedLeafDepthCost depth tree ∧
                  swappedTree.leaves.Perm tree.leaves := by
  obtain ⟨parentDepth, oldPre, oldSuffix, htreeDepth,
    hcontractedDepth, hbridge⟩ :=
    exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_context_lengths
      hcontract
  refine ⟨parentDepth, oldPre, oldSuffix, htreeDepth, hcontractedDepth, ?_⟩
  intro rest b shallow htwoSmallest hrest hdepth
  have hpairsFront :
      (leafDepthWeights depth tree).Perm
        ((parentDepth + 1, a) :: oldPre ++ [(parentDepth + 1, c)] ++
          oldSuffix) := by
    rw [htreeDepth]
    simp only [List.append_assoc, List.cons_append]
    exact List.perm_middle (a := (parentDepth + 1, a)) (l₁ := oldPre)
      (l₂ := (parentDepth + 1, c) :: oldSuffix)
  have htailPerm :
      (oldPre ++ [(parentDepth + 1, c)] ++ oldSuffix).Perm
        ((shallow, b) :: rest) :=
    List.Perm.cons_inv (hpairsFront.symm.trans htwoSmallest)
  have hsecond_mem :
      (shallow, b) ∈ oldPre ++ [(parentDepth + 1, c)] ++ oldSuffix :=
    (htailPerm.mem_iff).2 (by simp)
  simp [List.mem_append] at hsecond_mem
  rcases hsecond_mem with hpre | hright | hsuffix
  · obtain ⟨before, middle, hsplit⟩ :=
      exists_split_of_mem oldPre hpre
    let newPre := before ++ [(shallow, c)] ++ middle
    let swappedPairs :=
      newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
        oldSuffix
    have hpairsPerm :
        (leafDepthWeights depth tree).Perm
          (before ++ [(parentDepth + 1, a), (parentDepth + 1, c)] ++
            middle ++ [(shallow, b)] ++ oldSuffix) := by
      rw [htreeDepth, hsplit]
      simpa [List.append_assoc] using
        (listPerm_selected_before_adjacent_to_after
          before middle oldSuffix (shallow, b)
          (parentDepth + 1, a) (parentDepth + 1, c))
    have hswappedPerm :
        swappedPairs.Perm
          (before ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            middle ++ [(shallow, c)] ++ oldSuffix) := by
      simpa [swappedPairs, newPre, List.append_assoc] using
        (listPerm_selected_before_adjacent_to_after
          before middle oldSuffix (shallow, c)
          (parentDepth + 1, a) (parentDepth + 1, b))
    have hbranch :
        TwoSmallestDeepestExchangeBranch
          (leafDepthWeights depth tree) swappedPairs := by
      exact TwoSmallestDeepestExchangeBranch.leftDeepestFirstSmallest
        before middle oldSuffix rest hpairsPerm hswappedPerm
        htwoSmallest hrest hdepth
    have hdepths :
        swappedPairs.map Prod.fst =
          (leafDepthWeights depth tree).map Prod.fst := by
      rw [htreeDepth, hsplit]
      simp [swappedPairs, newPre, List.map_append]
    have hdisplay :
        swappedPairs =
          newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            oldSuffix := by
      rfl
    have hpreLen : newPre.length = oldPre.length := by
      rw [hsplit]
      simp [newPre, List.length_append]
    obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
        hleavesPerm, _hrealizedEq⟩ :=
      hbridge (swappedPairs := swappedPairs) (newPre := newPre)
        (newSuffix := oldSuffix) hbranch hdepths hdisplay hpreLen rfl
    exact ⟨swappedTree, swappedContracted, Or.inl hcontractedRelabel,
      hcost, hleavesPerm⟩
  · have hb_eq_c : b = c := hright.2
    subst b
    exact ⟨tree, contracted, Or.inl hcontract, le_rfl,
      List.Perm.refl tree.leaves⟩
  · obtain ⟨middle, suffix, hsplit⟩ :=
      exists_split_of_mem oldSuffix hsuffix
    let newSuffix := middle ++ [(shallow, c)] ++ suffix
    let swappedPairs :=
      oldPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
        newSuffix
    have hpairsPerm :
        (leafDepthWeights depth tree).Perm
          (oldPre ++ [(parentDepth + 1, a), (parentDepth + 1, c)] ++
            middle ++ [(shallow, b)] ++ suffix) := by
      rw [htreeDepth, hsplit]
      simp [List.append_assoc]
    have hbranch :
        TwoSmallestDeepestExchangeBranch
          (leafDepthWeights depth tree) swappedPairs := by
      exact TwoSmallestDeepestExchangeBranch.leftDeepestFirstSmallest
        oldPre middle suffix rest hpairsPerm
        (by simp [swappedPairs, newSuffix, List.append_assoc])
        htwoSmallest hrest hdepth
    have hdepths :
        swappedPairs.map Prod.fst =
          (leafDepthWeights depth tree).map Prod.fst := by
      rw [htreeDepth, hsplit]
      simp [swappedPairs, newSuffix, List.map_append]
    have hdisplay :
        swappedPairs =
          oldPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            newSuffix := by
      rfl
    have hsuffixLen : newSuffix.length = oldSuffix.length := by
      rw [hsplit]
      simp [newSuffix, List.length_append]
    obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
        hleavesPerm, _hrealizedEq⟩ :=
      hbridge (swappedPairs := swappedPairs) (newPre := oldPre)
        (newSuffix := newSuffix) hbranch hdepths hdisplay rfl hsuffixLen
    exact ⟨swappedTree, swappedContracted, Or.inl hcontractedRelabel,
      hcost, hleavesPerm⟩

/-- Combined contraction-aware classifier for the orientation where the first
selected two-smallest entry is already the right member of the old contracted
sibling pair.  The second selected entry may be before the pair, the left old
sibling, or after the pair. -/
theorem
    exists_relabelLeaves_contract_for_right_deepest_first_two_smallest_anywhere
    {tree contracted : InsertionScheduleTree} {depth : ℕ} {a c : ℝ}
    (hcontract : SiblingLeafContract tree contracted c a) :
    ∃ parentDepth : ℕ, ∃ oldPre oldSuffix : List (ℕ × ℝ),
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, a)] ++
          oldSuffix ∧
        leafDepthWeights depth contracted =
          oldPre ++ [(parentDepth, c + a)] ++ oldSuffix ∧
          ∀ {rest : List (ℕ × ℝ)} {b : ℝ} {shallow : ℕ},
            (leafDepthWeights depth tree).Perm
              ((parentDepth + 1, a) :: (shallow, b) :: rest) →
            (∀ pair ∈ rest, b ≤ pair.2) →
            shallow ≤ parentDepth + 1 →
            ∃ swappedTree swappedContracted : InsertionScheduleTree,
              (SiblingLeafContract swappedTree swappedContracted a b ∨
                SiblingLeafContract swappedTree swappedContracted b a) ∧
                weightedLeafDepthCost depth swappedTree ≤
                  weightedLeafDepthCost depth tree ∧
                  swappedTree.leaves.Perm tree.leaves := by
  obtain ⟨parentDepth, oldPre, oldSuffix, htreeDepth,
    hcontractedDepth, hbridge⟩ :=
    exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_context_lengths
      hcontract
  refine ⟨parentDepth, oldPre, oldSuffix, htreeDepth, hcontractedDepth, ?_⟩
  intro rest b shallow htwoSmallest hrest hdepth
  have hpairsFront :
      (leafDepthWeights depth tree).Perm
        ((parentDepth + 1, a) :: oldPre ++ [(parentDepth + 1, c)] ++
          oldSuffix) := by
    rw [htreeDepth]
    simpa [List.append_assoc] using
      (List.perm_middle (a := (parentDepth + 1, a))
        (l₁ := oldPre ++ [(parentDepth + 1, c)]) (l₂ := oldSuffix))
  have htailPerm :
      (oldPre ++ [(parentDepth + 1, c)] ++ oldSuffix).Perm
        ((shallow, b) :: rest) :=
    List.Perm.cons_inv (hpairsFront.symm.trans htwoSmallest)
  have hsecond_mem :
      (shallow, b) ∈ oldPre ++ [(parentDepth + 1, c)] ++ oldSuffix :=
    (htailPerm.mem_iff).2 (by simp)
  simp [List.mem_append] at hsecond_mem
  rcases hsecond_mem with hpre | hleft | hsuffix
  · obtain ⟨before, middle, hsplit⟩ :=
      exists_split_of_mem oldPre hpre
    let newPre := before ++ [(shallow, c)] ++ middle
    let swappedPairs :=
      newPre ++ [(parentDepth + 1, b), (parentDepth + 1, a)] ++
        oldSuffix
    have hpairsPerm :
        (leafDepthWeights depth tree).Perm
          (before ++ [(parentDepth + 1, c), (parentDepth + 1, a)] ++
            middle ++ [(shallow, b)] ++ oldSuffix) := by
      rw [htreeDepth, hsplit]
      simpa [List.append_assoc] using
        (listPerm_selected_before_adjacent_to_after
          before middle oldSuffix (shallow, b)
          (parentDepth + 1, c) (parentDepth + 1, a))
    have hswappedPerm :
        swappedPairs.Perm
          (before ++ [(parentDepth + 1, b), (parentDepth + 1, a)] ++
            middle ++ [(shallow, c)] ++ oldSuffix) := by
      simpa [swappedPairs, newPre, List.append_assoc] using
        (listPerm_selected_before_adjacent_to_after
          before middle oldSuffix (shallow, c)
          (parentDepth + 1, b) (parentDepth + 1, a))
    have hbranch :
        TwoSmallestDeepestExchangeBranch
          (leafDepthWeights depth tree) swappedPairs := by
      exact TwoSmallestDeepestExchangeBranch.rightDeepestFirstSmallest
        before middle oldSuffix rest hpairsPerm hswappedPerm
        htwoSmallest hrest hdepth
    have hdepths :
        swappedPairs.map Prod.fst =
          (leafDepthWeights depth tree).map Prod.fst := by
      rw [htreeDepth, hsplit]
      simp [swappedPairs, newPre, List.map_append]
    have hdisplay :
        swappedPairs =
          newPre ++ [(parentDepth + 1, b), (parentDepth + 1, a)] ++
            oldSuffix := by
      rfl
    have hpreLen : newPre.length = oldPre.length := by
      rw [hsplit]
      simp [newPre, List.length_append]
    obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
        hleavesPerm, _hrealizedEq⟩ :=
      hbridge (swappedPairs := swappedPairs) (newPre := newPre)
        (newSuffix := oldSuffix) (a := b) (b := a)
        hbranch hdepths hdisplay hpreLen rfl
    exact ⟨swappedTree, swappedContracted, Or.inr hcontractedRelabel,
      hcost, hleavesPerm⟩
  · have hb_eq_c : b = c := hleft.2
    subst b
    exact ⟨tree, contracted, Or.inr hcontract, le_rfl,
      List.Perm.refl tree.leaves⟩
  · obtain ⟨middle, suffix, hsplit⟩ :=
      exists_split_of_mem oldSuffix hsuffix
    let newSuffix := middle ++ [(shallow, c)] ++ suffix
    let swappedPairs :=
      oldPre ++ [(parentDepth + 1, b), (parentDepth + 1, a)] ++
        newSuffix
    have hpairsPerm :
        (leafDepthWeights depth tree).Perm
          (oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, a)] ++
            middle ++ [(shallow, b)] ++ suffix) := by
      rw [htreeDepth, hsplit]
      simp [List.append_assoc]
    have hbranch :
        TwoSmallestDeepestExchangeBranch
          (leafDepthWeights depth tree) swappedPairs := by
      exact TwoSmallestDeepestExchangeBranch.rightDeepestFirstSmallest
        oldPre middle suffix rest hpairsPerm
        (by simp [swappedPairs, newSuffix, List.append_assoc])
        htwoSmallest hrest hdepth
    have hdepths :
        swappedPairs.map Prod.fst =
          (leafDepthWeights depth tree).map Prod.fst := by
      rw [htreeDepth, hsplit]
      simp [swappedPairs, newSuffix, List.map_append]
    have hdisplay :
        swappedPairs =
          oldPre ++ [(parentDepth + 1, b), (parentDepth + 1, a)] ++
            newSuffix := by
      rfl
    have hsuffixLen : newSuffix.length = oldSuffix.length := by
      rw [hsplit]
      simp [newSuffix, List.length_append]
    obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
        hleavesPerm, _hrealizedEq⟩ :=
      hbridge (swappedPairs := swappedPairs) (newPre := oldPre)
        (newSuffix := newSuffix) (a := b) (b := a)
        hbranch hdepths hdisplay rfl hsuffixLen
    exact ⟨swappedTree, swappedContracted, Or.inr hcontractedRelabel,
      hcost, hleavesPerm⟩

/-- Fixed-context contraction-aware classifier for the orientation where the
first selected two-smallest entry is already the left member of the displayed
old contracted sibling pair.  This is the shared-context continuation used by
the arbitrary occurrence dispatcher. -/
theorem
    exists_relabelLeaves_contract_for_left_deepest_first_two_smallest_anywhere_of_context
    {tree contracted : InsertionScheduleTree} {depth parentDepth : ℕ}
    {oldPre oldSuffix : List (ℕ × ℝ)} {a c : ℝ}
    (hcontract : SiblingLeafContract tree contracted a c)
    (htreeDepth :
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, a), (parentDepth + 1, c)] ++
          oldSuffix)
    (hbridge :
      ∀ {swappedPairs newPre newSuffix : List (ℕ × ℝ)} {x y : ℝ},
        TwoSmallestDeepestExchangeBranch
          (leafDepthWeights depth tree) swappedPairs →
        swappedPairs.map Prod.fst =
          (leafDepthWeights depth tree).map Prod.fst →
        swappedPairs =
          newPre ++ [(parentDepth + 1, x), (parentDepth + 1, y)] ++
            newSuffix →
        newPre.length = oldPre.length →
        newSuffix.length = oldSuffix.length →
        ∃ swappedTree swappedContracted : InsertionScheduleTree,
          SiblingLeafContract swappedTree swappedContracted x y ∧
            weightedLeafDepthCost depth swappedTree ≤
              weightedLeafDepthCost depth tree ∧
              swappedTree.leaves.Perm tree.leaves ∧
                leafDepthWeights depth swappedTree = swappedPairs) :
    ∀ {rest : List (ℕ × ℝ)} {b : ℝ} {shallow : ℕ},
      (leafDepthWeights depth tree).Perm
        ((parentDepth + 1, a) :: (shallow, b) :: rest) →
      (∀ pair ∈ rest, b ≤ pair.2) →
      shallow ≤ parentDepth + 1 →
      ∃ swappedTree swappedContracted : InsertionScheduleTree,
        (SiblingLeafContract swappedTree swappedContracted a b ∨
          SiblingLeafContract swappedTree swappedContracted b a) ∧
          weightedLeafDepthCost depth swappedTree ≤
            weightedLeafDepthCost depth tree ∧
            swappedTree.leaves.Perm tree.leaves := by
  intro rest b shallow htwoSmallest hrest hdepth
  have hpairsFront :
      (leafDepthWeights depth tree).Perm
        ((parentDepth + 1, a) :: oldPre ++ [(parentDepth + 1, c)] ++
          oldSuffix) := by
    rw [htreeDepth]
    simp only [List.append_assoc, List.cons_append]
    exact List.perm_middle (a := (parentDepth + 1, a)) (l₁ := oldPre)
      (l₂ := (parentDepth + 1, c) :: oldSuffix)
  have htailPerm :
      (oldPre ++ [(parentDepth + 1, c)] ++ oldSuffix).Perm
        ((shallow, b) :: rest) :=
    List.Perm.cons_inv (hpairsFront.symm.trans htwoSmallest)
  have hsecond_mem :
      (shallow, b) ∈ oldPre ++ [(parentDepth + 1, c)] ++ oldSuffix :=
    (htailPerm.mem_iff).2 (by simp)
  simp [List.mem_append] at hsecond_mem
  rcases hsecond_mem with hpre | hright | hsuffix
  · obtain ⟨before, middle, hsplit⟩ :=
      exists_split_of_mem oldPre hpre
    let newPre := before ++ [(shallow, c)] ++ middle
    let swappedPairs :=
      newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
        oldSuffix
    have hpairsPerm :
        (leafDepthWeights depth tree).Perm
          (before ++ [(parentDepth + 1, a), (parentDepth + 1, c)] ++
            middle ++ [(shallow, b)] ++ oldSuffix) := by
      rw [htreeDepth, hsplit]
      simpa [List.append_assoc] using
        (listPerm_selected_before_adjacent_to_after
          before middle oldSuffix (shallow, b)
          (parentDepth + 1, a) (parentDepth + 1, c))
    have hswappedPerm :
        swappedPairs.Perm
          (before ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            middle ++ [(shallow, c)] ++ oldSuffix) := by
      simpa [swappedPairs, newPre, List.append_assoc] using
        (listPerm_selected_before_adjacent_to_after
          before middle oldSuffix (shallow, c)
          (parentDepth + 1, a) (parentDepth + 1, b))
    have hbranch :
        TwoSmallestDeepestExchangeBranch
          (leafDepthWeights depth tree) swappedPairs := by
      exact TwoSmallestDeepestExchangeBranch.leftDeepestFirstSmallest
        before middle oldSuffix rest hpairsPerm hswappedPerm
        htwoSmallest hrest hdepth
    have hdepths :
        swappedPairs.map Prod.fst =
          (leafDepthWeights depth tree).map Prod.fst := by
      rw [htreeDepth, hsplit]
      simp [swappedPairs, newPre, List.map_append]
    have hdisplay :
        swappedPairs =
          newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            oldSuffix := by
      rfl
    have hpreLen : newPre.length = oldPre.length := by
      rw [hsplit]
      simp [newPre, List.length_append]
    obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
        hleavesPerm, _hrealizedEq⟩ :=
      hbridge (swappedPairs := swappedPairs) (newPre := newPre)
        (newSuffix := oldSuffix) hbranch hdepths hdisplay hpreLen rfl
    exact ⟨swappedTree, swappedContracted, Or.inl hcontractedRelabel,
      hcost, hleavesPerm⟩
  · have hb_eq_c : b = c := hright.2
    subst b
    exact ⟨tree, contracted, Or.inl hcontract, le_rfl,
      List.Perm.refl tree.leaves⟩
  · obtain ⟨middle, suffix, hsplit⟩ :=
      exists_split_of_mem oldSuffix hsuffix
    let newSuffix := middle ++ [(shallow, c)] ++ suffix
    let swappedPairs :=
      oldPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
        newSuffix
    have hpairsPerm :
        (leafDepthWeights depth tree).Perm
          (oldPre ++ [(parentDepth + 1, a), (parentDepth + 1, c)] ++
            middle ++ [(shallow, b)] ++ suffix) := by
      rw [htreeDepth, hsplit]
      simp [List.append_assoc]
    have hbranch :
        TwoSmallestDeepestExchangeBranch
          (leafDepthWeights depth tree) swappedPairs := by
      exact TwoSmallestDeepestExchangeBranch.leftDeepestFirstSmallest
        oldPre middle suffix rest hpairsPerm
        (by simp [swappedPairs, newSuffix, List.append_assoc])
        htwoSmallest hrest hdepth
    have hdepths :
        swappedPairs.map Prod.fst =
          (leafDepthWeights depth tree).map Prod.fst := by
      rw [htreeDepth, hsplit]
      simp [swappedPairs, newSuffix, List.map_append]
    have hdisplay :
        swappedPairs =
          oldPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            newSuffix := by
      rfl
    have hsuffixLen : newSuffix.length = oldSuffix.length := by
      rw [hsplit]
      simp [newSuffix, List.length_append]
    obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
        hleavesPerm, _hrealizedEq⟩ :=
      hbridge (swappedPairs := swappedPairs) (newPre := oldPre)
        (newSuffix := newSuffix) hbranch hdepths hdisplay rfl hsuffixLen
    exact ⟨swappedTree, swappedContracted, Or.inl hcontractedRelabel,
      hcost, hleavesPerm⟩

/-- Fixed-context contraction-aware classifier for the orientation where the
first selected two-smallest entry is already the right member of the displayed
old contracted sibling pair.  This is the shared-context continuation used by
the arbitrary occurrence dispatcher. -/
theorem
    exists_relabelLeaves_contract_for_right_deepest_first_two_smallest_anywhere_of_context
    {tree contracted : InsertionScheduleTree} {depth parentDepth : ℕ}
    {oldPre oldSuffix : List (ℕ × ℝ)} {a c : ℝ}
    (hcontract : SiblingLeafContract tree contracted c a)
    (htreeDepth :
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, a)] ++
          oldSuffix)
    (hbridge :
      ∀ {swappedPairs newPre newSuffix : List (ℕ × ℝ)} {x y : ℝ},
        TwoSmallestDeepestExchangeBranch
          (leafDepthWeights depth tree) swappedPairs →
        swappedPairs.map Prod.fst =
          (leafDepthWeights depth tree).map Prod.fst →
        swappedPairs =
          newPre ++ [(parentDepth + 1, x), (parentDepth + 1, y)] ++
            newSuffix →
        newPre.length = oldPre.length →
        newSuffix.length = oldSuffix.length →
        ∃ swappedTree swappedContracted : InsertionScheduleTree,
          SiblingLeafContract swappedTree swappedContracted x y ∧
            weightedLeafDepthCost depth swappedTree ≤
              weightedLeafDepthCost depth tree ∧
              swappedTree.leaves.Perm tree.leaves ∧
                leafDepthWeights depth swappedTree = swappedPairs) :
    ∀ {rest : List (ℕ × ℝ)} {b : ℝ} {shallow : ℕ},
      (leafDepthWeights depth tree).Perm
        ((parentDepth + 1, a) :: (shallow, b) :: rest) →
      (∀ pair ∈ rest, b ≤ pair.2) →
      shallow ≤ parentDepth + 1 →
      ∃ swappedTree swappedContracted : InsertionScheduleTree,
        (SiblingLeafContract swappedTree swappedContracted a b ∨
          SiblingLeafContract swappedTree swappedContracted b a) ∧
          weightedLeafDepthCost depth swappedTree ≤
            weightedLeafDepthCost depth tree ∧
            swappedTree.leaves.Perm tree.leaves := by
  intro rest b shallow htwoSmallest hrest hdepth
  have hpairsFront :
      (leafDepthWeights depth tree).Perm
        ((parentDepth + 1, a) :: oldPre ++ [(parentDepth + 1, c)] ++
          oldSuffix) := by
    rw [htreeDepth]
    simpa [List.append_assoc] using
      (List.perm_middle (a := (parentDepth + 1, a))
        (l₁ := oldPre ++ [(parentDepth + 1, c)]) (l₂ := oldSuffix))
  have htailPerm :
      (oldPre ++ [(parentDepth + 1, c)] ++ oldSuffix).Perm
        ((shallow, b) :: rest) :=
    List.Perm.cons_inv (hpairsFront.symm.trans htwoSmallest)
  have hsecond_mem :
      (shallow, b) ∈ oldPre ++ [(parentDepth + 1, c)] ++ oldSuffix :=
    (htailPerm.mem_iff).2 (by simp)
  simp [List.mem_append] at hsecond_mem
  rcases hsecond_mem with hpre | hleft | hsuffix
  · obtain ⟨before, middle, hsplit⟩ :=
      exists_split_of_mem oldPre hpre
    let newPre := before ++ [(shallow, c)] ++ middle
    let swappedPairs :=
      newPre ++ [(parentDepth + 1, b), (parentDepth + 1, a)] ++
        oldSuffix
    have hpairsPerm :
        (leafDepthWeights depth tree).Perm
          (before ++ [(parentDepth + 1, c), (parentDepth + 1, a)] ++
            middle ++ [(shallow, b)] ++ oldSuffix) := by
      rw [htreeDepth, hsplit]
      simpa [List.append_assoc] using
        (listPerm_selected_before_adjacent_to_after
          before middle oldSuffix (shallow, b)
          (parentDepth + 1, c) (parentDepth + 1, a))
    have hswappedPerm :
        swappedPairs.Perm
          (before ++ [(parentDepth + 1, b), (parentDepth + 1, a)] ++
            middle ++ [(shallow, c)] ++ oldSuffix) := by
      simpa [swappedPairs, newPre, List.append_assoc] using
        (listPerm_selected_before_adjacent_to_after
          before middle oldSuffix (shallow, c)
          (parentDepth + 1, b) (parentDepth + 1, a))
    have hbranch :
        TwoSmallestDeepestExchangeBranch
          (leafDepthWeights depth tree) swappedPairs := by
      exact TwoSmallestDeepestExchangeBranch.rightDeepestFirstSmallest
        before middle oldSuffix rest hpairsPerm hswappedPerm
        htwoSmallest hrest hdepth
    have hdepths :
        swappedPairs.map Prod.fst =
          (leafDepthWeights depth tree).map Prod.fst := by
      rw [htreeDepth, hsplit]
      simp [swappedPairs, newPre, List.map_append]
    have hdisplay :
        swappedPairs =
          newPre ++ [(parentDepth + 1, b), (parentDepth + 1, a)] ++
            oldSuffix := by
      rfl
    have hpreLen : newPre.length = oldPre.length := by
      rw [hsplit]
      simp [newPre, List.length_append]
    obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
        hleavesPerm, _hrealizedEq⟩ :=
      hbridge (swappedPairs := swappedPairs) (newPre := newPre)
        (newSuffix := oldSuffix) (x := b) (y := a)
        hbranch hdepths hdisplay hpreLen rfl
    exact ⟨swappedTree, swappedContracted, Or.inr hcontractedRelabel,
      hcost, hleavesPerm⟩
  · have hb_eq_c : b = c := hleft.2
    subst b
    exact ⟨tree, contracted, Or.inr hcontract, le_rfl,
      List.Perm.refl tree.leaves⟩
  · obtain ⟨middle, suffix, hsplit⟩ :=
      exists_split_of_mem oldSuffix hsuffix
    let newSuffix := middle ++ [(shallow, c)] ++ suffix
    let swappedPairs :=
      oldPre ++ [(parentDepth + 1, b), (parentDepth + 1, a)] ++
        newSuffix
    have hpairsPerm :
        (leafDepthWeights depth tree).Perm
          (oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, a)] ++
            middle ++ [(shallow, b)] ++ suffix) := by
      rw [htreeDepth, hsplit]
      simp [List.append_assoc]
    have hbranch :
        TwoSmallestDeepestExchangeBranch
          (leafDepthWeights depth tree) swappedPairs := by
      exact TwoSmallestDeepestExchangeBranch.rightDeepestFirstSmallest
        oldPre middle suffix rest hpairsPerm
        (by simp [swappedPairs, newSuffix, List.append_assoc])
        htwoSmallest hrest hdepth
    have hdepths :
        swappedPairs.map Prod.fst =
          (leafDepthWeights depth tree).map Prod.fst := by
      rw [htreeDepth, hsplit]
      simp [swappedPairs, newSuffix, List.map_append]
    have hdisplay :
        swappedPairs =
          oldPre ++ [(parentDepth + 1, b), (parentDepth + 1, a)] ++
            newSuffix := by
      rfl
    have hsuffixLen : newSuffix.length = oldSuffix.length := by
      rw [hsplit]
      simp [newSuffix, List.length_append]
    obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
        hleavesPerm, _hrealizedEq⟩ :=
      hbridge (swappedPairs := swappedPairs) (newPre := oldPre)
        (newSuffix := newSuffix) (x := b) (y := a)
        hbranch hdepths hdisplay rfl hsuffixLen
    exact ⟨swappedTree, swappedContracted, Or.inr hcontractedRelabel,
      hcost, hleavesPerm⟩

/-- Fixed-context contraction-aware classifier for the orientation where the
first selected two-smallest slot is before the displayed old contracted
sibling pair.  The second selected slot may overlap either old sibling or be a
nonoverlapping occurrence elsewhere. -/
theorem
    exists_relabelLeaves_contract_for_first_before_contracted_pair_anywhere_of_context
    {tree : InsertionScheduleTree} {depth parentDepth : ℕ}
    {oldPre oldSuffix : List (ℕ × ℝ)} {c d : ℝ}
    (htreeDepth :
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          oldSuffix)
    (hbridge :
      ∀ {swappedPairs newPre newSuffix : List (ℕ × ℝ)} {a b : ℝ},
        TwoSmallestDeepestExchangeBranch
          (leafDepthWeights depth tree) swappedPairs →
        swappedPairs.map Prod.fst =
          (leafDepthWeights depth tree).map Prod.fst →
        swappedPairs =
          newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            newSuffix →
        newPre.length = oldPre.length →
        newSuffix.length = oldSuffix.length →
        ∃ swappedTree swappedContracted : InsertionScheduleTree,
          SiblingLeafContract swappedTree swappedContracted a b ∧
            weightedLeafDepthCost depth swappedTree ≤
              weightedLeafDepthCost depth tree ∧
              swappedTree.leaves.Perm tree.leaves ∧
                leafDepthWeights depth swappedTree = swappedPairs) :
    ∀ {before middle suffix rest : List (ℕ × ℝ)}
        {a b : ℝ} {shallow₁ shallow₂ : ℕ},
      oldPre = before ++ [(shallow₁, a)] ++ middle →
      oldSuffix = suffix →
      (leafDepthWeights depth tree).Perm
        ((shallow₁, a) :: (shallow₂, b) :: rest) →
      a ≤ b →
      (∀ pair ∈ rest, b ≤ pair.2) →
      shallow₁ ≤ parentDepth + 1 →
      shallow₂ ≤ parentDepth + 1 →
      ∃ swappedTree swappedContracted : InsertionScheduleTree,
        (SiblingLeafContract swappedTree swappedContracted a b ∨
          SiblingLeafContract swappedTree swappedContracted b a) ∧
          weightedLeafDepthCost depth swappedTree ≤
            weightedLeafDepthCost depth tree ∧
            swappedTree.leaves.Perm tree.leaves := by
  intro before middle suffix rest a b shallow₁ shallow₂ hpre hsuffix
    htwoSmallest hab hrest hdepth₁ hdepth₂
  by_cases hleft : (shallow₂, b) = (parentDepth + 1, c)
  · cases hleft
    let newPre := before ++ [(shallow₁, d)] ++ middle
    let swappedPairs :=
      newPre ++ [(parentDepth + 1, c), (parentDepth + 1, a)] ++
        oldSuffix
    have hpairsPerm :
        (leafDepthWeights depth tree).Perm
          (before ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
            middle ++ [(shallow₁, a)] ++ oldSuffix) := by
      rw [htreeDepth, hpre]
      simpa [List.append_assoc] using
        (listPerm_selected_before_adjacent_to_after
          before middle oldSuffix (shallow₁, a)
          (parentDepth + 1, c) (parentDepth + 1, d))
    have hswappedPerm :
        swappedPairs.Perm
          (before ++ [(parentDepth + 1, c), (parentDepth + 1, a)] ++
            middle ++ [(shallow₁, d)] ++ oldSuffix) := by
      simpa [swappedPairs, newPre, List.append_assoc] using
        (listPerm_selected_before_adjacent_to_after
          before middle oldSuffix (shallow₁, d)
          (parentDepth + 1, c) (parentDepth + 1, a))
    have hbranch :
        TwoSmallestDeepestExchangeBranch
          (leafDepthWeights depth tree) swappedPairs := by
      exact TwoSmallestDeepestExchangeBranch.leftDeepestSecondSmallest
        before middle oldSuffix rest hpairsPerm hswappedPerm
        htwoSmallest hab hrest hdepth₁
    have hdepths :
        swappedPairs.map Prod.fst =
          (leafDepthWeights depth tree).map Prod.fst := by
      rw [htreeDepth, hpre]
      simp [swappedPairs, newPre, List.map_append]
    have hdisplay :
        swappedPairs =
          newPre ++ [(parentDepth + 1, c), (parentDepth + 1, a)] ++
            oldSuffix := by
      rfl
    have hpreLen : newPre.length = oldPre.length := by
      rw [hpre]
      simp [newPre, List.length_append]
    obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
        hleavesPerm, _hrealizedEq⟩ :=
      hbridge (swappedPairs := swappedPairs) (newPre := newPre)
        (newSuffix := oldSuffix) (a := c) (b := a)
        hbranch hdepths hdisplay hpreLen rfl
    exact ⟨swappedTree, swappedContracted, Or.inr hcontractedRelabel,
      hcost, hleavesPerm⟩
  · by_cases hright : (shallow₂, b) = (parentDepth + 1, d)
    · cases hright
      let newPre := before ++ [(shallow₁, c)] ++ middle
      let swappedPairs :=
        newPre ++ [(parentDepth + 1, a), (parentDepth + 1, d)] ++
          oldSuffix
      have hpairsPerm :
          (leafDepthWeights depth tree).Perm
            (before ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
              middle ++ [(shallow₁, a)] ++ oldSuffix) := by
        rw [htreeDepth, hpre]
        simpa [List.append_assoc] using
          (listPerm_selected_before_adjacent_to_after
            before middle oldSuffix (shallow₁, a)
            (parentDepth + 1, c) (parentDepth + 1, d))
      have hswappedPerm :
          swappedPairs.Perm
            (before ++ [(parentDepth + 1, a), (parentDepth + 1, d)] ++
              middle ++ [(shallow₁, c)] ++ oldSuffix) := by
        simpa [swappedPairs, newPre, List.append_assoc] using
          (listPerm_selected_before_adjacent_to_after
            before middle oldSuffix (shallow₁, c)
            (parentDepth + 1, a) (parentDepth + 1, d))
      have hbranch :
          TwoSmallestDeepestExchangeBranch
            (leafDepthWeights depth tree) swappedPairs := by
        exact TwoSmallestDeepestExchangeBranch.rightDeepestSecondSmallest
          before middle oldSuffix rest hpairsPerm hswappedPerm
          htwoSmallest hab hrest hdepth₁
      have hdepths :
          swappedPairs.map Prod.fst =
            (leafDepthWeights depth tree).map Prod.fst := by
        rw [htreeDepth, hpre]
        simp [swappedPairs, newPre, List.map_append]
      have hdisplay :
          swappedPairs =
            newPre ++ [(parentDepth + 1, a), (parentDepth + 1, d)] ++
              oldSuffix := by
        rfl
      have hpreLen : newPre.length = oldPre.length := by
        rw [hpre]
        simp [newPre, List.length_append]
      obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
          hleavesPerm, _hrealizedEq⟩ :=
        hbridge (swappedPairs := swappedPairs) (newPre := newPre)
          (newSuffix := oldSuffix) (a := a) (b := d)
          hbranch hdepths hdisplay hpreLen rfl
      exact ⟨swappedTree, swappedContracted, Or.inl hcontractedRelabel,
        hcost, hleavesPerm⟩
    · have hpairsDisplay :
          leafDepthWeights depth tree =
            before ++ [(shallow₁, a)] ++ middle ++
              [(parentDepth + 1, c), (parentDepth + 1, d)] ++ suffix := by
        rw [htreeDepth, hpre, hsuffix]
      obtain hloc :=
        exists_second_position_of_first_before_adjacent_pair
          (pairs := leafDepthWeights depth tree) (rest := rest)
          (first := (shallow₁, a)) (second := (shallow₂, b))
          (left := (parentDepth + 1, c))
          (right := (parentDepth + 1, d))
          before middle suffix hpairsDisplay htwoSmallest hleft hright
      rcases hloc with hsecondBefore | hsecondMiddle | hsecondAfter
      · obtain ⟨pre₂, gap, hbeforeSplit, hpairs'⟩ := hsecondBefore
        let newPre :=
          pre₂ ++ [(shallow₂, d)] ++ gap ++ [(shallow₁, c)] ++ middle
        let swappedPairs :=
          newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            suffix
        have hpairsPerm :
            (leafDepthWeights depth tree).Perm
              (pre₂ ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
                gap ++ [(shallow₁, a)] ++ middle ++
                  [(shallow₂, b)] ++ suffix) := by
          rw [hpairs']
          simpa [List.append_assoc] using
            (listPerm_two_selected_before_deepest_to_canonical
              pre₂ gap middle suffix
              (parentDepth + 1, c) (parentDepth + 1, d)
              (shallow₂, b) (shallow₁, a)).trans
              (weightListPerm_pair_exchange
                (pre₂ ++ [(parentDepth + 1, c),
                  (parentDepth + 1, d)] ++ gap)
                middle suffix (shallow₂, b) (shallow₁, a))
        have hswappedToReverseCanonical :
            swappedPairs.Perm
              (pre₂ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                gap ++ [(shallow₂, d)] ++ middle ++
                  [(shallow₁, c)] ++ suffix) := by
          simpa [swappedPairs, newPre, List.append_assoc] using
            (listPerm_two_selected_before_deepest_to_canonical
              pre₂ gap middle suffix
              (parentDepth + 1, a) (parentDepth + 1, b)
              (shallow₂, d) (shallow₁, c))
        have hswappedPerm :
            swappedPairs.Perm
              (pre₂ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                gap ++ [(shallow₁, c)] ++ middle ++
                  [(shallow₂, d)] ++ suffix) := by
          exact hswappedToReverseCanonical.trans
            (weightListPerm_pair_exchange
              (pre₂ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                gap)
              middle suffix (shallow₂, d) (shallow₁, c))
        have hbranch :
            TwoSmallestDeepestExchangeBranch
              (leafDepthWeights depth tree) swappedPairs := by
          exact TwoSmallestDeepestExchangeBranch.nondegenerate
            pre₂ gap middle suffix rest hpairsPerm hswappedPerm
            htwoSmallest hab hrest hdepth₁ hdepth₂
        have hdepths :
            swappedPairs.map Prod.fst =
              (leafDepthWeights depth tree).map Prod.fst := by
          rw [hpairs']
          simp [swappedPairs, newPre, List.map_append]
        have hdisplay :
            swappedPairs =
              newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                suffix := by
          rfl
        have hpreLen : newPre.length = oldPre.length := by
          rw [hpre, hbeforeSplit]
          simp [newPre, List.length_append]
        obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
            hleavesPerm, _hrealizedEq⟩ :=
          hbridge (swappedPairs := swappedPairs) (newPre := newPre)
            (newSuffix := suffix) hbranch hdepths hdisplay hpreLen (by
              rw [hsuffix])
        exact ⟨swappedTree, swappedContracted, Or.inl hcontractedRelabel,
          hcost, hleavesPerm⟩
      · obtain ⟨gap, tail, hmiddleSplit, hpairs'⟩ := hsecondMiddle
        let newPre :=
          before ++ [(shallow₁, c)] ++ gap ++ [(shallow₂, d)] ++ tail
        let swappedPairs :=
          newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            suffix
        have hpairsPerm :
            (leafDepthWeights depth tree).Perm
              (before ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
                gap ++ [(shallow₁, a)] ++ tail ++
                  [(shallow₂, b)] ++ suffix) := by
          rw [hpairs']
          exact listPerm_two_selected_before_deepest_to_canonical
            before gap tail suffix
            (parentDepth + 1, c) (parentDepth + 1, d)
            (shallow₁, a) (shallow₂, b)
        have hswappedPerm :
            swappedPairs.Perm
              (before ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                gap ++ [(shallow₁, c)] ++ tail ++
                  [(shallow₂, d)] ++ suffix) := by
          simpa [swappedPairs, newPre, List.append_assoc] using
            (listPerm_two_selected_before_deepest_to_canonical
              before gap tail suffix
              (parentDepth + 1, a) (parentDepth + 1, b)
              (shallow₁, c) (shallow₂, d))
        have hbranch :
            TwoSmallestDeepestExchangeBranch
              (leafDepthWeights depth tree) swappedPairs := by
          exact TwoSmallestDeepestExchangeBranch.nondegenerate
            before gap tail suffix rest hpairsPerm hswappedPerm
            htwoSmallest hab hrest hdepth₁ hdepth₂
        have hdepths :
            swappedPairs.map Prod.fst =
              (leafDepthWeights depth tree).map Prod.fst := by
          rw [hpairs']
          simp [swappedPairs, newPre, List.map_append]
        have hdisplay :
            swappedPairs =
              newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                suffix := by
          rfl
        have hpreLen : newPre.length = oldPre.length := by
          rw [hpre]
          rw [hmiddleSplit]
          simp [newPre, List.length_append]
        obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
            hleavesPerm, _hrealizedEq⟩ :=
          hbridge (swappedPairs := swappedPairs) (newPre := newPre)
            (newSuffix := suffix) hbranch hdepths hdisplay hpreLen (by
              rw [hsuffix])
        exact ⟨swappedTree, swappedContracted, Or.inl hcontractedRelabel,
          hcost, hleavesPerm⟩
      · obtain ⟨gap, tail, hsuffixSplit, hpairs'⟩ := hsecondAfter
        let newPre := before ++ [(shallow₁, c)] ++ middle
        let newSuffix := gap ++ [(shallow₂, d)] ++ tail
        let swappedPairs :=
          newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            newSuffix
        have hpairsPerm :
            (leafDepthWeights depth tree).Perm
              (before ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
                middle ++ [(shallow₁, a)] ++ gap ++
                  [(shallow₂, b)] ++ tail) := by
          rw [hpairs']
          exact listPerm_selected_before_deepest_before_selected_to_canonical
            before middle gap tail
            (parentDepth + 1, c) (parentDepth + 1, d)
            (shallow₁, a) (shallow₂, b)
        have hswappedPerm :
            swappedPairs.Perm
              (before ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                middle ++ [(shallow₁, c)] ++ gap ++
                  [(shallow₂, d)] ++ tail) := by
          simpa [swappedPairs, newPre, newSuffix, List.append_assoc] using
            (listPerm_selected_before_deepest_before_selected_to_canonical
              before middle gap tail
              (parentDepth + 1, a) (parentDepth + 1, b)
              (shallow₁, c) (shallow₂, d))
        have hbranch :
            TwoSmallestDeepestExchangeBranch
              (leafDepthWeights depth tree) swappedPairs := by
          exact TwoSmallestDeepestExchangeBranch.nondegenerate
            before middle gap tail rest hpairsPerm hswappedPerm
            htwoSmallest hab hrest hdepth₁ hdepth₂
        have hdepths :
            swappedPairs.map Prod.fst =
              (leafDepthWeights depth tree).map Prod.fst := by
          rw [hpairs']
          simp [swappedPairs, newPre, newSuffix, List.map_append]
        have hdisplay :
            swappedPairs =
              newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                newSuffix := by
          rfl
        have hpreLen : newPre.length = oldPre.length := by
          rw [hpre]
          simp [newPre, List.length_append]
        have hsuffixLen : newSuffix.length = oldSuffix.length := by
          rw [hsuffix, hsuffixSplit]
          simp [newSuffix, List.length_append]
        obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
            hleavesPerm, _hrealizedEq⟩ :=
          hbridge (swappedPairs := swappedPairs) (newPre := newPre)
            (newSuffix := newSuffix) hbranch hdepths hdisplay hpreLen
            hsuffixLen
        exact ⟨swappedTree, swappedContracted, Or.inl hcontractedRelabel,
          hcost, hleavesPerm⟩

/-- Fixed-context contraction-aware classifier for the orientation where the
first selected two-smallest slot is after the displayed old contracted
sibling pair.  The second selected slot may overlap either old sibling or be a
nonoverlapping occurrence elsewhere. -/
theorem
    exists_relabelLeaves_contract_for_first_after_contracted_pair_anywhere_of_context
    {tree : InsertionScheduleTree} {depth parentDepth : ℕ}
    {oldPre oldSuffix : List (ℕ × ℝ)} {c d : ℝ}
    (htreeDepth :
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          oldSuffix)
    (hbridge :
      ∀ {swappedPairs newPre newSuffix : List (ℕ × ℝ)} {a b : ℝ},
        TwoSmallestDeepestExchangeBranch
          (leafDepthWeights depth tree) swappedPairs →
        swappedPairs.map Prod.fst =
          (leafDepthWeights depth tree).map Prod.fst →
        swappedPairs =
          newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            newSuffix →
        newPre.length = oldPre.length →
        newSuffix.length = oldSuffix.length →
        ∃ swappedTree swappedContracted : InsertionScheduleTree,
          SiblingLeafContract swappedTree swappedContracted a b ∧
            weightedLeafDepthCost depth swappedTree ≤
              weightedLeafDepthCost depth tree ∧
              swappedTree.leaves.Perm tree.leaves ∧
                leafDepthWeights depth swappedTree = swappedPairs) :
    ∀ {before middle suffix rest : List (ℕ × ℝ)}
        {a b : ℝ} {shallow₁ shallow₂ : ℕ},
      oldPre = before →
      oldSuffix = middle ++ [(shallow₁, a)] ++ suffix →
      (leafDepthWeights depth tree).Perm
        ((shallow₁, a) :: (shallow₂, b) :: rest) →
      a ≤ b →
      (∀ pair ∈ rest, b ≤ pair.2) →
      shallow₁ ≤ parentDepth + 1 →
      shallow₂ ≤ parentDepth + 1 →
      ∃ swappedTree swappedContracted : InsertionScheduleTree,
        (SiblingLeafContract swappedTree swappedContracted a b ∨
          SiblingLeafContract swappedTree swappedContracted b a) ∧
          weightedLeafDepthCost depth swappedTree ≤
            weightedLeafDepthCost depth tree ∧
            swappedTree.leaves.Perm tree.leaves := by
  intro before middle suffix rest a b shallow₁ shallow₂ hpre hsuffix
    htwoSmallest hab hrest hdepth₁ hdepth₂
  by_cases hleft : (shallow₂, b) = (parentDepth + 1, c)
  · cases hleft
    let newPre := before
    let newSuffix := middle ++ [(shallow₁, d)] ++ suffix
    let swappedPairs :=
      newPre ++ [(parentDepth + 1, c), (parentDepth + 1, a)] ++
        newSuffix
    have hpairsPerm :
        (leafDepthWeights depth tree).Perm
          (before ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
            middle ++ [(shallow₁, a)] ++ suffix) := by
      rw [htreeDepth, hpre, hsuffix]
      simp [List.append_assoc]
    have hbranch :
        TwoSmallestDeepestExchangeBranch
          (leafDepthWeights depth tree) swappedPairs := by
      exact TwoSmallestDeepestExchangeBranch.leftDeepestSecondSmallest
        before middle suffix rest hpairsPerm
        (by simp [swappedPairs, newPre, newSuffix, List.append_assoc])
        htwoSmallest hab hrest hdepth₁
    have hdepths :
        swappedPairs.map Prod.fst =
          (leafDepthWeights depth tree).map Prod.fst := by
      rw [htreeDepth, hpre, hsuffix]
      simp [swappedPairs, newPre, newSuffix, List.map_append]
    have hdisplay :
        swappedPairs =
          newPre ++ [(parentDepth + 1, c), (parentDepth + 1, a)] ++
            newSuffix := by
      rfl
    have hpreLen : newPre.length = oldPre.length := by
      rw [hpre]
    have hsuffixLen : newSuffix.length = oldSuffix.length := by
      rw [hsuffix]
      simp [newSuffix, List.length_append]
    obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
        hleavesPerm, _hrealizedEq⟩ :=
      hbridge (swappedPairs := swappedPairs) (newPre := newPre)
        (newSuffix := newSuffix) (a := c) (b := a)
        hbranch hdepths hdisplay hpreLen hsuffixLen
    exact ⟨swappedTree, swappedContracted, Or.inr hcontractedRelabel,
      hcost, hleavesPerm⟩
  · by_cases hright : (shallow₂, b) = (parentDepth + 1, d)
    · cases hright
      let newPre := before
      let newSuffix := middle ++ [(shallow₁, c)] ++ suffix
      let swappedPairs :=
        newPre ++ [(parentDepth + 1, a), (parentDepth + 1, d)] ++
          newSuffix
      have hpairsPerm :
          (leafDepthWeights depth tree).Perm
            (before ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
              middle ++ [(shallow₁, a)] ++ suffix) := by
        rw [htreeDepth, hpre, hsuffix]
        simp [List.append_assoc]
      have hbranch :
          TwoSmallestDeepestExchangeBranch
            (leafDepthWeights depth tree) swappedPairs := by
        exact TwoSmallestDeepestExchangeBranch.rightDeepestSecondSmallest
          before middle suffix rest hpairsPerm
          (by simp [swappedPairs, newPre, newSuffix, List.append_assoc])
          htwoSmallest hab hrest hdepth₁
      have hdepths :
          swappedPairs.map Prod.fst =
            (leafDepthWeights depth tree).map Prod.fst := by
        rw [htreeDepth, hpre, hsuffix]
        simp [swappedPairs, newPre, newSuffix, List.map_append]
      have hdisplay :
          swappedPairs =
            newPre ++ [(parentDepth + 1, a), (parentDepth + 1, d)] ++
              newSuffix := by
        rfl
      have hpreLen : newPre.length = oldPre.length := by
        rw [hpre]
      have hsuffixLen : newSuffix.length = oldSuffix.length := by
        rw [hsuffix]
        simp [newSuffix, List.length_append]
      obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
          hleavesPerm, _hrealizedEq⟩ :=
        hbridge (swappedPairs := swappedPairs) (newPre := newPre)
          (newSuffix := newSuffix) (a := a) (b := d)
          hbranch hdepths hdisplay hpreLen hsuffixLen
      exact ⟨swappedTree, swappedContracted, Or.inl hcontractedRelabel,
        hcost, hleavesPerm⟩
    · have hpairsDisplay :
          leafDepthWeights depth tree =
            before ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
              middle ++ [(shallow₁, a)] ++ suffix := by
        rw [htreeDepth, hpre, hsuffix]
        simp [List.append_assoc]
      obtain hloc :=
        exists_second_position_of_first_after_adjacent_pair
          (pairs := leafDepthWeights depth tree) (rest := rest)
          (first := (shallow₁, a)) (second := (shallow₂, b))
          (left := (parentDepth + 1, c))
          (right := (parentDepth + 1, d))
          before middle suffix hpairsDisplay htwoSmallest hleft hright
      rcases hloc with hsecondBefore | hsecondMiddle | hsecondAfter
      · obtain ⟨pre₂, gap, hbeforeSplit, hpairs'⟩ := hsecondBefore
        let newPre := pre₂ ++ [(shallow₂, d)] ++ gap
        let newSuffix := middle ++ [(shallow₁, c)] ++ suffix
        let swappedPairs :=
          newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            newSuffix
        have hpairsToReverseCanonical :
            (leafDepthWeights depth tree).Perm
              (pre₂ ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
                gap ++ [(shallow₂, b)] ++ middle ++
                  [(shallow₁, a)] ++ suffix) := by
          rw [hpairs']
          simpa [List.append_assoc] using
            (listPerm_selected_before_deepest_before_selected_to_canonical
              pre₂ gap middle suffix
              (parentDepth + 1, c) (parentDepth + 1, d)
              (shallow₂, b) (shallow₁, a))
        have hpairsPerm :
            (leafDepthWeights depth tree).Perm
              (pre₂ ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
                gap ++ [(shallow₁, a)] ++ middle ++
                  [(shallow₂, b)] ++ suffix) := by
          exact hpairsToReverseCanonical.trans
            (weightListPerm_pair_exchange
              (pre₂ ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
                gap)
              middle suffix (shallow₂, b) (shallow₁, a))
        have hswappedToReverseCanonical :
            swappedPairs.Perm
              (pre₂ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                gap ++ [(shallow₂, d)] ++ middle ++
                  [(shallow₁, c)] ++ suffix) := by
          simpa [swappedPairs, newPre, newSuffix, List.append_assoc] using
            (listPerm_selected_before_deepest_before_selected_to_canonical
              pre₂ gap middle suffix
              (parentDepth + 1, a) (parentDepth + 1, b)
              (shallow₂, d) (shallow₁, c))
        have hswappedPerm :
            swappedPairs.Perm
              (pre₂ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                gap ++ [(shallow₁, c)] ++ middle ++
                  [(shallow₂, d)] ++ suffix) := by
          exact hswappedToReverseCanonical.trans
            (weightListPerm_pair_exchange
              (pre₂ ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                gap)
              middle suffix (shallow₂, d) (shallow₁, c))
        have hbranch :
            TwoSmallestDeepestExchangeBranch
              (leafDepthWeights depth tree) swappedPairs := by
          exact TwoSmallestDeepestExchangeBranch.nondegenerate
            pre₂ gap middle suffix rest hpairsPerm hswappedPerm
            htwoSmallest hab hrest hdepth₁ hdepth₂
        have hdepths :
            swappedPairs.map Prod.fst =
              (leafDepthWeights depth tree).map Prod.fst := by
          rw [hpairs']
          simp [swappedPairs, newPre, newSuffix, List.map_append]
        have hdisplay :
            swappedPairs =
              newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                newSuffix := by
          rfl
        have hpreLen : newPre.length = oldPre.length := by
          rw [hpre, hbeforeSplit]
          simp [newPre, List.length_append]
        have hsuffixLen : newSuffix.length = oldSuffix.length := by
          rw [hsuffix]
          simp [newSuffix, List.length_append]
        obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
            hleavesPerm, _hrealizedEq⟩ :=
          hbridge (swappedPairs := swappedPairs) (newPre := newPre)
            (newSuffix := newSuffix) hbranch hdepths hdisplay hpreLen
            hsuffixLen
        exact ⟨swappedTree, swappedContracted, Or.inl hcontractedRelabel,
          hcost, hleavesPerm⟩
      · obtain ⟨gap, tail, hmiddleSplit, hpairs'⟩ := hsecondMiddle
        let newPre := before
        let newSuffix :=
          gap ++ [(shallow₂, d)] ++ tail ++ [(shallow₁, c)] ++ suffix
        let swappedPairs :=
          newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            newSuffix
        have hpairsPerm :
            (leafDepthWeights depth tree).Perm
              (before ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
                gap ++ [(shallow₁, a)] ++ tail ++
                  [(shallow₂, b)] ++ suffix) := by
          rw [hpairs']
          simpa [List.append_assoc] using
            (weightListPerm_pair_exchange
              (before ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
                gap)
              tail suffix (shallow₂, b) (shallow₁, a))
        have hswappedPerm :
            swappedPairs.Perm
              (before ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                gap ++ [(shallow₁, c)] ++ tail ++
                  [(shallow₂, d)] ++ suffix) := by
          simpa [swappedPairs, newPre, newSuffix, List.append_assoc] using
            (weightListPerm_pair_exchange
              (before ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                gap)
              tail suffix (shallow₂, d) (shallow₁, c))
        have hbranch :
            TwoSmallestDeepestExchangeBranch
              (leafDepthWeights depth tree) swappedPairs := by
          exact TwoSmallestDeepestExchangeBranch.nondegenerate
            before gap tail suffix rest hpairsPerm hswappedPerm
            htwoSmallest hab hrest hdepth₁ hdepth₂
        have hdepths :
            swappedPairs.map Prod.fst =
              (leafDepthWeights depth tree).map Prod.fst := by
          rw [hpairs']
          simp [swappedPairs, newPre, newSuffix, List.map_append]
        have hdisplay :
            swappedPairs =
              newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                newSuffix := by
          rfl
        have hpreLen : newPre.length = oldPre.length := by
          rw [hpre]
        have hsuffixLen : newSuffix.length = oldSuffix.length := by
          rw [hsuffix, hmiddleSplit]
          simp [newSuffix, List.length_append]
        obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
            hleavesPerm, _hrealizedEq⟩ :=
          hbridge (swappedPairs := swappedPairs) (newPre := newPre)
            (newSuffix := newSuffix) hbranch hdepths hdisplay hpreLen
            hsuffixLen
        exact ⟨swappedTree, swappedContracted, Or.inl hcontractedRelabel,
          hcost, hleavesPerm⟩
      · obtain ⟨gap, tail, hsuffixSplit, hpairs'⟩ := hsecondAfter
        let newPre := before
        let newSuffix :=
          middle ++ [(shallow₁, c)] ++ gap ++ [(shallow₂, d)] ++ tail
        let swappedPairs :=
          newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            newSuffix
        have hpairsPerm :
            (leafDepthWeights depth tree).Perm
              (before ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
                middle ++ [(shallow₁, a)] ++ gap ++
                  [(shallow₂, b)] ++ tail) := by
          rw [hpairs']
        have hbranch :
            TwoSmallestDeepestExchangeBranch
              (leafDepthWeights depth tree) swappedPairs := by
          exact TwoSmallestDeepestExchangeBranch.nondegenerate
            before middle gap tail rest hpairsPerm
            (by simp [swappedPairs, newPre, newSuffix, List.append_assoc])
            htwoSmallest hab hrest hdepth₁ hdepth₂
        have hdepths :
            swappedPairs.map Prod.fst =
              (leafDepthWeights depth tree).map Prod.fst := by
          rw [hpairs']
          simp [swappedPairs, newPre, newSuffix, List.map_append]
        have hdisplay :
            swappedPairs =
              newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
                newSuffix := by
          rfl
        have hpreLen : newPre.length = oldPre.length := by
          rw [hpre]
        have hsuffixLen : newSuffix.length = oldSuffix.length := by
          rw [hsuffix, hsuffixSplit]
          simp [newSuffix, List.length_append]
        obtain ⟨swappedTree, swappedContracted, hcontractedRelabel, hcost,
            hleavesPerm, _hrealizedEq⟩ :=
          hbridge (swappedPairs := swappedPairs) (newPre := newPre)
            (newSuffix := newSuffix) hbranch hdepths hdisplay hpreLen
            hsuffixLen
        exact ⟨swappedTree, swappedContracted, Or.inl hcontractedRelabel,
          hcost, hleavesPerm⟩

/-- Fixed-context arbitrary occurrence dispatcher for contraction-aware
two-smallest/deepest normalization.  Once the four occurrence continuations are
available for the same displayed old sibling-pair context, the finite
selected-relative split combines them into the pointwise normalized contraction
used by the Huffman induction. -/
theorem
    exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_of_occurrence_classifiers
    {tree : InsertionScheduleTree} {depth parentDepth : ℕ}
    {oldPre oldSuffix rest : List (ℕ × ℝ)}
    {a b c d : ℝ} {shallow₁ shallow₂ : ℕ}
    (htreeDepth :
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          oldSuffix)
    (hfirstBefore :
      ∀ {before middle suffix rest : List (ℕ × ℝ)}
          {a b : ℝ} {shallow₁ shallow₂ : ℕ},
        oldPre = before ++ [(shallow₁, a)] ++ middle →
        oldSuffix = suffix →
        (leafDepthWeights depth tree).Perm
          ((shallow₁, a) :: (shallow₂, b) :: rest) →
        a ≤ b →
        (∀ pair ∈ rest, b ≤ pair.2) →
        shallow₁ ≤ parentDepth + 1 →
        shallow₂ ≤ parentDepth + 1 →
        ∃ swappedTree swappedContracted : InsertionScheduleTree,
          (SiblingLeafContract swappedTree swappedContracted a b ∨
            SiblingLeafContract swappedTree swappedContracted b a) ∧
            weightedLeafDepthCost depth swappedTree ≤
              weightedLeafDepthCost depth tree ∧
              swappedTree.leaves.Perm tree.leaves)
    (hfirstAfter :
      ∀ {before middle suffix rest : List (ℕ × ℝ)}
          {a b : ℝ} {shallow₁ shallow₂ : ℕ},
        oldPre = before →
        oldSuffix = middle ++ [(shallow₁, a)] ++ suffix →
        (leafDepthWeights depth tree).Perm
          ((shallow₁, a) :: (shallow₂, b) :: rest) →
        a ≤ b →
        (∀ pair ∈ rest, b ≤ pair.2) →
        shallow₁ ≤ parentDepth + 1 →
        shallow₂ ≤ parentDepth + 1 →
        ∃ swappedTree swappedContracted : InsertionScheduleTree,
          (SiblingLeafContract swappedTree swappedContracted a b ∨
            SiblingLeafContract swappedTree swappedContracted b a) ∧
            weightedLeafDepthCost depth swappedTree ≤
              weightedLeafDepthCost depth tree ∧
              swappedTree.leaves.Perm tree.leaves)
    (hleftFirst :
      ∀ {rest : List (ℕ × ℝ)} {b : ℝ} {shallow : ℕ},
        (leafDepthWeights depth tree).Perm
          ((parentDepth + 1, c) :: (shallow, b) :: rest) →
        (∀ pair ∈ rest, b ≤ pair.2) →
        shallow ≤ parentDepth + 1 →
        ∃ swappedTree swappedContracted : InsertionScheduleTree,
          (SiblingLeafContract swappedTree swappedContracted c b ∨
            SiblingLeafContract swappedTree swappedContracted b c) ∧
            weightedLeafDepthCost depth swappedTree ≤
              weightedLeafDepthCost depth tree ∧
              swappedTree.leaves.Perm tree.leaves)
    (hrightFirst :
      ∀ {rest : List (ℕ × ℝ)} {b : ℝ} {shallow : ℕ},
        (leafDepthWeights depth tree).Perm
          ((parentDepth + 1, d) :: (shallow, b) :: rest) →
        (∀ pair ∈ rest, b ≤ pair.2) →
        shallow ≤ parentDepth + 1 →
        ∃ swappedTree swappedContracted : InsertionScheduleTree,
          (SiblingLeafContract swappedTree swappedContracted d b ∨
            SiblingLeafContract swappedTree swappedContracted b d) ∧
            weightedLeafDepthCost depth swappedTree ≤
              weightedLeafDepthCost depth tree ∧
              swappedTree.leaves.Perm tree.leaves)
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((shallow₁, a) :: (shallow₂, b) :: rest))
    (hab : a ≤ b)
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth₁ : shallow₁ ≤ parentDepth + 1)
    (hdepth₂ : shallow₂ ≤ parentDepth + 1) :
    ∃ swappedTree swappedContracted : InsertionScheduleTree,
      (SiblingLeafContract swappedTree swappedContracted a b ∨
        SiblingLeafContract swappedTree swappedContracted b a) ∧
        weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
          swappedTree.leaves.Perm tree.leaves := by
  have hfirst_mem :
      (shallow₁, a) ∈ oldPre ++
        [(parentDepth + 1, c), (parentDepth + 1, d)] ++ oldSuffix := by
    have hmem : (shallow₁, a) ∈ leafDepthWeights depth tree :=
      (htwoSmallest.mem_iff).2 (by simp)
    simpa [htreeDepth] using hmem
  obtain hloc :=
    exists_selected_relative_to_adjacent_pair
      oldPre oldSuffix (parentDepth + 1, c) (parentDepth + 1, d)
      (shallow₁, a) hfirst_mem
  rcases hloc with hbefore | hleft | hright | hafter
  · obtain ⟨before, middle, hpre, _hpairsDisplay⟩ := hbefore
    exact hfirstBefore (by simpa using hpre) rfl htwoSmallest hab hrest
      hdepth₁ hdepth₂
  · cases hleft
    exact hleftFirst htwoSmallest hrest hdepth₂
  · cases hright
    exact hrightFirst htwoSmallest hrest hdepth₂
  · obtain ⟨middle, after, hsuffix, _hpairsDisplay⟩ := hafter
    exact hfirstAfter rfl (by simpa using hsuffix) htwoSmallest hab hrest
      hdepth₁ hdepth₂

/-- Shared-context contraction normalization for an arbitrary two-smallest
decomposition relative to a displayed deepest sibling contraction.  Starting
from one structural `SiblingLeafContract`, the theorem moves the two selected
smallest weights into a deepest sibling pair and returns an actual normalized
contracted companion tree, preserving the leaf multiset and not increasing the
weighted external path length. -/
theorem
    exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere
    {tree contracted : InsertionScheduleTree} {depth : ℕ} {c d : ℝ}
    (hcontract : SiblingLeafContract tree contracted c d) :
    ∃ parentDepth : ℕ, ∃ oldPre oldSuffix : List (ℕ × ℝ),
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          oldSuffix ∧
        leafDepthWeights depth contracted =
          oldPre ++ [(parentDepth, c + d)] ++ oldSuffix ∧
          ∀ {rest : List (ℕ × ℝ)} {a b : ℝ} {shallow₁ shallow₂ : ℕ},
            (leafDepthWeights depth tree).Perm
              ((shallow₁, a) :: (shallow₂, b) :: rest) →
            a ≤ b →
            (∀ pair ∈ rest, b ≤ pair.2) →
            shallow₁ ≤ parentDepth + 1 →
            shallow₂ ≤ parentDepth + 1 →
            ∃ swappedTree swappedContracted : InsertionScheduleTree,
              (SiblingLeafContract swappedTree swappedContracted a b ∨
                SiblingLeafContract swappedTree swappedContracted b a) ∧
                weightedLeafDepthCost depth swappedTree ≤
                  weightedLeafDepthCost depth tree ∧
                  swappedTree.leaves.Perm tree.leaves := by
  obtain ⟨parentDepth, oldPre, oldSuffix, htreeDepth,
    hcontractedDepth, hbridge⟩ :=
    exists_relabelLeaves_contract_for_two_smallest_deepest_exchange_branch_of_context_lengths
      hcontract
  refine ⟨parentDepth, oldPre, oldSuffix, htreeDepth, hcontractedDepth, ?_⟩
  intro rest a b shallow₁ shallow₂ htwoSmallest hab hrest hdepth₁ hdepth₂
  refine
    exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_of_occurrence_classifiers
      htreeDepth ?_ ?_ ?_ ?_ htwoSmallest hab hrest hdepth₁ hdepth₂
  · exact
      exists_relabelLeaves_contract_for_first_before_contracted_pair_anywhere_of_context
        (tree := tree) (depth := depth) (parentDepth := parentDepth)
        (oldPre := oldPre) (oldSuffix := oldSuffix) (c := c) (d := d)
        htreeDepth hbridge
  · exact
      exists_relabelLeaves_contract_for_first_after_contracted_pair_anywhere_of_context
        (tree := tree) (depth := depth) (parentDepth := parentDepth)
        (oldPre := oldPre) (oldSuffix := oldSuffix) (c := c) (d := d)
        htreeDepth hbridge
  · exact
      exists_relabelLeaves_contract_for_left_deepest_first_two_smallest_anywhere_of_context
        (tree := tree) (contracted := contracted) (depth := depth)
        (parentDepth := parentDepth) (oldPre := oldPre)
        (oldSuffix := oldSuffix) (a := c) (c := d)
        hcontract htreeDepth hbridge
  · exact
      exists_relabelLeaves_contract_for_right_deepest_first_two_smallest_anywhere_of_context
        (tree := tree) (contracted := contracted) (depth := depth)
        (parentDepth := parentDepth) (oldPre := oldPre)
        (oldSuffix := oldSuffix) (a := d) (c := c)
        hcontract htreeDepth hbridge

/-- Explicit-context form of the normalized two-smallest/deepest contraction.
When the deepest sibling context and same-length branch bridge are already
fixed, this theorem composes the four occurrence continuations without
reopening the contraction-context existential. -/
theorem
    exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_of_context
    {tree contracted : InsertionScheduleTree} {depth parentDepth : ℕ}
    {oldPre oldSuffix rest : List (ℕ × ℝ)}
    {a b c d : ℝ} {shallow₁ shallow₂ : ℕ}
    (hcontract : SiblingLeafContract tree contracted c d)
    (htreeDepth :
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          oldSuffix)
    (hbridge :
      ∀ {swappedPairs newPre newSuffix : List (ℕ × ℝ)} {a b : ℝ},
        TwoSmallestDeepestExchangeBranch
          (leafDepthWeights depth tree) swappedPairs →
        swappedPairs.map Prod.fst =
          (leafDepthWeights depth tree).map Prod.fst →
        swappedPairs =
          newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            newSuffix →
        newPre.length = oldPre.length →
        newSuffix.length = oldSuffix.length →
        ∃ swappedTree swappedContracted : InsertionScheduleTree,
          SiblingLeafContract swappedTree swappedContracted a b ∧
            weightedLeafDepthCost depth swappedTree ≤
              weightedLeafDepthCost depth tree ∧
              swappedTree.leaves.Perm tree.leaves ∧
                leafDepthWeights depth swappedTree = swappedPairs)
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((shallow₁, a) :: (shallow₂, b) :: rest))
    (hab : a ≤ b)
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth₁ : shallow₁ ≤ parentDepth + 1)
    (hdepth₂ : shallow₂ ≤ parentDepth + 1) :
    ∃ swappedTree swappedContracted : InsertionScheduleTree,
      (SiblingLeafContract swappedTree swappedContracted a b ∨
        SiblingLeafContract swappedTree swappedContracted b a) ∧
        weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
          swappedTree.leaves.Perm tree.leaves := by
  refine
    exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_of_occurrence_classifiers
      htreeDepth ?_ ?_ ?_ ?_ htwoSmallest hab hrest hdepth₁ hdepth₂
  · exact
      exists_relabelLeaves_contract_for_first_before_contracted_pair_anywhere_of_context
        (tree := tree) (depth := depth) (parentDepth := parentDepth)
        (oldPre := oldPre) (oldSuffix := oldSuffix) (c := c) (d := d)
        htreeDepth hbridge
  · exact
      exists_relabelLeaves_contract_for_first_after_contracted_pair_anywhere_of_context
        (tree := tree) (depth := depth) (parentDepth := parentDepth)
        (oldPre := oldPre) (oldSuffix := oldSuffix) (c := c) (d := d)
        htreeDepth hbridge
  · exact
      exists_relabelLeaves_contract_for_left_deepest_first_two_smallest_anywhere_of_context
        (tree := tree) (contracted := contracted) (depth := depth)
        (parentDepth := parentDepth) (oldPre := oldPre)
        (oldSuffix := oldSuffix) (a := c) (c := d)
        hcontract htreeDepth hbridge
  · exact
      exists_relabelLeaves_contract_for_right_deepest_first_two_smallest_anywhere_of_context
        (tree := tree) (contracted := contracted) (depth := depth)
        (parentDepth := parentDepth) (oldPre := oldPre)
        (oldSuffix := oldSuffix) (a := d) (c := c)
        hcontract htreeDepth hbridge

/-- Leaf-multiset and cost-split form of the shared-context contraction
normalization.  Besides the normalized sibling contraction and cost
monotonicity, this packages the two facts needed by the Huffman induction:
the normalized tree cost splits across the selected two-smallest contraction,
and the contracted companion has exactly the merged selected weight plus the
remaining original selected-weight context. -/
theorem
    exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_with_contracted_perm
    {tree contracted : InsertionScheduleTree} {depth : ℕ} {c d : ℝ}
    (hcontract : SiblingLeafContract tree contracted c d) :
    ∃ parentDepth : ℕ, ∃ oldPre oldSuffix : List (ℕ × ℝ),
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          oldSuffix ∧
        leafDepthWeights depth contracted =
          oldPre ++ [(parentDepth, c + d)] ++ oldSuffix ∧
          ∀ {rest : List (ℕ × ℝ)} {a b : ℝ} {shallow₁ shallow₂ : ℕ},
            (leafDepthWeights depth tree).Perm
              ((shallow₁, a) :: (shallow₂, b) :: rest) →
            a ≤ b →
            (∀ pair ∈ rest, b ≤ pair.2) →
            shallow₁ ≤ parentDepth + 1 →
            shallow₂ ≤ parentDepth + 1 →
            ∃ swappedTree swappedContracted : InsertionScheduleTree,
              (SiblingLeafContract swappedTree swappedContracted a b ∨
                SiblingLeafContract swappedTree swappedContracted b a) ∧
                weightedLeafDepthCost depth swappedTree ≤
                  weightedLeafDepthCost depth tree ∧
                  swappedTree.leaves.Perm tree.leaves ∧
                    weightedLeafDepthCost depth swappedTree =
                      weightedLeafDepthCost depth swappedContracted +
                        (a + b) ∧
                      swappedContracted.leaves.Perm
                        ((a + b) :: rest.map Prod.snd) := by
  obtain ⟨parentDepth, oldPre, oldSuffix, htreeDepth,
      hcontractedDepth, hnormalize⟩ :=
    exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere
      hcontract
  refine ⟨parentDepth, oldPre, oldSuffix, htreeDepth, hcontractedDepth, ?_⟩
  intro rest a b shallow₁ shallow₂ htwoSmallest hab hrest hdepth₁ hdepth₂
  obtain ⟨swappedTree, swappedContracted, horient, hcostLe,
      hleavesPerm⟩ :=
    hnormalize htwoSmallest hab hrest hdepth₁ hdepth₂
  have htreeWeights :
      tree.leaves.Perm (a :: b :: rest.map Prod.snd) := by
    have hweights := htwoSmallest.map Prod.snd
    simpa [leafDepthWeights_weights_eq_leaves, List.map_map,
      Function.comp_def] using hweights
  have hswappedWeights :
      swappedTree.leaves.Perm (a :: b :: rest.map Prod.snd) :=
    hleavesPerm.trans htreeWeights
  rcases horient with hcontractedNorm | hcontractedNorm
  · have hcostEq :=
      SiblingLeafContract.weightedLeafDepthCost_eq depth hcontractedNorm
    have hcontractedPerm :=
      SiblingLeafContract.contracted_perm_of_leaves_perm hcontractedNorm
        hswappedWeights
    exact ⟨swappedTree, swappedContracted, Or.inl hcontractedNorm,
      hcostLe, hleavesPerm, hcostEq, hcontractedPerm⟩
  · have hswappedWeights' :
        swappedTree.leaves.Perm (b :: a :: rest.map Prod.snd) :=
      hswappedWeights.trans
        (List.Perm.swap a b (rest.map Prod.snd)).symm
    have hcostEqRaw :=
      SiblingLeafContract.weightedLeafDepthCost_eq depth hcontractedNorm
    have hcostEq :
        weightedLeafDepthCost depth swappedTree =
          weightedLeafDepthCost depth swappedContracted + (a + b) := by
      rw [hcostEqRaw]
      ring
    have hcontractedPermRaw :=
      SiblingLeafContract.contracted_perm_of_leaves_perm hcontractedNorm
        hswappedWeights'
    have hcontractedPerm :
        swappedContracted.leaves.Perm ((a + b) :: rest.map Prod.snd) := by
      simpa [add_comm] using hcontractedPermRaw
    exact ⟨swappedTree, swappedContracted, Or.inr hcontractedNorm,
      hcostLe, hleavesPerm, hcostEq, hcontractedPerm⟩

/-- Induction-data form of the shared-context contraction normalization.  For
nonnegative input leaves, the normalized contracted companion remains
nonnegative and has strictly fewer leaves than the original tree, while
retaining the selected-merge cost split and contracted leaf multiset. -/
theorem
    exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_with_induction_data
    {tree contracted : InsertionScheduleTree} {depth : ℕ} {c d : ℝ}
    (hcontract : SiblingLeafContract tree contracted c d)
    (hnonneg : ∀ x ∈ tree.leaves, 0 ≤ x) :
    ∃ parentDepth : ℕ, ∃ oldPre oldSuffix : List (ℕ × ℝ),
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          oldSuffix ∧
        leafDepthWeights depth contracted =
          oldPre ++ [(parentDepth, c + d)] ++ oldSuffix ∧
          ∀ {rest : List (ℕ × ℝ)} {a b : ℝ} {shallow₁ shallow₂ : ℕ},
            (leafDepthWeights depth tree).Perm
              ((shallow₁, a) :: (shallow₂, b) :: rest) →
            a ≤ b →
            (∀ pair ∈ rest, b ≤ pair.2) →
            shallow₁ ≤ parentDepth + 1 →
            shallow₂ ≤ parentDepth + 1 →
            ∃ swappedTree swappedContracted : InsertionScheduleTree,
              (SiblingLeafContract swappedTree swappedContracted a b ∨
                SiblingLeafContract swappedTree swappedContracted b a) ∧
                weightedLeafDepthCost depth swappedTree ≤
                  weightedLeafDepthCost depth tree ∧
                  swappedTree.leaves.Perm tree.leaves ∧
                    weightedLeafDepthCost depth swappedTree =
                      weightedLeafDepthCost depth swappedContracted +
                        (a + b) ∧
                      swappedContracted.leaves.Perm
                        ((a + b) :: rest.map Prod.snd) ∧
                        (∀ x ∈ swappedContracted.leaves, 0 ≤ x) ∧
                          swappedContracted.leafCount < tree.leafCount := by
  obtain ⟨parentDepth, oldPre, oldSuffix, htreeDepth,
      hcontractedDepth, hnormalize⟩ :=
    exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_with_contracted_perm
      hcontract
  refine ⟨parentDepth, oldPre, oldSuffix, htreeDepth, hcontractedDepth, ?_⟩
  intro rest a b shallow₁ shallow₂ htwoSmallest hab hrest hdepth₁ hdepth₂
  obtain ⟨swappedTree, swappedContracted, horient, hcostLe, hleavesPerm,
      hcostEq, hcontractedPerm⟩ :=
    hnormalize htwoSmallest hab hrest hdepth₁ hdepth₂
  have hswappedNonneg : ∀ x ∈ swappedTree.leaves, 0 ≤ x := by
    intro x hx
    exact hnonneg x ((hleavesPerm.mem_iff).1 hx)
  have hcountEq : swappedTree.leafCount = tree.leafCount := by
    have hlen := hleavesPerm.length_eq
    rw [← leaves_length swappedTree, ← leaves_length tree]
    exact hlen
  rcases horient with hcontractedNorm | hcontractedNorm
  · have hcontractedNonneg :
        ∀ x ∈ swappedContracted.leaves, 0 ≤ x :=
      SiblingLeafContract.contracted_leaves_nonnegative hcontractedNorm
        hswappedNonneg
    have hcountLtRaw :=
      SiblingLeafContract.contracted_leafCount_lt hcontractedNorm
    have hcountLt : swappedContracted.leafCount < tree.leafCount := by
      rw [← hcountEq]
      exact hcountLtRaw
    exact ⟨swappedTree, swappedContracted, Or.inl hcontractedNorm,
      hcostLe, hleavesPerm, hcostEq, hcontractedPerm,
      hcontractedNonneg, hcountLt⟩
  · have hcontractedNonneg :
        ∀ x ∈ swappedContracted.leaves, 0 ≤ x :=
      SiblingLeafContract.contracted_leaves_nonnegative hcontractedNorm
        hswappedNonneg
    have hcountLtRaw :=
      SiblingLeafContract.contracted_leafCount_lt hcontractedNorm
    have hcountLt : swappedContracted.leafCount < tree.leafCount := by
      rw [← hcountEq]
      exact hcountLtRaw
    exact ⟨swappedTree, swappedContracted, Or.inr hcontractedNorm,
      hcostLe, hleavesPerm, hcostEq, hcontractedPerm,
      hcontractedNonneg, hcountLt⟩

/-- Explicit-context leaf-multiset and cost-split form of the normalized
two-smallest/deepest contraction.  This is the same packaging as
`exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_with_contracted_perm`,
but it consumes an already-fixed deepest sibling context and branch bridge. -/
theorem
    exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_of_context_with_contracted_perm
    {tree contracted : InsertionScheduleTree} {depth parentDepth : ℕ}
    {oldPre oldSuffix rest : List (ℕ × ℝ)}
    {a b c d : ℝ} {shallow₁ shallow₂ : ℕ}
    (hcontract : SiblingLeafContract tree contracted c d)
    (htreeDepth :
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          oldSuffix)
    (hbridge :
      ∀ {swappedPairs newPre newSuffix : List (ℕ × ℝ)} {a b : ℝ},
        TwoSmallestDeepestExchangeBranch
          (leafDepthWeights depth tree) swappedPairs →
        swappedPairs.map Prod.fst =
          (leafDepthWeights depth tree).map Prod.fst →
        swappedPairs =
          newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            newSuffix →
        newPre.length = oldPre.length →
        newSuffix.length = oldSuffix.length →
        ∃ swappedTree swappedContracted : InsertionScheduleTree,
          SiblingLeafContract swappedTree swappedContracted a b ∧
            weightedLeafDepthCost depth swappedTree ≤
              weightedLeafDepthCost depth tree ∧
              swappedTree.leaves.Perm tree.leaves ∧
                leafDepthWeights depth swappedTree = swappedPairs)
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((shallow₁, a) :: (shallow₂, b) :: rest))
    (hab : a ≤ b)
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth₁ : shallow₁ ≤ parentDepth + 1)
    (hdepth₂ : shallow₂ ≤ parentDepth + 1) :
    ∃ swappedTree swappedContracted : InsertionScheduleTree,
      (SiblingLeafContract swappedTree swappedContracted a b ∨
        SiblingLeafContract swappedTree swappedContracted b a) ∧
        weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
          swappedTree.leaves.Perm tree.leaves ∧
            weightedLeafDepthCost depth swappedTree =
              weightedLeafDepthCost depth swappedContracted +
                (a + b) ∧
              swappedContracted.leaves.Perm
                ((a + b) :: rest.map Prod.snd) := by
  obtain ⟨swappedTree, swappedContracted, horient, hcostLe,
      hleavesPerm⟩ :=
    exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_of_context
      hcontract htreeDepth hbridge htwoSmallest hab hrest hdepth₁ hdepth₂
  have htreeWeights :
      tree.leaves.Perm (a :: b :: rest.map Prod.snd) := by
    have hweights := htwoSmallest.map Prod.snd
    simpa [leafDepthWeights_weights_eq_leaves, List.map_map,
      Function.comp_def] using hweights
  have hswappedWeights :
      swappedTree.leaves.Perm (a :: b :: rest.map Prod.snd) :=
    hleavesPerm.trans htreeWeights
  rcases horient with hcontractedNorm | hcontractedNorm
  · have hcostEq :=
      SiblingLeafContract.weightedLeafDepthCost_eq depth hcontractedNorm
    have hcontractedPerm :=
      SiblingLeafContract.contracted_perm_of_leaves_perm hcontractedNorm
        hswappedWeights
    exact ⟨swappedTree, swappedContracted, Or.inl hcontractedNorm,
      hcostLe, hleavesPerm, hcostEq, hcontractedPerm⟩
  · have hswappedWeights' :
        swappedTree.leaves.Perm (b :: a :: rest.map Prod.snd) :=
      hswappedWeights.trans
        (List.Perm.swap a b (rest.map Prod.snd)).symm
    have hcostEqRaw :=
      SiblingLeafContract.weightedLeafDepthCost_eq depth hcontractedNorm
    have hcostEq :
        weightedLeafDepthCost depth swappedTree =
          weightedLeafDepthCost depth swappedContracted + (a + b) := by
      rw [hcostEqRaw]
      ring
    have hcontractedPermRaw :=
      SiblingLeafContract.contracted_perm_of_leaves_perm hcontractedNorm
        hswappedWeights'
    have hcontractedPerm :
        swappedContracted.leaves.Perm ((a + b) :: rest.map Prod.snd) := by
      simpa [add_comm] using hcontractedPermRaw
    exact ⟨swappedTree, swappedContracted, Or.inr hcontractedNorm,
      hcostLe, hleavesPerm, hcostEq, hcontractedPerm⟩

/-- Explicit-context induction-data form of the normalized
two-smallest/deepest contraction.  The fixed context and branch bridge are
threaded through unchanged, while the returned contracted companion carries
the selected-merge multiset, nonnegativity, cost split, and strict leaf-count
decrease needed by the Huffman induction. -/
theorem
    exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_of_context_with_induction_data
    {tree contracted : InsertionScheduleTree} {depth parentDepth : ℕ}
    {oldPre oldSuffix rest : List (ℕ × ℝ)}
    {a b c d : ℝ} {shallow₁ shallow₂ : ℕ}
    (hcontract : SiblingLeafContract tree contracted c d)
    (htreeDepth :
      leafDepthWeights depth tree =
        oldPre ++ [(parentDepth + 1, c), (parentDepth + 1, d)] ++
          oldSuffix)
    (hbridge :
      ∀ {swappedPairs newPre newSuffix : List (ℕ × ℝ)} {a b : ℝ},
        TwoSmallestDeepestExchangeBranch
          (leafDepthWeights depth tree) swappedPairs →
        swappedPairs.map Prod.fst =
          (leafDepthWeights depth tree).map Prod.fst →
        swappedPairs =
          newPre ++ [(parentDepth + 1, a), (parentDepth + 1, b)] ++
            newSuffix →
        newPre.length = oldPre.length →
        newSuffix.length = oldSuffix.length →
        ∃ swappedTree swappedContracted : InsertionScheduleTree,
          SiblingLeafContract swappedTree swappedContracted a b ∧
            weightedLeafDepthCost depth swappedTree ≤
              weightedLeafDepthCost depth tree ∧
              swappedTree.leaves.Perm tree.leaves ∧
                leafDepthWeights depth swappedTree = swappedPairs)
    (hnonneg : ∀ x ∈ tree.leaves, 0 ≤ x)
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((shallow₁, a) :: (shallow₂, b) :: rest))
    (hab : a ≤ b)
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth₁ : shallow₁ ≤ parentDepth + 1)
    (hdepth₂ : shallow₂ ≤ parentDepth + 1) :
    ∃ swappedTree swappedContracted : InsertionScheduleTree,
      (SiblingLeafContract swappedTree swappedContracted a b ∨
        SiblingLeafContract swappedTree swappedContracted b a) ∧
        weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
          swappedTree.leaves.Perm tree.leaves ∧
            weightedLeafDepthCost depth swappedTree =
              weightedLeafDepthCost depth swappedContracted +
                (a + b) ∧
              swappedContracted.leaves.Perm
                ((a + b) :: rest.map Prod.snd) ∧
                (∀ x ∈ swappedContracted.leaves, 0 ≤ x) ∧
                  swappedContracted.leafCount < tree.leafCount := by
  obtain ⟨swappedTree, swappedContracted, horient, hcostLe, hleavesPerm,
      hcostEq, hcontractedPerm⟩ :=
    exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_of_context_with_contracted_perm
      hcontract htreeDepth hbridge htwoSmallest hab hrest hdepth₁ hdepth₂
  have hswappedNonneg : ∀ x ∈ swappedTree.leaves, 0 ≤ x := by
    intro x hx
    exact hnonneg x ((hleavesPerm.mem_iff).1 hx)
  have hcountEq : swappedTree.leafCount = tree.leafCount := by
    have hlen := hleavesPerm.length_eq
    rw [← leaves_length swappedTree, ← leaves_length tree]
    exact hlen
  rcases horient with hcontractedNorm | hcontractedNorm
  · have hcontractedNonneg :
        ∀ x ∈ swappedContracted.leaves, 0 ≤ x :=
      SiblingLeafContract.contracted_leaves_nonnegative hcontractedNorm
        hswappedNonneg
    have hcountLtRaw :=
      SiblingLeafContract.contracted_leafCount_lt hcontractedNorm
    have hcountLt : swappedContracted.leafCount < tree.leafCount := by
      rw [← hcountEq]
      exact hcountLtRaw
    exact ⟨swappedTree, swappedContracted, Or.inl hcontractedNorm,
      hcostLe, hleavesPerm, hcostEq, hcontractedPerm,
      hcontractedNonneg, hcountLt⟩
  · have hcontractedNonneg :
        ∀ x ∈ swappedContracted.leaves, 0 ≤ x :=
      SiblingLeafContract.contracted_leaves_nonnegative hcontractedNorm
        hswappedNonneg
    have hcountLtRaw :=
      SiblingLeafContract.contracted_leafCount_lt hcontractedNorm
    have hcountLt : swappedContracted.leafCount < tree.leafCount := by
      rw [← hcountEq]
      exact hcountLtRaw
    exact ⟨swappedTree, swappedContracted, Or.inr hcontractedNorm,
      hcostLe, hleavesPerm, hcostEq, hcontractedPerm,
      hcontractedNonneg, hcountLt⟩

/-- Tree-level induction-data form of the deepest two-smallest contraction
normalization.  For any non-leaf tree and any displayed two-smallest
decomposition of its leaf-depth list, the theorem internally chooses a deepest
sibling pair, moves the two selected weights into that pair without increasing
weighted external path length, and returns the contracted induction instance. -/
theorem
    exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_with_induction_data_of_tree
    {tree : InsertionScheduleTree} {depth : ℕ}
    (hcount : 1 < tree.leafCount)
    (hnonneg : ∀ x ∈ tree.leaves, 0 ≤ x)
    {rest : List (ℕ × ℝ)} {a b : ℝ} {shallow₁ shallow₂ : ℕ}
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((shallow₁, a) :: (shallow₂, b) :: rest))
    (hab : a ≤ b)
    (hrest : ∀ pair ∈ rest, b ≤ pair.2) :
    ∃ swappedTree swappedContracted : InsertionScheduleTree,
      (SiblingLeafContract swappedTree swappedContracted a b ∨
        SiblingLeafContract swappedTree swappedContracted b a) ∧
        weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
          swappedTree.leaves.Perm tree.leaves ∧
            weightedLeafDepthCost depth swappedTree =
              weightedLeafDepthCost depth swappedContracted +
                (a + b) ∧
              swappedContracted.leaves.Perm
                ((a + b) :: rest.map Prod.snd) ∧
                (∀ x ∈ swappedContracted.leaves, 0 ≤ x) ∧
                  swappedContracted.leafCount < tree.leafCount := by
  obtain ⟨contractedTree, parentDepth, oldPre, oldSuffix, c, d,
      hcontract, htreeDepth, _hcontractedDepth, hparent, _hcost,
      _hcountEq, hbridge⟩ :=
    exists_deepest_sibling_leaf_contract_with_branch_bridge
      depth tree hcount
  obtain ⟨hdepth₁, hdepth₂⟩ :=
    two_smallest_depths_le_deepest_parent_context
      (tree := tree) (depth := depth) (parentDepth := parentDepth)
      (rest := rest) (a := a) (b := b) (shallow₁ := shallow₁)
      (shallow₂ := shallow₂) hparent htwoSmallest
  exact
    exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_of_context_with_induction_data
      (tree := tree) (contracted := contractedTree) (depth := depth)
      (parentDepth := parentDepth) (oldPre := oldPre)
      (oldSuffix := oldSuffix) (rest := rest) (a := a) (b := b)
      (c := c) (d := d) (shallow₁ := shallow₁)
      (shallow₂ := shallow₂) hcontract htreeDepth hbridge hnonneg
      htwoSmallest hab hrest hdepth₁ hdepth₂

/-- Greedy insertion/Huffman schedule trees: at each internal expansion, the
two sibling leaves are the two smallest active weights before they are merged
into their parent weight. -/
inductive GreedyInsertionTree : InsertionScheduleTree → Prop
  | leaf (x : ℝ) : GreedyInsertionTree (leaf x)
  | merge {tree contracted : InsertionScheduleTree} {a b : ℝ}
      {rest : List ℝ}
      (hcontract : SiblingLeafContract tree contracted a b)
      (hcontractedLeaves : contracted.leaves.Perm ((a + b) :: rest))
      (hab : a ≤ b)
      (hrest : ∀ x ∈ rest, b ≤ x)
      (hgreedyContracted : GreedyInsertionTree contracted) :
      GreedyInsertionTree tree

/-- Huffman-style induction for the weighted external path objective.  For
every nonnegative schedule tree, there exists a greedy insertion tree with the
same leaf multiset and no larger weighted external path length at any starting
depth. -/
theorem exists_greedyInsertionTree_weightedLeafDepthCost_le
    (depth : ℕ) (tree : InsertionScheduleTree)
    (hnonneg : ∀ x ∈ tree.leaves, 0 ≤ x) :
    ∃ greedyTree : InsertionScheduleTree,
      GreedyInsertionTree greedyTree ∧
        greedyTree.leaves.Perm tree.leaves ∧
          weightedLeafDepthCost depth greedyTree ≤
            weightedLeafDepthCost depth tree := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (depth : ℕ) (tree : InsertionScheduleTree),
      tree.leafCount = n →
      (∀ x ∈ tree.leaves, 0 ≤ x) →
      ∃ greedyTree : InsertionScheduleTree,
        GreedyInsertionTree greedyTree ∧
          greedyTree.leaves.Perm tree.leaves ∧
            weightedLeafDepthCost depth greedyTree ≤
              weightedLeafDepthCost depth tree
  have hstep : ∀ n, (∀ m, m < n → P m) → P n := by
    intro n ih depth tree hcountEq hnonneg
    cases tree with
    | leaf x =>
        exact ⟨leaf x, GreedyInsertionTree.leaf x,
          List.Perm.refl (leaf x).leaves, le_rfl⟩
    | node left right =>
        have hcountNontrivial : 1 < (node left right).leafCount :=
          one_lt_leafCount_node left right
        have hlen : 2 ≤ (leafDepthWeights depth (node left right)).length := by
          rw [leafDepthWeights_length]
          exact hcountNontrivial
        obtain ⟨depth₁, a, depth₂, b, rest, htwoSmallest, hab,
            hrest⟩ :=
          exists_two_smallest_weight_decomposition_components
            (leafDepthWeights depth (node left right)) hlen
        obtain ⟨swappedTree, swappedContracted, _horient, hcostLe,
            _hleavesPerm, hcostEq, hcontractedPerm, hcontractedNonneg,
            hcountLt⟩ :=
          exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_with_induction_data_of_tree
            (tree := node left right) (depth := depth)
            hcountNontrivial hnonneg htwoSmallest hab hrest
        have hcountLtN : swappedContracted.leafCount < n := by
          rw [← hcountEq]
          exact hcountLt
        obtain ⟨greedyContracted, hgreedyContracted,
            hgreedyContractedLeaves, hgreedyContractedCost⟩ :=
          ih swappedContracted.leafCount hcountLtN depth swappedContracted
            rfl hcontractedNonneg
        have hmergedPerm :
            greedyContracted.leaves.Perm
              ((a + b) :: rest.map Prod.snd) :=
          hgreedyContractedLeaves.trans hcontractedPerm
        have hmergedMem : a + b ∈ greedyContracted.leaves :=
          (hmergedPerm.mem_iff).2 (by simp)
        obtain ⟨greedyTree, hgreedyContract⟩ :=
          SiblingLeafContract.exists_expansion_of_mem
            greedyContracted hmergedMem
        have hgreedyLeavesAB :
            greedyTree.leaves.Perm (a :: b :: rest.map Prod.snd) :=
          SiblingLeafContract.leaves_perm_of_contracted_perm
            hgreedyContract hmergedPerm
        have htreeLeavesAB :
            (node left right).leaves.Perm (a :: b :: rest.map Prod.snd) := by
          have hweights := htwoSmallest.map Prod.snd
          simpa [leafDepthWeights_weights_eq_leaves, List.map_map,
            Function.comp_def] using hweights
        have hgreedyLeaves :
            greedyTree.leaves.Perm (node left right).leaves :=
          hgreedyLeavesAB.trans htreeLeavesAB.symm
        have hgreedyCostToContracted :
            weightedLeafDepthCost depth greedyTree ≤
              weightedLeafDepthCost depth swappedContracted + (a + b) := by
          rw [SiblingLeafContract.weightedLeafDepthCost_eq
            depth hgreedyContract]
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hgreedyContractedCost (a + b)
        have hgreedyCostToSwapped :
            weightedLeafDepthCost depth greedyTree ≤
              weightedLeafDepthCost depth swappedTree := by
          rw [hcostEq]
          exact hgreedyCostToContracted
        have hrestWeights : ∀ x ∈ rest.map Prod.snd, b ≤ x := by
          intro x hx
          rcases List.mem_map.mp hx with ⟨pair, hpair, rfl⟩
          exact hrest pair hpair
        have hgreedy : GreedyInsertionTree greedyTree :=
          GreedyInsertionTree.merge hgreedyContract hmergedPerm hab
            hrestWeights hgreedyContracted
        exact ⟨greedyTree, hgreedy, hgreedyLeaves,
          le_trans hgreedyCostToSwapped hcostLe⟩
  have hmain : P tree.leafCount :=
    Nat.strong_induction_on tree.leafCount hstep
  exact hmain depth tree rfl hnonneg

/-- Supplied-greedy form of the Huffman optimality theorem for weighted
external path length.  Any `GreedyInsertionTree` is no more expensive than any
other schedule with the same nonnegative leaf multiset. -/
theorem GreedyInsertionTree.weightedLeafDepthCost_le
    {greedy other : InsertionScheduleTree}
    (hgreedy : GreedyInsertionTree greedy)
    (depth : ℕ)
    (hperm : greedy.leaves.Perm other.leaves)
    (hnonneg : ∀ x ∈ greedy.leaves, 0 ≤ x) :
    weightedLeafDepthCost depth greedy ≤ weightedLeafDepthCost depth other := by
  induction hgreedy generalizing other depth with
  | leaf x =>
      have hotherLen : other.leafCount = 1 := by
        have hlen := hperm.length_eq
        rw [leaves_length, leaves_length] at hlen
        simpa [leafCount] using hlen.symm
      cases other with
      | leaf y =>
          have hyx : y = x := by
            have hy_mem : y ∈ [x] := (hperm.symm.mem_iff).1 (by simp [leaves])
            simpa using hy_mem
          subst y
          simp [weightedLeafDepthCost]
      | node left right =>
          have htwo : 1 < (node left right).leafCount :=
            one_lt_leafCount_node left right
          omega
  | merge hcontract hcontractedLeaves hab hrest hgreedyContracted ih =>
      rename_i tree contracted a b rest
      have htreeLeavesAB : tree.leaves.Perm (a :: b :: rest) :=
        SiblingLeafContract.leaves_perm_of_contracted_perm
          hcontract hcontractedLeaves
      have hotherLeavesAB : other.leaves.Perm (a :: b :: rest) :=
        hperm.symm.trans htreeLeavesAB
      have hotherNonneg : ∀ x ∈ other.leaves, 0 ≤ x := by
        intro x hx
        exact hnonneg x ((hperm.mem_iff).2 hx)
      have hcountTree : 1 < tree.leafCount := by
        rw [SiblingLeafContract.leafCount_eq_succ hcontract]
        exact Nat.succ_lt_succ (leafCount_pos contracted)
      have hcountOther : 1 < other.leafCount := by
        have hlen := hperm.length_eq
        rw [leaves_length, leaves_length] at hlen
        rw [← hlen]
        exact hcountTree
      have hweights :
          ((leafDepthWeights depth other).map Prod.snd).Perm
            (a :: b :: rest) := by
        simpa [leafDepthWeights_weights_eq_leaves] using hotherLeavesAB
      obtain ⟨depth₁, depth₂, restPairs, htwoSmallest,
          hrestPairsWeights⟩ :=
        exists_pair_decomposition_of_weights_perm_cons_cons
          (pairs := leafDepthWeights depth other) hweights
      have hrestPairs : ∀ pair ∈ restPairs, b ≤ pair.2 := by
        intro pair hpair
        exact hrest pair.2
          ((hrestPairsWeights.mem_iff).1
            (by
              exact List.mem_map.mpr ⟨pair, hpair, rfl⟩))
      obtain ⟨swappedTree, swappedContracted, _horient, hcostLe,
          _hleavesPerm, hcostEq, hcontractedPerm, _hcontractedNonneg,
          _hcountLt⟩ :=
        exists_relabelLeaves_contract_for_two_smallest_deepest_pair_anywhere_with_induction_data_of_tree
          (tree := other) (depth := depth) hcountOther hotherNonneg
          (rest := restPairs) (a := a) (b := b)
          (shallow₁ := depth₁) (shallow₂ := depth₂)
          htwoSmallest hab hrestPairs
      have hcontractedToSwapped :
          contracted.leaves.Perm swappedContracted.leaves :=
        hcontractedLeaves.trans
          ((List.Perm.cons (a + b) hrestPairsWeights.symm).trans
            hcontractedPerm.symm)
      have hcontractedNonneg : ∀ x ∈ contracted.leaves, 0 ≤ x :=
        SiblingLeafContract.contracted_leaves_nonnegative hcontract hnonneg
      have hcontractedCost :
          weightedLeafDepthCost depth contracted ≤
            weightedLeafDepthCost depth swappedContracted :=
        ih depth hcontractedToSwapped hcontractedNonneg
      have htreeCostToSwapped :
          weightedLeafDepthCost depth tree ≤
            weightedLeafDepthCost depth swappedTree := by
        rw [SiblingLeafContract.weightedLeafDepthCost_eq depth hcontract,
          hcostEq]
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hcontractedCost (a + b)
      exact le_trans htreeCostToSwapped hcostLe

/-- No-op same-shape assembly for the already-arranged deepest sibling branch:
if the target deepest pair is already in the tree's explicit leaf-depth list,
  the original tree itself realizes that branch with no cost increase. -/
theorem exists_tree_for_deepest_pair_noop_eq
    {tree : InsertionScheduleTree} {depth : ℕ}
    (pre suffix : List (ℕ × ℝ)) {a b : ℝ} {deep : ℕ}
    (hpairs :
      leafDepthWeights depth tree =
        pre ++ [(deep, a), (deep, b)] ++ suffix) :
    ∃ swappedTree : InsertionScheduleTree,
      weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
        swappedTree.leaves.Perm tree.leaves ∧
          leafDepthWeights depth swappedTree =
            pre ++ [(deep, a), (deep, b)] ++ suffix := by
  exact ⟨tree, le_rfl, List.Perm.refl tree.leaves, hpairs⟩

/-- Nonoverlap same-shape assembly for the two-smallest/deepest dispatcher:
if the original tree's explicit leaf-depth list is displayed with a deepest
sibling pair and two separated selected smallest slots, then relabeling realizes
the depth-preserving exchanged list as an actual schedule tree. -/
theorem exists_tree_for_two_pair_exchange_of_two_smallest_decomposition_eq
    {tree : InsertionScheduleTree} {depth : ℕ}
    (pre middle₁ middle₂ suffix rest : List (ℕ × ℝ))
    {a b c d : ℝ} {deep shallow₁ shallow₂ : ℕ}
    (hpairs :
      leafDepthWeights depth tree =
        pre ++ [(deep, c), (deep, d)] ++ middle₁ ++
          [(shallow₁, a)] ++ middle₂ ++ [(shallow₂, b)] ++ suffix)
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((shallow₁, a) :: (shallow₂, b) :: rest))
    (hab : a ≤ b)
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth₁ : shallow₁ ≤ deep) (hdepth₂ : shallow₂ ≤ deep) :
    ∃ swappedTree : InsertionScheduleTree,
      weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
        swappedTree.leaves.Perm tree.leaves ∧
          leafDepthWeights depth swappedTree =
            pre ++ [(deep, a), (deep, b)] ++ middle₁ ++
              [(shallow₁, c)] ++ middle₂ ++
                [(shallow₂, d)] ++ suffix := by
  let swappedPairs :=
    pre ++ [(deep, a), (deep, b)] ++ middle₁ ++
      [(shallow₁, c)] ++ middle₂ ++ [(shallow₂, d)] ++ suffix
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.nondegenerate
      pre middle₁ middle₂ suffix rest
      (by rw [hpairs]) (by rfl) htwoSmallest hab hrest hdepth₁ hdepth₂
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [hpairs]
    simp [swappedPairs, List.map_append]
  exact
    exists_relabelLeaves_for_two_smallest_deepest_exchange_branch_of_depths_eq
      hbranch hdepths

/-- Nonoverlap same-shape assembly for the reverse selected-order orientation
where the displayed deepest sibling pair appears before the `b` slot and then
the `a` slot. -/
theorem
    exists_tree_for_two_pair_exchange_reverse_of_two_smallest_decomposition_eq
    {tree : InsertionScheduleTree} {depth : ℕ}
    (pre middle₁ middle₂ suffix rest : List (ℕ × ℝ))
    {a b c d : ℝ} {deep shallow₁ shallow₂ : ℕ}
    (hpairs :
      leafDepthWeights depth tree =
        pre ++ [(deep, c), (deep, d)] ++ middle₁ ++
          [(shallow₂, b)] ++ middle₂ ++ [(shallow₁, a)] ++ suffix)
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((shallow₁, a) :: (shallow₂, b) :: rest))
    (hab : a ≤ b)
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth₁ : shallow₁ ≤ deep) (hdepth₂ : shallow₂ ≤ deep) :
    ∃ swappedTree : InsertionScheduleTree,
      weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
        swappedTree.leaves.Perm tree.leaves ∧
          leafDepthWeights depth swappedTree =
            pre ++ [(deep, a), (deep, b)] ++ middle₁ ++
              [(shallow₂, d)] ++ middle₂ ++
                [(shallow₁, c)] ++ suffix := by
  let swappedPairs :=
    pre ++ [(deep, a), (deep, b)] ++ middle₁ ++
      [(shallow₂, d)] ++ middle₂ ++ [(shallow₁, c)] ++ suffix
  have hpairsPerm :
      (leafDepthWeights depth tree).Perm
        (pre ++ [(deep, c), (deep, d)] ++ middle₁ ++
          [(shallow₁, a)] ++ middle₂ ++ [(shallow₂, b)] ++ suffix) := by
    rw [hpairs]
    exact weightListPerm_pair_exchange
      (pre ++ [(deep, c), (deep, d)] ++ middle₁) middle₂ suffix
      (shallow₂, b) (shallow₁, a)
  have hswappedPerm :
      swappedPairs.Perm
        (pre ++ [(deep, a), (deep, b)] ++ middle₁ ++
          [(shallow₁, c)] ++ middle₂ ++ [(shallow₂, d)] ++ suffix) := by
    exact weightListPerm_pair_exchange
      (pre ++ [(deep, a), (deep, b)] ++ middle₁) middle₂ suffix
      (shallow₂, d) (shallow₁, c)
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.nondegenerate
      pre middle₁ middle₂ suffix rest hpairsPerm hswappedPerm
      htwoSmallest hab hrest hdepth₁ hdepth₂
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [hpairs]
    simp [swappedPairs, List.map_append]
  exact
    exists_relabelLeaves_for_two_smallest_deepest_exchange_branch_of_depths_eq
      hbranch hdepths

/-- Nonoverlap same-shape assembly for the orientation where the two selected
smallest slots appear before the displayed deepest sibling pair. -/
theorem
    exists_tree_for_two_pair_exchange_before_deepest_of_two_smallest_decomposition_eq
    {tree : InsertionScheduleTree} {depth : ℕ}
    (pre middle₁ middle₂ suffix rest : List (ℕ × ℝ))
    {a b c d : ℝ} {deep shallow₁ shallow₂ : ℕ}
    (hpairs :
      leafDepthWeights depth tree =
        pre ++ [(shallow₁, a)] ++ middle₁ ++ [(shallow₂, b)] ++
          middle₂ ++ [(deep, c), (deep, d)] ++ suffix)
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((shallow₁, a) :: (shallow₂, b) :: rest))
    (hab : a ≤ b)
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth₁ : shallow₁ ≤ deep) (hdepth₂ : shallow₂ ≤ deep) :
    ∃ swappedTree : InsertionScheduleTree,
      weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
        swappedTree.leaves.Perm tree.leaves ∧
          leafDepthWeights depth swappedTree =
            pre ++ [(shallow₁, c)] ++ middle₁ ++ [(shallow₂, d)] ++
              middle₂ ++ [(deep, a), (deep, b)] ++ suffix := by
  let swappedPairs :=
    pre ++ [(shallow₁, c)] ++ middle₁ ++ [(shallow₂, d)] ++
      middle₂ ++ [(deep, a), (deep, b)] ++ suffix
  have hpairsPerm :
      (leafDepthWeights depth tree).Perm
        (pre ++ [(deep, c), (deep, d)] ++ middle₁ ++
          [(shallow₁, a)] ++ middle₂ ++ [(shallow₂, b)] ++ suffix) := by
    rw [hpairs]
    exact listPerm_two_selected_before_deepest_to_canonical
      pre middle₁ middle₂ suffix (deep, c) (deep, d)
      (shallow₁, a) (shallow₂, b)
  have hswappedPerm :
      swappedPairs.Perm
        (pre ++ [(deep, a), (deep, b)] ++ middle₁ ++
          [(shallow₁, c)] ++ middle₂ ++ [(shallow₂, d)] ++ suffix) := by
    exact listPerm_two_selected_before_deepest_to_canonical
      pre middle₁ middle₂ suffix (deep, a) (deep, b)
      (shallow₁, c) (shallow₂, d)
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.nondegenerate
      pre middle₁ middle₂ suffix rest hpairsPerm hswappedPerm
      htwoSmallest hab hrest hdepth₁ hdepth₂
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [hpairs]
    simp [swappedPairs, List.map_append]
  exact
    exists_relabelLeaves_for_two_smallest_deepest_exchange_branch_of_depths_eq
      hbranch hdepths

/-- Nonoverlap same-shape assembly for the reverse selected-order orientation
where the `b` slot and then the `a` slot appear before the displayed deepest
sibling pair. -/
theorem
    exists_tree_for_two_pair_exchange_reverse_before_deepest_of_two_smallest_decomposition_eq
    {tree : InsertionScheduleTree} {depth : ℕ}
    (pre middle₁ middle₂ suffix rest : List (ℕ × ℝ))
    {a b c d : ℝ} {deep shallow₁ shallow₂ : ℕ}
    (hpairs :
      leafDepthWeights depth tree =
        pre ++ [(shallow₂, b)] ++ middle₁ ++ [(shallow₁, a)] ++
          middle₂ ++ [(deep, c), (deep, d)] ++ suffix)
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((shallow₁, a) :: (shallow₂, b) :: rest))
    (hab : a ≤ b)
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth₁ : shallow₁ ≤ deep) (hdepth₂ : shallow₂ ≤ deep) :
    ∃ swappedTree : InsertionScheduleTree,
      weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
        swappedTree.leaves.Perm tree.leaves ∧
          leafDepthWeights depth swappedTree =
            pre ++ [(shallow₂, d)] ++ middle₁ ++ [(shallow₁, c)] ++
              middle₂ ++ [(deep, a), (deep, b)] ++ suffix := by
  let swappedPairs :=
    pre ++ [(shallow₂, d)] ++ middle₁ ++ [(shallow₁, c)] ++
      middle₂ ++ [(deep, a), (deep, b)] ++ suffix
  have hpairsToReverseCanonical :
      (leafDepthWeights depth tree).Perm
        (pre ++ [(deep, c), (deep, d)] ++ middle₁ ++
          [(shallow₂, b)] ++ middle₂ ++ [(shallow₁, a)] ++ suffix) := by
    rw [hpairs]
    exact listPerm_two_selected_before_deepest_to_canonical
      pre middle₁ middle₂ suffix (deep, c) (deep, d)
      (shallow₂, b) (shallow₁, a)
  have hpairsPerm :
      (leafDepthWeights depth tree).Perm
        (pre ++ [(deep, c), (deep, d)] ++ middle₁ ++
          [(shallow₁, a)] ++ middle₂ ++ [(shallow₂, b)] ++ suffix) := by
    exact hpairsToReverseCanonical.trans
      (weightListPerm_pair_exchange
        (pre ++ [(deep, c), (deep, d)] ++ middle₁)
        middle₂ suffix (shallow₂, b) (shallow₁, a))
  have hswappedToReverseCanonical :
      swappedPairs.Perm
        (pre ++ [(deep, a), (deep, b)] ++ middle₁ ++
          [(shallow₂, d)] ++ middle₂ ++ [(shallow₁, c)] ++ suffix) := by
    exact listPerm_two_selected_before_deepest_to_canonical
      pre middle₁ middle₂ suffix (deep, a) (deep, b)
      (shallow₂, d) (shallow₁, c)
  have hswappedPerm :
      swappedPairs.Perm
        (pre ++ [(deep, a), (deep, b)] ++ middle₁ ++
          [(shallow₁, c)] ++ middle₂ ++ [(shallow₂, d)] ++ suffix) := by
    exact hswappedToReverseCanonical.trans
      (weightListPerm_pair_exchange
        (pre ++ [(deep, a), (deep, b)] ++ middle₁)
        middle₂ suffix (shallow₂, d) (shallow₁, c))
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.nondegenerate
      pre middle₁ middle₂ suffix rest hpairsPerm hswappedPerm
      htwoSmallest hab hrest hdepth₁ hdepth₂
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [hpairs]
    simp [swappedPairs, List.map_append]
  exact
    exists_relabelLeaves_for_two_smallest_deepest_exchange_branch_of_depths_eq
      hbranch hdepths

/-- Nonoverlap same-shape assembly for the mixed orientation where the first
two-smallest slot appears before the deepest sibling pair and the second
two-smallest slot appears after it. -/
theorem
    exists_tree_for_two_pair_exchange_around_deepest_of_two_smallest_decomposition_eq
    {tree : InsertionScheduleTree} {depth : ℕ}
    (pre middle₁ middle₂ suffix rest : List (ℕ × ℝ))
    {a b c d : ℝ} {deep shallow₁ shallow₂ : ℕ}
    (hpairs :
      leafDepthWeights depth tree =
        pre ++ [(shallow₁, a)] ++ middle₁ ++ [(deep, c), (deep, d)] ++
          middle₂ ++ [(shallow₂, b)] ++ suffix)
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((shallow₁, a) :: (shallow₂, b) :: rest))
    (hab : a ≤ b)
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth₁ : shallow₁ ≤ deep) (hdepth₂ : shallow₂ ≤ deep) :
    ∃ swappedTree : InsertionScheduleTree,
      weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
        swappedTree.leaves.Perm tree.leaves ∧
          leafDepthWeights depth swappedTree =
            pre ++ [(shallow₁, c)] ++ middle₁ ++
              [(deep, a), (deep, b)] ++ middle₂ ++
                [(shallow₂, d)] ++ suffix := by
  let swappedPairs :=
    pre ++ [(shallow₁, c)] ++ middle₁ ++
      [(deep, a), (deep, b)] ++ middle₂ ++ [(shallow₂, d)] ++
        suffix
  have hpairsPerm :
      (leafDepthWeights depth tree).Perm
        (pre ++ [(deep, c), (deep, d)] ++ middle₁ ++
          [(shallow₁, a)] ++ middle₂ ++ [(shallow₂, b)] ++ suffix) := by
    rw [hpairs]
    exact listPerm_selected_before_deepest_before_selected_to_canonical
      pre middle₁ middle₂ suffix (deep, c) (deep, d)
      (shallow₁, a) (shallow₂, b)
  have hswappedPerm :
      swappedPairs.Perm
        (pre ++ [(deep, a), (deep, b)] ++ middle₁ ++
          [(shallow₁, c)] ++ middle₂ ++ [(shallow₂, d)] ++ suffix) := by
    exact listPerm_selected_before_deepest_before_selected_to_canonical
      pre middle₁ middle₂ suffix (deep, a) (deep, b)
      (shallow₁, c) (shallow₂, d)
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.nondegenerate
      pre middle₁ middle₂ suffix rest hpairsPerm hswappedPerm
      htwoSmallest hab hrest hdepth₁ hdepth₂
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [hpairs]
    simp [swappedPairs, List.map_append]
  exact
    exists_relabelLeaves_for_two_smallest_deepest_exchange_branch_of_depths_eq
      hbranch hdepths

/-- Nonoverlap same-shape assembly for the reverse mixed orientation where the
`b` slot appears before the deepest sibling pair and the `a` slot appears
after it. -/
theorem
    exists_tree_for_two_pair_exchange_reverse_around_deepest_of_two_smallest_decomposition_eq
    {tree : InsertionScheduleTree} {depth : ℕ}
    (pre middle₁ middle₂ suffix rest : List (ℕ × ℝ))
    {a b c d : ℝ} {deep shallow₁ shallow₂ : ℕ}
    (hpairs :
      leafDepthWeights depth tree =
        pre ++ [(shallow₂, b)] ++ middle₁ ++ [(deep, c), (deep, d)] ++
          middle₂ ++ [(shallow₁, a)] ++ suffix)
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((shallow₁, a) :: (shallow₂, b) :: rest))
    (hab : a ≤ b)
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth₁ : shallow₁ ≤ deep) (hdepth₂ : shallow₂ ≤ deep) :
    ∃ swappedTree : InsertionScheduleTree,
      weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
        swappedTree.leaves.Perm tree.leaves ∧
          leafDepthWeights depth swappedTree =
            pre ++ [(shallow₂, d)] ++ middle₁ ++
              [(deep, a), (deep, b)] ++ middle₂ ++
                [(shallow₁, c)] ++ suffix := by
  let swappedPairs :=
    pre ++ [(shallow₂, d)] ++ middle₁ ++
      [(deep, a), (deep, b)] ++ middle₂ ++ [(shallow₁, c)] ++
        suffix
  have hpairsToReverseCanonical :
      (leafDepthWeights depth tree).Perm
        (pre ++ [(deep, c), (deep, d)] ++ middle₁ ++
          [(shallow₂, b)] ++ middle₂ ++ [(shallow₁, a)] ++ suffix) := by
    rw [hpairs]
    exact listPerm_selected_before_deepest_before_selected_to_canonical
      pre middle₁ middle₂ suffix (deep, c) (deep, d)
      (shallow₂, b) (shallow₁, a)
  have hpairsPerm :
      (leafDepthWeights depth tree).Perm
        (pre ++ [(deep, c), (deep, d)] ++ middle₁ ++
          [(shallow₁, a)] ++ middle₂ ++ [(shallow₂, b)] ++ suffix) := by
    exact hpairsToReverseCanonical.trans
      (weightListPerm_pair_exchange
        (pre ++ [(deep, c), (deep, d)] ++ middle₁)
        middle₂ suffix (shallow₂, b) (shallow₁, a))
  have hswappedToReverseCanonical :
      swappedPairs.Perm
        (pre ++ [(deep, a), (deep, b)] ++ middle₁ ++
          [(shallow₂, d)] ++ middle₂ ++ [(shallow₁, c)] ++ suffix) := by
    exact listPerm_selected_before_deepest_before_selected_to_canonical
      pre middle₁ middle₂ suffix (deep, a) (deep, b)
      (shallow₂, d) (shallow₁, c)
  have hswappedPerm :
      swappedPairs.Perm
        (pre ++ [(deep, a), (deep, b)] ++ middle₁ ++
          [(shallow₁, c)] ++ middle₂ ++ [(shallow₂, d)] ++ suffix) := by
    exact hswappedToReverseCanonical.trans
      (weightListPerm_pair_exchange
        (pre ++ [(deep, a), (deep, b)] ++ middle₁)
        middle₂ suffix (shallow₂, d) (shallow₁, c))
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.nondegenerate
      pre middle₁ middle₂ suffix rest hpairsPerm hswappedPerm
      htwoSmallest hab hrest hdepth₁ hdepth₂
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [hpairs]
    simp [swappedPairs, List.map_append]
  exact
    exists_relabelLeaves_for_two_smallest_deepest_exchange_branch_of_depths_eq
      hbranch hdepths

/-- Same-shape assembly for the overlap branch where the first two-smallest
entry is already the left deepest sibling. -/
theorem exists_tree_for_left_deepest_two_smallest_decomposition_eq
    {tree : InsertionScheduleTree} {depth : ℕ}
    (pre middle suffix rest : List (ℕ × ℝ))
    {a b c : ℝ} {deep shallow : ℕ}
    (hpairs :
      leafDepthWeights depth tree =
        pre ++ [(deep, a), (deep, c)] ++ middle ++
          [(shallow, b)] ++ suffix)
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((deep, a) :: (shallow, b) :: rest))
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth : shallow ≤ deep) :
    ∃ swappedTree : InsertionScheduleTree,
      weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
        swappedTree.leaves.Perm tree.leaves ∧
          leafDepthWeights depth swappedTree =
            pre ++ [(deep, a), (deep, b)] ++ middle ++
              [(shallow, c)] ++ suffix := by
  let swappedPairs :=
    pre ++ [(deep, a), (deep, b)] ++ middle ++
      [(shallow, c)] ++ suffix
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.leftDeepestFirstSmallest
      pre middle suffix rest
      (by rw [hpairs]) (by rfl) htwoSmallest hrest hdepth
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [hpairs]
    simp [swappedPairs, List.map_append]
  exact
    exists_relabelLeaves_for_two_smallest_deepest_exchange_branch_of_depths_eq
      hbranch hdepths

/-- Same-shape assembly for the overlap branch where the first two-smallest
entry is already the right deepest sibling. -/
theorem exists_tree_for_right_deepest_two_smallest_decomposition_eq
    {tree : InsertionScheduleTree} {depth : ℕ}
    (pre middle suffix rest : List (ℕ × ℝ))
    {a b c : ℝ} {deep shallow : ℕ}
    (hpairs :
      leafDepthWeights depth tree =
        pre ++ [(deep, c), (deep, a)] ++ middle ++
          [(shallow, b)] ++ suffix)
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((deep, a) :: (shallow, b) :: rest))
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth : shallow ≤ deep) :
    ∃ swappedTree : InsertionScheduleTree,
      weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
        swappedTree.leaves.Perm tree.leaves ∧
          leafDepthWeights depth swappedTree =
            pre ++ [(deep, b), (deep, a)] ++ middle ++
              [(shallow, c)] ++ suffix := by
  let swappedPairs :=
    pre ++ [(deep, b), (deep, a)] ++ middle ++
      [(shallow, c)] ++ suffix
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.rightDeepestFirstSmallest
      pre middle suffix rest
      (by rw [hpairs]) (by rfl) htwoSmallest hrest hdepth
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [hpairs]
    simp [swappedPairs, List.map_append]
  exact
    exists_relabelLeaves_for_two_smallest_deepest_exchange_branch_of_depths_eq
      hbranch hdepths

/-- Same-shape assembly for the overlap branch where the second two-smallest
entry is already the left deepest sibling. -/
theorem exists_tree_for_left_deepest_second_two_smallest_decomposition_eq
    {tree : InsertionScheduleTree} {depth : ℕ}
    (pre middle suffix rest : List (ℕ × ℝ))
    {a b c : ℝ} {deep shallow : ℕ}
    (hpairs :
      leafDepthWeights depth tree =
        pre ++ [(deep, b), (deep, c)] ++ middle ++
          [(shallow, a)] ++ suffix)
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((shallow, a) :: (deep, b) :: rest))
    (hab : a ≤ b)
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth : shallow ≤ deep) :
    ∃ swappedTree : InsertionScheduleTree,
      weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
        swappedTree.leaves.Perm tree.leaves ∧
          leafDepthWeights depth swappedTree =
            pre ++ [(deep, b), (deep, a)] ++ middle ++
              [(shallow, c)] ++ suffix := by
  let swappedPairs :=
    pre ++ [(deep, b), (deep, a)] ++ middle ++
      [(shallow, c)] ++ suffix
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.leftDeepestSecondSmallest
      pre middle suffix rest
      (by rw [hpairs]) (by rfl) htwoSmallest hab hrest hdepth
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [hpairs]
    simp [swappedPairs, List.map_append]
  exact
    exists_relabelLeaves_for_two_smallest_deepest_exchange_branch_of_depths_eq
      hbranch hdepths

/-- Same-shape assembly for the overlap branch where the second two-smallest
entry is already the right deepest sibling. -/
theorem exists_tree_for_right_deepest_second_two_smallest_decomposition_eq
    {tree : InsertionScheduleTree} {depth : ℕ}
    (pre middle suffix rest : List (ℕ × ℝ))
    {a b c : ℝ} {deep shallow : ℕ}
    (hpairs :
      leafDepthWeights depth tree =
        pre ++ [(deep, c), (deep, b)] ++ middle ++
          [(shallow, a)] ++ suffix)
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((shallow, a) :: (deep, b) :: rest))
    (hab : a ≤ b)
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth : shallow ≤ deep) :
    ∃ swappedTree : InsertionScheduleTree,
      weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
        swappedTree.leaves.Perm tree.leaves ∧
          leafDepthWeights depth swappedTree =
            pre ++ [(deep, a), (deep, b)] ++ middle ++
              [(shallow, c)] ++ suffix := by
  let swappedPairs :=
    pre ++ [(deep, a), (deep, b)] ++ middle ++
      [(shallow, c)] ++ suffix
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.rightDeepestSecondSmallest
      pre middle suffix rest
      (by rw [hpairs]) (by rfl) htwoSmallest hab hrest hdepth
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [hpairs]
    simp [swappedPairs, List.map_append]
  exact
    exists_relabelLeaves_for_two_smallest_deepest_exchange_branch_of_depths_eq
      hbranch hdepths

/-- Same-shape assembly for the overlap branch where the first two-smallest
entry is already the left deepest sibling and the other selected entry appears
before the displayed deepest sibling pair. -/
theorem exists_tree_for_left_deepest_two_smallest_before_deepest_decomposition_eq
    {tree : InsertionScheduleTree} {depth : ℕ}
    (pre middle suffix rest : List (ℕ × ℝ))
    {a b c : ℝ} {deep shallow : ℕ}
    (hpairs :
      leafDepthWeights depth tree =
        pre ++ [(shallow, b)] ++ middle ++ [(deep, a), (deep, c)] ++
          suffix)
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((deep, a) :: (shallow, b) :: rest))
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth : shallow ≤ deep) :
    ∃ swappedTree : InsertionScheduleTree,
      weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
        swappedTree.leaves.Perm tree.leaves ∧
          leafDepthWeights depth swappedTree =
            pre ++ [(shallow, c)] ++ middle ++ [(deep, a), (deep, b)] ++
              suffix := by
  let swappedPairs :=
    pre ++ [(shallow, c)] ++ middle ++ [(deep, a), (deep, b)] ++ suffix
  have hpairsPerm :
      (leafDepthWeights depth tree).Perm
        (pre ++ [(deep, a), (deep, c)] ++ middle ++
          [(shallow, b)] ++ suffix) := by
    rw [hpairs]
    exact listPerm_selected_before_adjacent_to_after
      pre middle suffix (shallow, b) (deep, a) (deep, c)
  have hswappedPerm :
      swappedPairs.Perm
        (pre ++ [(deep, a), (deep, b)] ++ middle ++
          [(shallow, c)] ++ suffix) := by
    exact listPerm_selected_before_adjacent_to_after
      pre middle suffix (shallow, c) (deep, a) (deep, b)
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.leftDeepestFirstSmallest
      pre middle suffix rest hpairsPerm hswappedPerm
      htwoSmallest hrest hdepth
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [hpairs]
    simp [swappedPairs, List.map_append]
  exact
    exists_relabelLeaves_for_two_smallest_deepest_exchange_branch_of_depths_eq
      hbranch hdepths

/-- Same-shape assembly for the overlap branch where the first two-smallest
entry is already the right deepest sibling and the other selected entry appears
before the displayed deepest sibling pair. -/
theorem exists_tree_for_right_deepest_two_smallest_before_deepest_decomposition_eq
    {tree : InsertionScheduleTree} {depth : ℕ}
    (pre middle suffix rest : List (ℕ × ℝ))
    {a b c : ℝ} {deep shallow : ℕ}
    (hpairs :
      leafDepthWeights depth tree =
        pre ++ [(shallow, b)] ++ middle ++ [(deep, c), (deep, a)] ++
          suffix)
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((deep, a) :: (shallow, b) :: rest))
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth : shallow ≤ deep) :
    ∃ swappedTree : InsertionScheduleTree,
      weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
        swappedTree.leaves.Perm tree.leaves ∧
          leafDepthWeights depth swappedTree =
            pre ++ [(shallow, c)] ++ middle ++ [(deep, b), (deep, a)] ++
              suffix := by
  let swappedPairs :=
    pre ++ [(shallow, c)] ++ middle ++ [(deep, b), (deep, a)] ++ suffix
  have hpairsPerm :
      (leafDepthWeights depth tree).Perm
        (pre ++ [(deep, c), (deep, a)] ++ middle ++
          [(shallow, b)] ++ suffix) := by
    rw [hpairs]
    exact listPerm_selected_before_adjacent_to_after
      pre middle suffix (shallow, b) (deep, c) (deep, a)
  have hswappedPerm :
      swappedPairs.Perm
        (pre ++ [(deep, b), (deep, a)] ++ middle ++
          [(shallow, c)] ++ suffix) := by
    exact listPerm_selected_before_adjacent_to_after
      pre middle suffix (shallow, c) (deep, b) (deep, a)
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.rightDeepestFirstSmallest
      pre middle suffix rest hpairsPerm hswappedPerm
      htwoSmallest hrest hdepth
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [hpairs]
    simp [swappedPairs, List.map_append]
  exact
    exists_relabelLeaves_for_two_smallest_deepest_exchange_branch_of_depths_eq
      hbranch hdepths

/-- Same-shape assembly for the overlap branch where the second two-smallest
entry is already the left deepest sibling and the other selected entry appears
before the displayed deepest sibling pair. -/
theorem
    exists_tree_for_left_deepest_second_two_smallest_before_deepest_decomposition_eq
    {tree : InsertionScheduleTree} {depth : ℕ}
    (pre middle suffix rest : List (ℕ × ℝ))
    {a b c : ℝ} {deep shallow : ℕ}
    (hpairs :
      leafDepthWeights depth tree =
        pre ++ [(shallow, a)] ++ middle ++ [(deep, b), (deep, c)] ++
          suffix)
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((shallow, a) :: (deep, b) :: rest))
    (hab : a ≤ b)
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth : shallow ≤ deep) :
    ∃ swappedTree : InsertionScheduleTree,
      weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
        swappedTree.leaves.Perm tree.leaves ∧
          leafDepthWeights depth swappedTree =
            pre ++ [(shallow, c)] ++ middle ++ [(deep, b), (deep, a)] ++
              suffix := by
  let swappedPairs :=
    pre ++ [(shallow, c)] ++ middle ++ [(deep, b), (deep, a)] ++ suffix
  have hpairsPerm :
      (leafDepthWeights depth tree).Perm
        (pre ++ [(deep, b), (deep, c)] ++ middle ++
          [(shallow, a)] ++ suffix) := by
    rw [hpairs]
    exact listPerm_selected_before_adjacent_to_after
      pre middle suffix (shallow, a) (deep, b) (deep, c)
  have hswappedPerm :
      swappedPairs.Perm
        (pre ++ [(deep, b), (deep, a)] ++ middle ++
          [(shallow, c)] ++ suffix) := by
    exact listPerm_selected_before_adjacent_to_after
      pre middle suffix (shallow, c) (deep, b) (deep, a)
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.leftDeepestSecondSmallest
      pre middle suffix rest hpairsPerm hswappedPerm
      htwoSmallest hab hrest hdepth
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [hpairs]
    simp [swappedPairs, List.map_append]
  exact
    exists_relabelLeaves_for_two_smallest_deepest_exchange_branch_of_depths_eq
      hbranch hdepths

/-- Same-shape assembly for the overlap branch where the second two-smallest
entry is already the right deepest sibling and the other selected entry appears
before the displayed deepest sibling pair. -/
theorem
    exists_tree_for_right_deepest_second_two_smallest_before_deepest_decomposition_eq
    {tree : InsertionScheduleTree} {depth : ℕ}
    (pre middle suffix rest : List (ℕ × ℝ))
    {a b c : ℝ} {deep shallow : ℕ}
    (hpairs :
      leafDepthWeights depth tree =
        pre ++ [(shallow, a)] ++ middle ++ [(deep, c), (deep, b)] ++
          suffix)
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((shallow, a) :: (deep, b) :: rest))
    (hab : a ≤ b)
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth : shallow ≤ deep) :
    ∃ swappedTree : InsertionScheduleTree,
      weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
        swappedTree.leaves.Perm tree.leaves ∧
          leafDepthWeights depth swappedTree =
            pre ++ [(shallow, c)] ++ middle ++ [(deep, a), (deep, b)] ++
              suffix := by
  let swappedPairs :=
    pre ++ [(shallow, c)] ++ middle ++ [(deep, a), (deep, b)] ++ suffix
  have hpairsPerm :
      (leafDepthWeights depth tree).Perm
        (pre ++ [(deep, c), (deep, b)] ++ middle ++
          [(shallow, a)] ++ suffix) := by
    rw [hpairs]
    exact listPerm_selected_before_adjacent_to_after
      pre middle suffix (shallow, a) (deep, c) (deep, b)
  have hswappedPerm :
      swappedPairs.Perm
        (pre ++ [(deep, a), (deep, b)] ++ middle ++
          [(shallow, c)] ++ suffix) := by
    exact listPerm_selected_before_adjacent_to_after
      pre middle suffix (shallow, c) (deep, a) (deep, b)
  have hbranch :
      TwoSmallestDeepestExchangeBranch
        (leafDepthWeights depth tree) swappedPairs := by
    exact TwoSmallestDeepestExchangeBranch.rightDeepestSecondSmallest
      pre middle suffix rest hpairsPerm hswappedPerm
      htwoSmallest hab hrest hdepth
  have hdepths :
      swappedPairs.map Prod.fst =
        (leafDepthWeights depth tree).map Prod.fst := by
    rw [hpairs]
    simp [swappedPairs, List.map_append]
  exact
    exists_relabelLeaves_for_two_smallest_deepest_exchange_branch_of_depths_eq
      hbranch hdepths

/-- Combined nonoverlap classifier for the orientation where the first
two-smallest slot is before the displayed deepest sibling pair.  If the second
two-smallest slot is not equal to either displayed deepest entry, the finite
occurrence split selects the appropriate before-before, before-between, or
around-deepest same-shape assembly theorem. -/
theorem exists_tree_for_first_before_deepest_two_smallest_nonoverlap_anywhere
    {tree : InsertionScheduleTree} {depth : ℕ}
    (before middle suffix rest : List (ℕ × ℝ))
    {a b c d : ℝ} {deep shallow₁ shallow₂ : ℕ}
    (hpairs :
      leafDepthWeights depth tree =
        before ++ [(shallow₁, a)] ++ middle ++ [(deep, c), (deep, d)] ++
          suffix)
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((shallow₁, a) :: (shallow₂, b) :: rest))
    (hab : a ≤ b)
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth₁ : shallow₁ ≤ deep) (hdepth₂ : shallow₂ ≤ deep)
    (hsecond_ne_left : (shallow₂, b) ≠ (deep, c))
    (hsecond_ne_right : (shallow₂, b) ≠ (deep, d)) :
    ∃ swappedTree : InsertionScheduleTree,
      weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
        swappedTree.leaves.Perm tree.leaves := by
  obtain hloc :=
    exists_second_position_of_first_before_adjacent_pair
      (pairs := leafDepthWeights depth tree) (rest := rest)
      (first := (shallow₁, a)) (second := (shallow₂, b))
      (left := (deep, c)) (right := (deep, d))
      before middle suffix hpairs htwoSmallest
      hsecond_ne_left hsecond_ne_right
  rcases hloc with hbefore | hbetween | hafter
  · obtain ⟨pre, gap, _hbefore, hpairs'⟩ := hbefore
    obtain ⟨swappedTree, hcost, hleaves, _hrealized⟩ :=
      exists_tree_for_two_pair_exchange_reverse_before_deepest_of_two_smallest_decomposition_eq
        pre gap middle suffix rest
        (by simpa [List.append_assoc] using hpairs')
        htwoSmallest hab hrest hdepth₁ hdepth₂
    exact ⟨swappedTree, hcost, hleaves⟩
  · obtain ⟨gap, tail, _hmiddle, hpairs'⟩ := hbetween
    obtain ⟨swappedTree, hcost, hleaves, _hrealized⟩ :=
      exists_tree_for_two_pair_exchange_before_deepest_of_two_smallest_decomposition_eq
        before gap tail suffix rest
        (by simpa [List.append_assoc] using hpairs')
        htwoSmallest hab hrest hdepth₁ hdepth₂
    exact ⟨swappedTree, hcost, hleaves⟩
  · obtain ⟨gap, tail, _hsuffix, hpairs'⟩ := hafter
    obtain ⟨swappedTree, hcost, hleaves, _hrealized⟩ :=
      exists_tree_for_two_pair_exchange_around_deepest_of_two_smallest_decomposition_eq
        before middle gap tail rest
        (by simpa [List.append_assoc] using hpairs')
        htwoSmallest hab hrest hdepth₁ hdepth₂
    exact ⟨swappedTree, hcost, hleaves⟩

/-- Combined nonoverlap classifier for the orientation where the first
two-smallest slot is after the displayed deepest sibling pair.  If the second
two-smallest slot is not equal to either displayed deepest entry, the finite
occurrence split selects the appropriate around-deepest or deepest-before
same-shape assembly theorem. -/
theorem exists_tree_for_first_after_deepest_two_smallest_nonoverlap_anywhere
    {tree : InsertionScheduleTree} {depth : ℕ}
    (before middle suffix rest : List (ℕ × ℝ))
    {a b c d : ℝ} {deep shallow₁ shallow₂ : ℕ}
    (hpairs :
      leafDepthWeights depth tree =
        before ++ [(deep, c), (deep, d)] ++ middle ++
          [(shallow₁, a)] ++ suffix)
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((shallow₁, a) :: (shallow₂, b) :: rest))
    (hab : a ≤ b)
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth₁ : shallow₁ ≤ deep) (hdepth₂ : shallow₂ ≤ deep)
    (hsecond_ne_left : (shallow₂, b) ≠ (deep, c))
    (hsecond_ne_right : (shallow₂, b) ≠ (deep, d)) :
    ∃ swappedTree : InsertionScheduleTree,
      weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
        swappedTree.leaves.Perm tree.leaves := by
  obtain hloc :=
    exists_second_position_of_first_after_adjacent_pair
      (pairs := leafDepthWeights depth tree) (rest := rest)
      (first := (shallow₁, a)) (second := (shallow₂, b))
      (left := (deep, c)) (right := (deep, d))
      before middle suffix hpairs htwoSmallest
      hsecond_ne_left hsecond_ne_right
  rcases hloc with hbefore | hbetween | hafter
  · obtain ⟨pre, gap, _hbefore, hpairs'⟩ := hbefore
    obtain ⟨swappedTree, hcost, hleaves, _hrealized⟩ :=
      exists_tree_for_two_pair_exchange_reverse_around_deepest_of_two_smallest_decomposition_eq
        pre gap middle suffix rest
        (by simpa [List.append_assoc] using hpairs')
        htwoSmallest hab hrest hdepth₁ hdepth₂
    exact ⟨swappedTree, hcost, hleaves⟩
  · obtain ⟨gap, tail, _hmiddle, hpairs'⟩ := hbetween
    obtain ⟨swappedTree, hcost, hleaves, _hrealized⟩ :=
      exists_tree_for_two_pair_exchange_reverse_of_two_smallest_decomposition_eq
        before gap tail suffix rest
        (by simpa [List.append_assoc] using hpairs')
        htwoSmallest hab hrest hdepth₁ hdepth₂
    exact ⟨swappedTree, hcost, hleaves⟩
  · obtain ⟨gap, tail, _hsuffix, hpairs'⟩ := hafter
    obtain ⟨swappedTree, hcost, hleaves, _hrealized⟩ :=
      exists_tree_for_two_pair_exchange_of_two_smallest_decomposition_eq
        before middle gap tail rest
        (by simpa [List.append_assoc] using hpairs')
        htwoSmallest hab hrest hdepth₁ hdepth₂
    exact ⟨swappedTree, hcost, hleaves⟩

/-- Combined classifier for the orientation where the first two-smallest slot
is before the displayed deepest sibling pair.  The second two-smallest slot may
be the left deepest sibling, the right deepest sibling, or a nonoverlapping
slot elsewhere. -/
theorem exists_tree_for_first_before_deepest_two_smallest_anywhere
    {tree : InsertionScheduleTree} {depth : ℕ}
    (before middle suffix rest : List (ℕ × ℝ))
    {a b c d : ℝ} {deep shallow₁ shallow₂ : ℕ}
    (hpairs :
      leafDepthWeights depth tree =
        before ++ [(shallow₁, a)] ++ middle ++ [(deep, c), (deep, d)] ++
          suffix)
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((shallow₁, a) :: (shallow₂, b) :: rest))
    (hab : a ≤ b)
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth₁ : shallow₁ ≤ deep) (hdepth₂ : shallow₂ ≤ deep) :
    ∃ swappedTree : InsertionScheduleTree,
      weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
        swappedTree.leaves.Perm tree.leaves := by
  by_cases hleft : (shallow₂, b) = (deep, c)
  · cases hleft
    obtain ⟨swappedTree, hcost, hleaves, _hrealized⟩ :=
      exists_tree_for_left_deepest_second_two_smallest_before_deepest_decomposition_eq
        before middle suffix rest hpairs htwoSmallest hab hrest hdepth₁
    exact ⟨swappedTree, hcost, hleaves⟩
  · by_cases hright : (shallow₂, b) = (deep, d)
    · cases hright
      obtain ⟨swappedTree, hcost, hleaves, _hrealized⟩ :=
        exists_tree_for_right_deepest_second_two_smallest_before_deepest_decomposition_eq
          before middle suffix rest hpairs htwoSmallest hab hrest hdepth₁
      exact ⟨swappedTree, hcost, hleaves⟩
    · exact
        exists_tree_for_first_before_deepest_two_smallest_nonoverlap_anywhere
          before middle suffix rest hpairs htwoSmallest hab hrest
          hdepth₁ hdepth₂ hleft hright

/-- Combined classifier for the orientation where the first two-smallest slot
is after the displayed deepest sibling pair.  The second two-smallest slot may
be the left deepest sibling, the right deepest sibling, or a nonoverlapping
slot elsewhere. -/
theorem exists_tree_for_first_after_deepest_two_smallest_anywhere
    {tree : InsertionScheduleTree} {depth : ℕ}
    (before middle suffix rest : List (ℕ × ℝ))
    {a b c d : ℝ} {deep shallow₁ shallow₂ : ℕ}
    (hpairs :
      leafDepthWeights depth tree =
        before ++ [(deep, c), (deep, d)] ++ middle ++
          [(shallow₁, a)] ++ suffix)
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((shallow₁, a) :: (shallow₂, b) :: rest))
    (hab : a ≤ b)
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth₁ : shallow₁ ≤ deep) (hdepth₂ : shallow₂ ≤ deep) :
    ∃ swappedTree : InsertionScheduleTree,
      weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
        swappedTree.leaves.Perm tree.leaves := by
  by_cases hleft : (shallow₂, b) = (deep, c)
  · cases hleft
    obtain ⟨swappedTree, hcost, hleaves, _hrealized⟩ :=
      exists_tree_for_left_deepest_second_two_smallest_decomposition_eq
        before middle suffix rest hpairs htwoSmallest hab hrest hdepth₁
    exact ⟨swappedTree, hcost, hleaves⟩
  · by_cases hright : (shallow₂, b) = (deep, d)
    · cases hright
      obtain ⟨swappedTree, hcost, hleaves, _hrealized⟩ :=
        exists_tree_for_right_deepest_second_two_smallest_decomposition_eq
          before middle suffix rest hpairs htwoSmallest hab hrest hdepth₁
      exact ⟨swappedTree, hcost, hleaves⟩
    · exact
        exists_tree_for_first_after_deepest_two_smallest_nonoverlap_anywhere
          before middle suffix rest hpairs htwoSmallest hab hrest
          hdepth₁ hdepth₂ hleft hright

/-- Combined classifier for the orientation where the first two-smallest slot
is already the left member of the displayed deepest sibling pair.  The second
two-smallest slot may be the right deepest sibling, before the pair, or after
the pair. -/
theorem exists_tree_for_left_deepest_first_two_smallest_anywhere
    {tree : InsertionScheduleTree} {depth : ℕ}
    (pre suffix rest : List (ℕ × ℝ))
    {a b c : ℝ} {deep shallow : ℕ}
    (hpairs :
      leafDepthWeights depth tree =
        pre ++ [(deep, a), (deep, c)] ++ suffix)
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((deep, a) :: (shallow, b) :: rest))
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth : shallow ≤ deep) :
    ∃ swappedTree : InsertionScheduleTree,
      weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
        swappedTree.leaves.Perm tree.leaves := by
  have hpairsFront :
      (leafDepthWeights depth tree).Perm
        ((deep, a) :: pre ++ [(deep, c)] ++ suffix) := by
    rw [hpairs]
    simp only [List.append_assoc, List.cons_append]
    exact List.perm_middle (a := (deep, a)) (l₁ := pre)
      (l₂ := (deep, c) :: suffix)
  have htailPerm :
      (pre ++ [(deep, c)] ++ suffix).Perm ((shallow, b) :: rest) :=
    List.Perm.cons_inv (hpairsFront.symm.trans htwoSmallest)
  have hsecond_mem : (shallow, b) ∈ pre ++ [(deep, c)] ++ suffix :=
    (htailPerm.mem_iff).2 (by simp)
  simp [List.mem_append] at hsecond_mem
  rcases hsecond_mem with hpre | hright | hsuffix
  · obtain ⟨before, middle, hsplit⟩ :=
      exists_split_of_mem pre hpre
    have hpairs' :
        leafDepthWeights depth tree =
          before ++ [(shallow, b)] ++ middle ++
            [(deep, a), (deep, c)] ++ suffix := by
      rw [hpairs, hsplit]
      simp [List.append_assoc]
    obtain ⟨swappedTree, hcost, hleaves, _hrealized⟩ :=
      exists_tree_for_left_deepest_two_smallest_before_deepest_decomposition_eq
        before middle suffix rest hpairs' htwoSmallest hrest hdepth
    exact ⟨swappedTree, hcost, hleaves⟩
  · cases hright
    obtain ⟨swappedTree, hcost, hleaves, _hrealized⟩ :=
      exists_tree_for_deepest_pair_noop_eq pre suffix hpairs
    exact ⟨swappedTree, hcost, hleaves⟩
  · obtain ⟨middle, after, hsplit⟩ :=
      exists_split_of_mem suffix hsuffix
    have hpairs' :
        leafDepthWeights depth tree =
          pre ++ [(deep, a), (deep, c)] ++ middle ++
            [(shallow, b)] ++ after := by
      rw [hpairs, hsplit]
      simp [List.append_assoc]
    obtain ⟨swappedTree, hcost, hleaves, _hrealized⟩ :=
      exists_tree_for_left_deepest_two_smallest_decomposition_eq
        pre middle after rest hpairs' htwoSmallest hrest hdepth
    exact ⟨swappedTree, hcost, hleaves⟩

/-- Combined classifier for the orientation where the first two-smallest slot
is already the right member of the displayed deepest sibling pair.  The second
two-smallest slot may be the left deepest sibling, before the pair, or after
the pair. -/
theorem exists_tree_for_right_deepest_first_two_smallest_anywhere
    {tree : InsertionScheduleTree} {depth : ℕ}
    (pre suffix rest : List (ℕ × ℝ))
    {a b c : ℝ} {deep shallow : ℕ}
    (hpairs :
      leafDepthWeights depth tree =
        pre ++ [(deep, c), (deep, a)] ++ suffix)
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((deep, a) :: (shallow, b) :: rest))
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth : shallow ≤ deep) :
    ∃ swappedTree : InsertionScheduleTree,
      weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
        swappedTree.leaves.Perm tree.leaves := by
  have hpairsFront :
      (leafDepthWeights depth tree).Perm
        ((deep, a) :: pre ++ [(deep, c)] ++ suffix) := by
    rw [hpairs]
    simpa [List.append_assoc] using
      (List.perm_middle (a := (deep, a)) (l₁ := pre ++ [(deep, c)])
        (l₂ := suffix))
  have htailPerm :
      (pre ++ [(deep, c)] ++ suffix).Perm ((shallow, b) :: rest) :=
    List.Perm.cons_inv (hpairsFront.symm.trans htwoSmallest)
  have hsecond_mem : (shallow, b) ∈ pre ++ [(deep, c)] ++ suffix :=
    (htailPerm.mem_iff).2 (by simp)
  simp [List.mem_append] at hsecond_mem
  rcases hsecond_mem with hpre | hleft | hsuffix
  · obtain ⟨before, middle, hsplit⟩ :=
      exists_split_of_mem pre hpre
    have hpairs' :
        leafDepthWeights depth tree =
          before ++ [(shallow, b)] ++ middle ++
            [(deep, c), (deep, a)] ++ suffix := by
      rw [hpairs, hsplit]
      simp [List.append_assoc]
    obtain ⟨swappedTree, hcost, hleaves, _hrealized⟩ :=
      exists_tree_for_right_deepest_two_smallest_before_deepest_decomposition_eq
        before middle suffix rest hpairs' htwoSmallest hrest hdepth
    exact ⟨swappedTree, hcost, hleaves⟩
  · cases hleft
    obtain ⟨swappedTree, hcost, hleaves, _hrealized⟩ :=
      exists_tree_for_deepest_pair_noop_eq pre suffix hpairs
    exact ⟨swappedTree, hcost, hleaves⟩
  · obtain ⟨middle, after, hsplit⟩ :=
      exists_split_of_mem suffix hsuffix
    have hpairs' :
        leafDepthWeights depth tree =
          pre ++ [(deep, c), (deep, a)] ++ middle ++
            [(shallow, b)] ++ after := by
      rw [hpairs, hsplit]
      simp [List.append_assoc]
    obtain ⟨swappedTree, hcost, hleaves, _hrealized⟩ :=
      exists_tree_for_right_deepest_two_smallest_decomposition_eq
        pre middle after rest hpairs' htwoSmallest hrest hdepth
    exact ⟨swappedTree, hcost, hleaves⟩

/-- Arbitrary occurrence classifier for a displayed deepest sibling pair and a
finite two-smallest decomposition.  The first selected occurrence may be before
the pair, after the pair, or one of the two displayed deepest siblings. -/
theorem exists_tree_for_two_smallest_deepest_pair_anywhere
    {tree : InsertionScheduleTree} {depth : ℕ}
    (pre suffix rest : List (ℕ × ℝ))
    {a b c d : ℝ} {deep shallow₁ shallow₂ : ℕ}
    (hpairs :
      leafDepthWeights depth tree =
        pre ++ [(deep, c), (deep, d)] ++ suffix)
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((shallow₁, a) :: (shallow₂, b) :: rest))
    (hab : a ≤ b)
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth₁ : shallow₁ ≤ deep) (hdepth₂ : shallow₂ ≤ deep) :
    ∃ swappedTree : InsertionScheduleTree,
      weightedLeafDepthCost depth swappedTree ≤
          weightedLeafDepthCost depth tree ∧
        swappedTree.leaves.Perm tree.leaves := by
  have hfirst_mem :
      (shallow₁, a) ∈ pre ++ [(deep, c), (deep, d)] ++ suffix := by
    have hmem : (shallow₁, a) ∈ leafDepthWeights depth tree :=
      (htwoSmallest.mem_iff).2 (by simp)
    simpa [hpairs] using hmem
  obtain hloc :=
    exists_selected_relative_to_adjacent_pair
      pre suffix (deep, c) (deep, d) (shallow₁, a) hfirst_mem
  rcases hloc with hbefore | hleft | hright | hafter
  · obtain ⟨before, middle, _hpre, hpairsDisplay⟩ := hbefore
    have hpairs' :
        leafDepthWeights depth tree =
          before ++ [(shallow₁, a)] ++ middle ++
            [(deep, c), (deep, d)] ++ suffix := by
      rw [hpairs, hpairsDisplay]
    exact
      exists_tree_for_first_before_deepest_two_smallest_anywhere
        before middle suffix rest hpairs' htwoSmallest hab hrest
        hdepth₁ hdepth₂
  · cases hleft
    exact
      exists_tree_for_left_deepest_first_two_smallest_anywhere
        pre suffix rest hpairs htwoSmallest hrest hdepth₂
  · cases hright
    exact
      exists_tree_for_right_deepest_first_two_smallest_anywhere
        pre suffix rest hpairs htwoSmallest hrest hdepth₂
  · obtain ⟨middle, after, _hsuffix, hpairsDisplay⟩ := hafter
    have hpairs' :
        leafDepthWeights depth tree =
          pre ++ [(deep, c), (deep, d)] ++ middle ++
            [(shallow₁, a)] ++ after := by
      rw [hpairs, hpairsDisplay]
    exact
      exists_tree_for_first_after_deepest_two_smallest_anywhere
        pre middle after rest hpairs' htwoSmallest hab hrest
        hdepth₁ hdepth₂

/-- Witness form of the arbitrary deepest-pair classifier.  Besides the cost
and leaf-multiset conclusion, the produced tree explicitly displays the two
selected smallest weights as an adjacent pair at the chosen deepest depth, in
one of the two sibling orientations. -/
theorem exists_tree_for_two_smallest_deepest_pair_anywhere_pair_witness
    {tree : InsertionScheduleTree} {depth : ℕ}
    (pre suffix rest : List (ℕ × ℝ))
    {a b c d : ℝ} {deep shallow₁ shallow₂ : ℕ}
    (hpairs :
      leafDepthWeights depth tree =
        pre ++ [(deep, c), (deep, d)] ++ suffix)
    (htwoSmallest :
      (leafDepthWeights depth tree).Perm
        ((shallow₁, a) :: (shallow₂, b) :: rest))
    (hab : a ≤ b)
    (hrest : ∀ pair ∈ rest, b ≤ pair.2)
    (hdepth₁ : shallow₁ ≤ deep) (hdepth₂ : shallow₂ ≤ deep) :
    ∃ swappedTree : InsertionScheduleTree,
      ∃ pairPre pairSuffix : List (ℕ × ℝ),
        weightedLeafDepthCost depth swappedTree ≤
            weightedLeafDepthCost depth tree ∧
          swappedTree.leaves.Perm tree.leaves ∧
            (leafDepthWeights depth swappedTree =
                pairPre ++ [(deep, a), (deep, b)] ++ pairSuffix ∨
              leafDepthWeights depth swappedTree =
                pairPre ++ [(deep, b), (deep, a)] ++ pairSuffix) := by
  have hfirst_mem :
      (shallow₁, a) ∈ pre ++ [(deep, c), (deep, d)] ++ suffix := by
    have hmem : (shallow₁, a) ∈ leafDepthWeights depth tree :=
      (htwoSmallest.mem_iff).2 (by simp)
    simpa [hpairs] using hmem
  obtain hloc :=
    exists_selected_relative_to_adjacent_pair
      pre suffix (deep, c) (deep, d) (shallow₁, a) hfirst_mem
  rcases hloc with hbefore | hleftFirst | hrightFirst | hafter
  · obtain ⟨before, middle, _hpre, hpairsDisplay⟩ := hbefore
    have hpairs' :
        leafDepthWeights depth tree =
          before ++ [(shallow₁, a)] ++ middle ++
            [(deep, c), (deep, d)] ++ suffix := by
      rw [hpairs, hpairsDisplay]
    by_cases hleftSecond : (shallow₂, b) = (deep, c)
    · cases hleftSecond
      obtain ⟨swappedTree, hcost, hleaves, hrealized⟩ :=
        exists_tree_for_left_deepest_second_two_smallest_before_deepest_decomposition_eq
          before middle suffix rest hpairs' htwoSmallest hab hrest hdepth₁
      refine ⟨swappedTree,
        before ++ [(shallow₁, d)] ++ middle, suffix, hcost, hleaves, ?_⟩
      right
      simpa [List.append_assoc] using hrealized
    · by_cases hrightSecond : (shallow₂, b) = (deep, d)
      · cases hrightSecond
        obtain ⟨swappedTree, hcost, hleaves, hrealized⟩ :=
          exists_tree_for_right_deepest_second_two_smallest_before_deepest_decomposition_eq
            before middle suffix rest hpairs' htwoSmallest hab hrest hdepth₁
        refine ⟨swappedTree,
          before ++ [(shallow₁, c)] ++ middle, suffix, hcost, hleaves, ?_⟩
        left
        simpa [List.append_assoc] using hrealized
      · obtain hsecondLoc :=
          exists_second_position_of_first_before_adjacent_pair
            (pairs := leafDepthWeights depth tree) (rest := rest)
            (first := (shallow₁, a)) (second := (shallow₂, b))
            (left := (deep, c)) (right := (deep, d))
            before middle suffix hpairs' htwoSmallest
            hleftSecond hrightSecond
        rcases hsecondLoc with hsecondBefore | hsecondMiddle | hsecondAfter
        · obtain ⟨pre₂, gap, _hbefore, hpairs''⟩ := hsecondBefore
          obtain ⟨swappedTree, hcost, hleaves, hrealized⟩ :=
            exists_tree_for_two_pair_exchange_reverse_before_deepest_of_two_smallest_decomposition_eq
              pre₂ gap middle suffix rest
              (by simpa [List.append_assoc] using hpairs'')
              htwoSmallest hab hrest hdepth₁ hdepth₂
          refine ⟨swappedTree,
            pre₂ ++ [(shallow₂, d)] ++ gap ++ [(shallow₁, c)] ++ middle,
            suffix, hcost, hleaves, ?_⟩
          left
          simpa [List.append_assoc] using hrealized
        · obtain ⟨gap, tail, _hmiddle, hpairs''⟩ := hsecondMiddle
          obtain ⟨swappedTree, hcost, hleaves, hrealized⟩ :=
            exists_tree_for_two_pair_exchange_before_deepest_of_two_smallest_decomposition_eq
              before gap tail suffix rest
              (by simpa [List.append_assoc] using hpairs'')
              htwoSmallest hab hrest hdepth₁ hdepth₂
          refine ⟨swappedTree,
            before ++ [(shallow₁, c)] ++ gap ++ [(shallow₂, d)] ++ tail,
            suffix, hcost, hleaves, ?_⟩
          left
          simpa [List.append_assoc] using hrealized
        · obtain ⟨gap, tail, _hsuffix, hpairs''⟩ := hsecondAfter
          obtain ⟨swappedTree, hcost, hleaves, hrealized⟩ :=
            exists_tree_for_two_pair_exchange_around_deepest_of_two_smallest_decomposition_eq
              before middle gap tail rest
              (by simpa [List.append_assoc] using hpairs'')
              htwoSmallest hab hrest hdepth₁ hdepth₂
          refine ⟨swappedTree,
            before ++ [(shallow₁, c)] ++ middle,
            gap ++ [(shallow₂, d)] ++ tail, hcost, hleaves, ?_⟩
          left
          simpa [List.append_assoc] using hrealized
  · cases hleftFirst
    have hpairsFront :
        (leafDepthWeights depth tree).Perm
          ((deep, a) :: pre ++ [(deep, d)] ++ suffix) := by
      rw [hpairs]
      simp only [List.append_assoc, List.cons_append]
      exact List.perm_middle (a := (deep, a)) (l₁ := pre)
        (l₂ := (deep, d) :: suffix)
    have htailPerm :
        (pre ++ [(deep, d)] ++ suffix).Perm ((shallow₂, b) :: rest) :=
      List.Perm.cons_inv (hpairsFront.symm.trans htwoSmallest)
    have hsecond_mem : (shallow₂, b) ∈ pre ++ [(deep, d)] ++ suffix :=
      (htailPerm.mem_iff).2 (by simp)
    simp [List.mem_append] at hsecond_mem
    rcases hsecond_mem with hpre | hrightSecond | hsuffix
    · obtain ⟨before, middle, hsplit⟩ :=
        exists_split_of_mem pre hpre
      have hpairs' :
          leafDepthWeights depth tree =
            before ++ [(shallow₂, b)] ++ middle ++
              [(deep, a), (deep, d)] ++ suffix := by
        rw [hpairs, hsplit]
        simp [List.append_assoc]
      obtain ⟨swappedTree, hcost, hleaves, hrealized⟩ :=
        exists_tree_for_left_deepest_two_smallest_before_deepest_decomposition_eq
          before middle suffix rest hpairs' htwoSmallest hrest hdepth₂
      refine ⟨swappedTree, before ++ [(shallow₂, d)] ++ middle, suffix,
        hcost, hleaves, ?_⟩
      left
      simpa [List.append_assoc] using hrealized
    · have hb_eq_d : b = d := hrightSecond.2
      obtain ⟨swappedTree, hcost, hleaves, hrealized⟩ :=
        exists_tree_for_deepest_pair_noop_eq pre suffix hpairs
      refine ⟨swappedTree, pre, suffix, hcost, hleaves, ?_⟩
      left
      rw [hb_eq_d]
      simpa using hrealized
    · obtain ⟨middle, after, hsplit⟩ :=
        exists_split_of_mem suffix hsuffix
      have hpairs' :
          leafDepthWeights depth tree =
            pre ++ [(deep, a), (deep, d)] ++ middle ++
              [(shallow₂, b)] ++ after := by
        rw [hpairs, hsplit]
        simp [List.append_assoc]
      obtain ⟨swappedTree, hcost, hleaves, hrealized⟩ :=
        exists_tree_for_left_deepest_two_smallest_decomposition_eq
          pre middle after rest hpairs' htwoSmallest hrest hdepth₂
      refine ⟨swappedTree, pre, middle ++ [(shallow₂, d)] ++ after,
        hcost, hleaves, ?_⟩
      left
      simpa [List.append_assoc] using hrealized
  · cases hrightFirst
    have hpairsFront :
        (leafDepthWeights depth tree).Perm
          ((deep, a) :: pre ++ [(deep, c)] ++ suffix) := by
      rw [hpairs]
      simpa [List.append_assoc] using
        (List.perm_middle (a := (deep, a)) (l₁ := pre ++ [(deep, c)])
          (l₂ := suffix))
    have htailPerm :
        (pre ++ [(deep, c)] ++ suffix).Perm ((shallow₂, b) :: rest) :=
      List.Perm.cons_inv (hpairsFront.symm.trans htwoSmallest)
    have hsecond_mem : (shallow₂, b) ∈ pre ++ [(deep, c)] ++ suffix :=
      (htailPerm.mem_iff).2 (by simp)
    simp [List.mem_append] at hsecond_mem
    rcases hsecond_mem with hpre | hleftSecond | hsuffix
    · obtain ⟨before, middle, hsplit⟩ :=
        exists_split_of_mem pre hpre
      have hpairs' :
          leafDepthWeights depth tree =
            before ++ [(shallow₂, b)] ++ middle ++
              [(deep, c), (deep, a)] ++ suffix := by
        rw [hpairs, hsplit]
        simp [List.append_assoc]
      obtain ⟨swappedTree, hcost, hleaves, hrealized⟩ :=
        exists_tree_for_right_deepest_two_smallest_before_deepest_decomposition_eq
          before middle suffix rest hpairs' htwoSmallest hrest hdepth₂
      refine ⟨swappedTree, before ++ [(shallow₂, c)] ++ middle, suffix,
        hcost, hleaves, ?_⟩
      right
      simpa [List.append_assoc] using hrealized
    · have hb_eq_c : b = c := hleftSecond.2
      obtain ⟨swappedTree, hcost, hleaves, hrealized⟩ :=
        exists_tree_for_deepest_pair_noop_eq pre suffix hpairs
      refine ⟨swappedTree, pre, suffix, hcost, hleaves, ?_⟩
      right
      rw [hb_eq_c]
      simpa using hrealized
    · obtain ⟨middle, after, hsplit⟩ :=
        exists_split_of_mem suffix hsuffix
      have hpairs' :
          leafDepthWeights depth tree =
            pre ++ [(deep, c), (deep, a)] ++ middle ++
              [(shallow₂, b)] ++ after := by
        rw [hpairs, hsplit]
        simp [List.append_assoc]
      obtain ⟨swappedTree, hcost, hleaves, hrealized⟩ :=
        exists_tree_for_right_deepest_two_smallest_decomposition_eq
          pre middle after rest hpairs' htwoSmallest hrest hdepth₂
      refine ⟨swappedTree, pre, middle ++ [(shallow₂, c)] ++ after,
        hcost, hleaves, ?_⟩
      right
      simpa [List.append_assoc] using hrealized
  · obtain ⟨middle, after, _hsuffix, hpairsDisplay⟩ := hafter
    have hpairs' :
        leafDepthWeights depth tree =
          pre ++ [(deep, c), (deep, d)] ++ middle ++
            [(shallow₁, a)] ++ after := by
      rw [hpairs, hpairsDisplay]
    by_cases hleftSecond : (shallow₂, b) = (deep, c)
    · cases hleftSecond
      obtain ⟨swappedTree, hcost, hleaves, hrealized⟩ :=
        exists_tree_for_left_deepest_second_two_smallest_decomposition_eq
          pre middle after rest hpairs' htwoSmallest hab hrest hdepth₁
      refine ⟨swappedTree, pre, middle ++ [(shallow₁, d)] ++ after,
        hcost, hleaves, ?_⟩
      right
      simpa [List.append_assoc] using hrealized
    · by_cases hrightSecond : (shallow₂, b) = (deep, d)
      · cases hrightSecond
        obtain ⟨swappedTree, hcost, hleaves, hrealized⟩ :=
          exists_tree_for_right_deepest_second_two_smallest_decomposition_eq
            pre middle after rest hpairs' htwoSmallest hab hrest hdepth₁
        refine ⟨swappedTree, pre, middle ++ [(shallow₁, c)] ++ after,
          hcost, hleaves, ?_⟩
        left
        simpa [List.append_assoc] using hrealized
      · obtain hsecondLoc :=
          exists_second_position_of_first_after_adjacent_pair
            (pairs := leafDepthWeights depth tree) (rest := rest)
            (first := (shallow₁, a)) (second := (shallow₂, b))
            (left := (deep, c)) (right := (deep, d))
            pre middle after hpairs' htwoSmallest
            hleftSecond hrightSecond
        rcases hsecondLoc with hsecondBefore | hsecondMiddle | hsecondAfter
        · obtain ⟨pre₂, gap, _hpre, hpairs''⟩ := hsecondBefore
          obtain ⟨swappedTree, hcost, hleaves, hrealized⟩ :=
            exists_tree_for_two_pair_exchange_reverse_around_deepest_of_two_smallest_decomposition_eq
              pre₂ gap middle after rest
              (by simpa [List.append_assoc] using hpairs'')
              htwoSmallest hab hrest hdepth₁ hdepth₂
          refine ⟨swappedTree,
            pre₂ ++ [(shallow₂, d)] ++ gap,
            middle ++ [(shallow₁, c)] ++ after, hcost, hleaves, ?_⟩
          left
          simpa [List.append_assoc] using hrealized
        · obtain ⟨gap, tail, _hmiddle, hpairs''⟩ := hsecondMiddle
          obtain ⟨swappedTree, hcost, hleaves, hrealized⟩ :=
            exists_tree_for_two_pair_exchange_reverse_of_two_smallest_decomposition_eq
              pre gap tail after rest
              (by simpa [List.append_assoc] using hpairs'')
              htwoSmallest hab hrest hdepth₁ hdepth₂
          refine ⟨swappedTree, pre,
            gap ++ [(shallow₂, d)] ++ tail ++ [(shallow₁, c)] ++ after,
            hcost, hleaves, ?_⟩
          left
          simpa [List.append_assoc] using hrealized
        · obtain ⟨gap, tail, _hafter, hpairs''⟩ := hsecondAfter
          obtain ⟨swappedTree, hcost, hleaves, hrealized⟩ :=
            exists_tree_for_two_pair_exchange_of_two_smallest_decomposition_eq
              pre middle gap tail rest
              (by simpa [List.append_assoc] using hpairs'')
              htwoSmallest hab hrest hdepth₁ hdepth₂
          refine ⟨swappedTree, pre,
            middle ++ [(shallow₁, c)] ++ gap ++ [(shallow₂, d)] ++ tail,
            hcost, hleaves, ?_⟩
          left
          simpa [List.append_assoc] using hrealized

/-- Tree-level deepest-pair placement for the two smallest weights.  Every
nontrivial schedule can be relabeled, without increasing weighted external path
cost or changing the leaf multiset, so that a maximum-depth sibling pair
contains the two smallest leaf weights. -/
theorem exists_tree_with_two_smallest_at_deepest_pair
    (depth : ℕ) (tree : InsertionScheduleTree)
    (hcount : 1 < tree.leafCount) :
    ∃ depth₁ : ℕ, ∃ a : ℝ, ∃ depth₂ : ℕ, ∃ b : ℝ,
      ∃ rest : List (ℕ × ℝ),
        ∃ swappedTree : InsertionScheduleTree,
          ∃ pairPre pairSuffix : List (ℕ × ℝ),
            (leafDepthWeights depth tree).Perm
                ((depth₁, a) :: (depth₂, b) :: rest) ∧
              a ≤ b ∧
                (∀ pair ∈ rest, b ≤ pair.2) ∧
                  weightedLeafDepthCost depth swappedTree ≤
                      weightedLeafDepthCost depth tree ∧
                    swappedTree.leaves.Perm tree.leaves ∧
                      (leafDepthWeights depth swappedTree =
                          pairPre ++
                            [(maxLeafDepth depth tree, a),
                              (maxLeafDepth depth tree, b)] ++
                              pairSuffix ∨
                        leafDepthWeights depth swappedTree =
                          pairPre ++
                            [(maxLeafDepth depth tree, b),
                              (maxLeafDepth depth tree, a)] ++
                              pairSuffix) := by
  have hlen : 2 ≤ (leafDepthWeights depth tree).length := by
    rw [leafDepthWeights_length]
    exact hcount
  obtain ⟨depth₁, a, depth₂, b, rest, htwoSmallest, hab, hrest⟩ :=
    exists_two_smallest_weight_decomposition_components
      (leafDepthWeights depth tree) hlen
  obtain ⟨pre, suffix, c, d, hdeepPair⟩ :=
    exists_deepest_sibling_leaf_pair depth tree hcount
  have hfirst_mem : (depth₁, a) ∈ leafDepthWeights depth tree :=
    (htwoSmallest.mem_iff).2 (by simp)
  have hsecond_mem : (depth₂, b) ∈ leafDepthWeights depth tree :=
    (htwoSmallest.mem_iff).2 (by simp)
  have hdepth₁ : depth₁ ≤ maxLeafDepth depth tree :=
    leafDepthWeights_depth_le_maxLeafDepth depth tree (depth₁, a) hfirst_mem
  have hdepth₂ : depth₂ ≤ maxLeafDepth depth tree :=
    leafDepthWeights_depth_le_maxLeafDepth depth tree (depth₂, b) hsecond_mem
  obtain ⟨swappedTree, pairPre, pairSuffix, hcost, hleaves,
      hdisplay⟩ :=
    exists_tree_for_two_smallest_deepest_pair_anywhere_pair_witness
      pre suffix rest hdeepPair htwoSmallest hab hrest hdepth₁ hdepth₂
  exact ⟨depth₁, a, depth₂, b, rest, swappedTree, pairPre, pairSuffix,
    htwoSmallest, hab, hrest, hcost, hleaves, hdisplay⟩

/-- A schedule with nonnegative leaves has nonnegative exact value. -/
theorem exactEval_nonneg_of_leaves_nonnegative
    (tree : InsertionScheduleTree)
    (hnonneg : ∀ x ∈ tree.leaves, 0 ≤ x) :
    0 ≤ tree.exactEval := by
  induction tree with
  | leaf x =>
      simpa [exactEval, leaves] using hnonneg x (by simp)
  | node left right ihl ihr =>
      have hleft : ∀ x ∈ left.leaves, 0 ≤ x := by
        intro x hx
        exact hnonneg x (by simp [leaves, hx])
      have hright : ∀ x ∈ right.leaves, 0 ≤ x := by
        intro x hx
        exact hnonneg x (by simp [leaves, hx])
      simpa [exactEval] using add_nonneg (ihl hleft) (ihr hright)

/-- For nonnegative left and right subtrees, the node's exact absolute
intermediate sum is just the unsigned exact intermediate sum. -/
theorem exactMergeCost_node_of_nonnegative
    (left right : InsertionScheduleTree)
    (hleft : ∀ x ∈ left.leaves, 0 ≤ x)
    (hright : ∀ x ∈ right.leaves, 0 ≤ x) :
    (node left right).exactMergeCost =
      left.exactMergeCost + right.exactMergeCost +
        (left.exactEval + right.exactEval) := by
  have hl := exactEval_nonneg_of_leaves_nonnegative left hleft
  have hr := exactEval_nonneg_of_leaves_nonnegative right hright
  simp [exactMergeCost, abs_of_nonneg (add_nonneg hl hr)]

/-- For nonnegative leaves, exact merge cost is the weighted external path
length of the schedule tree.  This is the weighted-path-length form of the
printed p. 83 insertion optimality objective. -/
theorem exactMergeCost_eq_weightedLeafDepthCost_of_leaves_nonnegative
    (tree : InsertionScheduleTree)
    (hnonneg : ∀ x ∈ tree.leaves, 0 ≤ x) :
    tree.exactMergeCost = weightedLeafDepthCost 0 tree := by
  induction tree with
  | leaf x =>
      simp [exactMergeCost, weightedLeafDepthCost]
  | node left right ihl ihr =>
      have hleft : ∀ x ∈ left.leaves, 0 ≤ x := by
        intro x hx
        exact hnonneg x (by simp [leaves, hx])
      have hright : ∀ x ∈ right.leaves, 0 ≤ x := by
        intro x hx
        exact hnonneg x (by simp [leaves, hx])
      rw [exactMergeCost_node_of_nonnegative left right hleft hright,
        ihl hleft, ihr hright]
      simp [weightedLeafDepthCost,
        weightedLeafDepthCost_succ_eq_add_exactEval 0 left,
        weightedLeafDepthCost_succ_eq_add_exactEval 0 right]
      ring

/-- Exact-merge-cost form of the greedy insertion optimality theorem for
nonnegative leaves. -/
theorem exists_greedyInsertionTree_exactMergeCost_le
    (tree : InsertionScheduleTree)
    (hnonneg : ∀ x ∈ tree.leaves, 0 ≤ x) :
    ∃ greedyTree : InsertionScheduleTree,
      GreedyInsertionTree greedyTree ∧
        greedyTree.leaves.Perm tree.leaves ∧
          greedyTree.exactMergeCost ≤ tree.exactMergeCost := by
  obtain ⟨greedyTree, hgreedy, hleaves, hcost⟩ :=
    exists_greedyInsertionTree_weightedLeafDepthCost_le 0 tree hnonneg
  have hgreedyNonneg : ∀ x ∈ greedyTree.leaves, 0 ≤ x := by
    intro x hx
    exact hnonneg x ((hleaves.mem_iff).1 hx)
  refine ⟨greedyTree, hgreedy, hleaves, ?_⟩
  rw [exactMergeCost_eq_weightedLeafDepthCost_of_leaves_nonnegative
      greedyTree hgreedyNonneg,
    exactMergeCost_eq_weightedLeafDepthCost_of_leaves_nonnegative
      tree hnonneg]
  exact hcost

/-- Supplied-greedy exact-merge-cost optimality for nonnegative leaves. -/
theorem GreedyInsertionTree.exactMergeCost_le
    {greedy other : InsertionScheduleTree}
    (hgreedy : GreedyInsertionTree greedy)
    (hperm : greedy.leaves.Perm other.leaves)
    (hnonneg : ∀ x ∈ greedy.leaves, 0 ≤ x) :
    greedy.exactMergeCost ≤ other.exactMergeCost := by
  have hotherNonneg : ∀ x ∈ other.leaves, 0 ≤ x := by
    intro x hx
    exact hnonneg x ((hperm.mem_iff).2 hx)
  rw [exactMergeCost_eq_weightedLeafDepthCost_of_leaves_nonnegative
      greedy hnonneg,
    exactMergeCost_eq_weightedLeafDepthCost_of_leaves_nonnegative
      other hotherNonneg]
  exact GreedyInsertionTree.weightedLeafDepthCost_le hgreedy 0 hperm hnonneg

/-- Exact arithmetic evaluates a list-shaped insertion schedule to its exact
real value. -/
theorem eval_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 ≤ u0) :
    (tree : InsertionScheduleTree) →
      tree.eval (FPModel.exactWithUnitRoundoff u0 hu0) = tree.exactEval
  | leaf x => by
      simp [eval, exactEval]
  | node left right => by
      change
        (FPModel.exactWithUnitRoundoff u0 hu0).fl_add
          (left.eval (FPModel.exactWithUnitRoundoff u0 hu0))
          (right.eval (FPModel.exactWithUnitRoundoff u0 hu0)) =
        left.exactEval + right.exactEval
      rw [eval_exactWithUnitRoundoff u0 hu0 left,
        eval_exactWithUnitRoundoff u0 hu0 right]
      simp [FPModel.exactWithUnitRoundoff]

/-- Under exact arithmetic, the dependent `SumTree` converted from a
list-shaped insertion schedule evaluates to the schedule's exact real value. -/
theorem toSumTree_eval_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 ≤ u0) (tree : InsertionScheduleTree) :
      SumTree.eval (FPModel.exactWithUnitRoundoff u0 hu0)
        tree.toSumTree tree.leafVector = tree.exactEval := by
  rw [toSumTree_eval (FPModel.exactWithUnitRoundoff u0 hu0) tree]
  exact eval_exactWithUnitRoundoff u0 hu0 tree

/-- Under exact arithmetic, the dependent `SumTree` running-error budget of a
converted insertion schedule is exactly its exact merge cost. -/
theorem toSumTree_runningErrorBudget_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 ≤ u0) :
    (tree : InsertionScheduleTree) →
      SumTree.runningErrorBudget (FPModel.exactWithUnitRoundoff u0 hu0)
        tree.toSumTree tree.leafVector = tree.exactMergeCost
  | leaf x => by
      simp [toSumTree, leafVector, exactMergeCost,
        SumTree.runningErrorBudget]
  | node left right => by
      simp [toSumTree, leafVector, exactMergeCost,
        SumTree.runningErrorBudget, SumTree.eval]
      rw [toSumTree_runningErrorBudget_exactWithUnitRoundoff u0 hu0 left,
        toSumTree_runningErrorBudget_exactWithUnitRoundoff u0 hu0 right,
        toSumTree_eval_exactWithUnitRoundoff u0 hu0 left,
        toSumTree_eval_exactWithUnitRoundoff u0 hu0 right]
      simp [FPModel.exactWithUnitRoundoff]

end InsertionScheduleTree

end NumStability
