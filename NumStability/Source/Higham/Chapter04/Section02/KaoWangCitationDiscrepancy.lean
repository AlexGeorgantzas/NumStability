import NumStability.Algorithms.Summation.Insertion.RunningError

namespace NumStability

/-!
# Higham Section 4.2: the Kao--Wang citation discrepancy

Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., Chapter 4,
p. 82, says that minimizing the running bound (4.3) is NP-hard and cites
Kao--Wang (2000).  The cited paper proves a precise but different statement:
its input is a multiset of nonzero integers, its search space is all binary
addition trees, and its cost is the sum of the absolute values of the *exact*
internal-node sums.

This file fixes the mathematical scope of that citation.  It gives a
computable integer-tree version of Kao--Wang's MAT/AT objective, embeds it into
the Chapter 4 `InsertionScheduleTree` model, and proves that it agrees with
Higham's (4.3) budget in exact arithmetic.  It also gives a standard-model
witness showing that the exact cost and the rounded (4.3) budget are not the
same objective for a general `FPModel`.

No NP-hardness theorem is asserted here.  The literal sentence in Higham is
not a uniquely formalizable complexity statement: (4.3) contains computed
intermediate sums, but the book fixes neither a floating-point format/model
nor an encoded decision problem, while Kao--Wang proves hardness for a
different exact-integer objective.  The discrepancy theorem below makes that
scope mismatch explicit.  The exact reduction proposition at the end records
the paper-level theorem one would use only after separately choosing an
encoding and a complexity framework; it is not assumed and is not silently
reported as a proof of the printed computed-bound claim.
-/

namespace HighamChapter4KaoWang

/-! ## The exact integer addition-tree problem of Kao--Wang -/

/-- A leaf-labelled full binary addition tree over integer data.

Unlike recursive summation, both children of a node may themselves be
nontrivial trees.  Thus this is the general Algorithm 4.1 search space used by
Kao--Wang's MINIMUM ADDITION TREE problem. -/
inductive IntegerAdditionTree where
  | leaf (x : ℤ) : IntegerAdditionTree
  | node (left right : IntegerAdditionTree) : IntegerAdditionTree
  deriving DecidableEq, Repr

namespace IntegerAdditionTree

/-- Exact integer value at the root. -/
def value : IntegerAdditionTree → ℤ
  | leaf x => x
  | node left right => left.value + right.value

/-- Leaf labels, preserving occurrences and left-to-right order. -/
def leaves : IntegerAdditionTree → List ℤ
  | leaf x => [x]
  | node left right => left.leaves ++ right.leaves

/-- Kao--Wang's exact addition-tree cost `C(T)`.

Each internal node contributes the absolute value of its exact integer sum.
The root is included; when the total sum is zero its contribution is zero. -/
def cost : IntegerAdditionTree → ℕ
  | leaf _ => 0
  | node left right =>
      left.cost + right.cost + (left.value + right.value).natAbs

/-- Embed an integer addition tree into the existing Chapter 4 real schedule
model without changing its shape or leaf labelling. -/
def toSchedule : IntegerAdditionTree → InsertionScheduleTree
  | leaf x => .leaf (x : ℝ)
  | node left right => .node left.toSchedule right.toSchedule

@[simp] theorem value_leaf (x : ℤ) : (leaf x).value = x := rfl

@[simp] theorem value_node (left right : IntegerAdditionTree) :
    (node left right).value = left.value + right.value := rfl

@[simp] theorem leaves_leaf (x : ℤ) : (leaf x).leaves = [x] := rfl

@[simp] theorem leaves_node (left right : IntegerAdditionTree) :
    (node left right).leaves = left.leaves ++ right.leaves := rfl

@[simp] theorem cost_leaf (x : ℤ) : (leaf x).cost = 0 := rfl

@[simp] theorem cost_node (left right : IntegerAdditionTree) :
    (node left right).cost =
      left.cost + right.cost + (left.value + right.value).natAbs := rfl

@[simp] theorem toSchedule_leaves (tree : IntegerAdditionTree) :
    tree.toSchedule.leaves = tree.leaves.map (fun x : ℤ => (x : ℝ)) := by
  induction tree with
  | leaf x => simp [toSchedule]
  | node left right ihLeft ihRight =>
      simp [toSchedule, ihLeft, ihRight]

@[simp] theorem toSchedule_exactEval (tree : IntegerAdditionTree) :
    tree.toSchedule.exactEval = (tree.value : ℝ) := by
  induction tree with
  | leaf x => simp [toSchedule]
  | node left right ihLeft ihRight =>
      simp [toSchedule, ihLeft, ihRight]

/-- The real exact-merge cost already used by the Chapter 4 insertion analysis
is precisely the cast of Kao--Wang's integer cost. -/
@[simp] theorem toSchedule_exactMergeCost (tree : IntegerAdditionTree) :
    tree.toSchedule.exactMergeCost = (tree.cost : ℝ) := by
  induction tree with
  | leaf x => simp [toSchedule]
  | node left right ihLeft ihRight =>
      simp [toSchedule, ihLeft, ihRight, Nat.cast_natAbs]

end IntegerAdditionTree

/-- The tree realizes the input multiset when its leaf list is a permutation
of that input list. -/
def Realizes (tree : IntegerAdditionTree) (input : List ℤ) : Prop :=
  tree.leaves.Perm input

/-- Kao--Wang's ADDITION TREE (AT) decision relation.

The paper takes `input` to contain nonzero integers and asks whether some
general binary addition tree has exact cost at most `threshold`.  Nonzeroness
is a domain restriction on instances, not smuggled into this pure relation. -/
def AdditionTreeDecision (input : List ℤ) (threshold : ℕ) : Prop :=
  ∃ tree : IntegerAdditionTree,
    Realizes tree input ∧ tree.cost ≤ threshold

/-- A MAT output: a realizing tree whose exact cost is no larger than the cost
of every other realizing general binary tree. -/
def IsMinimumAdditionTree (input : List ℤ)
    (tree : IntegerAdditionTree) : Prop :=
  Realizes tree input ∧
    ∀ other : IntegerAdditionTree,
      Realizes other input → tree.cost ≤ other.cost

/-! ## General Algorithm 4.1 trees are not recursive orderings -/

/-- The comb-shaped subclass arising from recursive summation in some order.
At each nontrivial addition, at least one child is a source leaf. -/
inductive IsRecursiveOrderTree : IntegerAdditionTree → Prop where
  | leaf (x : ℤ) : IsRecursiveOrderTree (.leaf x)
  | addLeft (x : ℤ) {tree : IntegerAdditionTree}
      (h : IsRecursiveOrderTree tree) :
      IsRecursiveOrderTree (.node (.leaf x) tree)
  | addRight {tree : IntegerAdditionTree} (x : ℤ)
      (h : IsRecursiveOrderTree tree) :
      IsRecursiveOrderTree (.node tree (.leaf x))

/-- The corresponding restricted decision relation for recursive orderings.
This is deliberately separate from Kao--Wang AT. -/
def RecursiveOrderDecision (input : List ℤ) (threshold : ℕ) : Prop :=
  ∃ tree : IntegerAdditionTree,
    Realizes tree input ∧
      IsRecursiveOrderTree tree ∧
        tree.cost ≤ threshold

theorem recursiveOrderDecision_implies_additionTreeDecision
    {input : List ℤ} {threshold : ℕ}
    (h : RecursiveOrderDecision input threshold) :
    AdditionTreeDecision input threshold := by
  rcases h with ⟨tree, hrealizes, _hrecursive, hcost⟩
  exact ⟨tree, hrealizes, hcost⟩

/-- A four-leaf balanced tree is an explicit member of the general AT search
space that is not a recursive-order comb. -/
theorem balancedFour_not_recursive (a b c d : ℤ) :
    ¬ IsRecursiveOrderTree
      (.node (.node (.leaf a) (.leaf b))
        (.node (.leaf c) (.leaf d))) := by
  intro h
  cases h

/-! ## Bridge to Higham (4.3) and a scope-discrepancy witness -/

/-- In exact arithmetic, Higham's running budget `sum |\hat T_i|` is the
Kao--Wang exact integer cost.  This is the precise first-order bridge behind
the citation on p. 82. -/
theorem higham43_runningBudget_exactArithmetic_eq_kaoWangCost
    (u0 : ℝ) (hu0 : 0 ≤ u0) (tree : IntegerAdditionTree) :
    SumTree.runningErrorBudget (FPModel.exactWithUnitRoundoff u0 hu0)
        tree.toSchedule.toSumTree tree.toSchedule.leafVector =
      (tree.cost : ℝ) := by
  rw [InsertionScheduleTree.toSumTree_runningErrorBudget_exactWithUnitRoundoff]
  exact IntegerAdditionTree.toSchedule_exactMergeCost tree

/-- A valid abstract standard-model arithmetic whose nonzero-left additions
have relative error `1/2`.  It is used only to separate the rounded (4.3)
objective from the exact Kao--Wang objective; it is not claimed to be a
concrete hardware format. -/
noncomputable def halfBiasedAddModel : FPModel where
  u := 1 / 2
  u_nonneg := by norm_num
  fl_add := fun x y => if x = 0 then y else (x + y) * (1 + 1 / 2)
  fl_sub := fun x y => x - y
  fl_mul := fun x y => x * y
  fl_div := fun x y => x / y
  fl_sqrt := fun x => Real.sqrt x
  fl_add_zero := by
    intro x
    simp
  model_add := by
    intro x y
    by_cases hx : x = 0
    · refine ⟨0, by norm_num, ?_⟩
      simp [hx]
    · refine ⟨1 / 2, by norm_num, ?_⟩
      simp [hx]
  model_sub := by
    intro x y
    refine ⟨0, by norm_num, ?_⟩
    ring
  model_mul := by
    intro x y
    refine ⟨0, by norm_num, ?_⟩
    ring
  model_div := by
    intro x y _hy
    refine ⟨0, by norm_num, ?_⟩
    ring
  model_sqrt := by
    intro x _hx
    refine ⟨0, by norm_num, ?_⟩
    ring

/-- The smallest nontrivial witness: the exact internal sum is `2`, while the
rounded internal sum in `halfBiasedAddModel` is `3`. -/
def twoOnes : IntegerAdditionTree :=
  .node (.leaf 1) (.leaf 1)

@[simp] theorem twoOnes_cost : twoOnes.cost = 2 := by
  norm_num [twoOnes, IntegerAdditionTree.cost,
    IntegerAdditionTree.value]

theorem twoOnes_higham43_runningBudget_halfBiased :
    SumTree.runningErrorBudget halfBiasedAddModel
        twoOnes.toSchedule.toSumTree twoOnes.toSchedule.leafVector = 3 := by
  have hshape : twoOnes.toSchedule.toSumTree =
      SumTree.node SumTree.leaf SumTree.leaf := rfl
  have hvector : twoOnes.toSchedule.leafVector =
      (fun _ : Fin 2 => (1 : ℝ)) := by
    funext i
    rw [InsertionScheduleTree.leafVector_eq_leaves_get]
    fin_cases i <;>
      simp [twoOnes, IntegerAdditionTree.toSchedule,
        InsertionScheduleTree.leaves,
        InsertionScheduleTree.leafCount]
  rw [hshape, hvector]
  norm_num [SumTree.runningErrorBudget, SumTree.eval, halfBiasedAddModel]
  exact abs_of_nonneg (Nat.cast_nonneg 3)

/-- Formal semantic discrepancy: the objective proved hard by Kao--Wang is
not Higham's rounded (4.3) objective for an arbitrary standard-model
arithmetic. -/
theorem higham43_computedBudget_ne_kaoWangExactCost_witness :
    SumTree.runningErrorBudget halfBiasedAddModel
        twoOnes.toSchedule.toSumTree twoOnes.toSchedule.leafVector ≠
      (twoOnes.cost : ℝ) := by
  rw [twoOnes_higham43_runningBudget_halfBiased, twoOnes_cost]
  norm_num

/-! ## Optional exact Kao--Wang reduction target (not assumed) -/

/-- A certificate for the decision version of 3-PARTITION, stated on a list
so repeated integers are preserved. -/
def IsThreePartition (numbers : List ℕ) (m K : ℕ) : Prop :=
  ∃ blocks : List (List ℕ),
    blocks.length = m ∧
      blocks.flatten.Perm numbers ∧
        ∀ block ∈ blocks, block.length = 3 ∧ block.sum = K

/-- Source instance restrictions used in Kao--Wang §2.  The inequalities are
written without natural-number division: `K/4 < b < K/2` becomes
`K < 4*b` and `2*b < K`. -/
def IsThreePartitionInstance (numbers : List ℕ) (m K : ℕ) : Prop :=
  0 < m ∧ 0 < K ∧
    numbers.length = 3 * m ∧
      numbers.sum = m * K ∧
        ∀ b ∈ numbers, K < 4 * b ∧ 2 * b < K

/-- `W = 100(5m)^2 K` from Kao--Wang's reduction. -/
def reductionW (m K : ℕ) : ℕ := 100 * (5 * m) ^ 2 * K

/-- `A = {b_i + W}`. -/
def reductionA (numbers : List ℕ) (m K : ℕ) : List ℕ :=
  numbers.map (fun b => b + reductionW m K)

/-- `L = 3W + K`. -/
def reductionL (m K : ℕ) : ℕ := 3 * reductionW m K + K

/-- `h = floor(4 ε L)`, where `ε = 1/(400(5m)^2)`.

For natural inputs the floor is exactly the displayed natural quotient. -/
def reductionh (m K : ℕ) : ℕ :=
  (4 * reductionL m K) / (400 * (5 * m) ^ 2)

/-- `H = L + h`. -/
def reductionH (m K : ℕ) : ℕ := reductionL m K + reductionh m K

/-- The AT multiset
`X = A ∪ m copies of (-H) ∪ m copies of h`, represented as a list. -/
def reductionX (numbers : List ℕ) (m K : ℕ) : List ℤ :=
  (reductionA numbers m K).map (fun a => (a : ℤ)) ++
    List.replicate m (-((reductionH m K : ℕ) : ℤ)) ++
      List.replicate m ((reductionh m K : ℕ) : ℤ)

/-- The AT threshold `m(H+h)` in Lemma 2.10/Theorem 2.11. -/
def reductionThreshold (m K : ℕ) : ℕ :=
  m * (reductionH m K + reductionh m K)

theorem reductionX_length {numbers : List ℕ} {m K : ℕ}
    (hlength : numbers.length = 3 * m) :
    (reductionX numbers m K).length = 5 * m := by
  calc
    (reductionX numbers m K).length =
        (reductionA numbers m K).length + m + m := by
      simp [reductionX, Nat.add_assoc]
    _ = numbers.length + m + m := by
      simp [reductionA]
    _ = 5 * m := by
      rw [hlength]
      omega

/-- The exact mathematical equivalence established by Kao--Wang Lemmas
2.1--2.10 and used in Theorem 2.11.

This is a definition, not a hypothesis or a theorem.  Proving the paper-level
hardness result would additionally require this equivalence, a chosen finite
encoding and polynomial-time framework, and a proof or trusted reuse of
3-PARTITION NP-completeness.  Those choices are absent from Higham's printed
computed-bound sentence, so this definition documents the exact external
specialization rather than pretending that the under-specified source claim
already determines such a theorem. -/
def ReductionCorrect (numbers : List ℕ) (m K : ℕ) : Prop :=
  IsThreePartition numbers m K ↔
    AdditionTreeDecision (reductionX numbers m K)
      (reductionThreshold m K)

end HighamChapter4KaoWang

end NumStability
