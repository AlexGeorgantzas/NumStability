-- Algorithms/Summation/Insertion/ScheduleExecution.lean

import Mathlib.Tactic.Linarith
import NumStability.Algorithms.Summation.Insertion.Executor
import NumStability.Algorithms.Summation.Insertion.RunningError

namespace NumStability

/-!
# Certified execution of insertion schedules

This reusable layer carries schedule trees alongside active computed values and
connects the list executor to greedy schedule, optimality, and `SumTree`
witnesses.
-/

/-- An active insertion-schedule item carries the current computed value and a
binary schedule that evaluates to it. -/
structure InsertionScheduleItem (fp : FPModel) where
  value : ℝ
  tree : InsertionScheduleTree
  eval_eq_value : tree.eval fp = value

namespace InsertionScheduleItem

/-- A source leaf item for the initial active list. -/
def source (fp : FPModel) (x : ℝ) : InsertionScheduleItem fp :=
  { value := x
    tree := InsertionScheduleTree.leaf x
    eval_eq_value := by simp }

@[simp] theorem source_value (fp : FPModel) (x : ℝ) :
    (source fp x).value = x := by
  rfl

@[simp] theorem source_tree (fp : FPModel) (x : ℝ) :
    (source fp x).tree = InsertionScheduleTree.leaf x := by
  rfl

end InsertionScheduleItem

/-- The current computed values carried by insertion-schedule items. -/
def insertionScheduleValues {fp : FPModel}
    (items : List (InsertionScheduleItem fp)) : List ℝ :=
  items.map (fun item => item.value)

/-- The source leaves represented by a list of active insertion-schedule
items. -/
def insertionScheduleLeaves {fp : FPModel}
    (items : List (InsertionScheduleItem fp)) : List ℝ :=
  items.flatMap (fun item => item.tree.leaves)

/-- One active schedule item differs from another by contracting one sibling
leaf pair, while carrying the same computed active value. -/
structure InsertionScheduleItemContract {fp : FPModel} (a b : ℝ)
    (item contracted : InsertionScheduleItem fp) : Prop where
  value_eq : item.value = contracted.value
  tree_contract :
    InsertionScheduleTree.SiblingLeafContract item.tree contracted.tree a b

/-- Two active item lists differ by one contracted active item at the same
position; all other active items are definitionally the same. -/
inductive InsertionScheduleItemsContract {fp : FPModel} (a b : ℝ) :
    List (InsertionScheduleItem fp) → List (InsertionScheduleItem fp) → Prop
  | here {item contracted : InsertionScheduleItem fp} {rest}
      (hitem : InsertionScheduleItemContract a b item contracted) :
      InsertionScheduleItemsContract a b (item :: rest) (contracted :: rest)
  | tail {item : InsertionScheduleItem fp} {rest contractedRest}
      (hrest : InsertionScheduleItemsContract a b rest contractedRest) :
      InsertionScheduleItemsContract a b (item :: rest)
        (item :: contractedRest)

namespace InsertionScheduleItemsContract

theorem values_eq {fp : FPModel} {a b : ℝ}
    {items contractedItems : List (InsertionScheduleItem fp)}
    (hrel : InsertionScheduleItemsContract a b items contractedItems) :
    insertionScheduleValues items =
      insertionScheduleValues contractedItems := by
  induction hrel with
  | here hitem =>
      simp [insertionScheduleValues, hitem.value_eq]
  | tail hrest ih =>
      simpa [insertionScheduleValues] using ih

/-- If the left side of a one-item contraction relation is a singleton, then
the right side is the matching contracted singleton. -/
theorem singleton_left {fp : FPModel} {a b : ℝ}
    {item : InsertionScheduleItem fp}
    {contractedItems : List (InsertionScheduleItem fp)}
    (hrel : InsertionScheduleItemsContract a b [item] contractedItems) :
    ∃ contracted : InsertionScheduleItem fp,
      contractedItems = [contracted] ∧
        InsertionScheduleItemContract a b item contracted := by
  cases hrel with
  | here hitem =>
      exact ⟨_, rfl, hitem⟩
  | tail hrest =>
      cases hrest

end InsertionScheduleItemsContract

/-- Insert an active schedule item according to increasing absolute value of
its current computed value. -/
noncomputable def insertInsertionScheduleItemIncreasingAbs {fp : FPModel}
    (item : InsertionScheduleItem fp) :
    List (InsertionScheduleItem fp) → List (InsertionScheduleItem fp)
  | [] => [item]
  | y :: ys =>
      if |item.value| ≤ |y.value| then
        item :: y :: ys
      else
        y :: insertInsertionScheduleItemIncreasingAbs item ys

/-- Item insertion projects to source-level value insertion. -/
theorem insertInsertionScheduleItemIncreasingAbs_values {fp : FPModel}
    (item : InsertionScheduleItem fp) :
    ∀ items : List (InsertionScheduleItem fp),
      insertionScheduleValues
          (insertInsertionScheduleItemIncreasingAbs item items) =
        insertIncreasingAbs item.value (insertionScheduleValues items)
  | [] => by simp [insertInsertionScheduleItemIncreasingAbs,
      insertionScheduleValues, insertIncreasingAbs]
  | y :: ys => by
      by_cases h : |item.value| ≤ |y.value|
      · simp [insertInsertionScheduleItemIncreasingAbs,
          insertionScheduleValues, insertIncreasingAbs, h]
      · calc
          insertionScheduleValues
              (insertInsertionScheduleItemIncreasingAbs item (y :: ys)) =
            y.value ::
              insertionScheduleValues
                (insertInsertionScheduleItemIncreasingAbs item ys) := by
              simp [insertInsertionScheduleItemIncreasingAbs,
                insertionScheduleValues, h]
          _ = y.value ::
                insertIncreasingAbs item.value
                  (insertionScheduleValues ys) := by
              rw [insertInsertionScheduleItemIncreasingAbs_values item ys]
          _ = insertIncreasingAbs item.value
                (insertionScheduleValues (y :: ys)) := by
              simp [insertIncreasingAbs, insertionScheduleValues, h]

/-- Item insertion only permutes the active schedule items. -/
theorem insertInsertionScheduleItemIncreasingAbs_perm {fp : FPModel}
    (item : InsertionScheduleItem fp) :
    ∀ items : List (InsertionScheduleItem fp),
      (insertInsertionScheduleItemIncreasingAbs item items).Perm
        (item :: items)
  | [] => by simp [insertInsertionScheduleItemIncreasingAbs]
  | y :: ys => by
      by_cases h : |item.value| ≤ |y.value|
      · simp [insertInsertionScheduleItemIncreasingAbs, h]
      · have hrec :=
          insertInsertionScheduleItemIncreasingAbs_perm item ys
        simpa [insertInsertionScheduleItemIncreasingAbs, h] using
          (List.Perm.cons y hrec).trans (List.Perm.swap item y ys)

/-- Inserting two contracted-related active items into the same active list
preserves the one-item contraction relation. -/
theorem insertInsertionScheduleItemIncreasingAbs_contract_item {fp : FPModel}
    {a b : ℝ} {item contracted : InsertionScheduleItem fp}
    (hitem : InsertionScheduleItemContract a b item contracted) :
    ∀ items : List (InsertionScheduleItem fp),
      InsertionScheduleItemsContract a b
        (insertInsertionScheduleItemIncreasingAbs item items)
        (insertInsertionScheduleItemIncreasingAbs contracted items)
  | [] => by
      exact InsertionScheduleItemsContract.here hitem
  | y :: ys => by
      by_cases hle : |item.value| ≤ |y.value|
      · have hle' : |contracted.value| ≤ |y.value| := by
          simpa [← hitem.value_eq] using hle
        simp [insertInsertionScheduleItemIncreasingAbs, hle, hle']
        exact InsertionScheduleItemsContract.here hitem
      · have hle' : ¬ |contracted.value| ≤ |y.value| := by
          simpa [← hitem.value_eq] using hle
        simp [insertInsertionScheduleItemIncreasingAbs, hle, hle']
        exact InsertionScheduleItemsContract.tail
          (insertInsertionScheduleItemIncreasingAbs_contract_item
            hitem ys)

/-- Inserting the same active item into two lists already related by one
contracted active item preserves that relation. -/
theorem insertInsertionScheduleItemIncreasingAbs_contract_list {fp : FPModel}
    {a b : ℝ} (item : InsertionScheduleItem fp) :
    ∀ {items contractedItems : List (InsertionScheduleItem fp)},
      InsertionScheduleItemsContract a b items contractedItems →
      InsertionScheduleItemsContract a b
        (insertInsertionScheduleItemIncreasingAbs item items)
        (insertInsertionScheduleItemIncreasingAbs item contractedItems)
  | _, _, InsertionScheduleItemsContract.here hhead => by
      rename_i head contractedHead rest
      by_cases hle : |item.value| ≤ |head.value|
      · have hle' : |item.value| ≤ |contractedHead.value| := by
          simpa [← hhead.value_eq] using hle
        simp [insertInsertionScheduleItemIncreasingAbs, hle, hle']
        exact InsertionScheduleItemsContract.tail
          (InsertionScheduleItemsContract.here hhead)
      · have hle' : ¬ |item.value| ≤ |contractedHead.value| := by
          simpa [← hhead.value_eq] using hle
        simp [insertInsertionScheduleItemIncreasingAbs, hle, hle']
        exact InsertionScheduleItemsContract.here hhead
  | _, _, InsertionScheduleItemsContract.tail htail => by
      rename_i head rest contractedRest
      by_cases hle : |item.value| ≤ |head.value|
      · simp [insertInsertionScheduleItemIncreasingAbs, hle]
        exact InsertionScheduleItemsContract.tail
          (InsertionScheduleItemsContract.tail htail)
      · simp [insertInsertionScheduleItemIncreasingAbs, hle]
        exact InsertionScheduleItemsContract.tail
          (insertInsertionScheduleItemIncreasingAbs_contract_list item htail)

/-- Item insertion preserves the represented source leaves up to permutation. -/
theorem insertInsertionScheduleItemIncreasingAbs_leaves_perm {fp : FPModel}
    (item : InsertionScheduleItem fp)
    (items : List (InsertionScheduleItem fp)) :
    (insertionScheduleLeaves
        (insertInsertionScheduleItemIncreasingAbs item items)).Perm
      (item.tree.leaves ++ insertionScheduleLeaves items) := by
  have hperm :=
    insertInsertionScheduleItemIncreasingAbs_perm item items
  have hflat := hperm.flatMap
    (f := fun item : InsertionScheduleItem fp => item.tree.leaves)
    (g := fun item : InsertionScheduleItem fp => item.tree.leaves)
    (by
      intro item _hmem
      exact List.Perm.refl item.tree.leaves)
  simpa [insertionScheduleLeaves] using hflat

/-- Initial active schedule items for a source list. -/
def initialInsertionScheduleItems (fp : FPModel) (xs : List ℝ) :
    List (InsertionScheduleItem fp) :=
  xs.map (InsertionScheduleItem.source fp)

/-- Initial active schedule values are exactly the source list. -/
theorem initialInsertionScheduleItems_values (fp : FPModel)
    (xs : List ℝ) :
    insertionScheduleValues (initialInsertionScheduleItems fp xs) = xs := by
  unfold initialInsertionScheduleItems insertionScheduleValues
  rw [List.map_map]
  change List.map (fun x : ℝ => x) xs = xs
  simp

/-- Initial active schedule leaves are exactly the source list. -/
theorem initialInsertionScheduleItems_leaves (fp : FPModel)
    (xs : List ℝ) :
    insertionScheduleLeaves (initialInsertionScheduleItems fp xs) = xs := by
  induction xs with
  | nil => simp [initialInsertionScheduleItems, insertionScheduleLeaves]
  | cons x xs ih =>
      simpa [initialInsertionScheduleItems, insertionScheduleLeaves,
        InsertionScheduleItem.source] using congrArg (fun ys => x :: ys) ih

/-- Source-level value insertion agrees with schedule-item insertion on
initial leaf items. -/
theorem initialInsertionScheduleItems_insertIncreasingAbs (fp : FPModel)
    (x : ℝ) :
    ∀ xs : List ℝ,
      initialInsertionScheduleItems fp (insertIncreasingAbs x xs) =
        insertInsertionScheduleItemIncreasingAbs
          (InsertionScheduleItem.source fp x)
          (initialInsertionScheduleItems fp xs)
  | [] => by
      simp [initialInsertionScheduleItems, insertIncreasingAbs,
        insertInsertionScheduleItemIncreasingAbs]
  | y :: ys => by
      by_cases hxy : |x| ≤ |y|
      · simp [initialInsertionScheduleItems, insertIncreasingAbs,
          insertInsertionScheduleItemIncreasingAbs,
          InsertionScheduleItem.source, hxy]
      · simpa [initialInsertionScheduleItems, insertIncreasingAbs,
          insertInsertionScheduleItemIncreasingAbs,
          InsertionScheduleItem.source, hxy] using
          initialInsertionScheduleItems_insertIncreasingAbs fp x ys

/-- One insertion-schedule step: combine the first two schedule items and
reinsert the combined item by increasing absolute current value. -/
noncomputable def insertionScheduleStep (fp : FPModel) :
    List (InsertionScheduleItem fp) → List (InsertionScheduleItem fp)
  | a :: b :: rest =>
      let combined : InsertionScheduleItem fp :=
        { value := fp.fl_add a.value b.value
          tree := InsertionScheduleTree.node a.tree b.tree
          eval_eq_value := by
            simp [InsertionScheduleTree.eval, a.eval_eq_value,
              b.eval_eq_value] }
      insertInsertionScheduleItemIncreasingAbs combined rest
  | items => items

/-- Schedule stepping projects to the source-level insertion step on computed
values. -/
theorem insertionScheduleStep_values (fp : FPModel)
    (items : List (InsertionScheduleItem fp)) :
    insertionScheduleValues (insertionScheduleStep fp items) =
      insertionStep fp (insertionScheduleValues items) := by
  cases items with
  | nil => simp [insertionScheduleStep, insertionScheduleValues, insertionStep]
  | cons a items =>
      cases items with
      | nil =>
          simp [insertionScheduleStep, insertionScheduleValues, insertionStep]
      | cons b rest =>
          let combined : InsertionScheduleItem fp :=
            { value := fp.fl_add a.value b.value
              tree := InsertionScheduleTree.node a.tree b.tree
              eval_eq_value := by
                simp [InsertionScheduleTree.eval, a.eval_eq_value,
                  b.eval_eq_value] }
          simpa [insertionScheduleStep, insertionScheduleValues,
            insertionStep, combined] using
            insertInsertionScheduleItemIncreasingAbs_values combined rest

/-- One schedule step preserves represented source leaves up to permutation. -/
theorem insertionScheduleStep_leaves_perm (fp : FPModel)
    (items : List (InsertionScheduleItem fp)) :
    (insertionScheduleLeaves (insertionScheduleStep fp items)).Perm
      (insertionScheduleLeaves items) := by
  cases items with
  | nil => simp [insertionScheduleStep, insertionScheduleLeaves]
  | cons a items =>
      cases items with
      | nil => simp [insertionScheduleStep, insertionScheduleLeaves]
      | cons b rest =>
          let combined : InsertionScheduleItem fp :=
            { value := fp.fl_add a.value b.value
              tree := InsertionScheduleTree.node a.tree b.tree
              eval_eq_value := by
                simp [InsertionScheduleTree.eval, a.eval_eq_value,
                  b.eval_eq_value] }
          have hinsert :=
            insertInsertionScheduleItemIncreasingAbs_leaves_perm combined rest
          simpa [insertionScheduleStep, insertionScheduleLeaves,
            InsertionScheduleTree.leaves, combined, List.append_assoc]
            using hinsert

/-- One insertion-schedule step preserves a single active-item sibling
contraction. -/
theorem insertionScheduleStep_contract {fp : FPModel} {a b : ℝ}
    {items contractedItems : List (InsertionScheduleItem fp)}
    (hrel : InsertionScheduleItemsContract a b items contractedItems) :
    InsertionScheduleItemsContract a b
      (insertionScheduleStep fp items)
      (insertionScheduleStep fp contractedItems) := by
  cases hrel with
  | here hitem =>
      rename_i item contracted rest
      cases rest with
      | nil =>
          simpa [insertionScheduleStep] using
            InsertionScheduleItemsContract.here hitem
      | cons y ys =>
          let combined : InsertionScheduleItem fp :=
            { value := fp.fl_add item.value y.value
              tree := InsertionScheduleTree.node item.tree y.tree
              eval_eq_value := by
                simp [InsertionScheduleTree.eval, item.eval_eq_value,
                  y.eval_eq_value] }
          let contractedCombined : InsertionScheduleItem fp :=
            { value := fp.fl_add contracted.value y.value
              tree := InsertionScheduleTree.node contracted.tree y.tree
              eval_eq_value := by
                simp [InsertionScheduleTree.eval, contracted.eval_eq_value,
                  y.eval_eq_value] }
          have hcombined :
              InsertionScheduleItemContract a b combined
                contractedCombined := by
            refine
              { value_eq := ?_
                tree_contract := ?_ }
            · simp [combined, contractedCombined, hitem.value_eq]
            · simpa [combined, contractedCombined] using
                InsertionScheduleTree.SiblingLeafContract.inLeft
                  hitem.tree_contract
          simpa [insertionScheduleStep, combined, contractedCombined] using
            insertInsertionScheduleItemIncreasingAbs_contract_item
              hcombined ys
  | tail hrest =>
      rename_i head rest contractedRest
      cases hrest with
      | here hsecond =>
          rename_i second contractedSecond restTail
          let combined : InsertionScheduleItem fp :=
            { value := fp.fl_add head.value second.value
              tree := InsertionScheduleTree.node head.tree second.tree
              eval_eq_value := by
                simp [InsertionScheduleTree.eval, head.eval_eq_value,
                  second.eval_eq_value] }
          let contractedCombined : InsertionScheduleItem fp :=
            { value := fp.fl_add head.value contractedSecond.value
              tree := InsertionScheduleTree.node head.tree
                contractedSecond.tree
              eval_eq_value := by
                simp [InsertionScheduleTree.eval, head.eval_eq_value,
                  contractedSecond.eval_eq_value] }
          have hcombined :
              InsertionScheduleItemContract a b combined
                contractedCombined := by
            refine
              { value_eq := ?_
                tree_contract := ?_ }
            · simp [combined, contractedCombined, hsecond.value_eq]
            · simpa [combined, contractedCombined] using
                InsertionScheduleTree.SiblingLeafContract.inRight
                  hsecond.tree_contract
          simpa [insertionScheduleStep, combined, contractedCombined] using
            insertInsertionScheduleItemIncreasingAbs_contract_item
              hcombined restTail
      | tail htail =>
          rename_i second restTail contractedRestTail
          let combined : InsertionScheduleItem fp :=
            { value := fp.fl_add head.value second.value
              tree := InsertionScheduleTree.node head.tree second.tree
              eval_eq_value := by
                simp [InsertionScheduleTree.eval, head.eval_eq_value,
                  second.eval_eq_value] }
          simpa [insertionScheduleStep, combined] using
            insertInsertionScheduleItemIncreasingAbs_contract_list
              combined htail

/-- Active schedule items after at most `fuel` insertion-summation steps. -/
noncomputable def insertionScheduleAfter (fp : FPModel) :
    ℕ → List (InsertionScheduleItem fp) → List (InsertionScheduleItem fp)
  | 0, items => items
  | _ + 1, [] => []
  | _ + 1, [item] => [item]
  | fuel + 1, a :: b :: rest =>
      insertionScheduleAfter fp fuel
        (insertionScheduleStep fp (a :: b :: rest))

/-- The full insertion-schedule trace preserves a single active-item sibling
contraction. -/
theorem insertionScheduleAfter_contract (fp : FPModel) {a b : ℝ} :
    ∀ fuel {items contractedItems : List (InsertionScheduleItem fp)},
      InsertionScheduleItemsContract a b items contractedItems →
      InsertionScheduleItemsContract a b
        (insertionScheduleAfter fp fuel items)
        (insertionScheduleAfter fp fuel contractedItems) := by
  intro fuel
  induction fuel with
  | zero =>
      intro items contractedItems hrel
      simpa [insertionScheduleAfter] using hrel
  | succ fuel ih =>
      intro items contractedItems hrel
      cases hrel with
      | here hitem =>
          rename_i item contracted rest
          cases rest with
          | nil =>
              simpa [insertionScheduleAfter] using
                InsertionScheduleItemsContract.here hitem
          | cons y ys =>
              have hstep :
                  InsertionScheduleItemsContract a b
                    (insertionScheduleStep fp (item :: y :: ys))
                    (insertionScheduleStep fp (contracted :: y :: ys)) :=
                insertionScheduleStep_contract (fp := fp)
                  (InsertionScheduleItemsContract.here hitem)
              simpa [insertionScheduleAfter] using ih hstep
      | tail hrest =>
          rename_i head rest contractedRest
          cases hrest with
          | here hsecond =>
              rename_i second contractedSecond restTail
              have hstep :
                  InsertionScheduleItemsContract a b
                    (insertionScheduleStep fp (head :: second :: restTail))
                    (insertionScheduleStep fp
                      (head :: contractedSecond :: restTail)) :=
                insertionScheduleStep_contract (fp := fp)
                  (InsertionScheduleItemsContract.tail
                    (InsertionScheduleItemsContract.here hsecond))
              simpa [insertionScheduleAfter] using ih hstep
          | tail htail =>
              rename_i second restTail contractedRestTail
              have hstep :
                  InsertionScheduleItemsContract a b
                    (insertionScheduleStep fp (head :: second :: restTail))
                    (insertionScheduleStep fp
                      (head :: second :: contractedRestTail)) :=
                insertionScheduleStep_contract (fp := fp)
                  (InsertionScheduleItemsContract.tail
                    (InsertionScheduleItemsContract.tail htail))
              simpa [insertionScheduleAfter] using ih hstep

/-- If the original schedule trace reaches a singleton, a related contracted
trace reaches the corresponding contracted singleton. -/
theorem insertionScheduleAfter_contract_singleton_left (fp : FPModel)
    {a b : ℝ} {fuel : ℕ}
    {items contractedItems : List (InsertionScheduleItem fp)}
    {item : InsertionScheduleItem fp}
    (hrel : InsertionScheduleItemsContract a b items contractedItems)
    (hsingleton : insertionScheduleAfter fp fuel items = [item]) :
    ∃ contracted : InsertionScheduleItem fp,
      insertionScheduleAfter fp fuel contractedItems = [contracted] ∧
        InsertionScheduleItemContract a b item contracted := by
  have hafter :=
    insertionScheduleAfter_contract (fp := fp) fuel hrel
  rw [hsingleton] at hafter
  exact InsertionScheduleItemsContract.singleton_left hafter

/-- The schedule trace projects to the source-level active-list trace on
computed values. -/
theorem insertionScheduleAfter_values (fp : FPModel) :
    ∀ fuel items,
      insertionScheduleValues (insertionScheduleAfter fp fuel items) =
        insertionActiveAfter fp fuel (insertionScheduleValues items) := by
  intro fuel
  induction fuel with
  | zero =>
      intro items
      simp [insertionScheduleAfter, insertionActiveAfter]
  | succ fuel ih =>
      intro items
      cases items with
      | nil => simp [insertionScheduleAfter, insertionActiveAfter,
          insertionScheduleValues]
      | cons a items =>
          cases items with
          | nil => simp [insertionScheduleAfter, insertionActiveAfter,
              insertionScheduleValues]
          | cons b rest =>
              calc
                insertionScheduleValues
                    (insertionScheduleAfter fp fuel
                      (insertionScheduleStep fp (a :: b :: rest))) =
                  insertionActiveAfter fp fuel
                    (insertionScheduleValues
                      (insertionScheduleStep fp (a :: b :: rest))) := by
                    exact ih (insertionScheduleStep fp (a :: b :: rest))
                _ = insertionActiveAfter fp fuel
                    (insertionStep fp
                      (insertionScheduleValues (a :: b :: rest))) := by
                    rw [insertionScheduleStep_values]
                _ = insertionActiveAfter fp (fuel + 1)
                    (insertionScheduleValues (a :: b :: rest)) := by
                    simp [insertionActiveAfter, insertionScheduleValues,
                      insertionStep]

/-- The schedule trace preserves represented source leaves up to permutation. -/
theorem insertionScheduleAfter_leaves_perm (fp : FPModel) :
    ∀ fuel items,
      (insertionScheduleLeaves
          (insertionScheduleAfter fp fuel items)).Perm
        (insertionScheduleLeaves items) := by
  intro fuel
  induction fuel with
  | zero =>
      intro items
      simp [insertionScheduleAfter]
  | succ fuel ih =>
      intro items
      cases items with
      | nil => simp [insertionScheduleAfter]
      | cons a items =>
          cases items with
          | nil => simp [insertionScheduleAfter]
          | cons b rest =>
              have hafter :=
                ih (insertionScheduleStep fp (a :: b :: rest))
              have hstep :=
                insertionScheduleStep_leaves_perm fp (a :: b :: rest)
              simpa [insertionScheduleAfter] using hafter.trans hstep

/-- For nonempty input, the full insertion schedule trace reaches a singleton
active schedule item. -/
theorem insertionScheduleAfter_full_eq_singleton_of_ne_nil (fp : FPModel)
    {xs : List ℝ} (hne : xs ≠ []) :
    ∃ item : InsertionScheduleItem fp,
      insertionScheduleAfter fp xs.length
        (initialInsertionScheduleItems fp xs) = [item] := by
  rcases insertionActiveAfter_full_eq_singleton_of_ne_nil fp hne with
    ⟨y, hactive⟩
  have hvalues :=
    insertionScheduleAfter_values fp xs.length
      (initialInsertionScheduleItems fp xs)
  have hmap :
      insertionScheduleValues
          (insertionScheduleAfter fp xs.length
            (initialInsertionScheduleItems fp xs)) = [y] := by
    rw [hvalues, initialInsertionScheduleItems_values, hactive]
  cases hschedule :
      insertionScheduleAfter fp xs.length
        (initialInsertionScheduleItems fp xs) with
  | nil =>
      simp [insertionScheduleValues, hschedule] at hmap
  | cons item rest =>
      cases rest with
      | nil => exact ⟨item, rfl⟩
      | cons item' rest' =>
          simp [insertionScheduleValues, hschedule] at hmap

/-- Under exact arithmetic, the concrete insertion-schedule trace generated
from a nonempty nonnegative increasing-absolute-value source list is a greedy
insertion tree. -/
theorem insertionScheduleAfter_full_greedy_exactWithUnitRoundoff_of_ne_nil
    (u0 : ℝ) (hu0 : 0 ≤ u0) :
    ∀ {xs : List ℝ} (_ : xs ≠ [])
      (_ : IncreasingAbsList xs)
      (_ : ∀ x ∈ xs, 0 ≤ x)
      {item : InsertionScheduleItem
        (FPModel.exactWithUnitRoundoff u0 hu0)},
      insertionScheduleAfter (FPModel.exactWithUnitRoundoff u0 hu0)
          xs.length
          (initialInsertionScheduleItems
            (FPModel.exactWithUnitRoundoff u0 hu0) xs) = [item] →
      item.tree.GreedyInsertionTree := by
  classical
  let fp := FPModel.exactWithUnitRoundoff u0 hu0
  let P : ℕ → Prop := fun n =>
    ∀ {xs : List ℝ}, xs.length = n →
      xs ≠ [] →
      IncreasingAbsList xs →
      (∀ x ∈ xs, 0 ≤ x) →
      ∀ {item : InsertionScheduleItem fp},
        insertionScheduleAfter fp xs.length
          (initialInsertionScheduleItems fp xs) = [item] →
        item.tree.GreedyInsertionTree
  have hstep : ∀ n, (∀ m, m < n → P m) → P n := by
    intro n ih xs hlen hne hsorted hnonneg item hterminal
    cases xs with
    | nil =>
        contradiction
    | cons a xs =>
        cases xs with
        | nil =>
            have hlist :
                [InsertionScheduleItem.source fp a] = [item] := by
              simpa [fp, initialInsertionScheduleItems,
                insertionScheduleAfter] using hterminal
            cases hlist
            simpa [InsertionScheduleItem.source] using
              InsertionScheduleTree.GreedyInsertionTree.leaf a
        | cons b rest =>
            let ys := insertIncreasingAbs (a + b) rest
            have ha_nonneg : 0 ≤ a := hnonneg a (by simp)
            have hb_nonneg : 0 ≤ b := hnonneg b (by simp)
            have hab : a ≤ b := by
              have hab_abs : |a| ≤ |b| := hsorted.1
              simpa [abs_of_nonneg ha_nonneg,
                abs_of_nonneg hb_nonneg] using hab_abs
            have htailSorted : IncreasingAbsList (b :: rest) :=
              IncreasingAbsList.tail hsorted
            have htailNonneg : ∀ x ∈ b :: rest, 0 ≤ x := by
              intro x hx
              exact hnonneg x (by simp [hx])
            have hrestGe : ∀ x ∈ rest, b ≤ x := by
              intro x hx
              exact
                IncreasingAbsList.head_le_of_mem_of_nonnegative
                  htailSorted htailNonneg (by simp [hx])
            have hrestSorted : IncreasingAbsList rest :=
              IncreasingAbsList.tail htailSorted
            have hrestNonneg : ∀ x ∈ rest, 0 ≤ x := by
              intro x hx
              exact hnonneg x (by simp [hx])
            have hab_nonneg : 0 ≤ a + b := by linarith
            have hysSorted : IncreasingAbsList ys := by
              simpa [ys] using
                insertIncreasingAbs_preserves (a + b) rest hrestSorted
            have hysNonneg : ∀ x ∈ ys, 0 ≤ x := by
              simpa [ys] using
                insertIncreasingAbs_nonnegative hab_nonneg hrestNonneg
            have hysNe : ys ≠ [] := by
              simpa [ys] using insertIncreasingAbs_ne_nil (a + b) rest
            have hysLen : ys.length = rest.length + 1 := by
              simp [ys, insertIncreasingAbs_length]
            have hysLt : ys.length < n := by
              rw [← hlen]
              simp [ys, insertIncreasingAbs_length]
            let combined : InsertionScheduleItem fp :=
              { value := fp.fl_add a b
                tree := InsertionScheduleTree.node
                  (InsertionScheduleTree.leaf a)
                  (InsertionScheduleTree.leaf b)
                eval_eq_value := by
                  simp [InsertionScheduleTree.eval] }
            let contracted : InsertionScheduleItem fp :=
              InsertionScheduleItem.source fp (a + b)
            have hcombined :
                InsertionScheduleItemContract a b combined contracted := by
              refine
                { value_eq := ?_
                  tree_contract := ?_ }
              · simp [combined, contracted, fp,
                  InsertionScheduleItem.source,
                  FPModel.exactWithUnitRoundoff]
              · simpa [combined, contracted,
                  InsertionScheduleItem.source] using
                  InsertionScheduleTree.SiblingLeafContract.here a b
            have hpost0 :
                InsertionScheduleItemsContract a b
                  (insertInsertionScheduleItemIncreasingAbs combined
                    (initialInsertionScheduleItems fp rest))
                  (insertInsertionScheduleItemIncreasingAbs contracted
                    (initialInsertionScheduleItems fp rest)) :=
              insertInsertionScheduleItemIncreasingAbs_contract_item
                hcombined (initialInsertionScheduleItems fp rest)
            have hpost :
                InsertionScheduleItemsContract a b
                  (insertionScheduleStep fp
                    (initialInsertionScheduleItems fp (a :: b :: rest)))
                  (initialInsertionScheduleItems fp ys) := by
              have hinitialYs :
                  initialInsertionScheduleItems fp ys =
                    insertInsertionScheduleItemIncreasingAbs contracted
                      (initialInsertionScheduleItems fp rest) := by
                simpa [ys, contracted] using
                  initialInsertionScheduleItems_insertIncreasingAbs
                    fp (a + b) rest
              rw [hinitialYs]
              simpa [fp, insertionScheduleStep,
                initialInsertionScheduleItems, combined, contracted,
                InsertionScheduleItem.source,
                FPModel.exactWithUnitRoundoff] using hpost0
            have hterminalTail :
                insertionScheduleAfter fp (rest.length + 1)
                  (insertionScheduleStep fp
                    (initialInsertionScheduleItems fp (a :: b :: rest))) =
                    [item] := by
              simpa [fp, initialInsertionScheduleItems,
                insertionScheduleAfter] using hterminal
            obtain ⟨contractedItem, hcontractedTail,
                hitemContract⟩ :=
              insertionScheduleAfter_contract_singleton_left fp hpost
                hterminalTail
            have hcontractedTerminal :
                insertionScheduleAfter fp ys.length
                  (initialInsertionScheduleItems fp ys) =
                  [contractedItem] := by
              simpa [hysLen] using hcontractedTail
            have hgreedyContracted :
                contractedItem.tree.GreedyInsertionTree :=
              ih ys.length hysLt (xs := ys) rfl hysNe hysSorted
                hysNonneg (item := contractedItem) hcontractedTerminal
            have hcontractedLeavesYs :
                contractedItem.tree.leaves.Perm ys := by
              have hleaves :=
                insertionScheduleAfter_leaves_perm fp ys.length
                  (initialInsertionScheduleItems fp ys)
              have hleafPerm0 :
                  contractedItem.tree.leaves.Perm
                    (insertionScheduleLeaves
                      (initialInsertionScheduleItems fp ys)) := by
                simpa [insertionScheduleLeaves, hcontractedTerminal]
                  using hleaves
              simpa [initialInsertionScheduleItems_leaves fp ys]
                using hleafPerm0
            have hcontractedLeaves :
                contractedItem.tree.leaves.Perm ((a + b) :: rest) :=
              hcontractedLeavesYs.trans (by
                simpa [ys] using insertIncreasingAbs_perm (a + b) rest)
            exact
              InsertionScheduleTree.GreedyInsertionTree.merge
                hitemContract.tree_contract hcontractedLeaves hab hrestGe
                hgreedyContracted
  intro xs hne hsorted hnonneg item hterminal
  have hmain : P xs.length :=
    Nat.strong_induction_on (p := P) xs.length hstep
  exact hmain rfl hne hsorted hnonneg hterminal

/-- Nonempty source-level insertion summation is represented by a list-shaped
binary schedule whose leaves are a permutation of the original active list. -/
theorem fl_insertionSumList_has_list_schedule_of_ne_nil (fp : FPModel)
    {xs : List ℝ} (hne : xs ≠ []) :
    ∃ tree : InsertionScheduleTree,
      tree.leaves.Perm xs ∧ tree.eval fp = fl_insertionSumList fp xs := by
  rcases insertionScheduleAfter_full_eq_singleton_of_ne_nil fp hne with
    ⟨item, hsingleton⟩
  have hleaves :=
    insertionScheduleAfter_leaves_perm fp xs.length
      (initialInsertionScheduleItems fp xs)
  have hleafPerm : item.tree.leaves.Perm xs := by
    have hleafPerm0 :
        item.tree.leaves.Perm
          (insertionScheduleLeaves
            (initialInsertionScheduleItems fp xs)) := by
      simpa [insertionScheduleLeaves, hsingleton] using hleaves
    simpa [initialInsertionScheduleItems_leaves fp xs] using hleafPerm0
  have hvalues :=
    insertionScheduleAfter_values fp xs.length
      (initialInsertionScheduleItems fp xs)
  have hactive :
      insertionActiveAfter fp xs.length xs = [item.value] := by
    have hactive0 :
        insertionActiveAfter fp xs.length
            (insertionScheduleValues
              (initialInsertionScheduleItems fp xs)) = [item.value] := by
      simpa [insertionScheduleValues, hsingleton] using hvalues.symm
    simpa [initialInsertionScheduleItems_values fp xs] using hactive0
  have hfl :
      fl_insertionSumList fp xs = item.value :=
    fl_insertionSumList_eq_of_activeAfter_eq_singleton fp hactive
  exact ⟨item.tree, hleafPerm, item.eval_eq_value.trans hfl.symm⟩

/-- Exact-arithmetic source-level insertion summation on a nonempty
nonnegative increasing-absolute-value list is represented by a greedy
insertion schedule tree. -/
theorem fl_insertionSumList_has_greedy_schedule_exactWithUnitRoundoff_of_ne_nil
    (u0 : ℝ) (hu0 : 0 ≤ u0)
    {xs : List ℝ} (hne : xs ≠ [])
    (hsorted : IncreasingAbsList xs)
    (hnonneg : ∀ x ∈ xs, 0 ≤ x) :
    ∃ tree : InsertionScheduleTree,
      tree.leaves.Perm xs ∧
        tree.GreedyInsertionTree ∧
          tree.eval (FPModel.exactWithUnitRoundoff u0 hu0) =
            fl_insertionSumList (FPModel.exactWithUnitRoundoff u0 hu0) xs := by
  let fp := FPModel.exactWithUnitRoundoff u0 hu0
  rcases insertionScheduleAfter_full_eq_singleton_of_ne_nil fp hne with
    ⟨item, hsingleton⟩
  have hgreedy : item.tree.GreedyInsertionTree :=
    insertionScheduleAfter_full_greedy_exactWithUnitRoundoff_of_ne_nil
      u0 hu0 hne hsorted hnonneg hsingleton
  have hleaves :=
    insertionScheduleAfter_leaves_perm fp xs.length
      (initialInsertionScheduleItems fp xs)
  have hleafPerm : item.tree.leaves.Perm xs := by
    have hleafPerm0 :
        item.tree.leaves.Perm
          (insertionScheduleLeaves
            (initialInsertionScheduleItems fp xs)) := by
      simpa [insertionScheduleLeaves, hsingleton] using hleaves
    simpa [initialInsertionScheduleItems_leaves fp xs] using hleafPerm0
  have hvalues :=
    insertionScheduleAfter_values fp xs.length
      (initialInsertionScheduleItems fp xs)
  have hactive :
      insertionActiveAfter fp xs.length xs = [item.value] := by
    have hactive0 :
        insertionActiveAfter fp xs.length
            (insertionScheduleValues
              (initialInsertionScheduleItems fp xs)) = [item.value] := by
      simpa [insertionScheduleValues, hsingleton] using hvalues.symm
    simpa [initialInsertionScheduleItems_values fp xs] using hactive0
  have hfl :
      fl_insertionSumList fp xs = item.value :=
    fl_insertionSumList_eq_of_activeAfter_eq_singleton fp hactive
  exact ⟨item.tree, hleafPerm, hgreedy, item.eval_eq_value.trans hfl.symm⟩

/-- Exact-arithmetic end-to-end insertion optimality bridge: for any
nonnegative Algorithm 4.1 summation tree with the same source-leaf multiset,
the concrete source-level insertion schedule is greedy and has no larger exact
running-error budget. -/
theorem fl_insertionSumList_exactWithUnitRoundoff_greedy_runningErrorBudget_le
    (u0 : ℝ) (hu0 : 0 ≤ u0)
    {xs : List ℝ} (hne : xs ≠ [])
    (hsorted : IncreasingAbsList xs)
    (other : SumTree n) (v : Fin n → ℝ)
    (hv : ∀ i, 0 ≤ v i)
    (hperm :
      xs.Perm (SumTree.toInsertionScheduleTree other v).leaves) :
    ∃ insertion : InsertionScheduleTree,
      insertion.leaves.Perm xs ∧
        insertion.GreedyInsertionTree ∧
          insertion.eval (FPModel.exactWithUnitRoundoff u0 hu0) =
            fl_insertionSumList
              (FPModel.exactWithUnitRoundoff u0 hu0) xs ∧
          insertion.exactMergeCost ≤
            SumTree.runningErrorBudget
              (FPModel.exactWithUnitRoundoff u0 hu0) other v := by
  have hmaterializedNonneg :
      ∀ x ∈ (SumTree.toInsertionScheduleTree other v).leaves, 0 ≤ x :=
    SumTree.toInsertionScheduleTree_leaves_nonnegative other v hv
  have hnonneg : ∀ x ∈ xs, 0 ≤ x := by
    intro x hx
    exact hmaterializedNonneg x ((hperm.mem_iff).1 hx)
  obtain ⟨insertion, hleaves, hgreedy, heval⟩ :=
    fl_insertionSumList_has_greedy_schedule_exactWithUnitRoundoff_of_ne_nil
      u0 hu0 hne hsorted hnonneg
  have hleavesMaterialized :
      insertion.leaves.Perm
        (SumTree.toInsertionScheduleTree other v).leaves :=
    hleaves.trans hperm
  have hbudget :
      insertion.exactMergeCost ≤
        SumTree.runningErrorBudget
          (FPModel.exactWithUnitRoundoff u0 hu0) other v :=
    SumTree.runningErrorBudget_exactWithUnitRoundoff_greedyInsertion_le
      u0 hu0 insertion other v hv hleavesMaterialized hgreedy
  exact ⟨insertion, hleaves, hgreedy, heval, hbudget⟩

/-- Nonempty insertion summation has a dependent `SumTree` shape whose leaf
count is the list-shaped schedule's leaf count, with the list-shaped schedule
still carrying the value and source-leaf permutation facts. -/
theorem fl_insertionSumList_has_sumTree_shape_of_ne_nil (fp : FPModel)
    {xs : List ℝ} (hne : xs ≠ []) :
    ∃ tree : InsertionScheduleTree,
      ∃ _ : SumTree tree.leaves.length,
        tree.leaves.Perm xs ∧
          tree.eval fp = fl_insertionSumList fp xs := by
  rcases fl_insertionSumList_has_list_schedule_of_ne_nil fp hne with
    ⟨tree, hperm, heval⟩
  refine ⟨tree, ?_, hperm, heval⟩
  rw [InsertionScheduleTree.leaves_length]
  exact tree.toSumTree

/-- Nonempty insertion summation is an Algorithm 4.1 `SumTree` evaluation
over the list-shaped schedule's ordered source leaves. -/
theorem fl_insertionSumList_has_sumTree_eval_of_ne_nil (fp : FPModel)
    {xs : List ℝ} (hne : xs ≠ []) :
    ∃ tree : InsertionScheduleTree,
      tree.leaves.Perm xs ∧
        SumTree.eval fp tree.toSumTree tree.leafVector =
          fl_insertionSumList fp xs := by
  rcases fl_insertionSumList_has_list_schedule_of_ne_nil fp hne with
    ⟨tree, hperm, heval⟩
  exact ⟨tree, hperm,
    (InsertionScheduleTree.toSumTree_eval fp tree).trans heval⟩

end NumStability
