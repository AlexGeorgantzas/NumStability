-- Algorithms/OrderingExamples.lean

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Log
import Batteries.Data.RBMap.Depth
import Batteries.Data.RBMap.Lemmas
import NumStability.Algorithms.Summation.Insertion.ActiveList
import NumStability.Algorithms.Summation.Recursive.Core
import NumStability.Algorithms.Summation.Tree.Core

namespace NumStability

/-!
# Ordering Examples for Recursive Summation (Higham Chapter 4, printed p. 83)

Higham's cancellation example (4.5) compares increasing, Psum, and decreasing
recursive summation orderings for the data `[1, M, 2M, -3M]`, under the
displayed assumption that `fl(1 + M) = M` and the exact scale additions used
in the example.  This file formalizes the three displayed computations and the
corresponding running-error-budget values `4M`, `3M`, and `M + 1`.

The concrete increasing/decreasing magnitude sorting layer is included below;
the source-side Psum greedy ordering and nonnegative increasing-order exact
prefix-budget theorem are included below.  The comparison-count bound and broad
heavy-cancellation ordering advice remain separate targets.
-/

open scoped BigOperators

/-! ## General recursive-summation order surfaces -/

/-- A finite permutation orders an input by nondecreasing magnitude. -/
def IncreasingMagnitudeOrder {n : ℕ} (v : Fin n → ℝ)
    (order : Fin n ≃ Fin n) : Prop :=
  ∀ i j : Fin n, i.val < j.val → |v (order i)| ≤ |v (order j)|

/-- A finite permutation orders an input by strictly increasing magnitude. -/
def StrictIncreasingMagnitudeOrder {n : ℕ} (v : Fin n → ℝ)
    (order : Fin n ≃ Fin n) : Prop :=
  ∀ i j : Fin n, i.val < j.val → |v (order i)| < |v (order j)|

/-- A finite permutation orders an input by nonincreasing magnitude. -/
def DecreasingMagnitudeOrder {n : ℕ} (v : Fin n → ℝ)
    (order : Fin n ≃ Fin n) : Prop :=
  ∀ i j : Fin n, i.val < j.val → |v (order j)| ≤ |v (order i)|

/-- A finite permutation orders an input by strictly decreasing magnitude. -/
def StrictDecreasingMagnitudeOrder {n : ℕ} (v : Fin n → ℝ)
    (order : Fin n ≃ Fin n) : Prop :=
  ∀ i j : Fin n, i.val < j.val → |v (order j)| < |v (order i)|

/-- Strictly increasing magnitude order implies the weak increasing order used
by the reusable recursive-summation surfaces. -/
theorem IncreasingMagnitudeOrder.of_strict {n : ℕ} {v : Fin n → ℝ}
    {order : Fin n ≃ Fin n}
    (h : StrictIncreasingMagnitudeOrder v order) :
    IncreasingMagnitudeOrder v order := by
  intro i j hij
  exact le_of_lt (h i j hij)

/-- Strictly decreasing magnitude order implies the weak decreasing order used
by the reusable recursive-summation surfaces. -/
theorem DecreasingMagnitudeOrder.of_strict {n : ℕ} {v : Fin n → ℝ}
    {order : Fin n ≃ Fin n}
    (h : StrictDecreasingMagnitudeOrder v order) :
    DecreasingMagnitudeOrder v order := by
  intro i j hij
  exact le_of_lt (h i j hij)

/-- Recursive summation after applying an explicit finite permutation to the
input order. -/
noncomputable def fl_recursiveSumInOrder (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (order : Fin n ≃ Fin n) : ℝ :=
  fl_recursiveSum fp n (fun i => v (order i))

/-- A finite reordering preserves the exact mathematical sum of the inputs. -/
theorem sum_orderedInput_eq_sum {n : ℕ} (v : Fin n → ℝ)
    (order : Fin n ≃ Fin n) :
    (∑ i : Fin n, v (order i)) = ∑ i : Fin n, v i :=
  Fintype.sum_equiv order
    (fun i : Fin n => v (order i))
    (fun i : Fin n => v i)
    (fun _ => rfl)

/-- The identity order recovers ordinary recursive summation. -/
theorem fl_recursiveSumInOrder_refl (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) :
    fl_recursiveSumInOrder fp v (Equiv.refl (Fin n)) =
      fl_recursiveSum fp n v := by
  rfl

/-! ## Concrete increasing/decreasing magnitude list sorters -/

/-- A list is ordered by nonincreasing absolute value. -/
def DecreasingAbsList : List ℝ → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => |y| ≤ |x| ∧ DecreasingAbsList (y :: rest)

/-- The tail of a decreasing-absolute-value list is decreasing. -/
theorem DecreasingAbsList.tail {x : ℝ} {xs : List ℝ}
    (h : DecreasingAbsList (x :: xs)) : DecreasingAbsList xs := by
  cases xs with
  | nil => trivial
  | cons y rest => exact h.2

/-- Insert a value into a list ordered by decreasing absolute value. -/
noncomputable def insertDecreasingAbs (x : ℝ) : List ℝ → List ℝ
  | [] => [x]
  | y :: ys =>
      if |y| ≤ |x| then
        x :: y :: ys
      else
        y :: insertDecreasingAbs x ys

/-- Insertion into a decreasing-absolute-value list only permutes the entries. -/
theorem insertDecreasingAbs_perm (x : ℝ) :
    ∀ xs : List ℝ, (insertDecreasingAbs x xs).Perm (x :: xs)
  | [] => by simp [insertDecreasingAbs]
  | y :: ys => by
      by_cases hyx : |y| ≤ |x|
      · simp [insertDecreasingAbs, hyx]
      · have hrec := insertDecreasingAbs_perm x ys
        simpa [insertDecreasingAbs, hyx] using
          (List.Perm.cons y hrec).trans (List.Perm.swap x y ys)

/-- Insertion preserves decreasing-absolute-value order. -/
theorem insertDecreasingAbs_preserves (x : ℝ) :
    ∀ xs : List ℝ,
      DecreasingAbsList xs → DecreasingAbsList (insertDecreasingAbs x xs)
  | [], _ => by simp [insertDecreasingAbs, DecreasingAbsList]
  | y :: [], _ => by
      by_cases hyx : |y| ≤ |x|
      · simp [insertDecreasingAbs, DecreasingAbsList, hyx]
      · have hxy : |x| ≤ |y| := le_of_lt (lt_of_not_ge hyx)
        simp [insertDecreasingAbs, DecreasingAbsList, hyx, hxy]
  | y :: z :: zs, hsorted => by
      rcases hsorted with ⟨hzy, htail⟩
      by_cases hyx : |y| ≤ |x|
      · simp [insertDecreasingAbs, DecreasingAbsList, hyx, hzy, htail]
      · have hxy : |x| ≤ |y| := le_of_lt (lt_of_not_ge hyx)
        by_cases hzx : |z| ≤ |x|
        · simp [insertDecreasingAbs, DecreasingAbsList, hyx, hzx, hxy,
            htail]
        · have hrec :=
            insertDecreasingAbs_preserves x (z :: zs) htail
          have hrec' :
              DecreasingAbsList (z :: insertDecreasingAbs x zs) := by
            simpa [insertDecreasingAbs, hzx] using hrec
          simp [insertDecreasingAbs, DecreasingAbsList, hyx, hzx, hzy,
            hrec']

/-- List sums are invariant under permutation. -/
theorem list_sum_eq_of_perm {xs ys : List ℝ} (hperm : xs.Perm ys) :
    xs.sum = ys.sum := by
  induction hperm with
  | nil => simp
  | cons x hperm ih => simp [ih]
  | swap x y zs => simp [add_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Concrete source-side sorting by increasing absolute value. -/
noncomputable def increasingAbsSort : List ℝ → List ℝ
  | [] => []
  | x :: xs => insertIncreasingAbs x (increasingAbsSort xs)

/-- Concrete increasing-magnitude sorting returns an increasing-absolute-value
list. -/
theorem increasingAbsSort_sorted :
    ∀ xs : List ℝ, IncreasingAbsList (increasingAbsSort xs)
  | [] => by simp [increasingAbsSort, IncreasingAbsList]
  | x :: xs => by
      simpa [increasingAbsSort] using
        insertIncreasingAbs_preserves x (increasingAbsSort xs)
          (increasingAbsSort_sorted xs)

/-- Concrete increasing-magnitude sorting preserves the input multiset. -/
theorem increasingAbsSort_perm :
    ∀ xs : List ℝ, (increasingAbsSort xs).Perm xs
  | [] => by simp [increasingAbsSort]
  | x :: xs => by
      have hinsert :=
        insertIncreasingAbs_perm x (increasingAbsSort xs)
      exact hinsert.trans
        (List.Perm.cons x (increasingAbsSort_perm xs))

/-- Concrete increasing-magnitude sorting preserves the exact source sum. -/
theorem increasingAbsSort_sum_eq (xs : List ℝ) :
    (increasingAbsSort xs).sum = xs.sum :=
  list_sum_eq_of_perm (increasingAbsSort_perm xs)

/-- Prepending an entry whose absolute value is no larger than every existing
entry preserves increasing-absolute-value order. -/
theorem IncreasingAbsList.cons_of_abs_le_all {x : ℝ} {xs : List ℝ}
    (hsorted : IncreasingAbsList xs)
    (hle : ∀ y ∈ xs, |x| ≤ |y|) :
    IncreasingAbsList (x :: xs) := by
  cases xs with
  | nil =>
      simp [IncreasingAbsList]
  | cons y ys =>
      exact ⟨hle y (by simp), hsorted⟩

/-- A nonnegative list ordered by increasing absolute value is sorted by the
ordinary real order. -/
theorem IncreasingAbsList.sortedLE_of_nonnegative :
    ∀ {xs : List ℝ},
      IncreasingAbsList xs →
      (∀ z ∈ xs, 0 ≤ z) →
      xs.SortedLE
  | [], _hsorted, _hnonneg => by
      rw [List.sortedLE_iff_pairwise]
      simp
  | [_x], _hsorted, _hnonneg => by
      rw [List.sortedLE_iff_pairwise]
      simp
  | x :: y :: rest, hsorted, hnonneg => by
      rw [List.sortedLE_iff_pairwise]
      constructor
      · intro z hz
        exact IncreasingAbsList.head_le_of_mem_of_nonnegative hsorted
          hnonneg (by simp [hz])
      · have htailSorted : IncreasingAbsList (y :: rest) :=
          IncreasingAbsList.tail hsorted
        have htailNonneg : ∀ z ∈ y :: rest, 0 ≤ z := by
          intro z hz
          exact hnonneg z (by simp [hz])
        have htail :=
          IncreasingAbsList.sortedLE_of_nonnegative htailSorted
            htailNonneg
        simpa [List.sortedLE_iff_pairwise] using htail

/-- Concrete source-side sorting by decreasing absolute value. -/
noncomputable def decreasingAbsSort : List ℝ → List ℝ
  | [] => []
  | x :: xs => insertDecreasingAbs x (decreasingAbsSort xs)

/-- Concrete decreasing-magnitude sorting returns a decreasing-absolute-value
list. -/
theorem decreasingAbsSort_sorted :
    ∀ xs : List ℝ, DecreasingAbsList (decreasingAbsSort xs)
  | [] => by simp [decreasingAbsSort, DecreasingAbsList]
  | x :: xs => by
      simpa [decreasingAbsSort] using
        insertDecreasingAbs_preserves x (decreasingAbsSort xs)
          (decreasingAbsSort_sorted xs)

/-- Concrete decreasing-magnitude sorting preserves the input multiset. -/
theorem decreasingAbsSort_perm :
    ∀ xs : List ℝ, (decreasingAbsSort xs).Perm xs
  | [] => by simp [decreasingAbsSort]
  | x :: xs => by
      have hinsert :=
        insertDecreasingAbs_perm x (decreasingAbsSort xs)
      exact hinsert.trans
        (List.Perm.cons x (decreasingAbsSort_perm xs))

/-- Concrete decreasing-magnitude sorting preserves the exact source sum. -/
theorem decreasingAbsSort_sum_eq (xs : List ℝ) :
    (decreasingAbsSort xs).sum = xs.sum :=
  list_sum_eq_of_perm (decreasingAbsSort_perm xs)

/-! ## Nonnegative recursive-summation ordering objective -/

/-- Exact a priori prefix-sum objective for recursive summation, starting from
an accumulator `acc`.  For a list `[x₁, …, xₙ]` this is
`|acc + x₁| + |acc + x₁ + x₂| + ...`, the source-side counterpart of the
recursive-summation bound that Higham minimizes on pp. 90--91. -/
noncomputable def recursiveExactPrefixBudgetFrom (acc : ℝ) : List ℝ → ℝ
  | [] => 0
  | x :: xs => |acc + x| + recursiveExactPrefixBudgetFrom (acc + x) xs

/-- Exact a priori prefix-sum objective for recursive summation from zero. -/
noncomputable def recursiveExactPrefixBudget (xs : List ℝ) : ℝ :=
  recursiveExactPrefixBudgetFrom 0 xs

/-- Recursive-loop running-error budget over a concrete list, starting from
an accumulator `acc`.

At each step this records the absolute value of the exact pre-rounding pair
sum `acc + x`; the accumulator then advances by the rounded sum
`fp.fl_add acc x`.  Thus it is the list-shaped counterpart of the recursive
summation running-error quantity in Higham equation (4.3). -/
noncomputable def recursiveRoundedPrefixBudgetFrom (fp : FPModel)
    (acc : ℝ) : List ℝ → ℝ
  | [] => 0
  | x :: xs =>
      |acc + x| +
        recursiveRoundedPrefixBudgetFrom fp (fp.fl_add acc x) xs

/-- Recursive-loop running-error budget from the zero accumulator. -/
noncomputable def recursiveRoundedPrefixBudget (fp : FPModel)
    (xs : List ℝ) : ℝ :=
  recursiveRoundedPrefixBudgetFrom fp 0 xs

/-- Under exact arithmetic, the rounded recursive-loop budget is exactly the
source-side exact prefix objective. -/
theorem recursiveRoundedPrefixBudgetFrom_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 ≤ u0) (acc : ℝ) :
    ∀ xs : List ℝ,
      recursiveRoundedPrefixBudgetFrom
          (FPModel.exactWithUnitRoundoff u0 hu0) acc xs =
        recursiveExactPrefixBudgetFrom acc xs := by
  intro xs
  induction xs generalizing acc with
  | nil =>
      simp [recursiveRoundedPrefixBudgetFrom, recursiveExactPrefixBudgetFrom]
  | cons x xs ih =>
      calc
        recursiveRoundedPrefixBudgetFrom
            (FPModel.exactWithUnitRoundoff u0 hu0) acc (x :: xs) =
          |acc + x| +
            recursiveRoundedPrefixBudgetFrom
              (FPModel.exactWithUnitRoundoff u0 hu0) (acc + x) xs := by
            simp [recursiveRoundedPrefixBudgetFrom, FPModel.exactWithUnitRoundoff]
        _ = |acc + x| + recursiveExactPrefixBudgetFrom (acc + x) xs := by
            rw [ih (acc + x)]
        _ = recursiveExactPrefixBudgetFrom acc (x :: xs) := by
            simp [recursiveExactPrefixBudgetFrom]

/-- Zero-accumulator form of
`recursiveRoundedPrefixBudgetFrom_exactWithUnitRoundoff`. -/
theorem recursiveRoundedPrefixBudget_exactWithUnitRoundoff
    (u0 : ℝ) (hu0 : 0 ≤ u0) (xs : List ℝ) :
    recursiveRoundedPrefixBudget (FPModel.exactWithUnitRoundoff u0 hu0) xs =
      recursiveExactPrefixBudget xs := by
  simpa [recursiveRoundedPrefixBudget, recursiveExactPrefixBudget] using
    recursiveRoundedPrefixBudgetFrom_exactWithUnitRoundoff u0 hu0 0 xs

/-- In a nonnegative sorted tail, inserting a nonnegative value by increasing
absolute value gives no larger exact prefix objective than placing that value
before the tail. -/
theorem recursiveExactPrefixBudgetFrom_insertIncreasingAbs_le_cons_of_nonnegative_sorted
    {acc x : ℝ} :
    ∀ xs : List ℝ,
      0 ≤ acc →
      0 ≤ x →
      (∀ y ∈ xs, 0 ≤ y) →
      IncreasingAbsList xs →
      recursiveExactPrefixBudgetFrom acc (insertIncreasingAbs x xs) ≤
        recursiveExactPrefixBudgetFrom acc (x :: xs)
  | [], hacc, hx, _hxs, _hsorted => by
      have haccx : 0 ≤ acc + x := add_nonneg hacc hx
      simp [recursiveExactPrefixBudgetFrom, insertIncreasingAbs,
        abs_of_nonneg haccx]
  | y :: ys, hacc, hx, hxs, hsorted => by
      have hy : 0 ≤ y := hxs y (by simp)
      have hys_nonneg : ∀ z ∈ ys, 0 ≤ z := by
        intro z hz
        exact hxs z (by simp [hz])
      by_cases hxy_abs : |x| ≤ |y|
      · simp [insertIncreasingAbs, recursiveExactPrefixBudgetFrom, hxy_abs]
      · have hy_le_x : y ≤ x := by
          have hlt_abs : |y| < |x| := lt_of_not_ge hxy_abs
          simpa [abs_of_nonneg hx, abs_of_nonneg hy] using le_of_lt hlt_abs
        have htail_sorted : IncreasingAbsList ys :=
          IncreasingAbsList.tail hsorted
        have haccy : 0 ≤ acc + y := add_nonneg hacc hy
        have hrec :=
          recursiveExactPrefixBudgetFrom_insertIncreasingAbs_le_cons_of_nonnegative_sorted
            ys haccy hx hys_nonneg htail_sorted
        have haccx : 0 ≤ acc + x := add_nonneg hacc hx
        have hacc_y_x : 0 ≤ acc + y + x := add_nonneg haccy hx
        have hacc_x_y : 0 ≤ acc + x + y := add_nonneg haccx hy
        have hbudget' :
            recursiveExactPrefixBudgetFrom (acc + y)
                (insertIncreasingAbs x ys) ≤
              (acc + x + y) +
                recursiveExactPrefixBudgetFrom (acc + x + y) ys := by
          have hsum_comm : acc + y + x = acc + x + y := by ring
          rw [← hsum_comm]
          simpa [recursiveExactPrefixBudgetFrom, abs_of_nonneg hacc_y_x]
            using hrec
        simp [insertIncreasingAbs, recursiveExactPrefixBudgetFrom, hxy_abs,
          abs_of_nonneg haccy, abs_of_nonneg haccx,
          abs_of_nonneg hacc_x_y]
        nlinarith [hbudget', hy_le_x]

/-- Sorting a nonnegative list by increasing absolute value minimizes the exact
a priori recursive prefix objective relative to the supplied order. -/
theorem increasingAbsSort_recursiveExactPrefixBudgetFrom_le :
    ∀ (xs : List ℝ) {acc : ℝ},
      0 ≤ acc →
      (∀ y ∈ xs, 0 ≤ y) →
      recursiveExactPrefixBudgetFrom acc (increasingAbsSort xs) ≤
        recursiveExactPrefixBudgetFrom acc xs
  | [], _acc, _hacc, _hxs => by
      simp [recursiveExactPrefixBudgetFrom, increasingAbsSort]
  | x :: xs, acc, hacc, hnonneg => by
      have hx : 0 ≤ x := hnonneg x (by simp)
      have hxs_nonneg : ∀ y ∈ xs, 0 ≤ y := by
        intro y hy
        exact hnonneg y (by simp [hy])
      have hsort_nonneg : ∀ y ∈ increasingAbsSort xs, 0 ≤ y := by
        intro y hy
        have hy_orig : y ∈ xs :=
          ((increasingAbsSort_perm xs).mem_iff).1 hy
        exact hxs_nonneg y hy_orig
      have hins :
          recursiveExactPrefixBudgetFrom acc
              (insertIncreasingAbs x (increasingAbsSort xs)) ≤
            recursiveExactPrefixBudgetFrom acc (x :: increasingAbsSort xs) :=
        recursiveExactPrefixBudgetFrom_insertIncreasingAbs_le_cons_of_nonnegative_sorted
          (increasingAbsSort xs) hacc hx hsort_nonneg
          (increasingAbsSort_sorted xs)
      have hrec :
          recursiveExactPrefixBudgetFrom (acc + x) (increasingAbsSort xs) ≤
            recursiveExactPrefixBudgetFrom (acc + x) xs :=
        increasingAbsSort_recursiveExactPrefixBudgetFrom_le xs
          (by linarith) hxs_nonneg
      calc
        recursiveExactPrefixBudgetFrom acc (increasingAbsSort (x :: xs))
            = recursiveExactPrefixBudgetFrom acc
                (insertIncreasingAbs x (increasingAbsSort xs)) := rfl
        _ ≤ recursiveExactPrefixBudgetFrom acc (x :: increasingAbsSort xs) :=
            hins
        _ ≤ recursiveExactPrefixBudgetFrom acc (x :: xs) := by
            simp [recursiveExactPrefixBudgetFrom]
            exact hrec

/-- Higham printed p. 83 nonnegative ordering claim in exact a priori form: replacing
any supplied nonnegative recursive-summation order by increasing magnitude does
not increase the exact prefix-sum bound. -/
theorem increasingAbsSort_recursiveExactPrefixBudget_le (xs : List ℝ)
    (hnonneg : ∀ y ∈ xs, 0 ≤ y) :
    recursiveExactPrefixBudget (increasingAbsSort xs) ≤
      recursiveExactPrefixBudget xs := by
  simpa [recursiveExactPrefixBudget] using
    increasingAbsSort_recursiveExactPrefixBudgetFrom_le xs
      (acc := 0) (by norm_num) hnonneg

/-- Higham pp. 90--91 nonnegative ordering claim in the recursive loop's
running-error-budget language: under exact arithmetic, replacing any supplied
nonnegative list by increasing magnitude cannot increase the list-shaped
pre-rounding budget from equation (4.3). -/
theorem increasingAbsSort_recursiveRoundedPrefixBudget_exactWithUnitRoundoff_le
    (u0 : ℝ) (hu0 : 0 ≤ u0) (xs : List ℝ)
    (hnonneg : ∀ y ∈ xs, 0 ≤ y) :
    recursiveRoundedPrefixBudget
        (FPModel.exactWithUnitRoundoff u0 hu0) (increasingAbsSort xs) ≤
      recursiveRoundedPrefixBudget
        (FPModel.exactWithUnitRoundoff u0 hu0) xs := by
  rw [recursiveRoundedPrefixBudget_exactWithUnitRoundoff,
    recursiveRoundedPrefixBudget_exactWithUnitRoundoff]
  exact increasingAbsSort_recursiveExactPrefixBudget_le xs hnonneg

/-! ## Psum order generation -/

/-- Select one available term minimizing the next exact partial sum
`|acc + x|`, returning the selected term and the remaining terms. -/
noncomputable def psumSelect (acc : ℝ) : List ℝ → Option (ℝ × List ℝ)
  | [] => none
  | x :: xs =>
      match psumSelect acc xs with
      | none => some (x, [])
      | some (y, rest) =>
          if |acc + x| ≤ |acc + y| then
            some (x, xs)
          else
            some (y, x :: rest)

/-- The Psum selector fails exactly on the empty list. -/
theorem psumSelect_eq_none_iff (acc : ℝ) :
    ∀ xs : List ℝ, psumSelect acc xs = none ↔ xs = []
  | [] => by simp [psumSelect]
  | x :: xs => by
      constructor
      · intro h
        cases hsel : psumSelect acc xs with
        | none =>
            simp [psumSelect, hsel] at h
        | some selected =>
            rcases selected with ⟨y, rest⟩
            by_cases hxy : |acc + x| ≤ |acc + y|
            · simp [psumSelect, hsel, hxy] at h
            · simp [psumSelect, hsel, hxy] at h
      · intro h
        cases h

/-- The Psum selector returns a selected element plus a remainder that is a
permutation of the original list. -/
theorem psumSelect_perm {acc x : ℝ} {rest xs : List ℝ}
    (hselect : psumSelect acc xs = some (x, rest)) :
    (x :: rest).Perm xs := by
  induction xs generalizing x rest with
  | nil =>
      simp [psumSelect] at hselect
  | cons z zs ih =>
      cases hsel : psumSelect acc zs with
      | none =>
          have hzs : zs = [] := (psumSelect_eq_none_iff acc zs).1 hsel
          simp [psumSelect, hsel] at hselect
          rcases hselect with ⟨rfl, rfl⟩
          simp [hzs]
      | some selected =>
          rcases selected with ⟨y, restTail⟩
          by_cases hzy : |acc + z| ≤ |acc + y|
          · simp [psumSelect, hsel, hzy] at hselect
            rcases hselect with ⟨rfl, rfl⟩
            rfl
          · simp [psumSelect, hsel, hzy] at hselect
            rcases hselect with ⟨rfl, rfl⟩
            exact (List.Perm.swap z y restTail).trans
              (List.Perm.cons z (ih hsel))

/-- The selected Psum term minimizes the next exact partial sum among all
currently available terms. -/
theorem psumSelect_min {acc x : ℝ} {rest xs : List ℝ}
    (hselect : psumSelect acc xs = some (x, rest)) :
    ∀ y ∈ xs, |acc + x| ≤ |acc + y| := by
  induction xs generalizing x rest with
  | nil =>
      simp [psumSelect] at hselect
  | cons z zs ih =>
      cases hsel : psumSelect acc zs with
      | none =>
          have hzs : zs = [] := (psumSelect_eq_none_iff acc zs).1 hsel
          simp [psumSelect, hsel] at hselect
          rcases hselect with ⟨rfl, rfl⟩
          intro y hy
          simp [hzs] at hy
          subst hy
          rfl
      | some selected =>
          rcases selected with ⟨w, restTail⟩
          have htail_min :
              ∀ y ∈ zs, |acc + w| ≤ |acc + y| := ih hsel
          by_cases hzw : |acc + z| ≤ |acc + w|
          · simp [psumSelect, hsel, hzw] at hselect
            rcases hselect with ⟨rfl, rfl⟩
            intro y hy
            simp at hy
            rcases hy with rfl | hy_tail
            · rfl
            · exact hzw.trans (htail_min y hy_tail)
          · simp [psumSelect, hsel, hzw] at hselect
            rcases hselect with ⟨rfl, rfl⟩
            have hwz : |acc + w| ≤ |acc + z| :=
              le_of_lt (lt_of_not_ge hzw)
            intro y hy
            simp at hy
            rcases hy with rfl | hy_tail
            · exact hwz
            · exact htail_min y hy_tail

/-- The selected Psum term is one of the available terms. -/
theorem psumSelect_mem {acc x : ℝ} {rest xs : List ℝ}
    (hselect : psumSelect acc xs = some (x, rest)) :
    x ∈ xs := by
  have hperm := psumSelect_perm hselect
  exact (hperm.mem_iff).1 (by simp)

/-- For nonnegative data and a nonnegative accumulated sum, Psum's
`|acc + x|` minimizer is a smallest available term. -/
theorem psumSelect_le_of_nonnegative {acc x : ℝ} {rest xs : List ℝ}
    (hacc : 0 ≤ acc)
    (hnonneg : ∀ y ∈ xs, 0 ≤ y)
    (hselect : psumSelect acc xs = some (x, rest)) :
    ∀ y ∈ xs, x ≤ y := by
  intro y hy
  have hmin := psumSelect_min hselect y hy
  have hx_mem : x ∈ xs := psumSelect_mem hselect
  have hx : 0 ≤ x := hnonneg x hx_mem
  have hy0 : 0 ≤ y := hnonneg y hy
  have haccx : 0 ≤ acc + x := add_nonneg hacc hx
  have haccy : 0 ≤ acc + y := add_nonneg hacc hy0
  have hle : acc + x ≤ acc + y := by
    simpa [abs_of_nonneg haccx, abs_of_nonneg haccy] using hmin
  linarith

/-- The remainder left by a Psum selection is nonnegative when the source list
is nonnegative. -/
theorem psumSelect_rest_nonnegative {acc x : ℝ} {rest xs : List ℝ}
    (hnonneg : ∀ y ∈ xs, 0 ≤ y)
    (hselect : psumSelect acc xs = some (x, rest)) :
    ∀ y ∈ rest, 0 ≤ y := by
  intro y hy
  have hperm := psumSelect_perm hselect
  have hy_selected : y ∈ x :: rest := by
    simp [hy]
  exact hnonneg y ((hperm.mem_iff).1 hy_selected)

/-! ### Psum scan comparison costs -/

/-- Number of magnitude comparisons made by the scan-based `psumSelect`
implementation in this file.  A nonempty list with `k + 1` entries compares
the current candidate against the best of the remaining `k` entries. -/
def psumSelectComparisonCost : List ℝ → ℕ
  | [] => 0
  | _ :: xs => xs.length

/-- The scan-based selector uses exactly `length - 1` comparisons, with the
empty-list convention giving zero. -/
theorem psumSelectComparisonCost_eq_pred_length (xs : List ℝ) :
    psumSelectComparisonCost xs = xs.length - 1 := by
  cases xs <;> simp [psumSelectComparisonCost]

/-- Triangular comparison count `0 + 1 + ... + (n - 1)`. -/
def psumTriangularComparisonCost : ℕ → ℕ
  | 0 => 0
  | n + 1 => psumTriangularComparisonCost n + n

/-- Fuelled source-side Psum ordering.  With fuel at least `xs.length`, this
selects a term minimizing `|acc + x|`, recurses with accumulator `acc + x`,
and stops after all original terms have been emitted. -/
noncomputable def psumOrderFromFuel : ℕ → ℝ → List ℝ → List ℝ
  | 0, _acc, _xs => []
  | fuel + 1, acc, xs =>
      match psumSelect acc xs with
      | none => []
      | some (x, rest) => x :: psumOrderFromFuel fuel (acc + x) rest

/-- Comparison count for the scan-based fuelled Psum ordering in this file. -/
noncomputable def psumOrderFromFuelComparisonCost :
    ℕ → ℝ → List ℝ → ℕ
  | 0, _acc, _xs => 0
  | fuel + 1, acc, xs =>
      psumSelectComparisonCost xs +
        match psumSelect acc xs with
        | none => 0
        | some (x, rest) =>
            psumOrderFromFuelComparisonCost fuel (acc + x) rest

/-- Psum ordering from an arbitrary current exact accumulator. -/
noncomputable def psumOrderFrom (acc : ℝ) (xs : List ℝ) : List ℝ :=
  psumOrderFromFuel xs.length acc xs

/-- Comparison count for the exported scan-based Psum ordering from an
arbitrary current exact accumulator. -/
noncomputable def psumOrderFromComparisonCost (acc : ℝ) (xs : List ℝ) : ℕ :=
  psumOrderFromFuelComparisonCost xs.length acc xs

/-- Psum ordering from zero, matching the recursive-summation use case. -/
noncomputable def psumOrder (xs : List ℝ) : List ℝ :=
  psumOrderFrom 0 xs

/-- Comparison count for the exported scan-based zero-accumulator Psum
ordering. -/
noncomputable def psumOrderComparisonCost (xs : List ℝ) : ℕ :=
  psumOrderFromComparisonCost 0 xs

/-- Greedy trace predicate for a complete Psum ordering. -/
inductive PsumGreedyOrderFrom : ℝ → List ℝ → List ℝ → Prop
  | nil (acc : ℝ) : PsumGreedyOrderFrom acc [] []
  | cons {acc x : ℝ} {xs rest out : List ℝ} :
      psumSelect acc xs = some (x, rest) →
      PsumGreedyOrderFrom (acc + x) rest out →
      PsumGreedyOrderFrom acc xs (x :: out)

/-- Every nonempty greedy trace chooses a current minimizer in its first step. -/
theorem PsumGreedyOrderFrom.head_min {acc x : ℝ} {xs out : List ℝ}
    (htrace : PsumGreedyOrderFrom acc xs (x :: out)) :
    x ∈ xs ∧ ∀ y ∈ xs, |acc + x| ≤ |acc + y| := by
  cases htrace with
  | cons hselect _ =>
      exact ⟨psumSelect_mem hselect, psumSelect_min hselect⟩

/-- A complete greedy Psum trace preserves the input multiset. -/
theorem PsumGreedyOrderFrom.perm {acc : ℝ} {xs out : List ℝ}
    (htrace : PsumGreedyOrderFrom acc xs out) :
    out.Perm xs := by
  induction htrace with
  | nil _ => rfl
  | cons hselect _ ih =>
      exact (List.Perm.cons _ ih).trans (psumSelect_perm hselect)

/-- The fuelled Psum order preserves the input multiset when enough fuel is
supplied. -/
theorem psumOrderFromFuel_perm :
    ∀ (fuel : ℕ) (acc : ℝ) (xs : List ℝ),
      xs.length ≤ fuel →
      (psumOrderFromFuel fuel acc xs).Perm xs
  | 0, _acc, xs, hfuel => by
      have hxs : xs = [] := by
        cases xs with
        | nil => rfl
        | cons _ rest => simp at hfuel
      simp [psumOrderFromFuel, hxs]
  | fuel + 1, acc, xs, hfuel => by
      cases hsel : psumSelect acc xs with
      | none =>
          have hxs : xs = [] := (psumSelect_eq_none_iff acc xs).1 hsel
          subst xs
          simp [psumOrderFromFuel, psumSelect]
      | some selected =>
          rcases selected with ⟨x, rest⟩
          have hselect_perm : (x :: rest).Perm xs :=
            psumSelect_perm hsel
          have hlen : rest.length ≤ fuel := by
            have hlen_eq : rest.length + 1 = xs.length := by
              simpa using hselect_perm.length_eq
            have hs : rest.length + 1 ≤ fuel + 1 := by
              rw [hlen_eq]
              exact hfuel
            exact Nat.succ_le_succ_iff.mp hs
          simp [psumOrderFromFuel, hsel]
          exact (List.Perm.cons x
            (psumOrderFromFuel_perm fuel (acc + x) rest hlen)).trans
              hselect_perm

/-- Psum ordering preserves the input multiset. -/
theorem psumOrderFrom_perm (acc : ℝ) (xs : List ℝ) :
    (psumOrderFrom acc xs).Perm xs := by
  exact psumOrderFromFuel_perm xs.length acc xs le_rfl

/-- Psum ordering from zero preserves the input multiset. -/
theorem psumOrder_perm (xs : List ℝ) :
    (psumOrder xs).Perm xs := by
  exact psumOrderFrom_perm 0 xs

/-- For nonnegative data and a nonnegative accumulated sum, the fuelled Psum
order is an increasing-absolute-value order.  This formalizes the printed p. 83
same-sign equivalence up to permutation/tie behavior. -/
theorem psumOrderFromFuel_increasingAbs_of_nonnegative :
    ∀ (fuel : ℕ) (acc : ℝ) (xs : List ℝ),
      xs.length ≤ fuel →
      0 ≤ acc →
      (∀ y ∈ xs, 0 ≤ y) →
      IncreasingAbsList (psumOrderFromFuel fuel acc xs)
  | 0, _acc, xs, _hfuel, _hacc, _hnonneg => by
      simp [psumOrderFromFuel, IncreasingAbsList]
  | fuel + 1, acc, xs, hfuel, hacc, hnonneg => by
      cases hsel : psumSelect acc xs with
      | none =>
          have hxs : xs = [] := (psumSelect_eq_none_iff acc xs).1 hsel
          subst xs
          simp [psumOrderFromFuel, psumSelect, IncreasingAbsList]
      | some selected =>
          rcases selected with ⟨x, rest⟩
          have hselect_perm : (x :: rest).Perm xs :=
            psumSelect_perm hsel
          have hlen : rest.length ≤ fuel := by
            have hlen_eq : rest.length + 1 = xs.length := by
              simpa using hselect_perm.length_eq
            have hs : rest.length + 1 ≤ fuel + 1 := by
              rw [hlen_eq]
              exact hfuel
            exact Nat.succ_le_succ_iff.mp hs
          have hx_mem : x ∈ xs := psumSelect_mem hsel
          have hx_nonneg : 0 ≤ x := hnonneg x hx_mem
          have hrest_nonneg : ∀ y ∈ rest, 0 ≤ y :=
            psumSelect_rest_nonnegative hnonneg hsel
          have hrec :
              IncreasingAbsList (psumOrderFromFuel fuel (acc + x) rest) :=
            psumOrderFromFuel_increasingAbs_of_nonnegative fuel (acc + x)
              rest hlen (add_nonneg hacc hx_nonneg) hrest_nonneg
          have hrest_perm :
              (psumOrderFromFuel fuel (acc + x) rest).Perm rest :=
            psumOrderFromFuel_perm fuel (acc + x) rest hlen
          have hhead_le_abs :
              ∀ y ∈ psumOrderFromFuel fuel (acc + x) rest, |x| ≤ |y| := by
            intro y hy
            have hy_rest : y ∈ rest := (hrest_perm.mem_iff).1 hy
            have hy_xs : y ∈ xs := by
              have hy_selected : y ∈ x :: rest := by
                simp [hy_rest]
              exact (hselect_perm.mem_iff).1 hy_selected
            have hxy : x ≤ y :=
              psumSelect_le_of_nonnegative hacc hnonneg hsel y hy_xs
            have hy_nonneg : 0 ≤ y := hrest_nonneg y hy_rest
            simpa [abs_of_nonneg hx_nonneg, abs_of_nonneg hy_nonneg]
              using hxy
          simp [psumOrderFromFuel, hsel]
          exact IncreasingAbsList.cons_of_abs_le_all hrec hhead_le_abs

/-- Exported Psum from a nonnegative accumulator is increasing by absolute value
on nonnegative inputs. -/
theorem psumOrderFrom_increasingAbs_of_nonnegative
    (acc : ℝ) (xs : List ℝ)
    (hacc : 0 ≤ acc)
    (hnonneg : ∀ y ∈ xs, 0 ≤ y) :
    IncreasingAbsList (psumOrderFrom acc xs) := by
  exact psumOrderFromFuel_increasingAbs_of_nonnegative xs.length acc xs
    le_rfl hacc hnonneg

/-- Zero-accumulator Psum is equivalent to increasing-absolute-value ordering on
nonnegative inputs, up to permutation/tie behavior. -/
theorem psumOrder_increasingAbs_of_nonnegative (xs : List ℝ)
    (hnonneg : ∀ y ∈ xs, 0 ≤ y) :
    IncreasingAbsList (psumOrder xs) := by
  exact psumOrderFrom_increasingAbs_of_nonnegative 0 xs (by norm_num)
    hnonneg

/-- For nonnegative data, Higham's Psum order is the same concrete order as
increasing-magnitude sorting, up to the deterministic tie behavior of the local
list routines.  This is the theorem-level form of the source statement that
same-sign Psum and increasing order are equivalent. -/
theorem psumOrder_eq_increasingAbsSort_of_nonnegative
    (xs : List ℝ) (hnonneg : ∀ z ∈ xs, 0 ≤ z) :
    psumOrder xs = increasingAbsSort xs := by
  have hpsumNonneg : ∀ z ∈ psumOrder xs, 0 ≤ z := by
    intro z hz
    exact hnonneg z ((psumOrder_perm xs).mem_iff.mp hz)
  have hincNonneg : ∀ z ∈ increasingAbsSort xs, 0 ≤ z := by
    intro z hz
    exact hnonneg z ((increasingAbsSort_perm xs).mem_iff.mp hz)
  have hpsumSorted : (psumOrder xs).SortedLE :=
    IncreasingAbsList.sortedLE_of_nonnegative
      (psumOrder_increasingAbs_of_nonnegative xs hnonneg) hpsumNonneg
  have hincSorted : (increasingAbsSort xs).SortedLE :=
    IncreasingAbsList.sortedLE_of_nonnegative
      (increasingAbsSort_sorted xs) hincNonneg
  have hperm : (psumOrder xs).Perm (increasingAbsSort xs) :=
    (psumOrder_perm xs).trans (increasingAbsSort_perm xs).symm
  exact List.Perm.eq_of_sortedLE hpsumSorted hincSorted hperm

/-- Since Psum and increasing order coincide for nonnegative data, Psum
inherits the smallest exact a priori recursive prefix objective. -/
theorem psumOrder_recursiveExactPrefixBudget_le
    (xs : List ℝ) (hnonneg : ∀ y ∈ xs, 0 ≤ y) :
    recursiveExactPrefixBudget (psumOrder xs) ≤
      recursiveExactPrefixBudget xs := by
  rw [psumOrder_eq_increasingAbsSort_of_nonnegative xs hnonneg]
  exact increasingAbsSort_recursiveExactPrefixBudget_le xs hnonneg

/-- Exact-arithmetic running-budget version of
`psumOrder_recursiveExactPrefixBudget_le`. -/
theorem psumOrder_recursiveRoundedPrefixBudget_exactWithUnitRoundoff_le
    (u0 : ℝ) (hu0 : 0 ≤ u0) (xs : List ℝ)
    (hnonneg : ∀ y ∈ xs, 0 ≤ y) :
    recursiveRoundedPrefixBudget
        (FPModel.exactWithUnitRoundoff u0 hu0) (psumOrder xs) ≤
      recursiveRoundedPrefixBudget
        (FPModel.exactWithUnitRoundoff u0 hu0) xs := by
  rw [psumOrder_eq_increasingAbsSort_of_nonnegative xs hnonneg]
  exact increasingAbsSort_recursiveRoundedPrefixBudget_exactWithUnitRoundoff_le
    u0 hu0 xs hnonneg

/-- With enough fuel, the scan-based Psum ordering uses exactly the triangular
number of comparisons.  This theorem records the cost of the concrete local
generator; Higham's `O(n log n)` implementation claim requires a different
data-structure-backed selector. -/
theorem psumOrderFromFuelComparisonCost_eq_triangular :
    ∀ (fuel : ℕ) (acc : ℝ) (xs : List ℝ),
      xs.length ≤ fuel →
      psumOrderFromFuelComparisonCost fuel acc xs =
        psumTriangularComparisonCost xs.length
  | 0, _acc, xs, hfuel => by
      have hxs : xs = [] := by
        cases xs with
        | nil => rfl
        | cons _ rest => simp at hfuel
      simp [psumOrderFromFuelComparisonCost, psumTriangularComparisonCost,
        hxs]
  | fuel + 1, acc, xs, hfuel => by
      cases hsel : psumSelect acc xs with
      | none =>
          have hxs : xs = [] := (psumSelect_eq_none_iff acc xs).1 hsel
          subst xs
          simp [psumOrderFromFuelComparisonCost, psumTriangularComparisonCost,
            psumSelect, psumSelectComparisonCost]
      | some selected =>
          rcases selected with ⟨x, rest⟩
          have hselect_perm : (x :: rest).Perm xs :=
            psumSelect_perm hsel
          have hlen_eq : rest.length + 1 = xs.length := by
            simpa using hselect_perm.length_eq
          have hlen : rest.length ≤ fuel := by
            have hs : rest.length + 1 ≤ fuel + 1 := by
              rw [hlen_eq]
              exact hfuel
            exact Nat.succ_le_succ_iff.mp hs
          have hcost : psumSelectComparisonCost xs = rest.length := by
            rw [psumSelectComparisonCost_eq_pred_length xs]
            omega
          calc
            psumOrderFromFuelComparisonCost (fuel + 1) acc xs
                = psumSelectComparisonCost xs +
                    psumOrderFromFuelComparisonCost fuel (acc + x) rest := by
                    simp [psumOrderFromFuelComparisonCost, hsel]
            _ = rest.length + psumTriangularComparisonCost rest.length := by
                    rw [hcost,
                      psumOrderFromFuelComparisonCost_eq_triangular
                        fuel (acc + x) rest hlen]
            _ = psumTriangularComparisonCost (rest.length + 1) := by
                    simp [psumTriangularComparisonCost, add_comm]
            _ = psumTriangularComparisonCost xs.length := by
                    rw [hlen_eq]

/-- The exported scan-based Psum ordering has exact triangular comparison
cost. -/
theorem psumOrderFromComparisonCost_eq_triangular
    (acc : ℝ) (xs : List ℝ) :
    psumOrderFromComparisonCost acc xs =
      psumTriangularComparisonCost xs.length := by
  exact psumOrderFromFuelComparisonCost_eq_triangular xs.length acc xs le_rfl

/-- The zero-accumulator scan-based Psum ordering has exact triangular
comparison cost. -/
theorem psumOrderComparisonCost_eq_triangular (xs : List ℝ) :
    psumOrderComparisonCost xs =
      psumTriangularComparisonCost xs.length := by
  exact psumOrderFromComparisonCost_eq_triangular 0 xs

/-- The fuelled Psum order realizes the greedy trace when enough fuel is
supplied. -/
theorem psumOrderFromFuel_greedyTrace :
    ∀ (fuel : ℕ) (acc : ℝ) (xs : List ℝ),
      xs.length ≤ fuel →
      PsumGreedyOrderFrom acc xs (psumOrderFromFuel fuel acc xs)
  | 0, acc, xs, hfuel => by
      have hxs : xs = [] := by
        cases xs with
        | nil => rfl
        | cons _ rest => simp at hfuel
      simp [psumOrderFromFuel, hxs]
      exact PsumGreedyOrderFrom.nil acc
  | fuel + 1, acc, xs, hfuel => by
      cases hsel : psumSelect acc xs with
      | none =>
          have hxs : xs = [] := (psumSelect_eq_none_iff acc xs).1 hsel
          subst xs
          simp [psumOrderFromFuel, psumSelect]
          exact PsumGreedyOrderFrom.nil acc
      | some selected =>
          rcases selected with ⟨x, rest⟩
          have hselect_perm : (x :: rest).Perm xs :=
            psumSelect_perm hsel
          have hlen : rest.length ≤ fuel := by
            have hlen_eq : rest.length + 1 = xs.length := by
              simpa using hselect_perm.length_eq
            have hs : rest.length + 1 ≤ fuel + 1 := by
              rw [hlen_eq]
              exact hfuel
            exact Nat.succ_le_succ_iff.mp hs
          simp [psumOrderFromFuel, hsel]
          exact PsumGreedyOrderFrom.cons hsel
            (psumOrderFromFuel_greedyTrace fuel (acc + x) rest hlen)

/-- The exported Psum ordering realizes the greedy trace from any accumulator. -/
theorem psumOrderFrom_greedyTrace (acc : ℝ) (xs : List ℝ) :
    PsumGreedyOrderFrom acc xs (psumOrderFrom acc xs) := by
  exact psumOrderFromFuel_greedyTrace xs.length acc xs le_rfl

/-- The exported zero-accumulator Psum ordering realizes Higham's greedy
successive-partial-sum rule. -/
theorem psumOrder_greedyTrace (xs : List ℝ) :
    PsumGreedyOrderFrom 0 xs (psumOrder xs) := by
  exact psumOrderFrom_greedyTrace 0 xs

/-! ### Optimized Psum comparison-cost contract -/

/-- Per-step comparison budget for a balanced-search implementation of Psum:
find a nearest available value to `-acc` and delete it from the ordered set. -/
def psumLogSearchStepBudget (m : ℕ) : ℕ :=
  2 * Nat.log2 (m + 1) + 1

/-- Total comparison budget obtained by spending a logarithmic selector budget
at each Psum step.  This is the concrete `O(n log n)` cost surface for the
optimized Psum implementation contract. -/
def psumLogSearchComparisonBudget : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      psumLogSearchStepBudget (n + 1) +
        psumLogSearchComparisonBudget n

/-- A Psum trace whose selector is supplied by a logarithmic-cost search data
structure.  The selected value is still the same mathematical Psum minimizer;
the cost field records only comparisons charged to that selector layer. -/
inductive PsumLogSearchTraceFrom :
    ℝ → List ℝ → List ℝ → ℕ → Prop
  | nil (acc : ℝ) :
      PsumLogSearchTraceFrom acc [] [] 0
  | cons {acc x : ℝ} {xs rest out : List ℝ}
      {stepCost restCost : ℕ} :
      psumSelect acc xs = some (x, rest) →
      stepCost ≤ psumLogSearchStepBudget xs.length →
      PsumLogSearchTraceFrom (acc + x) rest out restCost →
      PsumLogSearchTraceFrom acc xs (x :: out) (stepCost + restCost)

namespace PsumLogSearchTraceFrom

/-- A logarithmic-search Psum trace realizes the ordinary greedy Psum trace. -/
theorem greedyTrace {acc : ℝ} {xs out : List ℝ} {cost : ℕ}
    (htrace : PsumLogSearchTraceFrom acc xs out cost) :
    PsumGreedyOrderFrom acc xs out := by
  induction htrace with
  | nil acc =>
      exact PsumGreedyOrderFrom.nil acc
  | cons hselect _hstep _hrec ih =>
      exact PsumGreedyOrderFrom.cons hselect ih

/-- A logarithmic-search Psum trace preserves the input multiset. -/
theorem perm {acc : ℝ} {xs out : List ℝ} {cost : ℕ}
    (htrace : PsumLogSearchTraceFrom acc xs out cost) :
    out.Perm xs :=
  (greedyTrace htrace).perm

/-- The recursive logarithmic-search budget bounds any trace whose individual
selector costs satisfy the step budget. -/
theorem cost_le_budget {acc : ℝ} {xs out : List ℝ} {cost : ℕ}
    (htrace : PsumLogSearchTraceFrom acc xs out cost) :
    cost ≤ psumLogSearchComparisonBudget xs.length := by
  induction htrace with
  | nil acc =>
      simp [psumLogSearchComparisonBudget]
  | cons hselect hstep _hrec ih =>
      rename_i acc x xs rest out stepCost restCost
      have hperm := psumSelect_perm hselect
      have hlen : rest.length + 1 = xs.length := by
        simpa using hperm.length_eq
      calc
        stepCost + restCost ≤
            psumLogSearchStepBudget xs.length +
              psumLogSearchComparisonBudget rest.length := by
          exact Nat.add_le_add hstep ih
        _ = psumLogSearchStepBudget (rest.length + 1) +
              psumLogSearchComparisonBudget rest.length := by
          rw [hlen]
        _ = psumLogSearchComparisonBudget (rest.length + 1) := by
          simp [psumLogSearchComparisonBudget]
        _ = psumLogSearchComparisonBudget xs.length := by
          rw [hlen]

end PsumLogSearchTraceFrom

/-- The per-step logarithmic selector budget is monotone in the active-set
size. -/
theorem psumLogSearchStepBudget_mono {m n : ℕ} (hmn : m ≤ n) :
    psumLogSearchStepBudget m ≤ psumLogSearchStepBudget n := by
  have hlog :
      Nat.log2 (m + 1) ≤ Nat.log2 (n + 1) :=
    by
      simpa [Nat.log2_eq_log_two] using
        (Nat.log_mono_right (b := 2) (n := m + 1) (m := n + 1)
          (Nat.succ_le_succ hmn))
  unfold psumLogSearchStepBudget
  omega

/-- The recursive logarithmic-search budget is bounded by the usual compact
`n * log n`-shaped expression. -/
theorem psumLogSearchComparisonBudget_le_mul_stepBudget (n : ℕ) :
    psumLogSearchComparisonBudget n ≤
      n * psumLogSearchStepBudget n := by
  induction n with
  | zero =>
      simp [psumLogSearchComparisonBudget]
  | succ n ih =>
      have hmono :
          psumLogSearchStepBudget n ≤
            psumLogSearchStepBudget (n + 1) :=
        psumLogSearchStepBudget_mono (Nat.le_succ n)
      calc
        psumLogSearchComparisonBudget (n + 1) =
            psumLogSearchStepBudget (n + 1) +
              psumLogSearchComparisonBudget n := by
          simp [psumLogSearchComparisonBudget]
        _ ≤ psumLogSearchStepBudget (n + 1) +
              n * psumLogSearchStepBudget n := by
          exact Nat.add_le_add_left ih _
        _ ≤ psumLogSearchStepBudget (n + 1) +
              n * psumLogSearchStepBudget (n + 1) := by
          exact Nat.add_le_add_left (Nat.mul_le_mul_left n hmono) _
        _ = (n + 1) * psumLogSearchStepBudget (n + 1) := by
          rw [Nat.succ_mul]
          omega

/-- A predecessor certificate for a sorted/search-tree Psum selector: `x` is
the largest active value not exceeding the target.  For Psum the target is
usually `-acc`. -/
def PsumLowerNeighbor (target : ℝ) (xs : List ℝ) (x : ℝ) : Prop :=
  x ∈ xs ∧ x ≤ target ∧ ∀ y ∈ xs, y ≤ target → y ≤ x

/-- A successor certificate for a sorted/search-tree Psum selector: `x` is the
smallest active value not below the target. -/
def PsumUpperNeighbor (target : ℝ) (xs : List ℝ) (x : ℝ) : Prop :=
  x ∈ xs ∧ target ≤ x ∧ ∀ y ∈ xs, target ≤ y → x ≤ y

/-- Tail sortedness extracted from the `SortedLE` surface used by sorted
list/search-tree Psum adapters. -/
theorem sortedLE_tail_of_cons {x : ℝ} {xs : List ℝ}
    (hsorted : (x :: xs).SortedLE) :
    xs.SortedLE := by
  have hpair : List.Pairwise (fun a b : ℝ => a ≤ b) (x :: xs) := by
    simpa [List.sortedLE_iff_pairwise] using hsorted
  rw [List.sortedLE_iff_pairwise]
  exact (List.pairwise_cons.mp hpair).2

/-- In a `SortedLE` list, the head is no larger than any tail member. -/
theorem sortedLE_head_le_of_mem {x y : ℝ} {xs : List ℝ}
    (hsorted : (x :: xs).SortedLE) (hy : y ∈ xs) :
    x ≤ y := by
  have hpair : List.Pairwise (fun a b : ℝ => a ≤ b) (x :: xs) := by
    simpa [List.sortedLE_iff_pairwise] using hsorted
  exact (List.pairwise_cons.mp hpair).1 y hy

/-- Removing one value from a sorted active list preserves sortedness. -/
theorem sortedLE_erase {x : ℝ} {xs : List ℝ}
    (hsorted : xs.SortedLE) :
    (xs.erase x).SortedLE := by
  have hpair : List.Pairwise (fun a b : ℝ => a ≤ b) xs := by
    simpa [List.sortedLE_iff_pairwise] using hsorted
  rw [List.sortedLE_iff_pairwise]
  exact List.Pairwise.erase x hpair

/-- If `x` occurs in a list, then `x` followed by the list with one occurrence
erased is a permutation of the original list. -/
theorem cons_erase_perm_of_mem {x : ℝ} :
    ∀ {xs : List ℝ}, x ∈ xs → (x :: xs.erase x).Perm xs
  | [], hmem => by
      simp at hmem
  | y :: ys, hmem => by
      by_cases hyx : y = x
      · subst y
        simp [List.erase_cons_head]
      · have hx_mem_tail : x ∈ ys := by
          simp at hmem
          rcases hmem with hxy | hx_tail
          · exact False.elim (hyx hxy.symm)
          · exact hx_tail
        have htail := cons_erase_perm_of_mem hx_mem_tail
        have herase : (y :: ys).erase x = y :: ys.erase x := by
          simp [List.erase_cons_tail, hyx]
        rw [herase]
        exact (List.Perm.swap x y (ys.erase x)).symm.trans
          (List.Perm.cons y htail)

/-- Predecessor search in a sorted active list.  It returns the last entry not
exceeding `target`, when such an entry exists. -/
noncomputable def psumSortedLowerSearch (target : ℝ) : List ℝ → Option ℝ
  | [] => none
  | x :: xs =>
      if x ≤ target then
        match psumSortedLowerSearch target xs with
        | some y => some y
        | none => some x
      else
        none

/-- Successor search in a sorted active list.  It returns the first entry not
below `target`, when such an entry exists. -/
noncomputable def psumSortedUpperSearch (target : ℝ) : List ℝ → Option ℝ
  | [] => none
  | x :: xs =>
      if target ≤ x then
        some x
      else
        psumSortedUpperSearch target xs

/-- Choose the closer of the predecessor and successor candidates for the Psum
objective. -/
noncomputable def psumClosestNeighbor (acc lower upper : ℝ) : ℝ :=
  if |acc + lower| ≤ |acc + upper| then lower else upper

/-- The sorted-list predecessor search fails exactly when no list entry lies at
or below the target. -/
theorem psumSortedLowerSearch_eq_none_iff {target : ℝ} :
    (xs : List ℝ) → xs.SortedLE →
      (psumSortedLowerSearch target xs = none ↔
        ∀ y ∈ xs, ¬ y ≤ target) := by
  intro xs hsorted
  induction xs with
  | nil =>
      simp [psumSortedLowerSearch]
  | cons x xs ih =>
      by_cases hxt : x ≤ target
      · have htailSorted : xs.SortedLE := sortedLE_tail_of_cons hsorted
        cases htail : psumSortedLowerSearch target xs with
        | none =>
            constructor
            · intro h
              simp [psumSortedLowerSearch, hxt, htail] at h
            · intro hall
              exact False.elim ((hall x (by simp)) hxt)
        | some z =>
            constructor
            · intro h
              simp [psumSortedLowerSearch, hxt, htail] at h
            · intro hall
              exact False.elim ((hall x (by simp)) hxt)
      · constructor
        · intro _h y hy
          simp at hy
          rcases hy with rfl | hy_tail
          · exact hxt
          · intro hyt
            exact hxt ((sortedLE_head_le_of_mem hsorted hy_tail).trans hyt)
        · intro _hall
          simp [psumSortedLowerSearch, hxt]

/-- The sorted-list successor search fails exactly when no list entry lies at
or above the target. -/
theorem psumSortedUpperSearch_eq_none_iff {target : ℝ} :
    (xs : List ℝ) → xs.SortedLE →
      (psumSortedUpperSearch target xs = none ↔
        ∀ y ∈ xs, ¬ target ≤ y) := by
  intro xs hsorted
  induction xs with
  | nil =>
      simp [psumSortedUpperSearch]
  | cons x xs ih =>
      by_cases htx : target ≤ x
      · constructor
        · intro h
          simp [psumSortedUpperSearch, htx] at h
        · intro hall
          exact False.elim ((hall x (by simp)) htx)
      · have htailSorted : xs.SortedLE := sortedLE_tail_of_cons hsorted
        constructor
        · intro h y hy
          simp at hy
          rcases hy with rfl | hy_tail
          · exact htx
          · exact (ih htailSorted).1
              (by simpa [psumSortedUpperSearch, htx] using h) y hy_tail
        · intro hall
          have htail_none :
              psumSortedUpperSearch target xs = none :=
            (ih htailSorted).2 (by
              intro y hy
              exact hall y (by simp [hy]))
          simpa [psumSortedUpperSearch, htx] using htail_none

/-- A successful sorted-list predecessor search returns a predecessor
certificate for the target. -/
theorem psumSortedLowerSearch_neighbor {target x : ℝ} :
    ∀ (xs : List ℝ), xs.SortedLE →
      psumSortedLowerSearch target xs = some x →
      PsumLowerNeighbor target xs x
  | [], _hsorted, hsearch => by
      simp [psumSortedLowerSearch] at hsearch
  | y :: ys, hsorted, hsearch => by
      by_cases hyt : y ≤ target
      · cases htail : psumSortedLowerSearch target ys with
        | some z =>
            simp [psumSortedLowerSearch, hyt, htail] at hsearch
            subst x
            have htailSorted : ys.SortedLE := sortedLE_tail_of_cons hsorted
            have hz :
              PsumLowerNeighbor target ys z :=
              psumSortedLowerSearch_neighbor (target := target) (x := z)
                ys htailSorted htail
            constructor
            · simp [hz.1]
            constructor
            · exact hz.2.1
            · intro w hw hwt
              simp at hw
              rcases hw with rfl | hw_tail
              · exact sortedLE_head_le_of_mem hsorted hz.1
              · exact hz.2.2 w hw_tail hwt
        | none =>
            simp [psumSortedLowerSearch, hyt, htail] at hsearch
            subst x
            have htailSorted : ys.SortedLE := sortedLE_tail_of_cons hsorted
            have htail_no :
                ∀ w ∈ ys, ¬ w ≤ target :=
              (psumSortedLowerSearch_eq_none_iff ys htailSorted).1 htail
            constructor
            · simp
            constructor
            · exact hyt
            · intro w hw hwt
              simp at hw
              rcases hw with rfl | hw_tail
              · rfl
              · exact False.elim ((htail_no w hw_tail) hwt)
      · simp [psumSortedLowerSearch, hyt] at hsearch

/-- A successful sorted-list successor search returns a successor certificate
for the target. -/
theorem psumSortedUpperSearch_neighbor {target x : ℝ} :
    ∀ (xs : List ℝ), xs.SortedLE →
      psumSortedUpperSearch target xs = some x →
      PsumUpperNeighbor target xs x
  | [], _hsorted, hsearch => by
      simp [psumSortedUpperSearch] at hsearch
  | y :: ys, hsorted, hsearch => by
      by_cases hty : target ≤ y
      · simp [psumSortedUpperSearch, hty] at hsearch
        subst x
        constructor
        · simp
        constructor
        · exact hty
        · intro w hw _hwt
          simp at hw
          rcases hw with rfl | hw_tail
          · rfl
          · exact sortedLE_head_le_of_mem hsorted hw_tail
      · have htailSorted : ys.SortedLE := sortedLE_tail_of_cons hsorted
        have hx :
            PsumUpperNeighbor target ys x :=
          psumSortedUpperSearch_neighbor (target := target) (x := x)
            ys htailSorted
            (by simpa [psumSortedUpperSearch, hty] using hsearch)
        constructor
        · simp [hx.1]
        constructor
        · exact hx.2.1
        · intro w hw htw
          simp at hw
          rcases hw with rfl | hw_tail
          · exact False.elim (hty htw)
          · exact hx.2.2 w hw_tail htw

/-- Psum selection from a sorted active list by searching for the predecessor
and successor of `-acc`, with one-sided endpoint cases included. -/
noncomputable def psumSortedNeighborSelect (acc : ℝ) (xs : List ℝ) : Option ℝ :=
  match psumSortedLowerSearch (-acc) xs, psumSortedUpperSearch (-acc) xs with
  | some lower, some upper => some (psumClosestNeighbor acc lower upper)
  | some lower, none => some lower
  | none, some upper => some upper
  | none, none => none

/-- On a sorted active list, the sorted-neighbor Psum selector fails exactly on
the empty list. -/
theorem psumSortedNeighborSelect_eq_none_iff {acc : ℝ} {xs : List ℝ}
    (hsorted : xs.SortedLE) :
    psumSortedNeighborSelect acc xs = none ↔ xs = [] := by
  constructor
  · intro hnone
    cases xs with
    | nil => rfl
    | cons x xs =>
        unfold psumSortedNeighborSelect at hnone
        cases hlower : psumSortedLowerSearch (-acc) (x :: xs) with
        | some lower =>
            cases hupper : psumSortedUpperSearch (-acc) (x :: xs) <;>
              simp [hlower, hupper] at hnone
        | none =>
            cases hupper : psumSortedUpperSearch (-acc) (x :: xs) with
            | some upper =>
                simp [hlower, hupper] at hnone
            | none =>
                rcases le_total x (-acc) with hx | hx
                · have hnoLower :
                      ∀ y ∈ x :: xs, ¬ y ≤ -acc :=
                    (psumSortedLowerSearch_eq_none_iff (target := -acc)
                      (x :: xs) hsorted).1 hlower
                  exact False.elim ((hnoLower x (by simp)) hx)
                · have hnoUpper :
                      ∀ y ∈ x :: xs, ¬ -acc ≤ y :=
                    (psumSortedUpperSearch_eq_none_iff (target := -acc)
                      (x :: xs) hsorted).1 hupper
                  exact False.elim ((hnoUpper x (by simp)) hx)
  · intro hxs
    subst xs
    simp [psumSortedNeighborSelect, psumSortedLowerSearch,
      psumSortedUpperSearch]

namespace PsumLowerNeighbor

/-- A predecessor of `-acc` is at least as close to `-acc` as any active value
to its left, expressed in Psum's `|acc + x|` objective. -/
theorem abs_add_le_of_le_neg_acc {acc x y : ℝ} {xs : List ℝ}
    (hx : PsumLowerNeighbor (-acc) xs x)
    (hy_mem : y ∈ xs) (hy : y ≤ -acc) :
    |acc + x| ≤ |acc + y| := by
  have hyx : y ≤ x := hx.2.2 y hy_mem hy
  have hx_nonpos : acc + x ≤ 0 := by linarith [hx.2.1]
  have hy_nonpos : acc + y ≤ 0 := by linarith [hy]
  rw [abs_of_nonpos hx_nonpos, abs_of_nonpos hy_nonpos]
  linarith

/-- If every active value lies at or below `-acc`, the predecessor certificate
alone gives the global Psum minimizer. -/
theorem abs_add_le_all_of_all_le_neg_acc {acc x : ℝ} {xs : List ℝ}
    (hx : PsumLowerNeighbor (-acc) xs x)
    (hall : ∀ y ∈ xs, y ≤ -acc) :
    ∀ y ∈ xs, |acc + x| ≤ |acc + y| := by
  intro y hy_mem
  exact hx.abs_add_le_of_le_neg_acc hy_mem (hall y hy_mem)

end PsumLowerNeighbor

namespace PsumUpperNeighbor

/-- A successor of `-acc` is at least as close to `-acc` as any active value to
its right, expressed in Psum's `|acc + x|` objective. -/
theorem abs_add_le_of_neg_acc_le {acc x y : ℝ} {xs : List ℝ}
    (hx : PsumUpperNeighbor (-acc) xs x)
    (hy_mem : y ∈ xs) (hy : -acc ≤ y) :
    |acc + x| ≤ |acc + y| := by
  have hxy : x ≤ y := hx.2.2 y hy_mem hy
  have hx_nonneg : 0 ≤ acc + x := by linarith [hx.2.1]
  have hy_nonneg : 0 ≤ acc + y := by linarith [hy]
  rw [abs_of_nonneg hx_nonneg, abs_of_nonneg hy_nonneg]
  linarith

/-- If every active value lies at or above `-acc`, the successor certificate
alone gives the global Psum minimizer. -/
theorem abs_add_le_all_of_neg_acc_le_all {acc x : ℝ} {xs : List ℝ}
    (hx : PsumUpperNeighbor (-acc) xs x)
    (hall : ∀ y ∈ xs, -acc ≤ y) :
    ∀ y ∈ xs, |acc + x| ≤ |acc + y| := by
  intro y hy_mem
  exact hx.abs_add_le_of_neg_acc_le hy_mem (hall y hy_mem)

end PsumUpperNeighbor

/-- Core ordered-neighbor selector theorem for a future concrete balanced-tree
Psum implementation.  If a search structure exposes the predecessor and
successor around `-acc`, then choosing the closer of those two values gives a
global minimizer of Higham's Psum objective over the active set. -/
theorem psumNeighborChoice_mem_and_min
    {acc lower upper chosen : ℝ} {xs : List ℝ}
    (hlower : PsumLowerNeighbor (-acc) xs lower)
    (hupper : PsumUpperNeighbor (-acc) xs upper)
    (hchosen : chosen = lower ∨ chosen = upper)
    (hchoose_lower : |acc + chosen| ≤ |acc + lower|)
    (hchoose_upper : |acc + chosen| ≤ |acc + upper|) :
    chosen ∈ xs ∧ ∀ y ∈ xs, |acc + chosen| ≤ |acc + y| := by
  constructor
  · rcases hchosen with rfl | rfl
    · exact hlower.1
    · exact hupper.1
  · intro y hy_mem
    rcases le_total y (-acc) with hyleft | hyright
    · exact le_trans hchoose_lower
        (hlower.abs_add_le_of_le_neg_acc hy_mem hyleft)
    · exact le_trans hchoose_upper
        (hupper.abs_add_le_of_neg_acc_le hy_mem hyright)

/-- Concrete sorted-list selector correctness for Psum.  Searching for the
predecessor and successor of `-acc` in a sorted active list, then choosing the
closer available endpoint, returns a member that minimizes Higham's
`|acc + x|` Psum objective over the active set. -/
theorem psumSortedNeighborSelect_mem_and_min
    {acc selected : ℝ} {xs : List ℝ}
    (hsorted : xs.SortedLE)
    (hselect : psumSortedNeighborSelect acc xs = some selected) :
    selected ∈ xs ∧ ∀ y ∈ xs, |acc + selected| ≤ |acc + y| := by
  unfold psumSortedNeighborSelect at hselect
  cases hlower : psumSortedLowerSearch (-acc) xs with
  | none =>
      cases hupper : psumSortedUpperSearch (-acc) xs with
      | none =>
          simp [hlower, hupper] at hselect
      | some upper =>
          simp [hlower, hupper] at hselect
          subst selected
          have hupperCert :
              PsumUpperNeighbor (-acc) xs upper :=
            psumSortedUpperSearch_neighbor (target := -acc) (x := upper)
              xs hsorted hupper
          have hnoLower :
              ∀ y ∈ xs, ¬ y ≤ -acc :=
            (psumSortedLowerSearch_eq_none_iff (target := -acc)
              xs hsorted).1 hlower
          have hall : ∀ y ∈ xs, -acc ≤ y := by
            intro y hy
            exact le_of_lt (lt_of_not_ge (hnoLower y hy))
          exact ⟨hupperCert.1,
            hupperCert.abs_add_le_all_of_neg_acc_le_all hall⟩
  | some lower =>
      cases hupper : psumSortedUpperSearch (-acc) xs with
      | none =>
          simp [hlower, hupper] at hselect
          subst selected
          have hlowerCert :
              PsumLowerNeighbor (-acc) xs lower :=
            psumSortedLowerSearch_neighbor (target := -acc) (x := lower)
              xs hsorted hlower
          have hnoUpper :
              ∀ y ∈ xs, ¬ -acc ≤ y :=
            (psumSortedUpperSearch_eq_none_iff (target := -acc)
              xs hsorted).1 hupper
          have hall : ∀ y ∈ xs, y ≤ -acc := by
            intro y hy
            exact le_of_lt (lt_of_not_ge (hnoUpper y hy))
          exact ⟨hlowerCert.1,
            hlowerCert.abs_add_le_all_of_all_le_neg_acc hall⟩
      | some upper =>
          simp [hlower, hupper] at hselect
          subst selected
          have hlowerCert :
              PsumLowerNeighbor (-acc) xs lower :=
            psumSortedLowerSearch_neighbor (target := -acc) (x := lower)
              xs hsorted hlower
          have hupperCert :
              PsumUpperNeighbor (-acc) xs upper :=
            psumSortedUpperSearch_neighbor (target := -acc) (x := upper)
              xs hsorted hupper
          exact psumNeighborChoice_mem_and_min
            (hlower := hlowerCert) (hupper := hupperCert)
            (chosen := psumClosestNeighbor acc lower upper)
            (hchosen := by
              unfold psumClosestNeighbor
              by_cases h : |acc + lower| ≤ |acc + upper|
              · simp [h]
              · simp [h])
            (hchoose_lower := by
              unfold psumClosestNeighbor
              by_cases h : |acc + lower| ≤ |acc + upper|
              · simp [h]
              · have hle : |acc + upper| ≤ |acc + lower| :=
                  le_of_lt (lt_of_not_ge h)
                simpa [h] using hle)
            (hchoose_upper := by
              unfold psumClosestNeighbor
              by_cases h : |acc + lower| ≤ |acc + upper|
              · simp [h]
              · simp [h])

/-- Deletion adapter for the sorted-list Psum selector.  A successful selector
call supplies a sorted remainder, a one-element-deletion permutation witness, a
strict length drop, and the Psum minimizer property needed by a full ordered-set
implementation trace. -/
theorem psumSortedNeighborSelect_erase_sorted_perm_length_min
    {acc selected : ℝ} {xs : List ℝ}
    (hsorted : xs.SortedLE)
    (hselect : psumSortedNeighborSelect acc xs = some selected) :
    (xs.erase selected).SortedLE ∧
      (selected :: xs.erase selected).Perm xs ∧
      (xs.erase selected).length + 1 = xs.length ∧
      ∀ y ∈ xs, |acc + selected| ≤ |acc + y| := by
  have hmin := psumSortedNeighborSelect_mem_and_min hsorted hselect
  constructor
  · exact sortedLE_erase hsorted
  constructor
  · exact cons_erase_perm_of_mem hmin.1
  constructor
  · have hlen := List.length_erase_of_mem hmin.1
    have hpos := List.length_pos_of_mem hmin.1
    omega
  · exact hmin.2

/-- A Psum trace stated extensionally: each emitted head is a member of the
current active list, globally minimizes `|acc + x|`, and the recursive active
list is the old active list with one occurrence of the head removed up to
permutation.  This avoids committing to the scan selector's tie-breaking. -/
inductive PsumMinOrderFrom : ℝ → List ℝ → List ℝ → Prop
  | nil (acc : ℝ) : PsumMinOrderFrom acc [] []
  | cons {acc x : ℝ} {xs rest out : List ℝ} :
      x ∈ xs →
      (∀ y ∈ xs, |acc + x| ≤ |acc + y|) →
      (x :: rest).Perm xs →
      PsumMinOrderFrom (acc + x) rest out →
      PsumMinOrderFrom acc xs (x :: out)

namespace PsumMinOrderFrom

/-- An extensional Psum-minimizer trace preserves the active multiset. -/
theorem perm {acc : ℝ} {xs out : List ℝ}
    (htrace : PsumMinOrderFrom acc xs out) :
    out.Perm xs := by
  induction htrace with
  | nil _ =>
      simp
  | cons _hmem _hmin hperm _htrace ih =>
      exact (List.Perm.cons _ ih).trans hperm

end PsumMinOrderFrom

/-- Fuelled sorted-neighbor Psum ordering.  At each step it selects the closer
predecessor/successor around `-acc` in the sorted active list and removes one
selected occurrence. -/
noncomputable def psumSortedNeighborOrderFromFuel :
    ℕ → ℝ → List ℝ → List ℝ
  | 0, _acc, _xs => []
  | fuel + 1, acc, xs =>
      match psumSortedNeighborSelect acc xs with
      | none => []
      | some x =>
          x :: psumSortedNeighborOrderFromFuel fuel (acc + x)
            (xs.erase x)

/-- With enough fuel, the sorted-neighbor Psum implementation realizes an
extensional Psum-minimizer trace. -/
theorem psumSortedNeighborOrderFromFuel_minTrace :
    ∀ (fuel : ℕ) (acc : ℝ) (xs : List ℝ),
      xs.length ≤ fuel →
      xs.SortedLE →
      PsumMinOrderFrom acc xs
        (psumSortedNeighborOrderFromFuel fuel acc xs)
  | 0, acc, xs, hlen, _hsorted => by
      have hxs : xs = [] := by
        cases xs with
        | nil => rfl
        | cons _ rest => simp at hlen
      subst xs
      simp [psumSortedNeighborOrderFromFuel]
      exact PsumMinOrderFrom.nil acc
  | fuel + 1, acc, xs, hlen, hsorted => by
      cases hsel : psumSortedNeighborSelect acc xs with
      | none =>
          have hxs :
              xs = [] :=
            (psumSortedNeighborSelect_eq_none_iff hsorted).1 hsel
          subst xs
          simp [psumSortedNeighborOrderFromFuel, hsel]
          exact PsumMinOrderFrom.nil acc
      | some selected =>
          have hselectedMin :
              selected ∈ xs ∧
                ∀ y ∈ xs, |acc + selected| ≤ |acc + y| :=
            psumSortedNeighborSelect_mem_and_min hsorted hsel
          have hpkg :
              (xs.erase selected).SortedLE ∧
                (selected :: xs.erase selected).Perm xs ∧
                (xs.erase selected).length + 1 = xs.length ∧
                ∀ y ∈ xs, |acc + selected| ≤ |acc + y| :=
            psumSortedNeighborSelect_erase_sorted_perm_length_min
              hsorted hsel
          have hrestLen : (xs.erase selected).length ≤ fuel := by
            omega
          have hrec :
              PsumMinOrderFrom (acc + selected) (xs.erase selected)
                (psumSortedNeighborOrderFromFuel fuel (acc + selected)
                  (xs.erase selected)) :=
            psumSortedNeighborOrderFromFuel_minTrace fuel (acc + selected)
              (xs.erase selected) hrestLen hpkg.1
          simp [psumSortedNeighborOrderFromFuel, hsel]
          exact PsumMinOrderFrom.cons hselectedMin.1 hselectedMin.2
            hpkg.2.1 hrec

/-- A sorted-neighbor Psum trace with an explicit logarithmic selector/deletion
cost at each step.  This is the abstract cost contract a balanced search tree
must instantiate; the selector itself is the sorted predecessor/successor
adapter above. -/
inductive PsumSortedNeighborLogSearchTraceFrom :
    ℝ → List ℝ → List ℝ → ℕ → Prop
  | nil (acc : ℝ) :
      PsumSortedNeighborLogSearchTraceFrom acc [] [] 0
  | cons {acc x : ℝ} {xs out : List ℝ} {stepCost restCost : ℕ} :
      xs.SortedLE →
      psumSortedNeighborSelect acc xs = some x →
      stepCost ≤ psumLogSearchStepBudget xs.length →
      PsumSortedNeighborLogSearchTraceFrom (acc + x) (xs.erase x) out
        restCost →
      PsumSortedNeighborLogSearchTraceFrom acc xs (x :: out)
        (stepCost + restCost)

namespace PsumSortedNeighborLogSearchTraceFrom

/-- A sorted-neighbor log-search trace realizes the extensional Psum-minimizer
trace. -/
theorem minTrace {acc : ℝ} {xs out : List ℝ} {cost : ℕ}
    (htrace : PsumSortedNeighborLogSearchTraceFrom acc xs out cost) :
    PsumMinOrderFrom acc xs out := by
  induction htrace with
  | nil acc =>
      exact PsumMinOrderFrom.nil acc
  | cons hsorted hselect _hstep _hrec ih =>
      have hselectedMin :=
        psumSortedNeighborSelect_mem_and_min hsorted hselect
      have hpkg :=
        psumSortedNeighborSelect_erase_sorted_perm_length_min hsorted hselect
      exact PsumMinOrderFrom.cons hselectedMin.1 hselectedMin.2
        hpkg.2.1 ih

/-- A sorted-neighbor log-search trace preserves the input multiset. -/
theorem perm {acc : ℝ} {xs out : List ℝ} {cost : ℕ}
    (htrace : PsumSortedNeighborLogSearchTraceFrom acc xs out cost) :
    out.Perm xs :=
  (minTrace htrace).perm

/-- The recursive logarithmic-search budget bounds sorted-neighbor traces whose
individual search/delete steps satisfy the per-step logarithmic budget. -/
theorem cost_le_budget {acc : ℝ} {xs out : List ℝ} {cost : ℕ}
    (htrace : PsumSortedNeighborLogSearchTraceFrom acc xs out cost) :
    cost ≤ psumLogSearchComparisonBudget xs.length := by
  induction htrace with
  | nil acc =>
      simp [psumLogSearchComparisonBudget]
  | cons hsorted hselect hstep _hrec ih =>
      rename_i acc x xs out stepCost restCost
      have hpkg :=
        psumSortedNeighborSelect_erase_sorted_perm_length_min hsorted hselect
      have hlen : (xs.erase x).length + 1 = xs.length := hpkg.2.2.1
      calc
        stepCost + restCost ≤
            psumLogSearchStepBudget xs.length +
              psumLogSearchComparisonBudget (xs.erase x).length := by
          exact Nat.add_le_add hstep ih
        _ = psumLogSearchStepBudget ((xs.erase x).length + 1) +
              psumLogSearchComparisonBudget (xs.erase x).length := by
          rw [hlen]
        _ = psumLogSearchComparisonBudget ((xs.erase x).length + 1) := by
          simp [psumLogSearchComparisonBudget]
        _ = psumLogSearchComparisonBudget xs.length := by
          rw [hlen]

end PsumSortedNeighborLogSearchTraceFrom

/-- With enough fuel, the sorted-neighbor Psum implementation admits the same
recursive logarithmic-search cost trace as the abstract balanced-search
contract. -/
theorem psumSortedNeighborOrderFromFuel_logSearchTrace :
    ∀ (fuel : ℕ) (acc : ℝ) (xs : List ℝ),
      xs.length ≤ fuel →
      xs.SortedLE →
      PsumSortedNeighborLogSearchTraceFrom acc xs
        (psumSortedNeighborOrderFromFuel fuel acc xs)
        (psumLogSearchComparisonBudget xs.length)
  | 0, acc, xs, hlen, _hsorted => by
      have hxs : xs = [] := by
        cases xs with
        | nil => rfl
        | cons _ rest => simp at hlen
      subst xs
      simp [psumSortedNeighborOrderFromFuel, psumLogSearchComparisonBudget]
      exact PsumSortedNeighborLogSearchTraceFrom.nil acc
  | fuel + 1, acc, xs, hlen, hsorted => by
      cases hsel : psumSortedNeighborSelect acc xs with
      | none =>
          have hxs :
              xs = [] :=
            (psumSortedNeighborSelect_eq_none_iff hsorted).1 hsel
          subst xs
          simp [psumSortedNeighborOrderFromFuel, psumLogSearchComparisonBudget,
            hsel]
          exact PsumSortedNeighborLogSearchTraceFrom.nil acc
      | some selected =>
          have hpkg :
              (xs.erase selected).SortedLE ∧
                (selected :: xs.erase selected).Perm xs ∧
                (xs.erase selected).length + 1 = xs.length ∧
                ∀ y ∈ xs, |acc + selected| ≤ |acc + y| :=
            psumSortedNeighborSelect_erase_sorted_perm_length_min
              hsorted hsel
          have hrestLen : (xs.erase selected).length ≤ fuel := by
            omega
          have hrec :
              PsumSortedNeighborLogSearchTraceFrom (acc + selected)
                (xs.erase selected)
                (psumSortedNeighborOrderFromFuel fuel (acc + selected)
                  (xs.erase selected))
                (psumLogSearchComparisonBudget (xs.erase selected).length) :=
            psumSortedNeighborOrderFromFuel_logSearchTrace fuel
              (acc + selected) (xs.erase selected) hrestLen hpkg.1
          have hcost :
              psumLogSearchComparisonBudget xs.length =
                psumLogSearchStepBudget xs.length +
                  psumLogSearchComparisonBudget
                    (xs.erase selected).length := by
            rw [← hpkg.2.2.1]
            simp [psumLogSearchComparisonBudget]
          simp [psumSortedNeighborOrderFromFuel, hsel]
          rw [hcost]
          exact PsumSortedNeighborLogSearchTraceFrom.cons hsorted hsel
            le_rfl hrec

/-! ### Concrete red-black-set search certificate for Psum -/

/-- Comparator used by the concrete red-black Psum active set. -/
noncomputable def psumRealCmp (x y : ℝ) : Ordering :=
  compareOfLessAndEq x y

noncomputable instance psumRealCmp.instTransCmp :
    Std.TransCmp psumRealCmp := by
  unfold psumRealCmp
  exact
    Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm
      (fun x : ℝ => lt_irrefl x)
      (fun {x y z : ℝ} hxy hyz => lt_trans hxy hyz)
      (fun {x y : ℝ} hxy => le_of_not_gt hxy)
      (fun {x y : ℝ} hxy hyx => le_antisymm hxy hyx)

/-- The concrete Psum comparator agrees with the ordinary strict order. -/
theorem psumRealCmp_eq_lt {x y : ℝ} :
    psumRealCmp x y = .lt ↔ x < y := by
  unfold psumRealCmp
  exact Batteries.compareOfLessAndEq_eq_lt

/-- The concrete Psum comparator's `.gt` case agrees with the ordinary
reverse strict order. -/
theorem psumRealCmp_eq_gt {x y : ℝ} :
    psumRealCmp x y = .gt ↔ y < x := by
  rw [Std.OrientedCmp.gt_iff_lt (cmp := psumRealCmp), psumRealCmp_eq_lt]

/-- The concrete Psum comparator's `.eq` case is ordinary real equality. -/
theorem psumRealCmp_eq_eq {x y : ℝ} :
    psumRealCmp x y = .eq ↔ x = y := by
  unfold psumRealCmp
  constructor
  · intro h
    by_contra hxy
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · simp [compareOfLessAndEq, hlt] at h
    · have hnlt : ¬ x < y := not_lt_of_gt hgt
      simp [compareOfLessAndEq, hnlt, hxy] at h
  · intro h
    subst y
    simp [compareOfLessAndEq]

/-- A non-`.lt` comparison says the right input is no larger than the left. -/
theorem psumRealCmp_ne_lt_iff_ge {x y : ℝ} :
    psumRealCmp x y ≠ .lt ↔ y ≤ x := by
  exact (not_congr psumRealCmp_eq_lt).trans not_lt

/-- A non-`.gt` comparison says the left input is no larger than the right. -/
theorem psumRealCmp_ne_gt_iff_le {x y : ℝ} :
    psumRealCmp x y ≠ .gt ↔ x ≤ y := by
  exact (not_congr psumRealCmp_eq_gt).trans not_lt

/-- A concrete red-black active set for the distinct-key Psum route.  Equal
real keys are stored once; a counted multiset tree is still needed for duplicate
active values. -/
abbrev PsumRBSet : Type :=
  Batteries.RBSet ℝ psumRealCmp

namespace PsumRBSet

/-- Delete one real key from the red-black active set. -/
noncomputable def eraseValue (t : PsumRBSet) (x : ℝ) : PsumRBSet :=
  t.erase (psumRealCmp x)

/-- Batteries' ordered traversal of the red-black set is sorted by the ordinary
real order. -/
theorem toList_sortedLE (t : PsumRBSet) : t.toList.SortedLE := by
  have hpair :
      t.toList.Pairwise (Batteries.RBNode.cmpLT psumRealCmp) :=
    Batteries.RBSet.toList_sorted (t := t)
  rw [List.sortedLE_iff_pairwise]
  exact hpair.imp (by
    intro x y hxy
    have hcmp : psumRealCmp x y = .lt :=
      (Batteries.RBNode.cmpLT_iff (cmp := psumRealCmp)).1 hxy
    exact le_of_lt (psumRealCmp_eq_lt.1 hcmp))

/-- A red-black lower-bound search returns a Psum predecessor certificate for
the ordered traversal view. -/
theorem lowerBound_neighbor {target x : ℝ} {t : PsumRBSet}
    (h : t.lowerBound? target = some x) :
    PsumLowerNeighbor target t.toList x := by
  constructor
  · exact Batteries.RBSet.lowerBound?_mem_toList h
  constructor
  · exact psumRealCmp_ne_lt_iff_ge.1
      (Batteries.RBSet.lowerBound?_le h)
  · intro y hy hyle
    by_contra hxy_not
    have hxy : x < y := lt_of_not_ge hxy_not
    have hyTree : y ∈ t :=
      Batteries.RBSet.mem_of_mem_toList (t := t) hy
    have hcmp_xy : psumRealCmp x y = .lt :=
      psumRealCmp_eq_lt.2 hxy
    have hcmp_target_y : psumRealCmp target y = .lt :=
      (Batteries.RBSet.lowerBound?_lt
        (t := t) (x := target) (y := x) (z := y) h hyTree).1 hcmp_xy
    exact (not_lt_of_ge hyle) (psumRealCmp_eq_lt.1 hcmp_target_y)

/-- A red-black upper-bound search returns a Psum successor certificate for the
ordered traversal view. -/
theorem upperBound_neighbor {target x : ℝ} {t : PsumRBSet}
    (h : t.upperBound? target = some x) :
    PsumUpperNeighbor target t.toList x := by
  constructor
  · exact Batteries.RBSet.upperBound?_mem_toList h
  constructor
  · exact psumRealCmp_ne_gt_iff_le.1
      (Batteries.RBSet.upperBound?_ge h)
  · intro y hy hty
    by_contra hxy_not
    have hyx : y < x := lt_of_not_ge hxy_not
    have hyTree : y ∈ t :=
      Batteries.RBSet.mem_of_mem_toList (t := t) hy
    have hcmp_yx : psumRealCmp y x = .lt :=
      psumRealCmp_eq_lt.2 hyx
    have hcmp_y_target : psumRealCmp y target = .lt :=
      (Batteries.RBSet.lt_upperBound?
        (t := t) (x := target) (y := x) (z := y) h hyTree).1 hcmp_yx
    exact (not_lt_of_ge hty) (psumRealCmp_eq_lt.1 hcmp_y_target)

/-- Concrete red-black Psum selector: search predecessor and successor of
`-acc`, then choose whichever gives the smaller next partial sum. -/
noncomputable def neighborSelect (acc : ℝ) (t : PsumRBSet) : Option ℝ :=
  match t.lowerBound? (-acc), t.upperBound? (-acc) with
  | some lower, some upper => some (psumClosestNeighbor acc lower upper)
  | some lower, none => some lower
  | none, some upper => some upper
  | none, none => none

/-- If the concrete red-black lower-bound search fails, no value in the
ordered traversal lies at or below the target. -/
theorem lowerBound?_eq_none_no_le {target : ℝ} {t : PsumRBSet}
    (h : t.lowerBound? target = none) :
    ∀ y ∈ t.toList, ¬ y ≤ target := by
  intro y hy hyle
  have hyTree : y ∈ t :=
    Batteries.RBSet.mem_of_mem_toList (t := t) hy
  have hcmp : psumRealCmp target y ≠ .lt :=
    psumRealCmp_ne_lt_iff_ge.2 hyle
  have hexists : ∃ z, t.lowerBound? target = some z :=
    (Batteries.RBSet.lowerBound?_exists (t := t) (x := target)).2
      ⟨y, hyTree, hcmp⟩
  rcases hexists with ⟨z, hz⟩
  rw [h] at hz
  contradiction

/-- If the concrete red-black upper-bound search fails, no value in the
ordered traversal lies at or above the target. -/
theorem upperBound?_eq_none_no_ge {target : ℝ} {t : PsumRBSet}
    (h : t.upperBound? target = none) :
    ∀ y ∈ t.toList, ¬ target ≤ y := by
  intro y hy hty
  have hyTree : y ∈ t :=
    Batteries.RBSet.mem_of_mem_toList (t := t) hy
  have hcmp : psumRealCmp target y ≠ .gt :=
    psumRealCmp_ne_gt_iff_le.2 hty
  have hexists : ∃ z, t.upperBound? target = some z :=
    (Batteries.RBSet.upperBound?_exists (t := t) (x := target)).2
      ⟨y, hyTree, hcmp⟩
  rcases hexists with ⟨z, hz⟩
  rw [h] at hz
  contradiction

/-- The concrete red-black selector returns a member minimizing Higham's Psum
objective over the ordered traversal view of the active set. -/
theorem neighborSelect_mem_and_min {acc selected : ℝ} {t : PsumRBSet}
    (hselect : neighborSelect acc t = some selected) :
    selected ∈ t.toList ∧
      ∀ y ∈ t.toList, |acc + selected| ≤ |acc + y| := by
  unfold neighborSelect at hselect
  cases hlower : t.lowerBound? (-acc) with
  | none =>
      cases hupper : t.upperBound? (-acc) with
      | none =>
          simp [hlower, hupper] at hselect
      | some upper =>
          simp [hlower, hupper] at hselect
          subst selected
          have hupperCert :
              PsumUpperNeighbor (-acc) t.toList upper :=
            upperBound_neighbor hupper
          have hall : ∀ y ∈ t.toList, -acc ≤ y := by
            intro y hy
            exact le_of_lt
              (lt_of_not_ge (lowerBound?_eq_none_no_le hlower y hy))
          exact ⟨hupperCert.1,
            hupperCert.abs_add_le_all_of_neg_acc_le_all hall⟩
  | some lower =>
      cases hupper : t.upperBound? (-acc) with
      | none =>
          simp [hlower, hupper] at hselect
          subst selected
          have hlowerCert :
              PsumLowerNeighbor (-acc) t.toList lower :=
            lowerBound_neighbor hlower
          have hall : ∀ y ∈ t.toList, y ≤ -acc := by
            intro y hy
            exact le_of_lt
              (lt_of_not_ge (upperBound?_eq_none_no_ge hupper y hy))
          exact ⟨hlowerCert.1,
            hlowerCert.abs_add_le_all_of_all_le_neg_acc hall⟩
      | some upper =>
          simp [hlower, hupper] at hselect
          subst selected
          have hlowerCert :
              PsumLowerNeighbor (-acc) t.toList lower :=
            lowerBound_neighbor hlower
          have hupperCert :
              PsumUpperNeighbor (-acc) t.toList upper :=
            upperBound_neighbor hupper
          exact psumNeighborChoice_mem_and_min
            (hlower := hlowerCert) (hupper := hupperCert)
            (chosen := psumClosestNeighbor acc lower upper)
            (hchosen := by
              unfold psumClosestNeighbor
              by_cases h : |acc + lower| ≤ |acc + upper|
              · simp [h]
              · simp [h])
            (hchoose_lower := by
              unfold psumClosestNeighbor
              by_cases h : |acc + lower| ≤ |acc + upper|
              · simp [h]
              · have hle : |acc + upper| ≤ |acc + lower| :=
                  le_of_lt (lt_of_not_ge h)
                simpa [h] using hle)
            (hchoose_upper := by
              unfold psumClosestNeighbor
              by_cases h : |acc + lower| ≤ |acc + upper|
              · simp [h]
              · simp [h])

/-- Red-black balance gives the logarithmic depth bound used to justify the
Psum search/delete step budget. -/
theorem depth_le_logBudget (t : PsumRBSet) :
    t.1.depth ≤ 2 * Nat.log2 (t.size + 1) := by
  simpa using
    (Batteries.RBNode.WF.depth_bound
      (cmp := psumRealCmp) (t := t.1) t.2)

/-- The red-black depth plus one comparison is bounded by the existing
per-step Psum logarithmic budget. -/
theorem depth_succ_le_stepBudget (t : PsumRBSet) :
    t.1.depth + 1 ≤ psumLogSearchStepBudget t.toList.length := by
  have hdepth := depth_le_logBudget t
  have hsize := Batteries.RBSet.size_eq (t := t)
  unfold psumLogSearchStepBudget
  rw [← hsize]
  omega

/-- Erasing a key preserves the red-black depth budget, since Batteries'
`RBSet.erase` returns another well-formed red-black set. -/
theorem eraseValue_depth_succ_le_stepBudget (t : PsumRBSet) (x : ℝ) :
    (eraseValue t x).1.depth + 1 ≤
      psumLogSearchStepBudget (eraseValue t x).toList.length :=
  depth_succ_le_stepBudget (eraseValue t x)

end PsumRBSet

/-! ### Red-black traversal lemmas for native counted-map deletion -/

/-- Batteries' red-black append preserves the ordered traversal as list
append.  This is the structural list fact needed to expose native erase/alter
updates in the counted-map Psum implementation. -/
theorem rbNode_append_toList {α : Type _}
    (l r : Batteries.RBNode α) :
    (l.append r).toList = l.toList ++ r.toList := by
  fun_induction l.append r <;> simp [*]
  case case3 a x b c y d a' z c' h ih =>
    have hmid :
        (Batteries.RBNode.node Batteries.RBColor.red a' z c').toList =
          b.toList ++ c.toList := by
      rw [← h]
      exact ih
    simpa [List.append_assoc] using
      congrArg (fun xs => xs ++ (y :: d.toList)) hmid
  case case5 a x b c y d a' z c' h ih =>
    have hmid :
        (Batteries.RBNode.node Batteries.RBColor.red a' z c').toList =
          b.toList ++ c.toList := by
      rw [← h]
      exact ih
    simpa [List.append_assoc] using
      congrArg (fun xs => xs ++ (y :: d.toList)) hmid

/-- Unwinding a red-black deletion path preserves the traversal as the path
prefix/suffix wrapped around the replacement subtree. -/
theorem rbNodePath_del_toList {α : Type _}
    (p : Batteries.RBNode.Path α) (t : Batteries.RBNode α)
    (c : Batteries.RBColor) :
    (p.del t c).toList = p.withList t.toList := by
  induction p generalizing t c with
  | root =>
      cases c <;> simp [Batteries.RBNode.Path.del]
  | left pc parent y b ih =>
      cases c <;>
        simp [Batteries.RBNode.Path.del, ih]
  | right pc a y parent ih =>
      cases c <;>
        simp [Batteries.RBNode.Path.del, ih]

/-! ### Counted active-set deletion bridge for duplicate Psum values -/

/-- Expand counted active-set entries into the list/multiset view used by the
source Psum algorithm.  An entry `(x, k)` contributes `k` copies of `x`. -/
def psumCountEntriesExpand : List (ℝ × ℕ) → List ℝ
  | [] => []
  | (x, k) :: rest => List.replicate k x ++ psumCountEntriesExpand rest

/-- Expanding counted entries distributes over list append. -/
theorem psumCountEntriesExpand_append
    (xs ys : List (ℝ × ℕ)) :
    psumCountEntriesExpand (xs ++ ys) =
      psumCountEntriesExpand xs ++ psumCountEntriesExpand ys := by
  induction xs with
  | nil => simp [psumCountEntriesExpand]
  | cons entry rest ih =>
      rcases entry with ⟨x, k⟩
      simp [psumCountEntriesExpand, ih, List.append_assoc]

/-- Remove one positive counted occurrence of `x`, preserving entry order.
Zero-count entries are skipped so the operation remains correct even before a
future counted-tree invariant removes them. -/
noncomputable def psumCountEntriesEraseOne (x : ℝ) :
    List (ℝ × ℕ) → List (ℝ × ℕ)
  | [] => []
  | (y, 0) :: rest => (y, 0) :: psumCountEntriesEraseOne x rest
  | (y, k + 1) :: rest =>
      if y = x then
        match k with
        | 0 => rest
        | k' + 1 => (y, k' + 1) :: rest
      else
        (y, k + 1) :: psumCountEntriesEraseOne x rest

/-- Move a consed element across a fixed prefix, preserving the list multiset. -/
theorem list_cons_append_perm_append_cons {α : Type _} (x : α) :
    ∀ (pref suff : List α),
      (x :: pref ++ suff).Perm (pref ++ x :: suff)
  | [], suff => by simp
  | y :: ys, suff => by
      exact
        (List.Perm.swap x y (ys ++ suff)).symm.trans
          (List.Perm.cons y
            (list_cons_append_perm_append_cons x ys suff))

/-- Lift a one-element deletion permutation through fixed prefix and suffix
contexts. -/
theorem list_cons_append_perm_append_of_cons_perm {α : Type _}
    (x : α) (pref mid suff new : List α)
    (h : (x :: mid).Perm new) :
    (x :: pref ++ mid ++ suff).Perm (pref ++ new ++ suff) := by
  have hmove :
      (x :: pref ++ (mid ++ suff)).Perm
        (pref ++ x :: mid ++ suff) := by
    simpa [List.append_assoc] using
      (list_cons_append_perm_append_cons x pref (mid ++ suff))
  have happ :
      (pref ++ x :: mid ++ suff).Perm
        (pref ++ new ++ suff) := by
    simpa [List.append_assoc] using
      (List.Perm.append_left pref (h.append_right suff))
  simpa [List.append_assoc] using hmove.trans happ

/-- Counted deletion realizes one list-level deletion in the expanded
active-set view.  This is the duplicate-aware permutation bridge needed by a
future counted red-black Psum implementation. -/
theorem psumCountEntriesEraseOne_perm {x : ℝ} :
    ∀ {entries : List (ℝ × ℕ)},
      x ∈ psumCountEntriesExpand entries →
      (x :: psumCountEntriesExpand
        (psumCountEntriesEraseOne x entries)).Perm
        (psumCountEntriesExpand entries)
  | [], hmem => by
      simp [psumCountEntriesExpand] at hmem
  | (y, 0) :: rest, hmem => by
      have hrest : x ∈ psumCountEntriesExpand rest := by
        simpa [psumCountEntriesExpand] using hmem
      simpa [psumCountEntriesExpand, psumCountEntriesEraseOne] using
        (psumCountEntriesEraseOne_perm (x := x) hrest)
  | (y, k + 1) :: rest, hmem => by
      by_cases hyx : y = x
      · subst y
        cases k with
        | zero =>
            simp [psumCountEntriesExpand, psumCountEntriesEraseOne]
        | succ k' =>
            have hrep :
                List.replicate (k' + 2) x =
                  x :: List.replicate (k' + 1) x := by
              rw [show k' + 2 = Nat.succ (k' + 1) by omega]
              rfl
            simp [psumCountEntriesExpand, psumCountEntriesEraseOne, hrep]
      · have hrest : x ∈ psumCountEntriesExpand rest := by
          have hsplit :
              x = y ∨ x ∈ psumCountEntriesExpand rest := by
            simpa [psumCountEntriesExpand] using hmem
          rcases hsplit with hxy | hrest
          · exact False.elim (hyx hxy.symm)
          · exact hrest
        have ih :
            (x :: psumCountEntriesExpand
              (psumCountEntriesEraseOne x rest)).Perm
              (psumCountEntriesExpand rest) :=
          psumCountEntriesEraseOne_perm (x := x) hrest
        have hmove :
            (x :: List.replicate (k + 1) y ++
                psumCountEntriesExpand
                  (psumCountEntriesEraseOne x rest)).Perm
              (List.replicate (k + 1) y ++ x ::
                psumCountEntriesExpand
                  (psumCountEntriesEraseOne x rest)) :=
          list_cons_append_perm_append_cons x
            (List.replicate (k + 1) y)
            (psumCountEntriesExpand
              (psumCountEntriesEraseOne x rest))
        have happ :
            (List.replicate (k + 1) y ++ x ::
                psumCountEntriesExpand
                  (psumCountEntriesEraseOne x rest)).Perm
              (List.replicate (k + 1) y ++
                psumCountEntriesExpand rest) :=
          List.Perm.append_left (List.replicate (k + 1) y) ih
        simpa [psumCountEntriesExpand, psumCountEntriesEraseOne, hyx] using
          hmove.trans happ

/-- Counted deletion drops the expanded active-list length by exactly one. -/
theorem psumCountEntriesEraseOne_length {x : ℝ}
    {entries : List (ℝ × ℕ)}
    (hmem : x ∈ psumCountEntriesExpand entries) :
    (psumCountEntriesExpand
      (psumCountEntriesEraseOne x entries)).length + 1 =
      (psumCountEntriesExpand entries).length := by
  have hperm := psumCountEntriesEraseOne_perm (x := x) hmem
  have hlen := hperm.length_eq
  simpa [Nat.succ_eq_add_one] using hlen

/-- Decrementing one counted occurrence preserves the positive-count invariant
for every remaining entry. -/
theorem psumCountEntriesEraseOne_preserves_positive {x : ℝ} :
    ∀ {entries : List (ℝ × ℕ)},
      (∀ {y : ℝ} {k : ℕ}, (y, k) ∈ entries → 0 < k) →
      ∀ {y : ℝ} {k : ℕ},
        (y, k) ∈ psumCountEntriesEraseOne x entries → 0 < k
  | [], _hpos, y, k, hmem => by
      simp [psumCountEntriesEraseOne] at hmem
  | (z, 0) :: _rest, hpos, _y, _k, _hmem => by
      have hzero : 0 < 0 := hpos (y := z) (k := 0) (by simp)
      omega
  | (z, n + 1) :: rest, hpos, y, k, hmem => by
      have hrestPos :
          ∀ {w : ℝ} {m : ℕ}, (w, m) ∈ rest → 0 < m := by
        intro w m hw
        exact hpos (y := w) (k := m) (by simp [hw])
      by_cases hzx : z = x
      · subst z
        cases n with
        | zero =>
            exact hrestPos (by
              simpa [psumCountEntriesEraseOne] using hmem)
        | succ n' =>
            have hsplit :
                (y, k) = (x, n' + 1) ∨ (y, k) ∈ rest := by
              simpa [psumCountEntriesEraseOne] using hmem
            rcases hsplit with hhead | htail
            · cases hhead
              omega
            · exact hrestPos htail
      · have hsplit :
            (y, k) = (z, n + 1) ∨
              (y, k) ∈ psumCountEntriesEraseOne x rest := by
          simpa [psumCountEntriesEraseOne, hzx] using hmem
        rcases hsplit with hhead | htail
        · cases hhead
          omega
        · exact
            psumCountEntriesEraseOne_preserves_positive
              (x := x) (entries := rest) hrestPos htail

/-- A positive counted entry contributes its value to the expanded active list. -/
theorem mem_psumCountEntriesExpand_of_entry {x : ℝ} {k : ℕ} :
    ∀ {entries : List (ℝ × ℕ)},
      (x, k) ∈ entries →
      0 < k →
      x ∈ psumCountEntriesExpand entries
  | [], hmem, _hk => by
      simp at hmem
  | (y, m) :: rest, hmem, hk => by
      simp at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨rfl, rfl⟩
        have hk_ne : k ≠ 0 := by omega
        simp [psumCountEntriesExpand, hk_ne]
      · simp [psumCountEntriesExpand,
          mem_psumCountEntriesExpand_of_entry (entries := rest) htail hk]

/-- Every member of the expanded active list comes from a positive counted
entry. -/
theorem exists_entry_of_mem_psumCountEntriesExpand {x : ℝ} :
    ∀ {entries : List (ℝ × ℕ)},
      x ∈ psumCountEntriesExpand entries →
      ∃ k : ℕ, (x, k) ∈ entries ∧ 0 < k
  | [], hmem => by
      simp [psumCountEntriesExpand] at hmem
  | (y, k) :: rest, hmem => by
      have hsplit :
          x ∈ List.replicate k y ∨
            x ∈ psumCountEntriesExpand rest := by
        simpa [psumCountEntriesExpand] using hmem
      rcases hsplit with hrep | hrest
      · have hk_ne : k ≠ 0 := (List.mem_replicate.mp hrep).1
        have hx : x = y := (List.mem_replicate.mp hrep).2
        have hk : 0 < k := Nat.pos_of_ne_zero hk_ne
        subst x
        exact ⟨k, by simp, hk⟩
      · rcases exists_entry_of_mem_psumCountEntriesExpand
          (entries := rest) hrest with ⟨m, hm, hmpos⟩
        exact ⟨m, by simp [hm], hmpos⟩

/-- If every counted entry is positive, expanding counts cannot shorten the
entry list. -/
theorem psumCountEntriesExpand_length_ge_entries_length_of_positive
    {entries : List (ℝ × ℕ)}
    (hpos : ∀ {x : ℝ} {k : ℕ}, (x, k) ∈ entries → 0 < k) :
    entries.length ≤ (psumCountEntriesExpand entries).length := by
  induction entries with
  | nil =>
      simp [psumCountEntriesExpand]
  | cons entry rest ih =>
      rcases entry with ⟨x, k⟩
      have hk : 0 < k := hpos (x := x) (k := k) (by simp)
      have hrestPos :
          ∀ {y : ℝ} {m : ℕ}, (y, m) ∈ rest → 0 < m := by
        intro y m hmem
        exact hpos (x := y) (k := m) (by simp [hmem])
      have hrest := ih hrestPos
      simp [psumCountEntriesExpand]
      omega

/-! ### Counted red-black-map active set for duplicate Psum values -/

/-- A concrete counted red-black map for Psum active values.  Keys are active
real values and values are positive multiplicities. -/
abbrev PsumCountRBMap : Type :=
  Batteries.RBMap ℝ ℕ psumRealCmp

namespace PsumCountRBMap

/-- Expanded source-list view of the counted red-black active set. -/
noncomputable def activeList (t : PsumCountRBMap) : List ℝ :=
  psumCountEntriesExpand t.toList

/-- Counted active-set invariant: every stored key has positive multiplicity. -/
def PositiveCounts (t : PsumCountRBMap) : Prop :=
  ∀ {x : ℝ} {k : ℕ}, (x, k) ∈ t.toList → 0 < k

/-- Lower-bound query for the counted red-black map, using only the key. -/
noncomputable def lowerBound? (t : PsumCountRBMap) (target : ℝ) :
    Option (ℝ × ℕ) :=
  Batteries.RBSet.lowerBoundP? t
    (fun p : ℝ × ℕ => psumRealCmp target p.1)

/-- Upper-bound query for the counted red-black map, using only the key. -/
noncomputable def upperBound? (t : PsumCountRBMap) (target : ℝ) :
    Option (ℝ × ℕ) :=
  Batteries.RBSet.upperBoundP? t
    (fun p : ℝ × ℕ => psumRealCmp target p.1)

/-- A map entry with positive count contributes its key to the expanded active
list. -/
theorem mem_activeList_of_entry {t : PsumCountRBMap} {x : ℝ} {k : ℕ}
    (hmem : (x, k) ∈ t.toList) (hk : 0 < k) :
    x ∈ activeList t := by
  exact mem_psumCountEntriesExpand_of_entry
    (entries := t.toList) hmem hk

/-- Any expanded-list member comes from a positive counted map entry. -/
theorem exists_entry_of_mem_activeList {t : PsumCountRBMap} {x : ℝ}
    (hmem : x ∈ activeList t) :
    ∃ k : ℕ, (x, k) ∈ t.toList ∧ 0 < k := by
  exact exists_entry_of_mem_psumCountEntriesExpand
    (entries := t.toList) hmem

/-- A concrete counted entry is recovered by native key lookup. -/
theorem find?_some_of_mem_toList {t : PsumCountRBMap} {x : ℝ} {k : ℕ}
    (hmem : (x, k) ∈ t.toList) :
    t.find? x = some k := by
  exact (Batteries.RBMap.find?_some
    (t := t) (x := x) (v := k)).2
    ⟨x, hmem, psumRealCmp_eq_eq.2 rfl⟩

/-- Every expanded active-list member has a positive native lookup count. -/
theorem exists_find?_of_mem_activeList {t : PsumCountRBMap} {x : ℝ}
    (hmem : x ∈ activeList t) :
    ∃ k : ℕ, 0 < k ∧ t.find? x = some k := by
  rcases exists_entry_of_mem_activeList hmem with ⟨k, hentry, hpos⟩
  exact ⟨k, hpos, find?_some_of_mem_toList hentry⟩

/-- Concrete lower-bound search on a counted red-black map returns a Psum
predecessor certificate for the expanded active-list view. -/
theorem lowerBound_neighbor {target x : ℝ} {k : ℕ}
    {t : PsumCountRBMap}
    (hpos : PositiveCounts t)
    (h : lowerBound? t target = some (x, k)) :
    PsumLowerNeighbor target (activeList t) x := by
  have hentryMem : (x, k) ∈ t.toList := by
    simpa [lowerBound?] using
      (Batteries.RBSet.lowerBoundP?_mem_toList
        (t := t)
        (cut := fun p : ℝ × ℕ => psumRealCmp target p.1)
        h)
  constructor
  · exact mem_activeList_of_entry hentryMem (hpos hentryMem)
  constructor
  · exact psumRealCmp_ne_lt_iff_ge.1
      (Batteries.RBSet.lowerBoundP?_le
        (t := t)
        (cut := fun p : ℝ × ℕ => psumRealCmp target p.1)
        (by simpa [lowerBound?] using h))
  · intro y hy hyle
    rcases exists_entry_of_mem_activeList hy with ⟨ky, hyEntry, _hypos⟩
    by_contra hxy_not
    have hxy : x < y := lt_of_not_ge hxy_not
    have hyTree :
        Batteries.RBSet.Mem (cmp := Ordering.byKey Prod.fst psumRealCmp)
          (y, ky)
          (t : Batteries.RBSet (ℝ × ℕ)
            (Ordering.byKey Prod.fst psumRealCmp)) :=
      Batteries.RBSet.mem_of_mem_toList
        (t := (t : Batteries.RBSet (ℝ × ℕ)
          (Ordering.byKey Prod.fst psumRealCmp))) hyEntry
    have hcmp_xy :
        Ordering.byKey Prod.fst psumRealCmp (x, k) (y, ky) = .lt := by
      simpa [Ordering.byKey, psumRealCmp_eq_lt] using hxy
    have hcmp_target_y : psumRealCmp target y = .lt :=
      (Batteries.RBSet.lowerBoundP?_lt
        (t := t)
        (cut := fun p : ℝ × ℕ => psumRealCmp target p.1)
        (x := (x, k)) (y := (y, ky))
        (by simpa [lowerBound?] using h)
        hyTree).1 hcmp_xy
    exact (not_lt_of_ge hyle) (psumRealCmp_eq_lt.1 hcmp_target_y)

/-- Concrete upper-bound search on a counted red-black map returns a Psum
successor certificate for the expanded active-list view. -/
theorem upperBound_neighbor {target x : ℝ} {k : ℕ}
    {t : PsumCountRBMap}
    (hpos : PositiveCounts t)
    (h : upperBound? t target = some (x, k)) :
    PsumUpperNeighbor target (activeList t) x := by
  have hentryMem : (x, k) ∈ t.toList := by
    simpa [upperBound?] using
      (Batteries.RBSet.upperBoundP?_mem_toList
        (t := t)
        (cut := fun p : ℝ × ℕ => psumRealCmp target p.1)
        h)
  constructor
  · exact mem_activeList_of_entry hentryMem (hpos hentryMem)
  constructor
  · exact psumRealCmp_ne_gt_iff_le.1
      (Batteries.RBSet.upperBoundP?_ge
        (t := t)
        (cut := fun p : ℝ × ℕ => psumRealCmp target p.1)
        (by simpa [upperBound?] using h))
  · intro y hy hty
    rcases exists_entry_of_mem_activeList hy with ⟨ky, hyEntry, _hypos⟩
    by_contra hxy_not
    have hyx : y < x := lt_of_not_ge hxy_not
    have hyTree :
        Batteries.RBSet.Mem (cmp := Ordering.byKey Prod.fst psumRealCmp)
          (y, ky)
          (t : Batteries.RBSet (ℝ × ℕ)
            (Ordering.byKey Prod.fst psumRealCmp)) :=
      Batteries.RBSet.mem_of_mem_toList
        (t := (t : Batteries.RBSet (ℝ × ℕ)
          (Ordering.byKey Prod.fst psumRealCmp))) hyEntry
    have hcmp_yx :
        Ordering.byKey Prod.fst psumRealCmp (y, ky) (x, k) = .lt := by
      simpa [Ordering.byKey, psumRealCmp_eq_lt] using hyx
    have hcmp_target_y : psumRealCmp target y = .gt :=
      (Batteries.RBSet.lt_upperBoundP?
        (t := t)
        (cut := fun p : ℝ × ℕ => psumRealCmp target p.1)
        (x := (x, k)) (y := (y, ky))
        (by simpa [upperBound?] using h)
        hyTree).1 hcmp_yx
    exact (not_lt_of_ge hty) (psumRealCmp_eq_gt.1 hcmp_target_y)

/-- Counted red-black Psum selector: search predecessor and successor of
`-acc`, then choose the key giving the smaller next partial sum. -/
noncomputable def neighborSelect (acc : ℝ) (t : PsumCountRBMap) :
    Option ℝ :=
  match lowerBound? t (-acc), upperBound? t (-acc) with
  | some (lower, _), some (upper, _) =>
      some (psumClosestNeighbor acc lower upper)
  | some (lower, _), none => some lower
  | none, some (upper, _) => some upper
  | none, none => none

/-- Native counted-map decrement/erase operation.  It removes a key when the
stored multiplicity is `0` or `1`, and otherwise decrements the multiplicity
in place using Batteries' logarithmic `RBMap.alter`.  The positive-count
invariant rules out the `0` branch for certified calls; it is included here so
the executable operation remains total. -/
noncomputable def eraseOneNative (t : PsumCountRBMap) (x : ℝ) :
    PsumCountRBMap :=
  Batteries.RBMap.alter t x (fun
    | none => none
    | some k =>
        match k with
        | 0 => none
        | 1 => none
        | k' + 2 => some (k' + 1))

/-- Local ordered-traversal payload produced by the native counted-map
decrement/delete branch. -/
def eraseOneNativeBranchList (x : ℝ) (k : ℕ)
    (a b : Batteries.RBNode (ℝ × ℕ)) : List (ℝ × ℕ) :=
  match k with
  | 0 => a.toList ++ b.toList
  | 1 => a.toList ++ b.toList
  | k' + 2 => a.toList ++ (x, k' + 1) :: b.toList

/-- The native decrement/delete branch removes exactly one expanded occurrence
from the zoomed node traversal. -/
theorem eraseOneNativeBranchList_expand_perm_node
    {x : ℝ} {k : ℕ} (hk : 0 < k)
    (c : Batteries.RBColor) (a b : Batteries.RBNode (ℝ × ℕ)) :
    (x :: psumCountEntriesExpand (eraseOneNativeBranchList x k a b)).Perm
      (psumCountEntriesExpand
        (Batteries.RBNode.node c a (x, k) b).toList) := by
  cases k with
  | zero => omega
  | succ k0 =>
      cases k0 with
      | zero =>
          simpa [eraseOneNativeBranchList, psumCountEntriesExpand,
            psumCountEntriesExpand_append, List.append_assoc] using
            (list_cons_append_perm_append_cons x
              (psumCountEntriesExpand a.toList)
              (psumCountEntriesExpand b.toList))
      | succ k1 =>
          have hrep :
              List.replicate (k1 + 2) x =
                x :: List.replicate (k1 + 1) x := by
            rw [show k1 + 2 = Nat.succ (k1 + 1) by omega]
            rfl
          simpa [eraseOneNativeBranchList, psumCountEntriesExpand,
            psumCountEntriesExpand_append, List.append_assoc, hrep] using
            (list_cons_append_perm_append_cons x
              (psumCountEntriesExpand a.toList)
              (List.replicate (k1 + 1) x ++
                psumCountEntriesExpand b.toList))

/-- If the native decrement zooms to a concrete counted entry `(x, k)`, its
ordered traversal is exactly the local decrement/delete of that entry, wrapped
back through the red-black search path.  This is the executable `RBMap.alter`
branch theorem needed by the C4.3 counted-map Psum loop. -/
theorem eraseOneNative_toList_of_zoom {t : PsumCountRBMap} {x : ℝ}
    {c : Batteries.RBColor} {a b : Batteries.RBNode (ℝ × ℕ)}
    {path : Batteries.RBNode.Path (ℝ × ℕ)} {k : ℕ}
    (hzoom :
      t.1.zoom (fun p : ℝ × ℕ => psumRealCmp x p.1) =
        (Batteries.RBNode.node c a (x, k) b, path)) :
    (eraseOneNative t x).toList =
      path.withList (eraseOneNativeBranchList x k a b) := by
  unfold eraseOneNative Batteries.RBMap.alter Batteries.RBSet.alterP
  simp only [Batteries.RBMap.toList, Batteries.RBSet.toList]
  simp only [Batteries.RBNode.alter, hzoom]
  cases k with
  | zero =>
      simp [Batteries.RBMap.alter.adapt, rbNodePath_del_toList,
        rbNode_append_toList, eraseOneNativeBranchList]
  | succ k0 =>
      cases k0 with
      | zero =>
          simp [Batteries.RBMap.alter.adapt, rbNodePath_del_toList,
            rbNode_append_toList, eraseOneNativeBranchList]
      | succ k1 =>
          simp [Batteries.RBMap.alter.adapt, eraseOneNativeBranchList]

/-- A successful counted-map key lookup identifies the same concrete red-black
`zoom` branch.  This lifts the user-facing `find?` certificate to the native
node/path shape consumed by the `RBMap.alter` traversal theorem. -/
theorem find?_some_zoom {t : PsumCountRBMap} {x : ℝ} {k : ℕ}
    (hfind : t.find? x = some k) :
    ∃ (c : Batteries.RBColor) (a b : Batteries.RBNode (ℝ × ℕ))
      (path : Batteries.RBNode.Path (ℝ × ℕ)),
      t.1.zoom (fun p : ℝ × ℕ => psumRealCmp x p.1) =
        (Batteries.RBNode.node c a (x, k) b, path) := by
  simp only [Batteries.RBMap.find?, Batteries.RBMap.findEntry?,
    Batteries.RBSet.findP?] at hfind
  rw [Batteries.RBNode.find?_eq_zoom] at hfind
  cases hzoom : t.1.zoom (fun p : ℝ × ℕ => psumRealCmp x p.1) with
  | mk found path =>
      rw [hzoom] at hfind
      cases found with
      | nil =>
          exact False.elim (by
            rcases hfind with ⟨a, ha⟩)
      | node c a entry b =>
          rcases entry with ⟨x', k'⟩
          simp at hfind
          rcases hfind with ⟨xFound, hroot⟩
          cases hroot
          have hx : x' = x := by
            have hmemFind :
                (x', k) ∈
                  Batteries.RBNode.find?
                    (fun p : ℝ × ℕ => psumRealCmp x p.1) t.1 := by
              rw [Batteries.RBNode.find?_eq_zoom, hzoom]
              exact rfl
            have hcut :
                psumRealCmp x x' = .eq :=
              Batteries.RBNode.find?_some_eq_eq
                (t := t.1)
                (cut := fun p : ℝ × ℕ => psumRealCmp x p.1)
                (x := (x', k)) hmemFind
            exact (psumRealCmp_eq_eq.1 hcut).symm
          subst x'
          exact ⟨c, a, b, path, rfl⟩

/-- Global `find?`-indexed form of the native decrement traversal theorem. -/
theorem eraseOneNative_toList_of_find? {t : PsumCountRBMap} {x : ℝ}
    {k : ℕ} (hfind : t.find? x = some k) :
    ∃ (c : Batteries.RBColor) (a b : Batteries.RBNode (ℝ × ℕ))
      (path : Batteries.RBNode.Path (ℝ × ℕ)),
      t.1.zoom (fun p : ℝ × ℕ => psumRealCmp x p.1) =
        (Batteries.RBNode.node c a (x, k) b, path) ∧
      (eraseOneNative t x).toList =
        path.withList (eraseOneNativeBranchList x k a b) := by
  rcases find?_some_zoom hfind with ⟨c, a, b, path, hzoom⟩
  refine ⟨c, a, b, path, hzoom, ?_⟩
  simpa using (eraseOneNative_toList_of_zoom hzoom)

/-- Expanded active-list membership is enough to obtain the positive native
count and the concrete decrement/delete traversal for that key. -/
theorem eraseOneNative_toList_of_mem_activeList {t : PsumCountRBMap}
    {x : ℝ} (hmem : x ∈ activeList t) :
    ∃ (k : ℕ) (c : Batteries.RBColor)
      (a b : Batteries.RBNode (ℝ × ℕ))
      (path : Batteries.RBNode.Path (ℝ × ℕ)),
      0 < k ∧
      t.find? x = some k ∧
      t.1.zoom (fun p : ℝ × ℕ => psumRealCmp x p.1) =
        (Batteries.RBNode.node c a (x, k) b, path) ∧
      (eraseOneNative t x).toList =
        path.withList (eraseOneNativeBranchList x k a b) := by
  rcases exists_find?_of_mem_activeList hmem with ⟨k, hpos, hfind⟩
  rcases eraseOneNative_toList_of_find? hfind with
    ⟨c, a, b, path, hzoom, hlist⟩
  exact ⟨k, c, a, b, path, hpos, hfind, hzoom, hlist⟩

/-- The native counted-map decrement/delete realizes one expanded active-list
deletion by permutation. -/
theorem eraseOneNative_activeList_perm {t : PsumCountRBMap}
    {x : ℝ} (hmem : x ∈ activeList t) :
    (x :: activeList (eraseOneNative t x)).Perm (activeList t) := by
  rcases eraseOneNative_toList_of_mem_activeList hmem with
    ⟨k, c, a, b, path, hk, _hfind, hzoom, hlist⟩
  have horig :
      path.withList
        (Batteries.RBNode.node c a (x, k) b).toList =
        t.toList := by
    exact
      (Batteries.RBNode.zoom_toList (t := t.1)
        (cut := fun p : ℝ × ℕ => psumRealCmp x p.1)
        (t' := Batteries.RBNode.node c a (x, k) b)
        (p' := path) hzoom)
  have hlocal :
      (x ::
        psumCountEntriesExpand (eraseOneNativeBranchList x k a b)).Perm
        (psumCountEntriesExpand
          (Batteries.RBNode.node c a (x, k) b).toList) :=
    eraseOneNativeBranchList_expand_perm_node hk c a b
  have hwrapped :
      (x :: psumCountEntriesExpand
        (path.withList (eraseOneNativeBranchList x k a b))).Perm
        (psumCountEntriesExpand
          (path.withList
            (Batteries.RBNode.node c a (x, k) b).toList)) := by
    unfold Batteries.RBNode.Path.withList
    simp only [psumCountEntriesExpand_append, List.append_assoc]
    simpa [List.append_assoc] using
      (list_cons_append_perm_append_of_cons_perm x
        (psumCountEntriesExpand path.listL)
        (psumCountEntriesExpand (eraseOneNativeBranchList x k a b))
        (psumCountEntriesExpand path.listR)
        (psumCountEntriesExpand
          (Batteries.RBNode.node c a (x, k) b).toList)
        hlocal)
  rw [activeList, hlist]
  change
    (x :: psumCountEntriesExpand
      (path.withList (eraseOneNativeBranchList x k a b))).Perm
      (psumCountEntriesExpand t.toList)
  rw [← horig]
  exact hwrapped

/-- The native counted-map decrement/delete drops the expanded active-list
length by exactly one. -/
theorem eraseOneNative_activeList_length {t : PsumCountRBMap}
    {x : ℝ} (hmem : x ∈ activeList t) :
    (activeList (eraseOneNative t x)).length + 1 =
      (activeList t).length := by
  have hperm := eraseOneNative_activeList_perm (t := t) (x := x) hmem
  have hlen := hperm.length_eq
  simpa [Nat.succ_eq_add_one] using hlen

/-- The native counted-map decrement/delete preserves positive stored
multiplicities. -/
theorem eraseOneNative_preserves_positive {t : PsumCountRBMap}
    (hpos : PositiveCounts t) {x : ℝ}
    (hmem : x ∈ activeList t) :
    PositiveCounts (eraseOneNative t x) := by
  rcases eraseOneNative_toList_of_mem_activeList hmem with
    ⟨k, c, a, b, path, hk, _hfind, hzoom, hlist⟩
  have horig :
      path.withList
        (Batteries.RBNode.node c a (x, k) b).toList =
        t.toList := by
    exact
      (Batteries.RBNode.zoom_toList (t := t.1)
        (cut := fun p : ℝ × ℕ => psumRealCmp x p.1)
        (t' := Batteries.RBNode.node c a (x, k) b)
        (p' := path) hzoom)
  have hposOrig :
      ∀ {y : ℝ} {m : ℕ},
        (y, m) ∈ path.withList
          (Batteries.RBNode.node c a (x, k) b).toList →
        0 < m := by
    intro y m hy
    exact hpos (by
      rw [← horig]
      exact hy)
  intro y m hnext
  have hbranch :
      (y, m) ∈ path.withList (eraseOneNativeBranchList x k a b) := by
    simpa [hlist] using hnext
  cases k with
  | zero => omega
  | succ k0 =>
      cases k0 with
      | zero =>
          have hsplit :
              (y, m) ∈ path.listL ∨
                (y, m) ∈ a.toList ∨
                (y, m) ∈ b.toList ∨
                (y, m) ∈ path.listR := by
            simpa [Batteries.RBNode.Path.withList,
              eraseOneNativeBranchList] using hbranch
          rcases hsplit with hL | hA | hB | hR
          · exact hposOrig (y := y) (m := m) (by
              unfold Batteries.RBNode.Path.withList
              simp [hL])
          · exact hposOrig (y := y) (m := m) (by
              unfold Batteries.RBNode.Path.withList
              simp [hA])
          · exact hposOrig (y := y) (m := m) (by
              unfold Batteries.RBNode.Path.withList
              simp [hB])
          · exact hposOrig (y := y) (m := m) (by
              unfold Batteries.RBNode.Path.withList
              simp [hR])
      | succ k1 =>
          have hsplit :
              (y, m) ∈ path.listL ∨
                (y, m) ∈ a.toList ∨
                (y, m) = (x, k1 + 1) ∨
                (y, m) ∈ b.toList ∨
                (y, m) ∈ path.listR := by
            simpa [Batteries.RBNode.Path.withList,
              eraseOneNativeBranchList] using hbranch
          rcases hsplit with hL | hA | hDec | hB | hR
          · exact hposOrig (y := y) (m := m) (by
              unfold Batteries.RBNode.Path.withList
              simp [hL])
          · exact hposOrig (y := y) (m := m) (by
              unfold Batteries.RBNode.Path.withList
              simp [hA])
          · cases hDec
            omega
          · exact hposOrig (y := y) (m := m) (by
              unfold Batteries.RBNode.Path.withList
              simp [hB])
          · exact hposOrig (y := y) (m := m) (by
              unfold Batteries.RBNode.Path.withList
              simp [hR])

/-- If counted-map lower-bound search fails, no expanded active value lies at
or below the target. -/
theorem lowerBound?_eq_none_no_le {target : ℝ} {t : PsumCountRBMap}
    (h : lowerBound? t target = none) :
    ∀ y ∈ activeList t, ¬ y ≤ target := by
  intro y hy hyle
  rcases exists_entry_of_mem_activeList hy with ⟨ky, hyEntry, _hypos⟩
  have hyTree :
      Batteries.RBSet.Mem (cmp := Ordering.byKey Prod.fst psumRealCmp)
        (y, ky)
        (t : Batteries.RBSet (ℝ × ℕ)
          (Ordering.byKey Prod.fst psumRealCmp)) :=
    Batteries.RBSet.mem_of_mem_toList
      (t := (t : Batteries.RBSet (ℝ × ℕ)
        (Ordering.byKey Prod.fst psumRealCmp))) hyEntry
  have hcmp : psumRealCmp target y ≠ .lt :=
    psumRealCmp_ne_lt_iff_ge.2 hyle
  have hexists : ∃ z, Batteries.RBSet.lowerBoundP? t
      (fun p : ℝ × ℕ => psumRealCmp target p.1) = some z :=
    (Batteries.RBSet.lowerBoundP?_exists
      (t := t)
      (cut := fun p : ℝ × ℕ => psumRealCmp target p.1)).2
      ⟨(y, ky), hyTree, by simpa using hcmp⟩
  rcases hexists with ⟨z, hz⟩
  have hnone :
      Batteries.RBSet.lowerBoundP? t
        (fun p : ℝ × ℕ => psumRealCmp target p.1) = none := by
    simpa [lowerBound?] using h
  rw [hnone] at hz
  contradiction

/-- If counted-map upper-bound search fails, no expanded active value lies at
or above the target. -/
theorem upperBound?_eq_none_no_ge {target : ℝ} {t : PsumCountRBMap}
    (h : upperBound? t target = none) :
    ∀ y ∈ activeList t, ¬ target ≤ y := by
  intro y hy hty
  rcases exists_entry_of_mem_activeList hy with ⟨ky, hyEntry, _hypos⟩
  have hyTree :
      Batteries.RBSet.Mem (cmp := Ordering.byKey Prod.fst psumRealCmp)
        (y, ky)
        (t : Batteries.RBSet (ℝ × ℕ)
          (Ordering.byKey Prod.fst psumRealCmp)) :=
    Batteries.RBSet.mem_of_mem_toList
      (t := (t : Batteries.RBSet (ℝ × ℕ)
        (Ordering.byKey Prod.fst psumRealCmp))) hyEntry
  have hcmp : psumRealCmp target y ≠ .gt :=
    psumRealCmp_ne_gt_iff_le.2 hty
  have hexists : ∃ z, Batteries.RBSet.upperBoundP? t
      (fun p : ℝ × ℕ => psumRealCmp target p.1) = some z :=
    (Batteries.RBSet.upperBoundP?_exists
      (t := t)
      (cut := fun p : ℝ × ℕ => psumRealCmp target p.1)).2
      ⟨(y, ky), hyTree, by simpa using hcmp⟩
  rcases hexists with ⟨z, hz⟩
  have hnone :
      Batteries.RBSet.upperBoundP? t
        (fun p : ℝ × ℕ => psumRealCmp target p.1) = none := by
    simpa [upperBound?] using h
  rw [hnone] at hz
  contradiction

/-- The counted red-black selector returns a member minimizing Higham's Psum
objective over the expanded active-list view, including duplicate values. -/
theorem neighborSelect_mem_and_min {acc selected : ℝ} {t : PsumCountRBMap}
    (hpos : PositiveCounts t)
    (hselect : neighborSelect acc t = some selected) :
    selected ∈ activeList t ∧
      ∀ y ∈ activeList t, |acc + selected| ≤ |acc + y| := by
  unfold neighborSelect at hselect
  cases hlower : lowerBound? t (-acc) with
  | none =>
      cases hupper : upperBound? t (-acc) with
      | none =>
          simp [hlower, hupper] at hselect
      | some upperEntry =>
          rcases upperEntry with ⟨upper, upperCount⟩
          simp [hlower, hupper] at hselect
          subst selected
          have hupperCert :
              PsumUpperNeighbor (-acc) (activeList t) upper :=
            upperBound_neighbor hpos hupper
          have hall : ∀ y ∈ activeList t, -acc ≤ y := by
            intro y hy
            exact le_of_lt
              (lt_of_not_ge (lowerBound?_eq_none_no_le hlower y hy))
          exact ⟨hupperCert.1,
            hupperCert.abs_add_le_all_of_neg_acc_le_all hall⟩
  | some lowerEntry =>
      rcases lowerEntry with ⟨lower, lowerCount⟩
      cases hupper : upperBound? t (-acc) with
      | none =>
          simp [hlower, hupper] at hselect
          subst selected
          have hlowerCert :
              PsumLowerNeighbor (-acc) (activeList t) lower :=
            lowerBound_neighbor hpos hlower
          have hall : ∀ y ∈ activeList t, y ≤ -acc := by
            intro y hy
            exact le_of_lt
              (lt_of_not_ge (upperBound?_eq_none_no_ge hupper y hy))
          exact ⟨hlowerCert.1,
            hlowerCert.abs_add_le_all_of_all_le_neg_acc hall⟩
      | some upperEntry =>
          rcases upperEntry with ⟨upper, upperCount⟩
          simp [hlower, hupper] at hselect
          subst selected
          have hlowerCert :
              PsumLowerNeighbor (-acc) (activeList t) lower :=
            lowerBound_neighbor hpos hlower
          have hupperCert :
              PsumUpperNeighbor (-acc) (activeList t) upper :=
            upperBound_neighbor hpos hupper
          exact psumNeighborChoice_mem_and_min
            (hlower := hlowerCert) (hupper := hupperCert)
            (chosen := psumClosestNeighbor acc lower upper)
            (hchosen := by
              unfold psumClosestNeighbor
              by_cases h : |acc + lower| ≤ |acc + upper|
              · simp [h]
              · simp [h])
            (hchoose_lower := by
              unfold psumClosestNeighbor
              by_cases h : |acc + lower| ≤ |acc + upper|
              · simp [h]
              · have hle : |acc + upper| ≤ |acc + lower| :=
                  le_of_lt (lt_of_not_ge h)
                simpa [h] using hle)
            (hchoose_upper := by
              unfold psumClosestNeighbor
              by_cases h : |acc + lower| ≤ |acc + upper|
              · simp [h]
              · simp [h])

/-- Counted map deletion bridge: decrementing one selected value in the
expanded counted-entry view is a one-element deletion permutation of the
map's active-list view. -/
theorem eraseOne_entries_perm {t : PsumCountRBMap} {x : ℝ}
    (hmem : x ∈ activeList t) :
    (x :: psumCountEntriesExpand
      (psumCountEntriesEraseOne x t.toList)).Perm (activeList t) :=
  psumCountEntriesEraseOne_perm (x := x) hmem

/-- Counted map deletion bridge: decrementing one selected value drops the
expanded active-list length by exactly one. -/
theorem eraseOne_entries_length {t : PsumCountRBMap} {x : ℝ}
    (hmem : x ∈ activeList t) :
    (psumCountEntriesExpand
      (psumCountEntriesEraseOne x t.toList)).length + 1 =
      (activeList t).length :=
  psumCountEntriesEraseOne_length (x := x) hmem

/-- A single executable counted-map Psum step, expressed at the level of the
map's ordered counted-entry view.  The next entry list is the current
`toList` view with one selected occurrence decremented. -/
noncomputable def stepEntries (acc : ℝ) (t : PsumCountRBMap) :
    Option (ℝ × List (ℝ × ℕ)) :=
  match neighborSelect acc t with
  | none => none
  | some selected =>
      some (selected, psumCountEntriesEraseOne selected t.toList)

/-- A single executable counted-map Psum step using the native `RBMap` update. -/
noncomputable def stepNative (acc : ℝ) (t : PsumCountRBMap) :
    Option (ℝ × PsumCountRBMap) :=
  match neighborSelect acc t with
  | none => none
  | some selected => some (selected, eraseOneNative t selected)

/-- Positive counted maps have no more distinct stored entries than expanded
active occurrences. -/
theorem toList_length_le_activeList_length_of_positive
    {t : PsumCountRBMap}
    (hpos : PositiveCounts t) :
    t.toList.length ≤ (activeList t).length := by
  exact psumCountEntriesExpand_length_ge_entries_length_of_positive
    (entries := t.toList) hpos

/-- Red-black balance gives a logarithmic depth bound for the counted map in
terms of its number of distinct keys. -/
theorem depth_le_logBudget (t : PsumCountRBMap) :
    t.1.depth ≤ 2 * Nat.log2 (t.size + 1) := by
  simpa using
    (Batteries.RBNode.WF.depth_bound
      (cmp := Ordering.byKey Prod.fst psumRealCmp) (t := t.1) t.2)

/-- For positive counted maps, the tree depth plus one comparison is bounded by
the existing per-step Psum logarithmic budget for the expanded active list. -/
theorem depth_succ_le_stepBudget (t : PsumCountRBMap)
    (hpos : PositiveCounts t) :
    t.1.depth + 1 ≤ psumLogSearchStepBudget (activeList t).length := by
  have hdepth := depth_le_logBudget t
  have hdistinct :
      t.size ≤ (activeList t).length := by
    rw [Batteries.RBMap.size_eq]
    exact toList_length_le_activeList_length_of_positive hpos
  have hstepDistinct :
      t.1.depth + 1 ≤ psumLogSearchStepBudget t.size := by
    unfold psumLogSearchStepBudget
    omega
  exact le_trans hstepDistinct (psumLogSearchStepBudget_mono hdistinct)

/-- A successful counted-map Psum step packages exactly the facts needed by a
future recursive counted-map loop: the selected key is an expanded active
member, it globally minimizes `|acc + x|`, decrementing one occurrence realizes
a one-element deletion in the expanded view, the expanded length drops by one,
and the concrete tree-depth charge fits the logarithmic step budget. -/
theorem stepEntries_certifies {acc selected : ℝ}
    {nextEntries : List (ℝ × ℕ)} {t : PsumCountRBMap}
    (hpos : PositiveCounts t)
    (hstep : stepEntries acc t = some (selected, nextEntries)) :
    selected ∈ activeList t ∧
      (∀ y ∈ activeList t, |acc + selected| ≤ |acc + y|) ∧
      (selected :: psumCountEntriesExpand nextEntries).Perm
        (activeList t) ∧
      (psumCountEntriesExpand nextEntries).length + 1 =
        (activeList t).length ∧
      t.1.depth + 1 ≤ psumLogSearchStepBudget (activeList t).length := by
  unfold stepEntries at hstep
  cases hselect : neighborSelect acc t with
  | none =>
      simp [hselect] at hstep
  | some selected' =>
      simp [hselect] at hstep
      rcases hstep with ⟨rfl, rfl⟩
      have hmin := neighborSelect_mem_and_min hpos hselect
      exact ⟨hmin.1, hmin.2, eraseOne_entries_perm hmin.1,
        eraseOne_entries_length hmin.1, depth_succ_le_stepBudget t hpos⟩

/-- The counted-map selector fails exactly when the expanded active-list view
is empty. -/
theorem neighborSelect_eq_none_iff_activeList_eq_nil {acc : ℝ}
    {t : PsumCountRBMap}
    (hpos : PositiveCounts t) :
    neighborSelect acc t = none ↔ activeList t = [] := by
  constructor
  · intro hselect
    unfold neighborSelect at hselect
    cases hlower : lowerBound? t (-acc) with
    | some lowerEntry =>
        rcases lowerEntry with ⟨lower, lowerCount⟩
        cases hupper : upperBound? t (-acc) with
        | some upperEntry =>
            rcases upperEntry with ⟨upper, upperCount⟩
            simp [hlower, hupper] at hselect
        | none =>
            simp [hlower, hupper] at hselect
    | none =>
        cases hupper : upperBound? t (-acc) with
        | some upperEntry =>
            rcases upperEntry with ⟨upper, upperCount⟩
            simp [hlower, hupper] at hselect
        | none =>
            cases hxs : activeList t with
            | nil =>
                rfl
            | cons y ys =>
                have hy : y ∈ activeList t := by
                  rw [hxs]
                  simp
                rcases le_total y (-acc) with hyle | hyge
                · exact False.elim
                    ((lowerBound?_eq_none_no_le hlower y hy) hyle)
                · exact False.elim
                    ((upperBound?_eq_none_no_ge hupper y hy) hyge)
  · intro hempty
    unfold neighborSelect
    cases hlower : lowerBound? t (-acc) with
    | some lowerEntry =>
        rcases lowerEntry with ⟨lower, lowerCount⟩
        have hmem : lower ∈ activeList t :=
          (lowerBound_neighbor hpos hlower).1
        simp [hempty] at hmem
    | none =>
        cases hupper : upperBound? t (-acc) with
        | some upperEntry =>
            rcases upperEntry with ⟨upper, upperCount⟩
            have hmem : upper ∈ activeList t :=
              (upperBound_neighbor hpos hupper).1
            simp [hempty] at hmem
        | none =>
            rfl

/-- The executable counted-entry step fails exactly when the expanded
active-list view is empty. -/
theorem stepEntries_eq_none_iff_activeList_eq_nil {acc : ℝ}
    {t : PsumCountRBMap}
    (hpos : PositiveCounts t) :
    stepEntries acc t = none ↔ activeList t = [] := by
  constructor
  · intro hstep
    unfold stepEntries at hstep
    cases hselect : neighborSelect acc t with
    | none =>
        exact (neighborSelect_eq_none_iff_activeList_eq_nil hpos).1 hselect
    | some selected =>
        simp [hselect] at hstep
  · intro hempty
    have hselect :
        neighborSelect acc t = none :=
      (neighborSelect_eq_none_iff_activeList_eq_nil hpos).2 hempty
    simp [stepEntries, hselect]

/-- The native counted-map step fails exactly when the expanded active-list view
is empty. -/
theorem stepNative_eq_none_iff_activeList_eq_nil {acc : ℝ}
    {t : PsumCountRBMap}
    (hpos : PositiveCounts t) :
    stepNative acc t = none ↔ activeList t = [] := by
  unfold stepNative
  cases hselect : neighborSelect acc t with
  | none =>
      simp
      exact (neighborSelect_eq_none_iff_activeList_eq_nil hpos).1 hselect
  | some selected =>
      simp
      intro hempty
      have hnone :
          neighborSelect acc t = none :=
        (neighborSelect_eq_none_iff_activeList_eq_nil hpos).2 hempty
      rw [hselect] at hnone
      contradiction

/-- A successful counted-entry step strictly decreases the expanded active-list
length.  This is the measure fact needed by a future recursive counted-map
loop. -/
theorem stepEntries_decreases_activeList_length {acc selected : ℝ}
    {nextEntries : List (ℝ × ℕ)} {t : PsumCountRBMap}
    (hpos : PositiveCounts t)
    (hstep : stepEntries acc t = some (selected, nextEntries)) :
    (psumCountEntriesExpand nextEntries).length < (activeList t).length := by
  have hcert := stepEntries_certifies hpos hstep
  omega

/-- A successful counted-map step preserves the positive-count invariant for
the emitted next-entry list. -/
theorem stepEntries_preserves_positive_entries {acc selected : ℝ}
    {nextEntries : List (ℝ × ℕ)} {t : PsumCountRBMap}
    (hpos : PositiveCounts t)
    (hstep : stepEntries acc t = some (selected, nextEntries)) :
    ∀ {x : ℝ} {k : ℕ}, (x, k) ∈ nextEntries → 0 < k := by
  unfold stepEntries at hstep
  cases hselect : neighborSelect acc t with
  | none =>
      simp [hselect] at hstep
  | some selected' =>
      simp [hselect] at hstep
      rcases hstep with ⟨rfl, rfl⟩
      exact
        psumCountEntriesEraseOne_preserves_positive
          (x := selected') (entries := t.toList) hpos

/-- A successful native counted-map step strictly decreases the expanded
active-list length. -/
theorem stepNative_decreases_activeList_length {acc selected : ℝ}
    {nextMap : PsumCountRBMap} {t : PsumCountRBMap}
    (hpos : PositiveCounts t)
    (hstep : stepNative acc t = some (selected, nextMap)) :
    (activeList nextMap).length < (activeList t).length := by
  unfold stepNative at hstep
  cases hselect : neighborSelect acc t with
  | none =>
      simp [hselect] at hstep
  | some selected' =>
      simp [hselect] at hstep
      rcases hstep with ⟨rfl, rfl⟩
      have hmin := neighborSelect_mem_and_min hpos hselect
      have hlen := eraseOneNative_activeList_length (t := t)
        (x := selected') hmin.1
      omega

/-- A successful native counted-map step preserves the positive-count invariant
on the next concrete map. -/
theorem stepNative_preserves_positive {acc selected : ℝ}
    {nextMap : PsumCountRBMap} {t : PsumCountRBMap}
    (hpos : PositiveCounts t)
    (hstep : stepNative acc t = some (selected, nextMap)) :
    PositiveCounts nextMap := by
  unfold stepNative at hstep
  cases hselect : neighborSelect acc t with
  | none =>
      simp [hselect] at hstep
  | some selected' =>
      simp [hselect] at hstep
      rcases hstep with ⟨rfl, rfl⟩
      have hmin := neighborSelect_mem_and_min hpos hselect
      intro y k hy
      exact (eraseOneNative_preserves_positive hpos hmin.1) hy

/-- Counted-entry view of one certified Psum step.  This is the composable
contract exported by a counted red-black-map step: one selected expanded
occurrence is removed, the selected value minimizes the Psum objective, and the
charged selector/update cost fits the per-step logarithmic budget. -/
structure EntryStep (acc : ℝ) (entries : List (ℝ × ℕ))
    (selected : ℝ) (nextEntries : List (ℝ × ℕ)) (stepCost : ℕ) :
    Prop where
  selected_mem :
    selected ∈ psumCountEntriesExpand entries
  selected_min :
    ∀ y ∈ psumCountEntriesExpand entries,
      |acc + selected| ≤ |acc + y|
  perm :
    (selected :: psumCountEntriesExpand nextEntries).Perm
      (psumCountEntriesExpand entries)
  length_drop :
    (psumCountEntriesExpand nextEntries).length + 1 =
      (psumCountEntriesExpand entries).length
  cost_le :
    stepCost ≤
      psumLogSearchStepBudget (psumCountEntriesExpand entries).length

/-- A successful concrete counted-map step realizes the composable
counted-entry step contract. -/
theorem entryStep_of_stepEntries {acc selected : ℝ}
    {nextEntries : List (ℝ × ℕ)} {t : PsumCountRBMap}
    (hpos : PositiveCounts t)
    (hstep : stepEntries acc t = some (selected, nextEntries)) :
    EntryStep acc t.toList selected nextEntries (t.1.depth + 1) := by
  have hcert := stepEntries_certifies hpos hstep
  exact
    { selected_mem := hcert.1
      selected_min := hcert.2.1
      perm := hcert.2.2.1
      length_drop := hcert.2.2.2.1
      cost_le := hcert.2.2.2.2 }

/-- A successful native counted-map step realizes the composable counted-entry
step contract using the next concrete map's `toList` view. -/
theorem entryStep_of_stepNative {acc selected : ℝ}
    {nextMap : PsumCountRBMap} {t : PsumCountRBMap}
    (hpos : PositiveCounts t)
    (hstep : stepNative acc t = some (selected, nextMap)) :
    EntryStep acc t.toList selected nextMap.toList (t.1.depth + 1) := by
  unfold stepNative at hstep
  cases hselect : neighborSelect acc t with
  | none =>
      simp [hselect] at hstep
  | some selected' =>
      simp [hselect] at hstep
      rcases hstep with ⟨rfl, rfl⟩
      have hmin := neighborSelect_mem_and_min hpos hselect
      exact
        { selected_mem := hmin.1
          selected_min := hmin.2
          perm := eraseOneNative_activeList_perm hmin.1
          length_drop := eraseOneNative_activeList_length hmin.1
          cost_le := depth_succ_le_stepBudget t hpos }

/-- Recursive counted-entry Psum trace obtained by composing certified
counted-map steps.  This is a trace over counted-entry views; a separate
native map-update theorem is still needed to instantiate every recursive step
with an updated `RBMap`. -/
inductive EntryLogSearchTraceFrom :
    ℝ → List (ℝ × ℕ) → List ℝ → ℕ → Prop
  | nil {acc : ℝ} {entries : List (ℝ × ℕ)}
      (hempty : psumCountEntriesExpand entries = []) :
      EntryLogSearchTraceFrom acc entries [] 0
  | cons {acc selected : ℝ} {entries nextEntries : List (ℝ × ℕ)}
      {out : List ℝ} {stepCost restCost : ℕ} :
      EntryStep acc entries selected nextEntries stepCost →
      EntryLogSearchTraceFrom (acc + selected) nextEntries out restCost →
      EntryLogSearchTraceFrom acc entries (selected :: out)
        (stepCost + restCost)

namespace EntryLogSearchTraceFrom

/-- A counted-entry log-search trace realizes the extensional Psum-minimizer
trace over the expanded active list. -/
theorem minTrace {acc : ℝ} {entries : List (ℝ × ℕ)}
    {out : List ℝ} {cost : ℕ}
    (htrace : EntryLogSearchTraceFrom acc entries out cost) :
    PsumMinOrderFrom acc (psumCountEntriesExpand entries) out := by
  induction htrace with
  | nil hempty =>
      rw [hempty]
      exact PsumMinOrderFrom.nil _
  | cons hstep _hrec ih =>
      exact PsumMinOrderFrom.cons hstep.selected_mem hstep.selected_min
        hstep.perm ih

/-- A counted-entry log-search trace preserves the expanded active multiset. -/
theorem perm {acc : ℝ} {entries : List (ℝ × ℕ)}
    {out : List ℝ} {cost : ℕ}
    (htrace : EntryLogSearchTraceFrom acc entries out cost) :
    out.Perm (psumCountEntriesExpand entries) :=
  (minTrace htrace).perm

/-- The same recursive logarithmic budget bounds any counted-entry trace whose
individual certified steps satisfy the per-step logarithmic budget. -/
theorem cost_le_budget {acc : ℝ} {entries : List (ℝ × ℕ)}
    {out : List ℝ} {cost : ℕ}
    (htrace : EntryLogSearchTraceFrom acc entries out cost) :
    cost ≤
      psumLogSearchComparisonBudget (psumCountEntriesExpand entries).length := by
  induction htrace with
  | nil hempty =>
      simp [hempty, psumLogSearchComparisonBudget]
  | cons hstep _hrec ih =>
      rename_i acc selected entries nextEntries out stepCost restCost
      have hlen : (psumCountEntriesExpand nextEntries).length + 1 =
          (psumCountEntriesExpand entries).length :=
        hstep.length_drop
      calc
        stepCost + restCost ≤
            psumLogSearchStepBudget
                (psumCountEntriesExpand entries).length +
              psumLogSearchComparisonBudget
                (psumCountEntriesExpand nextEntries).length := by
          exact Nat.add_le_add hstep.cost_le ih
        _ =
            psumLogSearchStepBudget
                ((psumCountEntriesExpand nextEntries).length + 1) +
              psumLogSearchComparisonBudget
                (psumCountEntriesExpand nextEntries).length := by
          rw [hlen]
        _ =
            psumLogSearchComparisonBudget
                ((psumCountEntriesExpand nextEntries).length + 1) := by
          simp [psumLogSearchComparisonBudget]
        _ =
            psumLogSearchComparisonBudget
                (psumCountEntriesExpand entries).length := by
          rw [hlen]

end EntryLogSearchTraceFrom

/-- Fuelled executable Psum order generated by the native counted red-black map
selector and native decrement/delete update. -/
noncomputable def nativeOrderFromFuel :
    ℕ → ℝ → PsumCountRBMap → List ℝ
  | 0, _acc, _t => []
  | fuel + 1, acc, t =>
      match stepNative acc t with
      | none => []
      | some (selected, nextMap) =>
          selected :: nativeOrderFromFuel fuel (acc + selected) nextMap

/-- Comparison-cost counter for `nativeOrderFromFuel`, charging the current
tree depth plus one comparison at every successful native step. -/
noncomputable def nativeOrderCostFromFuel :
    ℕ → ℝ → PsumCountRBMap → ℕ
  | 0, _acc, _t => 0
  | fuel + 1, acc, t =>
      match stepNative acc t with
      | none => 0
      | some (selected, nextMap) =>
          t.1.depth + 1 +
            nativeOrderCostFromFuel fuel (acc + selected) nextMap

/-- The fuelled native counted-map Psum loop instantiates the counted-entry
log-search trace whenever the fuel covers the current expanded active length. -/
theorem nativeOrderFromFuel_entryLogSearchTrace :
    ∀ {fuel : ℕ} {acc : ℝ} {t : PsumCountRBMap},
      PositiveCounts t →
      (activeList t).length ≤ fuel →
      EntryLogSearchTraceFrom acc t.toList
        (nativeOrderFromFuel fuel acc t)
        (nativeOrderCostFromFuel fuel acc t)
  | 0, acc, t, _hpos, hlen => by
      have hempty : activeList t = [] := by
        have hlen0 : (activeList t).length = 0 :=
          Nat.eq_zero_of_le_zero hlen
        cases hxs : activeList t with
        | nil => rfl
        | cons y ys =>
            simp [hxs] at hlen0
      exact EntryLogSearchTraceFrom.nil (by
        simpa [activeList] using hempty)
  | fuel + 1, acc, t, hpos, hlen => by
      cases hstep : stepNative acc t with
      | none =>
          have hempty : activeList t = [] :=
            (stepNative_eq_none_iff_activeList_eq_nil hpos).1 hstep
          have hnil : EntryLogSearchTraceFrom acc t.toList [] 0 :=
            EntryLogSearchTraceFrom.nil (by
              simpa [activeList] using hempty)
          simpa [nativeOrderFromFuel, nativeOrderCostFromFuel, hstep] using
            hnil
      | some pair =>
          rcases pair with ⟨selected, nextMap⟩
          have hentry :
              EntryStep acc t.toList selected nextMap.toList
                (t.1.depth + 1) :=
            entryStep_of_stepNative hpos hstep
          have hposNext : PositiveCounts nextMap :=
            stepNative_preserves_positive hpos hstep
          have hdec :
              (activeList nextMap).length < (activeList t).length :=
            stepNative_decreases_activeList_length hpos hstep
          have hlenNext :
              (activeList nextMap).length ≤ fuel := by
            omega
          have hrec :
              EntryLogSearchTraceFrom (acc + selected) nextMap.toList
                (nativeOrderFromFuel fuel (acc + selected) nextMap)
                (nativeOrderCostFromFuel fuel (acc + selected) nextMap) :=
            nativeOrderFromFuel_entryLogSearchTrace hposNext hlenNext
          simpa [nativeOrderFromFuel, nativeOrderCostFromFuel, hstep] using
            EntryLogSearchTraceFrom.cons hentry hrec

/-- Native counted-map Psum order using exactly the current expanded active
length as fuel. -/
noncomputable def nativeOrderFrom (acc : ℝ) (t : PsumCountRBMap) : List ℝ :=
  nativeOrderFromFuel (activeList t).length acc t

/-- Native counted-map Psum comparison-cost counter with exact active-length
fuel. -/
noncomputable def nativeOrderCostFrom (acc : ℝ) (t : PsumCountRBMap) : ℕ :=
  nativeOrderCostFromFuel (activeList t).length acc t

/-- The executable native counted-map Psum loop has a counted-entry
log-search trace from its current `toList` view. -/
theorem nativeOrderFrom_entryLogSearchTrace {acc : ℝ} {t : PsumCountRBMap}
    (hpos : PositiveCounts t) :
    EntryLogSearchTraceFrom acc t.toList
      (nativeOrderFrom acc t) (nativeOrderCostFrom acc t) := by
  exact nativeOrderFromFuel_entryLogSearchTrace hpos le_rfl

/-- The native counted-map Psum order is an extensional Psum-minimizer trace over
the expanded active-list view. -/
theorem nativeOrderFrom_minTrace {acc : ℝ} {t : PsumCountRBMap}
    (hpos : PositiveCounts t) :
    PsumMinOrderFrom acc (activeList t) (nativeOrderFrom acc t) := by
  simpa [activeList] using
    (EntryLogSearchTraceFrom.minTrace
      (nativeOrderFrom_entryLogSearchTrace (acc := acc) (t := t) hpos))

/-- The native counted-map Psum order preserves the expanded active multiset. -/
theorem nativeOrderFrom_perm {acc : ℝ} {t : PsumCountRBMap}
    (hpos : PositiveCounts t) :
    (nativeOrderFrom acc t).Perm (activeList t) := by
  simpa [activeList] using
    (EntryLogSearchTraceFrom.perm
      (nativeOrderFrom_entryLogSearchTrace (acc := acc) (t := t) hpos))

/-- The native counted-map Psum loop satisfies the recursive logarithmic
comparison budget for the expanded active-list length. -/
theorem nativeOrderCostFrom_le_budget {acc : ℝ} {t : PsumCountRBMap}
    (hpos : PositiveCounts t) :
    nativeOrderCostFrom acc t ≤
      psumLogSearchComparisonBudget (activeList t).length := by
  simpa [activeList] using
    (EntryLogSearchTraceFrom.cost_le_budget
      (nativeOrderFrom_entryLogSearchTrace (acc := acc) (t := t) hpos))

end PsumCountRBMap

/-- With a logarithmic-cost selector at every step, the generated Psum order
admits the exact recursive logarithmic-search cost trace.  This theorem reuses
the same mathematical minimizer as the source-side `psumOrderFromFuel`; it
does not claim that the scan implementation above has this cost. -/
theorem psumOrderFromFuel_logSearchTrace :
    ∀ (fuel : ℕ) (acc : ℝ) (xs : List ℝ),
      xs.length ≤ fuel →
      PsumLogSearchTraceFrom acc xs (psumOrderFromFuel fuel acc xs)
        (psumLogSearchComparisonBudget xs.length)
  | 0, acc, xs, hfuel => by
      have hxs : xs = [] := by
        cases xs with
        | nil => rfl
        | cons _ rest => simp at hfuel
      subst xs
      simp [psumOrderFromFuel, psumLogSearchComparisonBudget]
      exact PsumLogSearchTraceFrom.nil acc
  | fuel + 1, acc, xs, hfuel => by
      cases hsel : psumSelect acc xs with
      | none =>
          have hxs : xs = [] := (psumSelect_eq_none_iff acc xs).1 hsel
          subst xs
          simp [psumOrderFromFuel, psumSelect, psumLogSearchComparisonBudget]
          exact PsumLogSearchTraceFrom.nil acc
      | some selected =>
          rcases selected with ⟨x, rest⟩
          have hselect_perm : (x :: rest).Perm xs :=
            psumSelect_perm hsel
          have hlen_eq : rest.length + 1 = xs.length := by
            simpa using hselect_perm.length_eq
          have hlen : rest.length ≤ fuel := by
            have hs : rest.length + 1 ≤ fuel + 1 := by
              rw [hlen_eq]
              exact hfuel
            exact Nat.succ_le_succ_iff.mp hs
          have hrec :
              PsumLogSearchTraceFrom (acc + x) rest
                (psumOrderFromFuel fuel (acc + x) rest)
                (psumLogSearchComparisonBudget rest.length) :=
            psumOrderFromFuel_logSearchTrace fuel (acc + x) rest hlen
          have htrace :
              PsumLogSearchTraceFrom acc xs
                (x :: psumOrderFromFuel fuel (acc + x) rest)
                (psumLogSearchStepBudget xs.length +
                  psumLogSearchComparisonBudget rest.length) :=
            PsumLogSearchTraceFrom.cons hsel le_rfl hrec
          have hbudget :
              psumLogSearchStepBudget xs.length +
                  psumLogSearchComparisonBudget rest.length =
                psumLogSearchComparisonBudget xs.length := by
            rw [← hlen_eq]
            simp [psumLogSearchComparisonBudget]
          simpa [psumOrderFromFuel, hsel, hbudget] using htrace

/-- Exported Psum-from-accumulator log-search trace. -/
theorem psumOrderFrom_logSearchTrace (acc : ℝ) (xs : List ℝ) :
    PsumLogSearchTraceFrom acc xs (psumOrderFrom acc xs)
      (psumLogSearchComparisonBudget xs.length) := by
  exact psumOrderFromFuel_logSearchTrace xs.length acc xs le_rfl

/-- Exported zero-accumulator Psum log-search trace. -/
theorem psumOrder_logSearchTrace (xs : List ℝ) :
    PsumLogSearchTraceFrom 0 xs (psumOrder xs)
      (psumLogSearchComparisonBudget xs.length) := by
  exact psumOrderFrom_logSearchTrace 0 xs

/-- Compact `n * log n`-shaped comparison-cost corollary for the optimized
Psum trace. -/
theorem psumOrder_logSearchComparisonCost_le_mul_stepBudget (xs : List ℝ) :
    psumLogSearchComparisonBudget xs.length ≤
      xs.length * psumLogSearchStepBudget xs.length :=
  psumLogSearchComparisonBudget_le_mul_stepBudget xs.length

/-! ## Finite-vector bridges for concrete source orderings -/

/-- Increasing-absolute-value sorting exported as a length-indexed vector
for finite source inputs. -/
noncomputable def increasingAbsSortVector {n : ℕ} (v : Fin n → ℝ) :
    List.Vector ℝ n :=
  ⟨increasingAbsSort (List.ofFn v), by
    have hlen := (increasingAbsSort_perm (List.ofFn v)).length_eq
    simpa [List.length_ofFn] using hlen⟩

/-- The vector bridge exposes exactly the source-side increasing sort. -/
theorem increasingAbsSortVector_toList {n : ℕ} (v : Fin n → ℝ) :
    (increasingAbsSortVector v).toList = increasingAbsSort (List.ofFn v) := by
  rfl

/-- The finite-vector increasing sort is ordered by increasing magnitude. -/
theorem increasingAbsSortVector_sorted {n : ℕ} (v : Fin n → ℝ) :
    IncreasingAbsList (increasingAbsSortVector v).toList := by
  simpa [increasingAbsSortVector_toList] using
    increasingAbsSort_sorted (List.ofFn v)

/-- The finite-vector increasing sort preserves the input multiset. -/
theorem increasingAbsSortVector_perm {n : ℕ} (v : Fin n → ℝ) :
    (increasingAbsSortVector v).toList.Perm (List.ofFn v) := by
  simpa [increasingAbsSortVector_toList] using
    increasingAbsSort_perm (List.ofFn v)

/-- The finite-vector increasing sort preserves the exact source sum. -/
theorem increasingAbsSortVector_sum_eq {n : ℕ} (v : Fin n → ℝ) :
    (increasingAbsSortVector v).toList.sum = ∑ i : Fin n, v i := by
  rw [increasingAbsSortVector_toList, increasingAbsSort_sum_eq, List.sum_ofFn]

/-- Finite-vector form of the exact-arithmetic recursive-loop budget
minimization theorem for nonnegative inputs. -/
theorem increasingAbsSortVector_recursiveRoundedPrefixBudget_exactWithUnitRoundoff_le
    (u0 : ℝ) (hu0 : 0 ≤ u0) {n : ℕ} (v : Fin n → ℝ)
    (hnonneg : ∀ i : Fin n, 0 ≤ v i) :
    recursiveRoundedPrefixBudget
        (FPModel.exactWithUnitRoundoff u0 hu0)
        (increasingAbsSortVector v).toList ≤
      recursiveRoundedPrefixBudget
        (FPModel.exactWithUnitRoundoff u0 hu0)
        (List.ofFn v) := by
  rw [increasingAbsSortVector_toList]
  exact increasingAbsSort_recursiveRoundedPrefixBudget_exactWithUnitRoundoff_le
    u0 hu0 (List.ofFn v) (by
      intro y hy
      rcases (List.mem_ofFn.mp hy) with ⟨i, rfl⟩
      exact hnonneg i)

/-- Decreasing-absolute-value sorting exported as a length-indexed vector
for finite source inputs. -/
noncomputable def decreasingAbsSortVector {n : ℕ} (v : Fin n → ℝ) :
    List.Vector ℝ n :=
  ⟨decreasingAbsSort (List.ofFn v), by
    have hlen := (decreasingAbsSort_perm (List.ofFn v)).length_eq
    simpa [List.length_ofFn] using hlen⟩

/-- The vector bridge exposes exactly the source-side decreasing sort. -/
theorem decreasingAbsSortVector_toList {n : ℕ} (v : Fin n → ℝ) :
    (decreasingAbsSortVector v).toList = decreasingAbsSort (List.ofFn v) := by
  rfl

/-- The finite-vector decreasing sort is ordered by decreasing magnitude. -/
theorem decreasingAbsSortVector_sorted {n : ℕ} (v : Fin n → ℝ) :
    DecreasingAbsList (decreasingAbsSortVector v).toList := by
  simpa [decreasingAbsSortVector_toList] using
    decreasingAbsSort_sorted (List.ofFn v)

/-- The finite-vector decreasing sort preserves the input multiset. -/
theorem decreasingAbsSortVector_perm {n : ℕ} (v : Fin n → ℝ) :
    (decreasingAbsSortVector v).toList.Perm (List.ofFn v) := by
  simpa [decreasingAbsSortVector_toList] using
    decreasingAbsSort_perm (List.ofFn v)

/-- The finite-vector decreasing sort preserves the exact source sum. -/
theorem decreasingAbsSortVector_sum_eq {n : ℕ} (v : Fin n → ℝ) :
    (decreasingAbsSortVector v).toList.sum = ∑ i : Fin n, v i := by
  rw [decreasingAbsSortVector_toList, decreasingAbsSort_sum_eq, List.sum_ofFn]

/-- Psum exported as a length-indexed vector for finite source inputs. -/
noncomputable def psumOrderVector {n : ℕ} (v : Fin n → ℝ) :
    List.Vector ℝ n :=
  ⟨psumOrder (List.ofFn v), by
    have hlen := (psumOrder_perm (List.ofFn v)).length_eq
    simpa [List.length_ofFn] using hlen⟩

/-- The vector bridge exposes exactly the source-side Psum order. -/
theorem psumOrderVector_toList {n : ℕ} (v : Fin n → ℝ) :
    (psumOrderVector v).toList = psumOrder (List.ofFn v) := by
  rfl

/-- For nonnegative finite source inputs, the Psum vector bridge coincides
with the increasing-magnitude vector bridge. -/
theorem psumOrderVector_eq_increasingAbsSortVector_of_nonnegative
    {n : ℕ} (v : Fin n → ℝ)
    (hnonneg : ∀ i : Fin n, 0 ≤ v i) :
    (psumOrderVector v).toList = (increasingAbsSortVector v).toList := by
  rw [psumOrderVector_toList, increasingAbsSortVector_toList]
  exact psumOrder_eq_increasingAbsSort_of_nonnegative (List.ofFn v) (by
    intro y hy
    rcases (List.mem_ofFn.mp hy) with ⟨i, rfl⟩
    exact hnonneg i)

/-- The finite-vector Psum order preserves the input multiset. -/
theorem psumOrderVector_perm {n : ℕ} (v : Fin n → ℝ) :
    (psumOrderVector v).toList.Perm (List.ofFn v) := by
  simpa [psumOrderVector_toList] using psumOrder_perm (List.ofFn v)

/-- The finite-vector Psum order realizes the greedy partial-sum trace. -/
theorem psumOrderVector_greedyTrace {n : ℕ} (v : Fin n → ℝ) :
    PsumGreedyOrderFrom 0 (List.ofFn v) (psumOrderVector v).toList := by
  simpa [psumOrderVector_toList] using psumOrder_greedyTrace (List.ofFn v)

/-- For nonnegative finite source inputs, the Psum vector bridge is ordered by
increasing absolute value, matching the same-sign equivalence claim. -/
theorem psumOrderVector_sorted_of_nonnegative {n : ℕ} (v : Fin n → ℝ)
    (hnonneg : ∀ i : Fin n, 0 ≤ v i) :
    IncreasingAbsList (psumOrderVector v).toList := by
  rw [psumOrderVector_toList]
  exact psumOrder_increasingAbs_of_nonnegative (List.ofFn v) (by
    intro y hy
    rcases (List.mem_ofFn.mp hy) with ⟨i, rfl⟩
    exact hnonneg i)

/-- The finite-vector Psum order preserves the exact source sum. -/
theorem psumOrderVector_sum_eq {n : ℕ} (v : Fin n → ℝ) :
    (psumOrderVector v).toList.sum = ∑ i : Fin n, v i := by
  have hsum := list_sum_eq_of_perm (psumOrderVector_perm v)
  simpa [List.sum_ofFn] using hsum

/-- Finite-vector Psum inherits the exact-arithmetic recursive-loop budget
minimization theorem for nonnegative inputs. -/
theorem psumOrderVector_recursiveRoundedPrefixBudget_exactWithUnitRoundoff_le
    (u0 : ℝ) (hu0 : 0 ≤ u0) {n : ℕ} (v : Fin n → ℝ)
    (hnonneg : ∀ i : Fin n, 0 ≤ v i) :
    recursiveRoundedPrefixBudget
        (FPModel.exactWithUnitRoundoff u0 hu0)
        (psumOrderVector v).toList ≤
      recursiveRoundedPrefixBudget
        (FPModel.exactWithUnitRoundoff u0 hu0)
        (List.ofFn v) := by
  rw [psumOrderVector_eq_increasingAbsSortVector_of_nonnegative v hnonneg]
  exact increasingAbsSortVector_recursiveRoundedPrefixBudget_exactWithUnitRoundoff_le
    u0 hu0 v hnonneg

/-- Four-leaf left chain used for the printed p. 83 recursive-ordering examples. -/
def p91RecursiveFourTree : SumTree 4 :=
  SumTree.node
    (SumTree.node
      (SumTree.node SumTree.leaf SumTree.leaf)
      SumTree.leaf)
    SumTree.leaf

/-- Increasing-magnitude order for Higham's printed p. 83 example:
`[1, M, 2M, -3M]`. -/
noncomputable def p91IncreasingInput (M : ℝ) : Fin 4 → ℝ
  := ![1, M, 2 * M, -(3 * M)]

/-- Psum order for Higham's printed p. 83 example:
`[1, M, -3M, 2M]`. -/
noncomputable def p91PsumInput (M : ℝ) : Fin 4 → ℝ
  := ![1, M, -(3 * M), 2 * M]

/-- Decreasing-magnitude order for Higham's printed p. 83 example:
`[-3M, 2M, M, 1]`. -/
noncomputable def p91DecreasingInput (M : ℝ) : Fin 4 → ℝ
  := ![-(3 * M), 2 * M, M, 1]

/-- The rounded operations assumed by Higham's displayed printed p. 83 cancellation
example.  The first field is the source condition `fl(1 + M) = M`; the
remaining fields record the exact scaled additions used in the display. -/
structure P91CancellationRounding (fp : FPModel) (M : ℝ) : Prop where
  one_add_M : fp.fl_add 1 M = M
  M_add_twoM : fp.fl_add M (2 * M) = 3 * M
  M_add_negThreeM : fp.fl_add M (-(3 * M)) = -(2 * M)
  negThreeM_add_twoM : fp.fl_add (-(3 * M)) (2 * M) = -M

/-- If the exact addends cancel, the abstract relative-error model forces the
rounded addition result to be zero. -/
lemma fl_add_eq_zero_of_add_eq_zero (fp : FPModel) {x y : ℝ}
    (hxy : x + y = 0) :
    fp.fl_add x y = 0 := by
  obtain ⟨δ, _hδ, hfl⟩ := fp.model_add x y
  rw [hfl, hxy]
  ring

/-- Recursive floating-point sum in the printed p. 83 increasing order. -/
noncomputable def fl_p91Increasing (fp : FPModel) (M : ℝ) : ℝ :=
  fl_recursiveSum fp 4 (p91IncreasingInput M)

/-- Recursive floating-point sum in the printed p. 83 Psum order. -/
noncomputable def fl_p91Psum (fp : FPModel) (M : ℝ) : ℝ :=
  fl_recursiveSum fp 4 (p91PsumInput M)

/-- Recursive floating-point sum in the printed p. 83 decreasing order. -/
noncomputable def fl_p91Decreasing (fp : FPModel) (M : ℝ) : ℝ :=
  fl_recursiveSum fp 4 (p91DecreasingInput M)

/-- The increasing-order exact sum in example (4.5) is `1`. -/
theorem p91Increasing_exact_sum (M : ℝ) :
    (∑ i : Fin 4, p91IncreasingInput M i) = 1 := by
  norm_num [p91IncreasingInput, Fin.sum_univ_succ]
  ring

/-- The Psum-order exact sum in example (4.5) is `1`. -/
theorem p91Psum_exact_sum (M : ℝ) :
    (∑ i : Fin 4, p91PsumInput M i) = 1 := by
  norm_num [p91PsumInput, Fin.sum_univ_succ]
  ring

/-- The decreasing-order exact sum in example (4.5) is `1`. -/
theorem p91Decreasing_exact_sum (M : ℝ) :
    (∑ i : Fin 4, p91DecreasingInput M i) = 1 := by
  norm_num [p91DecreasingInput, Fin.sum_univ_succ]
  ring

/-- The sum of magnitudes for the printed p. 83 increasing-order data is `1 + 6M`
when `M` is nonnegative. -/
theorem p91Increasing_sum_abs_eq {M : ℝ} (hM : 0 ≤ M) :
    (∑ i : Fin 4, |p91IncreasingInput M i|) = 1 + 6 * M := by
  have h2M : 0 ≤ 2 * M := by nlinarith
  have h3M : 0 ≤ 3 * M := by nlinarith
  have hneg3M : -(3 * M) ≤ 0 := by linarith
  norm_num [p91IncreasingInput, Fin.sum_univ_succ,
    abs_of_nonneg hM, abs_of_nonneg h2M, abs_of_nonpos hneg3M]
  ring

/-- The sum of magnitudes for the printed p. 83 Psum-order data is `1 + 6M`
when `M` is nonnegative. -/
theorem p91Psum_sum_abs_eq {M : ℝ} (hM : 0 ≤ M) :
    (∑ i : Fin 4, |p91PsumInput M i|) = 1 + 6 * M := by
  have h2M : 0 ≤ 2 * M := by nlinarith
  have h3M : 0 ≤ 3 * M := by nlinarith
  have hneg3M : -(3 * M) ≤ 0 := by linarith
  norm_num [p91PsumInput, Fin.sum_univ_succ,
    abs_of_nonneg hM, abs_of_nonneg h2M, abs_of_nonpos hneg3M]
  ring

/-- The sum of magnitudes for the printed p. 83 decreasing-order data is `1 + 6M`
when `M` is nonnegative. -/
theorem p91Decreasing_sum_abs_eq {M : ℝ} (hM : 0 ≤ M) :
    (∑ i : Fin 4, |p91DecreasingInput M i|) = 1 + 6 * M := by
  have h2M : 0 ≤ 2 * M := by nlinarith
  have h3M : 0 ≤ 3 * M := by nlinarith
  have hneg3M : -(3 * M) ≤ 0 := by linarith
  norm_num [p91DecreasingInput, Fin.sum_univ_succ,
    abs_of_nonneg hM, abs_of_nonneg h2M, abs_of_nonpos hneg3M]
  ring

/-- Higham's printed p. 83 increasing-order data have cancellation amplification
exactly matching the ratio `1 + 6M` in the nonnegative `M` regime. -/
theorem p91Increasing_heavyCancellationAtLeast {M : ℝ} (hM : 0 ≤ M) :
    HeavyCancellationAtLeast (p91IncreasingInput M) (1 + 6 * M) := by
  unfold HeavyCancellationAtLeast
  rw [p91Increasing_exact_sum, p91Increasing_sum_abs_eq hM]
  norm_num

/-- Higham's printed p. 83 Psum-order data have the same cancellation amplification
ratio as the source ordering. -/
theorem p91Psum_heavyCancellationAtLeast {M : ℝ} (hM : 0 ≤ M) :
    HeavyCancellationAtLeast (p91PsumInput M) (1 + 6 * M) := by
  unfold HeavyCancellationAtLeast
  rw [p91Psum_exact_sum, p91Psum_sum_abs_eq hM]
  norm_num

/-- Higham's printed p. 83 decreasing-order data preserve the same cancellation
amplification ratio while changing the rounded recursive-summation outcome. -/
theorem p91Decreasing_heavyCancellationAtLeast {M : ℝ} (hM : 0 ≤ M) :
    HeavyCancellationAtLeast (p91DecreasingInput M) (1 + 6 * M) := by
  unfold HeavyCancellationAtLeast
  rw [p91Decreasing_exact_sum, p91Decreasing_sum_abs_eq hM]
  norm_num

/-- Higham printed p. 83: increasing order computes `0`. -/
theorem fl_p91Increasing_eq_zero (fp : FPModel) (M : ℝ)
    (h : P91CancellationRounding fp M) :
    fl_p91Increasing fp M = 0 := by
  have hcancel : fp.fl_add (3 * M) (-(3 * M)) = 0 := by
    apply fl_add_eq_zero_of_add_eq_zero
    ring
  norm_num [fl_p91Increasing, fl_recursiveSum, p91IncreasingInput,
    Fin.foldl_succ, fp.fl_add_zero, h.one_add_M, h.M_add_twoM, hcancel]

/-- Higham printed p. 83: Psum order computes `0`. -/
theorem fl_p91Psum_eq_zero (fp : FPModel) (M : ℝ)
    (h : P91CancellationRounding fp M) :
    fl_p91Psum fp M = 0 := by
  have hcancel : fp.fl_add (-(2 * M)) (2 * M) = 0 := by
    apply fl_add_eq_zero_of_add_eq_zero
    ring
  norm_num [fl_p91Psum, fl_recursiveSum, p91PsumInput,
    Fin.foldl_succ, fp.fl_add_zero, h.one_add_M, h.M_add_negThreeM,
    hcancel]

/-- Higham printed p. 83: decreasing order computes the exact answer `1`. -/
theorem fl_p91Decreasing_eq_one (fp : FPModel) (M : ℝ)
    (h : P91CancellationRounding fp M) :
    fl_p91Decreasing fp M = 1 := by
  have hcancel : fp.fl_add (-M) M = 0 := by
    apply fl_add_eq_zero_of_add_eq_zero
    ring
  norm_num [fl_p91Decreasing, fl_recursiveSum, p91DecreasingInput,
    Fin.foldl_succ, fp.fl_add_zero, h.negThreeM_add_twoM, hcancel]

/-- Higham printed p. 83: increasing order has relative error `1`. -/
theorem p91Increasing_relError_eq_one (fp : FPModel) (M : ℝ)
    (h : P91CancellationRounding fp M) :
    relError (fl_p91Increasing fp M) (∑ i : Fin 4, p91IncreasingInput M i) =
      1 := by
  rw [fl_p91Increasing_eq_zero fp M h, p91Increasing_exact_sum]
  norm_num [relError]
  rfl

/-- Higham printed p. 83: Psum order has relative error `1`. -/
theorem p91Psum_relError_eq_one (fp : FPModel) (M : ℝ)
    (h : P91CancellationRounding fp M) :
    relError (fl_p91Psum fp M) (∑ i : Fin 4, p91PsumInput M i) = 1 := by
  rw [fl_p91Psum_eq_zero fp M h, p91Psum_exact_sum]
  norm_num [relError]
  rfl

/-- Higham printed p. 83: decreasing order computes the exact sum. -/
theorem fl_p91Decreasing_eq_exact_sum (fp : FPModel) (M : ℝ)
    (h : P91CancellationRounding fp M) :
    fl_p91Decreasing fp M = ∑ i : Fin 4, p91DecreasingInput M i := by
  rw [fl_p91Decreasing_eq_one fp M h, p91Decreasing_exact_sum]

/-- An exact computed result has zero relative error, using Lean's totalized
real division convention. -/
theorem relError_exact_eq_zero (exact : ℝ) :
    relError exact exact = 0 := by
  simp [relError]

/-- If the exact sum is nonzero, a computed zero has relative error one. -/
theorem relError_zero_eq_one_of_ne_zero {exact : ℝ} (hexact : exact ≠ 0) :
    relError 0 exact = 1 := by
  unfold relError
  rw [zero_sub, abs_neg]
  exact div_self (abs_ne_zero.mpr hexact)

/-- Any non-exact computed result has strictly positive relative error when
the exact reference is nonzero. -/
theorem relError_pos_of_ne_exact {computed exact : ℝ}
    (hexact : exact ≠ 0) (hne : computed ≠ exact) :
    0 < relError computed exact := by
  unfold relError
  have hnum : 0 < |computed - exact| := by
    exact abs_pos.mpr (sub_ne_zero.mpr hne)
  have hden : 0 < |exact| := abs_pos.mpr hexact
  exact div_pos hnum hden

/-- A checkable absolute-error certificate relative to the final nonzero
post-cancellation sum gives the corresponding relative-error bound. -/
theorem relError_le_of_abs_sub_le_mul_abs {computed exact ε : ℝ}
    (hexact : exact ≠ 0)
    (hbound : |computed - exact| ≤ ε * |exact|) :
    relError computed exact ≤ ε := by
  unfold relError
  have hden : 0 < |exact| := abs_pos.mpr hexact
  rw [div_le_iff₀ hden]
  exact hbound

/-- General post-cancellation comparison surface for the §4.6 (printed p. 89) advice:
heavy cancellation marks the source regime, but the accuracy conclusion comes
from checkable computed outcomes.  If the decreasing/post-cancellation method
has an explicit absolute-error certificate with relative radius `ε`, and the
competing method has relative error strictly larger than `ε`, then the
post-cancellation method is provably more accurate. -/
theorem heavyCancellation_postCancellation_bound_beats_competitor
    {n : ℕ} {vAccurate vOther : Fin n → ℝ}
    {κ computedAccurate computedOther ε : ℝ}
    (hheavy : HeavyCancellationAtLeast vOther κ)
    (hsame : (∑ i : Fin n, vAccurate i) = ∑ i : Fin n, vOther i)
    (hnz : (∑ i : Fin n, vOther i) ≠ 0)
    (haccurate :
      |computedAccurate - ∑ i : Fin n, vAccurate i| ≤
        ε * |∑ i : Fin n, vAccurate i|)
    (hother : ε < relError computedOther (∑ i : Fin n, vOther i)) :
    HeavyCancellationAtLeast vOther κ ∧
      relError computedAccurate (∑ i : Fin n, vOther i) ≤ ε ∧
      relError computedAccurate (∑ i : Fin n, vOther i) <
        relError computedOther (∑ i : Fin n, vOther i) := by
  have haccurateOther :
      |computedAccurate - ∑ i : Fin n, vOther i| ≤
        ε * |∑ i : Fin n, vOther i| := by
    simpa [hsame] using haccurate
  have hrel :
      relError computedAccurate (∑ i : Fin n, vOther i) ≤ ε :=
    relError_le_of_abs_sub_le_mul_abs hnz haccurateOther
  exact ⟨hheavy, hrel, lt_of_le_of_lt hrel hother⟩

/-- General conditional heavy-cancellation comparison surface for the printed p. 83
advice: when two orderings represent the same nonzero exact sum, one ordering
computes that exact sum, and the competing ordering is inexact, the exact
ordering has strictly smaller relative error.  The heavy-cancellation
hypothesis is carried explicitly as the source regime; by itself it is not
claimed to force either computed outcome. -/
theorem heavyCancellation_exact_result_beats_inexact_result
    {n : ℕ} {vExact vOther : Fin n → ℝ}
    {κ computedExact computedOther : ℝ}
    (hheavy : HeavyCancellationAtLeast vOther κ)
    (hsame : (∑ i : Fin n, vExact i) = ∑ i : Fin n, vOther i)
    (hnz : (∑ i : Fin n, vOther i) ≠ 0)
    (hexact : computedExact = ∑ i : Fin n, vExact i)
    (hinexact : computedOther ≠ ∑ i : Fin n, vOther i) :
    HeavyCancellationAtLeast vOther κ ∧
      relError computedExact (∑ i : Fin n, vOther i) = 0 ∧
      0 < relError computedOther (∑ i : Fin n, vOther i) ∧
      relError computedExact (∑ i : Fin n, vOther i) <
        relError computedOther (∑ i : Fin n, vOther i) := by
  have hcomputedExact :
      computedExact = ∑ i : Fin n, vOther i := by
    rw [hexact, hsame]
  constructor
  · exact hheavy
  constructor
  · rw [hcomputedExact]
    exact relError_exact_eq_zero _
  constructor
  · exact relError_pos_of_ne_exact hnz hinexact
  · rw [hcomputedExact, relError_exact_eq_zero]
    exact relError_pos_of_ne_exact hnz hinexact

/-- Conditional heavy-cancellation comparison surface for the printed p. 83 advice:
when two orderings represent the same nonzero exact sum, one ordering computes
that exact sum, and the other collapses to zero, the exact ordering has
strictly smaller relative error.  The heavy-cancellation hypothesis is carried
explicitly so this theorem can be used as a source-facing bridge without
claiming that heavy cancellation alone forces the two computed outcomes. -/
theorem heavyCancellation_exact_result_beats_zero_result
    {n : ℕ} {vExact vZero : Fin n → ℝ}
    {κ computedExact computedZero : ℝ}
    (hheavy : HeavyCancellationAtLeast vZero κ)
    (hsame : (∑ i : Fin n, vExact i) = ∑ i : Fin n, vZero i)
    (hnz : (∑ i : Fin n, vZero i) ≠ 0)
    (hexact : computedExact = ∑ i : Fin n, vExact i)
    (hzero : computedZero = 0) :
    HeavyCancellationAtLeast vZero κ ∧
      relError computedExact (∑ i : Fin n, vZero i) = 0 ∧
      relError computedZero (∑ i : Fin n, vZero i) = 1 ∧
      relError computedExact (∑ i : Fin n, vZero i) <
        relError computedZero (∑ i : Fin n, vZero i) := by
  have hcomputedExact :
      computedExact = ∑ i : Fin n, vZero i := by
    rw [hexact, hsame]
  constructor
  · exact hheavy
  constructor
  · rw [hcomputedExact]
    exact relError_exact_eq_zero _
  constructor
  · rw [hzero]
    exact relError_zero_eq_one_of_ne_zero hnz
  · rw [hcomputedExact, hzero, relError_exact_eq_zero,
      relError_zero_eq_one_of_ne_zero hnz]
    norm_num

/-- In Higham's printed p. 83 heavy-cancellation example, the decreasing order has
strictly smaller relative error than increasing order: decreasing computes the
common exact sum, while increasing order collapses to zero. -/
theorem p91_decreasing_beats_increasing_under_heavyCancellation
    (fp : FPModel) {M : ℝ} (hM : 0 ≤ M)
    (h : P91CancellationRounding fp M) :
    HeavyCancellationAtLeast (p91IncreasingInput M) (1 + 6 * M) ∧
      relError (fl_p91Decreasing fp M)
          (∑ i : Fin 4, p91IncreasingInput M i) = 0 ∧
      relError (fl_p91Increasing fp M)
          (∑ i : Fin 4, p91IncreasingInput M i) = 1 ∧
      relError (fl_p91Decreasing fp M)
          (∑ i : Fin 4, p91IncreasingInput M i) <
        relError (fl_p91Increasing fp M)
          (∑ i : Fin 4, p91IncreasingInput M i) := by
  refine
    heavyCancellation_exact_result_beats_zero_result
      (vExact := p91DecreasingInput M)
      (vZero := p91IncreasingInput M)
      (κ := 1 + 6 * M)
      (computedExact := fl_p91Decreasing fp M)
      (computedZero := fl_p91Increasing fp M)
      (p91Increasing_heavyCancellationAtLeast hM) ?_ ?_ ?_ ?_
  · rw [p91Decreasing_exact_sum, p91Increasing_exact_sum]
  · rw [p91Increasing_exact_sum]
    norm_num
  · exact fl_p91Decreasing_eq_exact_sum fp M h
  · exact fl_p91Increasing_eq_zero fp M h

/-- In Higham's printed p. 83 heavy-cancellation example, the decreasing order has
strictly smaller relative error than Psum order: decreasing computes the common
exact sum, while Psum collapses to zero. -/
theorem p91_decreasing_beats_psum_under_heavyCancellation
    (fp : FPModel) {M : ℝ} (hM : 0 ≤ M)
    (h : P91CancellationRounding fp M) :
    HeavyCancellationAtLeast (p91PsumInput M) (1 + 6 * M) ∧
      relError (fl_p91Decreasing fp M)
          (∑ i : Fin 4, p91PsumInput M i) = 0 ∧
      relError (fl_p91Psum fp M)
          (∑ i : Fin 4, p91PsumInput M i) = 1 ∧
      relError (fl_p91Decreasing fp M)
          (∑ i : Fin 4, p91PsumInput M i) <
        relError (fl_p91Psum fp M)
          (∑ i : Fin 4, p91PsumInput M i) := by
  refine
    heavyCancellation_exact_result_beats_zero_result
      (vExact := p91DecreasingInput M)
      (vZero := p91PsumInput M)
      (κ := 1 + 6 * M)
      (computedExact := fl_p91Decreasing fp M)
      (computedZero := fl_p91Psum fp M)
      (p91Psum_heavyCancellationAtLeast hM) ?_ ?_ ?_ ?_
  · rw [p91Decreasing_exact_sum, p91Psum_exact_sum]
  · rw [p91Psum_exact_sum]
    norm_num
  · exact fl_p91Decreasing_eq_exact_sum fp M h
  · exact fl_p91Psum_eq_zero fp M h

/-- The printed p. 83 decreasing-order computation also fits the checkable
post-cancellation certificate route: the decreasing result has zero absolute
error, while increasing order has relative error one. -/
theorem p91_decreasing_postCancellation_bound_beats_increasing
    (fp : FPModel) {M : ℝ} (hM : 0 ≤ M)
    (h : P91CancellationRounding fp M) :
    HeavyCancellationAtLeast (p91IncreasingInput M) (1 + 6 * M) ∧
      relError (fl_p91Decreasing fp M)
          (∑ i : Fin 4, p91IncreasingInput M i) ≤ 0 ∧
      relError (fl_p91Decreasing fp M)
          (∑ i : Fin 4, p91IncreasingInput M i) <
        relError (fl_p91Increasing fp M)
          (∑ i : Fin 4, p91IncreasingInput M i) := by
  refine
    heavyCancellation_postCancellation_bound_beats_competitor
      (vAccurate := p91DecreasingInput M)
      (vOther := p91IncreasingInput M)
      (κ := 1 + 6 * M)
      (computedAccurate := fl_p91Decreasing fp M)
      (computedOther := fl_p91Increasing fp M)
      (ε := 0)
      (p91Increasing_heavyCancellationAtLeast hM) ?_ ?_ ?_ ?_
  · rw [p91Decreasing_exact_sum, p91Increasing_exact_sum]
  · rw [p91Increasing_exact_sum]
    norm_num
  · rw [fl_p91Decreasing_eq_exact_sum fp M h]
    simp
  · rw [p91Increasing_relError_eq_one fp M h]
    norm_num

/-- The same checkable post-cancellation route compares decreasing order
against the Psum collapse in Higham's printed p. 83 example. -/
theorem p91_decreasing_postCancellation_bound_beats_psum
    (fp : FPModel) {M : ℝ} (hM : 0 ≤ M)
    (h : P91CancellationRounding fp M) :
    HeavyCancellationAtLeast (p91PsumInput M) (1 + 6 * M) ∧
      relError (fl_p91Decreasing fp M)
          (∑ i : Fin 4, p91PsumInput M i) ≤ 0 ∧
      relError (fl_p91Decreasing fp M)
          (∑ i : Fin 4, p91PsumInput M i) <
        relError (fl_p91Psum fp M)
          (∑ i : Fin 4, p91PsumInput M i) := by
  refine
    heavyCancellation_postCancellation_bound_beats_competitor
      (vAccurate := p91DecreasingInput M)
      (vOther := p91PsumInput M)
      (κ := 1 + 6 * M)
      (computedAccurate := fl_p91Decreasing fp M)
      (computedOther := fl_p91Psum fp M)
      (ε := 0)
      (p91Psum_heavyCancellationAtLeast hM) ?_ ?_ ?_ ?_
  · rw [p91Decreasing_exact_sum, p91Psum_exact_sum]
  · rw [p91Psum_exact_sum]
    norm_num
  · rw [fl_p91Decreasing_eq_exact_sum fp M h]
    simp
  · rw [p91Psum_relError_eq_one fp M h]
    norm_num

/-- The left-chain tree agrees with recursive summation for the printed p. 83
increasing order. -/
theorem p91RecursiveFourTree_eval_increasing_eq (fp : FPModel) (M : ℝ) :
    p91RecursiveFourTree.eval fp (p91IncreasingInput M) =
      fl_p91Increasing fp M := by
  norm_num [p91RecursiveFourTree, SumTree.eval, fl_p91Increasing,
    fl_recursiveSum, p91IncreasingInput, Fin.foldl_succ, fp.fl_add_zero,
    Fin.castAdd, Fin.natAdd, Fin.addNat, Fin.castLE]

/-- The left-chain tree agrees with recursive summation for the printed p. 83 Psum
order. -/
theorem p91RecursiveFourTree_eval_psum_eq (fp : FPModel) (M : ℝ) :
    p91RecursiveFourTree.eval fp (p91PsumInput M) = fl_p91Psum fp M := by
  norm_num [p91RecursiveFourTree, SumTree.eval, fl_p91Psum, fl_recursiveSum,
    p91PsumInput, Fin.foldl_succ, fp.fl_add_zero, Fin.castAdd, Fin.natAdd,
    Fin.addNat, Fin.castLE]

/-- The left-chain tree agrees with recursive summation for the printed p. 83
decreasing order. -/
theorem p91RecursiveFourTree_eval_decreasing_eq (fp : FPModel) (M : ℝ) :
    p91RecursiveFourTree.eval fp (p91DecreasingInput M) =
      fl_p91Decreasing fp M := by
  norm_num [p91RecursiveFourTree, SumTree.eval, fl_p91Decreasing,
    fl_recursiveSum, p91DecreasingInput, Fin.foldl_succ, fp.fl_add_zero,
    Fin.castAdd, Fin.natAdd, Fin.addNat, Fin.castLE]

/-- Higham printed p. 83: the running-error budget `µ` for increasing order is `4M`. -/
theorem p91Increasing_runningErrorBudget_eq (fp : FPModel) {M : ℝ}
    (hM : 0 ≤ M) (h : P91CancellationRounding fp M) :
    SumTree.runningErrorBudget fp p91RecursiveFourTree
        (p91IncreasingInput M) = 4 * M := by
  have h3M : 0 ≤ 3 * M := by linarith
  have hcancel : fp.fl_add (3 * M) (-(3 * M)) = 0 := by
    apply fl_add_eq_zero_of_add_eq_zero
    ring
  simp [p91RecursiveFourTree, SumTree.runningErrorBudget, SumTree.eval,
    p91IncreasingInput, h.one_add_M, h.M_add_twoM, hcancel,
    abs_of_nonneg hM, abs_of_nonneg h3M]
  ring

/-- Higham printed p. 83: the running-error budget `µ` for Psum order is `3M`. -/
theorem p91Psum_runningErrorBudget_eq (fp : FPModel) {M : ℝ}
    (hM : 0 ≤ M) (h : P91CancellationRounding fp M) :
    SumTree.runningErrorBudget fp p91RecursiveFourTree (p91PsumInput M) =
      3 * M := by
  have hneg2M : -(2 * M) ≤ 0 := by linarith
  have hcancel : fp.fl_add (-(2 * M)) (2 * M) = 0 := by
    apply fl_add_eq_zero_of_add_eq_zero
    ring
  simp [p91RecursiveFourTree, SumTree.runningErrorBudget, SumTree.eval,
    p91PsumInput, h.one_add_M, h.M_add_negThreeM, hcancel,
    abs_of_nonneg hM, abs_of_nonpos hneg2M]
  ring

/-- Higham printed p. 83: the running-error budget `µ` for decreasing order is
`M + 1`. -/
theorem p91Decreasing_runningErrorBudget_eq (fp : FPModel) {M : ℝ}
    (hM : 0 ≤ M) (h : P91CancellationRounding fp M) :
    SumTree.runningErrorBudget fp p91RecursiveFourTree
        (p91DecreasingInput M) = M + 1 := by
  have hnegM : -M ≤ 0 := by linarith
  have hcancel : fp.fl_add (-M) M = 0 := by
    apply fl_add_eq_zero_of_add_eq_zero
    ring
  simp [p91RecursiveFourTree, SumTree.runningErrorBudget, SumTree.eval,
    p91DecreasingInput, h.negThreeM_add_twoM, hcancel, fp.fl_add_zero,
    abs_of_nonpos hnegM]

/-- For the large positive `M` regime of example (4.5), the displayed budgets
rank decreasing order ahead of Psum and increasing order. -/
theorem p91_runningErrorBudget_ranking {M : ℝ} (hM : 1 ≤ M) :
    M + 1 ≤ 3 * M ∧ 3 * M ≤ 4 * M := by
  constructor <;> linarith

end NumStability
