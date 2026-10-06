-- Algorithms/Summation/Insertion/ActiveList.lean

import Mathlib.Data.List.Permutation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace NumStability

/-!
# Ordered active lists for insertion summation

This reusable layer defines increasing-absolute-value active lists, proves the
local nonnegative minimum-pair property, and implements insertion while
preserving order and the input multiset.
-/

/-- A list is ordered by increasing absolute value. This is the active-list
invariant for insertion summation. -/
def IncreasingAbsList : List ℝ → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => |x| ≤ |y| ∧ IncreasingAbsList (y :: rest)

/-- The tail of an increasing-absolute-value list is increasing. -/
theorem IncreasingAbsList.tail {x : ℝ} {xs : List ℝ}
    (h : IncreasingAbsList (x :: xs)) : IncreasingAbsList xs := by
  cases xs with
  | nil => trivial
  | cons y rest => exact h.2

/-- In a nonnegative list sorted by increasing absolute value, the head is
bounded above by every member of the list. -/
theorem IncreasingAbsList.head_le_of_mem_of_nonnegative {x : ℝ}
    {xs : List ℝ}
    (hsorted : IncreasingAbsList (x :: xs))
    (hnonneg : ∀ z ∈ x :: xs, 0 ≤ z) :
    ∀ {y : ℝ}, y ∈ x :: xs → x ≤ y := by
  induction xs generalizing x with
  | nil =>
      intro y hy
      simp at hy
      subst hy
      rfl
  | cons z zs ih =>
      intro y hy
      rcases hsorted with ⟨hxz_abs, htail⟩
      have hx_nonneg : 0 ≤ x := hnonneg x (by simp)
      have hz_nonneg : 0 ≤ z := hnonneg z (by simp)
      have hxz : x ≤ z := by
        simpa [abs_of_nonneg hx_nonneg, abs_of_nonneg hz_nonneg]
          using hxz_abs
      simp at hy
      rcases hy with rfl | hy_tail
      · rfl
      · have htail_nonneg : ∀ w ∈ z :: zs, 0 ≤ w := by
          intro w hw
          exact hnonneg w (by simp [hw])
        have hzy : z ≤ y :=
          ih htail htail_nonneg (by simpa using hy_tail)
        linarith

/-- For a nonnegative increasing active list, adding the first two entries
has no larger exact pair sum than adding the first entry to any later entry. -/
theorem insertion_first_two_exact_sum_le_head_tail_sum_of_nonnegative
    {a b y : ℝ} {rest : List ℝ}
    (hsorted : IncreasingAbsList (a :: b :: rest))
    (hnonneg : ∀ z ∈ a :: b :: rest, 0 ≤ z)
    (hy : y ∈ b :: rest) :
    a + b ≤ a + y := by
  have htail_nonneg : ∀ z ∈ b :: rest, 0 ≤ z := by
    intro z hz
    exact hnonneg z (by simp [hz])
  have hby : b ≤ y :=
    IncreasingAbsList.head_le_of_mem_of_nonnegative
      (IncreasingAbsList.tail hsorted) htail_nonneg hy
  linarith

/-- For a nonnegative increasing active list, adding the first two entries
has no larger exact pair sum than adding any two entries from the tail. -/
theorem insertion_first_two_exact_sum_le_tail_pair_sum_of_nonnegative
    {a b x y : ℝ} {rest : List ℝ}
    (hsorted : IncreasingAbsList (a :: b :: rest))
    (hnonneg : ∀ z ∈ a :: b :: rest, 0 ≤ z)
    (hx : x ∈ b :: rest) (hy : y ∈ b :: rest) :
    a + b ≤ x + y := by
  have ha_le_x : a ≤ x :=
    IncreasingAbsList.head_le_of_mem_of_nonnegative hsorted hnonneg
      (by simp [hx])
  have htail_nonneg : ∀ z ∈ b :: rest, 0 ≤ z := by
    intro z hz
    exact hnonneg z (by simp [hz])
  have hb_le_y : b ≤ y :=
    IncreasingAbsList.head_le_of_mem_of_nonnegative
      (IncreasingAbsList.tail hsorted) htail_nonneg hy
  linarith

/-- Local nonnegative optimality of the insertion choice: among admissible
pairs from a nonnegative active list sorted by increasing absolute value, the
first two entries minimize the next exact intermediate sum.  This is the
one-step foundation for Higham's printed p. 83 insertion optimality claim. -/
theorem insertion_first_two_exact_sum_le_pair_sum_of_nonnegative
    {a b x y : ℝ} {rest : List ℝ}
    (hsorted : IncreasingAbsList (a :: b :: rest))
    (hnonneg : ∀ z ∈ a :: b :: rest, 0 ≤ z)
    (hpair :
      (x = a ∧ y ∈ b :: rest) ∨
        (y = a ∧ x ∈ b :: rest) ∨
          (x ∈ b :: rest ∧ y ∈ b :: rest)) :
    a + b ≤ x + y := by
  rcases hpair with ⟨rfl, hy⟩ | ⟨rfl, hx⟩ | ⟨hx, hy⟩
  · exact insertion_first_two_exact_sum_le_head_tail_sum_of_nonnegative
      hsorted hnonneg hy
  · have hle :=
      insertion_first_two_exact_sum_le_head_tail_sum_of_nonnegative
        hsorted hnonneg hx
    linarith
  · exact insertion_first_two_exact_sum_le_tail_pair_sum_of_nonnegative
      hsorted hnonneg hx hy

/-- Insert a value into a list ordered by increasing absolute value. -/
noncomputable def insertIncreasingAbs (x : ℝ) : List ℝ → List ℝ
  | [] => [x]
  | y :: ys =>
      if |x| ≤ |y| then
        x :: y :: ys
      else
        y :: insertIncreasingAbs x ys

/-- Insertion into an empty ordered list. -/
theorem insertIncreasingAbs_nil (x : ℝ) :
    insertIncreasingAbs x [] = [x] := by
  rfl

/-- Insertion stops before the first entry whose absolute value is no smaller. -/
theorem insertIncreasingAbs_cons_of_le (x y : ℝ) (ys : List ℝ)
    (hxy : |x| ≤ |y|) :
    insertIncreasingAbs x (y :: ys) = x :: y :: ys := by
  simp [insertIncreasingAbs, hxy]

/-- If the new value is larger than the head, insertion recurses into the
tail. -/
theorem insertIncreasingAbs_cons_of_not_le (x y : ℝ) (ys : List ℝ)
    (hxy : ¬ |x| ≤ |y|) :
    insertIncreasingAbs x (y :: ys) = y :: insertIncreasingAbs x ys := by
  simp [insertIncreasingAbs, hxy]

/-- Inserting one value increases the active-list length by one. -/
theorem insertIncreasingAbs_length (x : ℝ) :
    ∀ xs : List ℝ, (insertIncreasingAbs x xs).length = xs.length + 1
  | [] => by simp [insertIncreasingAbs]
  | y :: ys => by
      by_cases hxy : |x| ≤ |y|
      · simp [insertIncreasingAbs, hxy]
      · simp [insertIncreasingAbs, hxy, insertIncreasingAbs_length x ys,
          Nat.add_assoc]

/-- Insertion always leaves a nonempty active list. -/
theorem insertIncreasingAbs_ne_nil (x : ℝ) (xs : List ℝ) :
    insertIncreasingAbs x xs ≠ [] := by
  intro hnil
  have hlen := congrArg List.length hnil
  rw [insertIncreasingAbs_length x xs] at hlen
  simp at hlen

/-- Inserting into an increasing-absolute-value active list only permutes the
new element with the existing elements. -/
theorem insertIncreasingAbs_perm (x : ℝ) :
    ∀ xs : List ℝ, (insertIncreasingAbs x xs).Perm (x :: xs)
  | [] => by simp [insertIncreasingAbs]
  | y :: ys => by
      by_cases hxy : |x| ≤ |y|
      · simp [insertIncreasingAbs, hxy]
      · have hrec := insertIncreasingAbs_perm x ys
        simpa [insertIncreasingAbs, hxy] using
          (List.Perm.cons y hrec).trans (List.Perm.swap x y ys)

/-- Inserting a nonnegative value into a nonnegative list preserves
nonnegativity of all entries. -/
theorem insertIncreasingAbs_nonnegative {x : ℝ} {xs : List ℝ}
    (hx : 0 ≤ x) (hxs : ∀ y ∈ xs, 0 ≤ y) :
    ∀ y ∈ insertIncreasingAbs x xs, 0 ≤ y := by
  intro y hy
  have hperm := insertIncreasingAbs_perm x xs
  have hy' : y ∈ x :: xs := (hperm.mem_iff).1 hy
  simpa using List.forall_mem_cons.2 ⟨hx, hxs⟩ y hy'

/-- Insertion preserves increasing absolute-value order. -/
theorem insertIncreasingAbs_preserves (x : ℝ) :
    ∀ xs : List ℝ,
      IncreasingAbsList xs → IncreasingAbsList (insertIncreasingAbs x xs)
  | [] , _ => by simp [insertIncreasingAbs, IncreasingAbsList]
  | y :: [], _ => by
      by_cases hxy : |x| ≤ |y|
      · simp [insertIncreasingAbs, IncreasingAbsList, hxy]
      · have hyx : |y| ≤ |x| := le_of_lt (lt_of_not_ge hxy)
        simp [insertIncreasingAbs, IncreasingAbsList, hxy, hyx]
  | y :: z :: zs, hsorted => by
      rcases hsorted with ⟨hyz, htail⟩
      by_cases hxy : |x| ≤ |y|
      · simp [insertIncreasingAbs, IncreasingAbsList, hxy, hyz, htail]
      · have hyx : |y| ≤ |x| := le_of_lt (lt_of_not_ge hxy)
        by_cases hxz : |x| ≤ |z|
        · simp [insertIncreasingAbs, IncreasingAbsList, hxy, hxz, hyx,
            htail]
        · have hrec :=
            insertIncreasingAbs_preserves x (z :: zs) htail
          have hrec' :
              IncreasingAbsList (z :: insertIncreasingAbs x zs) := by
            simpa [insertIncreasingAbs, hxz] using hrec
          simp [insertIncreasingAbs, IncreasingAbsList, hxy, hxz, hyz,
            hrec']

end NumStability
