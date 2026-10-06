import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Chapter05 Section03 LejaOrdering Basic

Canonical destination for material split out of
`NumStability.Algorithms.Horner` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Higham, 2nd ed., Chapter 5, Section 5.3, equation (5.13b):
the Leja prefix product `prod_{k=0}^{j-1} |alpha_i - alpha_k|`. -/
noncomputable def lejaPrefixProduct
    (nodes : ℕ → ℝ) (j i : ℕ) : ℝ :=
  (Finset.range j).prod (fun k => |nodes i - nodes k|)

theorem lejaPrefixProduct_zero
    (nodes : ℕ → ℝ) (i : ℕ) :
    lejaPrefixProduct nodes 0 i = 1 := by
  simp [lejaPrefixProduct]

theorem lejaPrefixProduct_nonneg
    (nodes : ℕ → ℝ) (j i : ℕ) :
    0 ≤ lejaPrefixProduct nodes j i := by
  unfold lejaPrefixProduct
  exact Finset.prod_nonneg (fun k _ => abs_nonneg (nodes i - nodes k))

theorem lejaPrefixProduct_succ
    (nodes : ℕ → ℝ) (j i : ℕ) :
    lejaPrefixProduct nodes (j + 1) i =
      lejaPrefixProduct nodes j i * |nodes i - nodes j| := by
  simp [lejaPrefixProduct, Finset.prod_range_succ]

/-- Higham (5.13a,b): a Leja ordering of `alpha_0, ..., alpha_n`.

The first node maximizes absolute value over the finite source set, and each
subsequent node maximizes the prefix product against the nodes already chosen.
Ties are allowed, as in the usual mathematical definition. -/
def IsLejaOrdering (nodes : ℕ → ℝ) (n : ℕ) : Prop :=
  (∀ i, i ≤ n → |nodes i| ≤ |nodes 0|) ∧
    ∀ j, 1 ≤ j → j < n →
      ∀ i, j ≤ i → i ≤ n →
        lejaPrefixProduct nodes j i ≤ lejaPrefixProduct nodes j j

/-- First greedy choice in the Leja ordering algorithm: position `0` contains
an index whose node has maximal absolute value among `0:n`. -/
def LejaGreedyFirstChoice (nodes : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ i, i ≤ n → |nodes i| ≤ |nodes 0|

/-- Greedy choice at Leja step `j`: after positions `< j` are fixed, position
`j` maximizes the current prefix product over the remaining positions `j:n`. -/
def LejaGreedyStepChoice (nodes : ℕ → ℝ) (n j : ℕ) : Prop :=
  ∀ i, j ≤ i → i ≤ n →
    lejaPrefixProduct nodes j i ≤ lejaPrefixProduct nodes j j

/-- Certificate surface for the standard greedy Leja-ordering algorithm.  The
algorithm repeatedly swaps a maximizer into the next position; this predicate
records the choices made by such a trace after the swaps have been applied. -/
def IsLejaGreedyTrace (nodes : ℕ → ℝ) (n : ℕ) : Prop :=
  LejaGreedyFirstChoice nodes n ∧
    ∀ j, 1 ≤ j → j < n → LejaGreedyStepChoice nodes n j

/-- A greedy Leja trace satisfies Higham's defining Leja-ordering conditions
(5.13a,b). -/
theorem IsLejaGreedyTrace.isLejaOrdering
    {nodes : ℕ → ℝ} {n : ℕ}
    (htrace : IsLejaGreedyTrace nodes n) :
    IsLejaOrdering nodes n := by
  exact htrace

/-- Source-facing flop budget for the greedy Leja-ordering construction in
Problem 5.4.  The recurrence adds the next odd increment, so after `n` stages
the budget is exactly `n^2`. -/
def lejaGreedyFlopCount : ℕ → ℕ
  | 0 => 0
  | n + 1 => lejaGreedyFlopCount n + (2 * n + 1)

theorem lejaGreedyFlopCount_eq_square (n : ℕ) :
    lejaGreedyFlopCount n = n * n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [lejaGreedyFlopCount, ih]
      ring

end NumStability
