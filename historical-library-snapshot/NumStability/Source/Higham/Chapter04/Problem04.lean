-- Source/Higham/Chapter04/Problem04.lean

import Mathlib.Data.List.Permutation
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace NumStability

/-!
# Higham Chapter 4, Problem 4.4

The problem asks for all recursive-summation outputs for
`{1, 2, 3, 4, M, -M}` when `M` is so large that adding the total small sum to
`M` is absorbed (`fl(10 + M) = M`).

The finite model below records the source-shaped consequences used by the
exercise: small integer additions are exact, any accumulated small sum up to
`10` is lost when a large term is added, small terms added while a large term
is outstanding are lost, and `M` cancels exactly with `-M`.  The exhaustive
theorem then enumerates all six-term recursive orders.
-/

/-- The six formal inputs of Problem 4.4. -/
inductive Problem44Term where
  | one
  | two
  | three
  | four
  | posM
  | negM
  deriving DecidableEq, Repr

namespace Problem44Term

/-- Real interpretation of a Problem 4.4 formal term. -/
def realValue (M : ℝ) : Problem44Term → ℝ
  | one => 1
  | two => 2
  | three => 3
  | four => 4
  | posM => M
  | negM => -M

/-- The small nonnegative contribution carried by a formal term. -/
def smallValue : Problem44Term → ℕ
  | one => 1
  | two => 2
  | three => 3
  | four => 4
  | posM => 0
  | negM => 0

end Problem44Term

/-- Symbolic recursive-summation accumulator for the absorbing-large-`M`
regime in Problem 4.4. -/
inductive Problem44Accumulator where
  | small (s : ℕ)
  | posLarge
  | negLarge
  deriving DecidableEq, Repr

open Problem44Term Problem44Accumulator

/-- One rounded recursive-summation step in the absorbing-large-`M` regime. -/
def problem44Step : Problem44Accumulator → Problem44Term → Problem44Accumulator
  | small s, one => small (s + 1)
  | small s, two => small (s + 2)
  | small s, three => small (s + 3)
  | small s, four => small (s + 4)
  | small _s, posM => posLarge
  | small _s, negM => negLarge
  | posLarge, negM => small 0
  | negLarge, posM => small 0
  | posLarge, _ => posLarge
  | negLarge, _ => negLarge

/-- Numeric output represented by the symbolic accumulator.

For complete Problem 4.4 permutations the final state is small; the large
fallback branches make the function total on arbitrary lists. -/
def problem44AccumulatorOutput : Problem44Accumulator → ℕ
  | small s => s
  | posLarge => 0
  | negLarge => 0

/-- A single symbolic step cannot increase the visible small output by more
than the small contribution of the consumed term. -/
theorem problem44AccumulatorOutput_step_le
    (acc : Problem44Accumulator) (x : Problem44Term) :
    problem44AccumulatorOutput (problem44Step acc x) ≤
      problem44AccumulatorOutput acc + Problem44Term.smallValue x := by
  cases acc <;> cases x <;>
    simp [problem44Step, problem44AccumulatorOutput,
      Problem44Term.smallValue]

/-- The source multiset `{1,2,3,4,M,-M}` as a concrete list. -/
def problem44Source : List Problem44Term :=
  [one, two, three, four, posM, negM]

/-- Symbolic recursive evaluation of a Problem 4.4 order. -/
def problem44Eval (xs : List Problem44Term) : Problem44Accumulator :=
  xs.foldl problem44Step (small 0)

/-- Numeric output of a symbolic Problem 4.4 recursive order. -/
def problem44Output (xs : List Problem44Term) : ℕ :=
  problem44AccumulatorOutput (problem44Eval xs)

/-- For any continuation, the symbolic output is bounded by the current visible
small accumulator plus the total small value still present in the list. -/
theorem problem44Fold_output_le
    (acc : Problem44Accumulator) :
    ∀ xs : List Problem44Term,
      problem44AccumulatorOutput (xs.foldl problem44Step acc) ≤
        problem44AccumulatorOutput acc +
          (xs.map Problem44Term.smallValue).sum
  | [] => by
      simp
  | x :: xs => by
      have hrec := problem44Fold_output_le (problem44Step acc x) xs
      have hstep := problem44AccumulatorOutput_step_le acc x
      calc
        problem44AccumulatorOutput ((x :: xs).foldl problem44Step acc)
            = problem44AccumulatorOutput (xs.foldl problem44Step
                (problem44Step acc x)) := rfl
        _ ≤ problem44AccumulatorOutput (problem44Step acc x) +
              (xs.map Problem44Term.smallValue).sum := hrec
        _ ≤ (problem44AccumulatorOutput acc + Problem44Term.smallValue x) +
              (xs.map Problem44Term.smallValue).sum := by
            exact Nat.add_le_add_right hstep _
        _ = problem44AccumulatorOutput acc +
              ((x :: xs).map Problem44Term.smallValue).sum := by
            simp
            omega

/-- The output of any symbolic Problem 4.4 order is bounded by the total small
value in that order. -/
theorem problem44Output_le_smallValue_sum (xs : List Problem44Term) :
    problem44Output xs ≤ (xs.map Problem44Term.smallValue).sum := by
  simpa [problem44Output, problem44Eval, problem44AccumulatorOutput] using
    problem44Fold_output_le (small 0) xs

/-- List sum is invariant under permutation for natural-number lists. -/
theorem problem44_nat_list_sum_eq_of_perm {xs ys : List ℕ}
    (hperm : xs.Perm ys) : xs.sum = ys.sum := by
  induction hperm with
  | nil => simp
  | cons x hperm ih => simp [ih]
  | swap x y zs =>
      simp [List.sum_cons]
      omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The exact real sum of the six source terms is `10`. -/
theorem problem44Source_exact_sum (M : ℝ) :
    (problem44Source.map (Problem44Term.realValue M)).sum = 10 := by
  simp [problem44Source, Problem44Term.realValue]
  norm_num

/-- The small contributions in the Problem 4.4 source list sum to `10`. -/
theorem problem44Source_smallValue_sum :
    (problem44Source.map Problem44Term.smallValue).sum = 10 := by
  simp [problem44Source, Problem44Term.smallValue]

/-- All outputs obtained by recursively summing all permutations of the six
Problem 4.4 terms in the absorbing-large-`M` model. -/
def problem44PossibleOutputs : Finset ℕ :=
  (problem44Source.permutations.map problem44Output).toFinset

/-- Every recursive order of the six terms produces a value in `0, ..., 10`. -/
theorem problem44Output_mem_Icc_of_perm (xs : List Problem44Term)
    (hxs : xs.Perm problem44Source) :
    problem44Output xs ∈ Finset.Icc 0 10 := by
  have hsmallPerm :
      (xs.map Problem44Term.smallValue).Perm
        (problem44Source.map Problem44Term.smallValue) :=
    hxs.map Problem44Term.smallValue
  have hsmallSum :
      (xs.map Problem44Term.smallValue).sum = 10 := by
    rw [problem44_nat_list_sum_eq_of_perm hsmallPerm,
      problem44Source_smallValue_sum]
  have hout := problem44Output_le_smallValue_sum xs
  rw [Finset.mem_Icc]
  constructor
  · exact Nat.zero_le _
  · omega

/-- A concrete order attaining each requested output in `0, ..., 10`.

Terms before the adjacent `M, -M` pair are lost; terms after that cancellation
are summed exactly. -/
def problem44WitnessOrder : ℕ → List Problem44Term
  | 0 => [one, two, three, four, posM, negM]
  | 1 => [two, three, four, posM, negM, one]
  | 2 => [one, three, four, posM, negM, two]
  | 3 => [one, two, four, posM, negM, three]
  | 4 => [one, two, three, posM, negM, four]
  | 5 => [two, three, posM, negM, one, four]
  | 6 => [one, three, posM, negM, two, four]
  | 7 => [one, two, posM, negM, three, four]
  | 8 => [two, posM, negM, one, three, four]
  | 9 => [one, posM, negM, two, three, four]
  | 10 => [posM, negM, one, two, three, four]
  | _ => problem44Source

/-- Each concrete witness order is a permutation of the source six terms. -/
theorem problem44WitnessOrder_perm (k : ℕ)
    (hk : k ∈ Finset.Icc 0 10) :
    (problem44WitnessOrder k).Perm problem44Source := by
  rw [Finset.mem_Icc] at hk
  have hcases :
      k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;>
    decide

/-- The concrete witness order for `k` evaluates to `k`. -/
theorem problem44WitnessOrder_output (k : ℕ)
    (hk : k ∈ Finset.Icc 0 10) :
    problem44Output (problem44WitnessOrder k) = k := by
  rw [Finset.mem_Icc] at hk
  have hcases :
      k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;>
    rfl

/-- Every value in `0, ..., 10` is attained by some recursive order of the
six Problem 4.4 terms. -/
theorem problem44Every_Icc_output_attained (k : ℕ)
    (hk : k ∈ Finset.Icc 0 10) :
    ∃ xs : List Problem44Term,
      xs.Perm problem44Source ∧ problem44Output xs = k := by
  exact ⟨problem44WitnessOrder k, problem44WitnessOrder_perm k hk,
    problem44WitnessOrder_output k hk⟩

/-- Exhaustive answer to Problem 4.4: the possible outputs are precisely
`0, 1, ..., 10`. -/
theorem problem44PossibleOutputs_eq_Icc :
    problem44PossibleOutputs = Finset.Icc 0 10 := by
  ext k
  constructor
  · intro hk
    rcases (by
        simpa [problem44PossibleOutputs] using hk :
          ∃ xs : List Problem44Term,
            xs ∈ problem44Source.permutations ∧ problem44Output xs = k) with
      ⟨xs, hmem, hout⟩
    have hperm : xs.Perm problem44Source :=
      List.mem_permutations.mp hmem
    rw [← hout]
    exact problem44Output_mem_Icc_of_perm xs hperm
  · intro hk
    rcases problem44Every_Icc_output_attained k hk with
      ⟨xs, hperm, hout⟩
    have hmem : xs ∈ problem44Source.permutations :=
      List.mem_permutations.mpr hperm
    have hmemList : problem44Output xs ∈
        problem44Source.permutations.map problem44Output :=
      List.mem_map.mpr ⟨xs, hmem, rfl⟩
    have hposs : problem44Output xs ∈ problem44PossibleOutputs := by
      simpa [problem44PossibleOutputs] using hmemList
    simpa [hout] using hposs

/-- Bidirectional packaged form of the exhaustive Problem 4.4 answer. -/
theorem problem44_outputs_exactly_Icc :
    (∀ xs : List Problem44Term,
        xs.Perm problem44Source → problem44Output xs ∈ Finset.Icc 0 10) ∧
      (∀ k : ℕ,
        k ∈ Finset.Icc 0 10 →
          ∃ xs : List Problem44Term,
            xs.Perm problem44Source ∧ problem44Output xs = k) := by
  exact ⟨problem44Output_mem_Icc_of_perm, problem44Every_Icc_output_attained⟩

end NumStability
