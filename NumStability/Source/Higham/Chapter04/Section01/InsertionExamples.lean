-- Source/Higham/Chapter04/Section01/InsertionExamples.lean

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Algorithms.Summation.Pairwise.Core
import NumStability.Algorithms.Summation.Recursive.Core
import NumStability.Algorithms.Summation.Tree.Balanced
import NumStability.Analysis.Error
import NumStability.Analysis.Summation.Signs

namespace NumStability

/-!
# Higham Section 4.1 insertion-summation examples

This source module records Higham's displayed `1,2,4,8` insertion schedule
and the near-one four-entry schedule, together with their recursive/pairwise
identifications and error corollaries.
-/

open scoped BigOperators

/-- The insertion tree for Higham's `1, 2, 4, 8` example:
`(((x1 + x2) + x3) + x4)`. -/
def insertionPowersFourTree : SumTree 4 :=
  SumTree.node
    (SumTree.node
      (SumTree.node SumTree.leaf SumTree.leaf)
      SumTree.leaf)
    SumTree.leaf

/-- The insertion tree for Higham's near-one four-entry example:
`(x1 + x2) + (x3 + x4)`. -/
def insertionNearOneFourTree : SumTree 4 :=
  SumTree.node
    (SumTree.node SumTree.leaf SumTree.leaf)
    (SumTree.node SumTree.leaf SumTree.leaf)

/-- Source input `1, 2, 4, 8`. -/
noncomputable def insertionPowersFourInput : Fin 4 → ℝ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 4
  | _ => 8

/-- Source input `1, 1 + eps, 1 + 2 eps, 1 + 3 eps`. -/
noncomputable def insertionNearOneFourInput (eps : ℝ) : Fin 4 → ℝ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1 + eps
  | ⟨2, _⟩ => 1 + 2 * eps
  | _ => 1 + 3 * eps

/-- The powers-of-two insertion example performs three additions. -/
theorem insertionPowersFourTree_numAdds :
    insertionPowersFourTree.numAdds = 3 := by
  norm_num [insertionPowersFourTree, SumTree.numAdds]

/-- The near-one insertion example performs three additions. -/
theorem insertionNearOneFourTree_numAdds :
    insertionNearOneFourTree.numAdds = 3 := by
  norm_num [insertionNearOneFourTree, SumTree.numAdds]

/-- The powers-of-two insertion example has recursive depth three. -/
theorem insertionPowersFourTree_depth :
    insertionPowersFourTree.depth = 3 := by
  norm_num [insertionPowersFourTree, SumTree.depth]

/-- The near-one insertion example has pairwise depth two. -/
theorem insertionNearOneFourTree_depth :
    insertionNearOneFourTree.depth = 2 := by
  norm_num [insertionNearOneFourTree, SumTree.depth]

/-- Exact ordering facts behind Higham's displayed
`1248 -> 348 -> 78 -> 15` insertion trace. -/
theorem insertionPowersFour_exact_order :
    1 + 2 = (3 : ℝ) ∧ (3 : ℝ) ≤ 4 ∧ 3 + 4 = (7 : ℝ) ∧ (7 : ℝ) ≤ 8 ∧
      7 + 8 = (15 : ℝ) := by
  norm_num

/-- Exact ordering facts behind Higham's displayed near-one insertion trace:
for `0 < eps < 1/2`, the newly formed sums are inserted at the end, giving the
four-entry pairwise parenthesization. -/
theorem insertionNearOneFour_exact_order {eps : ℝ} (hpos : 0 < eps)
    (hlt : eps < 1 / 2) :
    1 + (1 + eps) = 2 + eps ∧
      1 + 2 * eps ≤ 1 + 3 * eps ∧
      1 + 3 * eps ≤ 2 + eps ∧
      (1 + 2 * eps) + (1 + 3 * eps) = 2 + 5 * eps ∧
      2 + eps ≤ 2 + 5 * eps ∧
      (2 + eps) + (2 + 5 * eps) = 4 + 6 * eps := by
  constructor
  · ring
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · ring
  constructor
  · linarith
  · ring

/-- Floating-point evaluation of the powers-of-two insertion example. -/
noncomputable def fl_insertionPowersFour (fp : FPModel) : ℝ :=
  insertionPowersFourTree.eval fp insertionPowersFourInput

/-- The powers-of-two insertion example has the displayed recursive
parenthesization. -/
theorem fl_insertionPowersFour_eq (fp : FPModel) :
    fl_insertionPowersFour fp =
      fp.fl_add (fp.fl_add (fp.fl_add 1 2) 4) 8 := by
  norm_num [fl_insertionPowersFour, insertionPowersFourTree,
    insertionPowersFourInput, SumTree.eval, Fin.castAdd, Fin.natAdd,
    Fin.addNat, Fin.castLE]

/-- The powers-of-two insertion example agrees with the public recursive-sum
loop on the same four entries. -/
theorem fl_insertionPowersFour_eq_recursiveSum (fp : FPModel) :
    fl_insertionPowersFour fp =
      fl_recursiveSum fp 4 insertionPowersFourInput := by
  norm_num [fl_insertionPowersFour, fl_recursiveSum, insertionPowersFourTree,
    insertionPowersFourInput, SumTree.eval, Fin.castAdd, Fin.natAdd,
    Fin.addNat, Fin.castLE, Fin.succ, Fin.foldl_succ, fp.fl_add_zero]

/-- Floating-point evaluation of the near-one insertion example. -/
noncomputable def fl_insertionNearOneFour (fp : FPModel) (eps : ℝ) : ℝ :=
  insertionNearOneFourTree.eval fp (insertionNearOneFourInput eps)

/-- The near-one insertion example has the displayed pairwise
parenthesization. -/
theorem fl_insertionNearOneFour_eq (fp : FPModel) (eps : ℝ) :
    fl_insertionNearOneFour fp eps =
      fp.fl_add (fp.fl_add 1 (1 + eps))
        (fp.fl_add (1 + 2 * eps) (1 + 3 * eps)) := by
  norm_num [fl_insertionNearOneFour, insertionNearOneFourTree,
    insertionNearOneFourInput, SumTree.balancedTree, SumTree.eval,
    Fin.castAdd, Fin.natAdd, Fin.addNat, Fin.castLE]

/-- The near-one insertion example agrees with the public pairwise-sum routine
for four entries. -/
theorem fl_insertionNearOneFour_eq_pairwiseSum (fp : FPModel) (eps : ℝ) :
    fl_insertionNearOneFour fp eps =
      fl_pairwiseSum fp 2 (insertionNearOneFourInput eps) := by
  norm_num [fl_insertionNearOneFour, insertionNearOneFourTree,
    insertionNearOneFourInput, fl_pairwiseSum, SumTree.eval, Fin.castAdd,
    Fin.natAdd, Fin.addNat, Fin.castLE]

/-- Backward-error bound for the powers-of-two insertion example. -/
theorem insertionPowersFour_backward_error (fp : FPModel)
    (hγ : gammaValid fp 3) :
    ∃ η : Fin 4 → ℝ,
      (∀ i, |η i| ≤ gamma fp 3) ∧
      fl_insertionPowersFour fp =
        ∑ i : Fin 4, insertionPowersFourInput i * (1 + η i) := by
  have ht : gammaValid fp insertionPowersFourTree.depth := by
    simpa [insertionPowersFourTree_depth] using hγ
  obtain ⟨η, hη, hsum⟩ :=
    SumTree.backward_error fp insertionPowersFourTree ht insertionPowersFourInput
  rw [insertionPowersFourTree_depth] at hη
  exact ⟨η, hη, by simpa [fl_insertionPowersFour] using hsum⟩

/-- Forward-error bound for the powers-of-two insertion example. -/
theorem insertionPowersFour_forward_error_bound (fp : FPModel)
    (hγ : gammaValid fp 3) :
    |fl_insertionPowersFour fp - ∑ i : Fin 4, insertionPowersFourInput i| ≤
      gamma fp 3 * ∑ i : Fin 4, |insertionPowersFourInput i| := by
  have ht : gammaValid fp insertionPowersFourTree.depth := by
    simpa [insertionPowersFourTree_depth] using hγ
  have hbound :=
    SumTree.forward_error fp insertionPowersFourTree ht insertionPowersFourInput
  simpa [fl_insertionPowersFour, insertionPowersFourTree_depth] using hbound

/-- Running-error bound for the powers-of-two insertion example in the
source-facing inverse model of Higham eqs. (4.1)--(4.3). -/
theorem insertionPowersFour_running_error_bound_from_inverse_models
    (fp : FPModel)
    (hmodel :
      SumTree.inverseEvalModel fp insertionPowersFourTree
        insertionPowersFourInput) :
    |(∑ i : Fin 4, insertionPowersFourInput i) - fl_insertionPowersFour fp| ≤
      fp.u * SumTree.runningErrorBudget fp insertionPowersFourTree
        insertionPowersFourInput := by
  simpa [fl_insertionPowersFour] using
    SumTree.running_error_sum_bound_from_inverse_models fp
      insertionPowersFourTree insertionPowersFourInput hmodel

/-- The powers-of-two insertion example is one-signed. -/
theorem insertionPowersFour_oneSigned : OneSigned insertionPowersFourInput := by
  left
  intro i
  fin_cases i <;> norm_num [insertionPowersFourInput]

/-- Forward-error bound for the powers-of-two insertion example in one-signed
relative numerator form. -/
theorem insertionPowersFour_forward_error_bound_oneSigned (fp : FPModel)
    (hγ : gammaValid fp 3) :
    |fl_insertionPowersFour fp - ∑ i : Fin 4, insertionPowersFourInput i| ≤
      gamma fp 3 * |∑ i : Fin 4, insertionPowersFourInput i| := by
  have hbound := insertionPowersFour_forward_error_bound fp hγ
  simpa [sum_abs_eq_abs_sum_of_oneSigned insertionPowersFourInput
      insertionPowersFour_oneSigned] using hbound

/-- Relative-error bound for the powers-of-two insertion example. -/
theorem insertionPowersFour_relError_le_gamma_of_oneSigned (fp : FPModel)
    (hγ : gammaValid fp 3)
    (hsum : (∑ i : Fin 4, insertionPowersFourInput i) ≠ 0) :
    relError (fl_insertionPowersFour fp)
        (∑ i : Fin 4, insertionPowersFourInput i) ≤ gamma fp 3 := by
  have hden : 0 < |∑ i : Fin 4, insertionPowersFourInput i| :=
    abs_pos.mpr hsum
  have hbound := insertionPowersFour_forward_error_bound_oneSigned fp hγ
  unfold relError
  rw [div_le_iff₀ hden]
  exact hbound

/-- Backward-error bound for the near-one insertion example. -/
theorem insertionNearOneFour_backward_error (fp : FPModel) (eps : ℝ)
    (hγ : gammaValid fp 2) :
    ∃ η : Fin 4 → ℝ,
      (∀ i, |η i| ≤ gamma fp 2) ∧
      fl_insertionNearOneFour fp eps =
        ∑ i : Fin 4, insertionNearOneFourInput eps i * (1 + η i) := by
  have ht : gammaValid fp insertionNearOneFourTree.depth := by
    simpa [insertionNearOneFourTree_depth] using hγ
  obtain ⟨η, hη, hsum⟩ :=
    SumTree.backward_error fp insertionNearOneFourTree ht
      (insertionNearOneFourInput eps)
  rw [insertionNearOneFourTree_depth] at hη
  exact ⟨η, hη, by simpa [fl_insertionNearOneFour] using hsum⟩

/-- Forward-error bound for the near-one insertion example. -/
theorem insertionNearOneFour_forward_error_bound (fp : FPModel) (eps : ℝ)
    (hγ : gammaValid fp 2) :
    |fl_insertionNearOneFour fp eps -
        ∑ i : Fin 4, insertionNearOneFourInput eps i| ≤
      gamma fp 2 * ∑ i : Fin 4, |insertionNearOneFourInput eps i| := by
  have ht : gammaValid fp insertionNearOneFourTree.depth := by
    simpa [insertionNearOneFourTree_depth] using hγ
  have hbound :=
    SumTree.forward_error fp insertionNearOneFourTree ht
      (insertionNearOneFourInput eps)
  simpa [fl_insertionNearOneFour, insertionNearOneFourTree_depth] using hbound

/-- Running-error bound for the near-one insertion example in the source-facing
inverse model of Higham eqs. (4.1)--(4.3). -/
theorem insertionNearOneFour_running_error_bound_from_inverse_models
    (fp : FPModel) (eps : ℝ)
    (hmodel :
      SumTree.inverseEvalModel fp insertionNearOneFourTree
        (insertionNearOneFourInput eps)) :
    |(∑ i : Fin 4, insertionNearOneFourInput eps i) -
        fl_insertionNearOneFour fp eps| ≤
      fp.u * SumTree.runningErrorBudget fp insertionNearOneFourTree
        (insertionNearOneFourInput eps) := by
  simpa [fl_insertionNearOneFour] using
    SumTree.running_error_sum_bound_from_inverse_models fp
      insertionNearOneFourTree (insertionNearOneFourInput eps) hmodel

/-- The near-one insertion example is one-signed when `eps` is positive. -/
theorem insertionNearOneFour_oneSigned {eps : ℝ} (hpos : 0 < eps) :
    OneSigned (insertionNearOneFourInput eps) := by
  left
  intro i
  fin_cases i <;> simp [insertionNearOneFourInput] <;> linarith

/-- Forward-error bound for the near-one insertion example in one-signed
relative numerator form. -/
theorem insertionNearOneFour_forward_error_bound_oneSigned (fp : FPModel)
    {eps : ℝ} (hγ : gammaValid fp 2) (hpos : 0 < eps) :
    |fl_insertionNearOneFour fp eps -
        ∑ i : Fin 4, insertionNearOneFourInput eps i| ≤
      gamma fp 2 * |∑ i : Fin 4, insertionNearOneFourInput eps i| := by
  have hbound := insertionNearOneFour_forward_error_bound fp eps hγ
  simpa [sum_abs_eq_abs_sum_of_oneSigned (insertionNearOneFourInput eps)
      (insertionNearOneFour_oneSigned hpos)] using hbound

/-- Relative-error bound for the near-one insertion example. -/
theorem insertionNearOneFour_relError_le_gamma_of_oneSigned (fp : FPModel)
    {eps : ℝ} (hγ : gammaValid fp 2) (hpos : 0 < eps)
    (hsum : (∑ i : Fin 4, insertionNearOneFourInput eps i) ≠ 0) :
    relError (fl_insertionNearOneFour fp eps)
        (∑ i : Fin 4, insertionNearOneFourInput eps i) ≤ gamma fp 2 := by
  have hden : 0 < |∑ i : Fin 4, insertionNearOneFourInput eps i| :=
    abs_pos.mpr hsum
  have hbound :=
    insertionNearOneFour_forward_error_bound_oneSigned fp hγ hpos
  unfold relError
  rw [div_le_iff₀ hden]
  exact hbound

end NumStability
