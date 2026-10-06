-- Source/Higham/Chapter08/Lemma08Discrepancy.lean
--
-- Terminal source-discrepancy certificate for the reversed row-dominance
-- inequality printed immediately before Higham Chapter 8, Lemma 8.8.

import NumStability.Algorithms.HighamLemma88Entrywise

namespace NumStability

open scoped BigOperators

/-!
The PDF prints

`|u_ii| <= sum_{j > i} |u_ij|`

where the proof and conclusion of Lemma 8.8 require the opposite inequality.
The following explicit nonsingular upper-triangular matrix satisfies the
literal printed condition but has Skeel condition number `5`, exceeding the
claimed `2*n - 1 = 3` bound.
-/

/-- Literal-source counterexample matrix `[[1/2, 1], [0, 1]]`. -/
noncomputable def higham8_8_printedRowDominanceCounterU : Fin 2 → Fin 2 → ℝ :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then 1 / 2
    else if i.val = 0 ∧ j.val = 1 then 1
    else if i.val = 1 ∧ j.val = 1 then 1
    else 0

/-- Exact inverse `[[2, -2], [0, 1]]` of the counterexample matrix. -/
noncomputable def higham8_8_printedRowDominanceCounterUInv : Fin 2 → Fin 2 → ℝ :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then 2
    else if i.val = 0 ∧ j.val = 1 then -2
    else if i.val = 1 ∧ j.val = 1 then 1
    else 0

/-- The counterexample satisfies the inequality direction literally printed
before Lemma 8.8. -/
theorem higham8_8_printedRowDominanceCounter_satisfies_source :
    higham8_rowDominantUpperSource 2
      higham8_8_printedRowDominanceCounterU := by
  constructor
  · intro i j hji
    fin_cases i <;> fin_cases j <;>
      simp [higham8_8_printedRowDominanceCounterU] at hji ⊢
  · intro i hi
    fin_cases i
    · norm_num [Finset.sum_filter, Fin.sum_univ_two,
        higham8_8_printedRowDominanceCounterU]
    · norm_num at hi

/-- The displayed inverse is a genuine two-sided inverse. -/
theorem higham8_8_printedRowDominanceCounter_isInverse :
    IsInverse 2 higham8_8_printedRowDominanceCounterU
      higham8_8_printedRowDominanceCounterUInv := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Fin.sum_univ_two,
        higham8_8_printedRowDominanceCounterU,
        higham8_8_printedRowDominanceCounterUInv] <;> ring_nf
    all_goals rfl
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Fin.sum_univ_two,
        higham8_8_printedRowDominanceCounterU,
        higham8_8_printedRowDominanceCounterUInv] <;> ring_nf
    all_goals first | rfl | exact sub_self (1 : ℝ)

/-- The literal-source counterexample has Skeel condition number exactly 5. -/
theorem higham8_8_printedRowDominanceCounter_condSkeel_eq :
    condSkeel 2 (by norm_num) higham8_8_printedRowDominanceCounterU
      higham8_8_printedRowDominanceCounterUInv = 5 := by
  unfold condSkeel
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _hi
    fin_cases i
    · norm_num [Fin.sum_univ_two,
        higham8_8_printedRowDominanceCounterU,
        higham8_8_printedRowDominanceCounterUInv]
      simpa [add_comm] using (show (2 : ℝ) + 3 ≤ 5 by norm_num)
    · norm_num [Fin.sum_univ_two,
        higham8_8_printedRowDominanceCounterU,
        higham8_8_printedRowDominanceCounterUInv]
  · have h := Finset.le_sup'
        (fun i : Fin 2 =>
          ∑ j : Fin 2, |higham8_8_printedRowDominanceCounterUInv i j| *
            ∑ k : Fin 2, |higham8_8_printedRowDominanceCounterU j k|)
        (Finset.mem_univ (0 : Fin 2))
    have hrow :
        (∑ j : Fin 2,
          |higham8_8_printedRowDominanceCounterUInv (0 : Fin 2) j| *
            ∑ k : Fin 2, |higham8_8_printedRowDominanceCounterU j k|) = 5 := by
      norm_num [Fin.sum_univ_two,
        higham8_8_printedRowDominanceCounterU,
        higham8_8_printedRowDominanceCounterUInv]
      simpa [add_comm] using (show (2 : ℝ) + 3 = 5 by norm_num)
    rw [hrow] at h
    exact h

/-- **Terminal source correction for Lemma 8.8.** The reversed inequality
printed in the PDF does not imply the claimed `cond(U) <= 2*n - 1` conclusion,
even for a nonsingular upper-triangular `2 × 2` matrix. The corrected theorem
is `higham8_8_rowDiagDominantUpper_condSkeel_bound`. -/
theorem higham8_8_printed_rowDominance_condSkeel_claim_false :
    ∃ U U_inv : Fin 2 → Fin 2 → ℝ,
      higham8_rowDominantUpperSource 2 U ∧
      IsInverse 2 U U_inv ∧
      condSkeel 2 (by norm_num) U U_inv > 2 * (2 : ℝ) - 1 := by
  refine ⟨higham8_8_printedRowDominanceCounterU,
    higham8_8_printedRowDominanceCounterUInv,
    higham8_8_printedRowDominanceCounter_satisfies_source,
    higham8_8_printedRowDominanceCounter_isInverse, ?_⟩
  rw [higham8_8_printedRowDominanceCounter_condSkeel_eq]
  norm_num

end NumStability
