/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# Exact and small-`u` Bunch--Kaufman product growth

This module proves the exact-factor inequality quoted in Higham's discussion
of Theorem 11.4.  The proof is attached to the literal Algorithm 11.2
producer: every branch equality is computed from the current active matrix,
and the global factors are the factors flattened from that execution.

Higham [1997, §4.3] proves the constant `36` for the exact factors and observes
that replacing them by computed factors changes the analysis by `O(u)`.  The
exact theorem below formalizes that source argument.  The same structural
proof, combined with the sharper finite-`u` local bounds proved for the literal
GEPP producer, also yields an independent strengthening: the computed factors
retain the constant `36` when `36u ≤ 1/1000` and the execution completes.

The rounded strengthening uses the maximum over the *rounded* active matrices
actually visited.  It does not identify that quantity with the exact-path
growth factor, and neither theorem assumes a product-entry or target-shaped
growth bound.
-/

import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedGrowth
import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedGlobal
import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanExactGrowthArithmetic

open scoped BigOperators

namespace NumStability

open Ch11Closure.Mixed

private theorem blockOne_absProduct_00 {n : Nat}
    (w : Fin n -> Real) (Ls : Fin n -> Fin n -> Real)
    (d : Real) (Ds : Fin n -> Fin n -> Real) :
    higham11_4_bunchKaufmanProductEntry (n + 1)
      (higham11_2_blockOneL w Ls) (higham11_2_blockOneD d Ds) 0 0 = |d| := by
  simp [higham11_4_bunchKaufmanProductEntry, Fin.sum_univ_succ]

private theorem blockOne_absProduct_0s {n : Nat}
    (w : Fin n -> Real) (Ls : Fin n -> Fin n -> Real)
    (d : Real) (Ds : Fin n -> Fin n -> Real) (j : Fin n) :
    higham11_4_bunchKaufmanProductEntry (n + 1)
      (higham11_2_blockOneL w Ls) (higham11_2_blockOneD d Ds) 0 j.succ =
        |d| * |w j| := by
  simp [higham11_4_bunchKaufmanProductEntry, Fin.sum_univ_succ]

private theorem blockOne_absProduct_s0 {n : Nat}
    (w : Fin n -> Real) (Ls : Fin n -> Fin n -> Real)
    (d : Real) (Ds : Fin n -> Fin n -> Real) (i : Fin n) :
    higham11_4_bunchKaufmanProductEntry (n + 1)
      (higham11_2_blockOneL w Ls) (higham11_2_blockOneD d Ds) i.succ 0 =
        |w i| * |d| := by
  simp [higham11_4_bunchKaufmanProductEntry, Fin.sum_univ_succ]

private theorem blockTwo_absProduct_00 {n : Nat}
    (W : Fin n -> Fin 2 -> Real) (Ls : Fin n -> Fin n -> Real)
    (E : Fin 2 -> Fin 2 -> Real) (Ds : Fin n -> Fin n -> Real) :
    higham11_4_bunchKaufmanProductEntry (n + 2)
      (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
      0 0 = |E 0 0| := by
  simp only [higham11_4_bunchKaufmanProductEntry, sum_fin_add_two,
    higham11_2_blockTwoL_00, higham11_2_blockTwoL_01,
    higham11_2_blockTwoL_0t, higham11_2_blockTwoD_00,
    higham11_2_blockTwoD_01, higham11_2_blockTwoD_0t,
    abs_zero, abs_one, zero_mul, mul_zero, one_mul, mul_one,
    add_zero, zero_add, Finset.sum_const_zero]

private theorem blockTwo_absProduct_01 {n : Nat}
    (W : Fin n -> Fin 2 -> Real) (Ls : Fin n -> Fin n -> Real)
    (E : Fin 2 -> Fin 2 -> Real) (Ds : Fin n -> Fin n -> Real) :
    higham11_4_bunchKaufmanProductEntry (n + 2)
      (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
      0 (Fin.succ 0) = |E 0 1| := by
  simp only [higham11_4_bunchKaufmanProductEntry, sum_fin_add_two,
    higham11_2_blockTwoL_00, higham11_2_blockTwoL_01,
    higham11_2_blockTwoL_10, higham11_2_blockTwoL_11,
    higham11_2_blockTwoL_0t, higham11_2_blockTwoL_1t,
    higham11_2_blockTwoD_00, higham11_2_blockTwoD_01,
    higham11_2_blockTwoD_0t, abs_zero, abs_one, zero_mul, mul_zero,
    one_mul, mul_one, add_zero, zero_add, Finset.sum_const_zero]

private theorem blockTwo_absProduct_10 {n : Nat}
    (W : Fin n -> Fin 2 -> Real) (Ls : Fin n -> Fin n -> Real)
    (E : Fin 2 -> Fin 2 -> Real) (Ds : Fin n -> Fin n -> Real) :
    higham11_4_bunchKaufmanProductEntry (n + 2)
      (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
      (Fin.succ 0) 0 = |E 1 0| := by
  simp only [higham11_4_bunchKaufmanProductEntry, sum_fin_add_two,
    higham11_2_blockTwoL_00, higham11_2_blockTwoL_01,
    higham11_2_blockTwoL_10, higham11_2_blockTwoL_11,
    higham11_2_blockTwoL_0t, higham11_2_blockTwoL_1t,
    higham11_2_blockTwoD_10, higham11_2_blockTwoD_11,
    higham11_2_blockTwoD_1t, abs_zero, abs_one, zero_mul, mul_zero,
    one_mul, mul_one, add_zero, zero_add, Finset.sum_const_zero]

private theorem blockTwo_absProduct_11 {n : Nat}
    (W : Fin n -> Fin 2 -> Real) (Ls : Fin n -> Fin n -> Real)
    (E : Fin 2 -> Fin 2 -> Real) (Ds : Fin n -> Fin n -> Real) :
    higham11_4_bunchKaufmanProductEntry (n + 2)
      (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
      (Fin.succ 0) (Fin.succ 0) = |E 1 1| := by
  simp only [higham11_4_bunchKaufmanProductEntry, sum_fin_add_two,
    higham11_2_blockTwoL_10, higham11_2_blockTwoL_11,
    higham11_2_blockTwoL_1t, higham11_2_blockTwoD_10,
    higham11_2_blockTwoD_11, higham11_2_blockTwoD_1t,
    abs_zero, abs_one, zero_mul, mul_zero, one_mul, mul_one,
    add_zero, zero_add, Finset.sum_const_zero]

private theorem blockTwo_absProduct_pp {n : Nat}
    (W : Fin n -> Fin 2 -> Real) (Ls : Fin n -> Fin n -> Real)
    (E : Fin 2 -> Fin 2 -> Real) (Ds : Fin n -> Fin n -> Real)
    (p q : Fin 2) :
    higham11_4_bunchKaufmanProductEntry (n + 2)
      (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
      (embedTwo n p) (embedTwo n q) = |E p q| := by
  fin_cases p <;> fin_cases q
  · simpa [embedTwo] using blockTwo_absProduct_00 W Ls E Ds
  · simpa [embedTwo] using blockTwo_absProduct_01 W Ls E Ds
  · simpa [embedTwo] using blockTwo_absProduct_10 W Ls E Ds
  · simpa [embedTwo] using blockTwo_absProduct_11 W Ls E Ds

private theorem blockTwo_absProduct_pt {n : Nat}
    (W : Fin n -> Fin 2 -> Real) (Ls : Fin n -> Fin n -> Real)
    (E : Fin 2 -> Fin 2 -> Real) (Ds : Fin n -> Fin n -> Real)
    (p : Fin 2) (j : Fin n) :
    higham11_4_bunchKaufmanProductEntry (n + 2)
      (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
      (embedTwo n p) j.succ.succ =
        ∑ q : Fin 2, |E p q| * |W j q| := by
  fin_cases p
  · simpa [embedTwo] using
      higham11_2_blockTwo_absProduct_0t' W Ls E Ds j
  · simpa [embedTwo] using
      higham11_2_blockTwo_absProduct_1t' W Ls E Ds j

private theorem blockTwo_absProduct_tp {n : Nat}
    (W : Fin n -> Fin 2 -> Real) (Ls : Fin n -> Fin n -> Real)
    (E : Fin 2 -> Fin 2 -> Real) (Ds : Fin n -> Fin n -> Real)
    (i : Fin n) (q : Fin 2) :
    higham11_4_bunchKaufmanProductEntry (n + 2)
      (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
      i.succ.succ (embedTwo n q) =
        ∑ p : Fin 2, |W i p| * |E p q| := by
  fin_cases q
  · simpa [embedTwo] using
      higham11_2_blockTwo_absProduct_t0' W Ls E Ds i
  · simpa [embedTwo] using
      higham11_2_blockTwo_absProduct_t1' W Ls E Ds i

private theorem blockOne_global_budget_thirtySix {n : Nat}
    (w : Fin n -> Real) (Ls : Fin n -> Fin n -> Real)
    (d : Real) (Ds : Fin n -> Fin n -> Real) (M : Real)
    (hM : 0 <= M) (h00 : |d| <= M)
    (hcross : forall i : Fin n, |d| * |w i| <= 2 * M)
    (htrail : forall i j : Fin n,
      higham11_4_bunchKaufmanProductEntry (n + 1)
        (higham11_2_blockOneL w Ls) (higham11_2_blockOneD d Ds)
        i.succ j.succ <= 8 * M + 36 * (n : Real) * M) :
    forall I J : Fin (n + 1),
      higham11_4_bunchKaufmanProductEntry (n + 1)
        (higham11_2_blockOneL w Ls) (higham11_2_blockOneD d Ds) I J <=
          36 * (n + 1 : Nat) * M := by
  have hhead : M <= 36 * (n + 1 : Nat) * M := by
    have hc : (1 : Real) <= 36 * (n + 1 : Nat) := by
      norm_num [Nat.cast_add, Nat.cast_one]
      nlinarith
    simpa using mul_le_mul_of_nonneg_right hc hM
  have hcrossBudget : 2 * M <= 36 * (n + 1 : Nat) * M := by
    have hc : (2 : Real) <= 36 * (n + 1 : Nat) := by
      norm_num [Nat.cast_add, Nat.cast_one]
      nlinarith
    exact mul_le_mul_of_nonneg_right hc hM
  have htrailBudget :
      8 * M + 36 * (n : Real) * M <= 36 * (n + 1 : Nat) * M := by
    norm_num [Nat.cast_add, Nat.cast_one]
    nlinarith
  intro I J
  refine Fin.cases ?_ (fun i => ?_) I
  · refine Fin.cases ?_ (fun j => ?_) J
    · rw [blockOne_absProduct_00]
      exact h00.trans hhead
    · rw [blockOne_absProduct_0s]
      exact (hcross j).trans hcrossBudget
  · refine Fin.cases ?_ (fun j => ?_) J
    · rw [blockOne_absProduct_s0]
      rw [mul_comm]
      exact (hcross i).trans hcrossBudget
    · exact (htrail i j).trans htrailBudget

private theorem blockTwo_global_budget_thirtySix {n : Nat}
    (W : Fin n -> Fin 2 -> Real) (Ls : Fin n -> Fin n -> Real)
    (E : Fin 2 -> Fin 2 -> Real) (Ds : Fin n -> Fin n -> Real)
    (M : Real) (hM : 0 <= M)
    (hpp : forall p q : Fin 2,
      higham11_4_bunchKaufmanProductEntry (n + 2)
        (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
        (embedTwo n p) (embedTwo n q) <= M)
    (hpt : forall (p : Fin 2) (j : Fin n),
      higham11_4_bunchKaufmanProductEntry (n + 2)
        (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
        (embedTwo n p) j.succ.succ <= 6 * M)
    (htp : forall (i : Fin n) (q : Fin 2),
      higham11_4_bunchKaufmanProductEntry (n + 2)
        (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
        i.succ.succ (embedTwo n q) <= 6 * M)
    (htt : forall i j : Fin n,
      higham11_4_bunchKaufmanProductEntry (n + 2)
        (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
        i.succ.succ j.succ.succ <= 33 * M + 36 * (n : Real) * M) :
    forall I J : Fin (n + 2),
      higham11_4_bunchKaufmanProductEntry (n + 2)
        (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds) I J <=
          36 * (n + 2 : Nat) * M := by
  have hppBudget : M <= 36 * (n + 2 : Nat) * M := by
    have hc : (1 : Real) <= 36 * (n + 2 : Nat) := by
      norm_num [Nat.cast_add, Nat.cast_ofNat]
      nlinarith
    simpa using mul_le_mul_of_nonneg_right hc hM
  have hptBudget : 6 * M <= 36 * (n + 2 : Nat) * M := by
    have hc : (6 : Real) <= 36 * (n + 2 : Nat) := by
      norm_num [Nat.cast_add, Nat.cast_ofNat]
      nlinarith
    exact mul_le_mul_of_nonneg_right hc hM
  have httBudget :
      33 * M + 36 * (n : Real) * M <= 36 * (n + 2 : Nat) * M := by
    norm_num [Nat.cast_add, Nat.cast_ofNat]
    nlinarith
  intro I J
  refine Fin.cases ?_ (fun K => ?_) I
  · refine Fin.cases ?_ (fun L => ?_) J
    · simpa [embedTwo] using (hpp (0 : Fin 2) 0).trans hppBudget
    · refine Fin.cases ?_ (fun j => ?_) L
      · simpa [embedTwo] using (hpp (0 : Fin 2) 1).trans hppBudget
      · simpa [embedTwo] using (hpt (0 : Fin 2) j).trans hptBudget
  · refine Fin.cases ?_ (fun L => ?_) J
    · refine Fin.cases ?_ (fun i => ?_) K
      · simpa [embedTwo] using (hpp (1 : Fin 2) 0).trans hppBudget
      · simpa [embedTwo] using (htp i (0 : Fin 2)).trans hptBudget
    · refine Fin.cases ?_ (fun j => ?_) L
      · refine Fin.cases ?_ (fun i => ?_) K
        · simpa [embedTwo] using (hpp (1 : Fin 2) 1).trans hppBudget
        · simpa [embedTwo] using (htp i (1 : Fin 2)).trans hptBudget
      · refine Fin.cases ?_ (fun i => ?_) K
        · simpa [embedTwo] using (hpt (1 : Fin 2) j).trans hptBudget
        · exact (htt i j).trans httBudget

namespace Higham11RoundedBunchKaufmanExecution

/-- File-private structural induction used only to derive the exact-arithmetic
source theorem below.  It is deliberately not part of the public rounded API.
No global growth or factor-product inequality is a premise. -/
private theorem flatAbsProduct_le_thirtySix_dimension_stageMax
    (fp : FPModel) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2)
    (hu : fp.u <= 1) (huSmall : 36 * fp.u <= (1 : Real) / 1000) :
    forall {n : Nat} {A : Higham11RoundedBunchKaufmanMatrix n}
      (exec : Higham11RoundedBunchKaufmanExecution fp A),
      exec.Completed -> forall i j : Fin n,
        exec.flatAbsProduct i j <= 36 * (n : Real) * exec.roundedStageMax := by
  intro n A exec
  induction exec with
  | nil A =>
      intro _ i
      exact Fin.elim0 i
  | @noAction n A hA hbranch tail ih =>
      intro hcompleted
      let M := (Higham11RoundedBunchKaufmanExecution.noAction
        A hA hbranch tail).roundedStageMax
      have hM : 0 <= M := roundedStageMax_nonneg _
      have hcurrent : higham11_4_roundedActiveMax A <= M :=
        currentMax_le_roundedStageMax _
      have hA00 : |A 0 0| <= M :=
        (higham11_4_entry_le_roundedActiveMax A 0 0).trans hcurrent
      have htailM : tail.roundedStageMax <= M :=
        tail_roundedStageMax_le_noAction A hA hbranch tail
      have htail : forall i j : Fin n,
          tail.flatAbsProduct i j <= 36 * (n : Real) * M := by
        intro i j
        exact (ih hcompleted i j).trans
          (mul_le_mul_of_nonneg_left htailM
            (mul_nonneg (by norm_num) (Nat.cast_nonneg n)))
      intro I J
      change
        higham11_4_bunchKaufmanProductEntry (n + 1)
          (higham11_2_blockOneL (fun _ => 0) tail.flatL)
          (higham11_2_blockOneD (A 0 0) tail.flatD) I J <=
            36 * ((n + 1 : Nat) : Real) * M
      apply blockOne_global_budget_thirtySix
        (fun _ : Fin n => 0) tail.flatL (A 0 0) tail.flatD M hM hA00
      · intro i
        simp [hM]
      · intro i j
        rw [higham11_2_blockOne_absProduct_ss']
        simpa [flatAbsProduct] using
          (htail i j).trans (le_add_of_nonneg_left
            (mul_nonneg (by norm_num) hM))
  | @case1 n A hA hbranch tail ih =>
      intro hcompleted
      let exec := Higham11RoundedBunchKaufmanExecution.case1
        A hA hbranch tail
      let M := exec.roundedStageMax
      have hM : 0 <= M := roundedStageMax_nonneg exec
      have hcurrent : higham11_4_roundedActiveMax A <= M :=
        currentMax_le_roundedStageMax exec
      have htailM : tail.roundedStageMax <= M :=
        tail_roundedStageMax_le_case1 A hA hbranch tail
      intro I J
      change
        higham11_4_bunchKaufmanProductEntry (n + 2)
          (higham11_2_blockOneL
            (fun k => higham11_2_bunchKaufmanFlMultOne fp A
              (tail.permutation k)) tail.flatL)
          (higham11_2_blockOneD
            (higham11_2_bunchKaufmanRoundedActive A 0 0) tail.flatD) I J <=
          36 * ((n + 2 : Nat) : Real) * M
      apply blockOne_global_budget_thirtySix
      · exact hM
      · exact (higham11_4_roundedActive_entry_le_currentMax A 0 0).trans hcurrent
      · intro i
        exact (higham11_4_scalar_pivot_cross_le_two fp A hA
          (roundedActive_pivot_ne_zero_case1 A hbranch) hu
          (tail.permutation i)).trans
          (mul_le_mul_of_nonneg_left hcurrent (by norm_num))
      · intro i j
        rw [higham11_2_blockOne_absProduct_ss']
        change higham11_2_bunchKaufmanPivotPathOneAbs fp A
            (tail.permutation i) (tail.permutation j) +
          tail.flatAbsProduct i j <= _
        apply add_le_add
        · exact (higham11_4_pivotPathOneAbs_le_eight_case1 fp A hbranch
            (tail.permutation i) (tail.permutation j) hu).trans
            (mul_le_mul_of_nonneg_left hcurrent (by norm_num))
        · exact (ih hcompleted i j).trans
            (mul_le_mul_of_nonneg_left htailM
              (mul_nonneg (by norm_num) (Nat.cast_nonneg (n + 1))))
  | @case2 n A hA hbranch tail ih =>
      intro hcompleted
      let exec := Higham11RoundedBunchKaufmanExecution.case2
        A hA hbranch tail
      let M := exec.roundedStageMax
      have hM : 0 <= M := roundedStageMax_nonneg exec
      have hcurrent : higham11_4_roundedActiveMax A <= M :=
        currentMax_le_roundedStageMax exec
      have htailM : tail.roundedStageMax <= M :=
        tail_roundedStageMax_le_case2 A hA hbranch tail
      intro I J
      change
        higham11_4_bunchKaufmanProductEntry (n + 2)
          (higham11_2_blockOneL
            (fun k => higham11_2_bunchKaufmanFlMultOne fp A
              (tail.permutation k)) tail.flatL)
          (higham11_2_blockOneD
            (higham11_2_bunchKaufmanRoundedActive A 0 0) tail.flatD) I J <=
          36 * ((n + 2 : Nat) : Real) * M
      apply blockOne_global_budget_thirtySix
      · exact hM
      · exact (higham11_4_roundedActive_entry_le_currentMax A 0 0).trans hcurrent
      · intro i
        exact (higham11_4_scalar_pivot_cross_le_two fp A hA
          (roundedActive_pivot_ne_zero_case2 A hbranch) hu
          (tail.permutation i)).trans
          (mul_le_mul_of_nonneg_left hcurrent (by norm_num))
      · intro i j
        rw [higham11_2_blockOne_absProduct_ss']
        change higham11_2_bunchKaufmanPivotPathOneAbs fp A
            (tail.permutation i) (tail.permutation j) +
          tail.flatAbsProduct i j <= _
        apply add_le_add
        · exact (higham11_4_pivotPathOneAbs_le_eight_case2 fp A hbranch
            (tail.permutation i) (tail.permutation j) hu).trans
            (mul_le_mul_of_nonneg_left hcurrent (by norm_num))
        · exact (ih hcompleted i j).trans
            (mul_le_mul_of_nonneg_left htailM
              (mul_nonneg (by norm_num) (Nat.cast_nonneg (n + 1))))
  | @case3 n A hA hbranch tail ih =>
      intro hcompleted
      let exec := Higham11RoundedBunchKaufmanExecution.case3
        A hA hbranch tail
      let M := exec.roundedStageMax
      have hM : 0 <= M := roundedStageMax_nonneg exec
      have hcurrent : higham11_4_roundedActiveMax A <= M :=
        currentMax_le_roundedStageMax exec
      have htailM : tail.roundedStageMax <= M :=
        tail_roundedStageMax_le_case3 A hA hbranch tail
      intro I J
      change
        higham11_4_bunchKaufmanProductEntry (n + 2)
          (higham11_2_blockOneL
            (fun k => higham11_2_bunchKaufmanFlMultOne fp A
              (tail.permutation k)) tail.flatL)
          (higham11_2_blockOneD
            (higham11_2_bunchKaufmanRoundedActive A 0 0) tail.flatD) I J <=
          36 * ((n + 2 : Nat) : Real) * M
      apply blockOne_global_budget_thirtySix
      · exact hM
      · exact (higham11_4_roundedActive_entry_le_currentMax A 0 0).trans hcurrent
      · intro i
        exact (higham11_4_scalar_pivot_cross_le_two fp A hA
          (roundedActive_pivot_ne_zero_case3 A hA hbranch) hu
          (tail.permutation i)).trans
          (mul_le_mul_of_nonneg_left hcurrent (by norm_num))
      · intro i j
        rw [higham11_2_blockOne_absProduct_ss']
        change higham11_2_bunchKaufmanPivotPathOneAbs fp A
            (tail.permutation i) (tail.permutation j) +
          tail.flatAbsProduct i j <= _
        apply add_le_add
        · exact (higham11_4_pivotPathOneAbs_le_eight_case3 fp A hA hbranch
            (tail.permutation i) (tail.permutation j) hu).trans
            (mul_le_mul_of_nonneg_left hcurrent (by norm_num))
        · exact (ih hcompleted i j).trans
            (mul_le_mul_of_nonneg_left htailM
              (mul_nonneg (by norm_num) (Nat.cast_nonneg (n + 1))))
  | @case4 n A hA hbranch hsecond tail ih =>
      intro hcompleted
      let exec := Higham11RoundedBunchKaufmanExecution.case4
        A hA hbranch hsecond tail
      let M := exec.roundedStageMax
      have hM : 0 <= M := roundedStageMax_nonneg exec
      have hcurrent : higham11_4_roundedActiveMax A <= M :=
        currentMax_le_roundedStageMax exec
      have htailM : tail.roundedStageMax <= M :=
        tail_roundedStageMax_le_case4 A hA hbranch hsecond tail
      intro I J
      change
        higham11_4_bunchKaufmanProductEntry (n + 2)
          (higham11_2_blockTwoL
            (fun k p => higham11_2_bunchKaufmanFlMultTwo fp A
              (tail.permutation k) p) tail.flatL)
          (higham11_2_blockTwoD
            (fun p q => higham11_2_bunchKaufmanRoundedActive A
              (embedTwo n p) (embedTwo n q)) tail.flatD) I J <=
          36 * ((n + 2 : Nat) : Real) * M
      apply blockTwo_global_budget_thirtySix
      · exact hM
      · intro p q
        rw [blockTwo_absProduct_pp]
        exact (higham11_4_roundedActive_entry_le_currentMax A
          (embedTwo n p) (embedTwo n q)).trans hcurrent
      · intro p j
        rw [blockTwo_absProduct_pt]
        change higham11_2_bunchKaufmanPivotRowTwoAbs fp A
          p (tail.permutation j) <= 6 * M
        exact (higham11_4_pivotRowTwoAbs_le_six_case4 fp hval9 hsmall9
          A hA hbranch hsecond huSmall p (tail.permutation j)).trans
          (mul_le_mul_of_nonneg_left hcurrent (by norm_num))
      · intro i q
        rw [blockTwo_absProduct_tp]
        change higham11_2_bunchKaufmanPivotColTwoAbs fp A
          (tail.permutation i) q <= 6 * M
        exact (higham11_4_pivotColTwoAbs_le_six_case4 fp hval9 hsmall9
          A hA hbranch hsecond huSmall (tail.permutation i) q).trans
          (mul_le_mul_of_nonneg_left hcurrent (by norm_num))
      · intro i j
        rw [higham11_2_blockTwo_absProduct_tt']
        change higham11_2_bunchKaufmanPivotPathTwoAbs fp A
            (tail.permutation i) (tail.permutation j) +
          tail.flatAbsProduct i j <= _
        apply add_le_add
        · exact (higham11_4_pivotPathTwoAbs_le_thirtyThree_case4
            fp hval9 hsmall9 A hA hbranch hsecond huSmall
            (tail.permutation i) (tail.permutation j)).trans
            (mul_le_mul_of_nonneg_left hcurrent (by norm_num))
        · exact (ih hcompleted i j).trans
            (mul_le_mul_of_nonneg_left htailM
              (mul_nonneg (by norm_num) (Nat.cast_nonneg n)))
  | case4Breakdown A hA hbranch hsecond =>
      intro hcompleted
      exact False.elim hcompleted

/-- **Independent finite-precision strengthening of Higham's exact `36 n`
bound.**  For a completed literal rounded Algorithm 11.2 execution, the
computed factors satisfy the same numerical constant when the displayed
small-unit-roundoff assumptions hold.

Unlike the exact source theorem below, this statement measures growth using
the rounded active matrices actually visited.  Higham [1997, §4.3] does not
state this strengthened finite-`u` result; it follows here from the proved
finite-precision local caps and their strict slack below `36`. -/
theorem flatAbsProduct_le_thirtySix_dimension_stageMax_rounded
    (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2)
    (huSmall : 36 * fp.u <= (1 : Real) / 1000)
    {n : Nat} {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (hcompleted : exec.Completed) (i j : Fin n) :
    exec.flatAbsProduct i j <=
      36 * (n : Real) * exec.roundedStageMax := by
  have hu : fp.u <= 1 := by
    nlinarith [fp.u_nonneg]
  exact flatAbsProduct_le_thirtySix_dimension_stageMax
    fp hval9 hsmall9 hu huSmall exec hcompleted i j

/-- The rounded `36 n` strengthening normalized by the growth factor of the
actual rounded path at a positive input scale. -/
theorem flatAbsProduct_le_thirtySix_mul_dimension_mul_roundedGrowthFactor
    (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2)
    (huSmall : 36 * fp.u <= (1 : Real) / 1000)
    {n : Nat} {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (hcompleted : exec.Completed) {Amax : Real} (hAmax : 0 < Amax)
    (i j : Fin n) :
    exec.flatAbsProduct i j <=
      36 * (n : Real) * exec.roundedGrowthFactor Amax * Amax := by
  calc
    exec.flatAbsProduct i j <=
        36 * (n : Real) * exec.roundedStageMax :=
      flatAbsProduct_le_thirtySix_dimension_stageMax_rounded
        hval9 hsmall9 huSmall exec hcompleted i j
    _ = 36 * (n : Real) * exec.roundedGrowthFactor Amax * Amax := by
      rw [roundedStageMax_eq_growthFactor_mul exec hAmax]
      ring

/-- Exact coordinate transport of the rounded `36 n` estimate back from final
pivot order to the original source indices. -/
theorem sourceCoordinateFlatAbsProduct_le_thirtySix_mul_dimension_mul_roundedGrowthFactor
    (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2)
    (huSmall : 36 * fp.u <= (1 : Real) / 1000)
    {n : Nat} {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (hcompleted : exec.Completed) {Amax : Real} (hAmax : 0 < Amax)
    (i j : Fin n) :
    exec.flatAbsProduct (exec.permutation.symm i) (exec.permutation.symm j) <=
      36 * (n : Real) * exec.roundedGrowthFactor Amax * Amax := by
  exact flatAbsProduct_le_thirtySix_mul_dimension_mul_roundedGrowthFactor
    hval9 hsmall9 huSmall exec hcompleted hAmax
      (exec.permutation.symm i) (exec.permutation.symm j)

/-- Max-entry packaging of the independent rounded `36 n` strengthening.
Here `rho_n` is definitionally the rounded-path stage maximum divided by the
positive scale `Amax`; it is not the exact-arithmetic growth factor. -/
theorem rounded_maxEntryProductBound_thirtySix
    (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2)
    (huSmall : 36 * fp.u <= (1 : Real) / 1000)
    {n : Nat} (hn : 0 < n)
    {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (hcompleted : exec.Completed) {Amax : Real} (hAmax : 0 < Amax) :
    higham11_4_bunchKaufmanMaxEntryProductBound n
      (higham11_4_bunchKaufmanProductMax n hn exec.flatL exec.flatD)
      (exec.roundedGrowthFactor Amax) Amax := by
  apply higham11_4_bunchKaufmanMaxEntryProductBound_of_product_entries
  intro i j
  simpa [flatAbsProduct] using
    flatAbsProduct_le_thirtySix_mul_dimension_mul_roundedGrowthFactor
      hval9 hsmall9 huSmall exec hcompleted hAmax i j

/-- Exact-arithmetic form of the source entrywise estimate.  Completion is
not a premise: exact Algorithm 11.2 cannot reach the explicit GEPP breakdown
constructor. -/
theorem flatAbsProduct_le_thirtySix_dimension_stageMax_exactArithmetic
    {n : Nat} {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution
      higham11_2_bunchKaufmanExactArithmeticFP A) (i j : Fin n) :
    exec.flatAbsProduct i j <= 36 * (n : Real) * exec.roundedStageMax := by
  exact flatAbsProduct_le_thirtySix_dimension_stageMax
    higham11_2_bunchKaufmanExactArithmeticFP
    (by norm_num [gammaValid, higham11_2_bunchKaufmanExactArithmeticFP,
      FPModel.exactWithUnitRoundoff])
    (by norm_num [higham11_2_bunchKaufmanExactArithmeticFP,
      FPModel.exactWithUnitRoundoff])
    (by norm_num [higham11_2_bunchKaufmanExactArithmeticFP,
      FPModel.exactWithUnitRoundoff])
    (by norm_num [higham11_2_bunchKaufmanExactArithmeticFP,
      FPModel.exactWithUnitRoundoff])
    exec (completed_exactArithmetic exec) i j

/-- Source-facing exact Theorem 11.4 product bound for an honest growth-factor
certificate `stageMax = rho_n * Amax`.  The factors are flattened from the
literal Algorithm 11.2 producer; no product-entry or target-shaped growth
inequality is assumed. -/
theorem exactArithmetic_maxEntryProductBound_of_stageMax_eq
    {n : Nat} (hn : 0 < n)
    {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution
      higham11_2_bunchKaufmanExactArithmeticFP A)
    (rho_n Amax : Real)
    (hgrowth : exec.roundedStageMax = rho_n * Amax) :
    higham11_4_bunchKaufmanMaxEntryProductBound n
      (higham11_4_bunchKaufmanProductMax n hn exec.flatL exec.flatD)
      rho_n Amax := by
  apply higham11_4_bunchKaufmanMaxEntryProductBound_of_product_entries
  intro i j
  have hproduct :=
    flatAbsProduct_le_thirtySix_dimension_stageMax_exactArithmetic exec i j
  rw [hgrowth] at hproduct
  simpa [flatAbsProduct, mul_assoc] using hproduct

/-- The exact source bound with `rho_n` defined as the maximum entry over all
visited exact active matrices divided by the nonzero input scale. -/
theorem exactArithmetic_maxEntryProductBound
    {n : Nat} (hn : 0 < n)
    {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution
      higham11_2_bunchKaufmanExactArithmeticFP A)
    {Amax : Real} (hAmax : 0 < Amax) :
    higham11_4_bunchKaufmanMaxEntryProductBound n
      (higham11_4_bunchKaufmanProductMax n hn exec.flatL exec.flatD)
      (exec.roundedGrowthFactor Amax) Amax := by
  apply exactArithmetic_maxEntryProductBound_of_stageMax_eq
  exact roundedStageMax_eq_growthFactor_mul exec hAmax

end Higham11RoundedBunchKaufmanExecution

/-- **Higham [1997], Section 4.3 exact Bunch--Kaufman growth theorem.**
For the canonical literal Algorithm 11.2 producer in exact arithmetic,

`|| |L| |D| |L^T| ||_M <= 36 n rho_n ||A||_M`,

where `rho_n` is computed from the maximum entry of the actual exact active
matrices visited by the producer. -/
theorem higham11_4_exactArithmeticBunchKaufmanMaxEntryNorm_productBound
    {n : Nat} (hn : 0 < n)
    (A : Higham11RoundedBunchKaufmanMatrix n)
    (hA : IsSymmetricFiniteMatrix A)
    (hAmax : 0 < maxEntryNorm hn A) :
    let exec := higham11_2_exactArithmeticBunchKaufmanExecution A hA
    higham11_4_bunchKaufmanMaxEntryProductBound n
      (higham11_4_bunchKaufmanProductMax n hn exec.flatL exec.flatD)
      (exec.roundedGrowthFactor (maxEntryNorm hn A))
      (maxEntryNorm hn A) := by
  dsimp only
  exact
    Higham11RoundedBunchKaufmanExecution.exactArithmetic_maxEntryProductBound
      hn (higham11_2_exactArithmeticBunchKaufmanExecution A hA) hAmax

end NumStability
