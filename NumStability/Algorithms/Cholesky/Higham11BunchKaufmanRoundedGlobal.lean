/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# Global residual for the literal rounded Bunch--Kaufman execution
-/

import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedAccumulated

open scoped BigOperators

namespace NumStability

open Ch11Closure.Mixed

namespace Higham11RoundedBunchKaufmanExecution

theorem flatProduct_noAction_00 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 1)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanNoActionTail A)) :
    (Higham11RoundedBunchKaufmanExecution.noAction A hA hbranch tail).flatProduct 0 0 =
      A 0 0 := by
  change higham11_2_ldltProduct
      (higham11_2_blockOneL (fun _ => 0) tail.flatL)
      (higham11_2_blockOneD (A 0 0) tail.flatD) 0 0 = _
  exact higham11_2_blockOne_product_00 _ _ _ _

theorem flatProduct_noAction_0s (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 1)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanNoActionTail A)) (j : Fin n) :
    (Higham11RoundedBunchKaufmanExecution.noAction A hA hbranch tail).flatProduct
      0 j.succ = 0 := by
  change higham11_2_ldltProduct
      (higham11_2_blockOneL (fun _ => 0) tail.flatL)
      (higham11_2_blockOneD (A 0 0) tail.flatD) 0 j.succ = _
  rw [higham11_2_blockOne_product_0s]
  ring

theorem flatProduct_noAction_s0 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 1)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanNoActionTail A)) (i : Fin n) :
    (Higham11RoundedBunchKaufmanExecution.noAction A hA hbranch tail).flatProduct
      i.succ 0 = 0 := by
  change higham11_2_ldltProduct
      (higham11_2_blockOneL (fun _ => 0) tail.flatL)
      (higham11_2_blockOneD (A 0 0) tail.flatD) i.succ 0 = _
  rw [higham11_2_blockOne_product_s0]
  ring

theorem flatProduct_noAction_ss (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 1)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanNoActionTail A)) (i j : Fin n) :
    (Higham11RoundedBunchKaufmanExecution.noAction A hA hbranch tail).flatProduct
      i.succ j.succ = tail.flatProduct i j := by
  change higham11_2_ldltProduct
      (higham11_2_blockOneL (fun _ => 0) tail.flatL)
      (higham11_2_blockOneD (A 0 0) tail.flatD) i.succ j.succ = _
  rw [higham11_2_blockOne_product_ss]
  simp [flatProduct, higham11_2_ldltProduct]

theorem flatProduct_case1_00 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) :
    (Higham11RoundedBunchKaufmanExecution.case1 A hA hbranch tail).flatProduct 0 0 =
      higham11_2_bunchKaufmanRoundedActive A 0 0 := by
  change higham11_2_ldltProduct
      (higham11_2_blockOneL
        (fun k => higham11_2_bunchKaufmanFlMultOne fp A
          (tail.permutation k)) tail.flatL)
      (higham11_2_blockOneD
        (higham11_2_bunchKaufmanRoundedActive A 0 0) tail.flatD) 0 0 = _
  exact higham11_2_blockOne_product_00 _ _ _ _

theorem flatProduct_case1_0s (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) (j : Fin (n + 1)) :
    (Higham11RoundedBunchKaufmanExecution.case1 A hA hbranch tail).flatProduct
        0 j.succ =
      higham11_2_bunchKaufmanRoundedActive A 0 0 *
        higham11_2_bunchKaufmanFlMultOne fp A (tail.permutation j) := by
  change higham11_2_ldltProduct
      (higham11_2_blockOneL
        (fun k => higham11_2_bunchKaufmanFlMultOne fp A
          (tail.permutation k)) tail.flatL)
      (higham11_2_blockOneD
        (higham11_2_bunchKaufmanRoundedActive A 0 0) tail.flatD)
      0 j.succ = _
  exact higham11_2_blockOne_product_0s _ _ _ _ _

theorem flatProduct_case1_s0 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) (i : Fin (n + 1)) :
    (Higham11RoundedBunchKaufmanExecution.case1 A hA hbranch tail).flatProduct
        i.succ 0 =
      higham11_2_bunchKaufmanFlMultOne fp A (tail.permutation i) *
        higham11_2_bunchKaufmanRoundedActive A 0 0 := by
  change higham11_2_ldltProduct
      (higham11_2_blockOneL
        (fun k => higham11_2_bunchKaufmanFlMultOne fp A
          (tail.permutation k)) tail.flatL)
      (higham11_2_blockOneD
        (higham11_2_bunchKaufmanRoundedActive A 0 0) tail.flatD)
      i.succ 0 = _
  exact higham11_2_blockOne_product_s0 _ _ _ _ _

theorem flatProduct_case2_00 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) :
    (Higham11RoundedBunchKaufmanExecution.case2 A hA hbranch tail).flatProduct 0 0 =
      higham11_2_bunchKaufmanRoundedActive A 0 0 := by
  change higham11_2_ldltProduct
      (higham11_2_blockOneL
        (fun k => higham11_2_bunchKaufmanFlMultOne fp A
          (tail.permutation k)) tail.flatL)
      (higham11_2_blockOneD
        (higham11_2_bunchKaufmanRoundedActive A 0 0) tail.flatD) 0 0 = _
  exact higham11_2_blockOne_product_00 _ _ _ _

theorem flatProduct_case2_0s (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) (j : Fin (n + 1)) :
    (Higham11RoundedBunchKaufmanExecution.case2 A hA hbranch tail).flatProduct
        0 j.succ =
      higham11_2_bunchKaufmanRoundedActive A 0 0 *
        higham11_2_bunchKaufmanFlMultOne fp A (tail.permutation j) := by
  change higham11_2_ldltProduct
      (higham11_2_blockOneL
        (fun k => higham11_2_bunchKaufmanFlMultOne fp A
          (tail.permutation k)) tail.flatL)
      (higham11_2_blockOneD
        (higham11_2_bunchKaufmanRoundedActive A 0 0) tail.flatD)
      0 j.succ = _
  exact higham11_2_blockOne_product_0s _ _ _ _ _

theorem flatProduct_case2_s0 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) (i : Fin (n + 1)) :
    (Higham11RoundedBunchKaufmanExecution.case2 A hA hbranch tail).flatProduct
        i.succ 0 =
      higham11_2_bunchKaufmanFlMultOne fp A (tail.permutation i) *
        higham11_2_bunchKaufmanRoundedActive A 0 0 := by
  change higham11_2_ldltProduct
      (higham11_2_blockOneL
        (fun k => higham11_2_bunchKaufmanFlMultOne fp A
          (tail.permutation k)) tail.flatL)
      (higham11_2_blockOneD
        (higham11_2_bunchKaufmanRoundedActive A 0 0) tail.flatD)
      i.succ 0 = _
  exact higham11_2_blockOne_product_s0 _ _ _ _ _

theorem flatProduct_case3_00 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) :
    (Higham11RoundedBunchKaufmanExecution.case3 A hA hbranch tail).flatProduct 0 0 =
      higham11_2_bunchKaufmanRoundedActive A 0 0 := by
  change higham11_2_ldltProduct
      (higham11_2_blockOneL
        (fun k => higham11_2_bunchKaufmanFlMultOne fp A
          (tail.permutation k)) tail.flatL)
      (higham11_2_blockOneD
        (higham11_2_bunchKaufmanRoundedActive A 0 0) tail.flatD) 0 0 = _
  exact higham11_2_blockOne_product_00 _ _ _ _

theorem flatProduct_case3_0s (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) (j : Fin (n + 1)) :
    (Higham11RoundedBunchKaufmanExecution.case3 A hA hbranch tail).flatProduct
        0 j.succ =
      higham11_2_bunchKaufmanRoundedActive A 0 0 *
        higham11_2_bunchKaufmanFlMultOne fp A (tail.permutation j) := by
  change higham11_2_ldltProduct
      (higham11_2_blockOneL
        (fun k => higham11_2_bunchKaufmanFlMultOne fp A
          (tail.permutation k)) tail.flatL)
      (higham11_2_blockOneD
        (higham11_2_bunchKaufmanRoundedActive A 0 0) tail.flatD)
      0 j.succ = _
  exact higham11_2_blockOne_product_0s _ _ _ _ _

theorem flatProduct_case3_s0 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) (i : Fin (n + 1)) :
    (Higham11RoundedBunchKaufmanExecution.case3 A hA hbranch tail).flatProduct
        i.succ 0 =
      higham11_2_bunchKaufmanFlMultOne fp A (tail.permutation i) *
        higham11_2_bunchKaufmanRoundedActive A 0 0 := by
  change higham11_2_ldltProduct
      (higham11_2_blockOneL
        (fun k => higham11_2_bunchKaufmanFlMultOne fp A
          (tail.permutation k)) tail.flatL)
      (higham11_2_blockOneD
        (higham11_2_bunchKaufmanRoundedActive A 0 0) tail.flatD)
      i.succ 0 = _
  exact higham11_2_blockOne_product_s0 _ _ _ _ _

theorem flatProduct_case1_tt (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) (i j : Fin (n + 1)) :
    let exec := Higham11RoundedBunchKaufmanExecution.case1 A hA hbranch tail
    exec.flatProduct i.succ j.succ =
      higham11_2_bunchKaufmanPivotPathOne fp A
          (tail.permutation i) (tail.permutation j) +
        tail.flatProduct i j := by
  dsimp only
  change higham11_2_ldltProduct
      (higham11_2_blockOneL
        (fun k => higham11_2_bunchKaufmanFlMultOne fp A
          (tail.permutation k)) tail.flatL)
      (higham11_2_blockOneD
        (higham11_2_bunchKaufmanRoundedActive A 0 0) tail.flatD)
      i.succ j.succ = _
  rw [higham11_2_blockOne_product_ss]
  rfl

theorem flatProduct_case2_tt (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) (i j : Fin (n + 1)) :
    let exec := Higham11RoundedBunchKaufmanExecution.case2 A hA hbranch tail
    exec.flatProduct i.succ j.succ =
      higham11_2_bunchKaufmanPivotPathOne fp A
          (tail.permutation i) (tail.permutation j) +
        tail.flatProduct i j := by
  dsimp only
  change higham11_2_ldltProduct
      (higham11_2_blockOneL
        (fun k => higham11_2_bunchKaufmanFlMultOne fp A
          (tail.permutation k)) tail.flatL)
      (higham11_2_blockOneD
        (higham11_2_bunchKaufmanRoundedActive A 0 0) tail.flatD)
      i.succ j.succ = _
  rw [higham11_2_blockOne_product_ss]
  rfl

theorem flatProduct_case3_tt (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) (i j : Fin (n + 1)) :
    let exec := Higham11RoundedBunchKaufmanExecution.case3 A hA hbranch tail
    exec.flatProduct i.succ j.succ =
      higham11_2_bunchKaufmanPivotPathOne fp A
          (tail.permutation i) (tail.permutation j) +
        tail.flatProduct i j := by
  dsimp only
  change higham11_2_ldltProduct
      (higham11_2_blockOneL
        (fun k => higham11_2_bunchKaufmanFlMultOne fp A
          (tail.permutation k)) tail.flatL)
      (higham11_2_blockOneD
        (higham11_2_bunchKaufmanRoundedActive A 0 0) tail.flatD)
      i.succ j.succ = _
  rw [higham11_2_blockOne_product_ss]
  rfl

theorem flatProduct_case4_tt (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) (i j : Fin n) :
    let exec := Higham11RoundedBunchKaufmanExecution.case4
      A hA hbranch hsecond tail
    exec.flatProduct i.succ.succ j.succ.succ =
      higham11_2_bunchKaufmanPivotPathTwo fp A
          (tail.permutation i) (tail.permutation j) +
        tail.flatProduct i j := by
  dsimp only
  change higham11_2_ldltProduct
      (higham11_2_blockTwoL
        (fun k p => higham11_2_bunchKaufmanFlMultTwo fp A
          (tail.permutation k) p) tail.flatL)
      (higham11_2_blockTwoD
        (fun p q => higham11_2_bunchKaufmanRoundedActive A
          (embedTwo n p) (embedTwo n q)) tail.flatD)
      i.succ.succ j.succ.succ = _
  rw [higham11_2_blockTwo_product_tt]
  rfl

theorem flatProduct_case4_pp (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) (p q : Fin 2) :
    let exec := Higham11RoundedBunchKaufmanExecution.case4
      A hA hbranch hsecond tail
    exec.flatProduct (embedTwo n p) (embedTwo n q) =
      higham11_2_bunchKaufmanRoundedActive A
        (embedTwo n p) (embedTwo n q) := by
  dsimp only
  fin_cases p <;> fin_cases q
  · change higham11_2_ldltProduct
      (higham11_2_blockTwoL
        (fun k p => higham11_2_bunchKaufmanFlMultTwo fp A
          (tail.permutation k) p) tail.flatL)
      (higham11_2_blockTwoD
        (fun p q => higham11_2_bunchKaufmanRoundedActive A
          (embedTwo n p) (embedTwo n q)) tail.flatD) 0 0 = _
    exact higham11_2_blockTwo_product_00 _ _ _ _
  · change higham11_2_ldltProduct
      (higham11_2_blockTwoL
        (fun k p => higham11_2_bunchKaufmanFlMultTwo fp A
          (tail.permutation k) p) tail.flatL)
      (higham11_2_blockTwoD
        (fun p q => higham11_2_bunchKaufmanRoundedActive A
          (embedTwo n p) (embedTwo n q)) tail.flatD) 0 (Fin.succ 0) = _
    exact higham11_2_blockTwo_product_01 _ _ _ _
  · change higham11_2_ldltProduct
      (higham11_2_blockTwoL
        (fun k p => higham11_2_bunchKaufmanFlMultTwo fp A
          (tail.permutation k) p) tail.flatL)
      (higham11_2_blockTwoD
        (fun p q => higham11_2_bunchKaufmanRoundedActive A
          (embedTwo n p) (embedTwo n q)) tail.flatD) (Fin.succ 0) 0 = _
    exact higham11_2_blockTwo_product_10 _ _ _ _
  · change higham11_2_ldltProduct
      (higham11_2_blockTwoL
        (fun k p => higham11_2_bunchKaufmanFlMultTwo fp A
          (tail.permutation k) p) tail.flatL)
      (higham11_2_blockTwoD
        (fun p q => higham11_2_bunchKaufmanRoundedActive A
          (embedTwo n p) (embedTwo n q)) tail.flatD)
        (Fin.succ 0) (Fin.succ 0) = _
    exact higham11_2_blockTwo_product_11 _ _ _ _

theorem flatProduct_case4_pt (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) (p : Fin 2) (j : Fin n) :
    let exec := Higham11RoundedBunchKaufmanExecution.case4
      A hA hbranch hsecond tail
    exec.flatProduct (embedTwo n p) j.succ.succ =
      ∑ q : Fin 2, higham11_2_bunchKaufmanRoundedActive A
          (embedTwo n p) (embedTwo n q) *
        higham11_2_bunchKaufmanFlMultTwo fp A (tail.permutation j) q := by
  dsimp only
  fin_cases p
  · change higham11_2_ldltProduct
      (higham11_2_blockTwoL
        (fun k p => higham11_2_bunchKaufmanFlMultTwo fp A
          (tail.permutation k) p) tail.flatL)
      (higham11_2_blockTwoD
        (fun p q => higham11_2_bunchKaufmanRoundedActive A
          (embedTwo n p) (embedTwo n q)) tail.flatD) 0 j.succ.succ = _
    rw [higham11_2_blockTwo_product_0t, Fin.sum_univ_two]
    rfl
  · change higham11_2_ldltProduct
      (higham11_2_blockTwoL
        (fun k p => higham11_2_bunchKaufmanFlMultTwo fp A
          (tail.permutation k) p) tail.flatL)
      (higham11_2_blockTwoD
        (fun p q => higham11_2_bunchKaufmanRoundedActive A
          (embedTwo n p) (embedTwo n q)) tail.flatD)
        (Fin.succ 0) j.succ.succ = _
    rw [higham11_2_blockTwo_product_1t, Fin.sum_univ_two]
    rfl

theorem flatProduct_case4_tp (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) (i : Fin n) (q : Fin 2) :
    let exec := Higham11RoundedBunchKaufmanExecution.case4
      A hA hbranch hsecond tail
    exec.flatProduct i.succ.succ (embedTwo n q) =
      ∑ p : Fin 2, higham11_2_bunchKaufmanFlMultTwo fp A
          (tail.permutation i) p *
        higham11_2_bunchKaufmanRoundedActive A
          (embedTwo n p) (embedTwo n q) := by
  dsimp only
  fin_cases q
  · change higham11_2_ldltProduct
      (higham11_2_blockTwoL
        (fun k p => higham11_2_bunchKaufmanFlMultTwo fp A
          (tail.permutation k) p) tail.flatL)
      (higham11_2_blockTwoD
        (fun p q => higham11_2_bunchKaufmanRoundedActive A
          (embedTwo n p) (embedTwo n q)) tail.flatD) i.succ.succ 0 = _
    rw [higham11_2_blockTwo_product_t0, Fin.sum_univ_two]
    rfl
  · change higham11_2_ldltProduct
      (higham11_2_blockTwoL
        (fun k p => higham11_2_bunchKaufmanFlMultTwo fp A
          (tail.permutation k) p) tail.flatL)
      (higham11_2_blockTwoD
        (fun p q => higham11_2_bunchKaufmanRoundedActive A
          (embedTwo n p) (embedTwo n q)) tail.flatD)
        i.succ.succ (Fin.succ 0) = _
    rw [higham11_2_blockTwo_product_t1, Fin.sum_univ_two]
    rfl

theorem flatProduct_case4_00 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) :
    (Higham11RoundedBunchKaufmanExecution.case4
      A hA hbranch hsecond tail).flatProduct 0 0 =
        higham11_2_bunchKaufmanRoundedActive A 0 0 := by
  simpa using flatProduct_case4_pp fp A hA hbranch hsecond tail 0 0

theorem flatProduct_case4_01 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) :
    (Higham11RoundedBunchKaufmanExecution.case4
      A hA hbranch hsecond tail).flatProduct 0 (Fin.succ 0) =
        higham11_2_bunchKaufmanRoundedActive A 0 (Fin.succ 0) := by
  simpa using flatProduct_case4_pp fp A hA hbranch hsecond tail 0 1

theorem flatProduct_case4_10 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) :
    (Higham11RoundedBunchKaufmanExecution.case4
      A hA hbranch hsecond tail).flatProduct (Fin.succ 0) 0 =
        higham11_2_bunchKaufmanRoundedActive A (Fin.succ 0) 0 := by
  simpa using flatProduct_case4_pp fp A hA hbranch hsecond tail 1 0

theorem flatProduct_case4_11 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) :
    (Higham11RoundedBunchKaufmanExecution.case4
      A hA hbranch hsecond tail).flatProduct (Fin.succ 0) (Fin.succ 0) =
        higham11_2_bunchKaufmanRoundedActive A (Fin.succ 0) (Fin.succ 0) := by
  simpa using flatProduct_case4_pp fp A hA hbranch hsecond tail 1 1

theorem flatProduct_case4_0t (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) (j : Fin n) :
    (Higham11RoundedBunchKaufmanExecution.case4
      A hA hbranch hsecond tail).flatProduct 0 j.succ.succ =
      ∑ q : Fin 2, higham11_2_bunchKaufmanRoundedActive A 0 (embedTwo n q) *
        higham11_2_bunchKaufmanFlMultTwo fp A (tail.permutation j) q := by
  simpa using flatProduct_case4_pt fp A hA hbranch hsecond tail 0 j

theorem flatProduct_case4_1t (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) (j : Fin n) :
    (Higham11RoundedBunchKaufmanExecution.case4
      A hA hbranch hsecond tail).flatProduct (Fin.succ 0) j.succ.succ =
      ∑ q : Fin 2, higham11_2_bunchKaufmanRoundedActive A
          (Fin.succ 0) (embedTwo n q) *
        higham11_2_bunchKaufmanFlMultTwo fp A (tail.permutation j) q := by
  simpa using flatProduct_case4_pt fp A hA hbranch hsecond tail 1 j

theorem flatProduct_case4_t0 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) (i : Fin n) :
    (Higham11RoundedBunchKaufmanExecution.case4
      A hA hbranch hsecond tail).flatProduct i.succ.succ 0 =
      ∑ p : Fin 2, higham11_2_bunchKaufmanFlMultTwo fp A
          (tail.permutation i) p *
        higham11_2_bunchKaufmanRoundedActive A (embedTwo n p) 0 := by
  simpa using flatProduct_case4_tp fp A hA hbranch hsecond tail i 0

theorem flatProduct_case4_t1 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) (i : Fin n) :
    (Higham11RoundedBunchKaufmanExecution.case4
      A hA hbranch hsecond tail).flatProduct i.succ.succ (Fin.succ 0) =
      ∑ p : Fin 2, higham11_2_bunchKaufmanFlMultTwo fp A
          (tail.permutation i) p *
        higham11_2_bunchKaufmanRoundedActive A (embedTwo n p) (Fin.succ 0) := by
  simpa using flatProduct_case4_tp fp A hA hbranch hsecond tail i 1

/-! ## Absolute-product reductions -/

theorem flatAbsProduct_nonneg (fp : FPModel) {n : Nat}
    {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A) (i j : Fin n) :
    0 <= exec.flatAbsProduct i j := by
  exact higham11_4_bunchKaufmanProductEntry_nonneg
    n exec.flatL exec.flatD i j

theorem flatAbsProduct_noAction_ss (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 1)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanNoActionTail A)) (i j : Fin n) :
    (Higham11RoundedBunchKaufmanExecution.noAction
      A hA hbranch tail).flatAbsProduct i.succ j.succ =
        tail.flatAbsProduct i j := by
  change higham11_4_bunchKaufmanProductEntry (n + 1)
      (higham11_2_blockOneL (fun _ => 0) tail.flatL)
      (higham11_2_blockOneD (A 0 0) tail.flatD) i.succ j.succ = _
  rw [higham11_2_blockOne_absProduct_ss']
  simp [flatAbsProduct]

theorem flatAbsProduct_case1_tt (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) (i j : Fin (n + 1)) :
    (Higham11RoundedBunchKaufmanExecution.case1
      A hA hbranch tail).flatAbsProduct i.succ j.succ =
        higham11_2_bunchKaufmanPivotPathOneAbs fp A
            (tail.permutation i) (tail.permutation j) +
          tail.flatAbsProduct i j := by
  change higham11_4_bunchKaufmanProductEntry (n + 2)
      (higham11_2_blockOneL
        (fun k => higham11_2_bunchKaufmanFlMultOne fp A
          (tail.permutation k)) tail.flatL)
      (higham11_2_blockOneD
        (higham11_2_bunchKaufmanRoundedActive A 0 0) tail.flatD)
      i.succ j.succ = _
  rw [higham11_2_blockOne_absProduct_ss']
  rfl

theorem flatAbsProduct_case2_tt (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) (i j : Fin (n + 1)) :
    (Higham11RoundedBunchKaufmanExecution.case2
      A hA hbranch tail).flatAbsProduct i.succ j.succ =
        higham11_2_bunchKaufmanPivotPathOneAbs fp A
            (tail.permutation i) (tail.permutation j) +
          tail.flatAbsProduct i j := by
  change higham11_4_bunchKaufmanProductEntry (n + 2)
      (higham11_2_blockOneL
        (fun k => higham11_2_bunchKaufmanFlMultOne fp A
          (tail.permutation k)) tail.flatL)
      (higham11_2_blockOneD
        (higham11_2_bunchKaufmanRoundedActive A 0 0) tail.flatD)
      i.succ j.succ = _
  rw [higham11_2_blockOne_absProduct_ss']
  rfl

theorem flatAbsProduct_case3_tt (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) (i j : Fin (n + 1)) :
    (Higham11RoundedBunchKaufmanExecution.case3
      A hA hbranch tail).flatAbsProduct i.succ j.succ =
        higham11_2_bunchKaufmanPivotPathOneAbs fp A
            (tail.permutation i) (tail.permutation j) +
          tail.flatAbsProduct i j := by
  change higham11_4_bunchKaufmanProductEntry (n + 2)
      (higham11_2_blockOneL
        (fun k => higham11_2_bunchKaufmanFlMultOne fp A
          (tail.permutation k)) tail.flatL)
      (higham11_2_blockOneD
        (higham11_2_bunchKaufmanRoundedActive A 0 0) tail.flatD)
      i.succ j.succ = _
  rw [higham11_2_blockOne_absProduct_ss']
  rfl

theorem flatAbsProduct_case4_tt (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) (i j : Fin n) :
    (Higham11RoundedBunchKaufmanExecution.case4
      A hA hbranch hsecond tail).flatAbsProduct i.succ.succ j.succ.succ =
        higham11_2_bunchKaufmanPivotPathTwoAbs fp A
            (tail.permutation i) (tail.permutation j) +
          tail.flatAbsProduct i j := by
  change higham11_4_bunchKaufmanProductEntry (n + 2)
      (higham11_2_blockTwoL
        (fun k p => higham11_2_bunchKaufmanFlMultTwo fp A
          (tail.permutation k) p) tail.flatL)
      (higham11_2_blockTwoD
        (fun p q => higham11_2_bunchKaufmanRoundedActive A
          (embedTwo n p) (embedTwo n q)) tail.flatD)
      i.succ.succ j.succ.succ = _
  rw [higham11_2_blockTwo_absProduct_tt']
  rfl

theorem flatAbsProduct_case4_0t (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) (j : Fin n) :
    (Higham11RoundedBunchKaufmanExecution.case4
      A hA hbranch hsecond tail).flatAbsProduct 0 j.succ.succ =
        higham11_2_bunchKaufmanPivotRowTwoAbs fp A
          0 (tail.permutation j) := by
  change higham11_4_bunchKaufmanProductEntry (n + 2)
      (higham11_2_blockTwoL
        (fun k p => higham11_2_bunchKaufmanFlMultTwo fp A
          (tail.permutation k) p) tail.flatL)
      (higham11_2_blockTwoD
        (fun p q => higham11_2_bunchKaufmanRoundedActive A
          (embedTwo n p) (embedTwo n q)) tail.flatD)
      0 j.succ.succ = _
  rw [higham11_2_blockTwo_absProduct_0t']
  rfl

theorem flatAbsProduct_case4_1t (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) (j : Fin n) :
    (Higham11RoundedBunchKaufmanExecution.case4
      A hA hbranch hsecond tail).flatAbsProduct (Fin.succ 0) j.succ.succ =
        higham11_2_bunchKaufmanPivotRowTwoAbs fp A
          1 (tail.permutation j) := by
  change higham11_4_bunchKaufmanProductEntry (n + 2)
      (higham11_2_blockTwoL
        (fun k p => higham11_2_bunchKaufmanFlMultTwo fp A
          (tail.permutation k) p) tail.flatL)
      (higham11_2_blockTwoD
        (fun p q => higham11_2_bunchKaufmanRoundedActive A
          (embedTwo n p) (embedTwo n q)) tail.flatD)
      (Fin.succ 0) j.succ.succ = _
  rw [higham11_2_blockTwo_absProduct_1t']
  rfl

theorem flatAbsProduct_case4_t0 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) (i : Fin n) :
    (Higham11RoundedBunchKaufmanExecution.case4
      A hA hbranch hsecond tail).flatAbsProduct i.succ.succ 0 =
        higham11_2_bunchKaufmanPivotColTwoAbs fp A
          (tail.permutation i) 0 := by
  change higham11_4_bunchKaufmanProductEntry (n + 2)
      (higham11_2_blockTwoL
        (fun k p => higham11_2_bunchKaufmanFlMultTwo fp A
          (tail.permutation k) p) tail.flatL)
      (higham11_2_blockTwoD
        (fun p q => higham11_2_bunchKaufmanRoundedActive A
          (embedTwo n p) (embedTwo n q)) tail.flatD)
      i.succ.succ 0 = _
  rw [higham11_2_blockTwo_absProduct_t0']
  rfl

theorem flatAbsProduct_case4_t1 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) (i : Fin n) :
    (Higham11RoundedBunchKaufmanExecution.case4
      A hA hbranch hsecond tail).flatAbsProduct i.succ.succ (Fin.succ 0) =
        higham11_2_bunchKaufmanPivotColTwoAbs fp A
          (tail.permutation i) 1 := by
  change higham11_4_bunchKaufmanProductEntry (n + 2)
      (higham11_2_blockTwoL
        (fun k p => higham11_2_bunchKaufmanFlMultTwo fp A
          (tail.permutation k) p) tail.flatL)
      (higham11_2_blockTwoD
        (fun p q => higham11_2_bunchKaufmanRoundedActive A
          (embedTwo n p) (embedTwo n q)) tail.flatD)
      i.succ.succ (Fin.succ 0) = _
  rw [higham11_2_blockTwo_absProduct_t1']
  rfl

theorem permutedInput_noAction_ss (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 1)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanNoActionTail A)) (i j : Fin n) :
    (Higham11RoundedBunchKaufmanExecution.noAction A hA hbranch tail).permutedInput
        i.succ j.succ = tail.permutedInput i j := by
  rfl

theorem permutedInput_noAction_00 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 1)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanNoActionTail A)) :
    (Higham11RoundedBunchKaufmanExecution.noAction A hA hbranch tail).permutedInput
        0 0 = A 0 0 := by rfl

theorem permutedInput_noAction_0s (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 1)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanNoActionTail A)) (j : Fin n) :
    (Higham11RoundedBunchKaufmanExecution.noAction A hA hbranch tail).permutedInput
        0 j.succ = A 0 (tail.permutation j).succ := by rfl

theorem permutedInput_noAction_s0 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 1)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanNoActionTail A)) (i : Fin n) :
    (Higham11RoundedBunchKaufmanExecution.noAction A hA hbranch tail).permutedInput
        i.succ 0 = A (tail.permutation i).succ 0 := by rfl

theorem permutedInput_case1_ss (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) (i j : Fin (n + 1)) :
    (Higham11RoundedBunchKaufmanExecution.case1 A hA hbranch tail).permutedInput
        i.succ j.succ =
      higham11_2_bunchKaufmanRoundedActive A
        (tail.permutation i).succ (tail.permutation j).succ := by
  rfl

theorem permutedInput_case1_00 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) :
    (Higham11RoundedBunchKaufmanExecution.case1 A hA hbranch tail).permutedInput
        0 0 = higham11_2_bunchKaufmanRoundedActive A 0 0 := by
  rfl

theorem permutedInput_case1_0s (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) (j : Fin (n + 1)) :
    (Higham11RoundedBunchKaufmanExecution.case1 A hA hbranch tail).permutedInput
        0 j.succ = higham11_2_bunchKaufmanRoundedActive A
          0 (tail.permutation j).succ := by
  rfl

theorem permutedInput_case1_s0 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) (i : Fin (n + 1)) :
    (Higham11RoundedBunchKaufmanExecution.case1 A hA hbranch tail).permutedInput
        i.succ 0 = higham11_2_bunchKaufmanRoundedActive A
          (tail.permutation i).succ 0 := by
  rfl

theorem tail_permutedInput_case1 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) (i j : Fin (n + 1)) :
    tail.permutedInput i j =
      higham11_2_bunchKaufmanRoundedSchurOne fp A
        (tail.permutation i) (tail.permutation j) := by
  rfl

theorem permutedInput_case2_ss (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) (i j : Fin (n + 1)) :
    (Higham11RoundedBunchKaufmanExecution.case2 A hA hbranch tail).permutedInput
        i.succ j.succ =
      higham11_2_bunchKaufmanRoundedActive A
        (tail.permutation i).succ (tail.permutation j).succ := by
  rfl

theorem permutedInput_case2_00 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) :
    (Higham11RoundedBunchKaufmanExecution.case2 A hA hbranch tail).permutedInput
        0 0 = higham11_2_bunchKaufmanRoundedActive A 0 0 := by rfl

theorem permutedInput_case2_0s (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) (j : Fin (n + 1)) :
    (Higham11RoundedBunchKaufmanExecution.case2 A hA hbranch tail).permutedInput
        0 j.succ = higham11_2_bunchKaufmanRoundedActive A
          0 (tail.permutation j).succ := by rfl

theorem permutedInput_case2_s0 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) (i : Fin (n + 1)) :
    (Higham11RoundedBunchKaufmanExecution.case2 A hA hbranch tail).permutedInput
        i.succ 0 = higham11_2_bunchKaufmanRoundedActive A
          (tail.permutation i).succ 0 := by rfl

theorem permutedInput_case3_ss (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) (i j : Fin (n + 1)) :
    (Higham11RoundedBunchKaufmanExecution.case3 A hA hbranch tail).permutedInput
        i.succ j.succ =
      higham11_2_bunchKaufmanRoundedActive A
        (tail.permutation i).succ (tail.permutation j).succ := by
  rfl

theorem permutedInput_case3_00 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) :
    (Higham11RoundedBunchKaufmanExecution.case3 A hA hbranch tail).permutedInput
        0 0 = higham11_2_bunchKaufmanRoundedActive A 0 0 := by rfl

theorem permutedInput_case3_0s (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) (j : Fin (n + 1)) :
    (Higham11RoundedBunchKaufmanExecution.case3 A hA hbranch tail).permutedInput
        0 j.succ = higham11_2_bunchKaufmanRoundedActive A
          0 (tail.permutation j).succ := by rfl

theorem permutedInput_case3_s0 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurOne fp A)) (i : Fin (n + 1)) :
    (Higham11RoundedBunchKaufmanExecution.case3 A hA hbranch tail).permutedInput
        i.succ 0 = higham11_2_bunchKaufmanRoundedActive A
          (tail.permutation i).succ 0 := by rfl

theorem tail_permutedInput_case4 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) (i j : Fin n) :
    tail.permutedInput i j =
      higham11_2_bunchKaufmanRoundedSchurTwo fp A
        (tail.permutation i) (tail.permutation j) := by
  rfl

theorem permutedInput_case4_tt (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) (i j : Fin n) :
    (Higham11RoundedBunchKaufmanExecution.case4
        A hA hbranch hsecond tail).permutedInput i.succ.succ j.succ.succ =
      higham11_2_bunchKaufmanRoundedActive A
        (tail.permutation i).succ.succ (tail.permutation j).succ.succ := by
  rfl

theorem permutedInput_case4_pp (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) (p q : Fin 2) :
    (Higham11RoundedBunchKaufmanExecution.case4
        A hA hbranch hsecond tail).permutedInput
          (embedTwo n p) (embedTwo n q) =
      higham11_2_bunchKaufmanRoundedActive A
        (embedTwo n p) (embedTwo n q) := by
  fin_cases p <;> fin_cases q <;> rfl

theorem permutedInput_case4_pt (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) (p : Fin 2) (j : Fin n) :
    (Higham11RoundedBunchKaufmanExecution.case4
        A hA hbranch hsecond tail).permutedInput
          (embedTwo n p) j.succ.succ =
      higham11_2_bunchKaufmanRoundedActive A
        (embedTwo n p) (tail.permutation j).succ.succ := by
  fin_cases p <;> rfl

theorem permutedInput_case4_tp (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) (i : Fin n) (q : Fin 2) :
    (Higham11RoundedBunchKaufmanExecution.case4
        A hA hbranch hsecond tail).permutedInput
          i.succ.succ (embedTwo n q) =
      higham11_2_bunchKaufmanRoundedActive A
        (tail.permutation i).succ.succ (embedTwo n q) := by
  fin_cases q <;> rfl

theorem permutedInput_case4_00 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) :
    (Higham11RoundedBunchKaufmanExecution.case4
      A hA hbranch hsecond tail).permutedInput 0 0 =
        higham11_2_bunchKaufmanRoundedActive A 0 0 := by
  simpa using permutedInput_case4_pp fp A hA hbranch hsecond tail 0 0

theorem permutedInput_case4_01 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) :
    (Higham11RoundedBunchKaufmanExecution.case4
      A hA hbranch hsecond tail).permutedInput 0 (Fin.succ 0) =
        higham11_2_bunchKaufmanRoundedActive A 0 (Fin.succ 0) := by
  simpa using permutedInput_case4_pp fp A hA hbranch hsecond tail 0 1

theorem permutedInput_case4_10 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) :
    (Higham11RoundedBunchKaufmanExecution.case4
      A hA hbranch hsecond tail).permutedInput (Fin.succ 0) 0 =
        higham11_2_bunchKaufmanRoundedActive A (Fin.succ 0) 0 := by
  simpa using permutedInput_case4_pp fp A hA hbranch hsecond tail 1 0

theorem permutedInput_case4_11 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) :
    (Higham11RoundedBunchKaufmanExecution.case4
      A hA hbranch hsecond tail).permutedInput (Fin.succ 0) (Fin.succ 0) =
        higham11_2_bunchKaufmanRoundedActive A (Fin.succ 0) (Fin.succ 0) := by
  simpa using permutedInput_case4_pp fp A hA hbranch hsecond tail 1 1

theorem permutedInput_case4_0t (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) (j : Fin n) :
    (Higham11RoundedBunchKaufmanExecution.case4
      A hA hbranch hsecond tail).permutedInput 0 j.succ.succ =
      higham11_2_bunchKaufmanRoundedActive A 0
        (tail.permutation j).succ.succ := by
  simpa using permutedInput_case4_pt fp A hA hbranch hsecond tail 0 j

theorem permutedInput_case4_1t (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) (j : Fin n) :
    (Higham11RoundedBunchKaufmanExecution.case4
      A hA hbranch hsecond tail).permutedInput (Fin.succ 0) j.succ.succ =
      higham11_2_bunchKaufmanRoundedActive A (Fin.succ 0)
        (tail.permutation j).succ.succ := by
  simpa using permutedInput_case4_pt fp A hA hbranch hsecond tail 1 j

theorem permutedInput_case4_t0 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) (i : Fin n) :
    (Higham11RoundedBunchKaufmanExecution.case4
      A hA hbranch hsecond tail).permutedInput i.succ.succ 0 =
      higham11_2_bunchKaufmanRoundedActive A
        (tail.permutation i).succ.succ 0 := by
  simpa using permutedInput_case4_tp fp A hA hbranch hsecond tail i 0

theorem permutedInput_case4_t1 (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (hA) (hbranch) (hsecond)
    (tail : Higham11RoundedBunchKaufmanExecution fp
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) (i : Fin n) :
    (Higham11RoundedBunchKaufmanExecution.case4
      A hA hbranch hsecond tail).permutedInput i.succ.succ (Fin.succ 0) =
      higham11_2_bunchKaufmanRoundedActive A
        (tail.permutation i).succ.succ (Fin.succ 0) := by
  simpa using permutedInput_case4_tp fp A hA hbranch hsecond tail i 1

theorem roundedActive_pivot_ne_zero_case1 {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case1) :
    higham11_2_bunchKaufmanRoundedActive A 0 0 ≠ 0 := by
  have hp := higham11_2_bunchKaufmanCase1_pivot_ne_zero (by omega) A hbranch
  rw [higham11_2_bunchKaufmanRoundedActive,
    higham11_2_bunchKaufmanExactActive_eq_of_case1_or_case2 A (Or.inl hbranch)]
  simpa [higham11_2_firstIndex] using hp

theorem roundedActive_pivot_ne_zero_case2 {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case2) :
    higham11_2_bunchKaufmanRoundedActive A 0 0 ≠ 0 := by
  have hp := higham11_2_bunchKaufmanCase2_pivot_ne_zero (by omega) A hbranch
  rw [higham11_2_bunchKaufmanRoundedActive,
    higham11_2_bunchKaufmanExactActive_eq_of_case1_or_case2 A (Or.inr hbranch)]
  simpa [higham11_2_firstIndex] using hp

theorem roundedActive_pivot_ne_zero_case3 {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A)
    (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case3) :
    higham11_2_bunchKaufmanRoundedActive A 0 0 ≠ 0 := by
  have hp := higham11_2_bunchKaufmanCase3_pivot_ne_zero
    (by omega) A hA hbranch
  rw [higham11_2_bunchKaufmanRoundedActive,
    higham11_2_bunchKaufmanExactActive_case3_pivot A hbranch]
  exact hp

/-! ## Recursive residual envelope -/

/-- The exact stagewise residual envelope.  Nontrailing entries are recorded
literally.  A trailing entry is split into the current pivot-path/Schur
residual and the recursively accumulated tail residual. -/
noncomputable def residualEnvelope : {n : Nat} ->
    {A : Higham11RoundedBunchKaufmanMatrix n} ->
    (exec : Higham11RoundedBunchKaufmanExecution fp A) ->
      Fin n -> Fin n -> Real
  | _, _, .nil A => fun i _ => Fin.elim0 i
  | _, _, .noAction A hA hbranch tail => fun I J =>
      let exec := Higham11RoundedBunchKaufmanExecution.noAction A hA hbranch tail
      Fin.cases |exec.flatProduct 0 J - exec.permutedInput 0 J|
        (fun i => Fin.cases
          |exec.flatProduct i.succ 0 - exec.permutedInput i.succ 0|
          (fun j =>
            |tail.permutedInput i j - exec.permutedInput i.succ j.succ| +
              tail.residualEnvelope i j) J) I
  | _, _, .case1 A hA hbranch tail => fun I J =>
      let exec := Higham11RoundedBunchKaufmanExecution.case1 A hA hbranch tail
      Fin.cases |exec.flatProduct 0 J - exec.permutedInput 0 J|
        (fun i => Fin.cases
          |exec.flatProduct i.succ 0 - exec.permutedInput i.succ 0|
          (fun j =>
            |higham11_2_bunchKaufmanPivotPathOne fp A
                (tail.permutation i) (tail.permutation j) +
              tail.permutedInput i j - exec.permutedInput i.succ j.succ| +
              tail.residualEnvelope i j) J) I
  | _, _, .case2 A hA hbranch tail => fun I J =>
      let exec := Higham11RoundedBunchKaufmanExecution.case2 A hA hbranch tail
      Fin.cases |exec.flatProduct 0 J - exec.permutedInput 0 J|
        (fun i => Fin.cases
          |exec.flatProduct i.succ 0 - exec.permutedInput i.succ 0|
          (fun j =>
            |higham11_2_bunchKaufmanPivotPathOne fp A
                (tail.permutation i) (tail.permutation j) +
              tail.permutedInput i j - exec.permutedInput i.succ j.succ| +
              tail.residualEnvelope i j) J) I
  | _, _, .case3 A hA hbranch tail => fun I J =>
      let exec := Higham11RoundedBunchKaufmanExecution.case3 A hA hbranch tail
      Fin.cases |exec.flatProduct 0 J - exec.permutedInput 0 J|
        (fun i => Fin.cases
          |exec.flatProduct i.succ 0 - exec.permutedInput i.succ 0|
          (fun j =>
            |higham11_2_bunchKaufmanPivotPathOne fp A
                (tail.permutation i) (tail.permutation j) +
              tail.permutedInput i j - exec.permutedInput i.succ j.succ| +
              tail.residualEnvelope i j) J) I
  | _, _, .case4 A hA hbranch hsecond tail => fun I J =>
      let exec := Higham11RoundedBunchKaufmanExecution.case4
        A hA hbranch hsecond tail
      Fin.cases |exec.flatProduct 0 J - exec.permutedInput 0 J|
        (fun K => Fin.cases
          |exec.flatProduct (Fin.succ 0) J -
            exec.permutedInput (Fin.succ 0) J|
          (fun i => Fin.cases
            |exec.flatProduct i.succ.succ 0 -
              exec.permutedInput i.succ.succ 0|
            (fun L => Fin.cases
              |exec.flatProduct i.succ.succ (Fin.succ 0) -
                exec.permutedInput i.succ.succ (Fin.succ 0)|
              (fun j =>
                |higham11_2_bunchKaufmanPivotPathTwo fp A
                    (tail.permutation i) (tail.permutation j) +
                  tail.permutedInput i j -
                    exec.permutedInput i.succ.succ j.succ.succ| +
                  tail.residualEnvelope i j) L) J) K) I
  | _, _, exec@(.case4Breakdown _ _ _ _) => fun I J =>
      |exec.flatProduct I J - exec.permutedInput I J|

/-- Every literal rounded execution, including a terminal breakdown, satisfies
the recursive envelope.  Thus no success, nonsingularity, or stability
hypothesis is hidden in the global assembly statement. -/
theorem flat_residual_le_residualEnvelope : {n : Nat} ->
    {A : Higham11RoundedBunchKaufmanMatrix n} ->
    (exec : Higham11RoundedBunchKaufmanExecution fp A) ->
    forall i j, |exec.flatProduct i j - exec.permutedInput i j| <=
      exec.residualEnvelope i j
  | _, _, .nil A => by
      intro i
      exact Fin.elim0 i
  | _, _, .noAction A hA hbranch tail => by
      let exec := Higham11RoundedBunchKaufmanExecution.noAction A hA hbranch tail
      intro I J
      refine Fin.cases ?_ (fun i => ?_) I
      · simp [residualEnvelope]
      · refine Fin.cases ?_ (fun j => ?_) J
        · simp [residualEnvelope]
        · rw [flatProduct_noAction_ss]
          simp only [residualEnvelope, Fin.cases_succ]
          have ih := flat_residual_le_residualEnvelope tail i j
          have hsplit :
              tail.flatProduct i j - exec.permutedInput i.succ j.succ =
                (tail.flatProduct i j - tail.permutedInput i j) +
                  (tail.permutedInput i j - exec.permutedInput i.succ j.succ) := by
            ring
          rw [hsplit]
          refine le_trans (abs_add_le _ _) ?_
          dsimp only [exec]
          linarith
  | _, _, .case1 A hA hbranch tail => by
      let exec := Higham11RoundedBunchKaufmanExecution.case1 A hA hbranch tail
      intro I J
      refine Fin.cases ?_ (fun i => ?_) I
      · simp [residualEnvelope]
      · refine Fin.cases ?_ (fun j => ?_) J
        · simp [residualEnvelope]
        · rw [flatProduct_case1_tt]
          simp only [residualEnvelope, Fin.cases_succ]
          have ih := flat_residual_le_residualEnvelope tail i j
          have hsplit :
              higham11_2_bunchKaufmanPivotPathOne fp A
                    (tail.permutation i) (tail.permutation j) +
                  tail.flatProduct i j - exec.permutedInput i.succ j.succ =
                (tail.flatProduct i j - tail.permutedInput i j) +
                  (higham11_2_bunchKaufmanPivotPathOne fp A
                      (tail.permutation i) (tail.permutation j) +
                    tail.permutedInput i j -
                      exec.permutedInput i.succ j.succ) := by ring
          rw [hsplit]
          refine le_trans (abs_add_le _ _) ?_
          dsimp only [exec]
          linarith
  | _, _, .case2 A hA hbranch tail => by
      let exec := Higham11RoundedBunchKaufmanExecution.case2 A hA hbranch tail
      intro I J
      refine Fin.cases ?_ (fun i => ?_) I
      · simp [residualEnvelope]
      · refine Fin.cases ?_ (fun j => ?_) J
        · simp [residualEnvelope]
        · rw [flatProduct_case2_tt]
          simp only [residualEnvelope, Fin.cases_succ]
          have ih := flat_residual_le_residualEnvelope tail i j
          have hsplit :
              higham11_2_bunchKaufmanPivotPathOne fp A
                    (tail.permutation i) (tail.permutation j) +
                  tail.flatProduct i j - exec.permutedInput i.succ j.succ =
                (tail.flatProduct i j - tail.permutedInput i j) +
                  (higham11_2_bunchKaufmanPivotPathOne fp A
                      (tail.permutation i) (tail.permutation j) +
                    tail.permutedInput i j -
                      exec.permutedInput i.succ j.succ) := by ring
          rw [hsplit]
          refine le_trans (abs_add_le _ _) ?_
          dsimp only [exec]
          linarith
  | _, _, .case3 A hA hbranch tail => by
      let exec := Higham11RoundedBunchKaufmanExecution.case3 A hA hbranch tail
      intro I J
      refine Fin.cases ?_ (fun i => ?_) I
      · simp [residualEnvelope]
      · refine Fin.cases ?_ (fun j => ?_) J
        · simp [residualEnvelope]
        · rw [flatProduct_case3_tt]
          simp only [residualEnvelope, Fin.cases_succ]
          have ih := flat_residual_le_residualEnvelope tail i j
          have hsplit :
              higham11_2_bunchKaufmanPivotPathOne fp A
                    (tail.permutation i) (tail.permutation j) +
                  tail.flatProduct i j - exec.permutedInput i.succ j.succ =
                (tail.flatProduct i j - tail.permutedInput i j) +
                  (higham11_2_bunchKaufmanPivotPathOne fp A
                      (tail.permutation i) (tail.permutation j) +
                    tail.permutedInput i j -
                      exec.permutedInput i.succ j.succ) := by ring
          rw [hsplit]
          refine le_trans (abs_add_le _ _) ?_
          dsimp only [exec]
          linarith
  | _, _, .case4 A hA hbranch hsecond tail => by
      let exec := Higham11RoundedBunchKaufmanExecution.case4
        A hA hbranch hsecond tail
      intro I J
      refine Fin.cases ?_ (fun K => ?_) I
      · simp [residualEnvelope]
      · refine Fin.cases ?_ (fun i => ?_) K
        · unfold residualEnvelope
          rfl
        · refine Fin.cases ?_ (fun L => ?_) J
          · simp [residualEnvelope]
          · refine Fin.cases ?_ (fun j => ?_) L
            · unfold residualEnvelope
              rfl
            · rw [flatProduct_case4_tt]
              simp only [residualEnvelope, Fin.cases_succ]
              have ih := flat_residual_le_residualEnvelope tail i j
              have hsplit :
                  higham11_2_bunchKaufmanPivotPathTwo fp A
                        (tail.permutation i) (tail.permutation j) +
                      tail.flatProduct i j -
                        exec.permutedInput i.succ.succ j.succ.succ =
                    (tail.flatProduct i j - tail.permutedInput i j) +
                      (higham11_2_bunchKaufmanPivotPathTwo fp A
                          (tail.permutation i) (tail.permutation j) +
                        tail.permutedInput i j -
                          exec.permutedInput i.succ.succ j.succ.succ) := by ring
              rw [hsplit]
              refine le_trans (abs_add_le _ _) ?_
              dsimp only [exec]
              linarith
  | _, _, .case4Breakdown A hA hbranch hsecond => by
      intro I J
      exact le_rfl

/-! ## Source-shaped finite-precision endpoint -/

/-- An independently defined, finite-`u` componentwise envelope for a
*completed* rounded execution.  It contains only source data, computed
multipliers, `gamma` factors, and recursively accumulated tail bounds; in
particular it never mentions `flatProduct` or the target residual.

The one-by-one constants are the proved finite form `5 * gamma_3`; the
two-by-two update constant is `18 * gamma_3`, while the two pivot solve rows
use the finite equation-(11.5) constant `36 * u`.  These are the rigorous
finite-precision correction to the printed first-order `c u + O(u^2)` form
of Theorem 11.3. -/
noncomputable def finiteResidualEnvelope : {n : Nat} ->
    {A : Higham11RoundedBunchKaufmanMatrix n} ->
    (exec : Higham11RoundedBunchKaufmanExecution fp A) ->
      Fin n -> Fin n -> Real
  | _, _, .nil A => fun i _ => Fin.elim0 i
  | _, _, .noAction A hA hbranch tail => fun I J =>
      Fin.cases 0
        (fun i => Fin.cases 0
          (fun j => tail.finiteResidualEnvelope i j) J) I
  | _, _, .case1 A hA hbranch tail => fun I J =>
      let B := higham11_2_bunchKaufmanRoundedActive A
      let tau := tail.permutation
      Fin.cases
        (Fin.cases 0 (fun j => fp.u * |B 0 (tau j).succ|) J)
        (fun i => Fin.cases
          (fp.u * |B (tau i).succ 0|)
          (fun j =>
            5 * gamma fp 3 *
                (|B (tau i).succ (tau j).succ| +
                  higham11_2_bunchKaufmanPivotPathOneAbs fp A
                    (tau i) (tau j)) +
              tail.finiteResidualEnvelope i j) J) I
  | _, _, .case2 A hA hbranch tail => fun I J =>
      let B := higham11_2_bunchKaufmanRoundedActive A
      let tau := tail.permutation
      Fin.cases
        (Fin.cases 0 (fun j => fp.u * |B 0 (tau j).succ|) J)
        (fun i => Fin.cases
          (fp.u * |B (tau i).succ 0|)
          (fun j =>
            5 * gamma fp 3 *
                (|B (tau i).succ (tau j).succ| +
                  higham11_2_bunchKaufmanPivotPathOneAbs fp A
                    (tau i) (tau j)) +
              tail.finiteResidualEnvelope i j) J) I
  | _, _, .case3 A hA hbranch tail => fun I J =>
      let B := higham11_2_bunchKaufmanRoundedActive A
      let tau := tail.permutation
      Fin.cases
        (Fin.cases 0 (fun j => fp.u * |B 0 (tau j).succ|) J)
        (fun i => Fin.cases
          (fp.u * |B (tau i).succ 0|)
          (fun j =>
            5 * gamma fp 3 *
                (|B (tau i).succ (tau j).succ| +
                  higham11_2_bunchKaufmanPivotPathOneAbs fp A
                    (tau i) (tau j)) +
              tail.finiteResidualEnvelope i j) J) I
  | _, _, .case4 A hA hbranch hsecond tail => fun I J =>
      let B := higham11_2_bunchKaufmanRoundedActive A
      let tau := tail.permutation
      Fin.cases
        (Fin.cases 0
          (fun K => Fin.cases 0
            (fun j => 36 * fp.u *
              higham11_2_bunchKaufmanPivotRowTwoAbs fp A 0 (tau j)) K) J)
        (fun K => Fin.cases
          (Fin.cases 0
            (fun L => Fin.cases 0
              (fun j => 36 * fp.u *
                higham11_2_bunchKaufmanPivotRowTwoAbs fp A 1 (tau j)) L) J)
          (fun i => Fin.cases
            (36 * fp.u *
              higham11_2_bunchKaufmanPivotColTwoAbs fp A (tau i) 0)
            (fun L => Fin.cases
              (36 * fp.u *
                higham11_2_bunchKaufmanPivotColTwoAbs fp A (tau i) 1)
              (fun j =>
                18 * gamma fp 3 *
                    (|B (tau i).succ.succ (tau j).succ.succ| +
                      higham11_2_bunchKaufmanPivotPathTwoAbs fp A
                        (tau i) (tau j)) +
                  tail.finiteResidualEnvelope i j) L) J) K) I
  | _, _, .case4Breakdown _ _ _ _ => fun _ _ => 0

/-- The finite amplification coefficient generated by the literal pivot path.
It is computed solely from the sequence of completed one-by-one and two-by-two
stages and the model's `gamma_3`; it does not inspect either the assembled
factorization residual or the input entries. -/
noncomputable def finiteResidualCoefficient : {n : Nat} ->
    {A : Higham11RoundedBunchKaufmanMatrix n} ->
    Higham11RoundedBunchKaufmanExecution fp A -> Real
  | _, _, .nil _ => 0
  | _, _, .noAction _ _ _ tail => tail.finiteResidualCoefficient
  | _, _, .case1 _ _ _ tail =>
      let c := 5 * gamma fp 3
      c + (1 + c) * tail.finiteResidualCoefficient
  | _, _, .case2 _ _ _ tail =>
      let c := 5 * gamma fp 3
      c + (1 + c) * tail.finiteResidualCoefficient
  | _, _, .case3 _ _ _ tail =>
      let c := 5 * gamma fp 3
      c + (1 + c) * tail.finiteResidualCoefficient
  | _, _, .case4 _ _ _ _ tail =>
      let c := 18 * gamma fp 3
      c + (1 + c) * tail.finiteResidualCoefficient
  | _, _, .case4Breakdown _ _ _ _ => 0

theorem finiteResidualCoefficient_nonneg
    (hval3 : gammaValid fp 3) : {n : Nat} ->
    {A : Higham11RoundedBunchKaufmanMatrix n} ->
    (exec : Higham11RoundedBunchKaufmanExecution fp A) ->
    0 <= exec.finiteResidualCoefficient
  | _, _, .nil _ => by simp [finiteResidualCoefficient]
  | _, _, .noAction _ _ _ tail => by
      simpa [finiteResidualCoefficient] using
        finiteResidualCoefficient_nonneg hval3 tail
  | _, _, .case1 _ _ _ tail => by
      have hc : 0 <= 5 * gamma fp 3 :=
        mul_nonneg (by norm_num) (gamma_nonneg fp hval3)
      have ht := finiteResidualCoefficient_nonneg hval3 tail
      exact add_nonneg hc (mul_nonneg (by linarith) ht)
  | _, _, .case2 _ _ _ tail => by
      have hc : 0 <= 5 * gamma fp 3 :=
        mul_nonneg (by norm_num) (gamma_nonneg fp hval3)
      have ht := finiteResidualCoefficient_nonneg hval3 tail
      exact add_nonneg hc (mul_nonneg (by linarith) ht)
  | _, _, .case3 _ _ _ tail => by
      have hc : 0 <= 5 * gamma fp 3 :=
        mul_nonneg (by norm_num) (gamma_nonneg fp hval3)
      have ht := finiteResidualCoefficient_nonneg hval3 tail
      exact add_nonneg hc (mul_nonneg (by linarith) ht)
  | _, _, .case4 _ _ _ _ tail => by
      have hc : 0 <= 18 * gamma fp 3 :=
        mul_nonneg (by norm_num) (gamma_nonneg fp hval3)
      have ht := finiteResidualCoefficient_nonneg hval3 tail
      exact add_nonneg hc (mul_nonneg (by linarith) ht)
  | _, _, .case4Breakdown _ _ _ _ => by
      simp [finiteResidualCoefficient]

/-- Number of active 1-by-1 or 2-by-2 elimination stages in the literal
execution.  Zero-pivot no-action nodes do not contribute rounding growth. -/
noncomputable def activeStageCount : {n : Nat} ->
    {A : Higham11RoundedBunchKaufmanMatrix n} ->
    Higham11RoundedBunchKaufmanExecution fp A -> Nat
  | _, _, .nil _ => 0
  | _, _, .noAction _ _ _ tail => tail.activeStageCount
  | _, _, .case1 _ _ _ tail => tail.activeStageCount + 1
  | _, _, .case2 _ _ _ tail => tail.activeStageCount + 1
  | _, _, .case3 _ _ _ tail => tail.activeStageCount + 1
  | _, _, .case4 _ _ _ _ tail => tail.activeStageCount + 1
  | _, _, .case4Breakdown _ _ _ _ => 0

/-- Closed stage-count majorant for the recursive finite residual
coefficient.  It exposes the exact higher-order correction to the printed
first-order `p(n) u + O(u^2)` notation. -/
theorem one_add_finiteResidualCoefficient_le_pow_activeStageCount
    (hval3 : gammaValid fp 3) : {n : Nat} ->
    {A : Higham11RoundedBunchKaufmanMatrix n} ->
    (exec : Higham11RoundedBunchKaufmanExecution fp A) ->
    1 + exec.finiteResidualCoefficient <=
      (1 + 18 * gamma fp 3) ^ exec.activeStageCount
  | _, _, .nil _ => by
      norm_num [finiteResidualCoefficient, activeStageCount]
  | _, _, .noAction _ _ _ tail => by
      simpa [finiteResidualCoefficient, activeStageCount] using
        one_add_finiteResidualCoefficient_le_pow_activeStageCount hval3 tail
  | _, _, .case1 _ _ _ tail => by
      have hg : 0 <= gamma fp 3 := gamma_nonneg fp hval3
      have ht : 0 <= 1 + tail.finiteResidualCoefficient := by
        linarith [finiteResidualCoefficient_nonneg hval3 tail]
      have hb : 0 <= 1 + 18 * gamma fp 3 := by linarith
      have hstage : 1 + 5 * gamma fp 3 <= 1 + 18 * gamma fp 3 := by
        linarith
      have ih :=
        one_add_finiteResidualCoefficient_le_pow_activeStageCount hval3 tail
      change 1 + (5 * gamma fp 3 +
          (1 + 5 * gamma fp 3) * tail.finiteResidualCoefficient) <=
        (1 + 18 * gamma fp 3) ^ (tail.activeStageCount + 1)
      calc
        1 + (5 * gamma fp 3 +
            (1 + 5 * gamma fp 3) * tail.finiteResidualCoefficient) =
            (1 + 5 * gamma fp 3) *
              (1 + tail.finiteResidualCoefficient) := by ring
        _ <= (1 + 18 * gamma fp 3) *
              (1 + tail.finiteResidualCoefficient) :=
          mul_le_mul_of_nonneg_right hstage ht
        _ <= (1 + 18 * gamma fp 3) *
              (1 + 18 * gamma fp 3) ^ tail.activeStageCount :=
          mul_le_mul_of_nonneg_left ih hb
        _ = (1 + 18 * gamma fp 3) ^ (tail.activeStageCount + 1) := by
          rw [pow_succ]
          ring
  | _, _, .case2 _ _ _ tail => by
      have hg : 0 <= gamma fp 3 := gamma_nonneg fp hval3
      have ht : 0 <= 1 + tail.finiteResidualCoefficient := by
        linarith [finiteResidualCoefficient_nonneg hval3 tail]
      have hb : 0 <= 1 + 18 * gamma fp 3 := by linarith
      have hstage : 1 + 5 * gamma fp 3 <= 1 + 18 * gamma fp 3 := by
        linarith
      have ih :=
        one_add_finiteResidualCoefficient_le_pow_activeStageCount hval3 tail
      change 1 + (5 * gamma fp 3 +
          (1 + 5 * gamma fp 3) * tail.finiteResidualCoefficient) <=
        (1 + 18 * gamma fp 3) ^ (tail.activeStageCount + 1)
      calc
        1 + (5 * gamma fp 3 +
            (1 + 5 * gamma fp 3) * tail.finiteResidualCoefficient) =
            (1 + 5 * gamma fp 3) *
              (1 + tail.finiteResidualCoefficient) := by ring
        _ <= (1 + 18 * gamma fp 3) *
              (1 + tail.finiteResidualCoefficient) :=
          mul_le_mul_of_nonneg_right hstage ht
        _ <= (1 + 18 * gamma fp 3) *
              (1 + 18 * gamma fp 3) ^ tail.activeStageCount :=
          mul_le_mul_of_nonneg_left ih hb
        _ = (1 + 18 * gamma fp 3) ^ (tail.activeStageCount + 1) := by
          rw [pow_succ]
          ring
  | _, _, .case3 _ _ _ tail => by
      have hg : 0 <= gamma fp 3 := gamma_nonneg fp hval3
      have ht : 0 <= 1 + tail.finiteResidualCoefficient := by
        linarith [finiteResidualCoefficient_nonneg hval3 tail]
      have hb : 0 <= 1 + 18 * gamma fp 3 := by linarith
      have hstage : 1 + 5 * gamma fp 3 <= 1 + 18 * gamma fp 3 := by
        linarith
      have ih :=
        one_add_finiteResidualCoefficient_le_pow_activeStageCount hval3 tail
      change 1 + (5 * gamma fp 3 +
          (1 + 5 * gamma fp 3) * tail.finiteResidualCoefficient) <=
        (1 + 18 * gamma fp 3) ^ (tail.activeStageCount + 1)
      calc
        1 + (5 * gamma fp 3 +
            (1 + 5 * gamma fp 3) * tail.finiteResidualCoefficient) =
            (1 + 5 * gamma fp 3) *
              (1 + tail.finiteResidualCoefficient) := by ring
        _ <= (1 + 18 * gamma fp 3) *
              (1 + tail.finiteResidualCoefficient) :=
          mul_le_mul_of_nonneg_right hstage ht
        _ <= (1 + 18 * gamma fp 3) *
              (1 + 18 * gamma fp 3) ^ tail.activeStageCount :=
          mul_le_mul_of_nonneg_left ih hb
        _ = (1 + 18 * gamma fp 3) ^ (tail.activeStageCount + 1) := by
          rw [pow_succ]
          ring
  | _, _, .case4 _ _ _ _ tail => by
      have hg : 0 <= gamma fp 3 := gamma_nonneg fp hval3
      have hb : 0 <= 1 + 18 * gamma fp 3 := by linarith
      have ih :=
        one_add_finiteResidualCoefficient_le_pow_activeStageCount hval3 tail
      change 1 + (18 * gamma fp 3 +
          (1 + 18 * gamma fp 3) * tail.finiteResidualCoefficient) <=
        (1 + 18 * gamma fp 3) ^ (tail.activeStageCount + 1)
      calc
        1 + (18 * gamma fp 3 +
            (1 + 18 * gamma fp 3) * tail.finiteResidualCoefficient) =
            (1 + 18 * gamma fp 3) *
              (1 + tail.finiteResidualCoefficient) := by ring
        _ <= (1 + 18 * gamma fp 3) *
              (1 + 18 * gamma fp 3) ^ tail.activeStageCount :=
          mul_le_mul_of_nonneg_left ih hb
        _ = (1 + 18 * gamma fp 3) ^ (tail.activeStageCount + 1) := by
          rw [pow_succ]
          ring
  | _, _, .case4Breakdown _ _ _ _ => by
      norm_num [finiteResidualCoefficient, activeStageCount]

theorem finiteResidualCoefficient_le_pow_activeStageCount_sub_one
    (hval3 : gammaValid fp 3) {n : Nat}
    {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A) :
    exec.finiteResidualCoefficient <=
      (1 + 18 * gamma fp 3) ^ exec.activeStageCount - 1 := by
  linarith [one_add_finiteResidualCoefficient_le_pow_activeStageCount hval3 exec]

theorem activeStageCount_le_dimension : {n : Nat} ->
    {A : Higham11RoundedBunchKaufmanMatrix n} ->
    (exec : Higham11RoundedBunchKaufmanExecution fp A) -> exec.Completed ->
    exec.activeStageCount <= n
  | _, _, .nil _ => by
      intro _
      simp [activeStageCount]
  | _, _, .noAction _ _ _ tail => by
      intro hcompleted
      have ih := activeStageCount_le_dimension tail hcompleted
      simp only [activeStageCount]
      omega
  | _, _, .case1 _ _ _ tail => by
      intro hcompleted
      have ih := activeStageCount_le_dimension tail hcompleted
      simp only [activeStageCount]
      omega
  | _, _, .case2 _ _ _ tail => by
      intro hcompleted
      have ih := activeStageCount_le_dimension tail hcompleted
      simp only [activeStageCount]
      omega
  | _, _, .case3 _ _ _ tail => by
      intro hcompleted
      have ih := activeStageCount_le_dimension tail hcompleted
      simp only [activeStageCount]
      omega
  | _, _, .case4 _ _ _ _ tail => by
      intro hcompleted
      have ih := activeStageCount_le_dimension tail hcompleted
      simp only [activeStageCount]
      omega
  | _, _, .case4Breakdown _ _ _ _ => by
      intro hcompleted
      exact False.elim hcompleted

theorem finiteResidualCoefficient_le_pow_dimension_sub_one
    (hval3 : gammaValid fp 3) {n : Nat}
    {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (hcompleted : exec.Completed) :
    exec.finiteResidualCoefficient <=
      (1 + 18 * gamma fp 3) ^ n - 1 := by
  have hg : 0 <= gamma fp 3 := gamma_nonneg fp hval3
  have hpow :
      (1 + 18 * gamma fp 3) ^ exec.activeStageCount <=
        (1 + 18 * gamma fp 3) ^ n :=
    pow_le_pow_right₀ (by linarith)
      (activeStageCount_le_dimension exec hcompleted)
  linarith [finiteResidualCoefficient_le_pow_activeStageCount_sub_one hval3 exec]

theorem abs_pivotPathOne_le_pivotPathOneAbs (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (i j : Fin (n + 1)) :
    |higham11_2_bunchKaufmanPivotPathOne fp A i j| <=
      higham11_2_bunchKaufmanPivotPathOneAbs fp A i j := by
  simp [higham11_2_bunchKaufmanPivotPathOne,
    higham11_2_bunchKaufmanPivotPathOneAbs, abs_mul]

theorem abs_pivotPathTwo_le_pivotPathTwoAbs (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (i j : Fin n) :
    |higham11_2_bunchKaufmanPivotPathTwo fp A i j| <=
      higham11_2_bunchKaufmanPivotPathTwoAbs fp A i j := by
  unfold higham11_2_bunchKaufmanPivotPathTwo
    higham11_2_bunchKaufmanPivotPathTwoAbs
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum fun p _ => ?_
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum fun q _ => ?_
  simp [abs_mul]

/-- A local Schur residual controls the magnitude of the recursively passed
Schur entry.  This elementary bridge is what makes the global coefficient
induction independent of the target factorization residual. -/
theorem schur_abs_le_one_add_coefficient
    (c P Pabs S B : Real)
    (hP : |P| <= Pabs)
    (hres : |P + S - B| <= c * (|B| + Pabs)) :
    |S| <= (1 + c) * (|B| + Pabs) := by
  have hdecomp : S = ((P + S - B) + B) - P := by ring
  rw [hdecomp]
  calc
    |(P + S - B + B) - P| <= |P + S - B + B| + |P| := abs_sub _ _
    _ <= (|P + S - B| + |B|) + |P| := by
      have h := abs_add_le (P + S - B) B
      linarith
    _ <= c * (|B| + Pabs) + |B| + Pabs := by linarith
    _ = (1 + c) * (|B| + Pabs) := by ring

/-- One recursive stage preserves a scalar coefficient bound after adding
the current local residual. -/
theorem finiteResidual_accumulate
    (c C Babs Pabs Sabs Tabs Etail : Real)
    (hc : 0 <= c) (hC : 0 <= C) (hB : 0 <= Babs)
    (hP : 0 <= Pabs) (hT : 0 <= Tabs)
    (hS : Sabs <= (1 + c) * (Babs + Pabs))
    (hE : Etail <= C * (Sabs + Tabs)) :
    c * (Babs + Pabs) + Etail <=
      (c + (1 + c) * C) * (Babs + Pabs + Tabs) := by
  have hstage :
      c * (Babs + Pabs) <= c * (Babs + Pabs + Tabs) := by
    exact mul_le_mul_of_nonneg_left (by linarith) hc
  have hinput :
      Sabs + Tabs <= (1 + c) * (Babs + Pabs + Tabs) := by
    have hone : 1 <= 1 + c := by linarith
    have hscale : Tabs <= (1 + c) * Tabs := by
      nlinarith [mul_nonneg hc hT]
    nlinarith
  have htail :
      Etail <= C * ((1 + c) * (Babs + Pabs + Tabs)) :=
    le_trans hE (mul_le_mul_of_nonneg_left hinput hC)
  calc
    c * (Babs + Pabs) + Etail <=
        c * (Babs + Pabs + Tabs) +
          C * ((1 + c) * (Babs + Pabs + Tabs)) :=
      add_le_add hstage htail
    _ = (c + (1 + c) * C) * (Babs + Pabs + Tabs) := by ring

/-- A completed literal execution satisfies the independent finite-precision
envelope.  The explicit breakdown constructor is intentionally excluded by
`Completed`; no nonsingularity or successful-execution premise is hidden in
the envelope itself. -/
theorem residualEnvelope_le_finiteResidualEnvelope_of_completed
    (hval3 : gammaValid fp 3) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2) : {n : Nat} ->
    {A : Higham11RoundedBunchKaufmanMatrix n} ->
    (exec : Higham11RoundedBunchKaufmanExecution fp A) -> exec.Completed ->
    forall i j, exec.residualEnvelope i j <= exec.finiteResidualEnvelope i j
  | _, _, .nil A => by
      intro _ i
      exact Fin.elim0 i
  | _, _, .noAction A hA hbranch tail => by
      intro hcompleted I J
      refine Fin.cases ?_ (fun i => ?_) I
      · refine Fin.cases ?_ (fun j => ?_) J
        · simp [residualEnvelope, finiteResidualEnvelope,
            flatProduct_noAction_00, permutedInput_noAction_00]
        · have hz := Higham11ExactBunchKaufmanTrace.noAction_offDiagonal_zero
            A hA hbranch (tail.permutation j).succ (by
              simp [higham11_2_firstIndex])
          have hzrow : A 0 (tail.permutation j).succ = 0 := by
            simpa [higham11_2_firstIndex] using hz.2
          simp only [residualEnvelope, finiteResidualEnvelope,
            Fin.cases_zero, Fin.cases_succ]
          rw [flatProduct_noAction_0s, permutedInput_noAction_0s, hzrow]
          norm_num
      · refine Fin.cases ?_ (fun j => ?_) J
        · have hz := Higham11ExactBunchKaufmanTrace.noAction_offDiagonal_zero
            A hA hbranch (tail.permutation i).succ (by
              simp [higham11_2_firstIndex])
          have hzcol : A (tail.permutation i).succ 0 = 0 := by
            simpa [higham11_2_firstIndex] using hz.1
          simp only [residualEnvelope, finiteResidualEnvelope,
            Fin.cases_zero, Fin.cases_succ]
          rw [flatProduct_noAction_s0, permutedInput_noAction_s0, hzcol]
          norm_num
        · simp only [residualEnvelope, finiteResidualEnvelope, Fin.cases_succ]
          rw [permutedInput_noAction_ss]
          simp only [sub_self, abs_zero, zero_add]
          exact residualEnvelope_le_finiteResidualEnvelope_of_completed
            hval3 hval9 hsmall9 tail hcompleted i j
  | _, _, .case1 A hA hbranch tail => by
      intro hcompleted I J
      have hpivot := roundedActive_pivot_ne_zero_case1 A hbranch
      refine Fin.cases ?_ (fun i => ?_) I
      · refine Fin.cases ?_ (fun j => ?_) J
        · simp [residualEnvelope, finiteResidualEnvelope,
            flatProduct_case1_00, permutedInput_case1_00]
        · simp only [residualEnvelope, finiteResidualEnvelope,
            Fin.cases_zero, Fin.cases_succ]
          rw [flatProduct_case1_0s, permutedInput_case1_0s]
          exact higham11_2_bunchKaufmanFlMultOne_row_residual
            fp A hA hpivot (tail.permutation j)
      · refine Fin.cases ?_ (fun j => ?_) J
        · simp only [residualEnvelope, finiteResidualEnvelope,
            Fin.cases_zero, Fin.cases_succ]
          rw [flatProduct_case1_s0, permutedInput_case1_s0]
          exact higham11_2_bunchKaufmanFlMultOne_col_residual
            fp A hpivot (tail.permutation i)
        · simp only [residualEnvelope, finiteResidualEnvelope, Fin.cases_succ]
          rw [tail_permutedInput_case1, permutedInput_case1_ss]
          exact add_le_add
            (higham11_2_bunchKaufmanRoundedSchurOne_residual_bound
              fp hval3 hsmall9 A hA hpivot
                (tail.permutation i) (tail.permutation j))
            (residualEnvelope_le_finiteResidualEnvelope_of_completed
              hval3 hval9 hsmall9 tail hcompleted i j)
  | _, _, .case2 A hA hbranch tail => by
      intro hcompleted I J
      have hpivot := roundedActive_pivot_ne_zero_case2 A hbranch
      refine Fin.cases ?_ (fun i => ?_) I
      · refine Fin.cases ?_ (fun j => ?_) J
        · simp [residualEnvelope, finiteResidualEnvelope,
            flatProduct_case2_00, permutedInput_case2_00]
        · simp only [residualEnvelope, finiteResidualEnvelope,
            Fin.cases_zero, Fin.cases_succ]
          rw [flatProduct_case2_0s, permutedInput_case2_0s]
          exact higham11_2_bunchKaufmanFlMultOne_row_residual
            fp A hA hpivot (tail.permutation j)
      · refine Fin.cases ?_ (fun j => ?_) J
        · simp only [residualEnvelope, finiteResidualEnvelope,
            Fin.cases_zero, Fin.cases_succ]
          rw [flatProduct_case2_s0, permutedInput_case2_s0]
          exact higham11_2_bunchKaufmanFlMultOne_col_residual
            fp A hpivot (tail.permutation i)
        · simp only [residualEnvelope, finiteResidualEnvelope, Fin.cases_succ]
          rw [tail_permutedInput_case1, permutedInput_case2_ss]
          exact add_le_add
            (higham11_2_bunchKaufmanRoundedSchurOne_residual_bound
              fp hval3 hsmall9 A hA hpivot
                (tail.permutation i) (tail.permutation j))
            (residualEnvelope_le_finiteResidualEnvelope_of_completed
              hval3 hval9 hsmall9 tail hcompleted i j)
  | _, _, .case3 A hA hbranch tail => by
      intro hcompleted I J
      have hpivot := roundedActive_pivot_ne_zero_case3 A hA hbranch
      refine Fin.cases ?_ (fun i => ?_) I
      · refine Fin.cases ?_ (fun j => ?_) J
        · simp [residualEnvelope, finiteResidualEnvelope,
            flatProduct_case3_00, permutedInput_case3_00]
        · simp only [residualEnvelope, finiteResidualEnvelope,
            Fin.cases_zero, Fin.cases_succ]
          rw [flatProduct_case3_0s, permutedInput_case3_0s]
          exact higham11_2_bunchKaufmanFlMultOne_row_residual
            fp A hA hpivot (tail.permutation j)
      · refine Fin.cases ?_ (fun j => ?_) J
        · simp only [residualEnvelope, finiteResidualEnvelope,
            Fin.cases_zero, Fin.cases_succ]
          rw [flatProduct_case3_s0, permutedInput_case3_s0]
          exact higham11_2_bunchKaufmanFlMultOne_col_residual
            fp A hpivot (tail.permutation i)
        · simp only [residualEnvelope, finiteResidualEnvelope, Fin.cases_succ]
          rw [tail_permutedInput_case1, permutedInput_case3_ss]
          exact add_le_add
            (higham11_2_bunchKaufmanRoundedSchurOne_residual_bound
              fp hval3 hsmall9 A hA hpivot
                (tail.permutation i) (tail.permutation j))
            (residualEnvelope_le_finiteResidualEnvelope_of_completed
              hval3 hval9 hsmall9 tail hcompleted i j)
  | _, _, .case4 A hA hbranch hsecond tail => by
      intro hcompleted I J
      refine Fin.cases ?_ (fun K => ?_) I
      · refine Fin.cases ?_ (fun L => ?_) J
        · simp only [residualEnvelope, finiteResidualEnvelope,
            Fin.cases_zero, Fin.cases_succ]
          rw [flatProduct_case4_00, permutedInput_case4_00]
          norm_num
        · refine Fin.cases ?_ (fun j => ?_) L
          · simp only [residualEnvelope, finiteResidualEnvelope,
              Fin.cases_zero, Fin.cases_succ]
            rw [flatProduct_case4_01, permutedInput_case4_01]
            norm_num
          · simp only [residualEnvelope, finiteResidualEnvelope,
              Fin.cases_zero, Fin.cases_succ]
            rw [flatProduct_case4_0t, permutedInput_case4_0t]
            exact higham11_2_bunchKaufmanPivotRowTwo_residual
              fp hval9 hsmall9 A hA hbranch hsecond 0 (tail.permutation j)
      · refine Fin.cases ?_ (fun i => ?_) K
        · refine Fin.cases ?_ (fun L => ?_) J
          · simp only [residualEnvelope, finiteResidualEnvelope,
              Fin.cases_zero, Fin.cases_succ]
            rw [flatProduct_case4_10, permutedInput_case4_10]
            norm_num
          · refine Fin.cases ?_ (fun j => ?_) L
            · simp only [residualEnvelope, finiteResidualEnvelope,
                Fin.cases_zero, Fin.cases_succ]
              rw [flatProduct_case4_11, permutedInput_case4_11]
              norm_num
            · simp only [residualEnvelope, finiteResidualEnvelope,
                Fin.cases_zero, Fin.cases_succ]
              rw [flatProduct_case4_1t, permutedInput_case4_1t]
              exact higham11_2_bunchKaufmanPivotRowTwo_residual
                fp hval9 hsmall9 A hA hbranch hsecond 1 (tail.permutation j)
        · refine Fin.cases ?_ (fun L => ?_) J
          · simp only [residualEnvelope, finiteResidualEnvelope,
              Fin.cases_zero, Fin.cases_succ]
            rw [flatProduct_case4_t0, permutedInput_case4_t0]
            exact higham11_2_bunchKaufmanPivotColTwo_residual
              fp hval9 hsmall9 A hA hbranch hsecond (tail.permutation i) 0
          · refine Fin.cases ?_ (fun j => ?_) L
            · simp only [residualEnvelope, finiteResidualEnvelope,
                Fin.cases_zero, Fin.cases_succ]
              rw [flatProduct_case4_t1, permutedInput_case4_t1]
              exact higham11_2_bunchKaufmanPivotColTwo_residual
                fp hval9 hsmall9 A hA hbranch hsecond (tail.permutation i) 1
            · simp only [residualEnvelope, finiteResidualEnvelope,
                Fin.cases_succ]
              rw [tail_permutedInput_case4, permutedInput_case4_tt]
              exact add_le_add
                (higham11_2_bunchKaufmanRoundedSchurTwo_residual_bound
                  fp hval3 hval9 hsmall9 A hA hbranch hsecond
                    (tail.permutation i) (tail.permutation j))
                (residualEnvelope_le_finiteResidualEnvelope_of_completed
                  hval3 hval9 hsmall9 tail hcompleted i j)
  | _, _, .case4Breakdown A hA hbranch hsecond => by
      intro hcompleted
      exact False.elim hcompleted

/-- The independently defined finite residual envelope is bounded by a
source/computation-defined scalar times the Theorem-11.3 absolute data
`|P A P^T| + |Lhat| |Dhat| |Lhat^T|`. -/
theorem finiteResidualEnvelope_le_coefficient
    (hval3 : gammaValid fp 3) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2) : {n : Nat} ->
    {A : Higham11RoundedBunchKaufmanMatrix n} ->
    (exec : Higham11RoundedBunchKaufmanExecution fp A) -> exec.Completed ->
    forall i j,
      exec.finiteResidualEnvelope i j <=
        exec.finiteResidualCoefficient *
          (|exec.permutedInput i j| + exec.flatAbsProduct i j)
  | _, _, .nil A => by
      intro _ i
      exact Fin.elim0 i
  | _, _, .noAction A hA hbranch tail => by
      intro hcompleted I J
      let exec := Higham11RoundedBunchKaufmanExecution.noAction
        A hA hbranch tail
      have hcoeff : 0 <= exec.finiteResidualCoefficient :=
        finiteResidualCoefficient_nonneg hval3 exec
      refine Fin.cases ?_ (fun i => ?_) I
      · simp only [finiteResidualEnvelope, Fin.cases_zero]
        exact mul_nonneg hcoeff
          (add_nonneg (abs_nonneg _) (flatAbsProduct_nonneg fp exec 0 J))
      · refine Fin.cases ?_ (fun j => ?_) J
        · simp only [finiteResidualEnvelope, Fin.cases_succ, Fin.cases_zero]
          exact mul_nonneg hcoeff
            (add_nonneg (abs_nonneg _)
              (flatAbsProduct_nonneg fp exec i.succ 0))
        · simp only [finiteResidualEnvelope, finiteResidualCoefficient,
            Fin.cases_succ]
          rw [permutedInput_noAction_ss, flatAbsProduct_noAction_ss]
          exact finiteResidualEnvelope_le_coefficient
            hval3 hval9 hsmall9 tail hcompleted i j
  | _, _, .case1 A hA hbranch tail => by
      intro hcompleted I J
      let exec := Higham11RoundedBunchKaufmanExecution.case1
        A hA hbranch tail
      have hg : 0 <= gamma fp 3 := gamma_nonneg fp hval3
      have hct : 0 <= tail.finiteResidualCoefficient :=
        finiteResidualCoefficient_nonneg hval3 tail
      have hcoeff : 0 <= exec.finiteResidualCoefficient :=
        finiteResidualCoefficient_nonneg hval3 exec
      have h3u := n_mul_u_le_gamma fp 3 hval3
      have h3u' : (3 : Real) * fp.u <= gamma fp 3 := by
        simpa using h3u
      have hu5 : fp.u <= 5 * gamma fp 3 := by
        nlinarith [h3u', fp.u_nonneg]
      have htailterm :
          0 <= (1 + 5 * gamma fp 3) * tail.finiteResidualCoefficient :=
        mul_nonneg (by linarith) hct
      have hucoeff : fp.u <= exec.finiteResidualCoefficient := by
        change fp.u <= 5 * gamma fp 3 +
          (1 + 5 * gamma fp 3) * tail.finiteResidualCoefficient
        linarith
      have hpivot := roundedActive_pivot_ne_zero_case1 A hbranch
      refine Fin.cases ?_ (fun i => ?_) I
      · refine Fin.cases ?_ (fun j => ?_) J
        · simp only [finiteResidualEnvelope, Fin.cases_zero]
          exact mul_nonneg hcoeff
            (add_nonneg (abs_nonneg _) (flatAbsProduct_nonneg fp exec 0 0))
        · simp only [finiteResidualEnvelope, Fin.cases_zero, Fin.cases_succ]
          rw [permutedInput_case1_0s]
          calc
            fp.u * |higham11_2_bunchKaufmanRoundedActive A 0
                (tail.permutation j).succ| <=
                exec.finiteResidualCoefficient *
                  |higham11_2_bunchKaufmanRoundedActive A 0
                    (tail.permutation j).succ| :=
              mul_le_mul_of_nonneg_right hucoeff (abs_nonneg _)
            _ <= exec.finiteResidualCoefficient *
                (|higham11_2_bunchKaufmanRoundedActive A 0
                    (tail.permutation j).succ| +
                  exec.flatAbsProduct 0 j.succ) :=
              mul_le_mul_of_nonneg_left
                (le_add_of_nonneg_right
                  (flatAbsProduct_nonneg fp exec 0 j.succ)) hcoeff
      · refine Fin.cases ?_ (fun j => ?_) J
        · simp only [finiteResidualEnvelope, Fin.cases_succ, Fin.cases_zero]
          rw [permutedInput_case1_s0]
          calc
            fp.u * |higham11_2_bunchKaufmanRoundedActive A
                (tail.permutation i).succ 0| <=
                exec.finiteResidualCoefficient *
                  |higham11_2_bunchKaufmanRoundedActive A
                    (tail.permutation i).succ 0| :=
              mul_le_mul_of_nonneg_right hucoeff (abs_nonneg _)
            _ <= exec.finiteResidualCoefficient *
                (|higham11_2_bunchKaufmanRoundedActive A
                    (tail.permutation i).succ 0| +
                  exec.flatAbsProduct i.succ 0) :=
              mul_le_mul_of_nonneg_left
                (le_add_of_nonneg_right
                  (flatAbsProduct_nonneg fp exec i.succ 0)) hcoeff
        · have hres0 :=
            higham11_2_bunchKaufmanRoundedSchurOne_residual_bound
              fp hval3 hsmall9 A hA hpivot
                (tail.permutation i) (tail.permutation j)
          have hres :
              |higham11_2_bunchKaufmanPivotPathOne fp A
                    (tail.permutation i) (tail.permutation j) +
                  tail.permutedInput i j -
                  higham11_2_bunchKaufmanRoundedActive A
                    (tail.permutation i).succ (tail.permutation j).succ| <=
                5 * gamma fp 3 *
                  (|higham11_2_bunchKaufmanRoundedActive A
                      (tail.permutation i).succ (tail.permutation j).succ| +
                    higham11_2_bunchKaufmanPivotPathOneAbs fp A
                      (tail.permutation i) (tail.permutation j)) := by
            rw [tail_permutedInput_case1]
            exact hres0
          have hS := schur_abs_le_one_add_coefficient
            (5 * gamma fp 3)
            (higham11_2_bunchKaufmanPivotPathOne fp A
              (tail.permutation i) (tail.permutation j))
            (higham11_2_bunchKaufmanPivotPathOneAbs fp A
              (tail.permutation i) (tail.permutation j))
            (tail.permutedInput i j)
            (higham11_2_bunchKaufmanRoundedActive A
              (tail.permutation i).succ (tail.permutation j).succ)
            (abs_pivotPathOne_le_pivotPathOneAbs fp A
              (tail.permutation i) (tail.permutation j)) hres
          have hacc := finiteResidual_accumulate
            (5 * gamma fp 3) tail.finiteResidualCoefficient
            |higham11_2_bunchKaufmanRoundedActive A
              (tail.permutation i).succ (tail.permutation j).succ|
            (higham11_2_bunchKaufmanPivotPathOneAbs fp A
              (tail.permutation i) (tail.permutation j))
            |tail.permutedInput i j| (tail.flatAbsProduct i j)
            (tail.finiteResidualEnvelope i j)
            (mul_nonneg (by norm_num) hg) hct (abs_nonneg _)
            (by unfold higham11_2_bunchKaufmanPivotPathOneAbs; positivity)
            (flatAbsProduct_nonneg fp tail i j) hS
            (finiteResidualEnvelope_le_coefficient
              hval3 hval9 hsmall9 tail hcompleted i j)
          simp only [finiteResidualEnvelope, finiteResidualCoefficient,
            Fin.cases_succ]
          rw [permutedInput_case1_ss, flatAbsProduct_case1_tt]
          convert hacc using 1 <;> ring
  | _, _, .case2 A hA hbranch tail => by
      intro hcompleted I J
      let exec := Higham11RoundedBunchKaufmanExecution.case2
        A hA hbranch tail
      have hg : 0 <= gamma fp 3 := gamma_nonneg fp hval3
      have hct : 0 <= tail.finiteResidualCoefficient :=
        finiteResidualCoefficient_nonneg hval3 tail
      have hcoeff : 0 <= exec.finiteResidualCoefficient :=
        finiteResidualCoefficient_nonneg hval3 exec
      have h3u := n_mul_u_le_gamma fp 3 hval3
      have h3u' : (3 : Real) * fp.u <= gamma fp 3 := by
        simpa using h3u
      have hu5 : fp.u <= 5 * gamma fp 3 := by
        nlinarith [h3u', fp.u_nonneg]
      have htailterm :
          0 <= (1 + 5 * gamma fp 3) * tail.finiteResidualCoefficient :=
        mul_nonneg (by linarith) hct
      have hucoeff : fp.u <= exec.finiteResidualCoefficient := by
        change fp.u <= 5 * gamma fp 3 +
          (1 + 5 * gamma fp 3) * tail.finiteResidualCoefficient
        linarith
      have hpivot := roundedActive_pivot_ne_zero_case2 A hbranch
      refine Fin.cases ?_ (fun i => ?_) I
      · refine Fin.cases ?_ (fun j => ?_) J
        · simp only [finiteResidualEnvelope, Fin.cases_zero]
          exact mul_nonneg hcoeff
            (add_nonneg (abs_nonneg _) (flatAbsProduct_nonneg fp exec 0 0))
        · simp only [finiteResidualEnvelope, Fin.cases_zero, Fin.cases_succ]
          rw [permutedInput_case2_0s]
          calc
            fp.u * |higham11_2_bunchKaufmanRoundedActive A 0
                (tail.permutation j).succ| <=
                exec.finiteResidualCoefficient *
                  |higham11_2_bunchKaufmanRoundedActive A 0
                    (tail.permutation j).succ| :=
              mul_le_mul_of_nonneg_right hucoeff (abs_nonneg _)
            _ <= exec.finiteResidualCoefficient *
                (|higham11_2_bunchKaufmanRoundedActive A 0
                    (tail.permutation j).succ| +
                  exec.flatAbsProduct 0 j.succ) :=
              mul_le_mul_of_nonneg_left
                (le_add_of_nonneg_right
                  (flatAbsProduct_nonneg fp exec 0 j.succ)) hcoeff
      · refine Fin.cases ?_ (fun j => ?_) J
        · simp only [finiteResidualEnvelope, Fin.cases_succ, Fin.cases_zero]
          rw [permutedInput_case2_s0]
          calc
            fp.u * |higham11_2_bunchKaufmanRoundedActive A
                (tail.permutation i).succ 0| <=
                exec.finiteResidualCoefficient *
                  |higham11_2_bunchKaufmanRoundedActive A
                    (tail.permutation i).succ 0| :=
              mul_le_mul_of_nonneg_right hucoeff (abs_nonneg _)
            _ <= exec.finiteResidualCoefficient *
                (|higham11_2_bunchKaufmanRoundedActive A
                    (tail.permutation i).succ 0| +
                  exec.flatAbsProduct i.succ 0) :=
              mul_le_mul_of_nonneg_left
                (le_add_of_nonneg_right
                  (flatAbsProduct_nonneg fp exec i.succ 0)) hcoeff
        · have hres0 :=
            higham11_2_bunchKaufmanRoundedSchurOne_residual_bound
              fp hval3 hsmall9 A hA hpivot
                (tail.permutation i) (tail.permutation j)
          have hres :
              |higham11_2_bunchKaufmanPivotPathOne fp A
                    (tail.permutation i) (tail.permutation j) +
                  tail.permutedInput i j -
                  higham11_2_bunchKaufmanRoundedActive A
                    (tail.permutation i).succ (tail.permutation j).succ| <=
                5 * gamma fp 3 *
                  (|higham11_2_bunchKaufmanRoundedActive A
                      (tail.permutation i).succ (tail.permutation j).succ| +
                    higham11_2_bunchKaufmanPivotPathOneAbs fp A
                      (tail.permutation i) (tail.permutation j)) := by
            rw [tail_permutedInput_case1]
            exact hres0
          have hS := schur_abs_le_one_add_coefficient
            (5 * gamma fp 3)
            (higham11_2_bunchKaufmanPivotPathOne fp A
              (tail.permutation i) (tail.permutation j))
            (higham11_2_bunchKaufmanPivotPathOneAbs fp A
              (tail.permutation i) (tail.permutation j))
            (tail.permutedInput i j)
            (higham11_2_bunchKaufmanRoundedActive A
              (tail.permutation i).succ (tail.permutation j).succ)
            (abs_pivotPathOne_le_pivotPathOneAbs fp A
              (tail.permutation i) (tail.permutation j)) hres
          have hacc := finiteResidual_accumulate
            (5 * gamma fp 3) tail.finiteResidualCoefficient
            |higham11_2_bunchKaufmanRoundedActive A
              (tail.permutation i).succ (tail.permutation j).succ|
            (higham11_2_bunchKaufmanPivotPathOneAbs fp A
              (tail.permutation i) (tail.permutation j))
            |tail.permutedInput i j| (tail.flatAbsProduct i j)
            (tail.finiteResidualEnvelope i j)
            (mul_nonneg (by norm_num) hg) hct (abs_nonneg _)
            (by unfold higham11_2_bunchKaufmanPivotPathOneAbs; positivity)
            (flatAbsProduct_nonneg fp tail i j) hS
            (finiteResidualEnvelope_le_coefficient
              hval3 hval9 hsmall9 tail hcompleted i j)
          simp only [finiteResidualEnvelope, finiteResidualCoefficient,
            Fin.cases_succ]
          rw [permutedInput_case2_ss, flatAbsProduct_case2_tt]
          convert hacc using 1 <;> ring
  | _, _, .case3 A hA hbranch tail => by
      intro hcompleted I J
      let exec := Higham11RoundedBunchKaufmanExecution.case3
        A hA hbranch tail
      have hg : 0 <= gamma fp 3 := gamma_nonneg fp hval3
      have hct : 0 <= tail.finiteResidualCoefficient :=
        finiteResidualCoefficient_nonneg hval3 tail
      have hcoeff : 0 <= exec.finiteResidualCoefficient :=
        finiteResidualCoefficient_nonneg hval3 exec
      have h3u := n_mul_u_le_gamma fp 3 hval3
      have h3u' : (3 : Real) * fp.u <= gamma fp 3 := by
        simpa using h3u
      have hu5 : fp.u <= 5 * gamma fp 3 := by
        nlinarith [h3u', fp.u_nonneg]
      have htailterm :
          0 <= (1 + 5 * gamma fp 3) * tail.finiteResidualCoefficient :=
        mul_nonneg (by linarith) hct
      have hucoeff : fp.u <= exec.finiteResidualCoefficient := by
        change fp.u <= 5 * gamma fp 3 +
          (1 + 5 * gamma fp 3) * tail.finiteResidualCoefficient
        linarith
      have hpivot := roundedActive_pivot_ne_zero_case3 A hA hbranch
      refine Fin.cases ?_ (fun i => ?_) I
      · refine Fin.cases ?_ (fun j => ?_) J
        · simp only [finiteResidualEnvelope, Fin.cases_zero]
          exact mul_nonneg hcoeff
            (add_nonneg (abs_nonneg _) (flatAbsProduct_nonneg fp exec 0 0))
        · simp only [finiteResidualEnvelope, Fin.cases_zero, Fin.cases_succ]
          rw [permutedInput_case3_0s]
          calc
            fp.u * |higham11_2_bunchKaufmanRoundedActive A 0
                (tail.permutation j).succ| <=
                exec.finiteResidualCoefficient *
                  |higham11_2_bunchKaufmanRoundedActive A 0
                    (tail.permutation j).succ| :=
              mul_le_mul_of_nonneg_right hucoeff (abs_nonneg _)
            _ <= exec.finiteResidualCoefficient *
                (|higham11_2_bunchKaufmanRoundedActive A 0
                    (tail.permutation j).succ| +
                  exec.flatAbsProduct 0 j.succ) :=
              mul_le_mul_of_nonneg_left
                (le_add_of_nonneg_right
                  (flatAbsProduct_nonneg fp exec 0 j.succ)) hcoeff
      · refine Fin.cases ?_ (fun j => ?_) J
        · simp only [finiteResidualEnvelope, Fin.cases_succ, Fin.cases_zero]
          rw [permutedInput_case3_s0]
          calc
            fp.u * |higham11_2_bunchKaufmanRoundedActive A
                (tail.permutation i).succ 0| <=
                exec.finiteResidualCoefficient *
                  |higham11_2_bunchKaufmanRoundedActive A
                    (tail.permutation i).succ 0| :=
              mul_le_mul_of_nonneg_right hucoeff (abs_nonneg _)
            _ <= exec.finiteResidualCoefficient *
                (|higham11_2_bunchKaufmanRoundedActive A
                    (tail.permutation i).succ 0| +
                  exec.flatAbsProduct i.succ 0) :=
              mul_le_mul_of_nonneg_left
                (le_add_of_nonneg_right
                  (flatAbsProduct_nonneg fp exec i.succ 0)) hcoeff
        · have hres0 :=
            higham11_2_bunchKaufmanRoundedSchurOne_residual_bound
              fp hval3 hsmall9 A hA hpivot
                (tail.permutation i) (tail.permutation j)
          have hres :
              |higham11_2_bunchKaufmanPivotPathOne fp A
                    (tail.permutation i) (tail.permutation j) +
                  tail.permutedInput i j -
                  higham11_2_bunchKaufmanRoundedActive A
                    (tail.permutation i).succ (tail.permutation j).succ| <=
                5 * gamma fp 3 *
                  (|higham11_2_bunchKaufmanRoundedActive A
                      (tail.permutation i).succ (tail.permutation j).succ| +
                    higham11_2_bunchKaufmanPivotPathOneAbs fp A
                      (tail.permutation i) (tail.permutation j)) := by
            rw [tail_permutedInput_case1]
            exact hres0
          have hS := schur_abs_le_one_add_coefficient
            (5 * gamma fp 3)
            (higham11_2_bunchKaufmanPivotPathOne fp A
              (tail.permutation i) (tail.permutation j))
            (higham11_2_bunchKaufmanPivotPathOneAbs fp A
              (tail.permutation i) (tail.permutation j))
            (tail.permutedInput i j)
            (higham11_2_bunchKaufmanRoundedActive A
              (tail.permutation i).succ (tail.permutation j).succ)
            (abs_pivotPathOne_le_pivotPathOneAbs fp A
              (tail.permutation i) (tail.permutation j)) hres
          have hacc := finiteResidual_accumulate
            (5 * gamma fp 3) tail.finiteResidualCoefficient
            |higham11_2_bunchKaufmanRoundedActive A
              (tail.permutation i).succ (tail.permutation j).succ|
            (higham11_2_bunchKaufmanPivotPathOneAbs fp A
              (tail.permutation i) (tail.permutation j))
            |tail.permutedInput i j| (tail.flatAbsProduct i j)
            (tail.finiteResidualEnvelope i j)
            (mul_nonneg (by norm_num) hg) hct (abs_nonneg _)
            (by unfold higham11_2_bunchKaufmanPivotPathOneAbs; positivity)
            (flatAbsProduct_nonneg fp tail i j) hS
            (finiteResidualEnvelope_le_coefficient
              hval3 hval9 hsmall9 tail hcompleted i j)
          simp only [finiteResidualEnvelope, finiteResidualCoefficient,
            Fin.cases_succ]
          rw [permutedInput_case3_ss, flatAbsProduct_case3_tt]
          convert hacc using 1 <;> ring
  | _, _, .case4 A hA hbranch hsecond tail => by
      intro hcompleted I J
      let exec := Higham11RoundedBunchKaufmanExecution.case4
        A hA hbranch hsecond tail
      have hg : 0 <= gamma fp 3 := gamma_nonneg fp hval3
      have hct : 0 <= tail.finiteResidualCoefficient :=
        finiteResidualCoefficient_nonneg hval3 tail
      have hcoeff : 0 <= exec.finiteResidualCoefficient :=
        finiteResidualCoefficient_nonneg hval3 exec
      have h3u := n_mul_u_le_gamma fp 3 hval3
      have h3u' : (3 : Real) * fp.u <= gamma fp 3 := by
        simpa using h3u
      have h36c : 36 * fp.u <= 18 * gamma fp 3 := by
        nlinarith [h3u', fp.u_nonneg]
      have htailterm :
          0 <= (1 + 18 * gamma fp 3) * tail.finiteResidualCoefficient :=
        mul_nonneg (by linarith) hct
      have h36coeff : 36 * fp.u <= exec.finiteResidualCoefficient := by
        change 36 * fp.u <= 18 * gamma fp 3 +
          (1 + 18 * gamma fp 3) * tail.finiteResidualCoefficient
        linarith
      refine Fin.cases ?_ (fun K => ?_) I
      · refine Fin.cases ?_ (fun L => ?_) J
        · simp only [finiteResidualEnvelope, Fin.cases_zero]
          exact mul_nonneg hcoeff
            (add_nonneg (abs_nonneg _) (flatAbsProduct_nonneg fp exec 0 0))
        · refine Fin.cases ?_ (fun j => ?_) L
          · simp only [finiteResidualEnvelope, Fin.cases_zero, Fin.cases_succ]
            exact mul_nonneg hcoeff
              (add_nonneg (abs_nonneg _)
                (flatAbsProduct_nonneg fp exec 0 (Fin.succ 0)))
          · simp only [finiteResidualEnvelope, Fin.cases_zero, Fin.cases_succ]
            rw [flatAbsProduct_case4_0t]
            have hrow : 0 <= higham11_2_bunchKaufmanPivotRowTwoAbs fp A
                0 (tail.permutation j) := by
              rw [← flatAbsProduct_case4_0t fp A hA hbranch hsecond tail j]
              exact flatAbsProduct_nonneg fp exec 0 j.succ.succ
            calc
              36 * fp.u * higham11_2_bunchKaufmanPivotRowTwoAbs fp A
                  0 (tail.permutation j) <=
                  exec.finiteResidualCoefficient *
                    higham11_2_bunchKaufmanPivotRowTwoAbs fp A
                      0 (tail.permutation j) :=
                mul_le_mul_of_nonneg_right h36coeff hrow
              _ <= exec.finiteResidualCoefficient *
                  (|exec.permutedInput 0 j.succ.succ| +
                    higham11_2_bunchKaufmanPivotRowTwoAbs fp A
                      0 (tail.permutation j)) :=
                mul_le_mul_of_nonneg_left
                  (le_add_of_nonneg_left (abs_nonneg _)) hcoeff
      · refine Fin.cases ?_ (fun i => ?_) K
        · refine Fin.cases ?_ (fun L => ?_) J
          · simp only [finiteResidualEnvelope, Fin.cases_succ, Fin.cases_zero]
            exact mul_nonneg hcoeff
              (add_nonneg (abs_nonneg _)
                (flatAbsProduct_nonneg fp exec (Fin.succ 0) 0))
          · refine Fin.cases ?_ (fun j => ?_) L
            · simp only [finiteResidualEnvelope, Fin.cases_succ, Fin.cases_zero]
              exact mul_nonneg hcoeff
                (add_nonneg (abs_nonneg _)
                  (flatAbsProduct_nonneg fp exec (Fin.succ 0) (Fin.succ 0)))
            · simp only [finiteResidualEnvelope, Fin.cases_succ]
              rw [flatAbsProduct_case4_1t]
              have hrow : 0 <= higham11_2_bunchKaufmanPivotRowTwoAbs fp A
                  1 (tail.permutation j) := by
                rw [← flatAbsProduct_case4_1t fp A hA hbranch hsecond tail j]
                exact flatAbsProduct_nonneg fp exec (Fin.succ 0) j.succ.succ
              calc
                36 * fp.u * higham11_2_bunchKaufmanPivotRowTwoAbs fp A
                    1 (tail.permutation j) <=
                    exec.finiteResidualCoefficient *
                      higham11_2_bunchKaufmanPivotRowTwoAbs fp A
                        1 (tail.permutation j) :=
                  mul_le_mul_of_nonneg_right h36coeff hrow
                _ <= exec.finiteResidualCoefficient *
                    (|exec.permutedInput (Fin.succ 0) j.succ.succ| +
                      higham11_2_bunchKaufmanPivotRowTwoAbs fp A
                        1 (tail.permutation j)) :=
                  mul_le_mul_of_nonneg_left
                    (le_add_of_nonneg_left (abs_nonneg _)) hcoeff
        · refine Fin.cases ?_ (fun L => ?_) J
          · simp only [finiteResidualEnvelope, Fin.cases_succ, Fin.cases_zero]
            rw [flatAbsProduct_case4_t0]
            have hcol : 0 <= higham11_2_bunchKaufmanPivotColTwoAbs fp A
                (tail.permutation i) 0 := by
              rw [← flatAbsProduct_case4_t0 fp A hA hbranch hsecond tail i]
              exact flatAbsProduct_nonneg fp exec i.succ.succ 0
            calc
              36 * fp.u * higham11_2_bunchKaufmanPivotColTwoAbs fp A
                  (tail.permutation i) 0 <=
                  exec.finiteResidualCoefficient *
                    higham11_2_bunchKaufmanPivotColTwoAbs fp A
                      (tail.permutation i) 0 :=
                mul_le_mul_of_nonneg_right h36coeff hcol
              _ <= exec.finiteResidualCoefficient *
                  (|exec.permutedInput i.succ.succ 0| +
                    higham11_2_bunchKaufmanPivotColTwoAbs fp A
                      (tail.permutation i) 0) :=
                mul_le_mul_of_nonneg_left
                  (le_add_of_nonneg_left (abs_nonneg _)) hcoeff
          · refine Fin.cases ?_ (fun j => ?_) L
            · simp only [finiteResidualEnvelope, Fin.cases_succ]
              rw [flatAbsProduct_case4_t1]
              have hcol : 0 <= higham11_2_bunchKaufmanPivotColTwoAbs fp A
                  (tail.permutation i) 1 := by
                rw [← flatAbsProduct_case4_t1 fp A hA hbranch hsecond tail i]
                exact flatAbsProduct_nonneg fp exec i.succ.succ (Fin.succ 0)
              calc
                36 * fp.u * higham11_2_bunchKaufmanPivotColTwoAbs fp A
                    (tail.permutation i) 1 <=
                    exec.finiteResidualCoefficient *
                      higham11_2_bunchKaufmanPivotColTwoAbs fp A
                        (tail.permutation i) 1 :=
                  mul_le_mul_of_nonneg_right h36coeff hcol
                _ <= exec.finiteResidualCoefficient *
                    (|exec.permutedInput i.succ.succ (Fin.succ 0)| +
                      higham11_2_bunchKaufmanPivotColTwoAbs fp A
                        (tail.permutation i) 1) :=
                  mul_le_mul_of_nonneg_left
                    (le_add_of_nonneg_left (abs_nonneg _)) hcoeff
            · have hres0 :=
                higham11_2_bunchKaufmanRoundedSchurTwo_residual_bound
                  fp hval3 hval9 hsmall9 A hA hbranch hsecond
                    (tail.permutation i) (tail.permutation j)
              have hres :
                  |higham11_2_bunchKaufmanPivotPathTwo fp A
                        (tail.permutation i) (tail.permutation j) +
                      tail.permutedInput i j -
                      higham11_2_bunchKaufmanRoundedActive A
                        (tail.permutation i).succ.succ
                        (tail.permutation j).succ.succ| <=
                    18 * gamma fp 3 *
                      (|higham11_2_bunchKaufmanRoundedActive A
                          (tail.permutation i).succ.succ
                          (tail.permutation j).succ.succ| +
                        higham11_2_bunchKaufmanPivotPathTwoAbs fp A
                          (tail.permutation i) (tail.permutation j)) := by
                rw [tail_permutedInput_case4]
                exact hres0
              have hS := schur_abs_le_one_add_coefficient
                (18 * gamma fp 3)
                (higham11_2_bunchKaufmanPivotPathTwo fp A
                  (tail.permutation i) (tail.permutation j))
                (higham11_2_bunchKaufmanPivotPathTwoAbs fp A
                  (tail.permutation i) (tail.permutation j))
                (tail.permutedInput i j)
                (higham11_2_bunchKaufmanRoundedActive A
                  (tail.permutation i).succ.succ
                  (tail.permutation j).succ.succ)
                (abs_pivotPathTwo_le_pivotPathTwoAbs fp A
                  (tail.permutation i) (tail.permutation j)) hres
              have hacc := finiteResidual_accumulate
                (18 * gamma fp 3) tail.finiteResidualCoefficient
                |higham11_2_bunchKaufmanRoundedActive A
                  (tail.permutation i).succ.succ
                  (tail.permutation j).succ.succ|
                (higham11_2_bunchKaufmanPivotPathTwoAbs fp A
                  (tail.permutation i) (tail.permutation j))
                |tail.permutedInput i j| (tail.flatAbsProduct i j)
                (tail.finiteResidualEnvelope i j)
                (mul_nonneg (by norm_num) hg) hct (abs_nonneg _)
                (higham11_2_bunchKaufmanPivotPathTwoAbs_nonneg fp A
                  (tail.permutation i) (tail.permutation j))
                (flatAbsProduct_nonneg fp tail i j) hS
                (finiteResidualEnvelope_le_coefficient
                  hval3 hval9 hsmall9 tail hcompleted i j)
              simp only [finiteResidualEnvelope, finiteResidualCoefficient,
                Fin.cases_succ]
              rw [permutedInput_case4_tt, flatAbsProduct_case4_tt]
              convert hacc using 1 <;> ring
  | _, _, .case4Breakdown A hA hbranch hsecond => by
      intro hcompleted
      exact False.elim hcompleted

/-- The explicit entrywise backward error attached to the assembled factors. -/
noncomputable def backwardError {n : Nat}
    {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A) :
    Fin n -> Fin n -> Real :=
  fun i j => exec.flatProduct i j - exec.permutedInput i j

/-- Unconditional exact factorization identity.  Successful completion is not
needed for this algebraic statement; completion is used only to obtain the
independent finite-`u` bound below. -/
theorem permutedInput_add_backwardError {n : Nat}
    {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A) (i j : Fin n) :
    exec.permutedInput i j + exec.backwardError i j = exec.flatProduct i j := by
  unfold backwardError
  ring

theorem backwardError_abs_le_residualEnvelope {n : Nat}
    {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A) (i j : Fin n) :
    |exec.backwardError i j| <= exec.residualEnvelope i j := by
  exact flat_residual_le_residualEnvelope exec i j

/-- Final finite-precision backward-error statement for every completed
literal execution.  The right-hand side is independent of the target
residual and makes all finite-`u` correction factors explicit. -/
theorem backwardError_abs_le_finiteResidualEnvelope
    (hval3 : gammaValid fp 3) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2) {n : Nat}
    {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (hcompleted : exec.Completed) (i j : Fin n) :
    |exec.backwardError i j| <= exec.finiteResidualEnvelope i j :=
  le_trans (backwardError_abs_le_residualEnvelope exec i j)
    (residualEnvelope_le_finiteResidualEnvelope_of_completed
      hval3 hval9 hsmall9 exec hcompleted i j)

/-- Source-facing finite-`u` form of the factorization half of Theorem 11.3.
Unlike the printed first-order notation, the coefficient includes all proved
higher-order accumulation factors. -/
theorem backwardError_abs_le_finiteResidualCoefficient
    (hval3 : gammaValid fp 3) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2) {n : Nat}
    {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (hcompleted : exec.Completed) (i j : Fin n) :
    |exec.backwardError i j| <=
      exec.finiteResidualCoefficient *
        (|exec.permutedInput i j| + exec.flatAbsProduct i j) :=
  le_trans
    (backwardError_abs_le_finiteResidualEnvelope
      hval3 hval9 hsmall9 exec hcompleted i j)
    (finiteResidualEnvelope_le_coefficient
      hval3 hval9 hsmall9 exec hcompleted i j)

end Higham11RoundedBunchKaufmanExecution

end NumStability
