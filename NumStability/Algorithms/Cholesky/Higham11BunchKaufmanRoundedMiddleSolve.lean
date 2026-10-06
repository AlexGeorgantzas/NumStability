/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# Actual middle solve for the literal rounded Bunch--Kaufman execution

This module closes the operational middle-solve premise in Higham's Theorem
11.3.  It recursively solves the block-diagonal factor actually stored by
`Higham11RoundedBunchKaufmanExecution`.  Scalar blocks use rounded division;
two-by-two blocks use the selected two-step GEPP producer proved to satisfy
equation (11.5).

The only extra run-domain condition is the unavoidable one for a terminal
`noAction` scalar block: its diagonal entry must be nonzero.  The scalar pivots
in cases (1)--(3) are nonzero consequences of the selector, and a successful
case-(4) constructor already records that its computed second GEPP pivot is
nonzero.
-/

import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedSolve

open scoped BigOperators

namespace NumStability

open Ch11Closure.Mixed
open Ch11Closure.Solve

namespace Higham11RoundedBunchKaufmanExecution

/-- Honest run domain for solving the produced block-diagonal factor for every
right-hand side.  A `noAction` node can carry a zero scalar block (for example
on a singular zero matrix), so that constructor alone needs an explicit
nonzero condition. -/
def MiddleSolveRunDomain : {n : Nat} ->
    {A : Higham11RoundedBunchKaufmanMatrix n} ->
    Higham11RoundedBunchKaufmanExecution fp A -> Prop
  | _, _, .nil _ => True
  | _, _, .noAction A _ _ tail => A 0 0 ≠ 0 ∧ tail.MiddleSolveRunDomain
  | _, _, .case1 _ _ _ tail => tail.MiddleSolveRunDomain
  | _, _, .case2 _ _ _ tail => tail.MiddleSolveRunDomain
  | _, _, .case3 _ _ _ tail => tail.MiddleSolveRunDomain
  | _, _, .case4 _ _ _ _ tail => tail.MiddleSolveRunDomain
  | _, _, .case4Breakdown _ _ _ _ => False

/-- `gamma_1` is safely absorbed into the source equation-(11.5) coefficient
`36u` under the guards already required by the actual two-by-two producer. -/
theorem gamma_one_le_thirtySix_mul_u_of_gammaValid_nine
    (_hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2) :
    gamma fp 1 <= 36 * fp.u := by
  have hhalf1 : ((1 : Nat) : Real) * fp.u <= 1 / 2 := by
    nlinarith [fp.u_nonneg]
  have hgamma := gamma_le_two_mul_n_u_of_nu_le_half fp 1 hhalf1
  norm_num at hgamma ⊢
  nlinarith [fp.u_nonneg]

/-- Every admissible literal execution supplies the block middle solve required
by Theorem 11.3.  The witnesses `w` and `DeltaD` are constructed from the
actual scalar divisions and selected two-step GEPP solves; neither the solve
equation nor its perturbation bound is assumed. -/
theorem actualMiddleSolve_backward_error
    (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2) :
    forall {n : Nat} {A : Higham11RoundedBunchKaufmanMatrix n}
      (exec : Higham11RoundedBunchKaufmanExecution fp A),
      exec.MiddleSolveRunDomain ->
      forall z : Fin n -> Real,
        exists (w : Fin n -> Real) (DeltaD : Fin n -> Fin n -> Real),
          (forall i j : Fin n,
            |DeltaD i j| <= 36 * fp.u * |exec.flatD i j|) /\
          forall p : Fin n,
            (∑ q : Fin n, (exec.flatD p q + DeltaD p q) * w q) = z p := by
  intro n A exec
  induction exec with
  | nil A =>
      intro _ z
      refine ⟨(fun i => Fin.elim0 i), (fun i _ => Fin.elim0 i), ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro p
        exact Fin.elim0 p
  | noAction A hA hbranch tail ih =>
      intro hdomain z
      rcases hdomain with ⟨hpivot, htailDomain⟩
      have hval1 : gammaValid fp 1 := gammaValid_mono fp (by norm_num) hval9
      obtain ⟨Deltae, hDeltae, hheadEq⟩ :=
        fl_oneByOne_solve_backward_error fp (z 0) (A 0 0) hpivot hval1
      obtain ⟨wTail, DeltaTail, htailBound, htailEq⟩ :=
        ih htailDomain (fun i => z i.succ)
      have hgamma :=
        gamma_one_le_thirtySix_mul_u_of_gammaValid_nine hval9 hsmall9
      have hheadBound : |Deltae| <= 36 * fp.u * |A 0 0| :=
        hDeltae.trans (mul_le_mul_of_nonneg_right hgamma (abs_nonneg _))
      obtain ⟨w, DeltaD, hbound, heq⟩ :=
        middleBlockDiagConsOne_solve_assemble (36 * fp.u) (A 0 0) (z 0)
          tail.flatD (fun i => z i.succ)
          (fp.fl_div (z 0) (A 0 0)) Deltae wTail DeltaTail
          hheadBound hheadEq htailBound htailEq
      refine ⟨w, DeltaD, ?_, ?_⟩
      · intro i j
        simpa [flatD, middleBlockDiagConsOne] using hbound i j
      · intro p
        have hp := heq p
        cases p using Fin.cases with
        | zero => simpa [flatD, middleBlockDiagConsOne, middleVecConsOne] using hp
        | succ i => simpa [flatD, middleBlockDiagConsOne, middleVecConsOne] using hp
  | case1 A hA hbranch tail ih =>
      intro hdomain z
      let B := higham11_2_bunchKaufmanRoundedActive A
      have hpivot : B 0 0 ≠ 0 := roundedActive_pivot_ne_zero_case1 A hbranch
      have hval1 : gammaValid fp 1 := gammaValid_mono fp (by norm_num) hval9
      obtain ⟨Deltae, hDeltae, hheadEq⟩ :=
        fl_oneByOne_solve_backward_error fp (z 0) (B 0 0) hpivot hval1
      obtain ⟨wTail, DeltaTail, htailBound, htailEq⟩ :=
        ih hdomain (fun i => z i.succ)
      have hgamma :=
        gamma_one_le_thirtySix_mul_u_of_gammaValid_nine hval9 hsmall9
      have hheadBound : |Deltae| <= 36 * fp.u * |B 0 0| :=
        hDeltae.trans (mul_le_mul_of_nonneg_right hgamma (abs_nonneg _))
      obtain ⟨w, DeltaD, hbound, heq⟩ :=
        middleBlockDiagConsOne_solve_assemble (36 * fp.u) (B 0 0) (z 0)
          tail.flatD (fun i => z i.succ)
          (fp.fl_div (z 0) (B 0 0)) Deltae wTail DeltaTail
          hheadBound hheadEq htailBound htailEq
      refine ⟨w, DeltaD, ?_, ?_⟩
      · intro i j
        simpa [flatD, B, middleBlockDiagConsOne] using hbound i j
      · intro p
        have hp := heq p
        cases p using Fin.cases with
        | zero => simpa [flatD, B, middleBlockDiagConsOne, middleVecConsOne] using hp
        | succ i => simpa [flatD, B, middleBlockDiagConsOne, middleVecConsOne] using hp
  | case2 A hA hbranch tail ih =>
      intro hdomain z
      let B := higham11_2_bunchKaufmanRoundedActive A
      have hpivot : B 0 0 ≠ 0 := roundedActive_pivot_ne_zero_case2 A hbranch
      have hval1 : gammaValid fp 1 := gammaValid_mono fp (by norm_num) hval9
      obtain ⟨Deltae, hDeltae, hheadEq⟩ :=
        fl_oneByOne_solve_backward_error fp (z 0) (B 0 0) hpivot hval1
      obtain ⟨wTail, DeltaTail, htailBound, htailEq⟩ :=
        ih hdomain (fun i => z i.succ)
      have hgamma :=
        gamma_one_le_thirtySix_mul_u_of_gammaValid_nine hval9 hsmall9
      have hheadBound : |Deltae| <= 36 * fp.u * |B 0 0| :=
        hDeltae.trans (mul_le_mul_of_nonneg_right hgamma (abs_nonneg _))
      obtain ⟨w, DeltaD, hbound, heq⟩ :=
        middleBlockDiagConsOne_solve_assemble (36 * fp.u) (B 0 0) (z 0)
          tail.flatD (fun i => z i.succ)
          (fp.fl_div (z 0) (B 0 0)) Deltae wTail DeltaTail
          hheadBound hheadEq htailBound htailEq
      refine ⟨w, DeltaD, ?_, ?_⟩
      · intro i j
        simpa [flatD, B, middleBlockDiagConsOne] using hbound i j
      · intro p
        have hp := heq p
        cases p using Fin.cases with
        | zero => simpa [flatD, B, middleBlockDiagConsOne, middleVecConsOne] using hp
        | succ i => simpa [flatD, B, middleBlockDiagConsOne, middleVecConsOne] using hp
  | case3 A hA hbranch tail ih =>
      intro hdomain z
      let B := higham11_2_bunchKaufmanRoundedActive A
      have hpivot : B 0 0 ≠ 0 := roundedActive_pivot_ne_zero_case3 A hA hbranch
      have hval1 : gammaValid fp 1 := gammaValid_mono fp (by norm_num) hval9
      obtain ⟨Deltae, hDeltae, hheadEq⟩ :=
        fl_oneByOne_solve_backward_error fp (z 0) (B 0 0) hpivot hval1
      obtain ⟨wTail, DeltaTail, htailBound, htailEq⟩ :=
        ih hdomain (fun i => z i.succ)
      have hgamma :=
        gamma_one_le_thirtySix_mul_u_of_gammaValid_nine hval9 hsmall9
      have hheadBound : |Deltae| <= 36 * fp.u * |B 0 0| :=
        hDeltae.trans (mul_le_mul_of_nonneg_right hgamma (abs_nonneg _))
      obtain ⟨w, DeltaD, hbound, heq⟩ :=
        middleBlockDiagConsOne_solve_assemble (36 * fp.u) (B 0 0) (z 0)
          tail.flatD (fun i => z i.succ)
          (fp.fl_div (z 0) (B 0 0)) Deltae wTail DeltaTail
          hheadBound hheadEq htailBound htailEq
      refine ⟨w, DeltaD, ?_, ?_⟩
      · intro i j
        simpa [flatD, B, middleBlockDiagConsOne] using hbound i j
      · intro p
        have hp := heq p
        cases p using Fin.cases with
        | zero => simpa [flatD, B, middleBlockDiagConsOne, middleVecConsOne] using hp
        | succ i => simpa [flatD, B, middleBlockDiagConsOne, middleVecConsOne] using hp
  | @case4 n A hA hbranch hsecond tail ih =>
      intro hdomain z
      let B := higham11_2_bunchKaufmanRoundedActive A
      let zSource : Fin (n + 2) -> Real := fun k =>
        if k = 0 then z 0 else z 1
      obtain ⟨wTail, DeltaTail, htailBound, htailEq⟩ :=
        ih hdomain (fun i => z i.succ.succ)
      obtain ⟨DeltaE, hstable, hheadSourceEq⟩ :=
        higham11_2_flSelectedTwoByTwoSolve_higham115 fp hval9 hsmall9
          (by omega : 0 < n + 2) A hA zSource hbranch hsecond
      have hcase := higham11_2_bunchKaufmanFirstBranch_spec
        (by omega : 0 < n + 2) higham11_1_bunchParlettAlpha A
      rw [hbranch] at hcase
      have hr0 : higham11_2_bunchKaufmanMaxRow
          (by omega : 0 < n + 2) A ≠ (0 : Fin (n + 2)) := by
        simpa [higham11_2_firstIndex] using
          (higham11_2_bunchKaufmanMaxRow_ne_first_of_omegaOne_ne_zero
            (by omega : 0 < n + 2) A hcase.1)
      have hlead := higham11_2_bunchKaufmanSelectedTwoBlock_eq_activeLeading
        A hbranch
      have hheadBound : forall p q : Fin 2,
          |DeltaE p q| <= 36 * fp.u * |B (embedTwo n p) (embedTwo n q)| := by
        intro p q
        change |DeltaE p q| <= 36 * fp.u *
          |higham11_2_bunchKaufmanExactActive A (embedTwo n p) (embedTwo n q)|
        rw [← hlead p q]
        exact hstable p q
      have hheadEq : forall p : Fin 2,
          (∑ q : Fin 2,
            (B (embedTwo n p) (embedTwo n q) + DeltaE p q) *
              higham11_2_flSelectedTwoByTwoSolve fp (by omega : 0 < n + 2) A zSource q) =
            z (embedTwo n p) := by
        intro p
        have hp := hheadSourceEq p
        change (∑ q : Fin 2,
            (higham11_2_bunchKaufmanExactActive A
              (embedTwo n p) (embedTwo n q) + DeltaE p q) *
              higham11_2_flSelectedTwoByTwoSolve fp (by omega : 0 < n + 2) A zSource q) =
            z (embedTwo n p)
        simp_rw [← hlead]
        rw [hp]
        fin_cases p
        · simp [zSource, higham11_2_firstIndex]
        · change zSource
            (higham11_2_bunchKaufmanMaxRow (by omega : 0 < n + 2) A) = z 1
          simp [zSource, hr0]
      obtain ⟨w, DeltaD, hbound, heq⟩ :=
        middleBlockDiagConsTwo_solve_assemble (36 * fp.u)
          (fun p q => B (embedTwo n p) (embedTwo n q)) tail.flatD
          (fun p => z (embedTwo n p)) (fun i => z i.succ.succ)
          (higham11_2_flSelectedTwoByTwoSolve fp (by omega : 0 < n + 2) A zSource)
          DeltaE wTail DeltaTail hheadBound hheadEq htailBound htailEq
      refine ⟨w, DeltaD, ?_, ?_⟩
      · intro i j
        simpa [flatD, B, middleBlockDiagConsTwo] using hbound i j
      · intro p
        cases p using Fin.cases with
        | zero =>
            simpa [flatD, B, middleBlockDiagConsTwo, middleVecConsTwo] using
              heq (0 : Fin (n + 2))
        | succ k =>
            cases k using Fin.cases with
            | zero =>
                simpa [flatD, B, middleBlockDiagConsTwo, middleVecConsTwo] using
                  heq (Fin.succ (0 : Fin (n + 1)))
            | succ i =>
                simpa [flatD, B, middleBlockDiagConsTwo, middleVecConsTwo] using
                  heq i.succ.succ
  | case4Breakdown A hA hbranch hsecond =>
      intro hdomain
      exact False.elim hdomain

end Higham11RoundedBunchKaufmanExecution

end NumStability
