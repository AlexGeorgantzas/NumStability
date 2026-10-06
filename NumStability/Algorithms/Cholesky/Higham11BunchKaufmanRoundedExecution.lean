/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# Higham Algorithm 11.2: literal rounded active-submatrix execution

This module is the rounded counterpart of
`Higham11BunchKaufmanExactTrace`.  The selector is run on the current stored
active matrix, the prescribed symmetric interchange is applied, and the next
selector sees the *rounded*, stored-symmetric Schur complement.  A case-(4)
node uses the actual two-step GEPP kernel already proved to satisfy (11.5).

The executor is total: if the computed second GEPP pivot is zero it records a
`case4Breakdown` node.  Thus successful completion is an observable property
of the produced execution, not a hidden premise in its construction.

Source: Higham, 2nd ed., section 11.1.2, pp. 217--219, Algorithm 11.2 and
equation (11.5).
-/

import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedBridge

open scoped BigOperators

namespace NumStability

open Ch11Closure.Mixed

abbrev Higham11RoundedBunchKaufmanMatrix (n : Nat) :=
  Fin n -> Fin n -> Real

/-! ## Rounded stage data -/

/-- The matrix after the exact symmetric interchange selected at the current
rounded active stage. -/
noncomputable def higham11_2_bunchKaufmanRoundedActive {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) :
    Higham11RoundedBunchKaufmanMatrix (n + 2) :=
  higham11_2_bunchKaufmanExactActive A

theorem higham11_2_bunchKaufmanRoundedActive_symmetric {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A) :
    IsSymmetricFiniteMatrix (higham11_2_bunchKaufmanRoundedActive A) :=
  higham11_2_bunchKaufmanExactActive_symmetric A hA

/-- The right-hand side used to compute one multiplier row at a selected
case-(4) stage.  If `p` is the selected permutation, this is the row of the
original active matrix indexed by `p (i+2)`.  Its entries at `first` and `r`
are precisely the two entries of the permuted trailing row. -/
noncomputable def higham11_2_bunchKaufmanTrailingRhs {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (i : Fin n) :
    Fin (n + 2) -> Real :=
  fun j =>
    A (higham11_2_bunchKaufmanFirstPerm (by omega)
      higham11_1_bunchParlettAlpha A i.succ.succ) j

/-- The actual rounded multiplier row at a selected case-(4) stage.  It is
computed by the same GEPP kernel as the source-facing equation-(11.5)
producer, rather than by the unrelated `flMixedMult2` explicit-inverse path. -/
noncomputable def higham11_2_bunchKaufmanFlMultTwo (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (i : Fin n) :
    Fin 2 -> Real :=
  higham11_2_flSelectedTwoByTwoSolve fp (by omega) A
    (higham11_2_bunchKaufmanTrailingRhs A i)

/-- At a case-(4) node, the right-hand side passed to the selected solve is
exactly the corresponding trailing row of the symmetrically permuted active
matrix. -/
theorem higham11_2_bunchKaufmanTrailingRhs_eq_active {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4)
    (i : Fin n) (p : Fin 2) :
    higham11_2_bunchKaufmanTrailingRhs A i
        (Fin.cases (higham11_2_firstIndex (by omega))
          (fun _ => higham11_2_bunchKaufmanMaxRow (by omega) A) p) =
      higham11_2_bunchKaufmanRoundedActive A i.succ.succ (embedTwo n p) := by
  have hcase := higham11_2_bunchKaufmanFirstBranch_spec
    (by omega) higham11_1_bunchParlettAlpha A
  rw [hbranch] at hcase
  have hr := higham11_2_bunchKaufmanMaxRow_ne_first_of_omegaOne_ne_zero
    (by omega) A hcase.1
  have hr0 : higham11_2_bunchKaufmanMaxRow (by omega) A ≠
      (0 : Fin (n + 2)) := by
    simpa [higham11_2_firstIndex] using hr
  have hswap0 :
      Equiv.swap (1 : Fin (n + 2))
          (higham11_2_bunchKaufmanMaxRow (by omega) A) 0 = 0 := by
    exact Equiv.swap_apply_of_ne_of_ne (x := (0 : Fin (n + 2)))
      (show (0 : Fin (n + 2)) ≠ (1 : Fin (n + 2)) by
        apply Fin.ne_of_val_ne
        norm_num)
      (Ne.symm hr0)
  fin_cases p <;>
    simp [higham11_2_bunchKaufmanTrailingRhs,
      higham11_2_bunchKaufmanRoundedActive,
      higham11_2_bunchKaufmanExactActive,
      higham11_2_bunchKaufmanFirstPermutedMatrix,
      higham11_2_bunchKaufmanFirstPerm, hbranch,
      higham11_2_firstIndex, hswap0]
  all_goals rfl

/-- Local source equation (11.5) expressed entirely in the current permuted
active coordinates. -/
theorem higham11_2_bunchKaufmanFlMultTwo_active_certificate
    (fp : FPModel) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A)
    (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4)
    (hsecond : higham11_2_flSelectedTwoByTwoSecondPivot fp (by omega) A ≠ 0)
    (i : Fin n) :
    exists DeltaE : Fin 2 -> Fin 2 -> Real,
      (forall p q : Fin 2,
        |DeltaE p q| <= 36 * fp.u *
          |higham11_2_bunchKaufmanRoundedActive A
            (embedTwo n p) (embedTwo n q)|) /\
      forall p : Fin 2,
        (∑ q : Fin 2,
          (higham11_2_bunchKaufmanRoundedActive A
              (embedTwo n p) (embedTwo n q) + DeltaE p q) *
            higham11_2_bunchKaufmanFlMultTwo fp A i q) =
          higham11_2_bunchKaufmanRoundedActive A
            i.succ.succ (embedTwo n p) := by
  obtain ⟨DeltaE, hstable, heq⟩ :=
    higham11_2_flSelectedTwoByTwoSolve_higham115 fp hval9 hsmall9
      (by omega) A hA (higham11_2_bunchKaufmanTrailingRhs A i)
      hbranch hsecond
  refine ⟨DeltaE, ?_, ?_⟩
  · intro p q
    change |DeltaE p q| <= 36 * fp.u *
      |higham11_2_bunchKaufmanExactActive A
        (embedTwo n p) (embedTwo n q)|
    rw [← higham11_2_bunchKaufmanSelectedTwoBlock_eq_activeLeading
      A hbranch p q]
    exact hstable p q
  · intro p
    change (∑ q : Fin 2,
        (higham11_2_bunchKaufmanExactActive A
            (embedTwo n p) (embedTwo n q) + DeltaE p q) *
          higham11_2_bunchKaufmanFlMultTwo fp A i q) =
      higham11_2_bunchKaufmanExactActive A i.succ.succ (embedTwo n p)
    have hrhs :=
      higham11_2_bunchKaufmanTrailingRhs_eq_active A hbranch i p
    change higham11_2_bunchKaufmanTrailingRhs A i
        (Fin.cases (higham11_2_firstIndex (by omega))
          (fun _ => higham11_2_bunchKaufmanMaxRow (by omega) A) p) =
      higham11_2_bunchKaufmanExactActive A i.succ.succ (embedTwo n p) at hrhs
    rw [← hrhs]
    have hlead := higham11_2_bunchKaufmanSelectedTwoBlock_eq_activeLeading
      A hbranch
    simp_rw [← hlead]
    simpa [higham11_2_bunchKaufmanFlMultTwo] using heq p

/-- Corrected local absolute coupling in active coordinates.  The factor
`1 + 36u` is the one forced by equation (11.5); coefficient one is false. -/
theorem higham11_2_bunchKaufmanFlMultTwo_active_abs_coupling
    (fp : FPModel) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A)
    (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4)
    (hsecond : higham11_2_flSelectedTwoByTwoSecondPivot fp (by omega) A ≠ 0)
    (i j : Fin n) :
    (∑ p : Fin 2,
        |higham11_2_bunchKaufmanFlMultTwo fp A i p| *
          |higham11_2_bunchKaufmanRoundedActive A
            j.succ.succ (embedTwo n p)|) <=
      (1 + 36 * fp.u) *
        (∑ p : Fin 2, ∑ q : Fin 2,
          |higham11_2_bunchKaufmanFlMultTwo fp A i p| *
            |higham11_2_bunchKaufmanRoundedActive A
              (embedTwo n p) (embedTwo n q)| *
            |higham11_2_bunchKaufmanFlMultTwo fp A j q|) := by
  obtain ⟨DeltaE, hstable, heq⟩ :=
    higham11_2_bunchKaufmanFlMultTwo_active_certificate
      fp hval9 hsmall9 A hA hbranch hsecond j
  simpa [higham11_5_twoByTwoAbsBilinear] using
    (higham11_5_twoByTwoPivotSolveStable_abs_coupling
      fp.u 36
      (fun p q => higham11_2_bunchKaufmanRoundedActive A
        (embedTwo n p) (embedTwo n q))
      DeltaE
      (higham11_2_bunchKaufmanFlMultTwo fp A i)
      (higham11_2_bunchKaufmanFlMultTwo fp A j)
      (fun p => higham11_2_bunchKaufmanRoundedActive A
        j.succ.succ (embedTwo n p)) hstable heq)

/-- Raw rounded two-by-two Schur update. -/
noncomputable def higham11_2_bunchKaufmanRawSchurTwo (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) :
    Higham11RoundedBunchKaufmanMatrix n :=
  let B := higham11_2_bunchKaufmanRoundedActive A
  fun i j =>
    fp.fl_sub (B i.succ.succ j.succ.succ)
      (fp.fl_add
        (fp.fl_mul (higham11_2_bunchKaufmanFlMultTwo fp A i 0)
          (B j.succ.succ 0))
        (fp.fl_mul (higham11_2_bunchKaufmanFlMultTwo fp A i 1)
          (B j.succ.succ (Fin.succ 0))))

/-- Stored-symmetric rounded two-by-two Schur complement.  The implementation
computes one triangle and copies it to the other, matching a symmetric-storage
block-LDLT implementation and ensuring that the next Algorithm 11.2 selector
really receives a symmetric matrix. -/
noncomputable def higham11_2_bunchKaufmanRoundedSchurTwo (fp : FPModel)
    {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) :
    Higham11RoundedBunchKaufmanMatrix n :=
  fun i j =>
    if i.val <= j.val then
      higham11_2_bunchKaufmanRawSchurTwo fp A i j
    else
      higham11_2_bunchKaufmanRawSchurTwo fp A j i

theorem higham11_2_bunchKaufmanRoundedSchurTwo_symmetric (fp : FPModel)
    {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) :
    IsSymmetricFiniteMatrix
      (higham11_2_bunchKaufmanRoundedSchurTwo fp A) := by
  intro i j
  classical
  unfold higham11_2_bunchKaufmanRoundedSchurTwo
  by_cases hij : i.val <= j.val
  · by_cases hji : j.val <= i.val
    · have : i = j := Fin.ext (Nat.le_antisymm hij hji)
      subst j
      simp
    · simp [hij, hji]
  · have hji : j.val <= i.val := (Nat.le_total j.val i.val).resolve_right hij
    simp [hij, hji]

/-- Stored-symmetric rounded one-by-one Schur complement after the selected
symmetric interchange. -/
noncomputable def higham11_2_bunchKaufmanRoundedSchurOne (fp : FPModel)
    {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) :
    Higham11RoundedBunchKaufmanMatrix (n + 1) :=
  flStoredSymSchurCompl (n + 1) fp
    (higham11_2_bunchKaufmanRoundedActive A)

theorem higham11_2_bunchKaufmanRoundedSchurOne_symmetric (fp : FPModel)
    {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) :
    IsSymmetricFiniteMatrix
      (higham11_2_bunchKaufmanRoundedSchurOne fp A) :=
  flStoredSymSchurCompl_symm (n + 1) fp
    (higham11_2_bunchKaufmanRoundedActive A)

/-! ## Total execution, including honest breakdown -/

/-- A literal rounded Algorithm 11.2 execution.  Every successful constructor
stores the equality to the branch computed from the current rounded active
matrix.  `case4Breakdown` is terminal and records exactly the failed computed
GEPP pivot test. -/
inductive Higham11RoundedBunchKaufmanExecution (fp : FPModel) :
    {n : Nat} -> (A : Higham11RoundedBunchKaufmanMatrix n) -> Type
  | nil (A : Higham11RoundedBunchKaufmanMatrix 0) :
      Higham11RoundedBunchKaufmanExecution fp A
  | noAction {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 1))
      (hA : IsSymmetricFiniteMatrix A)
      (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
        higham11_1_bunchParlettAlpha A = BunchKaufmanCase.noAction)
      (tail : Higham11RoundedBunchKaufmanExecution fp
        (higham11_2_bunchKaufmanNoActionTail A)) :
      Higham11RoundedBunchKaufmanExecution fp A
  | case1 {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
      (hA : IsSymmetricFiniteMatrix A)
      (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
        higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case1)
      (tail : Higham11RoundedBunchKaufmanExecution fp
        (higham11_2_bunchKaufmanRoundedSchurOne fp A)) :
      Higham11RoundedBunchKaufmanExecution fp A
  | case2 {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
      (hA : IsSymmetricFiniteMatrix A)
      (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
        higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case2)
      (tail : Higham11RoundedBunchKaufmanExecution fp
        (higham11_2_bunchKaufmanRoundedSchurOne fp A)) :
      Higham11RoundedBunchKaufmanExecution fp A
  | case3 {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
      (hA : IsSymmetricFiniteMatrix A)
      (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
        higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case3)
      (tail : Higham11RoundedBunchKaufmanExecution fp
        (higham11_2_bunchKaufmanRoundedSchurOne fp A)) :
      Higham11RoundedBunchKaufmanExecution fp A
  | case4 {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
      (hA : IsSymmetricFiniteMatrix A)
      (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
        higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4)
      (hsecond : higham11_2_flSelectedTwoByTwoSecondPivot fp (by omega) A ≠ 0)
      (tail : Higham11RoundedBunchKaufmanExecution fp
        (higham11_2_bunchKaufmanRoundedSchurTwo fp A)) :
      Higham11RoundedBunchKaufmanExecution fp A
  | case4Breakdown {n : Nat}
      (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
      (hA : IsSymmetricFiniteMatrix A)
      (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
        higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4)
      (hsecond : higham11_2_flSelectedTwoByTwoSecondPivot fp (by omega) A = 0) :
      Higham11RoundedBunchKaufmanExecution fp A

namespace Higham11RoundedBunchKaufmanExecution

/-- Successful completion excludes precisely the explicit computed-pivot
breakdown constructor. -/
def Completed : {n : Nat} -> {A : Higham11RoundedBunchKaufmanMatrix n} ->
    Higham11RoundedBunchKaufmanExecution fp A -> Prop
  | _, _, .nil _ => True
  | _, _, .noAction _ _ _ tail => tail.Completed
  | _, _, .case1 _ _ _ tail => tail.Completed
  | _, _, .case2 _ _ _ tail => tail.Completed
  | _, _, .case3 _ _ _ tail => tail.Completed
  | _, _, .case4 _ _ _ _ tail => tail.Completed
  | _, _, .case4Breakdown _ _ _ _ => False

/-- Block widths consumed before completion or breakdown. -/
noncomputable def widths : {n : Nat} ->
    {A : Higham11RoundedBunchKaufmanMatrix n} ->
    Higham11RoundedBunchKaufmanExecution fp A -> List Nat
  | _, _, .nil _ => []
  | _, _, .noAction _ _ _ tail => 1 :: tail.widths
  | _, _, .case1 _ _ _ tail => 1 :: tail.widths
  | _, _, .case2 _ _ _ tail => 1 :: tail.widths
  | _, _, .case3 _ _ _ tail => 1 :: tail.widths
  | _, _, .case4 _ _ _ _ tail => 2 :: tail.widths
  | _, _, .case4Breakdown _ _ _ _ => []

/-- A completed rounded execution consumes exactly the input dimension. -/
theorem widths_sum_of_completed : {n : Nat} ->
    {A : Higham11RoundedBunchKaufmanMatrix n} ->
    (exec : Higham11RoundedBunchKaufmanExecution fp A) ->
    exec.Completed -> exec.widths.sum = n
  | _, _, .nil _ => by simp [Completed, widths]
  | _, _, .noAction _ _ _ tail => by
      intro ht
      simp [Completed, widths, widths_sum_of_completed tail ht]
      omega
  | _, _, .case1 _ _ _ tail => by
      intro ht
      simp [Completed, widths, widths_sum_of_completed tail ht]
      omega
  | _, _, .case2 _ _ _ tail => by
      intro ht
      simp [Completed, widths, widths_sum_of_completed tail ht]
      omega
  | _, _, .case3 _ _ _ tail => by
      intro ht
      simp [Completed, widths, widths_sum_of_completed tail ht]
      omega
  | _, _, .case4 _ _ _ _ tail => by
      intro ht
      simp [Completed, widths, widths_sum_of_completed tail ht]
      omega
  | _, _, .case4Breakdown _ _ _ _ => by
      intro h
      exact False.elim h

/-- Every matrix carried at a node is symmetric. -/
theorem symmetric : {n : Nat} ->
    {A : Higham11RoundedBunchKaufmanMatrix n} ->
    Higham11RoundedBunchKaufmanExecution fp A -> IsSymmetricFiniteMatrix A
  | _, _, .nil A => by intro i; exact Fin.elim0 i
  | _, _, .noAction _ hA _ _ => hA
  | _, _, .case1 _ hA _ _ => hA
  | _, _, .case2 _ hA _ _ => hA
  | _, _, .case3 _ hA _ _ => hA
  | _, _, .case4 _ hA _ _ _ => hA
  | _, _, .case4Breakdown _ hA _ _ => hA

/-- Every successful case-(4) node carries the actual equation-(11.5)
componentwise perturbation certificate for every computed multiplier row. -/
inductive AllTwoSolveCertificates (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2) :
    {n : Nat} -> {A : Higham11RoundedBunchKaufmanMatrix n} ->
      Higham11RoundedBunchKaufmanExecution fp A -> Prop
  | nil (A : Higham11RoundedBunchKaufmanMatrix 0) :
      AllTwoSolveCertificates hval9 hsmall9 (.nil A)
  | noAction {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 1))
      (hA) (hbranch) (tail) :
      AllTwoSolveCertificates hval9 hsmall9 tail ->
      AllTwoSolveCertificates hval9 hsmall9 (.noAction A hA hbranch tail)
  | case1 {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
      (hA) (hbranch) (tail) :
      AllTwoSolveCertificates hval9 hsmall9 tail ->
      AllTwoSolveCertificates hval9 hsmall9 (.case1 A hA hbranch tail)
  | case2 {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
      (hA) (hbranch) (tail) :
      AllTwoSolveCertificates hval9 hsmall9 tail ->
      AllTwoSolveCertificates hval9 hsmall9 (.case2 A hA hbranch tail)
  | case3 {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
      (hA) (hbranch) (tail) :
      AllTwoSolveCertificates hval9 hsmall9 tail ->
      AllTwoSolveCertificates hval9 hsmall9 (.case3 A hA hbranch tail)
  | case4 {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
      (hA) (hbranch) (hsecond) (tail)
      (hlocal : forall i : Fin n,
        exists DeltaE : Fin 2 -> Fin 2 -> Real,
          higham11_5_twoByTwoPivotSolveStable fp.u 36
            (higham11_2_bunchKaufmanSelectedTwoBlock (by omega) A) DeltaE /\
          forall p : Fin 2,
            (∑ q : Fin 2,
              (higham11_2_bunchKaufmanSelectedTwoBlock (by omega) A p q +
                DeltaE p q) *
                higham11_2_bunchKaufmanFlMultTwo fp A i q) =
              higham11_2_bunchKaufmanTrailingRhs A i
                (Fin.cases (higham11_2_firstIndex (by omega))
                  (fun _ => higham11_2_bunchKaufmanMaxRow (by omega) A) p)) :
      AllTwoSolveCertificates hval9 hsmall9 tail ->
      AllTwoSolveCertificates hval9 hsmall9
        (.case4 A hA hbranch hsecond tail)
  | case4Breakdown {n : Nat}
      (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
      (hA) (hbranch) (hsecond) :
      AllTwoSolveCertificates hval9 hsmall9
        (.case4Breakdown A hA hbranch hsecond)

/-- The equation-(11.5) certificates are produced from the literal GEPP run;
they are not hypotheses of successful completion. -/
theorem allTwoSolveCertificates (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2) :
    forall {n : Nat} {A : Higham11RoundedBunchKaufmanMatrix n}
      (exec : Higham11RoundedBunchKaufmanExecution fp A),
      exec.AllTwoSolveCertificates hval9 hsmall9 := by
  intro n A exec
  induction exec with
  | nil A => exact .nil A
  | noAction A hA hbranch tail ih => exact .noAction A hA hbranch tail ih
  | case1 A hA hbranch tail ih => exact .case1 A hA hbranch tail ih
  | case2 A hA hbranch tail ih => exact .case2 A hA hbranch tail ih
  | case3 A hA hbranch tail ih => exact .case3 A hA hbranch tail ih
  | case4 A hA hbranch hsecond tail ih =>
      exact .case4 A hA hbranch hsecond tail (fun i =>
        higham11_2_flSelectedTwoByTwoSolve_higham115 fp hval9 hsmall9
          (by omega) A hA (higham11_2_bunchKaufmanTrailingRhs A i)
          hbranch hsecond) ih
  | case4Breakdown A hA hbranch hsecond =>
      exact .case4Breakdown A hA hbranch hsecond

end Higham11RoundedBunchKaufmanExecution

/-! ## Canonical total producer -/

/-- Every finite symmetric input has a total rounded execution.  The result
either completes or contains a concrete `case4Breakdown` witness. -/
theorem higham11_2_nonempty_roundedBunchKaufmanExecution (fp : FPModel) :
    forall {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix n),
      IsSymmetricFiniteMatrix A ->
        Nonempty (Higham11RoundedBunchKaufmanExecution fp A) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro A hA
      cases n with
      | zero => exact Nonempty.intro (.nil A)
      | succ m =>
          cases hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
              higham11_1_bunchParlettAlpha A with
          | noAction =>
              let S := higham11_2_bunchKaufmanNoActionTail A
              have hS : IsSymmetricFiniteMatrix S :=
                higham11_2_bunchKaufmanNoActionTail_symmetric A hA
              let tail : Higham11RoundedBunchKaufmanExecution fp S :=
                Classical.choice (ih m (by omega) S hS)
              exact Nonempty.intro (.noAction A hA hbranch tail)
          | case1 =>
              cases m with
              | zero =>
                  have hnone := higham11_2_bunchKaufmanFirstBranch_finOne A
                  rw [hnone] at hbranch
                  contradiction
              | succ k =>
                  let S := higham11_2_bunchKaufmanRoundedSchurOne fp A
                  have hS : IsSymmetricFiniteMatrix S :=
                    higham11_2_bunchKaufmanRoundedSchurOne_symmetric fp A
                  let tail : Higham11RoundedBunchKaufmanExecution fp S :=
                    Classical.choice (ih (k + 1) (by omega) S hS)
                  exact Nonempty.intro (.case1 A hA hbranch tail)
          | case2 =>
              cases m with
              | zero =>
                  have hnone := higham11_2_bunchKaufmanFirstBranch_finOne A
                  rw [hnone] at hbranch
                  contradiction
              | succ k =>
                  let S := higham11_2_bunchKaufmanRoundedSchurOne fp A
                  have hS : IsSymmetricFiniteMatrix S :=
                    higham11_2_bunchKaufmanRoundedSchurOne_symmetric fp A
                  let tail : Higham11RoundedBunchKaufmanExecution fp S :=
                    Classical.choice (ih (k + 1) (by omega) S hS)
                  exact Nonempty.intro (.case2 A hA hbranch tail)
          | case3 =>
              cases m with
              | zero =>
                  have hnone := higham11_2_bunchKaufmanFirstBranch_finOne A
                  rw [hnone] at hbranch
                  contradiction
              | succ k =>
                  let S := higham11_2_bunchKaufmanRoundedSchurOne fp A
                  have hS : IsSymmetricFiniteMatrix S :=
                    higham11_2_bunchKaufmanRoundedSchurOne_symmetric fp A
                  let tail : Higham11RoundedBunchKaufmanExecution fp S :=
                    Classical.choice (ih (k + 1) (by omega) S hS)
                  exact Nonempty.intro (.case3 A hA hbranch tail)
          | case4 =>
              cases m with
              | zero =>
                  have hnone := higham11_2_bunchKaufmanFirstBranch_finOne A
                  rw [hnone] at hbranch
                  contradiction
              | succ k =>
                  by_cases hsecond :
                      higham11_2_flSelectedTwoByTwoSecondPivot fp (by omega) A = 0
                  · exact Nonempty.intro
                      (.case4Breakdown A hA hbranch hsecond)
                  · let S := higham11_2_bunchKaufmanRoundedSchurTwo fp A
                    have hS : IsSymmetricFiniteMatrix S :=
                      higham11_2_bunchKaufmanRoundedSchurTwo_symmetric fp A
                    let tail : Higham11RoundedBunchKaufmanExecution fp S :=
                      Classical.choice (ih k (by omega) S hS)
                    exact Nonempty.intro (.case4 A hA hbranch hsecond tail)

/-- Canonical choice-fixed total rounded execution. -/
noncomputable def higham11_2_roundedBunchKaufmanExecution (fp : FPModel)
    {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix n)
    (hA : IsSymmetricFiniteMatrix A) :
    Higham11RoundedBunchKaufmanExecution fp A :=
  Classical.choice (higham11_2_nonempty_roundedBunchKaufmanExecution fp A hA)

end NumStability
