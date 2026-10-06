/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.Sylvester.Higham16QuasiQuasiSylvester

namespace NumStability

namespace Wave16

open scoped BigOperators
open Wave15

/-!
# Chapter 16: an honest pivoted small-block suffix

Higham's discussion after (16.8) says that the real-Schur Bartels--Stewart
algorithm solves diagonal systems of order 2 or 4 with pivoted Gaussian
elimination (and, for the strongest componentwise statement, refinement).
The older quasi/quasi endpoint used the literal no-pivot kernel and therefore
required caller-supplied `flGEPivots` and `flGEBudget`-domination hypotheses.

This file adds a different, operational surface.  A successful run chooses
row and column permutations, requires the pivot at every rounded Schur stage
to be a complete pivot in the sense of Chapter 9, runs the existing literal
rounded GE/block-back-substitution graph on the permuted system, and
unpermutes the answer.  The option result is `none` when no successful
rounded pivot trace exists.  From an equality `executor = some x`, the
nonbreakdown certificate and the actual elimination budget are derived from
the run; neither is a theorem hypothesis.

There is deliberately no theorem deriving success from exact nonsingularity
alone.  In the nondeterministic relative-error `FPModel`, an admissible
rounding of a sufficiently ill-conditioned nonsingular 2-by-2 system can
make its final rounded Schur pivot zero.  The PDF supplies neither a
quantitative no-collapse condition nor a precise refinement/fallback
algorithm.  Consequently the honest source-facing conclusion here is the
exact operational residual budget for successful 1/2/4-block runs.  Rounded
QR/real-Schur production remains the separate source-deferred prefix.
-/

/-! ## Complete-pivot traces for the existing rounded GE kernel -/

/-- The active-matrix complete-pivot predicate used here.  This is the
`k = 0` specialization of Chapter 9's complete-pivot choice: the selected
head entry has maximal absolute value in the whole current Schur stage. -/
def higham16CompletePivotChoice {n : Nat}
    (M : Fin n -> Fin n -> Real) (r s : Fin n) : Prop :=
  ∀ i j : Fin n, |M i j| ≤ |M r s|

/-- Aggregate row/column permutation, using the repository's
`IsPermutation` convention from the GEPP/complete-pivoting infrastructure. -/
def higham16RowColPermutedMatrix {n : Nat}
    (M : Fin n -> Fin n -> Real) (rowPerm colPerm : Fin n -> Fin n) :
    Fin n -> Fin n -> Real :=
  fun i j => M (rowPerm i) (colPerm j)

/-- At each rounded Schur stage, the head entry is nonzero and is a complete
pivot of the current active matrix.  A dynamic complete-pivoting run can be
encoded by first composing its row/column swaps and then applying the
existing no-pivot kernel to the permuted active block. -/
def flGECompletePivots (fp : FPModel) :
    (N : Nat) -> (Fin (N + 1) -> Fin (N + 1) -> Real) -> Prop
  | 0, M => M 0 0 ≠ 0
  | N + 1, M =>
      higham16CompletePivotChoice M 0 0 ∧
        M 0 0 ≠ 0 ∧ flGECompletePivots fp N (flGESchur fp M)

/-- A complete-pivot trace supplies the nonzero-computed-pivot certificate
consumed by `flGESolve_backward_error`. -/
theorem flGECompletePivots_to_flGEPivots (fp : FPModel) :
    ∀ (N : Nat) (M : Fin (N + 1) -> Fin (N + 1) -> Real),
      flGECompletePivots fp N M -> flGEPivots fp N M := by
  intro N
  induction N with
  | zero =>
      intro M h
      simpa [flGECompletePivots, flGEPivots] using h
  | succ N ih =>
      intro M h
      rw [flGECompletePivots] at h
      rw [flGEPivots]
      exact And.intro h.2.1 (ih _ h.2.2)

/-! ## A successful complete-pivot plan for a partitioned solve -/

/-- The data produced by a successful complete-permutation search for a
partitioned block-upper-triangular system.  `rowPerm` and `colPerm` are the
aggregate swaps.  The final two fields certify that the permuted system is
still block upper triangular and that every diagonal-block run has the
actual rounded complete-pivot trace.

The structure contains no budget hypothesis: the operational budget is the
definition `partitionBudget` evaluated on the matrix that was actually run.
-/
structure Higham16CompletePivotPartitionPlan (fp : FPModel) (N : Nat)
    (bs be : Fin N -> Nat) (T : Fin N -> Fin N -> Real) where
  rowPerm : Fin N -> Fin N
  colPerm : Fin N -> Fin N
  rowPerm_isPermutation : IsPermutation N rowPerm
  colPerm_isPermutation : IsPermutation N colPerm
  permuted_upper : ∀ a c : Fin N, c.val < bs a ->
    higham16RowColPermutedMatrix T rowPerm colPerm a c = 0
  completePivots : ∀ r : Fin N,
    flGECompletePivots fp (be r - bs r - 1)
      (blockSubCoeff N
        (higham16RowColPermutedMatrix T rowPerm colPerm)
        (bs r) (be r))

namespace Higham16CompletePivotPartitionPlan

variable {fp : FPModel} {N : Nat} {bs be : Fin N -> Nat}
  {T : Fin N -> Fin N -> Real}

/-- The row equivalence represented by the aggregate pivot swaps. -/
noncomputable def rowEquiv
    (p : Higham16CompletePivotPartitionPlan fp N bs be T) :
    Fin N ≃ Fin N :=
  Equiv.ofBijective p.rowPerm p.rowPerm_isPermutation

/-- The column equivalence represented by the aggregate pivot swaps. -/
noncomputable def colEquiv
    (p : Higham16CompletePivotPartitionPlan fp N bs be T) :
    Fin N ≃ Fin N :=
  Equiv.ofBijective p.colPerm p.colPerm_isPermutation

/-- The coefficient matrix on which the rounded block solver is run. -/
def permutedCoeff
    (p : Higham16CompletePivotPartitionPlan fp N bs be T) :
    Fin N -> Fin N -> Real :=
  higham16RowColPermutedMatrix T p.rowPerm p.colPerm

/-- The correspondingly row-permuted right-hand side. -/
def permutedRhs
    (p : Higham16CompletePivotPartitionPlan fp N bs be T)
    (bb : Fin N -> Real) : Fin N -> Real :=
  fun i => bb (p.rowPerm i)

/-- The raw permuted-coordinate output of the literal rounded partitioned
block back substitution. -/
noncomputable def rawSolution
    (p : Higham16CompletePivotPartitionPlan fp N bs be T)
    (bb : Fin N -> Real) : Fin N -> Real :=
  flPartitionBackSub fp N bs be p.permutedCoeff (p.permutedRhs bb)

/-- The computed solution returned in the original column ordering. -/
noncomputable def solution
    (p : Higham16CompletePivotPartitionPlan fp N bs be T)
    (bb : Fin N -> Real) : Fin N -> Real :=
  fun j => p.rawSolution bb (p.colEquiv.symm j)

/-- The actual `|Lhat||Uhat|`-shaped partition budget of the successful run,
transported back to the original row and column ordering. -/
noncomputable def operationalBudget
    (p : Higham16CompletePivotPartitionPlan fp N bs be T) :
    Fin N -> Fin N -> Real :=
  fun i j =>
    partitionBudget fp N bs be p.permutedCoeff
      (p.rowEquiv.symm i) (p.colEquiv.symm j)

end Higham16CompletePivotPartitionPlan

/-- Noncomputable finite complete-permutation search.  This returns a plan
exactly when an admissible aggregate row/column permutation has a successful
rounded complete-pivot trace on every diagonal block. -/
noncomputable def higham16CompletePivotPartitionPlan?
    (fp : FPModel) (N : Nat) (bs be : Fin N -> Nat)
    (T : Fin N -> Fin N -> Real) :
    Option (Higham16CompletePivotPartitionPlan fp N bs be T) := by
  classical
  exact
    if h : Nonempty (Higham16CompletePivotPartitionPlan fp N bs be T) then
      some (Classical.choice h)
    else none

/-- The actual pivoted partitioned solve.  `some x` exposes successful
execution; `none` records rounded pivot breakdown/no admissible plan. -/
noncomputable def flCompletePivotPartitionBackSub?
    (fp : FPModel) (N : Nat) (bs be : Fin N -> Nat)
    (T : Fin N -> Fin N -> Real) (bb : Fin N -> Real) :
    Option (Fin N -> Real) :=
  match higham16CompletePivotPartitionPlan? fp N bs be T with
  | none => none
  | some p => some (p.solution bb)

/-- The operational budget returned by the same pivot search as the solver.
It is an output, not a caller-supplied domination certificate. -/
noncomputable def flCompletePivotPartitionBudget?
    (fp : FPModel) (N : Nat) (bs be : Fin N -> Nat)
    (T : Fin N -> Fin N -> Real) :
    Option (Fin N -> Fin N -> Real) :=
  match higham16CompletePivotPartitionPlan? fp N bs be T with
  | none => none
  | some p => some p.operationalBudget

/-! ## Backward error and residual from successful execution -/

/-- A successful actual complete-pivot block run derives both nonbreakdown
and its elimination budget.  No `flGEPivots`, `flGEBudget`, or growth
domination is supplied by the caller. -/
theorem flCompletePivotPartitionBackSub?_backward_error
    (fp : FPModel) (N B : Nat) (bs be : Fin N -> Nat)
    (T : Fin N -> Fin N -> Real) (bb x : Fin N -> Real)
    (hpart : IsBlockPartitionFn N bs be)
    (hB : ∀ r : Fin N, be r - bs r ≤ B)
    (hgv : gammaValid fp (N + 5 * B))
    (hsolve : flCompletePivotPartitionBackSub? fp N bs be T bb = some x) :
    ∃ budget : Fin N -> Fin N -> Real,
      flCompletePivotPartitionBudget? fp N bs be T = some budget ∧
      ∃ DeltaT : Fin N -> Fin N -> Real,
        (∀ r c : Fin N,
          |DeltaT r c| ≤ gamma fp (N + 5 * B) * budget r c) ∧
        ∀ r : Fin N,
          (∑ c : Fin N, (T r c + DeltaT r c) * x c) = bb r := by
  classical
  cases hplan : higham16CompletePivotPartitionPlan? fp N bs be T with
  | none =>
      simp [flCompletePivotPartitionBackSub?, hplan] at hsolve
  | some p =>
      have hx : p.solution bb = x := by
        simpa [flCompletePivotPartitionBackSub?, hplan] using hsolve
      subst x
      have hpiv : ∀ r : Fin N,
          flGEPivots fp (be r - bs r - 1)
            (blockSubCoeff N p.permutedCoeff (bs r) (be r)) := by
        intro r
        exact flGECompletePivots_to_flGEPivots fp _ _ (p.completePivots r)
      obtain ⟨DeltaP, hDeltaP, hEqP⟩ :=
        flPartitionBackSub_backward_error fp N B bs be p.permutedCoeff
          (p.permutedRhs bb) hpart p.permuted_upper hpiv hB hgv
      let er : Fin N ≃ Fin N := p.rowEquiv
      let ec : Fin N ≃ Fin N := p.colEquiv
      let DeltaT : Fin N -> Fin N -> Real :=
        fun i j => DeltaP (er.symm i) (ec.symm j)
      refine Exists.intro p.operationalBudget ?_
      constructor
      · simp [flCompletePivotPartitionBudget?, hplan]
      refine Exists.intro DeltaT ?_
      constructor
      · intro i j
        simpa [DeltaT, Higham16CompletePivotPartitionPlan.operationalBudget,
          er, ec] using hDeltaP (er.symm i) (ec.symm j)
      · intro i
        have hrow := hEqP (er.symm i)
        have hrow_apply : p.rowPerm (er.symm i) = i := by
          change er (er.symm i) = i
          exact er.apply_symm_apply i
        let f : Fin N -> Real :=
          fun j => (T i j + DeltaT i j) * p.solution bb j
        calc
          (∑ j : Fin N, (T i j + DeltaT i j) * p.solution bb j)
              = ∑ j : Fin N, f (ec j) := by
                  simpa [f] using (Equiv.sum_comp ec f).symm
          _ = ∑ j : Fin N,
                (p.permutedCoeff (er.symm i) j +
                    DeltaP (er.symm i) j) * p.rawSolution bb j := by
              apply Finset.sum_congr rfl
              intro j _
              have hcol_perm : p.colEquiv j = p.colPerm j := rfl
              have hcol_inv_perm : p.colEquiv.symm (p.colPerm j) = j := by
                rw [← hcol_perm]
                exact p.colEquiv.symm_apply_apply j
              simp [f, DeltaT,
                Higham16CompletePivotPartitionPlan.solution,
                Higham16CompletePivotPartitionPlan.permutedCoeff,
                higham16RowColPermutedMatrix, er, ec, hrow_apply,
                hcol_perm, hcol_inv_perm]
          _ = p.permutedRhs bb (er.symm i) := hrow
          _ = bb i := by
            simp [Higham16CompletePivotPartitionPlan.permutedRhs,
              er, hrow_apply]

/-- Exact operational residual budget for a successful pivoted block run.
This is the normwise-safe alternative described after (16.8): it makes no
componentwise `budget <= (1+rho)|T|` claim. -/
theorem flCompletePivotPartitionBackSub?_operational_residual
    (fp : FPModel) (N B : Nat) (bs be : Fin N -> Nat)
    (T : Fin N -> Fin N -> Real) (bb x : Fin N -> Real)
    (hpart : IsBlockPartitionFn N bs be)
    (hB : ∀ r : Fin N, be r - bs r ≤ B)
    (hgv : gammaValid fp (N + 5 * B))
    (hsolve : flCompletePivotPartitionBackSub? fp N bs be T bb = some x) :
    ∃ budget : Fin N -> Fin N -> Real,
      flCompletePivotPartitionBudget? fp N bs be T = some budget ∧
      ∀ r : Fin N,
        |bb r - ∑ c : Fin N, T r c * x c| ≤
          gamma fp (N + 5 * B) *
            ∑ c : Fin N, budget r c * |x c| := by
  obtain ⟨budget, hbudget, DeltaT, hDeltaT, hEq⟩ :=
    flCompletePivotPartitionBackSub?_backward_error fp N B bs be T bb x
      hpart hB hgv hsolve
  refine Exists.intro budget (And.intro hbudget ?_)
  intro r
  have hdiff : bb r - (∑ c : Fin N, T r c * x c) =
      ∑ c : Fin N, DeltaT r c * x c := by
    have h := hEq r
    rw [← h, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [hdiff]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  rw [abs_mul]
  calc
    |DeltaT r c| * |x c| ≤
        (gamma fp (N + 5 * B) * budget r c) * |x c| :=
      mul_le_mul_of_nonneg_right (hDeltaT r c) (abs_nonneg _)
    _ = gamma fp (N + 5 * B) * (budget r c * |x c|) := by ring

/-- Summing the row residual bounds gives a literal normwise (`l1`) residual
certificate with an operational, run-produced budget. -/
theorem flCompletePivotPartitionBackSub?_operational_residual_sum
    (fp : FPModel) (N B : Nat) (bs be : Fin N -> Nat)
    (T : Fin N -> Fin N -> Real) (bb x : Fin N -> Real)
    (hpart : IsBlockPartitionFn N bs be)
    (hB : ∀ r : Fin N, be r - bs r ≤ B)
    (hgv : gammaValid fp (N + 5 * B))
    (hsolve : flCompletePivotPartitionBackSub? fp N bs be T bb = some x) :
    ∃ budget : Fin N -> Fin N -> Real,
      flCompletePivotPartitionBudget? fp N bs be T = some budget ∧
      (∑ r : Fin N, |bb r - ∑ c : Fin N, T r c * x c|) ≤
        gamma fp (N + 5 * B) *
          ∑ r : Fin N, ∑ c : Fin N, budget r c * |x c| := by
  obtain ⟨budget, hbudget, hrow⟩ :=
    flCompletePivotPartitionBackSub?_operational_residual fp N B bs be T bb x
      hpart hB hgv hsolve
  refine Exists.intro budget (And.intro hbudget ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun r _ => hrow r

/-! ## The actual 1/2/4 quasi/quasi Sylvester suffix -/

/-- Successful complete-pivot Bartels--Stewart block solve in the interleaved
Schur-coordinate ordering.  The diagonal systems selected by `bs`/`be` have
orders 1, 2, or 4. -/
noncomputable def flSylvesterQQCompletePivotSolveVec?
    (fp : FPModel) (m n : Nat) (dblR : Fin m -> Bool)
    (dblS : Fin n -> Bool) (hSp : IsQuasiBlockPairing n dblS)
    (R : RMatFn m m) (S : RMatFn n n) (Ct : RMatFn m n) :
    Option (Fin (n * m) -> Real) :=
  flCompletePivotPartitionBackSub? fp (n * m)
    (sylvesterQQBs m n dblR dblS hSp)
    (sylvesterQQBe m n dblR dblS hSp)
    (sylvesterQQBackSubCoeff m n dblS hSp R S)
    (sylvesterQQBackSubRhs m n dblS hSp Ct)

/-- Operational budget produced by the same successful Sylvester pivot
search as `flSylvesterQQCompletePivotSolveVec?`. -/
noncomputable def flSylvesterQQCompletePivotBudget?
    (fp : FPModel) (m n : Nat) (dblR : Fin m -> Bool)
    (dblS : Fin n -> Bool) (hSp : IsQuasiBlockPairing n dblS)
    (R : RMatFn m m) (S : RMatFn n n) :
    Option (Fin (n * m) -> Fin (n * m) -> Real) :=
  flCompletePivotPartitionBudget? fp (n * m)
    (sylvesterQQBs m n dblR dblS hSp)
    (sylvesterQQBe m n dblR dblS hSp)
    (sylvesterQQBackSubCoeff m n dblS hSp R S)

/-- Source-facing supplied-Schur suffix: from successful execution of the
actual complete-pivot 1/2/4-block route, derive the exact operational
residual budget in the printed `gamma_(mn+20)` class.  No per-block
`flGEPivots` or `flGEBudget` hypothesis appears. -/
theorem higham16_eq16_8_suppliedSchur_completePivot_operational_residual
    (fp : FPModel) (m n : Nat) (dblR : Fin m -> Bool)
    (dblS : Fin n -> Bool)
    (hRp : IsQuasiBlockPairing m dblR)
    (hSp : IsQuasiBlockPairing n dblS)
    (R : RMatFn m m) (S : RMatFn n n) (Ct : RMatFn m n)
    (z : Fin (n * m) -> Real)
    (hgv : gammaValid fp (n * m + 20))
    (hsolve : flSylvesterQQCompletePivotSolveVec? fp m n dblR dblS hSp
      R S Ct = some z) :
    ∃ budget : Fin (n * m) -> Fin (n * m) -> Real,
      flSylvesterQQCompletePivotBudget? fp m n dblR dblS hSp R S =
        some budget ∧
      ∀ r : Fin (n * m),
        |sylvesterQQBackSubRhs m n dblS hSp Ct r -
            ∑ c : Fin (n * m),
              sylvesterQQBackSubCoeff m n dblS hSp R S r c * z c| ≤
          gamma fp (n * m + 20) *
            ∑ c : Fin (n * m), budget r c * |z c| := by
  simpa [flSylvesterQQCompletePivotSolveVec?,
    flSylvesterQQCompletePivotBudget?] using
    (flCompletePivotPartitionBackSub?_operational_residual fp (n * m) 4
      (sylvesterQQBs m n dblR dblS hSp)
      (sylvesterQQBe m n dblR dblS hSp)
      (sylvesterQQBackSubCoeff m n dblS hSp R S)
      (sylvesterQQBackSubRhs m n dblS hSp Ct) z
      (sylvesterQQPartition_valid m n dblR dblS hRp hSp)
      (fun r => sylvesterQQBlockSize_le m n dblR dblS hSp r)
      (by simpa using hgv) hsolve)

/-- Normwise (`l1`) version of the supplied-Schur operational residual.
This is the strongest unconditional-on-growth result available from the
successful actual pivot run without inventing the PDF's unspecified
constant or refinement policy. -/
theorem higham16_eq16_8_suppliedSchur_completePivot_operational_residual_sum
    (fp : FPModel) (m n : Nat) (dblR : Fin m -> Bool)
    (dblS : Fin n -> Bool)
    (hRp : IsQuasiBlockPairing m dblR)
    (hSp : IsQuasiBlockPairing n dblS)
    (R : RMatFn m m) (S : RMatFn n n) (Ct : RMatFn m n)
    (z : Fin (n * m) -> Real)
    (hgv : gammaValid fp (n * m + 20))
    (hsolve : flSylvesterQQCompletePivotSolveVec? fp m n dblR dblS hSp
      R S Ct = some z) :
    ∃ budget : Fin (n * m) -> Fin (n * m) -> Real,
      flSylvesterQQCompletePivotBudget? fp m n dblR dblS hSp R S =
        some budget ∧
      (∑ r : Fin (n * m),
          |sylvesterQQBackSubRhs m n dblS hSp Ct r -
            ∑ c : Fin (n * m),
              sylvesterQQBackSubCoeff m n dblS hSp R S r c * z c|) ≤
        gamma fp (n * m + 20) *
          ∑ r : Fin (n * m),
            ∑ c : Fin (n * m), budget r c * |z c| := by
  simpa [flSylvesterQQCompletePivotSolveVec?,
    flSylvesterQQCompletePivotBudget?] using
    (flCompletePivotPartitionBackSub?_operational_residual_sum fp (n * m) 4
      (sylvesterQQBs m n dblR dblS hSp)
      (sylvesterQQBe m n dblR dblS hSp)
      (sylvesterQQBackSubCoeff m n dblS hSp R S)
      (sylvesterQQBackSubRhs m n dblS hSp Ct) z
      (sylvesterQQPartition_valid m n dblR dblS hRp hSp)
      (fun r => sylvesterQQBlockSize_le m n dblR dblS hSp r)
      (by simpa using hgv) hsolve)

/-! These aliases name the preceding results as the supplied-Schur solve
suffix used in the derivation of (16.9).  They do not include, or assert the
existence of, the rounded QR/real-Schur producer that precedes that suffix. -/

alias H16_eq16_8_9_suppliedSchur_completePivot_operational_residual :=
  higham16_eq16_8_suppliedSchur_completePivot_operational_residual

alias H16_eq16_8_9_suppliedSchur_completePivot_operational_residual_sum :=
  higham16_eq16_8_suppliedSchur_completePivot_operational_residual_sum

end Wave16

end NumStability
