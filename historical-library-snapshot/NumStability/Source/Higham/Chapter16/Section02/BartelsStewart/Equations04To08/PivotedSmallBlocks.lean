import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.PivotedSmallBlocks.CompletePivot
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.QuasiTriangularSolve
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.SmallSystemRounding
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Source.Higham.Chapter16.Section02.BartelsStewart.Equations04To08.PivotedSmallBlocks

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/



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










































/-! ## A successful complete-pivot plan for a partitioned solve -/
























namespace Higham16CompletePivotPartitionPlan

variable {fp : FPModel} {N : Nat} {bs be : Fin N -> Nat}
  {T : Fin N -> Fin N -> Real}















































end Higham16CompletePivotPartitionPlan


































/-! ## Backward error and residual from successful execution -/









































































































































/-! ## The actual 1/2/4 quasi/quasi Sylvester suffix -/



























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
