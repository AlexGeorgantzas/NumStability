/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# Exact-arithmetic completion for the literal Bunch--Kaufman producer

The rounded execution is also an exact execution when its floating-point
model has unit roundoff zero and every primitive is interpreted exactly.
This module proves that the total producer cannot take its explicit
two-by-two breakdown branch in that model.  The proof uses the nonsingularity
of the pivot selected by Algorithm 11.2, rather than assuming completion.
-/

import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedExecution

namespace NumStability

/-- Exact real arithmetic, exposed through the same primitive interface as
the literal rounded Algorithm 11.2 producer. -/
noncomputable def higham11_2_bunchKaufmanExactArithmeticFP : FPModel :=
  FPModel.exactWithUnitRoundoff 0 (by norm_num)

/-- At an Algorithm 11.2 case-(4) stage, the exact-arithmetic GEPP kernel's
computed second pivot is nonzero.  This is derived from the selector's
nonsingular-pivot theorem and exact division by its nonzero first pivot. -/
theorem higham11_2_bunchKaufmanExactArithmetic_secondPivot_ne_zero {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A)
    (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4) :
    higham11_2_flSelectedTwoByTwoSecondPivot
      higham11_2_bunchKaufmanExactArithmeticFP (by omega) A ≠ 0 := by
  let i0 := higham11_2_firstIndex (show 0 < n + 2 by omega)
  let r := higham11_2_bunchKaufmanMaxRow (show 0 < n + 2 by omega) A
  have hcase := higham11_2_bunchKaufmanFirstBranch_spec
    (show 0 < n + 2 by omega) higham11_1_bunchParlettAlpha A
  rw [hbranch] at hcase
  have hattain : |A r i0| =
      higham11_2_bunchKaufmanOmegaOne (show 0 < n + 2 by omega) A := by
    simpa [i0, r] using
      (higham11_2_bunchKaufmanMaxRow_attains_omegaOne
        (show 0 < n + 2 by omega) A hcase.1)
  have hpivot : A r i0 ≠ 0 := by
    intro hpivot0
    apply hcase.1
    rw [<- hattain, hpivot0, abs_zero]
  have hdet : A i0 i0 * A r r - A r i0 ^ 2 ≠ 0 := by
    simpa [i0, r] using
      (higham11_2_bunchKaufmanCase4_det_ne_zero
        (show 0 < n + 2 by omega) A hbranch)
  intro hsecond
  change A i0 r - A i0 i0 / A r i0 * A r r = 0 at hsecond
  rw [hA i0 r] at hsecond
  apply hdet
  field_simp [hpivot] at hsecond
  nlinarith

namespace Higham11RoundedBunchKaufmanExecution

/-- Every literal execution in exact arithmetic completes: the explicit
breakdown constructor contradicts the exact selected-pivot lemma above. -/
theorem completed_exactArithmetic : forall {n : Nat}
    {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution
      higham11_2_bunchKaufmanExactArithmeticFP A), exec.Completed := by
  intro n A exec
  induction exec with
  | nil => trivial
  | noAction A hA hbranch tail ih => exact ih
  | case1 A hA hbranch tail ih => exact ih
  | case2 A hA hbranch tail ih => exact ih
  | case3 A hA hbranch tail ih => exact ih
  | case4 A hA hbranch hsecond tail ih => exact ih
  | case4Breakdown A hA hbranch hsecond =>
      exact (higham11_2_bunchKaufmanExactArithmetic_secondPivot_ne_zero
        A hA hbranch) hsecond

end Higham11RoundedBunchKaufmanExecution

/-- Canonical, choice-fixed, literal Algorithm 11.2 producer in exact real
arithmetic. -/
noncomputable def higham11_2_exactArithmeticBunchKaufmanExecution {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix n)
    (hA : IsSymmetricFiniteMatrix A) :
    Higham11RoundedBunchKaufmanExecution
      higham11_2_bunchKaufmanExactArithmeticFP A :=
  higham11_2_roundedBunchKaufmanExecution
    higham11_2_bunchKaufmanExactArithmeticFP A hA

/-- The canonical exact-arithmetic producer always completes. -/
theorem higham11_2_exactArithmeticBunchKaufmanExecution_completed {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix n)
    (hA : IsSymmetricFiniteMatrix A) :
    (higham11_2_exactArithmeticBunchKaufmanExecution A hA).Completed :=
  Higham11RoundedBunchKaufmanExecution.completed_exactArithmetic _

end NumStability
