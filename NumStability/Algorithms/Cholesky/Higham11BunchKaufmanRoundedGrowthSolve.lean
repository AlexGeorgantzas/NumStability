/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# Direct growth-to-solve closure for rounded Bunch--Kaufman

This module feeds the proved finite-precision `40 n` product-growth estimate
for the literal rounded executor into the computed-solve backward-error
theorem.  It does not assert the distinct exact-arithmetic `36 n` estimate
cited by Higham.
-/

import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedGrowth
import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedSolve

open scoped BigOperators

namespace NumStability

namespace Higham11RoundedBunchKaufmanExecution

/-- The direct computed-factor growth estimate, normalized by the actual
rounded-path growth factor at a positive input scale. -/
theorem flatAbsProduct_le_forty_mul_dimension_mul_roundedGrowthFactor
    (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2)
    (huSmall : 36 * fp.u <= (1 : Real) / 1000)
    {n : Nat} {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (hcompleted : exec.Completed) {Amax : Real} (hAmax : 0 < Amax)
    (i j : Fin n) :
    exec.flatAbsProduct i j <=
      40 * (n : Real) * exec.roundedGrowthFactor Amax * Amax := by
  calc
    exec.flatAbsProduct i j <=
        40 * (n : Real) * exec.roundedStageMax :=
      flatAbsProduct_le_forty_mul_dimension_mul_roundedStageMax
        hval9 hsmall9 huSmall exec hcompleted i j
    _ = 40 * (n : Real) * exec.roundedGrowthFactor Amax * Amax := by
      rw [roundedStageMax_eq_growthFactor_mul exec hAmax]
      ring

/-- Exact unpermutation of the direct computed-factor growth estimate. -/
theorem sourceFlatAbsProduct_le_forty_mul_dimension_mul_roundedGrowthFactor
    (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2)
    (huSmall : 36 * fp.u <= (1 : Real) / 1000)
    {n : Nat} {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (hcompleted : exec.Completed) {Amax : Real} (hAmax : 0 < Amax)
    (i j : Fin n) :
    exec.sourceFlatAbsProduct i j <=
      40 * (n : Real) * exec.roundedGrowthFactor Amax * Amax := by
  simpa [sourceFlatAbsProduct, unpermutedMatrix] using
    flatAbsProduct_le_forty_mul_dimension_mul_roundedGrowthFactor
      hval9 hsmall9 huSmall exec hcompleted hAmax
        (exec.permutation.symm i) (exec.permutation.symm j)

/-- Direct `40 n` normwise computed-solve conclusion in pivot coordinates.
The product-growth premise of the older interface has been eliminated; the
remaining middle-solve arguments are precisely the equation-(11.5)
certificate consumed by `computedSolve_backward_error`. -/
theorem computedSolve_backward_error_normwise_forty
    (hval3 : gammaValid fp 3) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2)
    (huSmall : 36 * fp.u <= (1 : Real) / 1000)
    {n : Nat} {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (hcompleted : exec.Completed) (b : Fin n -> Real)
    (hvaln : gammaValid fp n) (gammaMid Amax : Real)
    (hgammaMid : 0 <= gammaMid)
    (hAmax : forall i j : Fin n, |exec.permutedInput i j| <= Amax)
    (hAmaxPos : 0 < Amax)
    (w_hat : Fin n -> Real) (DeltaD : Fin n -> Fin n -> Real)
    (hDeltaD : forall i j : Fin n,
      |DeltaD i j| <= gammaMid * |exec.flatD i j|)
    (hmiddle : forall p : Fin n,
      (∑ q : Fin n, (exec.flatD p q + DeltaD p q) * w_hat q) =
        fl_forwardSub fp n exec.flatL b p) :
    exists DeltaA2 : Fin n -> Fin n -> Real,
      (forall i j : Fin n,
        |DeltaA2 i j| <=
          exec.finiteResidualCoefficient *
              ((1 + 40 * (n : Real) * exec.roundedGrowthFactor Amax) * Amax) +
            solveResidualCoefficient fp n gammaMid *
              (40 * (n : Real) * exec.roundedGrowthFactor Amax * Amax)) /\
      (forall i : Fin n,
        ∑ j : Fin n,
          (exec.permutedInput i j + DeltaA2 i j) *
              fl_backSub fp n (fun r c => exec.flatL c r) w_hat j = b i) := by
  obtain ⟨DeltaA2, hDeltaA2, hsolve⟩ := computedSolve_backward_error
    hval3 hval9 hsmall9 exec hcompleted b hvaln gammaMid hgammaMid
      w_hat DeltaD hDeltaD hmiddle
  refine ⟨DeltaA2, ?_, hsolve⟩
  have hC : 0 <= exec.finiteResidualCoefficient :=
    finiteResidualCoefficient_nonneg hval3 exec
  have hS : 0 <= solveResidualCoefficient fp n gammaMid :=
    solveResidualCoefficient_nonneg hvaln hgammaMid
  intro i j
  have hgrowth :=
    flatAbsProduct_le_forty_mul_dimension_mul_roundedGrowthFactor
      hval9 hsmall9 huSmall exec hcompleted hAmaxPos i j
  have hfactorInput :
      |exec.permutedInput i j| + exec.flatAbsProduct i j <=
        (1 + 40 * (n : Real) * exec.roundedGrowthFactor Amax) * Amax := by
    calc
      |exec.permutedInput i j| + exec.flatAbsProduct i j <=
          Amax + 40 * (n : Real) * exec.roundedGrowthFactor Amax * Amax :=
        add_le_add (hAmax i j) hgrowth
      _ = (1 + 40 * (n : Real) * exec.roundedGrowthFactor Amax) * Amax := by
        ring
  exact le_trans (hDeltaA2 i j)
    (add_le_add
      (mul_le_mul_of_nonneg_left hfactorInput hC)
      (mul_le_mul_of_nonneg_left hgrowth hS))

/-- Direct `40 n` normwise computed-solve conclusion in the original source
coordinates.  Both the matrix maximum bound and returned solve equation are
stated without pivot-coordinate exposure. -/
theorem computedSolve_backward_error_normwise_forty_source
    (hval3 : gammaValid fp 3) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2)
    (huSmall : 36 * fp.u <= (1 : Real) / 1000)
    {n : Nat} {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (hcompleted : exec.Completed) (b : Fin n -> Real)
    (hvaln : gammaValid fp n) (gammaMid Amax : Real)
    (hgammaMid : 0 <= gammaMid)
    (hAmax : forall i j : Fin n, |A i j| <= Amax)
    (hAmaxPos : 0 < Amax)
    (w_hat : Fin n -> Real) (DeltaD : Fin n -> Fin n -> Real)
    (hDeltaD : forall i j : Fin n,
      |DeltaD i j| <= gammaMid * |exec.flatD i j|)
    (hmiddle : forall p : Fin n,
      (∑ q : Fin n, (exec.flatD p q + DeltaD p q) * w_hat q) =
        fl_forwardSub fp n exec.flatL
          (fun i => b (exec.permutation i)) p) :
    exists DeltaA2 : Fin n -> Fin n -> Real,
      (forall i j : Fin n,
        |DeltaA2 i j| <=
          exec.finiteResidualCoefficient *
              ((1 + 40 * (n : Real) * exec.roundedGrowthFactor Amax) * Amax) +
            solveResidualCoefficient fp n gammaMid *
              (40 * (n : Real) * exec.roundedGrowthFactor Amax * Amax)) /\
      (forall i : Fin n,
        ∑ j : Fin n,
          (A i j + DeltaA2 i j) *
            exec.unpermutedVector
              (fl_backSub fp n (fun r c => exec.flatL c r) w_hat) j = b i) := by
  obtain ⟨DeltaA2, hDeltaA2, hsolve⟩ := computedSolve_backward_error_source
    hval3 hval9 hsmall9 exec hcompleted b hvaln gammaMid hgammaMid
      w_hat DeltaD hDeltaD hmiddle
  refine ⟨DeltaA2, ?_, hsolve⟩
  have hC : 0 <= exec.finiteResidualCoefficient :=
    finiteResidualCoefficient_nonneg hval3 exec
  have hS : 0 <= solveResidualCoefficient fp n gammaMid :=
    solveResidualCoefficient_nonneg hvaln hgammaMid
  intro i j
  have hgrowth :=
    sourceFlatAbsProduct_le_forty_mul_dimension_mul_roundedGrowthFactor
      hval9 hsmall9 huSmall exec hcompleted hAmaxPos i j
  have hfactorInput :
      |A i j| + exec.sourceFlatAbsProduct i j <=
        (1 + 40 * (n : Real) * exec.roundedGrowthFactor Amax) * Amax := by
    calc
      |A i j| + exec.sourceFlatAbsProduct i j <=
          Amax + 40 * (n : Real) * exec.roundedGrowthFactor Amax * Amax :=
        add_le_add (hAmax i j) hgrowth
      _ = (1 + 40 * (n : Real) * exec.roundedGrowthFactor Amax) * Amax := by
        ring
  exact le_trans (hDeltaA2 i j)
    (add_le_add
      (mul_le_mul_of_nonneg_left hfactorInput hC)
      (mul_le_mul_of_nonneg_left hgrowth hS))

end Higham11RoundedBunchKaufmanExecution

end NumStability
