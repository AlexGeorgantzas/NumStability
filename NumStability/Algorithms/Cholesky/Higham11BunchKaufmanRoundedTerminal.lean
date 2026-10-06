/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# Terminal rounded Bunch--Kaufman solve theorem for Higham Chapter 11

This module joins the literal block-diagonal middle solver to the proved
finite-precision `40 n` factor-growth estimate.  Consequently the public
solve theorems below assume neither a product-growth estimate nor an
equation-(11.5) middle-solve certificate: both are derived from the actual
rounded execution.
-/

import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedGrowthSolve
import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedMiddleSolve

open scoped BigOperators

namespace NumStability

namespace Higham11RoundedBunchKaufmanExecution

/-- The literal rounded Bunch--Kaufman factorization and solve, in pivot
coordinates, has a normwise backward error with the proved computed-factor
constant `40 n`.  The middle solution and its perturbation are constructed
from the actual scalar and selected two-by-two block solvers. -/
theorem computedSolve_backward_error_normwise_forty_actual
    (hval3 : gammaValid fp 3) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2)
    (huSmall : 36 * fp.u <= (1 : Real) / 1000)
    {n : Nat} {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (hcompleted : exec.Completed)
    (hmiddleDomain : exec.MiddleSolveRunDomain)
    (b : Fin n -> Real) (hvaln : gammaValid fp n) (Amax : Real)
    (hAmax : forall i j : Fin n, |exec.permutedInput i j| <= Amax)
    (hAmaxPos : 0 < Amax) :
    exists (w_hat : Fin n -> Real)
      (DeltaD DeltaA2 : Fin n -> Fin n -> Real),
      (forall i j : Fin n,
        |DeltaD i j| <= 36 * fp.u * |exec.flatD i j|) /\
      (forall p : Fin n,
        (∑ q : Fin n, (exec.flatD p q + DeltaD p q) * w_hat q) =
          fl_forwardSub fp n exec.flatL b p) /\
      (forall i j : Fin n,
        |DeltaA2 i j| <=
          exec.finiteResidualCoefficient *
              ((1 + 40 * (n : Real) * exec.roundedGrowthFactor Amax) * Amax) +
            solveResidualCoefficient fp n (36 * fp.u) *
              (40 * (n : Real) * exec.roundedGrowthFactor Amax * Amax)) /\
      (forall i : Fin n,
        ∑ j : Fin n,
          (exec.permutedInput i j + DeltaA2 i j) *
              fl_backSub fp n (fun r c => exec.flatL c r) w_hat j = b i) := by
  obtain ⟨w_hat, DeltaD, hDeltaD, hmiddle⟩ :=
    actualMiddleSolve_backward_error hval9 hsmall9 exec hmiddleDomain
      (fl_forwardSub fp n exec.flatL b)
  have hgammaMid : 0 <= 36 * fp.u :=
    mul_nonneg (by norm_num) fp.u_nonneg
  obtain ⟨DeltaA2, hDeltaA2, hsolve⟩ :=
    computedSolve_backward_error_normwise_forty
      hval3 hval9 hsmall9 huSmall exec hcompleted b hvaln
        (36 * fp.u) Amax hgammaMid hAmax hAmaxPos
        w_hat DeltaD hDeltaD hmiddle
  exact ⟨w_hat, DeltaD, DeltaA2, hDeltaD, hmiddle, hDeltaA2, hsolve⟩

/-- Source-coordinate form of
`computedSolve_backward_error_normwise_forty_actual`.  The matrix bound,
right-hand side, returned solution, and perturbation equation are all stated
in the original coordinates, while the pivoting permutation is confined to
the implementation of the solve. -/
theorem computedSolve_backward_error_normwise_forty_actual_source
    (hval3 : gammaValid fp 3) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2)
    (huSmall : 36 * fp.u <= (1 : Real) / 1000)
    {n : Nat} {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (hcompleted : exec.Completed)
    (hmiddleDomain : exec.MiddleSolveRunDomain)
    (b : Fin n -> Real) (hvaln : gammaValid fp n) (Amax : Real)
    (hAmax : forall i j : Fin n, |A i j| <= Amax)
    (hAmaxPos : 0 < Amax) :
    exists (w_hat : Fin n -> Real)
      (DeltaD DeltaA2 : Fin n -> Fin n -> Real),
      (forall i j : Fin n,
        |DeltaD i j| <= 36 * fp.u * |exec.flatD i j|) /\
      (forall p : Fin n,
        (∑ q : Fin n, (exec.flatD p q + DeltaD p q) * w_hat q) =
          fl_forwardSub fp n exec.flatL
            (fun i => b (exec.permutation i)) p) /\
      (forall i j : Fin n,
        |DeltaA2 i j| <=
          exec.finiteResidualCoefficient *
              ((1 + 40 * (n : Real) * exec.roundedGrowthFactor Amax) * Amax) +
            solveResidualCoefficient fp n (36 * fp.u) *
              (40 * (n : Real) * exec.roundedGrowthFactor Amax * Amax)) /\
      (forall i : Fin n,
        ∑ j : Fin n,
          (A i j + DeltaA2 i j) *
            exec.unpermutedVector
              (fl_backSub fp n (fun r c => exec.flatL c r) w_hat) j = b i) := by
  obtain ⟨w_hat, DeltaD, hDeltaD, hmiddle⟩ :=
    actualMiddleSolve_backward_error hval9 hsmall9 exec hmiddleDomain
      (fl_forwardSub fp n exec.flatL (fun i => b (exec.permutation i)))
  have hgammaMid : 0 <= 36 * fp.u :=
    mul_nonneg (by norm_num) fp.u_nonneg
  obtain ⟨DeltaA2, hDeltaA2, hsolve⟩ :=
    computedSolve_backward_error_normwise_forty_source
      hval3 hval9 hsmall9 huSmall exec hcompleted b hvaln
        (36 * fp.u) Amax hgammaMid hAmax hAmaxPos
        w_hat DeltaD hDeltaD hmiddle
  exact ⟨w_hat, DeltaD, DeltaA2, hDeltaD, hmiddle, hDeltaA2, hsolve⟩

end Higham11RoundedBunchKaufmanExecution

end NumStability
