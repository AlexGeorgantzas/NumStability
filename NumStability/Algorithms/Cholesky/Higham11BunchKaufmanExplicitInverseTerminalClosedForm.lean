/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# Closed-form terminal bounds for the explicit-inverse pivot solve

This module carries the actual scaled explicit-inverse implementation for
Algorithm 11.2 all the way to the source-coordinate endpoint of Theorem 11.4.
The local two-by-two solve contributes `360u`, the finite factorization path
coefficient is replaced by a dimension-only bound, and the final result is
an exact linear term plus an explicit quadratic remainder.

Sources: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
Problems 11.2 and 11.5 and Theorems 11.3--11.4, pp. 218--219; Higham,
"Stability of the Diagonal Pivoting Method with Partial Pivoting" (1997),
equations (4.3)--(4.5).
-/

import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanExplicitInverseSolve
import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedTerminalClosedForm

open scoped BigOperators

namespace NumStability

namespace Higham11RoundedBunchKaufmanExecution

/-- With the actual explicit-inverse middle solve, the solve-chain coefficient
has an exact linear bound and an explicit quadratic remainder.  The larger
constants relative to the GEPP arm come solely from the source-faithful
`gamma_180 <= 360u` local certificate. -/
theorem solveResidualCoefficient_threeHundredSixty_mul_u_le_linear_add_quadratic
    (fp : FPModel) (n : Nat) (hvaln : gammaValid fp n)
    (hhalf : (n : Real) * fp.u <= 1 / 2) (huOne : fp.u <= 1) :
    solveResidualCoefficient fp n (360 * fp.u) <=
      (4 * (n : Real) + 360) * fp.u +
        (1444 * (n : Real) ^ 2 + 1440 * (n : Real)) * fp.u ^ 2 := by
  let N : Real := n
  let u : Real := fp.u
  let g : Real := gamma fp n
  have hN0 : 0 <= N := by simp [N]
  have hu0 : 0 <= u := by simpa [u] using fp.u_nonneg
  have hg0 : 0 <= g := by simpa [g] using gamma_nonneg fp hvaln
  have hg : g <= 2 * N * u := by
    simpa [g, N, u, mul_assoc] using
      gamma_le_two_mul_n_u_of_nu_le_half fp n hhalf
  have hgsq : g ^ 2 <= 4 * N ^ 2 * u ^ 2 := by nlinarith
  have hgu : 720 * g * u <= 1440 * N * u ^ 2 := by nlinarith
  have huSq : u ^ 3 <= u ^ 2 := by nlinarith [sq_nonneg u]
  have hgsqu : 360 * g ^ 2 * u <= 1440 * N ^ 2 * u ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hgsq hu0
    have hN2 : 0 <= N ^ 2 := sq_nonneg N
    nlinarith [mul_le_mul_of_nonneg_left huSq
      (mul_nonneg (by norm_num : (0 : Real) <= 1440) hN2)]
  change (2 * g + g ^ 2) + (1 + 2 * g + g ^ 2) * (360 * u) <= _
  calc
    (2 * g + g ^ 2) + (1 + 2 * g + g ^ 2) * (360 * u)
        = 2 * g + 360 * u + g ^ 2 + 720 * g * u +
            360 * g ^ 2 * u := by ring
    _ <= 4 * N * u + 360 * u +
          4 * N ^ 2 * u ^ 2 + 1440 * N * u ^ 2 +
            1440 * N ^ 2 * u ^ 2 := by nlinarith
    _ = (4 * N + 360) * u +
          (1444 * N ^ 2 + 1440 * N) * u ^ 2 := by ring

private theorem explicitInverse_terminal_input_envelope_nonneg {n : Nat}
    {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A) (Amax : Real)
    (hAmaxPos : 0 < Amax) :
    0 <= (1 + 40 * (n : Real) * exec.roundedGrowthFactor Amax) * Amax := by
  have hstage : 0 <= exec.roundedStageMax := roundedStageMax_nonneg exec
  have hscale := roundedStageMax_eq_growthFactor_mul exec hAmaxPos
  calc
    0 <= Amax + 40 * (n : Real) * exec.roundedStageMax := by positivity
    _ = (1 + 40 * (n : Real) * exec.roundedGrowthFactor Amax) * Amax := by
      rw [hscale]
      ring

/-- Dimension-only pivot-coordinate terminal for the actual scaled
explicit-inverse arm.  The result contains neither `Completed` nor the
path-dependent `finiteResidualCoefficient` as a premise or output bound. -/
theorem computedSolve_backward_error_normwise_forty_actual_explicitInverse_dimension
    (hval3 : gammaValid fp 3) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2)
    (huSmall : 36 * fp.u <= (1 : Real) / 1000)
    {n : Nat} {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (hmiddleDomain : exec.MiddleSolveRunDomain)
    (b : Fin n -> Real) (hvaln : gammaValid fp n) (Amax : Real)
    (hAmax : forall i j : Fin n, |exec.permutedInput i j| <= Amax)
    (hAmaxPos : 0 < Amax) :
    exists (w_hat : Fin n -> Real)
      (DeltaD DeltaA2 : Fin n -> Fin n -> Real),
      (forall i j : Fin n,
        |DeltaD i j| <= 360 * fp.u * |exec.flatD i j|) /\
      (forall p : Fin n,
        (∑ q : Fin n, (exec.flatD p q + DeltaD p q) * w_hat q) =
          fl_forwardSub fp n exec.flatL b p) /\
      (forall i j : Fin n,
        |DeltaA2 i j| <=
          dimensionResidualCoefficient fp n *
              ((1 + 40 * (n : Real) * exec.roundedGrowthFactor Amax) * Amax) +
            solveResidualCoefficient fp n (360 * fp.u) *
              (40 * (n : Real) * exec.roundedGrowthFactor Amax * Amax)) /\
      (forall i : Fin n,
        ∑ j : Fin n,
          (exec.permutedInput i j + DeltaA2 i j) *
              fl_backSub fp n (fun r c => exec.flatL c r) w_hat j = b i) := by
  obtain ⟨w_hat, DeltaD, DeltaA2, hD, hmiddle, hA2, hsolve⟩ :=
    computedSolve_backward_error_normwise_forty_actual_explicitInverse
      hval3 hval9 hsmall9 huSmall exec hmiddleDomain b hvaln
        Amax hAmax hAmaxPos
  refine ⟨w_hat, DeltaD, DeltaA2, hD, hmiddle, ?_, hsolve⟩
  intro i j
  refine (hA2 i j).trans ?_
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right
    · exact finiteResidualCoefficient_le_dimensionResidualCoefficient
        hval3 exec hmiddleDomain
    · exact explicitInverse_terminal_input_envelope_nonneg exec Amax hAmaxPos
  · exact le_rfl

/-- Source-coordinate dimension-only terminal for the actual scaled
explicit-inverse arm. -/
theorem computedSolve_backward_error_normwise_forty_actual_explicitInverse_source_dimension
    (hval3 : gammaValid fp 3) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2)
    (huSmall : 36 * fp.u <= (1 : Real) / 1000)
    {n : Nat} {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (hmiddleDomain : exec.MiddleSolveRunDomain)
    (b : Fin n -> Real) (hvaln : gammaValid fp n) (Amax : Real)
    (hAmax : forall i j : Fin n, |A i j| <= Amax)
    (hAmaxPos : 0 < Amax) :
    exists (w_hat : Fin n -> Real)
      (DeltaD DeltaA2 : Fin n -> Fin n -> Real),
      (forall i j : Fin n,
        |DeltaD i j| <= 360 * fp.u * |exec.flatD i j|) /\
      (forall p : Fin n,
        (∑ q : Fin n, (exec.flatD p q + DeltaD p q) * w_hat q) =
          fl_forwardSub fp n exec.flatL
            (fun i => b (exec.permutation i)) p) /\
      (forall i j : Fin n,
        |DeltaA2 i j| <=
          dimensionResidualCoefficient fp n *
              ((1 + 40 * (n : Real) * exec.roundedGrowthFactor Amax) * Amax) +
            solveResidualCoefficient fp n (360 * fp.u) *
              (40 * (n : Real) * exec.roundedGrowthFactor Amax * Amax)) /\
      (forall i : Fin n,
        ∑ j : Fin n,
          (A i j + DeltaA2 i j) *
            exec.unpermutedVector
              (fl_backSub fp n (fun r c => exec.flatL c r) w_hat) j = b i) := by
  obtain ⟨w_hat, DeltaD, DeltaA2, hD, hmiddle, hA2, hsolve⟩ :=
    computedSolve_backward_error_normwise_forty_actual_explicitInverse_source
      hval3 hval9 hsmall9 huSmall exec hmiddleDomain b hvaln
        Amax hAmax hAmaxPos
  refine ⟨w_hat, DeltaD, DeltaA2, hD, hmiddle, ?_, hsolve⟩
  intro i j
  refine (hA2 i j).trans ?_
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right
    · exact finiteResidualCoefficient_le_dimensionResidualCoefficient
        hval3 exec hmiddleDomain
    · exact explicitInverse_terminal_input_envelope_nonneg exec Amax hAmaxPos
  · exact le_rfl

/-- Source-facing terminal at the literal max-entry input norm.  Its growth
factor is exactly the source ratio `rho_n`, not a ratio based on an arbitrary
upper scale. -/
theorem computedSolve_backward_error_normwise_forty_actual_explicitInverse_source_maxEntryNorm
    (hval3 : gammaValid fp 3) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2)
    (huSmall : 36 * fp.u <= (1 : Real) / 1000)
    {n : Nat} {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (hmiddleDomain : exec.MiddleSolveRunDomain)
    (b : Fin n -> Real) (hvaln : gammaValid fp n)
    (hAmaxPos : 0 < higham11_4_roundedActiveMax A) :
    exists (w_hat : Fin n -> Real)
      (DeltaD DeltaA2 : Fin n -> Fin n -> Real),
      (forall i j : Fin n,
        |DeltaD i j| <= 360 * fp.u * |exec.flatD i j|) /\
      (forall p : Fin n,
        (∑ q : Fin n, (exec.flatD p q + DeltaD p q) * w_hat q) =
          fl_forwardSub fp n exec.flatL
            (fun i => b (exec.permutation i)) p) /\
      (forall i j : Fin n,
        |DeltaA2 i j| <=
          dimensionResidualCoefficient fp n *
              ((1 + 40 * (n : Real) *
                  exec.roundedGrowthFactor (higham11_4_roundedActiveMax A)) *
                higham11_4_roundedActiveMax A) +
            solveResidualCoefficient fp n (360 * fp.u) *
              (40 * (n : Real) *
                exec.roundedGrowthFactor (higham11_4_roundedActiveMax A) *
                higham11_4_roundedActiveMax A)) /\
      (forall i : Fin n,
        ∑ j : Fin n,
          (A i j + DeltaA2 i j) *
            exec.unpermutedVector
              (fl_backSub fp n (fun r c => exec.flatL c r) w_hat) j = b i) := by
  exact
    computedSolve_backward_error_normwise_forty_actual_explicitInverse_source_dimension
      hval3 hval9 hsmall9 huSmall exec hmiddleDomain b hvaln
        (higham11_4_roundedActiveMax A)
        (fun i j => higham11_4_entry_le_roundedActiveMax A i j) hAmaxPos

/-- Exact finite-`u` first-order-plus-quadratic source theorem for the actual
scaled explicit-inverse arm.  For fixed `n`, the displayed second summand is
an explicit `O(u^2)` remainder; no asymptotic premise is hidden. -/
theorem computedSolve_backward_error_normwise_forty_actual_explicitInverse_source_firstOrder
    (hval3 : gammaValid fp 3) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2)
    (huSmall : 36 * fp.u <= (1 : Real) / 1000)
    {n : Nat} {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (hmiddleDomain : exec.MiddleSolveRunDomain)
    (b : Fin n -> Real) (hvaln : gammaValid fp n)
    (hAmaxPos : 0 < higham11_4_roundedActiveMax A)
    (hCoeffSmall : 108 * (n : Real) * fp.u <= 1 / 2)
    (huOne : fp.u <= 1) :
    exists (w_hat : Fin n -> Real)
      (DeltaD DeltaA2 : Fin n -> Fin n -> Real),
      (forall i j : Fin n,
        |DeltaD i j| <= 360 * fp.u * |exec.flatD i j|) /\
      (forall p : Fin n,
        (∑ q : Fin n, (exec.flatD p q + DeltaD p q) * w_hat q) =
          fl_forwardSub fp n exec.flatL
            (fun i => b (exec.permutation i)) p) /\
      (forall i j : Fin n,
        |DeltaA2 i j| <=
          216 * (n : Real) * fp.u *
              ((1 + 40 * (n : Real) *
                  exec.roundedGrowthFactor (higham11_4_roundedActiveMax A)) *
                higham11_4_roundedActiveMax A) +
            ((4 * (n : Real) + 360) * fp.u +
                (1444 * (n : Real) ^ 2 + 1440 * (n : Real)) * fp.u ^ 2) *
              (40 * (n : Real) *
                exec.roundedGrowthFactor (higham11_4_roundedActiveMax A) *
                higham11_4_roundedActiveMax A)) /\
      (forall i : Fin n,
        ∑ j : Fin n,
          (A i j + DeltaA2 i j) *
            exec.unpermutedVector
              (fl_backSub fp n (fun r c => exec.flatL c r) w_hat) j = b i) := by
  obtain ⟨w_hat, DeltaD, DeltaA2, hD, hmiddle, hA2, hsolve⟩ :=
    computedSolve_backward_error_normwise_forty_actual_explicitInverse_source_maxEntryNorm
      hval3 hval9 hsmall9 huSmall exec hmiddleDomain b hvaln hAmaxPos
  refine ⟨w_hat, DeltaD, DeltaA2, hD, hmiddle, ?_, hsolve⟩
  intro i j
  refine (hA2 i j).trans ?_
  have hK :=
    dimensionResidualCoefficient_le_twoHundredSixteen_mul_dimension_mul_u
      fp n hval3 hCoeffSmall
  have hS :=
    solveResidualCoefficient_threeHundredSixty_mul_u_le_linear_add_quadratic
      fp n hvaln (by
        have hn108 : (n : Real) * fp.u <= 108 * (n : Real) * fp.u := by
          nlinarith [fp.u_nonneg,
            show (0 : Real) <= (n : Real) by positivity]
        linarith) huOne
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right hK
      (explicitInverse_terminal_input_envelope_nonneg exec _ hAmaxPos)
  · apply mul_le_mul_of_nonneg_right hS
    have hstage : 0 <= exec.roundedStageMax := roundedStageMax_nonneg exec
    have hscale := roundedStageMax_eq_growthFactor_mul exec hAmaxPos
    rw [hscale] at hstage
    calc
      0 <= (40 * (n : Real)) *
          (exec.roundedGrowthFactor (higham11_4_roundedActiveMax A) *
            higham11_4_roundedActiveMax A) := by positivity
      _ = 40 * (n : Real) *
          exec.roundedGrowthFactor (higham11_4_roundedActiveMax A) *
            higham11_4_roundedActiveMax A := by ring

/-- Literal `p(n) rho_n u ||A||_M + C(n) rho_n u^2 ||A||_M` endpoint for
the explicit-inverse alternative in Theorem 11.4. -/
theorem computedSolve_backward_error_normwise_forty_actual_explicitInverse_source_polynomial
    (hval3 : gammaValid fp 3) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2)
    (huSmall : 36 * fp.u <= (1 : Real) / 1000)
    {n : Nat} {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (hmiddleDomain : exec.MiddleSolveRunDomain)
    (b : Fin n -> Real) (hvaln : gammaValid fp n)
    (hAmaxPos : 0 < higham11_4_roundedActiveMax A)
    (hCoeffSmall : 108 * (n : Real) * fp.u <= 1 / 2)
    (huOne : fp.u <= 1) :
    exists (w_hat : Fin n -> Real)
      (DeltaD DeltaA2 : Fin n -> Fin n -> Real),
      (forall i j : Fin n,
        |DeltaD i j| <= 360 * fp.u * |exec.flatD i j|) /\
      (forall p : Fin n,
        (∑ q : Fin n, (exec.flatD p q + DeltaD p q) * w_hat q) =
          fl_forwardSub fp n exec.flatL
            (fun i => b (exec.permutation i)) p) /\
      (forall i j : Fin n,
        |DeltaA2 i j| <=
          (216 * (n : Real) * (1 + 40 * (n : Real)) +
              40 * (n : Real) * (4 * (n : Real) + 360)) *
            exec.roundedGrowthFactor (higham11_4_roundedActiveMax A) *
            fp.u * higham11_4_roundedActiveMax A +
          (40 * (n : Real) *
              (1444 * (n : Real) ^ 2 + 1440 * (n : Real))) *
            exec.roundedGrowthFactor (higham11_4_roundedActiveMax A) *
            fp.u ^ 2 * higham11_4_roundedActiveMax A) /\
      (forall i : Fin n,
        ∑ j : Fin n,
          (A i j + DeltaA2 i j) *
            exec.unpermutedVector
              (fl_backSub fp n (fun r c => exec.flatL c r) w_hat) j = b i) := by
  obtain ⟨w_hat, DeltaD, DeltaA2, hD, hmiddle, hA2, hsolve⟩ :=
    computedSolve_backward_error_normwise_forty_actual_explicitInverse_source_firstOrder
      hval3 hval9 hsmall9 huSmall exec hmiddleDomain b hvaln hAmaxPos
        hCoeffSmall huOne
  refine ⟨w_hat, DeltaD, DeltaA2, hD, hmiddle, ?_, hsolve⟩
  intro i j
  refine (hA2 i j).trans ?_
  let N : Real := n
  let rho : Real := exec.roundedGrowthFactor (higham11_4_roundedActiveMax A)
  let M : Real := higham11_4_roundedActiveMax A
  let u : Real := fp.u
  have hN0 : 0 <= N := by simp [N]
  have hu0 : 0 <= u := by simpa [u] using fp.u_nonneg
  have hM0 : 0 <= M := by simpa [M] using le_of_lt hAmaxPos
  have hrho : 1 <= rho := by
    simpa [rho] using one_le_roundedGrowthFactor_at_sourceMax exec hAmaxPos
  have habsorb : 216 * N * u * M <= 216 * N * rho * u * M := by
    have hfactor : 0 <= 216 * N * u * M := by positivity
    have h := mul_le_mul_of_nonneg_left hrho hfactor
    nlinarith
  change
    216 * N * u * ((1 + 40 * N * rho) * M) +
        ((4 * N + 360) * u + (1444 * N ^ 2 + 1440 * N) * u ^ 2) *
          (40 * N * rho * M) <= _
  calc
    216 * N * u * ((1 + 40 * N * rho) * M) +
        ((4 * N + 360) * u + (1444 * N ^ 2 + 1440 * N) * u ^ 2) *
          (40 * N * rho * M) =
        216 * N * u * M + 216 * N * u * 40 * N * rho * M +
          (4 * N + 360) * u * 40 * N * rho * M +
          (1444 * N ^ 2 + 1440 * N) * u ^ 2 * 40 * N * rho * M := by ring
    _ <= 216 * N * rho * u * M + 216 * N * u * 40 * N * rho * M +
          (4 * N + 360) * u * 40 * N * rho * M +
          (1444 * N ^ 2 + 1440 * N) * u ^ 2 * 40 * N * rho * M := by
      linarith
    _ = (216 * N * (1 + 40 * N) + 40 * N * (4 * N + 360)) *
          rho * u * M +
        (40 * N * (1444 * N ^ 2 + 1440 * N)) * rho * u ^ 2 * M := by ring

end Higham11RoundedBunchKaufmanExecution

end NumStability
