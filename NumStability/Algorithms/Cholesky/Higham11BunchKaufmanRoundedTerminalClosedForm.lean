/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# Closed-form rounded Bunch--Kaufman terminal bounds

This module removes the path-dependent residual coefficient from the public
rounded Bunch--Kaufman solve theorem.  It also records the quantifier order
behind Higham's first-order statement: for each fixed dimension, under an
explicit small-unit-roundoff guard, the exact finite-precision radius is a
linear polynomial in `u` plus a displayed quadratic remainder.

Source: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
Theorems 11.3--11.4, pp. 218--219.
-/

import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedTerminal

open scoped BigOperators

namespace NumStability

namespace Higham11RoundedBunchKaufmanExecution

/-- The honest middle-solve run domain already excludes the sole breakdown
constructor, and therefore implies successful factorization completion. -/
theorem completed_of_middleSolveRunDomain : {n : Nat} ->
    {A : Higham11RoundedBunchKaufmanMatrix n} ->
    (exec : Higham11RoundedBunchKaufmanExecution fp A) ->
    exec.MiddleSolveRunDomain -> exec.Completed
  | _, _, .nil _ => by simp [MiddleSolveRunDomain, Completed]
  | _, _, .noAction _ _ _ tail => by
      intro h
      exact completed_of_middleSolveRunDomain tail h.2
  | _, _, .case1 _ _ _ tail => by
      intro h
      exact completed_of_middleSolveRunDomain tail h
  | _, _, .case2 _ _ _ tail => by
      intro h
      exact completed_of_middleSolveRunDomain tail h
  | _, _, .case3 _ _ _ tail => by
      intro h
      exact completed_of_middleSolveRunDomain tail h
  | _, _, .case4 _ _ _ _ tail => by
      intro h
      exact completed_of_middleSolveRunDomain tail h
  | _, _, .case4Breakdown _ _ _ _ => by
      intro h
      exact False.elim h

/-- Dimension-only replacement for the execution-path coefficient in the
factorization residual. -/
noncomputable def dimensionResidualCoefficient (fp : FPModel) (n : Nat) : Real :=
  (1 + 18 * gamma fp 3) ^ n - 1

theorem finiteResidualCoefficient_le_dimensionResidualCoefficient
    (hval3 : gammaValid fp 3) {n : Nat}
    {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (hmiddleDomain : exec.MiddleSolveRunDomain) :
    exec.finiteResidualCoefficient <= dimensionResidualCoefficient fp n := by
  exact finiteResidualCoefficient_le_pow_dimension_sub_one hval3 exec
    (completed_of_middleSolveRunDomain exec hmiddleDomain)

/-- The dimension coefficient is first order in `u` under a fully displayed
fixed-dimension smallness guard.  The order of quantification is intentional:
`n` is fixed before the bound on `u` is imposed. -/
theorem dimensionResidualCoefficient_le_twoHundredSixteen_mul_dimension_mul_u
    (fp : FPModel) (n : Nat) (hval3 : gammaValid fp 3)
    (hsmall : 108 * (n : Real) * fp.u <= 1 / 2) :
    dimensionResidualCoefficient fp n <= 216 * (n : Real) * fp.u := by
  by_cases hn : n = 0
  · subst n
    simp [dimensionResidualCoefficient]
  have hn0 : (0 : Real) <= (n : Real) := by positivity
  have hg0 : 0 <= gamma fp 3 := gamma_nonneg fp hval3
  have h3half : (3 : Real) * fp.u <= 1 / 2 := by
    have hn1 : (1 : Real) <= (n : Real) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    have hu108 : 108 * fp.u <= 108 * (n : Real) * fp.u := by
      nlinarith [fp.u_nonneg]
    nlinarith
  have hg : gamma fp 3 <= 6 * fp.u := by
    have h := gamma_le_two_mul_n_u_of_nu_le_half fp 3 h3half
    norm_num at h ⊢
    nlinarith
  have hc0 : 0 <= 18 * gamma fp 3 := mul_nonneg (by norm_num) hg0
  have hcsmall : (n : Real) * (18 * gamma fp 3) <= 1 / 2 := by
    have hc : 18 * gamma fp 3 <= 108 * fp.u := by nlinarith
    have := mul_le_mul_of_nonneg_left hc hn0
    nlinarith
  have hpow := one_add_pow_sub_one_le_two_mul_nat_mul_of_nat_mul_le_half
    n hc0 hcsmall
  unfold dimensionResidualCoefficient
  calc
    (1 + 18 * gamma fp 3) ^ n - 1
        <= 2 * ((n : Real) * (18 * gamma fp 3)) := hpow
    _ <= 216 * (n : Real) * fp.u := by
      have := mul_le_mul_of_nonneg_left hg
        (mul_nonneg (by positivity : (0 : Real) <= 36) hn0)
      nlinarith

/-- The solve-chain coefficient with the actual `36u` middle solve is bounded
by a displayed linear term and a displayed quadratic remainder.  In
particular, for every fixed `n`, the second term is genuinely `O(u^2)` with
constant `148 n^2 + 144 n`; no asymptotic premise is hidden. -/
theorem solveResidualCoefficient_thirtySix_mul_u_le_linear_add_quadratic
    (fp : FPModel) (n : Nat) (hvaln : gammaValid fp n)
    (hhalf : (n : Real) * fp.u <= 1 / 2) (huOne : fp.u <= 1) :
    solveResidualCoefficient fp n (36 * fp.u) <=
      (4 * (n : Real) + 36) * fp.u +
        (148 * (n : Real) ^ 2 + 144 * (n : Real)) * fp.u ^ 2 := by
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
  have hgu : 72 * g * u <= 144 * N * u ^ 2 := by nlinarith
  have huSq : u ^ 3 <= u ^ 2 := by nlinarith [sq_nonneg u]
  have hgsqu : 36 * g ^ 2 * u <= 144 * N ^ 2 * u ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hgsq hu0
    have hN2 : 0 <= N ^ 2 := sq_nonneg N
    nlinarith [mul_le_mul_of_nonneg_left huSq (mul_nonneg (by norm_num : (0 : Real) <= 144) hN2)]
  change (2 * g + g ^ 2) + (1 + 2 * g + g ^ 2) * (36 * u) <= _
  calc
    (2 * g + g ^ 2) + (1 + 2 * g + g ^ 2) * (36 * u)
        = 2 * g + 36 * u + g ^ 2 + 72 * g * u + 36 * g ^ 2 * u := by ring
    _ <= 4 * N * u + 36 * u +
          4 * N ^ 2 * u ^ 2 + 144 * N * u ^ 2 +
            144 * N ^ 2 * u ^ 2 := by nlinarith
    _ = (4 * N + 36) * u + (148 * N ^ 2 + 144 * N) * u ^ 2 := by ring

private theorem terminal_input_envelope_nonneg {n : Nat}
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

/-- Dimension-only pivot-coordinate terminal theorem.  Unlike the original
terminal API, successful completion is derived from `MiddleSolveRunDomain`,
and the path-dependent `finiteResidualCoefficient` is absent from the result. -/
theorem computedSolve_backward_error_normwise_forty_actual_dimension
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
        |DeltaD i j| <= 36 * fp.u * |exec.flatD i j|) /\
      (forall p : Fin n,
        (∑ q : Fin n, (exec.flatD p q + DeltaD p q) * w_hat q) =
          fl_forwardSub fp n exec.flatL b p) /\
      (forall i j : Fin n,
        |DeltaA2 i j| <=
          dimensionResidualCoefficient fp n *
              ((1 + 40 * (n : Real) * exec.roundedGrowthFactor Amax) * Amax) +
            solveResidualCoefficient fp n (36 * fp.u) *
              (40 * (n : Real) * exec.roundedGrowthFactor Amax * Amax)) /\
      (forall i : Fin n,
        ∑ j : Fin n,
          (exec.permutedInput i j + DeltaA2 i j) *
              fl_backSub fp n (fun r c => exec.flatL c r) w_hat j = b i) := by
  have hcompleted := completed_of_middleSolveRunDomain exec hmiddleDomain
  obtain ⟨w_hat, DeltaD, DeltaA2, hD, hmiddle, hA2, hsolve⟩ :=
    computedSolve_backward_error_normwise_forty_actual
      hval3 hval9 hsmall9 huSmall exec hcompleted hmiddleDomain b hvaln
        Amax hAmax hAmaxPos
  refine ⟨w_hat, DeltaD, DeltaA2, hD, hmiddle, ?_, hsolve⟩
  intro i j
  refine (hA2 i j).trans ?_
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right
    · exact finiteResidualCoefficient_le_dimensionResidualCoefficient
        hval3 exec hmiddleDomain
    · exact terminal_input_envelope_nonneg exec Amax hAmaxPos
  · exact le_rfl

/-- Source-coordinate form of the dimension-only terminal theorem. -/
theorem computedSolve_backward_error_normwise_forty_actual_source_dimension
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
        |DeltaD i j| <= 36 * fp.u * |exec.flatD i j|) /\
      (forall p : Fin n,
        (∑ q : Fin n, (exec.flatD p q + DeltaD p q) * w_hat q) =
          fl_forwardSub fp n exec.flatL
            (fun i => b (exec.permutation i)) p) /\
      (forall i j : Fin n,
        |DeltaA2 i j| <=
          dimensionResidualCoefficient fp n *
              ((1 + 40 * (n : Real) * exec.roundedGrowthFactor Amax) * Amax) +
            solveResidualCoefficient fp n (36 * fp.u) *
              (40 * (n : Real) * exec.roundedGrowthFactor Amax * Amax)) /\
      (forall i : Fin n,
        ∑ j : Fin n,
          (A i j + DeltaA2 i j) *
            exec.unpermutedVector
              (fl_backSub fp n (fun r c => exec.flatL c r) w_hat) j = b i) := by
  have hcompleted := completed_of_middleSolveRunDomain exec hmiddleDomain
  obtain ⟨w_hat, DeltaD, DeltaA2, hD, hmiddle, hA2, hsolve⟩ :=
    computedSolve_backward_error_normwise_forty_actual_source
      hval3 hval9 hsmall9 huSmall exec hcompleted hmiddleDomain b hvaln
        Amax hAmax hAmaxPos
  refine ⟨w_hat, DeltaD, DeltaA2, hD, hmiddle, ?_, hsolve⟩
  intro i j
  refine (hA2 i j).trans ?_
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right
    · exact finiteResidualCoefficient_le_dimensionResidualCoefficient
        hval3 exec hmiddleDomain
    · exact terminal_input_envelope_nonneg exec Amax hAmaxPos
  · exact le_rfl

/-- For a nonempty input, `higham11_4_roundedActiveMax A` is exactly the
source max-entry norm.  Consequently this wrapper's growth factor is the
literal Higham ratio `max visited active entry / max input entry`, rather than
a ratio formed with an arbitrary upper scale. -/
theorem computedSolve_backward_error_normwise_forty_actual_source_maxEntryNorm
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
        |DeltaD i j| <= 36 * fp.u * |exec.flatD i j|) /\
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
            solveResidualCoefficient fp n (36 * fp.u) *
              (40 * (n : Real) *
                exec.roundedGrowthFactor (higham11_4_roundedActiveMax A) *
                higham11_4_roundedActiveMax A)) /\
      (forall i : Fin n,
        ∑ j : Fin n,
          (A i j + DeltaA2 i j) *
            exec.unpermutedVector
              (fl_backSub fp n (fun r c => exec.flatL c r) w_hat) j = b i) := by
  exact computedSolve_backward_error_normwise_forty_actual_source_dimension
    hval3 hval9 hsmall9 huSmall exec hmiddleDomain b hvaln
      (higham11_4_roundedActiveMax A)
      (fun i j => higham11_4_entry_le_roundedActiveMax A i j) hAmaxPos

/-- Source-facing fixed-dimension first-order/quadratic radius.  For every
fixed `n`, every completed actual run in the middle-solve domain, and every
unit roundoff satisfying the displayed guards, the perturbation is bounded
by an explicit term linear in `u` plus an explicit multiple of `u^2`.
This is a quantified finite-`u` realization of Higham's
`p(n) rho_n u ||A||_M + O(u^2)` statement. -/
theorem computedSolve_backward_error_normwise_forty_actual_source_firstOrder
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
        |DeltaD i j| <= 36 * fp.u * |exec.flatD i j|) /\
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
            ((4 * (n : Real) + 36) * fp.u +
                (148 * (n : Real) ^ 2 + 144 * (n : Real)) * fp.u ^ 2) *
              (40 * (n : Real) *
                exec.roundedGrowthFactor (higham11_4_roundedActiveMax A) *
                higham11_4_roundedActiveMax A)) /\
      (forall i : Fin n,
        ∑ j : Fin n,
          (A i j + DeltaA2 i j) *
            exec.unpermutedVector
              (fl_backSub fp n (fun r c => exec.flatL c r) w_hat) j = b i) := by
  obtain ⟨w_hat, DeltaD, DeltaA2, hD, hmiddle, hA2, hsolve⟩ :=
    computedSolve_backward_error_normwise_forty_actual_source_maxEntryNorm
      hval3 hval9 hsmall9 huSmall exec hmiddleDomain b hvaln hAmaxPos
  refine ⟨w_hat, DeltaD, DeltaA2, hD, hmiddle, ?_, hsolve⟩
  intro i j
  refine (hA2 i j).trans ?_
  have hK :=
    dimensionResidualCoefficient_le_twoHundredSixteen_mul_dimension_mul_u
      fp n hval3 hCoeffSmall
  have hS := solveResidualCoefficient_thirtySix_mul_u_le_linear_add_quadratic
    fp n hvaln (by
      have hn108 : (n : Real) * fp.u <= 108 * (n : Real) * fp.u := by
        nlinarith [fp.u_nonneg, show (0 : Real) <= (n : Real) by positivity]
      linarith) huOne
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right hK
      (terminal_input_envelope_nonneg exec _ hAmaxPos)
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

/-- At the exact max-entry input scale, the rounded growth factor is at least
one because the initial matrix is one of the visited active matrices. -/
theorem one_le_roundedGrowthFactor_at_sourceMax {n : Nat}
    {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A)
    (hAmaxPos : 0 < higham11_4_roundedActiveMax A) :
    1 <= exec.roundedGrowthFactor (higham11_4_roundedActiveMax A) := by
  have hcurrent := currentMax_le_roundedStageMax exec
  have hscale := roundedStageMax_eq_growthFactor_mul exec hAmaxPos
  rw [hscale] at hcurrent
  nlinarith

/-- Literal polynomial-times-growth-factor form of Theorem 11.4.  The first
summand is `p(n) rho_n u ||A||_M`; the second is the exact finite-`u` remainder
`C(n) rho_n u^2 ||A||_M`.  Thus no asymptotic premise is hidden.  In any
family with fixed `n` and a uniform bound on `rho_n ||A||_M`, the displayed
second summand immediately supplies the corresponding uniform `O(u^2)`
statement. -/
theorem computedSolve_backward_error_normwise_forty_actual_source_polynomial
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
        |DeltaD i j| <= 36 * fp.u * |exec.flatD i j|) /\
      (forall p : Fin n,
        (∑ q : Fin n, (exec.flatD p q + DeltaD p q) * w_hat q) =
          fl_forwardSub fp n exec.flatL
            (fun i => b (exec.permutation i)) p) /\
      (forall i j : Fin n,
        |DeltaA2 i j| <=
          (216 * (n : Real) * (1 + 40 * (n : Real)) +
              40 * (n : Real) * (4 * (n : Real) + 36)) *
            exec.roundedGrowthFactor (higham11_4_roundedActiveMax A) *
            fp.u * higham11_4_roundedActiveMax A +
          (40 * (n : Real) *
              (148 * (n : Real) ^ 2 + 144 * (n : Real))) *
            exec.roundedGrowthFactor (higham11_4_roundedActiveMax A) *
            fp.u ^ 2 * higham11_4_roundedActiveMax A) /\
      (forall i : Fin n,
        ∑ j : Fin n,
          (A i j + DeltaA2 i j) *
            exec.unpermutedVector
              (fl_backSub fp n (fun r c => exec.flatL c r) w_hat) j = b i) := by
  obtain ⟨w_hat, DeltaD, DeltaA2, hD, hmiddle, hA2, hsolve⟩ :=
    computedSolve_backward_error_normwise_forty_actual_source_firstOrder
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
        ((4 * N + 36) * u + (148 * N ^ 2 + 144 * N) * u ^ 2) *
          (40 * N * rho * M) <= _
  calc
    216 * N * u * ((1 + 40 * N * rho) * M) +
        ((4 * N + 36) * u + (148 * N ^ 2 + 144 * N) * u ^ 2) *
          (40 * N * rho * M) =
        216 * N * u * M + 216 * N * u * 40 * N * rho * M +
          (4 * N + 36) * u * 40 * N * rho * M +
          (148 * N ^ 2 + 144 * N) * u ^ 2 * 40 * N * rho * M := by ring
    _ <= 216 * N * rho * u * M + 216 * N * u * 40 * N * rho * M +
          (4 * N + 36) * u * 40 * N * rho * M +
          (148 * N ^ 2 + 144 * N) * u ^ 2 * 40 * N * rho * M := by
      linarith
    _ = (216 * N * (1 + 40 * N) + 40 * N * (4 * N + 36)) *
          rho * u * M +
        (40 * N * (148 * N ^ 2 + 144 * N)) * rho * u ^ 2 * M := by ring

end Higham11RoundedBunchKaufmanExecution

end NumStability
