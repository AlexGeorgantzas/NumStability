-- NumStability/Source/Higham/Chapter01/Problem10/TwoPassSampleVariance/RemainderBound/Theorem.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Split component of a mixed/multi-destination owner.
-- Historical owner: `NumStability.Analysis.SampleVariance`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Basic
import NumStability.Analysis.Error.Measures.ScalarDefinitions
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Statistics.SampleVariance.Core
import NumStability.Analysis.Statistics.SampleVariance.TwoPass
import NumStability.Analysis.Statistics.SampleVariance.Updating
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.Source.Higham.Chapter01.Problem07.SampleVarianceConditioning.ConditionNumbers
import NumStability.Source.Higham.Chapter01.Problem10.TwoPassSampleVariance.Bounds
import NumStability.Source.Higham.Chapter01.Section09.SampleVariance.Examples

/-!
# Theorem

Relocated from `NumStability.Analysis.SampleVariance` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


-- Analysis/SampleVariance.lean
--
-- Exact sample-variance algebra for Higham Chapter 1, Section 1.9.
















namespace NumStability

open scoped BigOperators Topology

/-!
# Sample-Variance Algebra

Higham Chapter 1, Section 1.9 contrasts mathematically equivalent formulae
for the sample variance.  This file records the exact real-arithmetic
identities behind formulas (1.4) and (1.5), plus the shifted one-pass identity.
The floating-point stability bounds for the corresponding algorithms are
separate obligations.
-/

private lemma gamma_le_two_mul_nu_of_mul_u_le_half (fp : FPModel) (n : ℕ)
    (hcap : (n : ℝ) * fp.u ≤ (1 : ℝ) / 2) :
    gamma fp n ≤ 2 * ((n : ℝ) * fp.u) := by
  unfold gamma
  set a : ℝ := (n : ℝ) * fp.u with ha
  have ha_nonneg : 0 ≤ a := by
    rw [ha]
    exact mul_nonneg (by exact_mod_cast n.zero_le) fp.u_nonneg
  have hden_pos : 0 < 1 - a := by linarith
  rw [div_le_iff₀ hden_pos]
  nlinarith






























































/-- Source `O(u^2)` certificate for Problem 1.10: with fixed data and
`(n+3)u <= 1/2`, the named higher-order remainder after the source linear term
`(n+3)u` is bounded by an explicit quadratic expression in the unit roundoff. -/
theorem flSampleVarianceTwoPassProblem110Remainder_le_quadratic_bound {n : ℕ}
    (fp : FPModel) (x : Fin n → ℝ)
    (hn : 1 < n) (hVpos : 0 < sampleVarianceTwoPass x)
    (hγ : gammaValid fp (n + 3))
    (hcap : (((n + 3 : ℕ) : ℝ) * fp.u) ≤ (1 : ℝ) / 2) :
    flSampleVarianceTwoPassProblem110Remainder fp x ≤
      flSampleVarianceTwoPassProblem110RemainderQuadraticBound fp x := by
  set L : ℝ := ((n + 3 : ℕ) : ℝ) * fp.u with hL
  set A : ℝ := (∑ i : Fin n, |x i|) / (n : ℝ) with hA
  set B : ℝ := flSampleVarianceTwoPassProblem110MeanQuadraticBound fp x with hB
  set B2 : ℝ := (((n : ℝ) * (2 * ((n : ℝ) * fp.u) * A) ^ 2 /
      ((n : ℝ) - 1)) / sampleVarianceTwoPass x) with hB2
  have hn_pos_real : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.lt_trans Nat.zero_lt_one hn)
  have hn_nonneg_real : 0 ≤ (n : ℝ) := le_of_lt hn_pos_real
  have hden_pos : 0 < (n : ℝ) - 1 := by
    have hn_gt_one : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  have hA_nonneg : 0 ≤ A := by
    rw [hA]
    exact div_nonneg (Finset.sum_nonneg (fun i hi => abs_nonneg (x i)))
      (le_of_lt hn_pos_real)
  have hcap_n : (n : ℝ) * fp.u ≤ (1 : ℝ) / 2 := by
    have hnle : (n : ℝ) ≤ ((n + 3 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_add_right n 3)
    exact le_trans (mul_le_mul_of_nonneg_right hnle fp.u_nonneg) hcap
  have hγn : gammaValid fp n := gammaValid_mono fp (Nat.le_add_right n 3) hγ
  have hgamma_n_nonneg : 0 ≤ gamma fp n := gamma_nonneg fp hγn
  have hgamma_n_le : gamma fp n ≤ 2 * ((n : ℝ) * fp.u) :=
    gamma_le_two_mul_nu_of_mul_u_le_half fp n hcap_n
  have hleft_nonneg : 0 ≤ gamma fp n * A := mul_nonneg hgamma_n_nonneg hA_nonneg
  have hmul_le :
      gamma fp n * A ≤ 2 * ((n : ℝ) * fp.u) * A :=
    mul_le_mul_of_nonneg_right hgamma_n_le hA_nonneg
  have hsquare_le :
      (gamma fp n * A) ^ 2 ≤ (2 * ((n : ℝ) * fp.u) * A) ^ 2 := by
    nlinarith
  have hB_le_B2 : B ≤ B2 := by
    rw [hB, hB2, hA]
    have hnum_le :
        (n : ℝ) *
            (gamma fp n * ((∑ i : Fin n, |x i|) / (n : ℝ))) ^ 2 ≤
          (n : ℝ) *
            (2 * ((n : ℝ) * fp.u) * ((∑ i : Fin n, |x i|) / (n : ℝ))) ^ 2 :=
      mul_le_mul_of_nonneg_left (by simpa [hA] using hsquare_le) hn_nonneg_real
    have hdiv1 :
        (n : ℝ) *
            (gamma fp n * ((∑ i : Fin n, |x i|) / (n : ℝ))) ^ 2 /
            ((n : ℝ) - 1) ≤
          (n : ℝ) *
            (2 * ((n : ℝ) * fp.u) * ((∑ i : Fin n, |x i|) / (n : ℝ))) ^ 2 /
            ((n : ℝ) - 1) :=
      div_le_div_of_nonneg_right hnum_le (le_of_lt hden_pos)
    exact div_le_div_of_nonneg_right hdiv1 (le_of_lt hVpos)
  have hB_nonneg : 0 ≤ B := by
    rw [hB]
    exact flSampleVarianceTwoPassProblem110MeanQuadraticBound_nonneg fp x hn hVpos
  have hG_nonneg : 0 ≤ gamma fp (n + 3) := gamma_nonneg fp hγ
  have hG_le_one : gamma fp (n + 3) ≤ 1 := by
    have hle : gamma fp (n + 3) ≤
        2 * ((((n + 3 : ℕ) : ℝ) * fp.u) : ℝ) :=
      gamma_le_two_mul_nu_of_mul_u_le_half fp (n + 3) hcap
    nlinarith
  have hGB_le_B : gamma fp (n + 3) * B ≤ B := by
    nlinarith
  have hL_nonneg : 0 ≤ L := by
    rw [hL]
    exact mul_nonneg (by exact_mod_cast (n + 3).zero_le) fp.u_nonneg
  have hLden_pos : 0 < 1 - L := by linarith
  have hRquad :
      L ^ 2 / (1 - L) ≤ 2 * L ^ 2 := by
    rw [div_le_iff₀ hLden_pos]
    nlinarith
  have htotal :
      L ^ 2 / (1 - L) + B + gamma fp (n + 3) * B ≤ 2 * (L ^ 2 + B2) := by
    nlinarith
  simpa [flSampleVarianceTwoPassProblem110RemainderQuadraticBound,
    flSampleVarianceTwoPassProblem110Remainder,
    flSampleVarianceTwoPassProblem110MeanQuadraticBound, hL, hA, hB, hB2]
    using htotal

end NumStability
