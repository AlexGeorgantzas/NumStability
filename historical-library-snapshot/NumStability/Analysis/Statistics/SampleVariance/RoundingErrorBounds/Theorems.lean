-- NumStability/Analysis/Statistics/SampleVariance/RoundingErrorBounds/Theorems.lean
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

/-!
# Theorems

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




























































































































































































































private theorem abs_error_add_perturbed_term_rounding
    (u γ A T θ δ y : ℝ) (hu : 0 ≤ u) (hγ : 0 ≤ γ)
    (hθ : |θ| ≤ γ) (hδ : |δ| ≤ u)
    (hy : y = (A + T * (1 + θ)) * (1 + δ)) :
    |y - (A + T)| ≤ |A + T| * u + |T| * γ * (1 + u) := by
  subst y
  have h1δ : |1 + δ| ≤ 1 + u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le 1 δ
      _ = 1 + |δ| := by norm_num
      _ ≤ 1 + u := by linarith
  have hterm1 : |A + T| * |δ| ≤ |A + T| * u :=
    mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
  have hterm2a : |T| * |θ| ≤ |T| * γ :=
    mul_le_mul_of_nonneg_left hθ (abs_nonneg _)
  have hTγnonneg : 0 ≤ |T| * γ :=
    mul_nonneg (abs_nonneg _) hγ
  have hrightnonneg : 0 ≤ 1 + u := by linarith
  have hleftfactor_nonneg : 0 ≤ |1 + δ| := abs_nonneg _
  have hterm2 : |T| * |θ| * |1 + δ| ≤ |T| * γ * (1 + u) :=
    mul_le_mul hterm2a h1δ hleftfactor_nonneg hTγnonneg
  have hdiff :
      (A + T * (1 + θ)) * (1 + δ) - (A + T) =
        (A + T) * δ + T * θ * (1 + δ) := by
    ring
  calc
    |(A + T * (1 + θ)) * (1 + δ) - (A + T)|
        = |(A + T) * δ + T * θ * (1 + δ)| := by rw [hdiff]
    _ ≤ |(A + T) * δ| + |T * θ * (1 + δ)| := abs_add_le _ _
    _ = |A + T| * |δ| + |T| * |θ| * |1 + δ| := by
          rw [abs_mul, abs_mul, abs_mul]
    _ ≤ |A + T| * u + |T| * γ * (1 + u) :=
          add_le_add hterm1 hterm2

































/-- Absolute-error form of the rounded one-step mean update. -/
theorem flPrefixMeanStep_abs_error_le
    (fp : FPModel) (M x : ℝ) (k : ℕ) (hγ : gammaValid fp 2) :
    |flPrefixMeanStep fp M x k - prefixMeanStepExact M x k| ≤
      |prefixMeanStepExact M x k| * fp.u +
        |(x - M) / ((k + 1 : ℕ) : ℝ)| * gamma fp 2 * (1 + fp.u) := by
  obtain ⟨θ, δ, hθ, hδ, hfl⟩ :=
    flPrefixMeanStep_eq_exact_with_local_errors fp M x k hγ
  have hγnonneg : 0 ≤ gamma fp 2 := gamma_nonneg fp hγ
  exact
    (abs_error_add_perturbed_term_rounding fp.u (gamma fp 2) M
      ((x - M) / ((k + 1 : ℕ) : ℝ)) θ δ
      (flPrefixMeanStep fp M x k) fp.u_nonneg hγnonneg hθ hδ
      (by simpa using hfl))


/-- Instantiation of `flPrefixMeanStep_abs_error_le` against the exact prefix
mean recurrence. -/
theorem flPrefixMeanStep_abs_error_le_prefixMean_succ
    (fp : FPModel) (x : ℕ → ℝ) {k : ℕ}
    (hk : (k : ℝ) ≠ 0) (hγ : gammaValid fp 2) :
    |flPrefixMeanStep fp (prefixMean x k) (x k) k - prefixMean x (k + 1)| ≤
      |prefixMean x (k + 1)| * fp.u +
        |(x k - prefixMean x k) / ((k + 1 : ℕ) : ℝ)| *
          gamma fp 2 * (1 + fp.u) := by
  have hbase :=
    flPrefixMeanStep_abs_error_le fp (prefixMean x k) (x k) k hγ
  simpa [prefixMeanStepExact, prefixMean_succ x hk] using hbase








































































/-- Multi-step rounded-prefix-mean theorem for Higham §1.9's update
recurrence.  The bound is explicit and recursive: each previous mean error is
contracted by `k/(k+1)`, then the local rounded correction and final rounded
addition costs are added. -/
theorem flPrefixMeanTrajectory_abs_error_le_budget
    (fp : FPModel) (x : ℕ → ℝ) (hγ : gammaValid fp 2) :
    ∀ k : ℕ,
      |flPrefixMeanTrajectory fp x k - prefixMean x k| ≤
        flPrefixMeanTrajectoryAbsErrorBudget fp x k := by
  intro k
  induction k with
  | zero =>
      simp [flPrefixMeanTrajectory, flPrefixMeanTrajectoryAbsErrorBudget,
        prefixMean]
  | succ k ih =>
      set Mhat : ℝ := flPrefixMeanTrajectory fp x k with hMhat
      set Mexact : ℝ := prefixMean x k with hMexact
      set xk : ℝ := x k with hxk
      set coeff : ℝ := (k : ℝ) / ((k + 1 : ℕ) : ℝ) with hcoeff
      set localErr : ℝ :=
        |prefixMeanStepExact Mhat xk k| * fp.u +
          |(xk - Mhat) / ((k + 1 : ℕ) : ℝ)| *
            gamma fp 2 * (1 + fp.u) with hlocalErr
      have hstepLocal :
          |flPrefixMeanStep fp Mhat xk k - prefixMeanStepExact Mhat xk k| ≤
            localErr := by
        rw [hlocalErr]
        simpa [hMhat, hxk] using flPrefixMeanStep_abs_error_le fp Mhat xk k hγ
      have hstepExact :
          prefixMeanStepExact Mexact xk k = prefixMean x (k + 1) := by
        rw [hMexact, hxk]
        exact prefixMeanStepExact_prefixMean_eq_succ x k
      have hcoef_nonneg : 0 ≤ coeff := by
        rw [hcoeff]
        exact div_nonneg (by exact_mod_cast Nat.zero_le k)
          (le_of_lt (by exact_mod_cast Nat.succ_pos k))
      have hprev :
          |Mhat - Mexact| ≤ flPrefixMeanTrajectoryAbsErrorBudget fp x k := by
        simpa [hMhat, hMexact] using ih
      have hstepSensitive :
          |prefixMeanStepExact Mhat xk k - prefixMeanStepExact Mexact xk k| ≤
            coeff * flPrefixMeanTrajectoryAbsErrorBudget fp x k := by
        have hsub :=
          prefixMeanStepExact_sub_prefixMeanStepExact Mhat Mexact xk k
        calc
          |prefixMeanStepExact Mhat xk k - prefixMeanStepExact Mexact xk k|
              = |coeff * (Mhat - Mexact)| := by rw [hsub, hcoeff]
          _ = coeff * |Mhat - Mexact| := by
              rw [abs_mul, abs_of_nonneg hcoef_nonneg]
          _ ≤ coeff * flPrefixMeanTrajectoryAbsErrorBudget fp x k :=
              mul_le_mul_of_nonneg_left hprev hcoef_nonneg
      have htriangle :
          |flPrefixMeanStep fp Mhat xk k - prefixMeanStepExact Mexact xk k| ≤
            localErr + coeff * flPrefixMeanTrajectoryAbsErrorBudget fp x k := by
        have hsplit :
            flPrefixMeanStep fp Mhat xk k - prefixMeanStepExact Mexact xk k =
              (flPrefixMeanStep fp Mhat xk k - prefixMeanStepExact Mhat xk k) +
                (prefixMeanStepExact Mhat xk k -
                  prefixMeanStepExact Mexact xk k) := by
          ring
        calc
          |flPrefixMeanStep fp Mhat xk k - prefixMeanStepExact Mexact xk k|
              = |(flPrefixMeanStep fp Mhat xk k - prefixMeanStepExact Mhat xk k) +
                  (prefixMeanStepExact Mhat xk k -
                    prefixMeanStepExact Mexact xk k)| := by rw [hsplit]
          _ ≤ |flPrefixMeanStep fp Mhat xk k - prefixMeanStepExact Mhat xk k| +
              |prefixMeanStepExact Mhat xk k -
                prefixMeanStepExact Mexact xk k| := abs_add_le _ _
          _ ≤ localErr + coeff * flPrefixMeanTrajectoryAbsErrorBudget fp x k :=
              add_le_add hstepLocal hstepSensitive
      have hbudget :
          flPrefixMeanTrajectoryAbsErrorBudget fp x (k + 1) =
            coeff * flPrefixMeanTrajectoryAbsErrorBudget fp x k + localErr := by
        simp [flPrefixMeanTrajectoryAbsErrorBudget, hcoeff, hlocalErr, hMhat, hxk]
        ring
      calc
        |flPrefixMeanTrajectory fp x (k + 1) - prefixMean x (k + 1)|
            = |flPrefixMeanStep fp Mhat xk k - prefixMean x (k + 1)| := by
              simp [flPrefixMeanTrajectory, hMhat, hxk]
        _ = |flPrefixMeanStep fp Mhat xk k -
                prefixMeanStepExact Mexact xk k| := by
              rw [hstepExact]
        _ ≤ localErr + coeff * flPrefixMeanTrajectoryAbsErrorBudget fp x k :=
              htriangle
        _ = flPrefixMeanTrajectoryAbsErrorBudget fp x (k + 1) := by
              rw [hbudget]
              ring
































































































































/-- Absolute-error form of the rounded corrected-sum-of-squares update. -/
theorem flPrefixCorrectedSumSquaresStep_abs_error_le
    (fp : FPModel) (Q M x : ℝ) (k : ℕ) (hγ : gammaValid fp 5) :
    |flPrefixCorrectedSumSquaresStep fp Q M x k -
        prefixCorrectedSumSquaresStepExact Q M x k| ≤
      |prefixCorrectedSumSquaresStepExact Q M x k| * fp.u +
        |(k : ℝ) / ((k + 1 : ℕ) : ℝ) * (x - M) ^ 2| *
          gamma fp 5 * (1 + fp.u) := by
  obtain ⟨θ, δ, hθ, hδ, hfl⟩ :=
    flPrefixCorrectedSumSquaresStep_eq_exact_with_local_errors fp Q M x k hγ
  have hγnonneg : 0 ≤ gamma fp 5 := gamma_nonneg fp hγ
  exact
    (abs_error_add_perturbed_term_rounding fp.u (gamma fp 5) Q
      ((k : ℝ) / ((k + 1 : ℕ) : ℝ) * (x - M) ^ 2) θ δ
      (flPrefixCorrectedSumSquaresStep fp Q M x k)
      fp.u_nonneg hγnonneg hθ hδ (by simpa using hfl))


/-- Instantiation of `flPrefixCorrectedSumSquaresStep_abs_error_le` against
the exact prefix corrected-sum-of-squares recurrence. -/
theorem flPrefixCorrectedSumSquaresStep_abs_error_le_prefix_succ
    (fp : FPModel) (x : ℕ → ℝ) {k : ℕ}
    (hk : (k : ℝ) ≠ 0) (hγ : gammaValid fp 5) :
    |flPrefixCorrectedSumSquaresStep fp
        (prefixCorrectedSumSquares x k) (prefixMean x k) (x k) k -
        prefixCorrectedSumSquares x (k + 1)| ≤
      |prefixCorrectedSumSquares x (k + 1)| * fp.u +
        |(k : ℝ) / ((k + 1 : ℕ) : ℝ) *
          (x k - prefixMean x k) ^ 2| * gamma fp 5 * (1 + fp.u) := by
  have hbase :=
    flPrefixCorrectedSumSquaresStep_abs_error_le fp
      (prefixCorrectedSumSquares x k) (prefixMean x k) (x k) k hγ
  simpa [prefixCorrectedSumSquaresStepExact,
    prefixCorrectedSumSquares_succ x hk] using hbase






































































/-- Multi-step rounded corrected-sum-of-squares theorem for Higham §1.9's
update recurrence.  The computed `Q_k` is generated using the rounded prefix
means, and the budget charges previous `Q` error, previous mean error, and the
local five-operation update plus final rounded addition at every step. -/
theorem flPrefixCorrectedSumSquaresTrajectory_abs_error_le_budget
    (fp : FPModel) (x : ℕ → ℝ) (hγ : gammaValid fp 5) :
    ∀ k : ℕ,
      |flPrefixCorrectedSumSquaresTrajectory fp x k -
          prefixCorrectedSumSquares x k| ≤
        flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x k := by
  intro k
  induction k with
  | zero =>
      simp [flPrefixCorrectedSumSquaresTrajectory,
        flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget,
        prefixCorrectedSumSquares]
  | succ k ih =>
      have hγ2 : gammaValid fp 2 := gammaValid_mono fp (by omega) hγ
      set Qhat : ℝ := flPrefixCorrectedSumSquaresTrajectory fp x k with hQhat
      set Qexact : ℝ := prefixCorrectedSumSquares x k with hQexact
      set Mhat : ℝ := flPrefixMeanTrajectory fp x k with hMhat
      set Mexact : ℝ := prefixMean x k with hMexact
      set xk : ℝ := x k with hxk
      set coeff : ℝ := (k : ℝ) / ((k + 1 : ℕ) : ℝ) with hcoeff
      set localErr : ℝ :=
        |prefixCorrectedSumSquaresStepExact Qhat Mhat xk k| * fp.u +
          |coeff * (xk - Mhat) ^ 2| * gamma fp 5 * (1 + fp.u)
        with hlocalErr
      set meanSens : ℝ :=
        |coeff| * flPrefixMeanTrajectoryAbsErrorBudget fp x k *
          (|xk - Mhat| + |xk - Mexact|)
        with hmeanSens
      have hstepLocal :
          |flPrefixCorrectedSumSquaresStep fp Qhat Mhat xk k -
              prefixCorrectedSumSquaresStepExact Qhat Mhat xk k| ≤
            localErr := by
        rw [hlocalErr]
        simpa [hQhat, hMhat, hxk, hcoeff] using
          flPrefixCorrectedSumSquaresStep_abs_error_le fp Qhat Mhat xk k hγ
      have hstepExact :
          prefixCorrectedSumSquaresStepExact Qexact Mexact xk k =
            prefixCorrectedSumSquares x (k + 1) := by
        rw [hQexact, hMexact, hxk]
        exact prefixCorrectedSumSquaresStepExact_prefix_eq_succ x k
      have hQprev :
          |Qhat - Qexact| ≤
            flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x k := by
        simpa [hQhat, hQexact] using ih
      have hMprev :
          |Mhat - Mexact| ≤
            flPrefixMeanTrajectoryAbsErrorBudget fp x k := by
        simpa [hMhat, hMexact] using
          flPrefixMeanTrajectory_abs_error_le_budget fp x hγ2 k
      have hdevSum_nonneg :
          0 ≤ |xk - Mhat| + |xk - Mexact| :=
        add_nonneg (abs_nonneg _) (abs_nonneg _)
      have hmeanTerm :
          |coeff| * |Mhat - Mexact| * (|xk - Mhat| + |xk - Mexact|) ≤
            meanSens := by
        have hfirst :
            |coeff| * |Mhat - Mexact| ≤
              |coeff| * flPrefixMeanTrajectoryAbsErrorBudget fp x k :=
          mul_le_mul_of_nonneg_left hMprev (abs_nonneg _)
        have hmul :=
          mul_le_mul_of_nonneg_right hfirst hdevSum_nonneg
        simpa [hmeanSens, mul_assoc] using hmul
      have hsensitive :
          |prefixCorrectedSumSquaresStepExact Qhat Mhat xk k -
              prefixCorrectedSumSquaresStepExact Qexact Mexact xk k| ≤
            flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x k +
              meanSens := by
        have hbase :=
          prefixCorrectedSumSquaresStepExact_abs_sub_le
            Qhat Qexact Mhat Mexact xk k
        calc
          |prefixCorrectedSumSquaresStepExact Qhat Mhat xk k -
              prefixCorrectedSumSquaresStepExact Qexact Mexact xk k|
              ≤ |Qhat - Qexact| +
                  |coeff| * |Mhat - Mexact| *
                    (|xk - Mhat| + |xk - Mexact|) := by
                simpa [hcoeff] using hbase
          _ ≤ flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x k +
              meanSens :=
                add_le_add hQprev hmeanTerm
      have htriangle :
          |flPrefixCorrectedSumSquaresStep fp Qhat Mhat xk k -
              prefixCorrectedSumSquaresStepExact Qexact Mexact xk k| ≤
            localErr +
              (flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x k +
                meanSens) := by
        have hsplit :
            flPrefixCorrectedSumSquaresStep fp Qhat Mhat xk k -
                prefixCorrectedSumSquaresStepExact Qexact Mexact xk k =
              (flPrefixCorrectedSumSquaresStep fp Qhat Mhat xk k -
                prefixCorrectedSumSquaresStepExact Qhat Mhat xk k) +
              (prefixCorrectedSumSquaresStepExact Qhat Mhat xk k -
                prefixCorrectedSumSquaresStepExact Qexact Mexact xk k) := by
          ring
        calc
          |flPrefixCorrectedSumSquaresStep fp Qhat Mhat xk k -
              prefixCorrectedSumSquaresStepExact Qexact Mexact xk k|
              =
                |(flPrefixCorrectedSumSquaresStep fp Qhat Mhat xk k -
                    prefixCorrectedSumSquaresStepExact Qhat Mhat xk k) +
                  (prefixCorrectedSumSquaresStepExact Qhat Mhat xk k -
                    prefixCorrectedSumSquaresStepExact Qexact Mexact xk k)| := by
                rw [hsplit]
          _ ≤ |flPrefixCorrectedSumSquaresStep fp Qhat Mhat xk k -
                  prefixCorrectedSumSquaresStepExact Qhat Mhat xk k| +
                |prefixCorrectedSumSquaresStepExact Qhat Mhat xk k -
                  prefixCorrectedSumSquaresStepExact Qexact Mexact xk k| :=
                abs_add_le _ _
          _ ≤ localErr +
              (flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x k +
                meanSens) :=
                add_le_add hstepLocal hsensitive
      have hbudget :
          flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x (k + 1) =
            localErr +
              (flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x k +
                meanSens) := by
        simp [flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget, hlocalErr,
          hmeanSens, hQhat, hMhat, hMexact, hxk, hcoeff]
      calc
        |flPrefixCorrectedSumSquaresTrajectory fp x (k + 1) -
            prefixCorrectedSumSquares x (k + 1)|
            =
              |flPrefixCorrectedSumSquaresStep fp Qhat Mhat xk k -
                prefixCorrectedSumSquares x (k + 1)| := by
              simp [flPrefixCorrectedSumSquaresTrajectory, hQhat, hMhat, hxk]
        _ =
              |flPrefixCorrectedSumSquaresStep fp Qhat Mhat xk k -
                prefixCorrectedSumSquaresStepExact Qexact Mexact xk k| := by
              rw [hstepExact]
        _ ≤ localErr +
            (flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x k +
              meanSens) :=
              htriangle
        _ = flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x (k + 1) :=
              hbudget.symm











































/-- End-to-end rounded-update theorem for Higham §1.9's recurrence-based
sample variance.  The rounded mean and `Q` trajectories are charged by the
recursive `Q` budget, and the final division by `n-1` contributes one more
rounded-division term. -/
theorem flSampleVarianceUpdate_abs_error_le_budget
    (fp : FPModel) (x : ℕ → ℝ) {n : ℕ} (hn : 1 < n)
    (hγ : gammaValid fp 5) :
    |flSampleVarianceUpdate fp x n - sampleVariancePrefix x n| ≤
      flSampleVarianceUpdateAbsErrorBudget fp x n := by
  set Qhat : ℝ := flPrefixCorrectedSumSquaresTrajectory fp x n with hQhat
  set Qexact : ℝ := prefixCorrectedSumSquares x n with hQexact
  set d : ℝ := (n : ℝ) - 1 with hd
  have hden : d ≠ 0 := by
    have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
    rw [hd]
    linarith
  have hdenAbs_pos : 0 < |d| := abs_pos.mpr hden
  obtain ⟨δ, hδ, hdiv⟩ := fp.model_div Qhat d hden
  have hQprev :
      |Qhat - Qexact| ≤
        flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x n := by
    simpa [hQhat, hQexact] using
      flPrefixCorrectedSumSquaresTrajectory_abs_error_le_budget fp x hγ n
  have hquot :
      |Qhat / d - Qexact / d| ≤
        flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x n / |d| := by
    calc
      |Qhat / d - Qexact / d| = |(Qhat - Qexact) / d| := by
        field_simp [hden]
      _ = |Qhat - Qexact| / |d| := by
        rw [abs_div]
      _ ≤ flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x n / |d| :=
        div_le_div_of_nonneg_right hQprev (le_of_lt hdenAbs_pos)
  have hround :
      |Qhat / d * (1 + δ) - Qhat / d| ≤ |Qhat / d| * fp.u := by
    calc
      |Qhat / d * (1 + δ) - Qhat / d|
          = |Qhat / d * δ| := by ring_nf
      _ = |Qhat / d| * |δ| := by rw [abs_mul]
      _ ≤ |Qhat / d| * fp.u :=
        mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
  have hsplit :
      Qhat / d * (1 + δ) - Qexact / d =
        (Qhat / d * (1 + δ) - Qhat / d) +
          (Qhat / d - Qexact / d) := by
    ring
  calc
    |flSampleVarianceUpdate fp x n - sampleVariancePrefix x n|
        = |Qhat / d * (1 + δ) - Qexact / d| := by
          simp [flSampleVarianceUpdate, sampleVariancePrefix, ← hQhat,
            ← hQexact, ← hd, hdiv]
    _ = |(Qhat / d * (1 + δ) - Qhat / d) +
          (Qhat / d - Qexact / d)| := by
          rw [hsplit]
    _ ≤ |Qhat / d * (1 + δ) - Qhat / d| + |Qhat / d - Qexact / d| :=
          abs_add_le _ _
    _ ≤ |Qhat / d| * fp.u +
        flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x n / |d| :=
          add_le_add hround hquot
    _ = flSampleVarianceUpdateAbsErrorBudget fp x n := by
          simp [flSampleVarianceUpdateAbsErrorBudget, hQhat, hd]
          ring_nf

end NumStability
