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
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.Analysis.Statistics.SampleVariance.Core
import NumStability.Analysis.Statistics.SampleVariance.TwoPass
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.FloatingPoint.Model

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






































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- In exact arithmetic, the two-pass and one-pass sample-variance formulae
are equal. -/
theorem sampleVarianceTwoPass_eq_onePass {n : ℕ} (x : Fin n → ℝ)
    (hn : (n : ℝ) ≠ 0) :
    sampleVarianceTwoPass x = sampleVarianceOnePass x := by
  unfold sampleVarianceTwoPass sampleVarianceOnePass
  rw [sum_sq_sub_sampleMean_eq x hn]

/-- The sample mean shifts by the same constant as the data. -/
theorem sampleMean_shift {n : ℕ} (x : Fin n → ℝ) (d : ℝ) (hn : (n : ℝ) ≠ 0) :
    sampleMean (fun i => x i - d) = sampleMean x - d := by
  unfold sampleMean
  simp [Finset.sum_sub_distrib, Finset.sum_const]
  field_simp [hn]

/-- The two-pass sample variance is invariant under shifting all data by the
same constant. -/
theorem sampleVarianceTwoPass_shift_eq {n : ℕ} (x : Fin n → ℝ) (d : ℝ)
    (hn : (n : ℝ) ≠ 0) :
    sampleVarianceTwoPass (fun i => x i - d) = sampleVarianceTwoPass x := by
  unfold sampleVarianceTwoPass
  rw [sampleMean_shift x d hn]
  congr
  ext i
  ring

/-- The shifted one-pass formula is exactly the same variance as the two-pass
formula in real arithmetic. -/
theorem sampleVarianceShiftedOnePass_eq_twoPass {n : ℕ} (x : Fin n → ℝ) (d : ℝ)
    (hn : (n : ℝ) ≠ 0) :
    sampleVarianceShiftedOnePass x d = sampleVarianceTwoPass x := by
  unfold sampleVarianceShiftedOnePass
  rw [← sampleVarianceTwoPass_eq_onePass (fun i => x i - d) hn]
  exact sampleVarianceTwoPass_shift_eq x d hn

/-- Prefix deviations from the prefix mean sum to zero. -/
theorem prefixDeviationSum_eq_zero (x : ℕ → ℝ) {k : ℕ} (hk : (k : ℝ) ≠ 0) :
    ∑ j ∈ Finset.range k, (x j - prefixMean x k) = 0 := by
  unfold prefixMean
  rw [Finset.sum_sub_distrib]
  simp [Finset.sum_const]
  field_simp [hk]
  ring

/-- Exact update formula for the prefix mean:
`M_{k+1} = M_k + (x_k - M_k)/(k+1)`. -/
theorem prefixMean_succ (x : ℕ → ℝ) {k : ℕ} (hk : (k : ℝ) ≠ 0) :
    prefixMean x (k + 1) =
      prefixMean x k + (x k - prefixMean x k) / ((k + 1 : ℕ) : ℝ) := by
  unfold prefixMean
  rw [Finset.sum_range_succ]
  have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero k)
  field_simp [hk, hk1]
  simp only [Nat.cast_add, Nat.cast_one]
  ring_nf

/-- Exact update formula for the corrected sum of squares:
`Q_{k+1} = Q_k + k/(k+1) * (x_k - M_k)^2`. -/
theorem prefixCorrectedSumSquares_succ (x : ℕ → ℝ) {k : ℕ}
    (hk : (k : ℝ) ≠ 0) :
    prefixCorrectedSumSquares x (k + 1) =
      prefixCorrectedSumSquares x k +
        (k : ℝ) / ((k + 1 : ℕ) : ℝ) * (x k - prefixMean x k) ^ 2 := by
  unfold prefixCorrectedSumSquares
  rw [Finset.sum_range_succ]
  set M : ℝ := prefixMean x k with hM
  set d : ℝ := x k - M with hd
  set t : ℝ := d / ((k + 1 : ℕ) : ℝ) with ht
  have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero k)
  have hmean : prefixMean x (k + 1) = M + t := by
    rw [prefixMean_succ x hk, ← hM, ← hd, ← ht]
  have hdev : ∑ j ∈ Finset.range k, (x j - M) = 0 := by
    rw [hM]
    exact prefixDeviationSum_eq_zero x hk
  have hold :
      (∑ j ∈ Finset.range k, (x j - prefixMean x (k + 1)) ^ 2) =
        (∑ j ∈ Finset.range k, (x j - M) ^ 2) + (k : ℝ) * t ^ 2 := by
    rw [hmean]
    calc
      (∑ j ∈ Finset.range k, (x j - (M + t)) ^ 2)
          = ∑ j ∈ Finset.range k,
              ((x j - M) ^ 2 - 2 * t * (x j - M) + t ^ 2) := by
              congr
              ext j
              ring
      _ = (∑ j ∈ Finset.range k, (x j - M) ^ 2) -
            (∑ j ∈ Finset.range k, 2 * t * (x j - M)) +
            (∑ j ∈ Finset.range k, t ^ 2) := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = (∑ j ∈ Finset.range k, (x j - M) ^ 2) -
            2 * t * (∑ j ∈ Finset.range k, (x j - M)) +
            (k : ℝ) * t ^ 2 := by
              rw [Finset.mul_sum]
              simp [Finset.sum_const]
      _ = (∑ j ∈ Finset.range k, (x j - M) ^ 2) + (k : ℝ) * t ^ 2 := by
              rw [hdev]
              ring
  have hnew :
      (x k - prefixMean x (k + 1)) ^ 2 =
        ((k : ℝ) / ((k + 1 : ℕ) : ℝ) * d) ^ 2 := by
    rw [hmean, ht, hd]
    field_simp [hk1]
    simp only [Nat.cast_add, Nat.cast_one]
    ring_nf
  rw [hold, hnew]
  set Q : ℝ := ∑ j ∈ Finset.range k, (x j - M) ^ 2
  rw [ht]
  field_simp [hk1]
  simp only [Nat.cast_add, Nat.cast_one]
  ring_nf

/-- One rounded step of Higham §1.9's updated mean recurrence, starting from
an already stored mean `M` and adding the next sample `x`. -/
noncomputable def flPrefixMeanStep (fp : FPModel) (M x : ℝ) (k : ℕ) : ℝ :=
  fp.fl_add M (fp.fl_div (fp.fl_sub x M) ((k + 1 : ℕ) : ℝ))

/-- Exact counterpart of `flPrefixMeanStep`. -/
noncomputable def prefixMeanStepExact (M x : ℝ) (k : ℕ) : ℝ :=
  M + (x - M) / ((k + 1 : ℕ) : ℝ)

/-- One rounded step of Higham §1.9's corrected-sum-of-squares recurrence,
starting from already stored `Q` and mean `M`. -/
noncomputable def flPrefixCorrectedSumSquaresStep
    (fp : FPModel) (Q M x : ℝ) (k : ℕ) : ℝ :=
  let d := fp.fl_sub x M
  let sq := fp.fl_mul d d
  let coeff := fp.fl_div (k : ℝ) ((k + 1 : ℕ) : ℝ)
  fp.fl_add Q (fp.fl_mul coeff sq)

/-- Exact counterpart of `flPrefixCorrectedSumSquaresStep`. -/
noncomputable def prefixCorrectedSumSquaresStepExact
    (Q M x : ℝ) (k : ℕ) : ℝ :=
  Q + (k : ℝ) / ((k + 1 : ℕ) : ℝ) * (x - M) ^ 2



































/-- The rounded one-step mean update is the exact update with a two-operation
relative factor on the correction term, followed by the final rounded add. -/
theorem flPrefixMeanStep_eq_exact_with_local_errors
    (fp : FPModel) (M x : ℝ) (k : ℕ) (hγ : gammaValid fp 2) :
    ∃ θ δ : ℝ, |θ| ≤ gamma fp 2 ∧ |δ| ≤ fp.u ∧
      flPrefixMeanStep fp M x k =
        (M + ((x - M) / ((k + 1 : ℕ) : ℝ)) * (1 + θ)) * (1 + δ) := by
  have hden : ((k + 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero k)
  have h1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hγ
  obtain ⟨δs, hδs, hsub⟩ := fp.model_sub x M
  obtain ⟨δd, hδd, hdiv⟩ :=
    fp.model_div (fp.fl_sub x M) ((k + 1 : ℕ) : ℝ) hden
  have hδsγ : |δs| ≤ gamma fp 1 :=
    le_trans hδs (u_le_gamma fp one_pos h1)
  have hδdγ : |δd| ≤ gamma fp 1 :=
    le_trans hδd (u_le_gamma fp one_pos h1)
  obtain ⟨θ, hθ, hθeq⟩ :=
    gamma_mul fp 1 1 δs δd hδsγ hδdγ hγ
  obtain ⟨δa, hδa, hadd⟩ :=
    fp.model_add M (fp.fl_div (fp.fl_sub x M) ((k + 1 : ℕ) : ℝ))
  refine ⟨θ, δa, hθ, hδa, ?_⟩
  unfold flPrefixMeanStep
  rw [hadd, hdiv, hsub]
  have hterm :
      ((x - M) * (1 + δs) / ((k + 1 : ℕ) : ℝ)) * (1 + δd) =
        ((x - M) / ((k + 1 : ℕ) : ℝ)) * (1 + θ) := by
    rw [← hθeq]
    field_simp [hden]
  rw [hterm]





























/-- The exact prefix mean satisfies the step formula also at `k = 0`; the
older `prefixMean_succ` theorem keeps the nonzero-`k` hypothesis visible for
source recurrences that divide by the previous sample count. -/
theorem prefixMeanStepExact_prefixMean_eq_succ (x : ℕ → ℝ) (k : ℕ) :
    prefixMeanStepExact (prefixMean x k) (x k) k = prefixMean x (k + 1) := by
  cases k with
  | zero =>
      simp [prefixMeanStepExact, prefixMean]
  | succ k =>
      have hk : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by
        exact_mod_cast (Nat.succ_ne_zero k)
      simpa [prefixMeanStepExact] using (prefixMean_succ x (k := k + 1) hk).symm

/-- Exact sensitivity of one mean-update step to the stored incoming mean. -/
theorem prefixMeanStepExact_sub_prefixMeanStepExact
    (Mhat M x : ℝ) (k : ℕ) :
    prefixMeanStepExact Mhat x k - prefixMeanStepExact M x k =
      ((k : ℝ) / ((k + 1 : ℕ) : ℝ)) * (Mhat - M) := by
  simp only [Nat.cast_add, Nat.cast_one]
  have hden : (k : ℝ) + 1 ≠ 0 := by positivity
  unfold prefixMeanStepExact
  field_simp [hden]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

/-- Rounded trajectory generated by Higham §1.9's updated mean recurrence.
The initial `0` is only a seed; after the first update the recurrence has seen
one sample. -/
noncomputable def flPrefixMeanTrajectory (fp : FPModel) (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => flPrefixMeanStep fp (flPrefixMeanTrajectory fp x k) (x k) k

/-- Accumulated absolute-error budget for `flPrefixMeanTrajectory`.  The
coefficient `k/(k+1)` is the exact contraction of the previous mean error, and
the remaining two terms are the local division/subtraction factor plus the
final rounded-add factor from `flPrefixMeanStep_abs_error_le`. -/
noncomputable def flPrefixMeanTrajectoryAbsErrorBudget
    (fp : FPModel) (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 =>
      ((k : ℝ) / ((k + 1 : ℕ) : ℝ)) *
          flPrefixMeanTrajectoryAbsErrorBudget fp x k +
        |prefixMeanStepExact (flPrefixMeanTrajectory fp x k) (x k) k| * fp.u +
        |(x k - flPrefixMeanTrajectory fp x k) / ((k + 1 : ℕ) : ℝ)| *
          gamma fp 2 * (1 + fp.u)

theorem flPrefixMeanTrajectoryAbsErrorBudget_nonneg
    (fp : FPModel) (x : ℕ → ℝ) (hγ : gammaValid fp 2) :
    ∀ k : ℕ, 0 ≤ flPrefixMeanTrajectoryAbsErrorBudget fp x k := by
  intro k
  induction k with
  | zero =>
      simp [flPrefixMeanTrajectoryAbsErrorBudget]
  | succ k ih =>
      have hcoef_nonneg :
          0 ≤ (k : ℝ) / ((k : ℝ) + 1) := by
        positivity
      have hlocal1 :
          0 ≤ |prefixMeanStepExact (flPrefixMeanTrajectory fp x k) (x k) k| *
              fp.u :=
        mul_nonneg (abs_nonneg _) fp.u_nonneg
      have hlocal2 :
          0 ≤ |(x k - flPrefixMeanTrajectory fp x k) /
                ((k : ℝ) + 1)| * gamma fp 2 * (1 + fp.u) := by
        exact mul_nonneg
          (mul_nonneg (abs_nonneg _) (gamma_nonneg fp hγ))
          (by linarith [fp.u_nonneg])
      simp [flPrefixMeanTrajectoryAbsErrorBudget, Nat.cast_add, Nat.cast_one]
      exact add_nonneg (add_nonneg (mul_nonneg hcoef_nonneg ih) hlocal1) hlocal2

























































































/-- The exact corrected-sum-of-squares step agrees with the prefix definition
at every prefix length, including the first step `k = 0`. -/
theorem prefixCorrectedSumSquaresStepExact_prefix_eq_succ
    (x : ℕ → ℝ) (k : ℕ) :
    prefixCorrectedSumSquaresStepExact
        (prefixCorrectedSumSquares x k) (prefixMean x k) (x k) k =
      prefixCorrectedSumSquares x (k + 1) := by
  cases k with
  | zero =>
      simp [prefixCorrectedSumSquaresStepExact, prefixCorrectedSumSquares,
        prefixMean]
  | succ k =>
      have hk : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by
        exact_mod_cast (Nat.succ_ne_zero k)
      simpa [prefixCorrectedSumSquaresStepExact] using
        (prefixCorrectedSumSquares_succ x (k := k + 1) hk).symm

/-- Exact perturbation bound for one corrected-sum-of-squares update.  A stored
`Q` error enters additively, while a stored mean error is multiplied by the
coefficient and by the sum of the two exact/perturbed deviations. -/
theorem prefixCorrectedSumSquaresStepExact_abs_sub_le
    (Qhat Q Mhat M x : ℝ) (k : ℕ) :
    |prefixCorrectedSumSquaresStepExact Qhat Mhat x k -
        prefixCorrectedSumSquaresStepExact Q M x k| ≤
      |Qhat - Q| +
        |(k : ℝ) / ((k + 1 : ℕ) : ℝ)| * |Mhat - M| *
          (|x - Mhat| + |x - M|) := by
  set c : ℝ := (k : ℝ) / ((k + 1 : ℕ) : ℝ) with hc
  have hsquare :
      |(x - Mhat) ^ 2 - (x - M) ^ 2| ≤
        |Mhat - M| * (|x - Mhat| + |x - M|) := by
    have hfactor :
        (x - Mhat) ^ 2 - (x - M) ^ 2 =
          ((x - Mhat) - (x - M)) * ((x - Mhat) + (x - M)) := by
      ring
    calc
      |(x - Mhat) ^ 2 - (x - M) ^ 2|
          = |((x - Mhat) - (x - M)) * ((x - Mhat) + (x - M))| := by
            rw [hfactor]
      _ = |Mhat - M| * |(x - Mhat) + (x - M)| := by
            rw [abs_mul]
            have hdiff : (x - Mhat) - (x - M) = -(Mhat - M) := by ring
            rw [hdiff, abs_neg]
      _ ≤ |Mhat - M| * (|x - Mhat| + |x - M|) :=
            mul_le_mul_of_nonneg_left
              (abs_add_le (x - Mhat) (x - M)) (abs_nonneg _)
  have hterm :
      |c * ((x - Mhat) ^ 2 - (x - M) ^ 2)| ≤
        |c| * |Mhat - M| * (|x - Mhat| + |x - M|) := by
    calc
      |c * ((x - Mhat) ^ 2 - (x - M) ^ 2)|
          = |c| * |(x - Mhat) ^ 2 - (x - M) ^ 2| := by
            rw [abs_mul]
      _ ≤ |c| * (|Mhat - M| * (|x - Mhat| + |x - M|)) :=
            mul_le_mul_of_nonneg_left hsquare (abs_nonneg _)
      _ = |c| * |Mhat - M| * (|x - Mhat| + |x - M|) := by
            ring
  have hsplit :
      prefixCorrectedSumSquaresStepExact Qhat Mhat x k -
          prefixCorrectedSumSquaresStepExact Q M x k =
        (Qhat - Q) + c * ((x - Mhat) ^ 2 - (x - M) ^ 2) := by
    unfold prefixCorrectedSumSquaresStepExact
    rw [hc]
    ring
  calc
    |prefixCorrectedSumSquaresStepExact Qhat Mhat x k -
        prefixCorrectedSumSquaresStepExact Q M x k|
        = |(Qhat - Q) + c * ((x - Mhat) ^ 2 - (x - M) ^ 2)| := by
          rw [hsplit]
    _ ≤ |Qhat - Q| + |c * ((x - Mhat) ^ 2 - (x - M) ^ 2)| :=
          abs_add_le _ _
    _ ≤ |Qhat - Q| +
        |(k : ℝ) / ((k + 1 : ℕ) : ℝ)| * |Mhat - M| *
          (|x - Mhat| + |x - M|) := by
          have hterm' :
              |(k : ℝ) / ((k + 1 : ℕ) : ℝ) *
                  ((x - Mhat) ^ 2 - (x - M) ^ 2)| ≤
                |(k : ℝ) / ((k + 1 : ℕ) : ℝ)| * |Mhat - M| *
                  (|x - Mhat| + |x - M|) := by
            simpa [hc] using hterm
          exact add_le_add (le_refl _) hterm'

/-- The rounded one-step corrected-sum-of-squares update is the exact update
with a five-operation relative factor on the new positive term, followed by
the final rounded add. -/
theorem flPrefixCorrectedSumSquaresStep_eq_exact_with_local_errors
    (fp : FPModel) (Q M x : ℝ) (k : ℕ) (hγ : gammaValid fp 5) :
    ∃ θ δ : ℝ, |θ| ≤ gamma fp 5 ∧ |δ| ≤ fp.u ∧
      flPrefixCorrectedSumSquaresStep fp Q M x k =
        (Q + ((k : ℝ) / ((k + 1 : ℕ) : ℝ) * (x - M) ^ 2) *
          (1 + θ)) * (1 + δ) := by
  have hden : ((k + 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero k)
  have h1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hγ
  have h3 : gammaValid fp 3 := gammaValid_mono fp (by omega) hγ
  have h4 : gammaValid fp 4 := gammaValid_mono fp (by omega) hγ
  obtain ⟨θsq, hθsq, hsq⟩ :=
    flSquaredDeviationWithMean_eq_mul_one_add_gamma3 fp x M h3
  obtain ⟨δc, hδc, hcoeff⟩ :=
    fp.model_div (k : ℝ) ((k + 1 : ℕ) : ℝ) hden
  have hδcγ : |δc| ≤ gamma fp 1 :=
    le_trans hδc (u_le_gamma fp one_pos h1)
  obtain ⟨θ4, hθ4, hθ4eq⟩ :=
    gamma_mul fp 1 3 δc θsq hδcγ hθsq h4
  obtain ⟨δt, hδt, htermMul⟩ :=
    fp.model_mul (fp.fl_div (k : ℝ) ((k + 1 : ℕ) : ℝ))
      (fp.fl_mul (fp.fl_sub x M) (fp.fl_sub x M))
  have hδtγ : |δt| ≤ gamma fp 1 :=
    le_trans hδt (u_le_gamma fp one_pos h1)
  obtain ⟨θ5, hθ5, hθ5eq⟩ :=
    gamma_mul fp 4 1 θ4 δt hθ4 hδtγ hγ
  obtain ⟨δa, hδa, hadd⟩ :=
    fp.model_add Q
      (fp.fl_mul (fp.fl_div (k : ℝ) ((k + 1 : ℕ) : ℝ))
        (fp.fl_mul (fp.fl_sub x M) (fp.fl_sub x M)))
  refine ⟨θ5, δa, hθ5, hδa, ?_⟩
  unfold flPrefixCorrectedSumSquaresStep
  rw [hadd, htermMul, hcoeff, hsq]
  have hterm :
      (((k : ℝ) / ((k + 1 : ℕ) : ℝ) * (1 + δc)) *
          ((x - M) ^ 2 * (1 + θsq))) * (1 + δt) =
        ((k : ℝ) / ((k + 1 : ℕ) : ℝ) * (x - M) ^ 2) * (1 + θ5) := by
    rw [← hθ5eq, ← hθ4eq]
    ring
  rw [hterm]



































/-- Rounded trajectory generated by Higham §1.9's corrected-sum-of-squares
update recurrence, driven by the rounded prefix-mean trajectory. -/
noncomputable def flPrefixCorrectedSumSquaresTrajectory
    (fp : FPModel) (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 =>
      flPrefixCorrectedSumSquaresStep fp
        (flPrefixCorrectedSumSquaresTrajectory fp x k)
        (flPrefixMeanTrajectory fp x k) (x k) k

/-- Accumulated absolute-error budget for the rounded corrected-sum-of-squares
trajectory.  Each step adds the local rounded-update error and the propagated
effects of the previous `Q_k` and rounded-mean errors. -/
noncomputable def flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget
    (fp : FPModel) (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 =>
      |prefixCorrectedSumSquaresStepExact
          (flPrefixCorrectedSumSquaresTrajectory fp x k)
          (flPrefixMeanTrajectory fp x k) (x k) k| * fp.u +
        |(k : ℝ) / ((k + 1 : ℕ) : ℝ) *
          (x k - flPrefixMeanTrajectory fp x k) ^ 2| *
            gamma fp 5 * (1 + fp.u) +
        (flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x k +
          |(k : ℝ) / ((k + 1 : ℕ) : ℝ)| *
            flPrefixMeanTrajectoryAbsErrorBudget fp x k *
              (|x k - flPrefixMeanTrajectory fp x k| +
                |x k - prefixMean x k|))

theorem flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget_nonneg
    (fp : FPModel) (x : ℕ → ℝ) (hγ : gammaValid fp 5) :
    ∀ k : ℕ,
      0 ≤ flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x k := by
  intro k
  induction k with
  | zero =>
      simp [flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget]
  | succ k ih =>
      have hγ2 : gammaValid fp 2 := gammaValid_mono fp (by omega) hγ
      have hMeanBudget :
          0 ≤ flPrefixMeanTrajectoryAbsErrorBudget fp x k :=
        flPrefixMeanTrajectoryAbsErrorBudget_nonneg fp x hγ2 k
      have hLocalRound :
          0 ≤ |prefixCorrectedSumSquaresStepExact
                (flPrefixCorrectedSumSquaresTrajectory fp x k)
                (flPrefixMeanTrajectory fp x k) (x k) k| * fp.u :=
        mul_nonneg (abs_nonneg _) fp.u_nonneg
      have hLocalTerm :
          0 ≤ |(k : ℝ) / ((k : ℝ) + 1)| *
              (x k - flPrefixMeanTrajectory fp x k) ^ 2 *
              gamma fp 5 * (1 + fp.u) := by
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (abs_nonneg _) (sq_nonneg _))
            (gamma_nonneg fp hγ))
          (by linarith [fp.u_nonneg])
      have hMeanSens :
          0 ≤ |(k : ℝ) / ((k : ℝ) + 1)| *
              flPrefixMeanTrajectoryAbsErrorBudget fp x k *
                (|x k - flPrefixMeanTrajectory fp x k| +
                  |x k - prefixMean x k|) :=
        mul_nonneg
          (mul_nonneg (abs_nonneg _) hMeanBudget)
          (add_nonneg (abs_nonneg _) (abs_nonneg _))
      simp [flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget]
      exact add_nonneg (add_nonneg hLocalRound hLocalTerm)
        (add_nonneg ih hMeanSens)














































































































































/-- Exact sample variance obtained from the prefix corrected-sum-of-squares
state generated by the update recurrence. -/
noncomputable def sampleVariancePrefix (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  prefixCorrectedSumSquares x n / ((n : ℝ) - 1)

/-- Rounded final quotient after the rounded Higham §1.9 update trajectory. -/
noncomputable def flSampleVarianceUpdate (fp : FPModel) (x : ℕ → ℝ)
    (n : ℕ) : ℝ :=
  fp.fl_div (flPrefixCorrectedSumSquaresTrajectory fp x n) ((n : ℝ) - 1)

/-- Absolute-error budget for the rounded update algorithm's final variance
quotient: the propagated `Q_n` error divided by `|n-1|`, plus the final rounded
division cost. -/
noncomputable def flSampleVarianceUpdateAbsErrorBudget
    (fp : FPModel) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x n /
      |(n : ℝ) - 1| +
    |flPrefixCorrectedSumSquaresTrajectory fp x n / ((n : ℝ) - 1)| * fp.u

theorem flSampleVarianceUpdateAbsErrorBudget_nonneg
    (fp : FPModel) (x : ℕ → ℝ) {n : ℕ} (hn : 1 < n)
    (hγ : gammaValid fp 5) :
    0 ≤ flSampleVarianceUpdateAbsErrorBudget fp x n := by
  have hden : ((n : ℝ) - 1) ≠ 0 := by
    have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  have hdenAbs : 0 ≤ |(n : ℝ) - 1| := abs_nonneg _
  have hQBudget :
      0 ≤ flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x n :=
    flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget_nonneg fp x hγ n
  have hfirst :
      0 ≤ flPrefixCorrectedSumSquaresTrajectoryAbsErrorBudget fp x n /
          |(n : ℝ) - 1| :=
    div_nonneg hQBudget hdenAbs
  have hsecond :
      0 ≤ |flPrefixCorrectedSumSquaresTrajectory fp x n / ((n : ℝ) - 1)| *
          fp.u :=
    mul_nonneg (abs_nonneg _) fp.u_nonneg
  simp [flSampleVarianceUpdateAbsErrorBudget]
  exact add_nonneg hfirst hsecond


















































































































































































































-- ============================================================
-- Concrete binary32 one-pass trace for Higham §1.9
-- ============================================================

















































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































-- ============================================================
-- Supplied rounded-aggregate negative final-operation trace
-- ============================================================





































































































-- ============================================================
-- Higham Problem 1.7 condition-number closed forms
-- ============================================================







































































































































































































































































































































































end NumStability
