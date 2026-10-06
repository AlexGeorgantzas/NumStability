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
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Statistics.SampleVariance.Core
import NumStability.Analysis.Summation.ErrorBounds

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




















































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































-- ============================================================
-- Concrete binary32 one-pass trace for Higham §1.9
-- ============================================================

















































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































-- ============================================================
-- Supplied rounded-aggregate negative final-operation trace
-- ============================================================





































































































-- ============================================================
-- Higham Problem 1.7 condition-number closed forms
-- ============================================================

/-- Denominator `(n-1)V(x)` appearing in the sample-variance condition-number
formulae from Problem 1.7. -/
noncomputable def sampleVarianceConditionDen {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ((n : ℝ) - 1) * sampleVarianceTwoPass x

/-- Closed-form componentwise condition-number expression from Problem 1.7. -/
noncomputable def sampleVarianceKappaCClosed {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  2 * (∑ i : Fin n, |x i - sampleMean x| * |x i|) /
    sampleVarianceConditionDen x

/-- Closed-form normwise condition-number expression from Problem 1.7. -/
noncomputable def sampleVarianceKappaNClosed {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  2 * vecNorm2 x / Real.sqrt (sampleVarianceConditionDen x)

/-- Expanded normwise expression
`2 * sqrt(1 + n * mean^2 / ((n-1)*V(x)))` from Problem 1.7. -/
noncomputable def sampleVarianceKappaNExpanded {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  2 * Real.sqrt
    (1 + (n : ℝ) * sampleMean x ^ 2 / sampleVarianceConditionDen x)

/-- Linear coefficient in the first-order perturbation of the sample variance
in direction `dx`, normalized by `(n-1)V(x)`.  This is the directional form
behind Problem 1.7's componentwise and normwise condition numbers. -/
noncomputable def sampleVarianceDirectionalCoeff {n : ℕ}
    (x dx : Fin n → ℝ) : ℝ :=
  2 * (∑ i : Fin n, (x i - sampleMean x) * dx i) /
    sampleVarianceConditionDen x

/-- The sample mean is affine along a finite perturbation line. -/
theorem sampleMean_add_scaled {n : ℕ} (x dx : Fin n → ℝ) (t : ℝ)
    (hn : (n : ℝ) ≠ 0) :
    sampleMean (fun i => x i + t * dx i) =
      sampleMean x + t * sampleMean dx := by
  unfold sampleMean
  rw [Finset.sum_add_distrib]
  have hsum_mul : (∑ i : Fin n, t * dx i) = t * ∑ i : Fin n, dx i := by
    rw [Finset.mul_sum]
  rw [hsum_mul]
  field_simp [hn]

/-- Exact finite-difference expansion behind Problem 1.7.  Along the line
`x + t dx`, the sample variance changes by a linear term whose coefficient is
`2*sum((x_i-mean(x))*dx_i)/(n-1)` plus a quadratic remainder. -/
theorem sampleVarianceTwoPass_add_scaled_sub_eq {n : ℕ}
    (x dx : Fin n → ℝ) (t : ℝ)
    (hn0 : (n : ℝ) ≠ 0) (hn1 : (n : ℝ) - 1 ≠ 0) :
    sampleVarianceTwoPass (fun i => x i + t * dx i) -
        sampleVarianceTwoPass x =
      (2 * t * (∑ i : Fin n, (x i - sampleMean x) * dx i) +
        t ^ 2 * (∑ i : Fin n, (dx i - sampleMean dx) ^ 2)) /
        ((n : ℝ) - 1) := by
  have hmean := sampleMean_add_scaled x dx t hn0
  have hdevzero := sampleMean_deviation_sum_eq_zero x hn0
  have hcross :
      (∑ i : Fin n, (x i - sampleMean x) * (dx i - sampleMean dx)) =
        ∑ i : Fin n, (x i - sampleMean x) * dx i := by
    calc
      (∑ i : Fin n, (x i - sampleMean x) * (dx i - sampleMean dx))
          = ∑ i : Fin n,
              ((x i - sampleMean x) * dx i -
                sampleMean dx * (x i - sampleMean x)) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = (∑ i : Fin n, (x i - sampleMean x) * dx i) -
            sampleMean dx * (∑ i : Fin n, (x i - sampleMean x)) := by
              rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = ∑ i : Fin n, (x i - sampleMean x) * dx i := by
              rw [hdevzero]
              ring
  have hsum_expand :
      (∑ i : Fin n,
          ((x i - sampleMean x) + t * (dx i - sampleMean dx)) ^ 2) =
        (∑ i : Fin n, (x i - sampleMean x) ^ 2) +
          2 * t * (∑ i : Fin n, (x i - sampleMean x) * dx i) +
          t ^ 2 * (∑ i : Fin n, (dx i - sampleMean dx) ^ 2) := by
    calc
      (∑ i : Fin n,
          ((x i - sampleMean x) + t * (dx i - sampleMean dx)) ^ 2)
          = ∑ i : Fin n,
              ((x i - sampleMean x) ^ 2 +
                2 * t * ((x i - sampleMean x) * (dx i - sampleMean dx)) +
                t ^ 2 * (dx i - sampleMean dx) ^ 2) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = (∑ i : Fin n, (x i - sampleMean x) ^ 2) +
            2 * t *
              (∑ i : Fin n, (x i - sampleMean x) * (dx i - sampleMean dx)) +
            t ^ 2 * (∑ i : Fin n, (dx i - sampleMean dx) ^ 2) := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
                ← Finset.mul_sum, ← Finset.mul_sum]
      _ = (∑ i : Fin n, (x i - sampleMean x) ^ 2) +
            2 * t * (∑ i : Fin n, (x i - sampleMean x) * dx i) +
            t ^ 2 * (∑ i : Fin n, (dx i - sampleMean dx) ^ 2) := by
              rw [hcross]
  unfold sampleVarianceTwoPass
  rw [hmean]
  have hnum :
      (∑ i : Fin n,
          (x i + t * dx i - (sampleMean x + t * sampleMean dx)) ^ 2) =
        (∑ i : Fin n, (x i - sampleMean x) ^ 2) +
          2 * t * (∑ i : Fin n, (x i - sampleMean x) * dx i) +
          t ^ 2 * (∑ i : Fin n, (dx i - sampleMean dx) ^ 2) := by
    calc
      (∑ i : Fin n,
          (x i + t * dx i - (sampleMean x + t * sampleMean dx)) ^ 2)
          = ∑ i : Fin n,
              ((x i - sampleMean x) + t * (dx i - sampleMean dx)) ^ 2 := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = (∑ i : Fin n, (x i - sampleMean x) ^ 2) +
            2 * t * (∑ i : Fin n, (x i - sampleMean x) * dx i) +
            t ^ 2 * (∑ i : Fin n, (dx i - sampleMean dx) ^ 2) := hsum_expand
  rw [hnum]
  field_simp [hn1]
  ring

/-- Data-dependent quadratic coefficient in the relative finite-difference
remainder from Problem 1.7. -/
noncomputable def sampleVarianceProblem17RelativeRemainderCoeff {n : ℕ}
    (x dx : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, (dx i - sampleMean dx) ^ 2) /
    sampleVarianceConditionDen x

/-- Scalar quadratic envelope for the relative finite-difference remainder in
Problem 1.7. -/
noncomputable def sampleVarianceProblem17RelativeRemainderEnvelope {n : ℕ}
    (x dx : Fin n → ℝ) (t : ℝ) : ℝ :=
  sampleVarianceProblem17RelativeRemainderCoeff x dx * t ^ 2

/-- Exact relative finite-difference expansion behind Problem 1.7: after
subtracting the first-order directional term, the relative sample-variance
change is the named quadratic envelope. -/
theorem sampleVarianceTwoPass_relative_add_scaled_sub_linear_eq_remainder
    {n : ℕ} (x dx : Fin n → ℝ) (t : ℝ)
    (hn0 : (n : ℝ) ≠ 0) (hn1 : (n : ℝ) - 1 ≠ 0)
    (hV : sampleVarianceTwoPass x ≠ 0) :
    ((sampleVarianceTwoPass (fun i => x i + t * dx i) -
          sampleVarianceTwoPass x) / sampleVarianceTwoPass x -
        t * sampleVarianceDirectionalCoeff x dx) =
      sampleVarianceProblem17RelativeRemainderEnvelope x dx t := by
  have hfd := sampleVarianceTwoPass_add_scaled_sub_eq x dx t hn0 hn1
  unfold sampleVarianceProblem17RelativeRemainderEnvelope
  unfold sampleVarianceProblem17RelativeRemainderCoeff
  unfold sampleVarianceDirectionalCoeff sampleVarianceConditionDen
  rw [hfd]
  field_simp [hn1, hV]
  ring

/-- Literal Landau form of the Problem 1.7 finite-difference remainder: for
fixed data and perturbation direction, the relative remainder is `O(t^2)` as
the perturbation scale `t` tends to zero. -/
theorem sampleVarianceProblem17RelativeRemainderEnvelope_isBigO {n : ℕ}
    (x dx : Fin n → ℝ) :
    (fun t : ℝ => sampleVarianceProblem17RelativeRemainderEnvelope x dx t)
      =O[𝓝 0] (fun t : ℝ => t ^ 2) := by
  simpa [sampleVarianceProblem17RelativeRemainderEnvelope] using
    (Asymptotics.isBigO_const_mul_self
      (sampleVarianceProblem17RelativeRemainderCoeff x dx)
      (fun t : ℝ => t ^ 2) (𝓝 0))

/-- Componentwise first-order perturbations bounded by `|x_i|` are controlled
by the closed-form componentwise condition number from Problem 1.7. -/
theorem sampleVarianceDirectionalCoeff_componentwise_le {n : ℕ}
    (x dx : Fin n → ℝ) (hDpos : 0 < sampleVarianceConditionDen x)
    (hdx : ∀ i, |dx i| ≤ |x i|) :
    |sampleVarianceDirectionalCoeff x dx| ≤ sampleVarianceKappaCClosed x := by
  set D : ℝ := sampleVarianceConditionDen x with hD
  set T : ℝ := ∑ i : Fin n, (x i - sampleMean x) * dx i with hT
  set S : ℝ := ∑ i : Fin n, |x i - sampleMean x| * |x i| with hS
  have hDpos' : 0 < D := by
    rw [hD]
    exact hDpos
  have hT_abs_le : |T| ≤ S := by
    rw [hT, hS]
    calc
      |∑ i : Fin n, (x i - sampleMean x) * dx i|
          ≤ ∑ i : Fin n, |(x i - sampleMean x) * dx i| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin n, |x i - sampleMean x| * |dx i| := by
            apply Finset.sum_congr rfl
            intro i _
            rw [abs_mul]
      _ ≤ ∑ i : Fin n, |x i - sampleMean x| * |x i| := by
            exact Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left (hdx i) (abs_nonneg _)
  unfold sampleVarianceDirectionalCoeff sampleVarianceKappaCClosed
  rw [← hD, ← hT, ← hS]
  calc
    |2 * T / D| = 2 * |T| / D := by
      rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos hDpos']
    _ ≤ 2 * S / D := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hT_abs_le (by norm_num)) (le_of_lt hDpos')

/-- Normwise first-order perturbations with `||dx||₂ <= ||x||₂` are controlled
by the closed-form normwise condition number from Problem 1.7. -/
theorem sampleVarianceDirectionalCoeff_normwise_le {n : ℕ}
    (x dx : Fin n → ℝ) (hDpos : 0 < sampleVarianceConditionDen x)
    (hdx : vecNorm2 dx ≤ vecNorm2 x) :
    |sampleVarianceDirectionalCoeff x dx| ≤ sampleVarianceKappaNClosed x := by
  set D : ℝ := sampleVarianceConditionDen x with hD
  set dev : Fin n → ℝ := fun i => x i - sampleMean x with hdev
  set T : ℝ := ∑ i : Fin n, dev i * dx i with hT
  have hDpos' : 0 < D := by
    rw [hD]
    exact hDpos
  have hDne : D ≠ 0 := ne_of_gt hDpos'
  have hsqrtD_pos : 0 < Real.sqrt D := Real.sqrt_pos.2 hDpos'
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    intro hzero
    have hDzero : D = 0 := by
      simp [hD, sampleVarianceConditionDen, hzero]
    linarith
  have hden_eq : D = ∑ i : Fin n, (x i - sampleMean x) ^ 2 := by
    rw [hD]
    unfold sampleVarianceConditionDen sampleVarianceTwoPass
    field_simp [hn1]
  have hdev_norm : vecNorm2 dev = Real.sqrt D := by
    have hsum_eq : (∑ i : Fin n, (x i - sampleMean x) ^ 2) = D := by
      exact hden_eq.symm
    unfold dev vecNorm2 vecNorm2Sq
    simpa using congrArg Real.sqrt hsum_eq
  have hT_abs_le : |T| ≤ Real.sqrt D * vecNorm2 x := by
    have hcs := abs_vecInnerProduct_le_vecNorm2_mul dev dx
    calc
      |T| = |∑ i : Fin n, dev i * dx i| := by rw [hT]
      _ ≤ vecNorm2 dev * vecNorm2 dx := hcs
      _ ≤ Real.sqrt D * vecNorm2 x := by
        rw [hdev_norm]
        exact mul_le_mul_of_nonneg_left hdx (le_of_lt hsqrtD_pos)
  unfold sampleVarianceDirectionalCoeff sampleVarianceKappaNClosed
  rw [← hD, ← hT]
  calc
    |2 * (∑ i : Fin n, (x i - sampleMean x) * dx i) / D|
        = |2 * T / D| := by
            have hsumT : (∑ i : Fin n, (x i - sampleMean x) * dx i) = T := by
              rw [hT]
            rw [hsumT]
    _ = 2 * |T| / D := by
          rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
            abs_of_pos hDpos']
    _ ≤ 2 * (Real.sqrt D * vecNorm2 x) / D := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hT_abs_le (by norm_num))
            (le_of_lt hDpos')
    _ = 2 * vecNorm2 x / Real.sqrt D := by
          field_simp [hDne, ne_of_gt hsqrtD_pos]
          rw [Real.sq_sqrt (le_of_lt hDpos')]
          ring

/-- The denominator `(n-1)V(x)` is the corrected sum of squares, provided the
source denominator `n-1` is nonzero. -/
theorem sampleVarianceConditionDen_eq_sum_sq_deviation {n : ℕ}
    (x : Fin n → ℝ) (hn1 : (n : ℝ) - 1 ≠ 0) :
    sampleVarianceConditionDen x =
      ∑ i : Fin n, (x i - sampleMean x) ^ 2 := by
  unfold sampleVarianceConditionDen sampleVarianceTwoPass
  field_simp [hn1]

/-- Problem 1.7 algebra: `||x||₂² = (n-1)V(x) + n * mean(x)^2`. -/
theorem sampleVariance_vecNorm2Sq_eq_conditionDen_add_mean_sq {n : ℕ}
    (x : Fin n → ℝ) (hn0 : (n : ℝ) ≠ 0) (hn1 : (n : ℝ) - 1 ≠ 0) :
    vecNorm2Sq x =
      sampleVarianceConditionDen x + (n : ℝ) * sampleMean x ^ 2 := by
  have hdev := sum_sq_sub_sampleMean_eq x hn0
  have hden := sampleVarianceConditionDen_eq_sum_sq_deviation x hn1
  calc
    vecNorm2Sq x = ∑ i : Fin n, x i ^ 2 := rfl
    _ = (∑ i : Fin n, (x i - sampleMean x) ^ 2) +
        (n : ℝ) * sampleMean x ^ 2 := by
          rw [hdev]
          unfold sampleMean
          field_simp [hn0]
          ring
    _ = sampleVarianceConditionDen x + (n : ℝ) * sampleMean x ^ 2 := by
          rw [← hden]

/-- The two displayed normwise condition-number formulae in Problem 1.7 agree,
under the usual nonzero positive-variance denominator assumptions. -/
theorem sampleVarianceKappaNClosed_eq_expanded {n : ℕ}
    (x : Fin n → ℝ) (hn0 : (n : ℝ) ≠ 0) (hn1 : (n : ℝ) - 1 ≠ 0)
    (hDpos : 0 < sampleVarianceConditionDen x) :
    sampleVarianceKappaNClosed x = sampleVarianceKappaNExpanded x := by
  set D : ℝ := sampleVarianceConditionDen x with hD
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hnorm :=
    sampleVariance_vecNorm2Sq_eq_conditionDen_add_mean_sq x hn0 hn1
  have harg :
      vecNorm2Sq x / D =
        1 + (n : ℝ) * sampleMean x ^ 2 / D := by
    rw [← hD] at hnorm
    rw [hnorm]
    field_simp [hDne]
  unfold sampleVarianceKappaNClosed sampleVarianceKappaNExpanded
  rw [← hD, ← harg]
  unfold vecNorm2
  rw [Real.sqrt_div (vecNorm2Sq_nonneg x) D]
  ring

/-- Problem 1.7 inequality between the displayed closed forms:
the componentwise condition-number formula is bounded by the normwise one. -/
theorem sampleVarianceKappaCClosed_le_KappaNClosed {n : ℕ}
    (x : Fin n → ℝ) (hDpos : 0 < sampleVarianceConditionDen x) :
    sampleVarianceKappaCClosed x ≤ sampleVarianceKappaNClosed x := by
  set D : ℝ := sampleVarianceConditionDen x with hD
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hsqrtD_pos : 0 < Real.sqrt D := Real.sqrt_pos.2 hDpos
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    intro hzero
    have hDzero : D = 0 := by
      simp [hD, sampleVarianceConditionDen, hzero]
    linarith
  set dev : Fin n → ℝ := fun i => x i - sampleMean x
  set S : ℝ := ∑ i : Fin n, |dev i| * |x i|
  have hS_nonneg : 0 ≤ S := by
    unfold S
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hS_abs : |S| = S := abs_of_nonneg hS_nonneg
  have hcs := abs_vecInnerProduct_le_vecNorm2_mul
    (fun i : Fin n => |dev i|) (fun i : Fin n => |x i|)
  have hS_le_norms : S ≤ vecNorm2 dev * vecNorm2 x := by
    have hsum :
        (∑ i : Fin n, |dev i| * |x i|) = S := rfl
    rw [hsum] at hcs
    rw [hS_abs, vecNorm2_abs dev, vecNorm2_abs x] at hcs
    exact hcs
  have hden_eq := sampleVarianceConditionDen_eq_sum_sq_deviation x hn1
  have hdev_norm : vecNorm2 dev = Real.sqrt D := by
    have hsum_eq : (∑ i : Fin n, (x i - sampleMean x) ^ 2) = D := by
      rw [← hden_eq, ← hD]
    unfold dev vecNorm2 vecNorm2Sq
    simpa using congrArg Real.sqrt hsum_eq
  have hS_le : S ≤ Real.sqrt D * vecNorm2 x := by
    simpa [hdev_norm] using hS_le_norms
  have hdiv :
      S / D ≤ (Real.sqrt D * vecNorm2 x) / D :=
    div_le_div_of_nonneg_right hS_le (le_of_lt hDpos)
  have hscaled :
      2 * (S / D) ≤ 2 * ((Real.sqrt D * vecNorm2 x) / D) :=
    mul_le_mul_of_nonneg_left hdiv (by norm_num)
  unfold sampleVarianceKappaCClosed sampleVarianceKappaNClosed
  rw [← hD]
  calc
    2 * (∑ i : Fin n, |x i - sampleMean x| * |x i|) / D
        = 2 * (S / D) := by
          unfold S dev
          ring
    _ ≤ 2 * ((Real.sqrt D * vecNorm2 x) / D) := hscaled
    _ = 2 * vecNorm2 x / Real.sqrt D := by
          field_simp [hDne, ne_of_gt hsqrtD_pos]
          rw [Real.sq_sqrt (le_of_lt hDpos)]
          ring

end NumStability
