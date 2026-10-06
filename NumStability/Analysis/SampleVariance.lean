-- Analysis/SampleVariance.lean
--
-- Exact sample-variance algebra for Higham Chapter 1, Section 1.9.

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
import NumStability.Analysis.Error
import NumStability.Analysis.FloatingPointArithmetic
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Summation.ErrorBounds

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

/-- Sample mean of `n` real data values. -/
noncomputable def sampleMean {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (∑ i, x i) / (n : ℝ)

/-- Floating-point sample mean computed by recursive summation followed by one
rounded division by `n`. -/
noncomputable def flSampleMean (fp : FPModel) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  fp.fl_div (Fin.foldl n (fun acc i => fp.fl_add acc (x i)) 0) (n : ℝ)

/-- Two-pass sample-variance formula `1/(n-1) * ∑ᵢ (xᵢ - mean)^2`. -/
noncomputable def sampleVarianceTwoPass {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (∑ i, (x i - sampleMean x) ^ 2) / ((n : ℝ) - 1)

/-- Two-pass sample-variance formula when the second pass uses an already
computed mean `m`.  This isolates the algebra used in Problem 1.10 before
roundoff from subtraction, squaring, summation, and division is charged. -/
noncomputable def sampleVarianceTwoPassWithMean {n : ℕ} (x : Fin n → ℝ)
    (m : ℝ) : ℝ :=
  (∑ i, (x i - m) ^ 2) / ((n : ℝ) - 1)

/-- Floating-point version of the second pass of the two-pass sample-variance
formula when the supplied mean is `m`: each deviation is rounded, squared by a
rounded multiplication, the squared deviations are summed recursively, and the
final quotient by `n - 1` is rounded. -/
noncomputable def flSampleVarianceTwoPassWithMean (fp : FPModel) {n : ℕ}
    (x : Fin n → ℝ) (m : ℝ) : ℝ :=
  fp.fl_div
    (Fin.foldl n
      (fun acc i =>
        let d := fp.fl_sub (x i) m
        fp.fl_add acc (fp.fl_mul d d))
      0)
    ((n : ℝ) - 1)

/-- Full two-pass floating-point variance kernel using the recursively computed
first-pass mean in the rounded second pass. -/
noncomputable def flSampleVarianceTwoPass (fp : FPModel) {n : ℕ}
    (x : Fin n → ℝ) : ℝ :=
  flSampleVarianceTwoPassWithMean fp x (flSampleMean fp x)

/-- One-pass sample-variance formula
`1/(n-1) * (∑ᵢ xᵢ^2 - (∑ᵢ xᵢ)^2/n)`. -/
noncomputable def sampleVarianceOnePass {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ((∑ i, (x i) ^ 2) - (∑ i, x i) ^ 2 / (n : ℝ)) / ((n : ℝ) - 1)

/-- One-pass sample-variance formula evaluated from already-formed aggregate
quantities `sumSq ≈ ∑xᵢ²` and `sum ≈ ∑xᵢ`.  This is useful for isolating
the final cancellation in Higham §1.9's one-pass warning. -/
noncomputable def sampleVarianceOnePassAggregates
    (n : ℕ) (sumSq sum : ℝ) : ℝ :=
  (sumSq - sum ^ 2 / (n : ℝ)) / ((n : ℝ) - 1)

/-- The ordinary one-pass formula is the aggregate formula with exact
aggregates. -/
theorem sampleVarianceOnePass_eq_fromAggregates {n : ℕ} (x : Fin n → ℝ) :
    sampleVarianceOnePass x =
      sampleVarianceOnePassAggregates n (∑ i, (x i) ^ 2) (∑ i, x i) := by
  rfl

/-- Shifted one-pass formula, obtained by applying the one-pass formula to
`xᵢ - d`.  Higham notes that this exact shift does not change the variance. -/
noncomputable def sampleVarianceShiftedOnePass {n : ℕ} (x : Fin n → ℝ) (d : ℝ) :
    ℝ :=
  sampleVarianceOnePass (fun i => x i - d)

/-- Mean of the first `k` entries of a stream.  This is the prefix version used
in the updating formulae in Higham §1.9. -/
noncomputable def prefixMean (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∑ j ∈ Finset.range k, x j) / (k : ℝ)

/-- Corrected sum of squares `Q_k = ∑_{j<k} (x_j - prefixMean x k)^2`. -/
noncomputable def prefixCorrectedSumSquares (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, (x j - prefixMean x k) ^ 2

/-- The exact expansion underlying the equivalence of the two-pass and
one-pass sample-variance formulas. -/
theorem sum_sq_sub_sampleMean_eq {n : ℕ} (x : Fin n → ℝ) (hn : (n : ℝ) ≠ 0) :
    (∑ i, (x i - sampleMean x) ^ 2) =
      (∑ i, (x i) ^ 2) - (∑ i, x i) ^ 2 / (n : ℝ) := by
  unfold sampleMean
  set S : ℝ := ∑ i, x i with hS
  calc
    (∑ i, (x i - S / (n : ℝ)) ^ 2)
        = ∑ i, ((x i) ^ 2 - 2 * (S / (n : ℝ)) * x i + (S / (n : ℝ)) ^ 2) := by
            congr
            ext i
            ring
    _ = (∑ i, (x i) ^ 2) - 2 * (S / (n : ℝ)) * S +
          (n : ℝ) * (S / (n : ℝ)) ^ 2 := by
            simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum,
              Finset.sum_const, hS]
    _ = (∑ i, (x i) ^ 2) - S ^ 2 / (n : ℝ) := by
            field_simp [hn]
            ring
    _ = (∑ i, (x i) ^ 2) - (∑ i, x i) ^ 2 / (n : ℝ) := by
            rw [hS]

/-- Deviations from the finite sample mean sum to zero. -/
theorem sampleMean_deviation_sum_eq_zero {n : ℕ} (x : Fin n → ℝ)
    (hn : (n : ℝ) ≠ 0) :
    ∑ i, (x i - sampleMean x) = 0 := by
  unfold sampleMean
  rw [Finset.sum_sub_distrib]
  simp [Finset.sum_const]
  field_simp [hn]
  ring

/-- Exact cancellation behind Problem 1.10: if the second pass uses a
perturbed mean `m`, the corrected sum of squares changes by only the quadratic
term `n * (m - mean)^2`; the first-order cross term vanishes because
deviations from the sample mean sum to zero. -/
theorem sum_sq_sub_perturbedMean_eq_sum_sq_sub_sampleMean_add {n : ℕ}
    (x : Fin n → ℝ) (m : ℝ) (hn : (n : ℝ) ≠ 0) :
    (∑ i, (x i - m) ^ 2) =
      (∑ i, (x i - sampleMean x) ^ 2) +
        (n : ℝ) * (m - sampleMean x) ^ 2 := by
  set M : ℝ := sampleMean x with hM
  have hdev : ∑ i : Fin n, (x i - M) = 0 := by
    rw [hM]
    exact sampleMean_deviation_sum_eq_zero x hn
  have hcalc :
      (∑ i : Fin n, (x i - m) ^ 2) =
        (∑ i : Fin n, (x i - M) ^ 2) + (n : ℝ) * (m - M) ^ 2 := by
    calc
      (∑ i : Fin n, (x i - m) ^ 2)
          = ∑ i : Fin n, ((x i - M) + (M - m)) ^ 2 := by
              congr
              ext i
              ring
      _ = ∑ i : Fin n,
            ((x i - M) ^ 2 + 2 * (M - m) * (x i - M) + (M - m) ^ 2) := by
              congr
              ext i
              ring
      _ = (∑ i : Fin n, (x i - M) ^ 2) +
            (∑ i : Fin n, 2 * (M - m) * (x i - M)) +
            (∑ i : Fin n, (M - m) ^ 2) := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = (∑ i : Fin n, (x i - M) ^ 2) +
            2 * (M - m) * (∑ i : Fin n, (x i - M)) +
            (n : ℝ) * (M - m) ^ 2 := by
              rw [Finset.mul_sum]
              simp [Finset.sum_const]
      _ = (∑ i : Fin n, (x i - M) ^ 2) + (n : ℝ) * (m - M) ^ 2 := by
              rw [hdev]
              ring
  simpa [hM] using hcalc

/-- Exact two-pass variance with a perturbed second-pass mean.  The mean error
contributes only the displayed quadratic term before the remaining rounded
arithmetic in Problem 1.10 is modeled. -/
theorem sampleVarianceTwoPassWithMean_eq_twoPass_add {n : ℕ}
    (x : Fin n → ℝ) (m : ℝ) (hn : (n : ℝ) ≠ 0) :
    sampleVarianceTwoPassWithMean x m =
      sampleVarianceTwoPass x +
        (n : ℝ) * (m - sampleMean x) ^ 2 / ((n : ℝ) - 1) := by
  unfold sampleVarianceTwoPassWithMean sampleVarianceTwoPass
  rw [sum_sq_sub_perturbedMean_eq_sum_sq_sub_sampleMean_add x m hn]
  ring

/-- With `n > 1`, using any real second-pass mean can only increase the exact
corrected two-pass variance by the nonnegative quadratic mean-error term. -/
theorem sampleVarianceTwoPass_le_twoPassWithMean {n : ℕ}
    (x : Fin n → ℝ) (m : ℝ) (hn : 1 < n) :
    sampleVarianceTwoPass x ≤ sampleVarianceTwoPassWithMean x m := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (Nat.lt_trans Nat.zero_lt_one hn)
    exact ne_of_gt hnpos
  rw [sampleVarianceTwoPassWithMean_eq_twoPass_add x m hn0]
  have hden : 0 ≤ (n : ℝ) - 1 := by
    have hnreal : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn
    linarith
  have hnum : 0 ≤ (n : ℝ) * (m - sampleMean x) ^ 2 := by
    exact mul_nonneg (by exact_mod_cast (Nat.zero_le n)) (sq_nonneg _)
  have hterm :
      0 ≤ (n : ℝ) * (m - sampleMean x) ^ 2 / ((n : ℝ) - 1) :=
    div_nonneg hnum hden
  linarith

/-- Exact relative error from using a perturbed second-pass mean in the
otherwise exact two-pass quotient.  This is the Problem 1.10 cancellation
substrate in relative-error form: the mean perturbation enters quadratically,
not through the sample-variance condition numbers. -/
theorem sampleVarianceTwoPassWithMean_relError_eq_quadratic {n : ℕ}
    (x : Fin n → ℝ) (m : ℝ) (hn : 1 < n)
    (hVpos : 0 < sampleVarianceTwoPass x) :
    relError (sampleVarianceTwoPassWithMean x m) (sampleVarianceTwoPass x) =
      ((n : ℝ) * (m - sampleMean x) ^ 2) /
        (((n : ℝ) - 1) * sampleVarianceTwoPass x) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (Nat.lt_trans Nat.zero_lt_one hn)
    exact ne_of_gt hnpos
  have hdenpos : 0 < (n : ℝ) - 1 := by
    have hnreal : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn
    linarith
  have hterm_nonneg :
      0 ≤ (n : ℝ) * (m - sampleMean x) ^ 2 / ((n : ℝ) - 1) := by
    have hnum : 0 ≤ (n : ℝ) * (m - sampleMean x) ^ 2 := by
      exact mul_nonneg (by exact_mod_cast (Nat.zero_le n)) (sq_nonneg _)
    exact div_nonneg hnum (le_of_lt hdenpos)
  rw [sampleVarianceTwoPassWithMean_eq_twoPass_add x m hn0]
  unfold relError
  have hdiff :
      sampleVarianceTwoPass x +
            (n : ℝ) * (m - sampleMean x) ^ 2 / ((n : ℝ) - 1) -
          sampleVarianceTwoPass x =
        (n : ℝ) * (m - sampleMean x) ^ 2 / ((n : ℝ) - 1) := by
    ring
  rw [hdiff, abs_of_nonneg hterm_nonneg, abs_of_pos hVpos]
  field_simp [ne_of_gt hdenpos, ne_of_gt hVpos]

/-- Transfer form for the next Problem 1.10 step.  If the rounded second-pass
work after choosing mean `m` is summarized by a relative factor `1 + theta`,
then the relative error against the exact variance is bounded by the rounded
operation error plus the exact quadratic mean-error contribution. -/
theorem sampleVarianceTwoPassWithMean_mul_one_add_relError_le {n : ℕ}
    (x : Fin n → ℝ) (m θ ε : ℝ) (hn : 1 < n)
    (hVpos : 0 < sampleVarianceTwoPass x) (hθ : |θ| ≤ ε) :
    relError (sampleVarianceTwoPassWithMean x m * (1 + θ))
        (sampleVarianceTwoPass x) ≤
      ((n : ℝ) * (m - sampleMean x) ^ 2 / ((n : ℝ) - 1)) /
          sampleVarianceTwoPass x +
        ε * (1 +
          ((n : ℝ) * (m - sampleMean x) ^ 2 / ((n : ℝ) - 1)) /
            sampleVarianceTwoPass x) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (Nat.lt_trans Nat.zero_lt_one hn)
    exact ne_of_gt hnpos
  have hdenpos : 0 < (n : ℝ) - 1 := by
    have hnreal : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn
    linarith
  set V : ℝ := sampleVarianceTwoPass x with hV
  set Q : ℝ := (n : ℝ) * (m - sampleMean x) ^ 2 / ((n : ℝ) - 1) with hQ
  have hVpos' : 0 < V := by
    rw [hV]
    exact hVpos
  have hQ_nonneg : 0 ≤ Q := by
    rw [hQ]
    have hnum : 0 ≤ (n : ℝ) * (m - sampleMean x) ^ 2 := by
      exact mul_nonneg (by exact_mod_cast (Nat.zero_le n)) (sq_nonneg _)
    exact div_nonneg hnum (le_of_lt hdenpos)
  have hVQ_nonneg : 0 ≤ V + Q := by
    linarith
  have hcomp : sampleVarianceTwoPassWithMean x m = V + Q := by
    rw [hV, hQ]
    exact sampleVarianceTwoPassWithMean_eq_twoPass_add x m hn0
  have hcalc :
      relError ((V + Q) * (1 + θ)) V ≤
        Q / V + ε * (1 + Q / V) := by
    unfold relError
    rw [abs_of_pos hVpos']
    have hdiff : (V + Q) * (1 + θ) - V = Q + θ * (V + Q) := by
      ring
    rw [hdiff]
    have habs :
        |Q + θ * (V + Q)| ≤ Q + ε * (V + Q) := by
      calc
        |Q + θ * (V + Q)| ≤ |Q| + |θ * (V + Q)| :=
          abs_add_le Q (θ * (V + Q))
        _ = Q + |θ| * (V + Q) := by
              rw [abs_of_nonneg hQ_nonneg, abs_mul, abs_of_nonneg hVQ_nonneg]
        _ ≤ Q + ε * (V + Q) := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_left
                  (mul_le_mul_of_nonneg_right hθ hVQ_nonneg) Q
    calc
      |Q + θ * (V + Q)| / V ≤ (Q + ε * (V + Q)) / V := by
        exact div_le_div_of_nonneg_right habs (le_of_lt hVpos')
      _ = Q / V + ε * (1 + Q / V) := by
        field_simp [ne_of_gt hVpos']
  simpa [hcomp, hV, hQ] using hcalc

/-- Nonnegative weighted sums of componentwise relative perturbations have one
aggregate relative perturbation with the same radius.  This is the reusable
weighted-average step needed to turn squared-deviation summation errors into a
single relative factor in the Problem 1.10 two-pass analysis. -/
theorem exists_weightedRelativeErrorFactor_of_nonneg_sum {n : ℕ}
    (a θ : Fin n → ℝ) (B : ℝ) (ha : ∀ i, 0 ≤ a i)
    (hSpos : 0 < ∑ i : Fin n, a i) (hθ : ∀ i, |θ i| ≤ B) :
    ∃ Θ : ℝ, |Θ| ≤ B ∧
      (∑ i : Fin n, a i * (1 + θ i)) =
        (∑ i : Fin n, a i) * (1 + Θ) := by
  set S : ℝ := ∑ i : Fin n, a i with hS
  have hSpos' : 0 < S := by
    rw [hS]
    exact hSpos
  refine ⟨(∑ i : Fin n, a i * θ i) / S, ?_, ?_⟩
  · have habs_sum : |∑ i : Fin n, a i * θ i| ≤ B * S := by
      calc
        |∑ i : Fin n, a i * θ i|
            ≤ ∑ i : Fin n, |a i * θ i| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ i : Fin n, a i * |θ i| := by
              apply Finset.sum_congr rfl
              intro i _
              rw [abs_mul, abs_of_nonneg (ha i)]
        _ ≤ ∑ i : Fin n, a i * B := by
              exact Finset.sum_le_sum fun i _ =>
                mul_le_mul_of_nonneg_left (hθ i) (ha i)
        _ = B * S := by
              rw [← Finset.sum_mul, hS]
              ring
    rw [abs_div, abs_of_pos hSpos']
    calc
      |∑ i : Fin n, a i * θ i| / S ≤ (B * S) / S := by
        exact div_le_div_of_nonneg_right habs_sum (le_of_lt hSpos')
      _ = B := by
        field_simp [ne_of_gt hSpos']
  · have hsum_expand :
        (∑ i : Fin n, a i * (1 + θ i)) =
          S + ∑ i : Fin n, a i * θ i := by
      rw [hS]
      calc
        (∑ i : Fin n, a i * (1 + θ i))
            = ∑ i : Fin n, (a i + a i * θ i) := by
                apply Finset.sum_congr rfl
                intro i _
                ring
        _ = (∑ i : Fin n, a i) + ∑ i : Fin n, a i * θ i := by
                rw [Finset.sum_add_distrib]
    rw [hsum_expand]
    field_simp [ne_of_gt hSpos']

/-- First pass of the two-pass variance algorithm: recursive summation followed
by rounded division computes the exact mean of componentwise perturbed inputs,
with every perturbation bounded by `γ_n`. -/
theorem flSampleMean_backward_error {n : ℕ} (fp : FPModel)
    (x : Fin n → ℝ) (hn : 0 < n) (hγ : gammaValid fp n) :
    ∃ η : Fin n → ℝ, (∀ i, |η i| ≤ gamma fp n) ∧
      flSampleMean fp x = (∑ i : Fin n, x i * (1 + η i)) / (n : ℝ) := by
  have hsumValid : gammaValid fp (n - 1) :=
    gammaValid_mono fp (Nat.sub_le n 1) hγ
  obtain ⟨σ, hσ, hfold⟩ := fl_sum_error_tight fp n hn x hsumValid
  have hden : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  obtain ⟨δd, hδd, hdiv⟩ :=
    fp.model_div (Fin.foldl n (fun acc i => fp.fl_add acc (x i)) 0) (n : ℝ) hden
  have h1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hγ
  have hδdγ : |δd| ≤ gamma fp 1 :=
    le_trans hδd (u_le_gamma fp one_pos h1)
  have hNat : n - 1 + 1 = n := by omega
  have hfinalValid : gammaValid fp ((n - 1) + 1) := by
    simpa [hNat] using hγ
  let η : Fin n → ℝ :=
    fun i => Classical.choose
      (gamma_mul fp (n - 1) 1 (σ i) δd (hσ i) hδdγ hfinalValid)
  have hηspec : ∀ i,
      |η i| ≤ gamma fp n ∧ (1 + σ i) * (1 + δd) = 1 + η i := by
    intro i
    have hspec := Classical.choose_spec
      (gamma_mul fp (n - 1) 1 (σ i) δd (hσ i) hδdγ hfinalValid)
    constructor
    · simpa [η, hNat] using hspec.1
    · simpa [η] using hspec.2
  refine ⟨η, fun i => (hηspec i).1, ?_⟩
  have hsumη :
      (∑ i : Fin n, x i * (1 + σ i)) * (1 + δd) =
        ∑ i : Fin n, x i * (1 + η i) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    calc
      (x i * (1 + σ i)) * (1 + δd)
          = x i * ((1 + σ i) * (1 + δd)) := by ring
      _ = x i * (1 + η i) := by rw [(hηspec i).2]
  calc
    flSampleMean fp x
        = fp.fl_div (Fin.foldl n (fun acc i => fp.fl_add acc (x i)) 0)
            (n : ℝ) := by
          rfl
    _ = ((∑ i : Fin n, x i * (1 + σ i)) / (n : ℝ)) * (1 + δd) := by
          rw [hdiv, hfold]
    _ = ((∑ i : Fin n, x i * (1 + σ i)) * (1 + δd)) / (n : ℝ) := by
          field_simp [hden]
    _ = (∑ i : Fin n, x i * (1 + η i)) / (n : ℝ) := by
          rw [hsumη]

/-- Forward absolute-error corollary for the computed first-pass mean.  The
error is bounded by `γ_n` times the average absolute input size. -/
theorem flSampleMean_abs_error_le_gamma {n : ℕ} (fp : FPModel)
    (x : Fin n → ℝ) (hn : 0 < n) (hγ : gammaValid fp n) :
    |flSampleMean fp x - sampleMean x| ≤
      gamma fp n * ((∑ i : Fin n, |x i|) / (n : ℝ)) := by
  obtain ⟨η, hη, hfl⟩ := flSampleMean_backward_error fp x hn hγ
  have hden_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hden_ne : (n : ℝ) ≠ 0 := ne_of_gt hden_pos
  have hγ_nonneg : 0 ≤ gamma fp n := gamma_nonneg fp hγ
  have hnum :
      (∑ i : Fin n, x i * (1 + η i)) - (∑ i : Fin n, x i) =
        ∑ i : Fin n, x i * η i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hdiff :
      flSampleMean fp x - sampleMean x =
        (∑ i : Fin n, x i * η i) / (n : ℝ) := by
    rw [hfl, sampleMean]
    calc
      (∑ i : Fin n, x i * (1 + η i)) / (n : ℝ) -
          (∑ i : Fin n, x i) / (n : ℝ)
          = ((∑ i : Fin n, x i * (1 + η i)) -
              (∑ i : Fin n, x i)) / (n : ℝ) := by
            field_simp [hden_ne]
      _ = (∑ i : Fin n, x i * η i) / (n : ℝ) := by
            rw [hnum]
  rw [hdiff, abs_div, abs_of_pos hden_pos]
  calc
    |∑ i : Fin n, x i * η i| / (n : ℝ)
        ≤ (∑ i : Fin n, |x i * η i|) / (n : ℝ) := by
          exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _)
            (le_of_lt hden_pos)
    _ = (∑ i : Fin n, |x i| * |η i|) / (n : ℝ) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [abs_mul]
    _ ≤ (∑ i : Fin n, |x i| * gamma fp n) / (n : ℝ) := by
          exact div_le_div_of_nonneg_right
            (Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left (hη i) (abs_nonneg _))
            (le_of_lt hden_pos)
    _ = gamma fp n * ((∑ i : Fin n, |x i|) / (n : ℝ)) := by
          rw [← Finset.sum_mul]
          field_simp [hden_ne]

/-- A rounded deviation followed by a rounded square is the exact squared
deviation multiplied by one relative factor bounded by `γ_3`. -/
theorem flSquaredDeviationWithMean_eq_mul_one_add_gamma3 (fp : FPModel)
    (x m : ℝ) (h3 : gammaValid fp 3) :
    ∃ η : ℝ, |η| ≤ gamma fp 3 ∧
      fp.fl_mul (fp.fl_sub x m) (fp.fl_sub x m) =
        (x - m) ^ 2 * (1 + η) := by
  have h1 : gammaValid fp 1 := gammaValid_mono fp (by omega) h3
  have h2 : gammaValid fp 2 := gammaValid_mono fp (by omega) h3
  obtain ⟨δs, hδs, hsub⟩ := fp.model_sub x m
  obtain ⟨δm, hδm, hmul⟩ :=
    fp.model_mul (fp.fl_sub x m) (fp.fl_sub x m)
  have hδsγ : |δs| ≤ gamma fp 1 :=
    le_trans hδs (u_le_gamma fp one_pos h1)
  have hδmγ : |δm| ≤ gamma fp 1 :=
    le_trans hδm (u_le_gamma fp one_pos h1)
  obtain ⟨θ2, hθ2, hθ2eq⟩ :=
    gamma_mul fp 1 1 δs δs hδsγ hδsγ h2
  obtain ⟨η, hη, hηeq⟩ :=
    gamma_mul fp 2 1 θ2 δm hθ2 hδmγ h3
  refine ⟨η, hη, ?_⟩
  rw [hmul, hsub]
  calc
    ((x - m) * (1 + δs) * ((x - m) * (1 + δs))) * (1 + δm)
        = (x - m) ^ 2 * ((1 + δs) * (1 + δs)) * (1 + δm) := by
          ring
    _ = (x - m) ^ 2 * (1 + θ2) * (1 + δm) := by
          rw [hθ2eq]
    _ = (x - m) ^ 2 * ((1 + θ2) * (1 + δm)) := by
          ring
    _ = (x - m) ^ 2 * (1 + η) := by
          rw [hηeq]

/-- Operation-by-operation rounded second-pass theorem for Problem 1.10.

Once the mean supplied to the second pass is fixed, the rounded subtraction,
squaring, recursive summation, and final division compute the exact
two-pass-with-that-mean variance multiplied by one relative factor bounded by
`γ_(n+3)`, assuming the corrected squared-deviation sum is positive. -/
theorem flSampleVarianceTwoPassWithMean_eq_mul_one_add_gamma {n : ℕ}
    (fp : FPModel) (x : Fin n → ℝ) (m : ℝ)
    (hn : 1 < n) (hsumpos : 0 < ∑ i : Fin n, (x i - m) ^ 2)
    (hγ : gammaValid fp (n + 3)) :
    ∃ θ : ℝ, |θ| ≤ gamma fp (n + 3) ∧
      flSampleVarianceTwoPassWithMean fp x m =
        sampleVarianceTwoPassWithMean x m * (1 + θ) := by
  let denom : ℝ := (n : ℝ) - 1
  let a : Fin n → ℝ := fun i => (x i - m) ^ 2
  let p : Fin n → ℝ :=
    fun i =>
      fp.fl_mul (fp.fl_sub (x i) m) (fp.fl_sub (x i) m)
  have hnpos : 0 < n := by omega
  have hden : denom ≠ 0 := by
    have hnR : (1 : ℝ) < n := by exact_mod_cast hn
    unfold denom
    linarith
  have h1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hγ
  have h3 : gammaValid fp 3 := gammaValid_mono fp (by omega) hγ
  have hsumValid : gammaValid fp (n - 1) :=
    gammaValid_mono fp (by omega) hγ
  have hcompValid : gammaValid fp (3 + (n - 1)) :=
    gammaValid_mono fp (by omega) hγ
  have hNat : 3 + (n - 1) + 1 = n + 3 := by omega
  have hfinalValid : gammaValid fp (3 + (n - 1) + 1) := by
    simpa [hNat] using hγ
  let η : Fin n → ℝ :=
    fun i => Classical.choose
      (flSquaredDeviationWithMean_eq_mul_one_add_gamma3 fp (x i) m h3)
  have hηspec : ∀ i, |η i| ≤ gamma fp 3 ∧ p i = a i * (1 + η i) := by
    intro i
    exact Classical.choose_spec
      (flSquaredDeviationWithMean_eq_mul_one_add_gamma3 fp (x i) m h3)
  obtain ⟨σ, hσ, hfold⟩ := fl_sum_error_tight fp n hnpos p hsumValid
  let τ : Fin n → ℝ :=
    fun i => Classical.choose
      (gamma_mul fp 3 (n - 1) (η i) (σ i) (hηspec i).1 (hσ i) hcompValid)
  have hτspec : ∀ i,
      |τ i| ≤ gamma fp (3 + (n - 1)) ∧
        (1 + η i) * (1 + σ i) = 1 + τ i := by
    intro i
    exact Classical.choose_spec
      (gamma_mul fp 3 (n - 1) (η i) (σ i) (hηspec i).1 (hσ i) hcompValid)
  have hfoldτ :
      Fin.foldl n (fun acc i => fp.fl_add acc (p i)) 0 =
        ∑ i : Fin n, a i * (1 + τ i) := by
    calc
      Fin.foldl n (fun acc i => fp.fl_add acc (p i)) 0
          = ∑ i : Fin n, p i * (1 + σ i) := hfold
      _ = ∑ i : Fin n, (a i * (1 + η i)) * (1 + σ i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [(hηspec i).2]
      _ = ∑ i : Fin n, a i * (1 + τ i) := by
            apply Finset.sum_congr rfl
            intro i _
            calc
              (a i * (1 + η i)) * (1 + σ i)
                  = a i * ((1 + η i) * (1 + σ i)) := by ring
              _ = a i * (1 + τ i) := by rw [(hτspec i).2]
  have ha : ∀ i, 0 ≤ a i := by
    intro i
    exact sq_nonneg _
  have hsumpos_a : 0 < ∑ i : Fin n, a i := by
    simpa [a] using hsumpos
  obtain ⟨Θ, hΘ, hweighted⟩ :=
    exists_weightedRelativeErrorFactor_of_nonneg_sum a τ
      (gamma fp (3 + (n - 1))) ha hsumpos_a (fun i => (hτspec i).1)
  have hfoldΘ :
      Fin.foldl n (fun acc i => fp.fl_add acc (p i)) 0 =
        (∑ i : Fin n, a i) * (1 + Θ) := by
    rw [hfoldτ, hweighted]
  obtain ⟨δd, hδd, hdiv⟩ :=
    fp.model_div (Fin.foldl n (fun acc i => fp.fl_add acc (p i)) 0) denom hden
  have hδdγ : |δd| ≤ gamma fp 1 :=
    le_trans hδd (u_le_gamma fp one_pos h1)
  obtain ⟨θ, hθ, hθeq⟩ :=
    gamma_mul fp (3 + (n - 1)) 1 Θ δd hΘ hδdγ hfinalValid
  refine ⟨θ, ?_, ?_⟩
  · simpa [hNat] using hθ
  · calc
      flSampleVarianceTwoPassWithMean fp x m
          = fp.fl_div
              (Fin.foldl n (fun acc i => fp.fl_add acc (p i)) 0) denom := by
            simp [flSampleVarianceTwoPassWithMean, p, denom]
      _ = ((∑ i : Fin n, a i) * (1 + Θ) / denom) * (1 + δd) := by
            rw [hdiv, hfoldΘ]
      _ = ((∑ i : Fin n, a i) / denom) * ((1 + Θ) * (1 + δd)) := by
            field_simp [hden]
      _ = ((∑ i : Fin n, a i) / denom) * (1 + θ) := by
            rw [hθeq]
      _ = sampleVarianceTwoPassWithMean x m * (1 + θ) := by
            simp [sampleVarianceTwoPassWithMean, a, denom]

/-- Composed two-pass relative-error bound for the algorithm using the computed
first-pass mean.  The remaining non-first-order term is exactly the quadratic
mean-error contribution. -/
theorem flSampleVarianceTwoPass_relError_le_gamma_add_mean_quadratic {n : ℕ}
    (fp : FPModel) (x : Fin n → ℝ)
    (hn : 1 < n) (hVpos : 0 < sampleVarianceTwoPass x)
    (hsumpos : 0 < ∑ i : Fin n, (x i - flSampleMean fp x) ^ 2)
    (hγ : gammaValid fp (n + 3)) :
    relError (flSampleVarianceTwoPass fp x) (sampleVarianceTwoPass x) ≤
      (((n : ℝ) * (flSampleMean fp x - sampleMean x) ^ 2 /
          ((n : ℝ) - 1)) / sampleVarianceTwoPass x) +
        gamma fp (n + 3) *
          (1 + (((n : ℝ) * (flSampleMean fp x - sampleMean x) ^ 2 /
            ((n : ℝ) - 1)) / sampleVarianceTwoPass x)) := by
  obtain ⟨θ, hθ, hfl⟩ :=
    flSampleVarianceTwoPassWithMean_eq_mul_one_add_gamma
      fp x (flSampleMean fp x) hn hsumpos hγ
  have hbound :=
    sampleVarianceTwoPassWithMean_mul_one_add_relError_le
      x (flSampleMean fp x) θ (gamma fp (n + 3)) hn hVpos hθ
  rw [← hfl] at hbound
  simpa [flSampleVarianceTwoPass] using hbound

/-- The explicit quadratic first-pass mean-error term in the composed
Problem 1.10 bound is itself bounded by the square of the first-pass `γ_n`
mean-error radius. -/
theorem flSampleVarianceTwoPass_mean_quadratic_le_gamma_sq {n : ℕ}
    (fp : FPModel) (x : Fin n → ℝ)
    (hn : 1 < n) (hVpos : 0 < sampleVarianceTwoPass x)
    (hγ : gammaValid fp n) :
    (((n : ℝ) * (flSampleMean fp x - sampleMean x) ^ 2 /
        ((n : ℝ) - 1)) / sampleVarianceTwoPass x) ≤
      (((n : ℝ) *
          (gamma fp n * ((∑ i : Fin n, |x i|) / (n : ℝ))) ^ 2 /
        ((n : ℝ) - 1)) / sampleVarianceTwoPass x) := by
  have hnpos : 0 < n := by omega
  have hnRpos : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hnRgt1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdenpos : 0 < (n : ℝ) - 1 := by linarith
  have hV_nonneg : 0 ≤ sampleVarianceTwoPass x := le_of_lt hVpos
  have hmean := flSampleMean_abs_error_le_gamma fp x hnpos hγ
  set B : ℝ := gamma fp n * ((∑ i : Fin n, |x i|) / (n : ℝ)) with hB
  have hB_nonneg : 0 ≤ B := by
    rw [hB]
    have hsum_nonneg : 0 ≤ ∑ i : Fin n, |x i| :=
      Finset.sum_nonneg fun i _ => abs_nonneg (x i)
    have havg_nonneg : 0 ≤ (∑ i : Fin n, |x i|) / (n : ℝ) :=
      div_nonneg hsum_nonneg (le_of_lt hnRpos)
    exact mul_nonneg (gamma_nonneg fp hγ) havg_nonneg
  have hsquare :
      (flSampleMean fp x - sampleMean x) ^ 2 ≤ B ^ 2 := by
    have hB_abs : |B| = B := abs_of_nonneg hB_nonneg
    have habs : |flSampleMean fp x - sampleMean x| ≤ |B| := by
      rw [hB_abs]
      simpa [hB] using hmean
    exact (sq_le_sq).mpr habs
  have hnum_le :
      (n : ℝ) * (flSampleMean fp x - sampleMean x) ^ 2 ≤
        (n : ℝ) * B ^ 2 :=
    mul_le_mul_of_nonneg_left hsquare (le_of_lt hnRpos)
  have hdiv_le :
      ((n : ℝ) * (flSampleMean fp x - sampleMean x) ^ 2 /
          ((n : ℝ) - 1)) ≤
        ((n : ℝ) * B ^ 2 / ((n : ℝ) - 1)) :=
    div_le_div_of_nonneg_right hnum_le (le_of_lt hdenpos)
  have hfinal :
      (((n : ℝ) * (flSampleMean fp x - sampleMean x) ^ 2 /
          ((n : ℝ) - 1)) / sampleVarianceTwoPass x) ≤
        (((n : ℝ) * B ^ 2 / ((n : ℝ) - 1)) /
          sampleVarianceTwoPass x) :=
    div_le_div_of_nonneg_right hdiv_le hV_nonneg
  simpa [hB] using hfinal

/-- Composed Problem 1.10 bound with the first-pass mean contribution written
as an explicit squared-`γ_n` term. -/
theorem flSampleVarianceTwoPass_relError_le_gamma_add_gamma_sq_mean_bound {n : ℕ}
    (fp : FPModel) (x : Fin n → ℝ)
    (hn : 1 < n) (hVpos : 0 < sampleVarianceTwoPass x)
    (hsumpos : 0 < ∑ i : Fin n, (x i - flSampleMean fp x) ^ 2)
    (hγ : gammaValid fp (n + 3)) :
    relError (flSampleVarianceTwoPass fp x) (sampleVarianceTwoPass x) ≤
      (((n : ℝ) *
          (gamma fp n * ((∑ i : Fin n, |x i|) / (n : ℝ))) ^ 2 /
        ((n : ℝ) - 1)) / sampleVarianceTwoPass x) +
        gamma fp (n + 3) *
          (1 + (((n : ℝ) *
            (gamma fp n * ((∑ i : Fin n, |x i|) / (n : ℝ))) ^ 2 /
          ((n : ℝ) - 1)) / sampleVarianceTwoPass x)) := by
  have hγn : gammaValid fp n := gammaValid_mono fp (by omega) hγ
  have hbase :=
    flSampleVarianceTwoPass_relError_le_gamma_add_mean_quadratic
      fp x hn hVpos hsumpos hγ
  have hquad :=
    flSampleVarianceTwoPass_mean_quadratic_le_gamma_sq
      fp x hn hVpos hγn
  set Q : ℝ :=
    (((n : ℝ) * (flSampleMean fp x - sampleMean x) ^ 2 /
      ((n : ℝ) - 1)) / sampleVarianceTwoPass x) with hQ
  set B : ℝ :=
    (((n : ℝ) *
      (gamma fp n * ((∑ i : Fin n, |x i|) / (n : ℝ))) ^ 2 /
      ((n : ℝ) - 1)) / sampleVarianceTwoPass x) with hB
  set G : ℝ := gamma fp (n + 3) with hG
  have hQleB : Q ≤ B := by
    simpa [hQ, hB] using hquad
  have hG_nonneg : 0 ≤ G := by
    rw [hG]
    exact gamma_nonneg fp hγ
  have hbase' :
      relError (flSampleVarianceTwoPass fp x) (sampleVarianceTwoPass x) ≤
        Q + G * (1 + Q) := by
    simpa [hQ, hG] using hbase
  have hmono : Q + G * (1 + Q) ≤ B + G * (1 + B) := by
    have hmul : G * Q ≤ G * B :=
      mul_le_mul_of_nonneg_left hQleB hG_nonneg
    nlinarith
  exact le_trans hbase' (by simpa [hB, hG] using hmono)

/-- The explicit bounded first-pass mean contribution in Higham Problem 1.10's
two-pass variance analysis. -/
noncomputable def flSampleVarianceTwoPassProblem110MeanQuadraticBound
    (fp : FPModel) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (((n : ℝ) *
      (gamma fp n * ((∑ i : Fin n, |x i|) / (n : ℝ))) ^ 2 /
    ((n : ℝ) - 1)) / sampleVarianceTwoPass x)

/-- The explicit higher-order remainder accompanying the source linear term
`(n+3)u` in the Problem 1.10 two-pass variance bound. -/
noncomputable def flSampleVarianceTwoPassProblem110Remainder
    (fp : FPModel) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (((((n + 3 : ℕ) : ℝ) * fp.u) ^ 2) /
      (1 - ((n + 3 : ℕ) : ℝ) * fp.u) +
    flSampleVarianceTwoPassProblem110MeanQuadraticBound fp x +
    gamma fp (n + 3) *
      flSampleVarianceTwoPassProblem110MeanQuadraticBound fp x)

/-- The explicit bounded first-pass mean contribution is nonnegative under the
ordinary positive-variance side conditions. -/
theorem flSampleVarianceTwoPassProblem110MeanQuadraticBound_nonneg {n : ℕ}
    (fp : FPModel) (x : Fin n → ℝ)
    (hn : 1 < n) (hVpos : 0 < sampleVarianceTwoPass x) :
    0 ≤ flSampleVarianceTwoPassProblem110MeanQuadraticBound fp x := by
  have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hn_gt_one : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hden_nonneg : 0 ≤ (n : ℝ) - 1 := by linarith
  have hnum_nonneg :
      0 ≤ (n : ℝ) *
        (gamma fp n * ((∑ i : Fin n, |x i|) / (n : ℝ))) ^ 2 :=
    mul_nonneg hn_nonneg (sq_nonneg _)
  have hquot_nonneg :
      0 ≤ ((n : ℝ) *
        (gamma fp n * ((∑ i : Fin n, |x i|) / (n : ℝ))) ^ 2 /
        ((n : ℝ) - 1)) :=
    div_nonneg hnum_nonneg hden_nonneg
  exact div_nonneg hquot_nonneg (le_of_lt hVpos)

/-- The named Problem 1.10 higher-order remainder is nonnegative whenever the
`γ_{n+3}` guard and positive-variance side conditions hold. -/
theorem flSampleVarianceTwoPassProblem110Remainder_nonneg {n : ℕ}
    (fp : FPModel) (x : Fin n → ℝ)
    (hn : 1 < n) (hVpos : 0 < sampleVarianceTwoPass x)
    (hγ : gammaValid fp (n + 3)) :
    0 ≤ flSampleVarianceTwoPassProblem110Remainder fp x := by
  have hB :=
    flSampleVarianceTwoPassProblem110MeanQuadraticBound_nonneg
      fp x hn hVpos
  have hG : 0 ≤ gamma fp (n + 3) := gamma_nonneg fp hγ
  have hR : 0 ≤
      ((((n + 3 : ℕ) : ℝ) * fp.u) ^ 2) /
        (1 - ((n + 3 : ℕ) : ℝ) * fp.u) := by
    have hden : 0 ≤ 1 - ((n + 3 : ℕ) : ℝ) * fp.u := by
      unfold gammaValid at hγ
      linarith
    exact div_nonneg (sq_nonneg _) hden
  have hGB : 0 ≤ gamma fp (n + 3) *
      flSampleVarianceTwoPassProblem110MeanQuadraticBound fp x :=
    mul_nonneg hG hB
  unfold flSampleVarianceTwoPassProblem110Remainder
  nlinarith

/-- Non-vacuity check for the named first-pass mean contribution: at zero unit
roundoff the explicit `γ_n`-squared contribution vanishes. -/
theorem flSampleVarianceTwoPassProblem110MeanQuadraticBound_eq_zero_of_u_eq_zero
    {n : ℕ} (fp : FPModel) (x : Fin n → ℝ) (hu : fp.u = 0) :
    flSampleVarianceTwoPassProblem110MeanQuadraticBound fp x = 0 := by
  simp [flSampleVarianceTwoPassProblem110MeanQuadraticBound, gamma, hu]

/-- Non-vacuity check for the named Problem 1.10 remainder: at zero unit
roundoff the whole higher-order remainder vanishes. -/
theorem flSampleVarianceTwoPassProblem110Remainder_eq_zero_of_u_eq_zero
    {n : ℕ} (fp : FPModel) (x : Fin n → ℝ) (hu : fp.u = 0) :
    flSampleVarianceTwoPassProblem110Remainder fp x = 0 := by
  simp [flSampleVarianceTwoPassProblem110Remainder,
    flSampleVarianceTwoPassProblem110MeanQuadraticBound, gamma, hu]

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

/-- Explicit quadratic-in-`u` envelope for the named Problem 1.10 remainder.
Under the public half-unit cap `(n+3)u <= 1/2`, the theorem below proves that
the full higher-order remainder is bounded by this expression. -/
noncomputable def flSampleVarianceTwoPassProblem110RemainderQuadraticBound
    (fp : FPModel) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  2 * (
    ((((n + 3 : ℕ) : ℝ) * fp.u) ^ 2) +
    (((n : ℝ) *
      (2 * ((n : ℝ) * fp.u) * ((∑ i : Fin n, |x i|) / (n : ℝ))) ^ 2 /
      ((n : ℝ) - 1)) / sampleVarianceTwoPass x))

/-- The data-dependent coefficient in the explicit quadratic envelope for the
Problem 1.10 higher-order remainder.  It is independent of the unit roundoff;
the next theorem rewrites the envelope as this coefficient times `u^2`. -/
noncomputable def flSampleVarianceTwoPassProblem110RemainderQuadraticCoeff
    {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  2 * ((((n + 3 : ℕ) : ℝ) ^ 2) +
    ((((n : ℝ) *
      (2 * (n : ℝ) * ((∑ i : Fin n, |x i|) / (n : ℝ))) ^ 2) /
      ((n : ℝ) - 1)) / sampleVarianceTwoPass x))

/-- The explicit Problem 1.10 quadratic envelope is literally a fixed
data-dependent coefficient times `fp.u^2`.  This supplies the theorem-level
coefficient form used by the asymptotic wrapper below. -/
theorem flSampleVarianceTwoPassProblem110RemainderQuadraticBound_eq_coeff_mul_u_sq
    (fp : FPModel) {n : ℕ} (x : Fin n → ℝ) :
    flSampleVarianceTwoPassProblem110RemainderQuadraticBound fp x =
      flSampleVarianceTwoPassProblem110RemainderQuadraticCoeff x * fp.u ^ 2 := by
  unfold flSampleVarianceTwoPassProblem110RemainderQuadraticBound
  unfold flSampleVarianceTwoPassProblem110RemainderQuadraticCoeff
  ring

/-- Scalar-variable quadratic envelope for Problem 1.10.  Evaluating this at
`fp.u` recovers the explicit FP-model envelope above, while keeping the
asymptotic statement independent of any particular machine model. -/
noncomputable def flSampleVarianceTwoPassProblem110RemainderQuadraticEnvelope
    {n : ℕ} (x : Fin n → ℝ) (u : ℝ) : ℝ :=
  flSampleVarianceTwoPassProblem110RemainderQuadraticCoeff x * u ^ 2

/-- The scalar-variable quadratic envelope recovers the FP-model envelope when
the scalar variable is instantiated with the model's unit roundoff. -/
theorem flSampleVarianceTwoPassProblem110RemainderQuadraticEnvelope_eq_bound
    (fp : FPModel) {n : ℕ} (x : Fin n → ℝ) :
    flSampleVarianceTwoPassProblem110RemainderQuadraticEnvelope x fp.u =
      flSampleVarianceTwoPassProblem110RemainderQuadraticBound fp x := by
  rw [flSampleVarianceTwoPassProblem110RemainderQuadraticBound_eq_coeff_mul_u_sq]
  rfl

/-- Literal Landau form of the Problem 1.10 quadratic certificate: for fixed
data, the explicit higher-order envelope is `O(u^2)` as `u -> 0`. -/
theorem flSampleVarianceTwoPassProblem110RemainderQuadraticEnvelope_isBigO
    {n : ℕ} (x : Fin n → ℝ) :
    (fun u : ℝ =>
      flSampleVarianceTwoPassProblem110RemainderQuadraticEnvelope x u)
      =O[𝓝 0] (fun u : ℝ => u ^ 2) := by
  simpa [flSampleVarianceTwoPassProblem110RemainderQuadraticEnvelope] using
    (Asymptotics.isBigO_const_mul_self
      (flSampleVarianceTwoPassProblem110RemainderQuadraticCoeff x)
      (fun u : ℝ => u ^ 2) (𝓝 0))

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

/-- Source-style Problem 1.10 form: the rounded two-pass relative error is
bounded by the displayed linear term `(n+3)u` plus an explicit higher-order
remainder.  The remainder consists of the rational quadratic part of
`gamma fp (n+3)`, the squared-`gamma fp n` first-pass mean contribution, and
their product. -/
theorem flSampleVarianceTwoPass_relError_le_linear_u_add_explicit_remainder {n : ℕ}
    (fp : FPModel) (x : Fin n → ℝ)
    (hn : 1 < n) (hVpos : 0 < sampleVarianceTwoPass x)
    (hsumpos : 0 < ∑ i : Fin n, (x i - flSampleMean fp x) ^ 2)
    (hγ : gammaValid fp (n + 3)) :
    relError (flSampleVarianceTwoPass fp x) (sampleVarianceTwoPass x) ≤
      ((n + 3 : ℕ) : ℝ) * fp.u +
        (((((n + 3 : ℕ) : ℝ) * fp.u) ^ 2) /
          (1 - ((n + 3 : ℕ) : ℝ) * fp.u) +
        (((n : ℝ) *
            (gamma fp n * ((∑ i : Fin n, |x i|) / (n : ℝ))) ^ 2 /
          ((n : ℝ) - 1)) / sampleVarianceTwoPass x) +
        gamma fp (n + 3) *
          (((n : ℝ) *
            (gamma fp n * ((∑ i : Fin n, |x i|) / (n : ℝ))) ^ 2 /
          ((n : ℝ) - 1)) / sampleVarianceTwoPass x)) := by
  have hbase :=
    flSampleVarianceTwoPass_relError_le_gamma_add_gamma_sq_mean_bound
      fp x hn hVpos hsumpos hγ
  set B : ℝ :=
    (((n : ℝ) *
      (gamma fp n * ((∑ i : Fin n, |x i|) / (n : ℝ))) ^ 2 /
      ((n : ℝ) - 1)) / sampleVarianceTwoPass x) with hB
  set G : ℝ := gamma fp (n + 3) with hG
  set L : ℝ := ((n + 3 : ℕ) : ℝ) * fp.u with hL
  set R : ℝ :=
    ((((n + 3 : ℕ) : ℝ) * fp.u) ^ 2) /
      (1 - ((n + 3 : ℕ) : ℝ) * fp.u) with hR
  have hgamma : G = L + R := by
    rw [hG, hL, hR]
    exact gamma_eq_linear_plus_quadratic_remainder fp (n + 3) hγ
  have hbase' :
      relError (flSampleVarianceTwoPass fp x) (sampleVarianceTwoPass x) ≤
        B + G * (1 + B) := by
    simpa [hB, hG] using hbase
  have hrewrite : B + G * (1 + B) = L + (R + B + G * B) := by
    rw [hgamma]
    ring
  rw [hrewrite] at hbase'
  simpa [hB, hG, hL, hR] using hbase'

/-- Source-style Problem 1.10 form using the named explicit higher-order
remainder. -/
theorem flSampleVarianceTwoPass_relError_le_linear_u_add_problem110_remainder {n : ℕ}
    (fp : FPModel) (x : Fin n → ℝ)
    (hn : 1 < n) (hVpos : 0 < sampleVarianceTwoPass x)
    (hsumpos : 0 < ∑ i : Fin n, (x i - flSampleMean fp x) ^ 2)
    (hγ : gammaValid fp (n + 3)) :
    relError (flSampleVarianceTwoPass fp x) (sampleVarianceTwoPass x) ≤
      ((n + 3 : ℕ) : ℝ) * fp.u +
        flSampleVarianceTwoPassProblem110Remainder fp x := by
  simpa [flSampleVarianceTwoPassProblem110Remainder,
    flSampleVarianceTwoPassProblem110MeanQuadraticBound] using
    flSampleVarianceTwoPass_relError_le_linear_u_add_explicit_remainder
      fp x hn hVpos hsumpos hγ

/-- Non-vacuity check for the source-style Problem 1.10 theorem: when unit
roundoff is zero, the modeled two-pass relative-error bound collapses to zero. -/
theorem flSampleVarianceTwoPass_relError_eq_zero_of_u_eq_zero {n : ℕ}
    (fp : FPModel) (x : Fin n → ℝ)
    (hn : 1 < n) (hVpos : 0 < sampleVarianceTwoPass x)
    (hsumpos : 0 < ∑ i : Fin n, (x i - flSampleMean fp x) ^ 2)
    (hu : fp.u = 0) :
    relError (flSampleVarianceTwoPass fp x) (sampleVarianceTwoPass x) = 0 := by
  have hγ : gammaValid fp (n + 3) := by
    unfold gammaValid
    simp [hu]
  have hle :=
    flSampleVarianceTwoPass_relError_le_linear_u_add_problem110_remainder
      fp x hn hVpos hsumpos hγ
  have hrem :=
    flSampleVarianceTwoPassProblem110Remainder_eq_zero_of_u_eq_zero
      fp x hu
  rw [hu, hrem] at hle
  norm_num at hle
  exact le_antisymm hle (relError_nonneg _ _)

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

/-- The prefix means generated by the exact update formulae for Higham §1.9's
data `[10000, 10001, 10002]`. -/
theorem prefixMean_example_values_10000_10001_10002 :
    prefixMean (fun j : ℕ => (10000 : ℝ) + (j : ℝ)) 1 = 10000 ∧
      prefixMean (fun j : ℕ => (10000 : ℝ) + (j : ℝ)) 2 = 20001 / 2 ∧
      prefixMean (fun j : ℕ => (10000 : ℝ) + (j : ℝ)) 3 = 10001 := by
  constructor
  · norm_num [prefixMean]
  constructor
  · norm_num [prefixMean, Finset.sum_range_succ]
  · norm_num [prefixMean, Finset.sum_range_succ]
    ring_nf
    rfl

/-- The corrected sums of squares generated by the exact update formulae for
Higham §1.9's data `[10000, 10001, 10002]`: after three samples, `Q_3 = 2`. -/
theorem prefixCorrectedSumSquares_example_values_10000_10001_10002 :
    prefixCorrectedSumSquares (fun j : ℕ => (10000 : ℝ) + (j : ℝ)) 1 = 0 ∧
      prefixCorrectedSumSquares (fun j : ℕ => (10000 : ℝ) + (j : ℝ)) 2 = 1 / 2 ∧
      prefixCorrectedSumSquares (fun j : ℕ => (10000 : ℝ) + (j : ℝ)) 3 = 2 := by
  constructor
  · norm_num [prefixCorrectedSumSquares, prefixMean]
  constructor
  · norm_num [prefixCorrectedSumSquares, prefixMean, Finset.sum_range_succ]
  · norm_num [prefixCorrectedSumSquares, prefixMean, Finset.sum_range_succ]
    change ((10000 : ℝ) - 10001) ^ 2 + ((10001 : ℝ) - 10001) ^ 2 +
        ((10002 : ℝ) - 10001) ^ 2 = 2
    norm_num
    ring_nf
    change (1 : ℝ) * 2 + 0 = 2
    norm_num

/-- Higham §1.9's update recurrence example returns the exact sample variance
`Q_3/(3-1) = 1` on the data `[10000, 10001, 10002]`. -/
theorem sampleVarianceUpdate_example_10000_10001_10002 :
    prefixCorrectedSumSquares (fun j : ℕ => (10000 : ℝ) + (j : ℝ)) 3 /
        ((3 : ℝ) - 1) = 1 := by
  rw [(prefixCorrectedSumSquares_example_values_10000_10001_10002).2.2]
  norm_num

/-- The exact two-pass sample-variance formula is nonnegative for `n > 1`. -/
theorem sampleVarianceTwoPass_nonneg {n : ℕ} (x : Fin n → ℝ) (hn : 1 < n) :
    0 ≤ sampleVarianceTwoPass x := by
  unfold sampleVarianceTwoPass
  have hsum : 0 ≤ ∑ i, (x i - sampleMean x) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hden : 0 ≤ (n : ℝ) - 1 := by
    have hnreal : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  exact div_nonneg hsum hden

/-- Consequently, the exact one-pass formula is also nonnegative; only its
floating-point evaluation can become negative. -/
theorem sampleVarianceOnePass_nonneg_exact {n : ℕ} (x : Fin n → ℝ) (hn : 1 < n) :
    0 ≤ sampleVarianceOnePass x := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have hnreal : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (Nat.lt_trans Nat.zero_lt_one hn)
    exact ne_of_gt hnreal
  rw [← sampleVarianceTwoPass_eq_onePass x hn0]
  exact sampleVarianceTwoPass_nonneg x hn

/-- Higham §1.9's exact-real target for the data `[10000, 10001, 10002]` is
sample variance `1`. -/
theorem sampleVarianceTwoPass_example_10000_10001_10002 :
    sampleVarianceTwoPass (fun i : Fin 3 => (10000 : ℝ) + (i.val : ℝ)) = 1 := by
  simp [sampleVarianceTwoPass, sampleMean, Fin.sum_univ_succ]
  field_simp
  ring

/-- With exact aggregates, the one-pass aggregate formula gives the same
target value `1` for Higham §1.9's `[10000, 10001, 10002]` example. -/
theorem sampleVarianceOnePassAggregates_exact_example_10000_10001_10002 :
    sampleVarianceOnePassAggregates 3 300060005 30003 = 1 := by
  norm_num [sampleVarianceOnePassAggregates]
  rfl

/-- If the already-formed sum-of-squares aggregate has rounded down to the
same value as `sum^2/n`, the one-pass aggregate formula returns zero.  This
records the final cancellation mechanism in Higham §1.9's single-precision
example; the upstream proof that a particular machine rounds to this aggregate
is a separate floating-point accumulation obligation. -/
theorem sampleVarianceOnePassAggregates_cancelled_example_10000_10001_10002 :
    sampleVarianceOnePassAggregates 3 300060003 30003 = 0 := by
  norm_num [sampleVarianceOnePassAggregates]
  rfl

/-- The aggregate-collapsed one-pass value in the `[10000, 10001, 10002]`
example has relative error `1` against the exact target. -/
theorem sampleVarianceOnePassAggregates_cancelled_relError_example_10000_10001_10002 :
    relError (sampleVarianceOnePassAggregates 3 300060003 30003)
      (sampleVarianceTwoPass (fun i : Fin 3 => (10000 : ℝ) + (i.val : ℝ))) = 1 := by
  rw [sampleVarianceOnePassAggregates_cancelled_example_10000_10001_10002,
    sampleVarianceTwoPass_example_10000_10001_10002]
  norm_num [relError]
  rfl

/-- Once rounded one-pass aggregates violate the exact Cauchy-Schwarz
nonnegativity relation `sumSq >= sum^2/n`, the aggregate one-pass variance is
negative.  This isolates the sign mechanism behind Higham's warning that the
computed one-pass answer can be negative. -/
theorem sampleVarianceOnePassAggregates_neg_of_sumSq_lt {n : ℕ}
    {sumSq sum : ℝ} (hn : 1 < n) (hbad : sumSq < sum ^ 2 / (n : ℝ)) :
    sampleVarianceOnePassAggregates n sumSq sum < 0 := by
  unfold sampleVarianceOnePassAggregates
  have hden : 0 < (n : ℝ) - 1 := by
    have hnreal : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn
    linarith
  have hnum : sumSq - sum ^ 2 / (n : ℝ) < 0 := by
    linarith
  exact div_neg_of_neg_of_pos hnum hden

/-- A neighboring aggregate to Higham §1.9's single-precision example produces
a negative one-pass variance: if the rounded sum of squares is one unit below
`sum^2/n`, the aggregate formula returns `-1/2`. -/
theorem sampleVarianceOnePassAggregates_negative_example_10000_10001_10002 :
    sampleVarianceOnePassAggregates 3 300060002 30003 = -(1 / 2 : ℝ) := by
  norm_num [sampleVarianceOnePassAggregates]

/-- The neighboring aggregate in the one-pass warning is strictly negative. -/
theorem sampleVarianceOnePassAggregates_negative_lt_zero_example_10000_10001_10002 :
    sampleVarianceOnePassAggregates 3 300060002 30003 < 0 := by
  rw [sampleVarianceOnePassAggregates_negative_example_10000_10001_10002]
  norm_num

/-- The neighboring negative aggregate is `3/2` away in absolute error from
the exact variance `1` for Higham §1.9's `[10000, 10001, 10002]` data. -/
theorem sampleVarianceOnePassAggregates_negative_absError_example_10000_10001_10002 :
    absError (sampleVarianceOnePassAggregates 3 300060002 30003)
      (sampleVarianceTwoPass (fun i : Fin 3 => (10000 : ℝ) + (i.val : ℝ))) =
        3 / 2 := by
  rw [sampleVarianceOnePassAggregates_negative_example_10000_10001_10002,
    sampleVarianceTwoPass_example_10000_10001_10002]
  norm_num [absError]

/-- The neighboring negative aggregate has relative error `3/2` against the
exact variance `1` for Higham §1.9's `[10000, 10001, 10002]` data. -/
theorem sampleVarianceOnePassAggregates_negative_relError_example_10000_10001_10002 :
    relError (sampleVarianceOnePassAggregates 3 300060002 30003)
      (sampleVarianceTwoPass (fun i : Fin 3 => (10000 : ℝ) + (i.val : ℝ))) =
        3 / 2 := by
  rw [sampleVarianceOnePassAggregates_negative_example_10000_10001_10002,
    sampleVarianceTwoPass_example_10000_10001_10002]
  norm_num [relError]

-- ============================================================
-- Concrete binary32 one-pass trace for Higham §1.9
-- ============================================================

private abbrev sampleVarianceIeeeSingleFormat : FloatingPointFormat :=
  FloatingPointFormat.ieeeSingleFormat

private theorem ieeeSingleFiniteSystem_of_normalizedExponentRepresentation
    {x : ℝ} {e : ℤ}
    (h : sampleVarianceIeeeSingleFormat.normalizedExponentRepresentation x e) :
    sampleVarianceIeeeSingleFormat.finiteSystem x :=
  Or.inr (Or.inl
    (FloatingPointFormat.normalizedExponentRepresentation_normalizedSystem h))

private theorem ieeeSingle_finiteSystem_zero :
    sampleVarianceIeeeSingleFormat.finiteSystem (0 : ℝ) :=
  Or.inl rfl

private theorem ieeeSingle_finiteSystem_10000 :
    sampleVarianceIeeeSingleFormat.finiteSystem (10000 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 14)
  refine ⟨false, 10240000, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl

private theorem ieeeSingle_finiteSystem_10001 :
    sampleVarianceIeeeSingleFormat.finiteSystem (10001 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 14)
  refine ⟨false, 10241024, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl

private theorem ieeeSingle_finiteSystem_10002 :
    sampleVarianceIeeeSingleFormat.finiteSystem (10002 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 14)
  refine ⟨false, 10242048, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl

private theorem ieeeSingle_finiteSystem_20001 :
    sampleVarianceIeeeSingleFormat.finiteSystem (20001 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 15)
  refine ⟨false, 10240512, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl

private theorem ieeeSingle_finiteSystem_30003 :
    sampleVarianceIeeeSingleFormat.finiteSystem (30003 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 15)
  refine ⟨false, 15361536, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl

private theorem ieeeSingle_finiteSystem_100000000 :
    sampleVarianceIeeeSingleFormat.finiteSystem (100000000 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 27)
  refine ⟨false, 12500000, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl

private theorem ieeeSingle_finiteSystem_200020000 :
    sampleVarianceIeeeSingleFormat.finiteSystem (200020000 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 28)
  refine ⟨false, 12501250, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl

private theorem ieeeSingle_finiteSystem_300060000 :
    sampleVarianceIeeeSingleFormat.finiteSystem (300060000 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 29)
  refine ⟨false, 9376875, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl

private theorem ieeeSingle_finiteSystem_300059968 :
    sampleVarianceIeeeSingleFormat.finiteSystem (300059968 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 29)
  refine ⟨false, 9376874, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl

private theorem ieeeSingle_finiteSystem_neg32 :
    sampleVarianceIeeeSingleFormat.finiteSystem (-32 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 6)
  refine ⟨true, 8388608, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl

private theorem ieeeSingle_finiteSystem_neg16 :
    sampleVarianceIeeeSingleFormat.finiteSystem (-16 : ℝ) := by
  apply ieeeSingleFiniteSystem_of_normalizedExponentRepresentation (e := 5)
  refine ⟨true, 8388608, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa, FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.exponentInRange]
  · norm_num [sampleVarianceIeeeSingleFormat, FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
    try rfl

/-- The first datum in Higham §1.9's single-precision one-pass example. -/
noncomputable def sampleVarianceOnePassIeeeSingle_x0 : ℝ :=
  10000

/-- The second datum in Higham §1.9's single-precision one-pass example. -/
noncomputable def sampleVarianceOnePassIeeeSingle_x1 : ℝ :=
  10001

/-- The third datum in Higham §1.9's single-precision one-pass example. -/
noncomputable def sampleVarianceOnePassIeeeSingle_x2 : ℝ :=
  10002

/-- Rounded binary32 square of `10000` in the one-pass sample-variance path. -/
noncomputable def sampleVarianceOnePassIeeeSingle_sq0 : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.mul sampleVarianceOnePassIeeeSingle_x0
    sampleVarianceOnePassIeeeSingle_x0

/-- Rounded binary32 square of `10001` in the one-pass sample-variance path. -/
noncomputable def sampleVarianceOnePassIeeeSingle_sq1 : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.mul sampleVarianceOnePassIeeeSingle_x1
    sampleVarianceOnePassIeeeSingle_x1

/-- Rounded binary32 square of `10002` in the one-pass sample-variance path. -/
noncomputable def sampleVarianceOnePassIeeeSingle_sq2 : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.mul sampleVarianceOnePassIeeeSingle_x2
    sampleVarianceOnePassIeeeSingle_x2

/-- First rounded binary32 sum in the one-pass sum-of-squares accumulator. -/
noncomputable def sampleVarianceOnePassIeeeSingle_sumSq01 : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.add sampleVarianceOnePassIeeeSingle_sq0
    sampleVarianceOnePassIeeeSingle_sq1

/-- Final rounded binary32 sum-of-squares accumulator. -/
noncomputable def sampleVarianceOnePassIeeeSingle_sumSq : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.add sampleVarianceOnePassIeeeSingle_sumSq01
    sampleVarianceOnePassIeeeSingle_sq2

/-- First rounded binary32 ordinary sum accumulator. -/
noncomputable def sampleVarianceOnePassIeeeSingle_sum01 : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.add sampleVarianceOnePassIeeeSingle_x0
    sampleVarianceOnePassIeeeSingle_x1

/-- Final rounded binary32 ordinary sum accumulator. -/
noncomputable def sampleVarianceOnePassIeeeSingle_sum : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.add sampleVarianceOnePassIeeeSingle_sum01
    sampleVarianceOnePassIeeeSingle_x2

/-- Rounded binary32 square of the rounded ordinary sum. -/
noncomputable def sampleVarianceOnePassIeeeSingle_sumSquare : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.mul sampleVarianceOnePassIeeeSingle_sum
    sampleVarianceOnePassIeeeSingle_sum

/-- Rounded binary32 quotient `(rounded sum)^2 / 3`. -/
noncomputable def sampleVarianceOnePassIeeeSingle_meanSquareTerm : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.div sampleVarianceOnePassIeeeSingle_sumSquare 3

/-- Rounded binary32 cancellation numerator in the one-pass variance formula. -/
noncomputable def sampleVarianceOnePassIeeeSingle_numerator : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.sub sampleVarianceOnePassIeeeSingle_sumSq
    sampleVarianceOnePassIeeeSingle_meanSquareTerm

/-- Rounded binary32 one-pass sample-variance trace for Higham §1.9's data. -/
noncomputable def sampleVarianceOnePassIeeeSingleTrace : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.div sampleVarianceOnePassIeeeSingle_numerator 2

/-- The four nontrivial binary32 nearest/even primitive values in the concrete
one-pass sample-variance trace.  Exact grid-point operations in the same trace
are proved below from `finiteSystem` facts; later theorems prove these four
selector equalities outright and close the full concrete operation trace. -/
def sampleVarianceOnePassIeeeSingleRoundingCertificate : Prop :=
  sampleVarianceOnePassIeeeSingle_sq1 = 100020000 ∧
    sampleVarianceOnePassIeeeSingle_sq2 = 100040000 ∧
      sampleVarianceOnePassIeeeSingle_sumSquare = 900180032 ∧
        sampleVarianceOnePassIeeeSingle_meanSquareTerm = 300060000

/-- Source round-to-even evidence for the non-grid binary32 primitive
`10001^2 -> 100020000` in Higham §1.9's one-pass example. -/
theorem sampleVarianceOnePassIeeeSingle_sq1_sourceRoundToEvenEvidence :
    sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
      (BasicOp.exact BasicOp.mul sampleVarianceOnePassIeeeSingle_x1
        sampleVarianceOnePassIeeeSingle_x1) (100020000 : ℝ) := by
  norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x1]
  change sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
    (100020001 : ℝ) (100020000 : ℝ)
  refine Or.inl ⟨27, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
  · refine Or.inr ⟨100020000, 100020008, 12502500, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact
        FloatingPointFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
          (fmt := sampleVarianceIeeeSingleFormat) (by
            refine ⟨false, 12502500, 27, ?_, ?_, ?_⟩
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedMantissa,
                FloatingPointFormat.mantissaInRange,
                FloatingPointFormat.minNormalMantissa]
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedMantissa,
                FloatingPointFormat.mantissaInRange,
                FloatingPointFormat.minNormalMantissa]
            · refine Or.inl ⟨?_, ?_⟩
              · norm_num [sampleVarianceIeeeSingleFormat,
                  FloatingPointFormat.ieeeSingleFormat,
                  FloatingPointFormat.normalizedValue,
                  FloatingPointFormat.signValue, FloatingPointFormat.betaR]
                try rfl
              · norm_num [sampleVarianceIeeeSingleFormat,
                  FloatingPointFormat.ieeeSingleFormat,
                  FloatingPointFormat.normalizedValue,
                  FloatingPointFormat.signValue, FloatingPointFormat.betaR]
                try rfl)
    · refine ⟨false, 27, ?_, ?_⟩
      · norm_num [sampleVarianceIeeeSingleFormat,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.mantissaInRange,
          FloatingPointFormat.minNormalMantissa]
      · norm_num [sampleVarianceIeeeSingleFormat,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedValue,
          FloatingPointFormat.signValue, FloatingPointFormat.betaR]
        try rfl
    · norm_num
    · norm_num
    · norm_num
    · rw [FloatingPointFormat.nearestAdjacentRoundToEven_eq_left_of_left_closer]
      norm_num

private theorem sampleVarianceOnePassIeeeSingle_sq1_finiteNormalRange :
    sampleVarianceIeeeSingleFormat.finiteNormalRange (100020001 : ℝ) := by
  constructor
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.finiteNormalRange,
      FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR]
  · simp [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.maxFiniteMagnitude,
      FloatingPointFormat.betaR]
    change (100020001 : ℝ) ≤
      (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹)
    have hfactor : (1 / 2 : ℝ) ≤ 1 - ((2 : ℝ) ^ 24)⁻¹ := by
      norm_num
    have hmul :
        (2 : ℝ) ^ 128 * (1 / 2 : ℝ) ≤
          (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    have hpow : (2 : ℝ) ^ 128 * (1 / 2 : ℝ) = (2 : ℝ) ^ 127 := by
      norm_num
    have hsmall : (100020001 : ℝ) ≤ (2 : ℝ) ^ 127 := by
      norm_num
    have hlarge :
        (2 : ℝ) ^ 127 ≤
          (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) := by
      calc
        (2 : ℝ) ^ 127 = (2 : ℝ) ^ 128 * (1 / 2 : ℝ) := by
          rw [hpow]
        _ ≤ (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) := hmul
    exact le_trans hsmall hlarge

/-- The total binary32 round-to-even selector sends `10001^2 = 100020001` to
`100020000`; the left endpoint of the adjacent binary32 bracket is strictly
nearer than the right endpoint. -/
theorem sampleVarianceOnePassIeeeSingle_sq1_eq :
    sampleVarianceOnePassIeeeSingle_sq1 = 100020000 := by
  have hpolicy :
      sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
        (100020001 : ℝ)
        (sampleVarianceIeeeSingleFormat.finiteRoundToEven (100020001 : ℝ)) :=
    FloatingPointFormat.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      sampleVarianceOnePassIeeeSingle_sq1_finiteNormalRange
  have hround :
      sampleVarianceIeeeSingleFormat.nearestRoundingToUnbounded
        (100020001 : ℝ)
        (sampleVarianceIeeeSingleFormat.finiteRoundToEven (100020001 : ℝ)) :=
    FloatingPointFormat.sourceRoundToEvenEvidence_nearestRoundingToUnbounded hpolicy
  have hadj :
      sampleVarianceIeeeSingleFormat.realOrderAdjacentNormalized
        (100020000 : ℝ) (100020008 : ℝ) := by
    exact
      FloatingPointFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
        (fmt := sampleVarianceIeeeSingleFormat) (by
          refine ⟨false, 12502500, 27, ?_, ?_, ?_⟩
          · norm_num [sampleVarianceIeeeSingleFormat,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedMantissa,
              FloatingPointFormat.mantissaInRange,
              FloatingPointFormat.minNormalMantissa]
          · norm_num [sampleVarianceIeeeSingleFormat,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedMantissa,
              FloatingPointFormat.mantissaInRange,
              FloatingPointFormat.minNormalMantissa]
          · refine Or.inl ⟨?_, ?_⟩
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedValue,
                FloatingPointFormat.signValue, FloatingPointFormat.betaR]
              try rfl
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedValue,
                FloatingPointFormat.signValue, FloatingPointFormat.betaR]
              try rfl)
  have hrounded :
      sampleVarianceIeeeSingleFormat.finiteRoundToEven (100020001 : ℝ) =
        (100020000 : ℝ) :=
    FloatingPointFormat.nearestRoundingToUnbounded_eq_left_of_realOrderAdjacent_ordered_between_of_left_closer
      hround hadj (by norm_num) (by norm_num)
  unfold sampleVarianceOnePassIeeeSingle_sq1
  change sampleVarianceIeeeSingleFormat.finiteRoundToEven
      (BasicOp.exact BasicOp.mul sampleVarianceOnePassIeeeSingle_x1
        sampleVarianceOnePassIeeeSingle_x1) = (100020000 : ℝ)
  norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x1]
  exact hrounded

/-- Source round-to-even evidence for the halfway binary32 primitive
`10002^2 -> 100040000`: the endpoints are equally near and the left mantissa
is even. -/
theorem sampleVarianceOnePassIeeeSingle_sq2_sourceRoundToEvenEvidence :
    sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
      (BasicOp.exact BasicOp.mul sampleVarianceOnePassIeeeSingle_x2
        sampleVarianceOnePassIeeeSingle_x2) (100040000 : ℝ) := by
  norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x2]
  change sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
    (100040004 : ℝ) (100040000 : ℝ)
  refine Or.inl ⟨27, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
  · refine Or.inr ⟨100040000, 100040008, 12505000, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact
        FloatingPointFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
          (fmt := sampleVarianceIeeeSingleFormat) (by
            refine ⟨false, 12505000, 27, ?_, ?_, ?_⟩
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedMantissa,
                FloatingPointFormat.mantissaInRange,
                FloatingPointFormat.minNormalMantissa]
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedMantissa,
                FloatingPointFormat.mantissaInRange,
                FloatingPointFormat.minNormalMantissa]
            · refine Or.inl ⟨?_, ?_⟩
              · norm_num [sampleVarianceIeeeSingleFormat,
                  FloatingPointFormat.ieeeSingleFormat,
                  FloatingPointFormat.normalizedValue,
                  FloatingPointFormat.signValue, FloatingPointFormat.betaR]
                try rfl
              · norm_num [sampleVarianceIeeeSingleFormat,
                  FloatingPointFormat.ieeeSingleFormat,
                  FloatingPointFormat.normalizedValue,
                  FloatingPointFormat.signValue, FloatingPointFormat.betaR]
                try rfl)
    · refine ⟨false, 27, ?_, ?_⟩
      · norm_num [sampleVarianceIeeeSingleFormat,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.mantissaInRange,
          FloatingPointFormat.minNormalMantissa]
      · norm_num [sampleVarianceIeeeSingleFormat,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedValue,
          FloatingPointFormat.signValue, FloatingPointFormat.betaR]
        try rfl
    · norm_num
    · norm_num
    · norm_num
    · rw [FloatingPointFormat.nearestAdjacentRoundToEven_eq_left_of_tie_even]
      · norm_num
      · norm_num [FloatingPointFormat.evenMantissa]

private theorem sampleVarianceOnePassIeeeSingle_sq2_finiteNormalRange :
    sampleVarianceIeeeSingleFormat.finiteNormalRange (100040004 : ℝ) := by
  constructor
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.finiteNormalRange,
      FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR]
  · simp [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.maxFiniteMagnitude,
      FloatingPointFormat.betaR]
    change (100040004 : ℝ) ≤
      (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹)
    have hfactor : (1 / 2 : ℝ) ≤ 1 - ((2 : ℝ) ^ 24)⁻¹ := by
      norm_num
    have hmul :
        (2 : ℝ) ^ 128 * (1 / 2 : ℝ) ≤
          (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    have hpow : (2 : ℝ) ^ 128 * (1 / 2 : ℝ) = (2 : ℝ) ^ 127 := by
      norm_num
    have hsmall : (100040004 : ℝ) ≤ (2 : ℝ) ^ 127 := by
      norm_num
    have hlarge :
        (2 : ℝ) ^ 127 ≤
          (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) := by
      calc
        (2 : ℝ) ^ 127 = (2 : ℝ) ^ 128 * (1 / 2 : ℝ) := by
          rw [hpow]
        _ ≤ (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) := hmul
    exact le_trans hsmall hlarge

/-- The total binary32 round-to-even selector sends the exact halfway square
`10002^2 = 100040004` to the even-left endpoint `100040000`. -/
theorem sampleVarianceOnePassIeeeSingle_sq2_eq :
    sampleVarianceOnePassIeeeSingle_sq2 = 100040000 := by
  have hpolicy :
      sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
        (100040004 : ℝ)
        (sampleVarianceIeeeSingleFormat.finiteRoundToEven (100040004 : ℝ)) :=
    FloatingPointFormat.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      sampleVarianceOnePassIeeeSingle_sq2_finiteNormalRange
  have hadj :
      sampleVarianceIeeeSingleFormat.realOrderAdjacentNormalized
        (100040000 : ℝ) (100040008 : ℝ) := by
    exact
      FloatingPointFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
        (fmt := sampleVarianceIeeeSingleFormat) (by
          refine ⟨false, 12505000, 27, ?_, ?_, ?_⟩
          · norm_num [sampleVarianceIeeeSingleFormat,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedMantissa,
              FloatingPointFormat.mantissaInRange,
              FloatingPointFormat.minNormalMantissa]
          · norm_num [sampleVarianceIeeeSingleFormat,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedMantissa,
              FloatingPointFormat.mantissaInRange,
              FloatingPointFormat.minNormalMantissa]
          · refine Or.inl ⟨?_, ?_⟩
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedValue,
                FloatingPointFormat.signValue, FloatingPointFormat.betaR]
              try rfl
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedValue,
                FloatingPointFormat.signValue, FloatingPointFormat.betaR]
              try rfl)
  have hleftMantissa :
      sampleVarianceIeeeSingleFormat.normalizedMantissa 12505000 := by
    norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hleft :
      (100040000 : ℝ) =
        sampleVarianceIeeeSingleFormat.normalizedValue false 12505000 27 := by
    norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR]
    try rfl
  have hrounded :
      sampleVarianceIeeeSingleFormat.finiteRoundToEven (100040004 : ℝ) =
        (100040000 : ℝ) :=
    FloatingPointFormat.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_tie_even
      hpolicy hadj (by norm_num) hleftMantissa hleft
      (by norm_num) (by norm_num [FloatingPointFormat.evenMantissa])
  unfold sampleVarianceOnePassIeeeSingle_sq2
  change sampleVarianceIeeeSingleFormat.finiteRoundToEven
      (BasicOp.exact BasicOp.mul sampleVarianceOnePassIeeeSingle_x2
        sampleVarianceOnePassIeeeSingle_x2) = (100040000 : ℝ)
  norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x2]
  exact hrounded

/-- Source round-to-even evidence for the exact binary32 primitive value
`30003^2 -> 900180032` in the one-pass trace. -/
theorem sampleVarianceOnePassIeeeSingle_sumSquare_exact_sourceRoundToEvenEvidence :
    sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
      (900180009 : ℝ) (900180032 : ℝ) := by
  refine Or.inl ⟨30, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
  · refine Or.inr ⟨900179968, 900180032, 14065312, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact
        FloatingPointFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
          (fmt := sampleVarianceIeeeSingleFormat) (by
            refine ⟨false, 14065312, 30, ?_, ?_, ?_⟩
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedMantissa,
                FloatingPointFormat.mantissaInRange,
                FloatingPointFormat.minNormalMantissa]
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedMantissa,
                FloatingPointFormat.mantissaInRange,
                FloatingPointFormat.minNormalMantissa]
            · refine Or.inl ⟨?_, ?_⟩
              · norm_num [sampleVarianceIeeeSingleFormat,
                  FloatingPointFormat.ieeeSingleFormat,
                  FloatingPointFormat.normalizedValue,
                  FloatingPointFormat.signValue, FloatingPointFormat.betaR]
                try rfl
              · norm_num [sampleVarianceIeeeSingleFormat,
                  FloatingPointFormat.ieeeSingleFormat,
                  FloatingPointFormat.normalizedValue,
                  FloatingPointFormat.signValue, FloatingPointFormat.betaR]
                try rfl)
    · refine ⟨false, 30, ?_, ?_⟩
      · norm_num [sampleVarianceIeeeSingleFormat,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.mantissaInRange,
          FloatingPointFormat.minNormalMantissa]
      · norm_num [sampleVarianceIeeeSingleFormat,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedValue,
          FloatingPointFormat.signValue, FloatingPointFormat.betaR]
        try rfl
    · norm_num
    · norm_num
    · norm_num
    · rw [FloatingPointFormat.nearestAdjacentRoundToEven_eq_right_of_right_closer]
      norm_num

private theorem sampleVarianceOnePassIeeeSingle_sumSquare_exact_finiteNormalRange :
    sampleVarianceIeeeSingleFormat.finiteNormalRange (900180009 : ℝ) := by
  constructor
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.finiteNormalRange,
      FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR]
  · simp [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.maxFiniteMagnitude,
      FloatingPointFormat.betaR]
    change (900180009 : ℝ) ≤
      (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹)
    have hfactor : (1 / 2 : ℝ) ≤ 1 - ((2 : ℝ) ^ 24)⁻¹ := by
      norm_num
    have hmul :
        (2 : ℝ) ^ 128 * (1 / 2 : ℝ) ≤
          (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    have hpow : (2 : ℝ) ^ 128 * (1 / 2 : ℝ) = (2 : ℝ) ^ 127 := by
      norm_num
    have hsmall : (900180009 : ℝ) ≤ (2 : ℝ) ^ 127 := by
      norm_num
    have hlarge :
        (2 : ℝ) ^ 127 ≤
          (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) := by
      calc
        (2 : ℝ) ^ 127 = (2 : ℝ) ^ 128 * (1 / 2 : ℝ) := by
          rw [hpow]
        _ ≤ (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) := hmul
    exact le_trans hsmall hlarge

private theorem sampleVarianceOnePassIeeeSingle_sumSquare_exact_round_eq :
    sampleVarianceIeeeSingleFormat.finiteRoundToEven (900180009 : ℝ) =
      (900180032 : ℝ) := by
  have hpolicy :
      sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
        (900180009 : ℝ)
        (sampleVarianceIeeeSingleFormat.finiteRoundToEven (900180009 : ℝ)) :=
    FloatingPointFormat.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      sampleVarianceOnePassIeeeSingle_sumSquare_exact_finiteNormalRange
  have hround :
      sampleVarianceIeeeSingleFormat.nearestRoundingToUnbounded
        (900180009 : ℝ)
        (sampleVarianceIeeeSingleFormat.finiteRoundToEven (900180009 : ℝ)) :=
    FloatingPointFormat.sourceRoundToEvenEvidence_nearestRoundingToUnbounded hpolicy
  have hadj :
      sampleVarianceIeeeSingleFormat.realOrderAdjacentNormalized
        (900179968 : ℝ) (900180032 : ℝ) := by
    exact
      FloatingPointFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
        (fmt := sampleVarianceIeeeSingleFormat) (by
          refine ⟨false, 14065312, 30, ?_, ?_, ?_⟩
          · norm_num [sampleVarianceIeeeSingleFormat,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedMantissa,
              FloatingPointFormat.mantissaInRange,
              FloatingPointFormat.minNormalMantissa]
          · norm_num [sampleVarianceIeeeSingleFormat,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedMantissa,
              FloatingPointFormat.mantissaInRange,
              FloatingPointFormat.minNormalMantissa]
          · refine Or.inl ⟨?_, ?_⟩
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedValue,
                FloatingPointFormat.signValue, FloatingPointFormat.betaR]
              try rfl
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedValue,
                FloatingPointFormat.signValue, FloatingPointFormat.betaR]
              try rfl)
  exact
    FloatingPointFormat.nearestRoundingToUnbounded_eq_right_of_realOrderAdjacent_ordered_between_of_right_closer
      hround hadj (by norm_num) (by norm_num)

/-- Source round-to-even evidence for the exact binary32 primitive
`900180032 / 3 -> 300060000` in the one-pass trace. -/
theorem sampleVarianceOnePassIeeeSingle_meanSquareTerm_exact_sourceRoundToEvenEvidence :
    sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
      ((900180032 : ℝ) / 3) (300060000 : ℝ) := by
  refine Or.inl ⟨29, ?_, ?_, ?_⟩
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.betaR]
  · refine Or.inr ⟨300060000, 300060032, 9376875, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact
        FloatingPointFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
          (fmt := sampleVarianceIeeeSingleFormat) (by
            refine ⟨false, 9376875, 29, ?_, ?_, ?_⟩
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedMantissa,
                FloatingPointFormat.mantissaInRange,
                FloatingPointFormat.minNormalMantissa]
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedMantissa,
                FloatingPointFormat.mantissaInRange,
                FloatingPointFormat.minNormalMantissa]
            · refine Or.inl ⟨?_, ?_⟩
              · norm_num [sampleVarianceIeeeSingleFormat,
                  FloatingPointFormat.ieeeSingleFormat,
                  FloatingPointFormat.normalizedValue,
                  FloatingPointFormat.signValue, FloatingPointFormat.betaR]
                try rfl
              · norm_num [sampleVarianceIeeeSingleFormat,
                  FloatingPointFormat.ieeeSingleFormat,
                  FloatingPointFormat.normalizedValue,
                  FloatingPointFormat.signValue, FloatingPointFormat.betaR]
                try rfl)
    · refine ⟨false, 29, ?_, ?_⟩
      · norm_num [sampleVarianceIeeeSingleFormat,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.mantissaInRange,
          FloatingPointFormat.minNormalMantissa]
      · norm_num [sampleVarianceIeeeSingleFormat,
          FloatingPointFormat.ieeeSingleFormat,
          FloatingPointFormat.normalizedValue,
          FloatingPointFormat.signValue, FloatingPointFormat.betaR]
        try rfl
    · norm_num
    · norm_num
    · norm_num
    · rw [FloatingPointFormat.nearestAdjacentRoundToEven_eq_left_of_left_closer]
      norm_num

private theorem sampleVarianceOnePassIeeeSingle_meanSquareTerm_exact_finiteNormalRange :
    sampleVarianceIeeeSingleFormat.finiteNormalRange ((900180032 : ℝ) / 3) := by
  constructor
  · norm_num [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.finiteNormalRange,
      FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR]
  · have hpos : 0 ≤ ((900180032 : ℝ) / 3) := by
      norm_num
    rw [abs_of_nonneg hpos]
    simp [sampleVarianceIeeeSingleFormat,
      FloatingPointFormat.ieeeSingleFormat, FloatingPointFormat.maxFiniteMagnitude,
      FloatingPointFormat.betaR]
    change ((900180032 : ℝ) / 3) ≤
      (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹)
    have hfactor : (1 / 2 : ℝ) ≤ 1 - ((2 : ℝ) ^ 24)⁻¹ := by
      norm_num
    have hmul :
        (2 : ℝ) ^ 128 * (1 / 2 : ℝ) ≤
          (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    have hpow : (2 : ℝ) ^ 128 * (1 / 2 : ℝ) = (2 : ℝ) ^ 127 := by
      norm_num
    have hsmall : ((900180032 : ℝ) / 3) ≤ (2 : ℝ) ^ 127 := by
      norm_num
    have hlarge :
        (2 : ℝ) ^ 127 ≤
          (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) := by
      calc
        (2 : ℝ) ^ 127 = (2 : ℝ) ^ 128 * (1 / 2 : ℝ) := by
          rw [hpow]
        _ ≤ (2 : ℝ) ^ 128 * (1 - ((2 : ℝ) ^ 24)⁻¹) := hmul
    exact le_trans hsmall hlarge

private theorem sampleVarianceOnePassIeeeSingle_meanSquareTerm_exact_round_eq :
    sampleVarianceIeeeSingleFormat.finiteRoundToEven ((900180032 : ℝ) / 3) =
      (300060000 : ℝ) := by
  have hpolicy :
      sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
        ((900180032 : ℝ) / 3)
        (sampleVarianceIeeeSingleFormat.finiteRoundToEven ((900180032 : ℝ) / 3)) :=
    FloatingPointFormat.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      sampleVarianceOnePassIeeeSingle_meanSquareTerm_exact_finiteNormalRange
  have hround :
      sampleVarianceIeeeSingleFormat.nearestRoundingToUnbounded
        ((900180032 : ℝ) / 3)
        (sampleVarianceIeeeSingleFormat.finiteRoundToEven ((900180032 : ℝ) / 3)) :=
    FloatingPointFormat.sourceRoundToEvenEvidence_nearestRoundingToUnbounded hpolicy
  have hadj :
      sampleVarianceIeeeSingleFormat.realOrderAdjacentNormalized
        (300060000 : ℝ) (300060032 : ℝ) := by
    exact
      FloatingPointFormat.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
        (fmt := sampleVarianceIeeeSingleFormat) (by
          refine ⟨false, 9376875, 29, ?_, ?_, ?_⟩
          · norm_num [sampleVarianceIeeeSingleFormat,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedMantissa,
              FloatingPointFormat.mantissaInRange,
              FloatingPointFormat.minNormalMantissa]
          · norm_num [sampleVarianceIeeeSingleFormat,
              FloatingPointFormat.ieeeSingleFormat,
              FloatingPointFormat.normalizedMantissa,
              FloatingPointFormat.mantissaInRange,
              FloatingPointFormat.minNormalMantissa]
          · refine Or.inl ⟨?_, ?_⟩
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedValue,
                FloatingPointFormat.signValue, FloatingPointFormat.betaR]
              try rfl
            · norm_num [sampleVarianceIeeeSingleFormat,
                FloatingPointFormat.ieeeSingleFormat,
                FloatingPointFormat.normalizedValue,
                FloatingPointFormat.signValue, FloatingPointFormat.betaR]
              try rfl)
  exact
    FloatingPointFormat.nearestRoundingToUnbounded_eq_left_of_realOrderAdjacent_ordered_between_of_left_closer
      hround hadj (by norm_num) (by norm_num)

/-- Source round-to-even evidence for the binary32 division primitive once the
rounded sum square is known to be `900180032`. -/
theorem sampleVarianceOnePassIeeeSingle_meanSquareTerm_sourceRoundToEvenEvidence_of_sumSquare
    (hsumSquare : sampleVarianceOnePassIeeeSingle_sumSquare = 900180032) :
    sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
      (BasicOp.exact BasicOp.div sampleVarianceOnePassIeeeSingle_sumSquare 3)
      (300060000 : ℝ) := by
  rw [hsumSquare]
  exact sampleVarianceOnePassIeeeSingle_meanSquareTerm_exact_sourceRoundToEvenEvidence

/-- The first square in the concrete binary32 one-pass trace is exact. -/
theorem sampleVarianceOnePassIeeeSingle_sq0_eq :
    sampleVarianceOnePassIeeeSingle_sq0 = 100000000 := by
  have hfinite :
      sampleVarianceIeeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.mul sampleVarianceOnePassIeeeSingle_x0
          sampleVarianceOnePassIeeeSingle_x0) := by
    norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x0]
    exact ieeeSingle_finiteSystem_100000000
  unfold sampleVarianceOnePassIeeeSingle_sq0
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite]
  norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x0]

/-- The first ordinary sum in the concrete binary32 one-pass trace is exact. -/
theorem sampleVarianceOnePassIeeeSingle_sum01_eq :
    sampleVarianceOnePassIeeeSingle_sum01 = 20001 := by
  have hfinite :
      sampleVarianceIeeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.add sampleVarianceOnePassIeeeSingle_x0
          sampleVarianceOnePassIeeeSingle_x1) := by
    norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x0,
      sampleVarianceOnePassIeeeSingle_x1]
    exact ieeeSingle_finiteSystem_20001
  unfold sampleVarianceOnePassIeeeSingle_sum01
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite]
  norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x0,
    sampleVarianceOnePassIeeeSingle_x1]

/-- The ordinary sum accumulator in the concrete binary32 one-pass trace is
exact. -/
theorem sampleVarianceOnePassIeeeSingle_sum_eq :
    sampleVarianceOnePassIeeeSingle_sum = 30003 := by
  have hfinite :
      sampleVarianceIeeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.add sampleVarianceOnePassIeeeSingle_sum01
          sampleVarianceOnePassIeeeSingle_x2) := by
    rw [sampleVarianceOnePassIeeeSingle_sum01_eq]
    norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x2]
    exact ieeeSingle_finiteSystem_30003
  unfold sampleVarianceOnePassIeeeSingle_sum
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite,
    sampleVarianceOnePassIeeeSingle_sum01_eq]
  norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingle_x2]

/-- Source round-to-even evidence for the binary32 primitive
`sampleVarianceOnePassIeeeSingle_sum^2 -> 900180032`, after the ordinary sum
accumulator has been proved exact. -/
theorem sampleVarianceOnePassIeeeSingle_sumSquare_sourceRoundToEvenEvidence :
    sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
      (BasicOp.exact BasicOp.mul sampleVarianceOnePassIeeeSingle_sum
        sampleVarianceOnePassIeeeSingle_sum) (900180032 : ℝ) := by
  rw [sampleVarianceOnePassIeeeSingle_sum_eq]
  have hmul : BasicOp.exact BasicOp.mul (30003 : ℝ) (30003 : ℝ) =
      (900180009 : ℝ) := by
    norm_num [BasicOp.exact]
  simpa [hmul] using
    sampleVarianceOnePassIeeeSingle_sumSquare_exact_sourceRoundToEvenEvidence

/-- The rounded binary32 square of the exact ordinary sum is the displayed
single-precision value `900180032`. -/
theorem sampleVarianceOnePassIeeeSingle_sumSquare_eq :
    sampleVarianceOnePassIeeeSingle_sumSquare = 900180032 := by
  unfold sampleVarianceOnePassIeeeSingle_sumSquare
  rw [sampleVarianceOnePassIeeeSingle_sum_eq]
  change sampleVarianceIeeeSingleFormat.finiteRoundToEven
      (BasicOp.exact BasicOp.mul (30003 : ℝ) (30003 : ℝ)) = (900180032 : ℝ)
  norm_num [BasicOp.exact]
  exact sampleVarianceOnePassIeeeSingle_sumSquare_exact_round_eq

/-- The rounded binary32 quotient `(rounded sum)^2 / 3` is the displayed
single-precision value `300060000`. -/
theorem sampleVarianceOnePassIeeeSingle_meanSquareTerm_eq :
    sampleVarianceOnePassIeeeSingle_meanSquareTerm = 300060000 := by
  unfold sampleVarianceOnePassIeeeSingle_meanSquareTerm
  rw [sampleVarianceOnePassIeeeSingle_sumSquare_eq]
  change sampleVarianceIeeeSingleFormat.finiteRoundToEven
      (BasicOp.exact BasicOp.div (900180032 : ℝ) 3) = (300060000 : ℝ)
  norm_num [BasicOp.exact]
  exact sampleVarianceOnePassIeeeSingle_meanSquareTerm_exact_round_eq

/-- Closed source-level evidence for the four non-grid binary32 primitive
roundings used by the one-pass trace.  This proves the intended grid endpoints
and tie choices.  Later total-selector equalities turn this source evidence into
the closed concrete operation trace. -/
theorem sampleVarianceOnePassIeeeSingle_sourceRoundingEvidenceCertificate :
    sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
        (BasicOp.exact BasicOp.mul sampleVarianceOnePassIeeeSingle_x1
          sampleVarianceOnePassIeeeSingle_x1) (100020000 : ℝ) ∧
      sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
        (BasicOp.exact BasicOp.mul sampleVarianceOnePassIeeeSingle_x2
          sampleVarianceOnePassIeeeSingle_x2) (100040000 : ℝ) ∧
      sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
        (BasicOp.exact BasicOp.mul sampleVarianceOnePassIeeeSingle_sum
          sampleVarianceOnePassIeeeSingle_sum) (900180032 : ℝ) ∧
      sampleVarianceIeeeSingleFormat.sourceRoundToEvenEvidence
        ((900180032 : ℝ) / 3) (300060000 : ℝ) := by
  exact ⟨sampleVarianceOnePassIeeeSingle_sq1_sourceRoundToEvenEvidence,
    sampleVarianceOnePassIeeeSingle_sq2_sourceRoundToEvenEvidence,
    sampleVarianceOnePassIeeeSingle_sumSquare_sourceRoundToEvenEvidence,
    sampleVarianceOnePassIeeeSingle_meanSquareTerm_exact_sourceRoundToEvenEvidence⟩

/-- The closed square, sum-square, and mean-square primitive equalities imply
the full concrete binary32 rounding certificate. -/
theorem sampleVarianceOnePassIeeeSingleRoundingCertificate_of_sq2_eq
    (hsq2 : sampleVarianceOnePassIeeeSingle_sq2 = 100040000) :
    sampleVarianceOnePassIeeeSingleRoundingCertificate := by
  exact ⟨sampleVarianceOnePassIeeeSingle_sq1_eq, hsq2,
    sampleVarianceOnePassIeeeSingle_sumSquare_eq,
    sampleVarianceOnePassIeeeSingle_meanSquareTerm_eq⟩

/-- The concrete binary32 one-pass operation trace has all four non-grid
nearest/even primitive roundings closed. -/
theorem sampleVarianceOnePassIeeeSingleRoundingCertificate_closed :
    sampleVarianceOnePassIeeeSingleRoundingCertificate :=
  sampleVarianceOnePassIeeeSingleRoundingCertificate_of_sq2_eq
    sampleVarianceOnePassIeeeSingle_sq2_eq

private theorem sampleVarianceOnePassIeeeSingle_sumSq01_eq_of_sq1
    (hsq1 : sampleVarianceOnePassIeeeSingle_sq1 = 100020000) :
    sampleVarianceOnePassIeeeSingle_sumSq01 = 200020000 := by
  have hfinite :
      sampleVarianceIeeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.add sampleVarianceOnePassIeeeSingle_sq0
          sampleVarianceOnePassIeeeSingle_sq1) := by
    rw [sampleVarianceOnePassIeeeSingle_sq0_eq, hsq1]
    norm_num [BasicOp.exact]
    exact ieeeSingle_finiteSystem_200020000
  unfold sampleVarianceOnePassIeeeSingle_sumSq01
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite,
    sampleVarianceOnePassIeeeSingle_sq0_eq, hsq1]
  norm_num [BasicOp.exact]

/-- Under the two non-grid square-rounding facts, the sum-of-squares accumulator
in the concrete binary32 one-pass trace is exactly `300060000`. -/
theorem sampleVarianceOnePassIeeeSingle_sumSq_eq_of_sq1_sq2
    (hsq1 : sampleVarianceOnePassIeeeSingle_sq1 = 100020000)
    (hsq2 : sampleVarianceOnePassIeeeSingle_sq2 = 100040000) :
    sampleVarianceOnePassIeeeSingle_sumSq = 300060000 := by
  have hsumSq01 := sampleVarianceOnePassIeeeSingle_sumSq01_eq_of_sq1 hsq1
  have hfinite :
      sampleVarianceIeeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.add sampleVarianceOnePassIeeeSingle_sumSq01
          sampleVarianceOnePassIeeeSingle_sq2) := by
    rw [hsumSq01, hsq2]
    norm_num [BasicOp.exact]
    exact ieeeSingle_finiteSystem_300060000
  unfold sampleVarianceOnePassIeeeSingle_sumSq
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite,
    hsumSq01, hsq2]
  norm_num [BasicOp.exact]

/-- With the first square unconditional, the final sum-of-squares accumulator
can be reduced to the `10002^2` primitive equality. -/
theorem sampleVarianceOnePassIeeeSingle_sumSq_eq_of_sq2
    (hsq2 : sampleVarianceOnePassIeeeSingle_sq2 = 100040000) :
    sampleVarianceOnePassIeeeSingle_sumSq = 300060000 :=
  sampleVarianceOnePassIeeeSingle_sumSq_eq_of_sq1_sq2
    sampleVarianceOnePassIeeeSingle_sq1_eq hsq2

/-- The final sum-of-squares accumulator in the concrete binary32 one-pass trace
is exactly `300060000`. -/
theorem sampleVarianceOnePassIeeeSingle_sumSq_eq :
    sampleVarianceOnePassIeeeSingle_sumSq = 300060000 :=
  sampleVarianceOnePassIeeeSingle_sumSq_eq_of_sq2
    sampleVarianceOnePassIeeeSingle_sq2_eq

private theorem sampleVarianceOnePassIeeeSingle_numerator_eq_zero_of_roundingCertificate
    (hcert : sampleVarianceOnePassIeeeSingleRoundingCertificate) :
    sampleVarianceOnePassIeeeSingle_numerator = 0 := by
  rcases hcert with ⟨hsq1, hsq2, _hsumSquare, hmeanSquare⟩
  have hsumSq := sampleVarianceOnePassIeeeSingle_sumSq_eq_of_sq1_sq2 hsq1 hsq2
  have hfinite :
      sampleVarianceIeeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.sub sampleVarianceOnePassIeeeSingle_sumSq
          sampleVarianceOnePassIeeeSingle_meanSquareTerm) := by
    rw [hsumSq, hmeanSquare]
    simpa [BasicOp.exact] using ieeeSingle_finiteSystem_zero
  unfold sampleVarianceOnePassIeeeSingle_numerator
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite,
    hsumSq, hmeanSquare]
  norm_num [BasicOp.exact]
  rfl

/-- If the four non-grid binary32 primitive roundings in the §1.9 one-pass
trace have the displayed nearest/even values, then the actual rounded operation
trace returns `0.0`. -/
theorem sampleVarianceOnePassIeeeSingleTrace_zero_of_roundingCertificate
    (hcert : sampleVarianceOnePassIeeeSingleRoundingCertificate) :
    sampleVarianceOnePassIeeeSingleTrace = 0 := by
  have hnumer :=
    sampleVarianceOnePassIeeeSingle_numerator_eq_zero_of_roundingCertificate
      hcert
  have hfinite :
      sampleVarianceIeeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.div sampleVarianceOnePassIeeeSingle_numerator 2) := by
    rw [hnumer]
    simpa [BasicOp.exact] using ieeeSingle_finiteSystem_zero
  unfold sampleVarianceOnePassIeeeSingleTrace
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite,
    hnumer]
  norm_num [BasicOp.exact]
  rfl

/-- Under the same concrete binary32 rounding certificate, the one-pass trace
has relative error `1` against the exact sample variance, matching Higham
§1.9's displayed single-precision result. -/
theorem sampleVarianceOnePassIeeeSingleTrace_relError_one_of_roundingCertificate
    (hcert : sampleVarianceOnePassIeeeSingleRoundingCertificate) :
    relError sampleVarianceOnePassIeeeSingleTrace
        (sampleVarianceTwoPass
          (fun i : Fin 3 => (10000 : ℝ) + (i.val : ℝ))) = 1 := by
  rw [sampleVarianceOnePassIeeeSingleTrace_zero_of_roundingCertificate hcert,
    sampleVarianceTwoPass_example_10000_10001_10002]
  norm_num [relError]
  rfl

/-- The concrete binary32 one-pass trace returns `0.0` as soon as the
`10002^2 -> 100040000` primitive equality is supplied. -/
theorem sampleVarianceOnePassIeeeSingleTrace_zero_of_sq2_eq
    (hsq2 : sampleVarianceOnePassIeeeSingle_sq2 = 100040000) :
    sampleVarianceOnePassIeeeSingleTrace = 0 :=
  sampleVarianceOnePassIeeeSingleTrace_zero_of_roundingCertificate
    (sampleVarianceOnePassIeeeSingleRoundingCertificate_of_sq2_eq hsq2)

/-- The concrete binary32 one-pass trace returns `0.0`. -/
theorem sampleVarianceOnePassIeeeSingleTrace_zero :
    sampleVarianceOnePassIeeeSingleTrace = 0 :=
  sampleVarianceOnePassIeeeSingleTrace_zero_of_sq2_eq
    sampleVarianceOnePassIeeeSingle_sq2_eq

/-- The `10002^2 -> 100040000` primitive equality also suffices for the
relative-error-`1` statement against the exact two-pass sample variance. -/
theorem sampleVarianceOnePassIeeeSingleTrace_relError_one_of_sq2_eq
    (hsq2 : sampleVarianceOnePassIeeeSingle_sq2 = 100040000) :
    relError sampleVarianceOnePassIeeeSingleTrace
        (sampleVarianceTwoPass
          (fun i : Fin 3 => (10000 : ℝ) + (i.val : ℝ))) = 1 :=
  sampleVarianceOnePassIeeeSingleTrace_relError_one_of_roundingCertificate
    (sampleVarianceOnePassIeeeSingleRoundingCertificate_of_sq2_eq hsq2)

/-- The concrete binary32 one-pass trace has relative error `1` against the
exact two-pass sample variance. -/
theorem sampleVarianceOnePassIeeeSingleTrace_relError_one :
    relError sampleVarianceOnePassIeeeSingleTrace
        (sampleVarianceTwoPass
          (fun i : Fin 3 => (10000 : ℝ) + (i.val : ℝ))) = 1 :=
  sampleVarianceOnePassIeeeSingleTrace_relError_one_of_sq2_eq
    sampleVarianceOnePassIeeeSingle_sq2_eq

-- ============================================================
-- Supplied rounded-aggregate negative final-operation trace
-- ============================================================

/-- A supplied rounded sum-of-squares aggregate one binary32 ulp below
`300060000`.  This is not the aggregate produced by the concrete
`[10000,10001,10002]` binary32 trace above; it isolates the final-operation
mechanism behind the source warning that one-pass variance values can become
negative when rounded aggregates violate the exact nonnegativity relation. -/
noncomputable def sampleVarianceOnePassIeeeSingleNegativeAggregate_sumSq : ℝ :=
  300059968

/-- Supplied rounded mean-square aggregate used in the negative final-operation
diagnostic. -/
noncomputable def sampleVarianceOnePassIeeeSingleNegativeAggregate_meanSquareTerm :
    ℝ :=
  300060000

/-- Rounded binary32 final numerator from the supplied negative aggregate
diagnostic. -/
noncomputable def sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator :
    ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.sub sampleVarianceOnePassIeeeSingleNegativeAggregate_sumSq
    sampleVarianceOnePassIeeeSingleNegativeAggregate_meanSquareTerm

/-- Rounded binary32 final variance quotient from the supplied negative
aggregate diagnostic. -/
noncomputable def sampleVarianceOnePassIeeeSingleNegativeAggregateTrace : ℝ :=
  FloatingPointFormat.finiteRoundToEvenOp sampleVarianceIeeeSingleFormat
    BasicOp.div sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator 2

/-- The supplied rounded aggregates are binary32 finite-system values. -/
theorem sampleVarianceOnePassIeeeSingleNegativeAggregate_inputs_finiteSystem :
    sampleVarianceIeeeSingleFormat.finiteSystem
        sampleVarianceOnePassIeeeSingleNegativeAggregate_sumSq ∧
      sampleVarianceIeeeSingleFormat.finiteSystem
        sampleVarianceOnePassIeeeSingleNegativeAggregate_meanSquareTerm := by
  exact ⟨by
      simpa [sampleVarianceOnePassIeeeSingleNegativeAggregate_sumSq] using
        ieeeSingle_finiteSystem_300059968,
    by
      simpa [sampleVarianceOnePassIeeeSingleNegativeAggregate_meanSquareTerm] using
        ieeeSingle_finiteSystem_300060000⟩

/-- The final rounded subtraction in the supplied negative aggregate diagnostic
is exact and gives `-32`. -/
theorem sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator_eq :
    sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator = -32 := by
  have hfinite :
      sampleVarianceIeeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.sub
          sampleVarianceOnePassIeeeSingleNegativeAggregate_sumSq
          sampleVarianceOnePassIeeeSingleNegativeAggregate_meanSquareTerm) := by
    have hcalc :
        BasicOp.exact BasicOp.sub
            sampleVarianceOnePassIeeeSingleNegativeAggregate_sumSq
            sampleVarianceOnePassIeeeSingleNegativeAggregate_meanSquareTerm =
          (-32 : ℝ) := by
      norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingleNegativeAggregate_sumSq,
        sampleVarianceOnePassIeeeSingleNegativeAggregate_meanSquareTerm]
    simpa [hcalc] using ieeeSingle_finiteSystem_neg32
  unfold sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite]
  norm_num [BasicOp.exact, sampleVarianceOnePassIeeeSingleNegativeAggregate_sumSq,
    sampleVarianceOnePassIeeeSingleNegativeAggregate_meanSquareTerm]

/-- The supplied rounded-aggregate final operation trace returns the concrete
negative binary32 value `-16`. -/
theorem sampleVarianceOnePassIeeeSingleNegativeAggregateTrace_eq_neg_sixteen :
    sampleVarianceOnePassIeeeSingleNegativeAggregateTrace = -16 := by
  have hfinite :
      sampleVarianceIeeeSingleFormat.finiteSystem
        (BasicOp.exact BasicOp.div
          sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator 2) := by
    have hcalc :
        BasicOp.exact BasicOp.div
            sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator 2 =
          (-16 : ℝ) := by
      rw [sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator_eq]
      norm_num [BasicOp.exact]
    simpa [hcalc] using ieeeSingle_finiteSystem_neg16
  unfold sampleVarianceOnePassIeeeSingleNegativeAggregateTrace
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite,
    sampleVarianceOnePassIeeeSingleNegativeAggregate_numerator_eq]
  norm_num [BasicOp.exact]

/-- The supplied rounded-aggregate final operation trace is strictly negative. -/
theorem sampleVarianceOnePassIeeeSingleNegativeAggregateTrace_lt_zero :
    sampleVarianceOnePassIeeeSingleNegativeAggregateTrace < 0 := by
  rw [sampleVarianceOnePassIeeeSingleNegativeAggregateTrace_eq_neg_sixteen]
  norm_num

/-- Against the exact sample variance `1` for `[10000,10001,10002]`, the
supplied rounded-aggregate negative final trace has relative error `17`. -/
theorem sampleVarianceOnePassIeeeSingleNegativeAggregateTrace_relError :
    relError sampleVarianceOnePassIeeeSingleNegativeAggregateTrace
        (sampleVarianceTwoPass
          (fun i : Fin 3 => (10000 : ℝ) + (i.val : ℝ))) = 17 := by
  rw [sampleVarianceOnePassIeeeSingleNegativeAggregateTrace_eq_neg_sixteen,
    sampleVarianceTwoPass_example_10000_10001_10002]
  norm_num [relError]
  rfl

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
