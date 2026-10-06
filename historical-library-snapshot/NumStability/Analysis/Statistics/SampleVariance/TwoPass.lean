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
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.Analysis.Statistics.SampleVariance.Core
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
