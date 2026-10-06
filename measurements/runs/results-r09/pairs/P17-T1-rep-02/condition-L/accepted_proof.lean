import HighamBench.P17Definitions
import NumStability.Analysis.FiniteProbability

namespace HighamBench

open scoped BigOperators

lemma p17RecursiveCoefficient_castSucc
    {m : ℕ} (error : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    p17RecursiveCoefficient error i.castSucc =
      p17RecursiveCoefficient (fun k : Fin m => error k.castSucc) i *
        (1 + error (Fin.last m)) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [p17RecursiveCoefficient, Fin.prod_univ_castSucc]
  · simp [p17RecursiveCoefficient, p17SuffixErrorProduct]

lemma p17RecursiveCoefficient_last
    {m : ℕ} (error : Fin (m + 1) → ℝ) :
    p17RecursiveCoefficient error (Fin.last (m + 1)) =
      1 + error (Fin.last m) := by
  rw [← Fin.succ_last]
  change p17SuffixErrorProduct (m + 1) error (Fin.last m) = _
  simp [p17SuffixErrorProduct]

lemma p17RecursiveSum_eq_sum_coefficients
    {m : ℕ} (a : Fin (m + 1) → ℝ) (error : Fin m → ℝ) :
    p17RecursiveSum a error =
      ∑ i, a i * p17RecursiveCoefficient error i := by
  induction m with
  | zero =>
      simp [p17RecursiveSum, p17RecursiveCoefficient]
  | succ m ih =>
      rw [p17RecursiveSum]
      rw [Fin.foldl_succ_last]
      change
        (p17RecursiveSum (fun i : Fin (m + 1) => a i.castSucc)
              (fun k : Fin m => error k.castSucc) +
            a (Fin.last (m + 1))) *
          (1 + error (Fin.last m)) = _
      rw [ih]
      conv_rhs => rw [Fin.sum_univ_castSucc]
      simp only [p17RecursiveCoefficient_castSucc,
        p17RecursiveCoefficient_last, ← mul_assoc, ← Finset.sum_mul]
      ring

lemma p17Expectation_weighted_sum_sq
    {n : ℕ} {Ω : Type*} [Fintype Ω]
    (P : P17FiniteProbability Ω) (a : Fin n → ℝ)
    (c : Fin n → Ω → ℝ) :
    p17Expectation P (fun ω => (∑ i, a i * c i ω) ^ 2) =
      ∑ i, ∑ j, a i * a j *
        p17Expectation P (fun ω => c i ω * c j ω) := by
  simp only [p17Expectation, pow_two]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro ω hω
  ring

lemma p17RecursiveSum_error_decomposition
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17LimitedPrecisionRecursiveSumRun m Ω) (ω : Ω) :
    p17RecursiveSum run.a (fun k => run.delta k ω) -
        p17ExactSum run.a =
      p17CenteredSummationError run ω +
        p17LimitedPrecisionRemainder run ω := by
  rw [p17RecursiveSum_eq_sum_coefficients]
  unfold p17ExactSum p17CenteredSummationError
    p17LimitedPrecisionRemainder p17CoefficientRemainder
  simp_rw [mul_sub]
  simp only [mul_one]
  repeat' rw [Finset.sum_sub_distrib]
  ring

lemma p17CenteredSummationError_second_moment_bound
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17VarianceRecursiveSumRun m Ω) :
    p17Expectation run.probability
        (fun ω =>
          p17CenteredSummationError
              run.toP17LimitedPrecisionRecursiveSumRun ω ^ 2) ≤
      (∑ i, |run.a i|) ^ 2 *
        p17Gamma m ((p17UnitRoundoff run.p) ^ 2) := by
  let c : Fin (m + 1) → Ω → ℝ := fun i ω =>
    p17RecursiveCoefficient
        (fun k => p17Alpha run.toP17LimitedPrecisionRecursiveSumRun k ω) i - 1
  have hgamma : 0 ≤ p17Gamma m ((p17UnitRoundoff run.p) ^ 2) :=
    (run.alpha_product_covariance_bound 0 0).1.trans
      (run.alpha_product_covariance_bound 0 0).2
  unfold p17CenteredSummationError
  change p17Expectation run.probability
      (fun ω => (∑ i, run.a i * c i ω) ^ 2) ≤ _
  rw [p17Expectation_weighted_sum_sq]
  calc
    (∑ i, ∑ j, run.a i * run.a j *
          p17Expectation run.probability (fun ω => c i ω * c j ω)) ≤
        ∑ i, ∑ j, |run.a i| * |run.a j| *
          p17Gamma m ((p17UnitRoundoff run.p) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hcov := run.alpha_product_covariance_bound i j
      calc
        run.a i * run.a j *
              p17Expectation run.probability (fun ω => c i ω * c j ω) ≤
            |run.a i * run.a j| *
              p17Expectation run.probability (fun ω => c i ω * c j ω) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hcov.1
        _ = |run.a i| * |run.a j| *
              p17Expectation run.probability (fun ω => c i ω * c j ω) := by
          rw [abs_mul]
        _ ≤ |run.a i| * |run.a j| *
              p17Gamma m ((p17UnitRoundoff run.p) ^ 2) :=
          mul_le_mul_of_nonneg_left hcov.2
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (∑ i, |run.a i|) ^ 2 *
          p17Gamma m ((p17UnitRoundoff run.p) ^ 2) := by
      rw [pow_two]
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring

lemma p17LimitedPrecisionRemainder_abs_bound
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17VarianceRecursiveSumRun m Ω) (ω : Ω) :
    |p17LimitedPrecisionRemainder
        run.toP17LimitedPrecisionRecursiveSumRun ω| ≤
      (∑ i, |run.a i|) *
        (p17Gamma m
            (p17UnitRoundoff run.p +
              p17UnitRoundoff (run.p + run.r)) -
          p17Gamma m (p17UnitRoundoff run.p)) := by
  unfold p17LimitedPrecisionRemainder
  calc
    |∑ i, run.a i * p17CoefficientRemainder
          run.toP17LimitedPrecisionRecursiveSumRun i ω| ≤
        ∑ i, |run.a i * p17CoefficientRemainder
          run.toP17LimitedPrecisionRecursiveSumRun i ω| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |run.a i| * |p17CoefficientRemainder
          run.toP17LimitedPrecisionRecursiveSumRun i ω| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul]
    _ ≤ ∑ i, |run.a i| *
          (p17Gamma m
              (p17UnitRoundoff run.p +
                p17UnitRoundoff (run.p + run.r)) -
            p17Gamma m (p17UnitRoundoff run.p)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (run.coefficient_remainder_bound i ω) (abs_nonneg _)
    _ = (∑ i, |run.a i|) *
          (p17Gamma m
              (p17UnitRoundoff run.p +
                p17UnitRoundoff (run.p + run.r)) -
            p17Gamma m (p17UnitRoundoff run.p)) := by
      rw [Finset.sum_mul]

theorem p17_t1_variance_plus_bias_probability_bound
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17VarianceRecursiveSumRun m Ω)
    (hsum : p17ExactSum run.a ≠ 0)
    (lambda : ℝ) (hlambda_pos : 0 < lambda) (hlambda_lt_one : lambda < 1) :
    1 - lambda ≤
      p17EventProb run.probability {ω |
        |p17RecursiveSum run.a (fun k => run.delta k ω) -
            p17ExactSum run.a| / |p17ExactSum run.a| ≤
          p17SummationCondition run.a *
            (Real.sqrt
                (p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda) +
              p17Gamma m
                  (p17UnitRoundoff run.p +
                    p17UnitRoundoff (run.p + run.r)) -
          p17Gamma m (p17UnitRoundoff run.p))} := by
  -- PROOF_START P17-T1-H001
  classical
  cases m with
  | zero =>
      simp [p17RecursiveSum, p17ExactSum, p17Gamma, p17EventProb]
      rw [run.probability.prob_sum]
      linarith
  | succ m =>
      let lp : P17LimitedPrecisionRecursiveSumRun (m + 1) Ω :=
        run.toP17LimitedPrecisionRecursiveSumRun
      let S : ℝ := ∑ i, |run.a i|
      let g : ℝ :=
        p17Gamma (m + 1) ((p17UnitRoundoff run.p) ^ 2)
      let b : ℝ :=
        p17Gamma (m + 1)
            (p17UnitRoundoff run.p +
              p17UnitRoundoff (run.p + run.r)) -
          p17Gamma (m + 1) (p17UnitRoundoff run.p)
      let M : Ω → ℝ := fun ω => p17CenteredSummationError lp ω
      let eta : ℝ := S * Real.sqrt (g / lambda)
      let P : NumStability.FiniteProbability Ω := {
        prob := run.probability.prob
        prob_nonneg := run.probability.prob_nonneg
        prob_sum := run.probability.prob_sum }
      have habs_exact_pos : 0 < |p17ExactSum run.a| := abs_pos.mpr hsum
      have habs_exact_le : |p17ExactSum run.a| ≤ S := by
        dsimp [S, p17ExactSum]
        exact Finset.abs_sum_le_sum_abs _ _
      have hSpos : 0 < S := habs_exact_pos.trans_le habs_exact_le
      have hu : 0 < p17UnitRoundoff run.p := by
        unfold p17UnitRoundoff
        positivity
      have hbase : (1 : ℝ) < 1 + (p17UnitRoundoff run.p) ^ 2 := by
        nlinarith [sq_pos_of_pos hu]
      have hgpos : 0 < g := by
        dsimp [g, p17Gamma]
        have hp : (1 : ℝ) <
            (1 + (p17UnitRoundoff run.p) ^ 2) ^ (m + 1) :=
          one_lt_pow₀ hbase (Nat.succ_ne_zero m)
        linarith
      have heta_pos : 0 < eta := by
        dsimp [eta]
        exact mul_pos hSpos (Real.sqrt_pos.2 (div_pos hgpos hlambda_pos))
      have hM2 :
          p17Expectation run.probability (fun ω => M ω ^ 2) ≤
            S ^ 2 * g := by
        simpa [M, S, g, lp] using
          (p17CenteredSummationError_second_moment_bound run)
      have heta_sq : eta ^ 2 = S ^ 2 * (g / lambda) := by
        dsimp [eta]
        rw [mul_pow, Real.sq_sqrt (div_nonneg hgpos.le hlambda_pos.le)]
      have hmoment :
          P.expectationReal (fun ω => (M ω - 0) ^ 2) / eta ^ 2 ≤
            lambda := by
        dsimp [P, NumStability.FiniteProbability.expectationReal]
        simp only [sub_zero]
        change p17Expectation run.probability (fun ω => M ω ^ 2) /
            eta ^ 2 ≤ lambda
        calc
          p17Expectation run.probability (fun ω => M ω ^ 2) /
                eta ^ 2 ≤
              (S ^ 2 * g) / eta ^ 2 :=
            div_le_div_of_nonneg_right hM2 (sq_nonneg eta)
          _ = lambda := by
            rw [heta_sq]
            field_simp [ne_of_gt hSpos, ne_of_gt hgpos,
              ne_of_gt hlambda_pos]
      have hcentered :=
        NumStability.FiniteProbability.eventProb_abs_sub_le_ge_one_sub_of_second_moment
            P M 0 eta lambda heta_pos hmoment
      have hsubset :
          {ω | |M ω - 0| ≤ eta} ⊆
            {ω |
              |p17RecursiveSum run.a (fun k => run.delta k ω) -
                    p17ExactSum run.a| / |p17ExactSum run.a| ≤
                p17SummationCondition run.a *
                  (Real.sqrt
                      (p17Gamma (m + 1)
                          ((p17UnitRoundoff run.p) ^ 2) / lambda) +
                    p17Gamma (m + 1)
                        (p17UnitRoundoff run.p +
                          p17UnitRoundoff (run.p + run.r)) -
                      p17Gamma (m + 1)
                        (p17UnitRoundoff run.p))} := by
        intro ω hω
        have hdecomp := p17RecursiveSum_error_decomposition lp ω
        have hrem := p17LimitedPrecisionRemainder_abs_bound run ω
        have hcenter : |M ω| ≤ eta := by simpa using hω
        have herr :
            |p17RecursiveSum run.a (fun k => run.delta k ω) -
                p17ExactSum run.a| ≤
              S * (Real.sqrt (g / lambda) + b) := by
          calc
            |p17RecursiveSum run.a (fun k => run.delta k ω) -
                  p17ExactSum run.a| =
                |M ω + p17LimitedPrecisionRemainder lp ω| := by
              rw [hdecomp]
            _ ≤ |M ω| + |p17LimitedPrecisionRemainder lp ω| :=
              abs_add_le _ _
            _ ≤ eta + S * b := add_le_add hcenter (by simpa [S, b, lp] using hrem)
            _ = S * (Real.sqrt (g / lambda) + b) := by
              dsimp [eta]
              ring
        calc
          |p17RecursiveSum run.a (fun k => run.delta k ω) -
                p17ExactSum run.a| / |p17ExactSum run.a| ≤
              (S * (Real.sqrt (g / lambda) + b)) /
                |p17ExactSum run.a| :=
            div_le_div_of_nonneg_right herr (abs_nonneg _)
          _ = p17SummationCondition run.a *
                (Real.sqrt
                    (p17Gamma (m + 1)
                        ((p17UnitRoundoff run.p) ^ 2) / lambda) +
                  p17Gamma (m + 1)
                      (p17UnitRoundoff run.p +
                        p17UnitRoundoff (run.p + run.r)) -
                    p17Gamma (m + 1)
                      (p17UnitRoundoff run.p)) := by
            dsimp [S, g, b, p17SummationCondition]
            rw [div_eq_mul_inv]
            ring
      have hresult := hcentered.trans
        (NumStability.FiniteProbability.eventProb_mono P hsubset)
      simpa [P, NumStability.FiniteProbability.eventProb, p17EventProb] using hresult

end HighamBench
