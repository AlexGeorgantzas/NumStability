import HighamBench.P17Definitions

namespace HighamBench

open scoped BigOperators

lemma p17RecursiveSum_eq_sum_coeff
    {m : ℕ} (a : Fin (m + 1) → ℝ) (error : Fin m → ℝ) :
    p17RecursiveSum a error =
      ∑ i, a i * p17RecursiveCoefficient error i := by
  induction m with
  | zero =>
      simp [p17RecursiveSum, p17RecursiveCoefficient]
  | succ m ih =>
      rw [p17RecursiveSum, Fin.foldl_succ_last]
      change
        (p17RecursiveSum (fun i : Fin (m + 1) => a i.castSucc)
              (fun k : Fin m => error k.castSucc) + a (Fin.last (m + 1))) *
            (1 + error (Fin.last m)) = _
      rw [ih]
      have hcoeff : ∀ i : Fin (m + 1),
          p17RecursiveCoefficient error i.castSucc =
            p17RecursiveCoefficient (fun k : Fin m => error k.castSucc) i *
              (1 + error (Fin.last m)) := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [p17RecursiveCoefficient, Fin.prod_univ_castSucc]
        · simp [p17RecursiveCoefficient, p17SuffixErrorProduct]
      have hlast :
          p17RecursiveCoefficient error (Fin.last (m + 1)) =
            1 + error (Fin.last m) := by
        change p17SuffixErrorProduct (m + 1) error (Fin.last m) = _
        simp [p17SuffixErrorProduct]
      conv_rhs => rw [Fin.sum_univ_castSucc]
      simp_rw [hcoeff]
      rw [hlast]
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul]
      ring

lemma p17RecursiveSum_error_decomposition
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17LimitedPrecisionRecursiveSumRun m Ω) (ω : Ω) :
    p17RecursiveSum run.a (fun k => run.delta k ω) - p17ExactSum run.a =
      p17CenteredSummationError run ω +
        p17LimitedPrecisionRemainder run ω := by
  rw [p17RecursiveSum_eq_sum_coeff]
  simp only [p17ExactSum, p17CenteredSummationError,
    p17LimitedPrecisionRemainder, p17CoefficientRemainder]
  rw [← Finset.sum_sub_distrib]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma p17LimitedPrecisionRemainder_abs_le
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17VarianceRecursiveSumRun m Ω) (ω : Ω) :
    |p17LimitedPrecisionRemainder
        run.toP17LimitedPrecisionRecursiveSumRun ω| ≤
      (∑ i, |run.a i|) *
        (p17Gamma m
            (p17UnitRoundoff run.p + p17UnitRoundoff (run.p + run.r)) -
          p17Gamma m (p17UnitRoundoff run.p)) := by
  let B :=
    p17Gamma m
        (p17UnitRoundoff run.p + p17UnitRoundoff (run.p + run.r)) -
      p17Gamma m (p17UnitRoundoff run.p)
  calc
    |p17LimitedPrecisionRemainder
        run.toP17LimitedPrecisionRecursiveSumRun ω| =
        |∑ i, run.a i *
          p17CoefficientRemainder
            run.toP17LimitedPrecisionRecursiveSumRun i ω| := by
              rfl
    _ ≤ ∑ i, |run.a i *
          p17CoefficientRemainder
            run.toP17LimitedPrecisionRecursiveSumRun i ω| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |run.a i| * B := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (run.coefficient_remainder_bound i ω) (abs_nonneg _)
    _ = (∑ i, |run.a i|) * B := by
      rw [Finset.sum_mul]

lemma p17CenteredSummationError_second_moment_le
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17VarianceRecursiveSumRun m Ω) :
    p17Expectation run.probability (fun ω =>
        (p17CenteredSummationError
          run.toP17LimitedPrecisionRecursiveSumRun ω) ^ 2) ≤
      (∑ i, |run.a i|) ^ 2 *
        p17Gamma m ((p17UnitRoundoff run.p) ^ 2) := by
  let x : Fin (m + 1) → Ω → ℝ := fun i ω =>
    p17RecursiveCoefficient
        (fun k => p17Alpha
          run.toP17LimitedPrecisionRecursiveSumRun k ω) i - 1
  let G := p17Gamma m ((p17UnitRoundoff run.p) ^ 2)
  have hcov (i j : Fin (m + 1)) :
      0 ≤ p17Expectation run.probability (fun ω => x i ω * x j ω) ∧
        p17Expectation run.probability (fun ω => x i ω * x j ω) ≤ G := by
    exact run.alpha_product_covariance_bound i j
  calc
    p17Expectation run.probability (fun ω =>
        (p17CenteredSummationError
          run.toP17LimitedPrecisionRecursiveSumRun ω) ^ 2) =
      ∑ i, ∑ j,
        run.a i * run.a j *
          p17Expectation run.probability (fun ω => x i ω * x j ω) := by
            simp only [p17Expectation, p17CenteredSummationError,
              x, pow_two]
            simp_rw [Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro ω hω
            ring
    _ ≤ ∑ i, ∑ j, |run.a i| * |run.a j| * G := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rcases hcov i j with ⟨hc_nonneg, hc_le⟩
      calc
        run.a i * run.a j *
            p17Expectation run.probability (fun ω => x i ω * x j ω) ≤
          |run.a i * run.a j| *
            p17Expectation run.probability (fun ω => x i ω * x j ω) := by
              exact mul_le_mul_of_nonneg_right (le_abs_self _) hc_nonneg
        _ = |run.a i| * |run.a j| *
            p17Expectation run.probability (fun ω => x i ω * x j ω) := by
              rw [abs_mul]
        _ ≤ |run.a i| * |run.a j| * G := by
              exact mul_le_mul_of_nonneg_left hc_le
                (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (∑ i, |run.a i|) ^ 2 * G := by
      rw [pow_two]
      calc
        (∑ i, ∑ j, |run.a i| * |run.a j| * G) =
            ∑ i, (|run.a i| * (∑ j, |run.a j|)) * G := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← Finset.sum_mul, ← Finset.mul_sum]
        _ = (∑ i, |run.a i|) * (∑ j, |run.a j|) * G := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]

lemma p17EventProb_sq_le_of_second_moment_le
    {Ω : Type*} [Fintype Ω]
    (P : P17FiniteProbability Ω) (X : Ω → ℝ)
    (C lambda : ℝ) (hC : 0 < C) (hlambda : 0 < lambda)
    (hsecond : p17Expectation P (fun ω => (X ω) ^ 2) ≤ C) :
    1 - lambda ≤
      p17EventProb P {ω | (X ω) ^ 2 ≤ C / lambda} := by
  classical
  let Q := C / lambda
  have hQ : 0 < Q := div_pos hC hlambda
  let good : Set Ω := {ω | (X ω) ^ 2 ≤ Q}
  let bad : Set Ω := {ω | Q < (X ω) ^ 2}
  have hpartition :
      p17EventProb P good + p17EventProb P bad = 1 := by
    rw [← P.prob_sum]
    simp only [p17EventProb]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases h : (X ω) ^ 2 ≤ Q
    · have hnlt : ¬ Q < (X ω) ^ 2 := not_lt_of_ge h
      simp [good, bad, h, hnlt]
    · have hlt : Q < (X ω) ^ 2 := lt_of_not_ge h
      simp [good, bad, h, hlt]
  have hmarkov :
      Q * p17EventProb P bad ≤
        p17Expectation P (fun ω => (X ω) ^ 2) := by
    simp only [p17EventProb, p17Expectation]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ω hω
    by_cases h : Q < (X ω) ^ 2
    · simp only [bad, Set.mem_setOf_eq, h, if_true]
      simpa [mul_comm] using
        (mul_le_mul_of_nonneg_right (le_of_lt h) (P.prob_nonneg ω))
    · simp only [bad, Set.mem_setOf_eq, h, if_false, mul_zero]
      exact mul_nonneg (P.prob_nonneg ω) (sq_nonneg (X ω))
  have hQlambda : Q * lambda = C := by
    dsimp [Q]
    field_simp
  have hbad : p17EventProb P bad ≤ lambda := by
    have hprod : Q * p17EventProb P bad ≤ Q * lambda := calc
      Q * p17EventProb P bad ≤
          p17Expectation P (fun ω => (X ω) ^ 2) := hmarkov
      _ ≤ C := hsecond
      _ = Q * lambda := hQlambda.symm
    nlinarith
  change 1 - lambda ≤ p17EventProb P good
  linarith

lemma p17EventProb_mono
    {Ω : Type*} [Fintype Ω] (P : P17FiniteProbability Ω)
    {E F : Set Ω} (hEF : E ⊆ F) :
    p17EventProb P E ≤ p17EventProb P F := by
  classical
  simp only [p17EventProb]
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hE : ω ∈ E
  · have hF : ω ∈ F := hEF hE
    simp [hE, hF]
  · simp only [hE, if_false]
    split <;> simp [P.prob_nonneg]

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
      simp [p17EventProb, p17RecursiveSum, p17ExactSum, p17Gamma]
      rw [run.probability.prob_sum]
      linarith
  | succ m =>
      let S : ℝ := ∑ i, |run.a i|
      have hden : 0 < |p17ExactSum run.a| := abs_pos.mpr hsum
      have htriangle : |p17ExactSum run.a| ≤ S := by
        dsimp [S, p17ExactSum]
        exact Finset.abs_sum_le_sum_abs _ _
      have hS : 0 < S := lt_of_lt_of_le hden htriangle
      let G : ℝ :=
        p17Gamma (m + 1) ((p17UnitRoundoff run.p) ^ 2)
      have hu : 0 < p17UnitRoundoff run.p := by
        simp only [p17UnitRoundoff]
        positivity
      have hbase :
          (1 : ℝ) < 1 + (p17UnitRoundoff run.p) ^ 2 := by
        nlinarith [sq_pos_of_pos hu]
      have hpow :
          (1 : ℝ) <
            (1 + (p17UnitRoundoff run.p) ^ 2) ^ (m + 1) :=
        one_lt_pow₀ hbase (Nat.succ_ne_zero m)
      have hG : 0 < G := by
        dsimp [G, p17Gamma]
        linarith
      let M : Ω → ℝ := fun ω =>
        p17CenteredSummationError
          run.toP17LimitedPrecisionRecursiveSumRun ω
      let C : ℝ := S ^ 2 * G
      have hC : 0 < C := by
        dsimp [C]
        positivity
      have hsecond :
          p17Expectation run.probability (fun ω => (M ω) ^ 2) ≤ C := by
        simpa [M, C, S, G] using
          (p17CenteredSummationError_second_moment_le run)
      have hprob :
          1 - lambda ≤
            p17EventProb run.probability
              {ω | (M ω) ^ 2 ≤ C / lambda} :=
        p17EventProb_sq_le_of_second_moment_le
          run.probability M C lambda hC hlambda_pos hsecond
      apply le_trans hprob
      apply p17EventProb_mono
      intro ω hω
      change (M ω) ^ 2 ≤ C / lambda at hω
      have hq : 0 ≤ G / lambda :=
        (div_nonneg (le_of_lt hG) (le_of_lt hlambda_pos))
      have hsqrt_sq : (Real.sqrt (G / lambda)) ^ 2 = G / lambda :=
        Real.sq_sqrt hq
      have hCdiv : C / lambda = S ^ 2 * (G / lambda) := by
        dsimp [C]
        field_simp
        <;> ring
      have hM : |M ω| ≤ S * Real.sqrt (G / lambda) := by
        have hright : 0 ≤ S * Real.sqrt (G / lambda) :=
          mul_nonneg (le_of_lt hS) (Real.sqrt_nonneg _)
        rw [hCdiv] at hω
        nlinarith [sq_abs (M ω)]
      let B : ℝ :=
        p17Gamma (m + 1)
            (p17UnitRoundoff run.p +
              p17UnitRoundoff (run.p + run.r)) -
          p17Gamma (m + 1) (p17UnitRoundoff run.p)
      have hR :
          |p17LimitedPrecisionRemainder
              run.toP17LimitedPrecisionRecursiveSumRun ω| ≤ S * B := by
        simpa [S, B] using
          (p17LimitedPrecisionRemainder_abs_le run ω)
      have herr :
          |p17RecursiveSum run.a (fun k => run.delta k ω) -
              p17ExactSum run.a| ≤
            S * (Real.sqrt (G / lambda) + B) := by
        rw [p17RecursiveSum_error_decomposition
          run.toP17LimitedPrecisionRecursiveSumRun ω]
        calc
          |M ω + p17LimitedPrecisionRemainder
              run.toP17LimitedPrecisionRecursiveSumRun ω| ≤
              |M ω| +
                |p17LimitedPrecisionRemainder
                  run.toP17LimitedPrecisionRecursiveSumRun ω| :=
            abs_add_le _ _
          _ ≤ S * Real.sqrt (G / lambda) + S * B :=
            add_le_add hM hR
          _ = S * (Real.sqrt (G / lambda) + B) := by ring
      have hdiv := div_le_div_of_nonneg_right herr (le_of_lt hden)
      have hfinal :
        |p17RecursiveSum run.a (fun k => run.delta k ω) -
            p17ExactSum run.a| / |p17ExactSum run.a| ≤
          (S / |p17ExactSum run.a|) *
            (Real.sqrt (G / lambda) + B) := by
        calc
          |p17RecursiveSum run.a (fun k => run.delta k ω) -
              p17ExactSum run.a| / |p17ExactSum run.a| ≤
              S * (Real.sqrt (G / lambda) + B) /
                |p17ExactSum run.a| := hdiv
          _ = (S / |p17ExactSum run.a|) *
                (Real.sqrt (G / lambda) + B) := by ring
      simpa [Set.mem_setOf_eq, p17SummationCondition, S, G, B,
        sub_eq_add_neg, add_assoc] using hfinal

end HighamBench
