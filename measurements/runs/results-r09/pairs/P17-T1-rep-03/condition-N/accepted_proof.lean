import HighamBench.P17Definitions

namespace HighamBench

open scoped BigOperators

lemma p17RecursiveCoefficient_castSucc
    {m : ℕ} (e : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    p17RecursiveCoefficient e i.castSucc =
      p17RecursiveCoefficient (fun k : Fin m ↦ e k.castSucc) i *
        (1 + e (Fin.last m)) := by
  cases i using Fin.cases with
  | zero =>
      simp [p17RecursiveCoefficient, Fin.prod_univ_castSucc]
  | succ i =>
      simp [p17RecursiveCoefficient, p17SuffixErrorProduct]

lemma p17RecursiveCoefficient_last
    {m : ℕ} (e : Fin (m + 1) → ℝ) :
    p17RecursiveCoefficient e (Fin.last (m + 1)) =
      1 + e (Fin.last m) := by
  unfold p17RecursiveCoefficient
  rw [show Fin.last (m + 1) = (Fin.last m).succ by
    exact (Fin.succ_last m).symm, Fin.cases_succ]
  rw [p17SuffixErrorProduct]
  simp only [Fin.lastCases_last]

lemma p17RecursiveSum_eq_sum_coefficient
    {m : ℕ} (a : Fin (m + 1) → ℝ) (e : Fin m → ℝ) :
    p17RecursiveSum a e =
      ∑ i : Fin (m + 1), a i * p17RecursiveCoefficient e i := by
  induction m with
  | zero =>
      simp [p17RecursiveSum, p17RecursiveCoefficient]
  | succ m ih =>
      rw [p17RecursiveSum, Fin.foldl_succ_last]
      change
        (p17RecursiveSum (fun i : Fin (m + 1) ↦ a i.castSucc)
            (fun k : Fin m ↦ e k.castSucc) + a (Fin.last (m + 1))) *
              (1 + e (Fin.last m)) = _
      rw [ih]
      conv_rhs => rw [Fin.sum_univ_castSucc]
      simp_rw [p17RecursiveCoefficient_castSucc]
      rw [p17RecursiveCoefficient_last]
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul]
      ring

lemma p17RecursiveSum_error_decomposition
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17LimitedPrecisionRecursiveSumRun m Ω) (ω : Ω) :
    p17RecursiveSum run.a (fun k ↦ run.delta k ω) - p17ExactSum run.a =
      p17CenteredSummationError run ω +
        p17LimitedPrecisionRemainder run ω := by
  rw [p17RecursiveSum_eq_sum_coefficient]
  simp only [p17ExactSum, p17CenteredSummationError,
    p17LimitedPrecisionRemainder, p17CoefficientRemainder]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma p17CenteredSummationError_second_moment
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17VarianceRecursiveSumRun m Ω) :
    p17Expectation run.probability
        (fun ω ↦ p17CenteredSummationError
          run.toP17LimitedPrecisionRecursiveSumRun ω ^ 2) =
      ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        run.a i * run.a j *
          p17Expectation run.probability (fun ω ↦
            (p17RecursiveCoefficient
                (fun k ↦ p17Alpha
                  run.toP17LimitedPrecisionRecursiveSumRun k ω) i - 1) *
              (p17RecursiveCoefficient
                (fun k ↦ p17Alpha
                  run.toP17LimitedPrecisionRecursiveSumRun k ω) j - 1)) := by
  simp only [p17Expectation, p17CenteredSummationError, pow_two]
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

lemma p17CenteredSummationError_second_moment_le
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17VarianceRecursiveSumRun m Ω) :
    p17Expectation run.probability
        (fun ω ↦ p17CenteredSummationError
          run.toP17LimitedPrecisionRecursiveSumRun ω ^ 2) ≤
      (∑ i : Fin (m + 1), |run.a i|) ^ 2 *
        p17Gamma m ((p17UnitRoundoff run.p) ^ 2) := by
  rw [p17CenteredSummationError_second_moment]
  calc
    (∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        run.a i * run.a j *
          p17Expectation run.probability (fun ω ↦
            (p17RecursiveCoefficient
                (fun k ↦ p17Alpha
                  run.toP17LimitedPrecisionRecursiveSumRun k ω) i - 1) *
              (p17RecursiveCoefficient
                (fun k ↦ p17Alpha
                  run.toP17LimitedPrecisionRecursiveSumRun k ω) j - 1))) ≤
      ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        |run.a i| * |run.a j| *
          p17Gamma m ((p17UnitRoundoff run.p) ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        let C := p17Expectation run.probability (fun ω ↦
          (p17RecursiveCoefficient
              (fun k ↦ p17Alpha
                run.toP17LimitedPrecisionRecursiveSumRun k ω) i - 1) *
            (p17RecursiveCoefficient
              (fun k ↦ p17Alpha
                run.toP17LimitedPrecisionRecursiveSumRun k ω) j - 1))
        have hC := run.alpha_product_covariance_bound i j
        change run.a i * run.a j * C ≤
          |run.a i| * |run.a j| *
            p17Gamma m ((p17UnitRoundoff run.p) ^ 2)
        calc
          run.a i * run.a j * C ≤ |run.a i * run.a j| * C :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hC.1
          _ = |run.a i| * |run.a j| * C := by rw [abs_mul]
          _ ≤ |run.a i| * |run.a j| *
              p17Gamma m ((p17UnitRoundoff run.p) ^ 2) :=
            mul_le_mul_of_nonneg_left hC.2
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (∑ i : Fin (m + 1), |run.a i|) ^ 2 *
          p17Gamma m ((p17UnitRoundoff run.p) ^ 2) := by
      simp_rw [mul_assoc]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      rw [← Finset.sum_mul]
      rw [pow_two]
      ring

lemma p17LimitedPrecisionRemainder_abs_le
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17VarianceRecursiveSumRun m Ω) (ω : Ω) :
    |p17LimitedPrecisionRemainder
        run.toP17LimitedPrecisionRecursiveSumRun ω| ≤
      (∑ i : Fin (m + 1), |run.a i|) *
        (p17Gamma m
            (p17UnitRoundoff run.p +
              p17UnitRoundoff (run.p + run.r)) -
          p17Gamma m (p17UnitRoundoff run.p)) := by
  unfold p17LimitedPrecisionRemainder
  calc
    |∑ i : Fin (m + 1),
        run.a i *
          p17CoefficientRemainder
            run.toP17LimitedPrecisionRecursiveSumRun i ω| ≤
      ∑ i : Fin (m + 1),
        |run.a i *
          p17CoefficientRemainder
            run.toP17LimitedPrecisionRecursiveSumRun i ω| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (m + 1), |run.a i| *
        (p17Gamma m
            (p17UnitRoundoff run.p +
              p17UnitRoundoff (run.p + run.r)) -
          p17Gamma m (p17UnitRoundoff run.p)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (run.coefficient_remainder_bound i ω) (abs_nonneg _)
    _ = (∑ i : Fin (m + 1), |run.a i|) *
        (p17Gamma m
            (p17UnitRoundoff run.p +
              p17UnitRoundoff (run.p + run.r)) -
          p17Gamma m (p17UnitRoundoff run.p)) := by
      rw [Finset.sum_mul]

lemma p17EventProb_abs_le_of_second_moment
    {Ω : Type*} [Fintype Ω]
    (P : P17FiniteProbability Ω) (X : Ω → ℝ)
    (t lambda : ℝ) (ht : 0 < t)
    (hsecond : p17Expectation P (fun ω ↦ X ω ^ 2) ≤
      lambda * t ^ 2) :
    1 - lambda ≤ p17EventProb P {ω | |X ω| ≤ t} := by
  classical
  let bad : ℝ := ∑ ω, if |X ω| ≤ t then 0 else P.prob ω
  have hbad_moment : bad * t ^ 2 ≤
      p17Expectation P (fun ω ↦ X ω ^ 2) := by
    calc
      bad * t ^ 2 =
          ∑ ω, (if |X ω| ≤ t then 0 else P.prob ω) * t ^ 2 := by
            dsimp [bad]
            rw [Finset.sum_mul]
      _ ≤ ∑ ω, P.prob ω * X ω ^ 2 := by
        apply Finset.sum_le_sum
        intro ω hω
        by_cases hgood : |X ω| ≤ t
        · simp only [hgood, if_pos]
          simpa using mul_nonneg (P.prob_nonneg ω) (sq_nonneg (X ω))
        · simp only [hgood, if_neg]
          apply mul_le_mul_of_nonneg_left _ (P.prob_nonneg ω)
          rw [← sq_abs (X ω)]
          exact (sq_le_sq₀ (le_of_lt ht) (abs_nonneg _)).2
            (le_of_not_ge hgood)
      _ = p17Expectation P (fun ω ↦ X ω ^ 2) := by
        rfl
  have hbad : bad ≤ lambda := by
    apply le_of_mul_le_mul_right (hbad_moment.trans hsecond)
    exact sq_pos_of_pos ht
  have hsplit : p17EventProb P {ω | |X ω| ≤ t} + bad = 1 := by
    rw [← P.prob_sum]
    simp only [p17EventProb, bad]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases hgood : |X ω| ≤ t <;> simp [hgood]
  linarith

lemma p17EventProb_mono
    {Ω : Type*} [Fintype Ω]
    (P : P17FiniteProbability Ω) {E F : Set Ω} (hEF : E ⊆ F) :
    p17EventProb P E ≤ p17EventProb P F := by
  classical
  unfold p17EventProb
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hE : ω ∈ E
  · simp only [hE, if_pos]
    have hF := hEF hE
    simp only [hF, if_pos]
    exact le_rfl
  · simp only [hE, if_neg]
    by_cases hF : ω ∈ F
    · simp only [hF, if_pos]
      exact P.prob_nonneg ω
    · simp [hF]

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
  let S : ℝ := ∑ i : Fin (m + 1), |run.a i|
  let G : ℝ := p17Gamma m ((p17UnitRoundoff run.p) ^ 2)
  let B : ℝ :=
    p17Gamma m
        (p17UnitRoundoff run.p + p17UnitRoundoff (run.p + run.r)) -
      p17Gamma m (p17UnitRoundoff run.p)
  let M : Ω → ℝ := fun ω ↦
    p17CenteredSummationError
      run.toP17LimitedPrecisionRecursiveSumRun ω
  have hS : 0 < S := by
    have habs : |p17ExactSum run.a| ≤ S := by
      simpa only [p17ExactSum, S] using
        (Finset.abs_sum_le_sum_abs run.a Finset.univ)
    exact lt_of_lt_of_le (abs_pos.mpr hsum) habs
  have hG : 0 ≤ G := by
    have hcov := run.alpha_product_covariance_bound
      (0 : Fin (m + 1)) (0 : Fin (m + 1))
    exact hcov.1.trans hcov.2
  have hmoment :
      p17Expectation run.probability (fun ω ↦ M ω ^ 2) ≤ S ^ 2 * G := by
    simpa only [M, S, G] using
      (p17CenteredSummationError_second_moment_le run)
  have hcenter :
      1 - lambda ≤
        p17EventProb run.probability
          {ω | |M ω| ≤ S * Real.sqrt (G / lambda)} := by
    rcases hG.eq_or_lt with hGzero | hGpos
    · have hexp_nonneg :
          0 ≤ p17Expectation run.probability (fun ω ↦ M ω ^ 2) := by
        unfold p17Expectation
        exact Finset.sum_nonneg fun ω hω ↦
          mul_nonneg (run.probability.prob_nonneg ω) (sq_nonneg _)
      have hexp_zero :
          p17Expectation run.probability (fun ω ↦ M ω ^ 2) = 0 := by
        apply le_antisymm
        · calc
            p17Expectation run.probability (fun ω ↦ M ω ^ 2) ≤ S ^ 2 * G :=
              hmoment
            _ = 0 := by rw [← hGzero, mul_zero]
        · exact hexp_nonneg
      have hterm_zero : ∀ ω, run.probability.prob ω * M ω ^ 2 = 0 := by
        intro ω
        have hsum_zero :
            ∑ ω, run.probability.prob ω * M ω ^ 2 = 0 := by
          exact hexp_zero
        exact (Finset.sum_eq_zero_iff_of_nonneg
          (fun x hx ↦ mul_nonneg (run.probability.prob_nonneg x)
            (sq_nonneg _))).1 hsum_zero ω (Finset.mem_univ ω)
      have hall : p17EventProb run.probability
          {ω | |M ω| ≤ S * Real.sqrt (G / lambda)} = 1 := by
        rw [← run.probability.prob_sum]
        unfold p17EventProb
        apply Finset.sum_congr rfl
        intro ω hω
        by_cases hgood : |M ω| ≤ S * Real.sqrt (G / lambda)
        · simp [hgood]
        · have hthreshold : S * Real.sqrt (G / lambda) = 0 := by
            rw [← hGzero]
            norm_num
          have hM : M ω ≠ 0 := by
            intro hMz
            apply hgood
            rw [hthreshold, hMz, abs_zero]
          have hpzero : run.probability.prob ω = 0 := by
            rcases mul_eq_zero.mp (hterm_zero ω) with hp | hsq
            · exact hp
            · exact (hM (sq_eq_zero_iff.mp hsq)).elim
          simp [hgood, hpzero]
      rw [hall]
      linarith
    · have hratio : 0 < G / lambda := div_pos hGpos hlambda_pos
      have ht : 0 < S * Real.sqrt (G / lambda) :=
        mul_pos hS (Real.sqrt_pos.2 hratio)
      apply p17EventProb_abs_le_of_second_moment
        run.probability M (S * Real.sqrt (G / lambda)) lambda ht
      calc
        p17Expectation run.probability (fun ω ↦ M ω ^ 2) ≤ S ^ 2 * G :=
          hmoment
        _ = lambda * (S * Real.sqrt (G / lambda)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (le_of_lt hratio)]
          field_simp
  calc
    1 - lambda ≤
        p17EventProb run.probability
          {ω | |M ω| ≤ S * Real.sqrt (G / lambda)} := hcenter
    _ ≤ p17EventProb run.probability {ω |
        |p17RecursiveSum run.a (fun k => run.delta k ω) -
            p17ExactSum run.a| / |p17ExactSum run.a| ≤
          p17SummationCondition run.a *
            (Real.sqrt
                (p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda) +
              p17Gamma m
                  (p17UnitRoundoff run.p +
                    p17UnitRoundoff (run.p + run.r)) -
                p17Gamma m (p17UnitRoundoff run.p))} := by
      apply p17EventProb_mono
      intro ω hcentered
      change |M ω| ≤ S * Real.sqrt (G / lambda) at hcentered
      have hdecomp := p17RecursiveSum_error_decomposition
        run.toP17LimitedPrecisionRecursiveSumRun ω
      have hbias :
          |p17LimitedPrecisionRemainder
            run.toP17LimitedPrecisionRecursiveSumRun ω| ≤ S * B := by
        simpa only [S, B] using p17LimitedPrecisionRemainder_abs_le run ω
      have herr :
          |p17RecursiveSum run.a (fun k ↦ run.delta k ω) -
              p17ExactSum run.a| ≤
            S * (Real.sqrt (G / lambda) + B) := by
        calc
          |p17RecursiveSum run.a (fun k ↦ run.delta k ω) -
              p17ExactSum run.a| =
              |M ω + p17LimitedPrecisionRemainder
                run.toP17LimitedPrecisionRecursiveSumRun ω| := by
                rw [hdecomp]
          _ ≤ |M ω| +
              |p17LimitedPrecisionRemainder
                run.toP17LimitedPrecisionRecursiveSumRun ω| := abs_add_le _ _
          _ ≤ S * Real.sqrt (G / lambda) + S * B :=
            add_le_add hcentered hbias
          _ = S * (Real.sqrt (G / lambda) + B) := by ring
      have hdenom : 0 < |p17ExactSum run.a| := abs_pos.mpr hsum
      have hdiv := (div_le_div_iff_of_pos_right hdenom).2 herr
      simp only [Set.mem_setOf_eq, p17SummationCondition]
      dsimp only [S, G, B] at hdiv
      convert hdiv using 1 <;> ring

end HighamBench
