import HighamBench.P17Definitions
import NumStability.Analysis.FiniteProbability

namespace HighamBench

open scoped BigOperators

lemma p17_suffixErrorProduct_castSucc
    {m : ℕ} (error : Fin (m + 1) → ℝ) (i : Fin m) :
    p17SuffixErrorProduct (m + 1) error i.castSucc =
      p17SuffixErrorProduct m (fun k => error k.castSucc) i *
        (1 + error (Fin.last m)) := by
  rw [p17SuffixErrorProduct]
  change Fin.lastCases (motive := fun _ => ℝ) (1 + error (Fin.last m))
      (fun i => p17SuffixErrorProduct m (fun j => error j.castSucc) i *
        (1 + error (Fin.last m))) i.castSucc = _
  rw [Fin.lastCases_castSucc]

lemma p17_recursiveCoefficient_castSucc
    {m : ℕ} (error : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    p17RecursiveCoefficient error i.castSucc =
      p17RecursiveCoefficient (fun k : Fin m => error k.castSucc) i *
        (1 + error (Fin.last m)) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · change (∏ k : Fin (m + 1), (1 + error k)) =
        (∏ k : Fin m, (1 + error k.castSucc)) *
          (1 + error (Fin.last m))
    rw [Fin.prod_univ_castSucc]
  · change p17SuffixErrorProduct (m + 1) error j.castSucc = _
    exact p17_suffixErrorProduct_castSucc error j

lemma p17_recursiveCoefficient_last
    {m : ℕ} (error : Fin (m + 1) → ℝ) :
    p17RecursiveCoefficient error (Fin.last (m + 1)) =
      1 + error (Fin.last m) := by
  simp only [p17RecursiveCoefficient]
  change p17SuffixErrorProduct (m + 1) error (Fin.last m) = _
  rw [p17SuffixErrorProduct]
  change Fin.lastCases (motive := fun _ => ℝ) (1 + error (Fin.last m))
      (fun i => p17SuffixErrorProduct m (fun j => error j.castSucc) i *
        (1 + error (Fin.last m))) (Fin.last m) = _
  rw [Fin.lastCases_last]

lemma p17_recursiveSum_eq_coefficient_sum :
    ∀ {m : ℕ} (a : Fin (m + 1) → ℝ) (error : Fin m → ℝ),
      p17RecursiveSum a error =
        ∑ i, a i * p17RecursiveCoefficient error i := by
  intro m
  induction m with
  | zero =>
      intro a error
      rw [p17RecursiveSum, Fin.foldl_zero]
      rw [show (∑ i : Fin 1, a i * p17RecursiveCoefficient error i) =
          a 0 * p17RecursiveCoefficient error 0 by
            rw [Fin.sum_univ_succ]
            simp]
      simp [p17RecursiveCoefficient]
  | succ m ih =>
      intro a error
      rw [p17RecursiveSum, Fin.foldl_succ_last]
      change
        (p17RecursiveSum (fun i : Fin (m + 1) => a i.castSucc)
            (fun k : Fin m => error k.castSucc) + a (Fin.last (m + 1))) *
              (1 + error (Fin.last m)) = _
      rw [Fin.sum_univ_castSucc]
      rw [ih]
      simp_rw [p17_recursiveCoefficient_castSucc]
      rw [p17_recursiveCoefficient_last]
      rw [add_mul]
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

lemma p17_recursive_error_decomposition
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17VarianceRecursiveSumRun m Ω) (ω : Ω) :
    p17RecursiveSum run.a (fun k => run.delta k ω) - p17ExactSum run.a =
      p17CenteredSummationError run.toP17LimitedPrecisionRecursiveSumRun ω +
        p17LimitedPrecisionRemainder
          run.toP17LimitedPrecisionRecursiveSumRun ω := by
  rw [p17_recursiveSum_eq_coefficient_sum]
  unfold p17ExactSum p17CenteredSummationError
    p17LimitedPrecisionRemainder p17CoefficientRemainder
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma p17_remainder_abs_le
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17VarianceRecursiveSumRun m Ω) (ω : Ω) :
    |p17LimitedPrecisionRemainder
        run.toP17LimitedPrecisionRecursiveSumRun ω| ≤
      (∑ i, |run.a i|) *
        (p17Gamma m
            (p17UnitRoundoff run.p + p17UnitRoundoff (run.p + run.r)) -
          p17Gamma m (p17UnitRoundoff run.p)) := by
  unfold p17LimitedPrecisionRemainder
  calc
    |∑ i, run.a i *
        p17CoefficientRemainder
          run.toP17LimitedPrecisionRecursiveSumRun i ω| ≤
        ∑ i, |run.a i *
          p17CoefficientRemainder
            run.toP17LimitedPrecisionRecursiveSumRun i ω| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |run.a i| *
        |p17CoefficientRemainder
          run.toP17LimitedPrecisionRecursiveSumRun i ω| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul]
    _ ≤ ∑ i, |run.a i| *
        (p17Gamma m
            (p17UnitRoundoff run.p + p17UnitRoundoff (run.p + run.r)) -
          p17Gamma m (p17UnitRoundoff run.p)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (run.coefficient_remainder_bound i ω) (abs_nonneg _)
    _ = (∑ i, |run.a i|) *
        (p17Gamma m
            (p17UnitRoundoff run.p + p17UnitRoundoff (run.p + run.r)) -
          p17Gamma m (p17UnitRoundoff run.p)) := by
      rw [Finset.sum_mul]

lemma p17_sum_sq_eq_double_sum
    {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∑ i, f i) ^ 2 = ∑ i, ∑ j, f i * f j := by
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]

lemma p17_centered_second_moment_le
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17VarianceRecursiveSumRun m Ω) :
    p17Expectation run.probability (fun ω =>
        (p17CenteredSummationError
          run.toP17LimitedPrecisionRecursiveSumRun ω) ^ 2) ≤
      (∑ i, |run.a i|) ^ 2 *
        p17Gamma m ((p17UnitRoundoff run.p) ^ 2) := by
  let C : Fin (m + 1) → Ω → ℝ := fun i ω =>
    p17RecursiveCoefficient
        (fun k => p17Alpha
          run.toP17LimitedPrecisionRecursiveSumRun k ω) i - 1
  have hexpand :
      p17Expectation run.probability (fun ω =>
          (p17CenteredSummationError
            run.toP17LimitedPrecisionRecursiveSumRun ω) ^ 2) =
        ∑ i, ∑ j, run.a i * run.a j *
          p17Expectation run.probability (fun ω => C i ω * C j ω) := by
    unfold p17Expectation p17CenteredSummationError
    change
      (∑ ω, run.probability.prob ω * (∑ i, run.a i * C i ω) ^ 2) = _
    calc
      (∑ ω, run.probability.prob ω * (∑ i, run.a i * C i ω) ^ 2) =
          ∑ ω, run.probability.prob ω *
            (∑ i, ∑ j, (run.a i * C i ω) * (run.a j * C j ω)) := by
        apply Finset.sum_congr rfl
        intro ω hω
        rw [p17_sum_sq_eq_double_sum]
      _ = ∑ i, ∑ j, ∑ ω,
          run.probability.prob ω *
            ((run.a i * C i ω) * (run.a j * C j ω)) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
      _ = ∑ i, ∑ j, run.a i * run.a j *
          (∑ ω, run.probability.prob ω * (C i ω * C j ω)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω hω
        ring
  rw [hexpand]
  calc
    (∑ i, ∑ j, run.a i * run.a j *
        p17Expectation run.probability (fun ω => C i ω * C j ω)) ≤
        ∑ i, ∑ j, |run.a i| * |run.a j| *
          p17Gamma m ((p17UnitRoundoff run.p) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hcov := run.alpha_product_covariance_bound i j
      change 0 ≤ p17Expectation run.probability
          (fun ω => C i ω * C j ω) ∧
        p17Expectation run.probability (fun ω => C i ω * C j ω) ≤
          p17Gamma m ((p17UnitRoundoff run.p) ^ 2) at hcov
      calc
        run.a i * run.a j *
            p17Expectation run.probability (fun ω => C i ω * C j ω) ≤
          |run.a i| * |run.a j| *
            p17Expectation run.probability (fun ω => C i ω * C j ω) := by
              apply mul_le_mul_of_nonneg_right _ hcov.1
              nlinarith [le_abs_self (run.a i), le_abs_self (run.a j),
                neg_le_abs (run.a i), neg_le_abs (run.a j)]
        _ ≤ |run.a i| * |run.a j| *
            p17Gamma m ((p17UnitRoundoff run.p) ^ 2) :=
          mul_le_mul_of_nonneg_left hcov.2
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (∑ i, |run.a i|) ^ 2 *
        p17Gamma m ((p17UnitRoundoff run.p) ^ 2) := by
      rw [p17_sum_sq_eq_double_sum]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_mul]

lemma p17_eventProb_abs_le_zero_eq_one_of_second_moment_le_zero
    {Ω : Type*} [Fintype Ω]
    (P : NumStability.FiniteProbability Ω) (X : Ω → ℝ)
    (hsecond : P.expectationReal (fun ω => (X ω) ^ 2) ≤ 0) :
    P.eventProb {ω | |X ω| ≤ 0} = 1 := by
  classical
  have hsecond_nonneg :
      0 ≤ P.expectationReal (fun ω => (X ω) ^ 2) :=
    NumStability.FiniteProbability.expectationReal_sq_nonneg P X
  have hsecond_zero :
      P.expectationReal (fun ω => (X ω) ^ 2) = 0 :=
    le_antisymm hsecond hsecond_nonneg
  have hterm_zero : ∀ ω, P.prob ω * (X ω) ^ 2 = 0 := by
    intro ω
    have hterm_nonneg : 0 ≤ P.prob ω * (X ω) ^ 2 :=
      mul_nonneg (P.prob_nonneg ω) (sq_nonneg _)
    have hterm_le :
        P.prob ω * (X ω) ^ 2 ≤
          ∑ η, P.prob η * (X η) ^ 2 := by
      exact Finset.single_le_sum
        (fun η _ => mul_nonneg (P.prob_nonneg η) (sq_nonneg _))
        (Finset.mem_univ ω)
    change (∑ η, P.prob η * (X η) ^ 2) = 0 at hsecond_zero
    rw [hsecond_zero] at hterm_le
    exact le_antisymm hterm_le hterm_nonneg
  unfold NumStability.FiniteProbability.eventProb
  calc
    (∑ ω, if ω ∈ {ω | |X ω| ≤ 0} then P.prob ω else 0) =
        ∑ ω, P.prob ω := by
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases hp : P.prob ω = 0
      · simp [hp]
      · have hsquare : (X ω) ^ 2 = 0 :=
          (mul_eq_zero.mp (hterm_zero ω)).resolve_left hp
        have hx : X ω = 0 := by nlinarith
        simp [hx]
    _ = 1 := P.prob_sum

lemma p17_centered_probability_bound
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17VarianceRecursiveSumRun m Ω)
    (hsum : p17ExactSum run.a ≠ 0)
    (lambda : ℝ) (hlambda_pos : 0 < lambda) :
    1 - lambda ≤
      p17EventProb run.probability {ω |
        |p17CenteredSummationError
          run.toP17LimitedPrecisionRecursiveSumRun ω| ≤
          (∑ i, |run.a i|) *
            Real.sqrt
              (p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda)} := by
  classical
  let P : NumStability.FiniteProbability Ω :=
    { prob := run.probability.prob
      prob_nonneg := run.probability.prob_nonneg
      prob_sum := run.probability.prob_sum }
  let M : Ω → ℝ := fun ω =>
    p17CenteredSummationError
      run.toP17LimitedPrecisionRecursiveSumRun ω
  let S : ℝ := ∑ i, |run.a i|
  let G : ℝ := p17Gamma m ((p17UnitRoundoff run.p) ^ 2)
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have habs_sum_le : |p17ExactSum run.a| ≤ S := by
    dsimp [S]
    unfold p17ExactSum
    exact Finset.abs_sum_le_sum_abs _ _
  have hS_pos : 0 < S := by
    have hexact_pos : 0 < |p17ExactSum run.a| := abs_pos.mpr hsum
    exact lt_of_lt_of_le hexact_pos habs_sum_le
  have hG_nonneg : 0 ≤ G := by
    have hcov := run.alpha_product_covariance_bound
      (0 : Fin (m + 1)) (0 : Fin (m + 1))
    dsimp [G]
    exact hcov.1.trans hcov.2
  have hsecond :
      P.expectationReal (fun ω => (M ω) ^ 2) ≤ S ^ 2 * G := by
    simpa [P, M, S, G, NumStability.FiniteProbability.expectationReal] using
      p17_centered_second_moment_le run
  by_cases hGzero : G = 0
  · have hsecond_zero : P.expectationReal (fun ω => (M ω) ^ 2) ≤ 0 := by
      simpa [hGzero] using hsecond
    have hevent : P.eventProb {ω | |M ω| ≤ 0} = 1 :=
      p17_eventProb_abs_le_zero_eq_one_of_second_moment_le_zero
        P M hsecond_zero
    have hevent' :
        p17EventProb run.probability {ω |
          |p17CenteredSummationError
            run.toP17LimitedPrecisionRecursiveSumRun ω| ≤
            (∑ i, |run.a i|) *
              Real.sqrt
                (p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda)} = 1 := by
      simpa [P, M, S, G, hGzero, p17EventProb,
        NumStability.FiniteProbability.eventProb] using hevent
    rw [hevent']
    linarith
  · have hG_pos : 0 < G := lt_of_le_of_ne hG_nonneg (Ne.symm hGzero)
    have hquot_pos : 0 < G / lambda := div_pos hG_pos hlambda_pos
    have hthreshold_pos : 0 < S * Real.sqrt (G / lambda) :=
      mul_pos hS_pos (Real.sqrt_pos.mpr hquot_pos)
    have hmoment :
        P.expectationReal (fun ω => (M ω - 0) ^ 2) /
            (S * Real.sqrt (G / lambda)) ^ 2 ≤ lambda := by
      have hdenom_nonneg :
          0 ≤ (S * Real.sqrt (G / lambda)) ^ 2 := sq_nonneg _
      calc
        P.expectationReal (fun ω => (M ω - 0) ^ 2) /
            (S * Real.sqrt (G / lambda)) ^ 2 =
          P.expectationReal (fun ω => (M ω) ^ 2) /
            (S * Real.sqrt (G / lambda)) ^ 2 := by simp
        _ ≤ (S ^ 2 * G) / (S * Real.sqrt (G / lambda)) ^ 2 :=
          div_le_div_of_nonneg_right hsecond hdenom_nonneg
        _ = lambda := by
          rw [mul_pow, Real.sq_sqrt (le_of_lt hquot_pos)]
          field_simp [ne_of_gt hS_pos, ne_of_gt hG_pos, ne_of_gt hlambda_pos]
    have hcheb :=
      NumStability.FiniteProbability.eventProb_abs_sub_le_ge_one_sub_of_second_moment
        P M 0 (S * Real.sqrt (G / lambda)) lambda
        hthreshold_pos hmoment
    simpa [P, M, S, G, p17EventProb,
      NumStability.FiniteProbability.eventProb] using hcheb

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
  let centeredEvent : Set Ω := {ω |
    |p17CenteredSummationError
      run.toP17LimitedPrecisionRecursiveSumRun ω| ≤
      (∑ i, |run.a i|) *
        Real.sqrt
          (p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda)}
  let finalEvent : Set Ω := {ω |
    |p17RecursiveSum run.a (fun k => run.delta k ω) -
        p17ExactSum run.a| / |p17ExactSum run.a| ≤
      p17SummationCondition run.a *
        (Real.sqrt
            (p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda) +
          p17Gamma m
              (p17UnitRoundoff run.p +
                p17UnitRoundoff (run.p + run.r)) -
            p17Gamma m (p17UnitRoundoff run.p))}
  have hcentered :
      1 - lambda ≤ p17EventProb run.probability centeredEvent := by
    simpa [centeredEvent] using
      p17_centered_probability_bound run hsum lambda hlambda_pos
  have hsubset : centeredEvent ⊆ finalEvent := by
    intro ω hω
    change
      |p17CenteredSummationError
        run.toP17LimitedPrecisionRecursiveSumRun ω| ≤
        (∑ i, |run.a i|) *
          Real.sqrt
            (p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda) at hω
    change
      |p17RecursiveSum run.a (fun k => run.delta k ω) -
          p17ExactSum run.a| / |p17ExactSum run.a| ≤
        p17SummationCondition run.a *
          (Real.sqrt
              (p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda) +
            p17Gamma m
                (p17UnitRoundoff run.p +
                  p17UnitRoundoff (run.p + run.r)) -
              p17Gamma m (p17UnitRoundoff run.p))
    have hdecomp := p17_recursive_error_decomposition run ω
    have htotal :
        |p17RecursiveSum run.a (fun k => run.delta k ω) -
            p17ExactSum run.a| ≤
          (∑ i, |run.a i|) *
            (Real.sqrt
                (p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda) +
              (p17Gamma m
                  (p17UnitRoundoff run.p +
                    p17UnitRoundoff (run.p + run.r)) -
                p17Gamma m (p17UnitRoundoff run.p))) := by
      calc
        |p17RecursiveSum run.a (fun k => run.delta k ω) -
            p17ExactSum run.a| =
          |p17CenteredSummationError
              run.toP17LimitedPrecisionRecursiveSumRun ω +
            p17LimitedPrecisionRemainder
              run.toP17LimitedPrecisionRecursiveSumRun ω| := by rw [hdecomp]
        _ ≤ |p17CenteredSummationError
                run.toP17LimitedPrecisionRecursiveSumRun ω| +
              |p17LimitedPrecisionRemainder
                run.toP17LimitedPrecisionRecursiveSumRun ω| := abs_add_le _ _
        _ ≤ (∑ i, |run.a i|) *
                Real.sqrt
                  (p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda) +
              (∑ i, |run.a i|) *
                (p17Gamma m
                    (p17UnitRoundoff run.p +
                      p17UnitRoundoff (run.p + run.r)) -
                  p17Gamma m (p17UnitRoundoff run.p)) :=
            add_le_add hω (p17_remainder_abs_le run ω)
        _ = (∑ i, |run.a i|) *
            (Real.sqrt
                (p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda) +
              (p17Gamma m
                  (p17UnitRoundoff run.p +
                    p17UnitRoundoff (run.p + run.r)) -
                p17Gamma m (p17UnitRoundoff run.p))) := by ring
    have hdenom_pos : 0 < |p17ExactSum run.a| := abs_pos.mpr hsum
    have hdiv := div_le_div_of_nonneg_right htotal (le_of_lt hdenom_pos)
    unfold p17SummationCondition
    convert hdiv using 1 <;> ring
  let P : NumStability.FiniteProbability Ω :=
    { prob := run.probability.prob
      prob_nonneg := run.probability.prob_nonneg
      prob_sum := run.probability.prob_sum }
  have hmono :
      p17EventProb run.probability centeredEvent ≤
        p17EventProb run.probability finalEvent := by
    have := NumStability.FiniteProbability.eventProb_mono P hsubset
    simpa [P, p17EventProb,
      NumStability.FiniteProbability.eventProb] using this
  have hfinal : 1 - lambda ≤ p17EventProb run.probability finalEvent :=
    hcentered.trans hmono
  simpa [finalEvent] using hfinal

end HighamBench
