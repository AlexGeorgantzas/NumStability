import HighamBench.P17Definitions

namespace HighamBench

open scoped BigOperators

lemma p17Gamma_nonneg (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ p17Gamma n u := by
  unfold p17Gamma
  have h : 1 ≤ 1 + u := by linarith
  exact sub_nonneg.mpr (one_le_pow₀ h)

lemma p17UnitRoundoff_nonneg (p : ℕ) : 0 ≤ p17UnitRoundoff p := by
  unfold p17UnitRoundoff
  positivity

lemma p17RecursiveCoefficient_castSucc
    {m : ℕ} (e : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    p17RecursiveCoefficient e i.castSucc =
      p17RecursiveCoefficient (fun k : Fin m => e k.castSucc) i *
        (1 + e (Fin.last m)) := by
  cases i using Fin.cases with
  | zero =>
      simp [p17RecursiveCoefficient, p17SuffixErrorProduct,
        Fin.prod_univ_castSucc]
  | succ i =>
      simp [p17RecursiveCoefficient, p17SuffixErrorProduct]

lemma p17RecursiveCoefficient_last
    {m : ℕ} (e : Fin (m + 1) → ℝ) :
    p17RecursiveCoefficient e (Fin.last (m + 1)) =
      1 + e (Fin.last m) := by
  unfold p17RecursiveCoefficient
  rw [show Fin.last (m + 1) = (Fin.last m).succ by rfl]
  rw [Fin.cases_succ]
  simp [p17RecursiveCoefficient, p17SuffixErrorProduct]

lemma p17RecursiveSum_eq_sum_coeff :
    ∀ {m : ℕ} (a : Fin (m + 1) → ℝ) (e : Fin m → ℝ),
      p17RecursiveSum a e =
        ∑ i, a i * p17RecursiveCoefficient e i := by
  intro m
  induction m with
  | zero =>
      intro a e
      simp [p17RecursiveSum, p17RecursiveCoefficient]
  | succ m ih =>
      intro a e
      rw [p17RecursiveSum, Fin.foldl_succ_last]
      change
        (p17RecursiveSum (fun i : Fin (m + 1) => a i.castSucc)
              (fun k : Fin m => e k.castSucc) +
            a (Fin.last m).succ) *
            (1 + e (Fin.last m)) = _
      rw [ih]
      conv_rhs => rw [Fin.sum_univ_castSucc]
      simp only [p17RecursiveCoefficient_castSucc,
        p17RecursiveCoefficient_last]
      simp [add_mul, Finset.sum_mul, mul_assoc]

lemma p17RecursiveSum_error_decomposition
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17LimitedPrecisionRecursiveSumRun m Ω) (ω : Ω) :
    p17RecursiveSum run.a (fun k => run.delta k ω) - p17ExactSum run.a =
      p17CenteredSummationError run ω +
        p17LimitedPrecisionRemainder run ω := by
  rw [p17RecursiveSum_eq_sum_coeff]
  unfold p17ExactSum p17CenteredSummationError
    p17LimitedPrecisionRemainder p17CoefficientRemainder
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
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
  have hB : 0 ≤ B :=
    le_trans (abs_nonneg _)
      (run.coefficient_remainder_bound (0 : Fin (m + 1)) ω)
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
      simp only [abs_mul]
    _ ≤ ∑ i, |run.a i| * B := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (run.coefficient_remainder_bound i ω) (abs_nonneg _)
    _ = (∑ i, |run.a i|) * B := by
      rw [Finset.sum_mul]

lemma p17EventProb_mono
    {Ω : Type*} [Fintype Ω] (P : P17FiniteProbability Ω)
    {E F : Set Ω} (hEF : E ⊆ F) :
    p17EventProb P E ≤ p17EventProb P F := by
  classical
  unfold p17EventProb
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hE : ω ∈ E
  · have hF : ω ∈ F := hEF hE
    simp [hE, hF]
  · by_cases hF : ω ∈ F
    · simp [hE, hF, P.prob_nonneg]
    · simp [hE, hF]

lemma p17EventProb_sq_gt_le
    {Ω : Type*} [Fintype Ω] (P : P17FiniteProbability Ω)
    (X : Ω → ℝ) {q : ℝ} (hq : 0 < q) :
    p17EventProb P {ω | q < (X ω) ^ 2} ≤
      p17Expectation P (fun ω => (X ω) ^ 2) / q := by
  classical
  unfold p17EventProb p17Expectation
  calc
    (∑ ω, if ω ∈ {ω | q < (X ω) ^ 2} then P.prob ω else 0) ≤
        ∑ ω, P.prob ω * (X ω) ^ 2 / q := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases h : q < (X ω) ^ 2
      · have hone : 1 ≤ (X ω) ^ 2 / q :=
          (le_div_iff₀ hq).2 (by simpa using le_of_lt h)
        simp only [Set.mem_setOf_eq, h, if_true]
        calc
          P.prob ω = P.prob ω * 1 := by ring
          _ ≤ P.prob ω * ((X ω) ^ 2 / q) :=
            mul_le_mul_of_nonneg_left hone (P.prob_nonneg ω)
          _ = P.prob ω * (X ω) ^ 2 / q := by ring
      · simp only [Set.mem_setOf_eq, h, if_false]
        exact div_nonneg
          (mul_nonneg (P.prob_nonneg ω) (sq_nonneg _)) (le_of_lt hq)
    _ = (∑ ω, P.prob ω * (X ω) ^ 2) / q := by
      rw [Finset.sum_div]

lemma p17CenteredSummationError_second_moment_le
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17VarianceRecursiveSumRun m Ω) :
    p17Expectation run.probability
        (fun ω =>
          (p17CenteredSummationError
            run.toP17LimitedPrecisionRecursiveSumRun ω) ^ 2) ≤
      (∑ i, |run.a i|) ^ 2 *
        p17Gamma m ((p17UnitRoundoff run.p) ^ 2) := by
  let Z : Fin (m + 1) → Ω → ℝ := fun i ω =>
    p17RecursiveCoefficient
        (fun k => p17Alpha
          run.toP17LimitedPrecisionRecursiveSumRun k ω) i - 1
  let G := p17Gamma m ((p17UnitRoundoff run.p) ^ 2)
  have hG : 0 ≤ G := by
    apply p17Gamma_nonneg
    positivity
  have hterm : ∀ i j,
      run.a i * run.a j *
          p17Expectation run.probability (fun ω => Z i ω * Z j ω) ≤
        |run.a i| * |run.a j| * G := by
    intro i j
    have hc := run.alpha_product_covariance_bound i j
    have ha : run.a i * run.a j ≤ |run.a i| * |run.a j| := by
      rw [← abs_mul]
      exact le_abs_self _
    calc
      run.a i * run.a j *
          p17Expectation run.probability (fun ω => Z i ω * Z j ω) ≤
          |run.a i| * |run.a j| *
            p17Expectation run.probability (fun ω => Z i ω * Z j ω) :=
        mul_le_mul_of_nonneg_right ha hc.1
      _ ≤ |run.a i| * |run.a j| * G :=
        mul_le_mul_of_nonneg_left hc.2
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hexpand :
      p17Expectation run.probability
          (fun ω =>
            (p17CenteredSummationError
              run.toP17LimitedPrecisionRecursiveSumRun ω) ^ 2) =
        ∑ i, ∑ j,
          run.a i * run.a j *
            p17Expectation run.probability (fun ω => Z i ω * Z j ω) := by
    unfold p17Expectation p17CenteredSummationError
    dsimp only [Z]
    simp only [pow_two]
    simp_rw [Finset.sum_mul_sum]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    funext i
    rw [Finset.sum_comm]
    congr 1
    funext j
    apply Finset.sum_congr rfl
    intro ω hω
    ring
  rw [hexpand]
  calc
    (∑ i, ∑ j,
        run.a i * run.a j *
          p17Expectation run.probability (fun ω => Z i ω * Z j ω)) ≤
        ∑ i, ∑ j, |run.a i| * |run.a j| * G := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact hterm i j
    _ = (∑ i, |run.a i|) ^ 2 * G := by
      rw [pow_two, Finset.sum_mul_sum]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_mul]

lemma p17CenteredSummationError_probability_bound
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17VarianceRecursiveSumRun m Ω)
    (lambda : ℝ) (hlambda_pos : 0 < lambda) :
    1 - lambda ≤
      p17EventProb run.probability {ω |
        |p17CenteredSummationError
            run.toP17LimitedPrecisionRecursiveSumRun ω| ≤
          (∑ i, |run.a i|) *
            Real.sqrt
              (p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda)} := by
  classical
  let X : Ω → ℝ := fun ω =>
    p17CenteredSummationError
      run.toP17LimitedPrecisionRecursiveSumRun ω
  let S : ℝ := ∑ i, |run.a i|
  let G : ℝ := p17Gamma m ((p17UnitRoundoff run.p) ^ 2)
  let Q : ℝ := S ^ 2 * G
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun i hi => abs_nonneg _
  have hG : 0 ≤ G := by
    dsimp [G]
    apply p17Gamma_nonneg
    positivity
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hmoment :
      p17Expectation run.probability (fun ω => (X ω) ^ 2) ≤ Q := by
    dsimp [X, Q, S, G]
    exact p17CenteredSummationError_second_moment_le run
  have hsqrt_nonneg : 0 ≤ Real.sqrt (G / lambda) := Real.sqrt_nonneg _
  have hthreshold_nonneg : 0 ≤ S * Real.sqrt (G / lambda) :=
    mul_nonneg hS hsqrt_nonneg
  have hpartition :
      p17EventProb run.probability
          {ω | |X ω| ≤ S * Real.sqrt (G / lambda)} +
        p17EventProb run.probability
          {ω | S * Real.sqrt (G / lambda) < |X ω|} = 1 := by
    unfold p17EventProb
    rw [← Finset.sum_add_distrib, ← run.probability.prob_sum]
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases h : |X ω| ≤ S * Real.sqrt (G / lambda)
    · have hnlt := not_lt_of_ge h
      simp [h, hnlt]
    · have hlt : S * Real.sqrt (G / lambda) < |X ω| :=
        lt_of_not_ge h
      simp [h, hlt]
  have hbad :
      p17EventProb run.probability
          {ω | S * Real.sqrt (G / lambda) < |X ω|} ≤ lambda := by
    rcases hQ.eq_or_lt with hQzero | hQpos
    · have hthreshold_zero : S * Real.sqrt (G / lambda) = 0 := by
        have hprod : S ^ 2 = 0 ∨ G = 0 := by
          exact mul_eq_zero.mp (by simpa [Q] using hQzero)
        rcases hprod with hSsq | hGzero
        · have hSzero : S = 0 := sq_eq_zero_iff.mp hSsq
          simp [hSzero]
        · simp [hGzero]
      have hexpect_nonneg :
          0 ≤ p17Expectation run.probability (fun ω => (X ω) ^ 2) := by
        unfold p17Expectation
        exact Finset.sum_nonneg fun ω hω =>
          mul_nonneg (run.probability.prob_nonneg ω) (sq_nonneg _)
      have hexpect_zero :
          p17Expectation run.probability (fun ω => (X ω) ^ 2) = 0 := by
        apply le_antisymm
        · simpa [hQzero] using hmoment
        · exact hexpect_nonneg
      have heach : ∀ ω, run.probability.prob ω * (X ω) ^ 2 = 0 := by
        have hsum : ∑ ω, run.probability.prob ω * (X ω) ^ 2 = 0 := by
          simpa [p17Expectation] using hexpect_zero
        have hall :=
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun ω (_ : ω ∈ (Finset.univ : Finset Ω)) =>
              mul_nonneg (run.probability.prob_nonneg ω) (sq_nonneg _))).mp hsum
        intro ω
        exact hall ω (Finset.mem_univ ω)
      have hbadzero :
          p17EventProb run.probability
              {ω | S * Real.sqrt (G / lambda) < |X ω|} = 0 := by
        unfold p17EventProb
        apply Finset.sum_eq_zero
        intro ω hω
        by_cases hb : S * Real.sqrt (G / lambda) < |X ω|
        · have habspos : 0 < |X ω| := by
            rw [hthreshold_zero] at hb
            exact hb
          have hxne : X ω ≠ 0 := (abs_pos.mp habspos)
          have hpzero : run.probability.prob ω = 0 :=
            (mul_eq_zero.mp (heach ω)).resolve_right (pow_ne_zero 2 hxne)
          simp [hb, hpzero]
        · simp [hb]
      rw [hbadzero]
      exact le_of_lt hlambda_pos
    · have hq : 0 < Q / lambda := div_pos hQpos hlambda_pos
      have hsqrt_sq : (Real.sqrt (G / lambda)) ^ 2 = G / lambda := by
        apply Real.sq_sqrt
        exact div_nonneg hG (le_of_lt hlambda_pos)
      have hthreshold_sq :
          (S * Real.sqrt (G / lambda)) ^ 2 = Q / lambda := by
        dsimp [Q]
        rw [mul_pow, hsqrt_sq]
        ring
      have hsubset :
          {ω | S * Real.sqrt (G / lambda) < |X ω|} ⊆
            {ω | Q / lambda < (X ω) ^ 2} := by
        intro ω hω
        have hsquares :
            (S * Real.sqrt (G / lambda)) ^ 2 < |X ω| ^ 2 :=
          (sq_lt_sq₀ hthreshold_nonneg (abs_nonneg _)).2 hω
        rw [hthreshold_sq, sq_abs] at hsquares
        exact hsquares
      calc
        p17EventProb run.probability
            {ω | S * Real.sqrt (G / lambda) < |X ω|} ≤
            p17EventProb run.probability
              {ω | Q / lambda < (X ω) ^ 2} :=
          p17EventProb_mono run.probability hsubset
        _ ≤ p17Expectation run.probability (fun ω => (X ω) ^ 2) /
              (Q / lambda) :=
          p17EventProb_sq_gt_le run.probability X hq
        _ ≤ Q / (Q / lambda) :=
          div_le_div_of_nonneg_right hmoment (le_of_lt hq)
        _ = lambda := by
          field_simp
  change 1 - lambda ≤
    p17EventProb run.probability
      {ω | |X ω| ≤ S * Real.sqrt (G / lambda)}
  linarith

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
  calc
    1 - lambda ≤
        p17EventProb run.probability {ω |
          |p17CenteredSummationError
              run.toP17LimitedPrecisionRecursiveSumRun ω| ≤
            (∑ i, |run.a i|) *
              Real.sqrt
                (p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda)} :=
      p17CenteredSummationError_probability_bound run lambda hlambda_pos
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
      apply p17EventProb_mono run.probability
      intro ω hcenter
      have hdecomp :=
        p17RecursiveSum_error_decomposition
          run.toP17LimitedPrecisionRecursiveSumRun ω
      have hrem := p17LimitedPrecisionRemainder_abs_le run ω
      have herr :
          |p17RecursiveSum run.a (fun k => run.delta k ω) -
              p17ExactSum run.a| ≤
            (∑ i, |run.a i|) *
              (Real.sqrt
                  (p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda) +
                (p17Gamma m
                    (p17UnitRoundoff run.p +
                      p17UnitRoundoff (run.p + run.r)) -
                  p17Gamma m (p17UnitRoundoff run.p))) := by
        rw [hdecomp]
        calc
          |p17CenteredSummationError
                run.toP17LimitedPrecisionRecursiveSumRun ω +
              p17LimitedPrecisionRemainder
                run.toP17LimitedPrecisionRecursiveSumRun ω| ≤
              |p17CenteredSummationError
                  run.toP17LimitedPrecisionRecursiveSumRun ω| +
                |p17LimitedPrecisionRemainder
                  run.toP17LimitedPrecisionRecursiveSumRun ω| :=
            abs_add_le _ _
          _ ≤ (∑ i, |run.a i|) *
                  Real.sqrt
                    (p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda) +
                (∑ i, |run.a i|) *
                  (p17Gamma m
                      (p17UnitRoundoff run.p +
                        p17UnitRoundoff (run.p + run.r)) -
                    p17Gamma m (p17UnitRoundoff run.p)) :=
            add_le_add hcenter hrem
          _ = (∑ i, |run.a i|) *
                (Real.sqrt
                    (p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda) +
                  (p17Gamma m
                      (p17UnitRoundoff run.p +
                        p17UnitRoundoff (run.p + run.r)) -
                    p17Gamma m (p17UnitRoundoff run.p))) := by
            ring
      have hden : 0 < |p17ExactSum run.a| := abs_pos.mpr hsum
      unfold p17SummationCondition
      calc
        |p17RecursiveSum run.a (fun k => run.delta k ω) -
              p17ExactSum run.a| / |p17ExactSum run.a| ≤
            ((∑ i, |run.a i|) *
              (Real.sqrt
                  (p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda) +
                (p17Gamma m
                    (p17UnitRoundoff run.p +
                      p17UnitRoundoff (run.p + run.r)) -
                  p17Gamma m (p17UnitRoundoff run.p)))) /
              |p17ExactSum run.a| :=
          (div_le_div_iff_of_pos_right hden).2 herr
        _ = (∑ i, |run.a i|) / |p17ExactSum run.a| *
              (Real.sqrt
                  (p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda) +
                p17Gamma m
                    (p17UnitRoundoff run.p +
                      p17UnitRoundoff (run.p + run.r)) -
                  p17Gamma m (p17UnitRoundoff run.p)) := by
          ring

end HighamBench
