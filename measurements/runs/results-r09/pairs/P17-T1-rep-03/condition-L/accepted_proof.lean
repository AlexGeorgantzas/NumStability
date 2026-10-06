import HighamBench.P17Definitions
import NumStability.Analysis.FiniteProbability

namespace HighamBench

open scoped BigOperators

lemma p17_recursiveCoefficient_castSucc
    {m : ℕ} (delta : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    p17RecursiveCoefficient delta i.castSucc =
      p17RecursiveCoefficient (fun k : Fin m => delta k.castSucc) i *
        (1 + delta (Fin.last m)) := by
  refine Fin.cases ?_ ?_ i
  · simp [p17RecursiveCoefficient, Fin.prod_univ_castSucc]
  · intro j
    simp [p17RecursiveCoefficient, p17SuffixErrorProduct]

lemma p17_recursiveCoefficient_last
    {m : ℕ} (delta : Fin (m + 1) → ℝ) :
    p17RecursiveCoefficient delta (Fin.last (m + 1)) =
      1 + delta (Fin.last m) := by
  change p17SuffixErrorProduct (m + 1) delta (Fin.last m) = _
  simp [p17SuffixErrorProduct]

lemma p17_sum_recursiveCoefficient_succ
    {m : ℕ} (a : Fin (m + 2) → ℝ) (delta : Fin (m + 1) → ℝ) :
    (∑ i, a i * p17RecursiveCoefficient delta i) =
      ((∑ i : Fin (m + 1),
          a i.castSucc *
            p17RecursiveCoefficient (fun k : Fin m => delta k.castSucc) i) +
        a (Fin.last (m + 1))) * (1 + delta (Fin.last m)) := by
  rw [Fin.sum_univ_castSucc]
  simp_rw [p17_recursiveCoefficient_castSucc]
  rw [p17_recursiveCoefficient_last]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  ring

lemma p17_recursiveSum_eq_sum_coeff
    {m : ℕ} (a : Fin (m + 1) → ℝ) (delta : Fin m → ℝ) :
    p17RecursiveSum a delta =
      ∑ i, a i * p17RecursiveCoefficient delta i := by
  induction m with
  | zero =>
      simp [p17RecursiveSum, p17RecursiveCoefficient]
  | succ m ih =>
      rw [p17RecursiveSum, Fin.foldl_succ_last]
      change
        (p17RecursiveSum (fun i : Fin (m + 1) => a i.castSucc)
            (fun k : Fin m => delta k.castSucc) + a (Fin.last (m + 1))) *
            (1 + delta (Fin.last m)) = _
      rw [ih]
      exact (p17_sum_recursiveCoefficient_succ a delta).symm

lemma p17_expectation_sum
    {ι Ω : Type*} [Fintype ι] [Fintype Ω]
    (P : P17FiniteProbability Ω) (X : ι → Ω → ℝ) :
    p17Expectation P (fun ω => ∑ i, X i ω) =
      ∑ i, p17Expectation P (X i) := by
  classical
  unfold p17Expectation
  calc
    ∑ ω, P.prob ω * ∑ i, X i ω =
        ∑ ω, ∑ i, P.prob ω * X i ω := by
          apply Finset.sum_congr rfl
          intro ω _
          rw [Finset.mul_sum]
    _ = ∑ i, ∑ ω, P.prob ω * X i ω := by
          rw [Finset.sum_comm]

lemma p17_expectation_const_mul
    {Ω : Type*} [Fintype Ω] (P : P17FiniteProbability Ω)
    (c : ℝ) (X : Ω → ℝ) :
    p17Expectation P (fun ω => c * X ω) =
      c * p17Expectation P X := by
  classical
  unfold p17Expectation
  calc
    ∑ ω, P.prob ω * (c * X ω) =
        ∑ ω, c * (P.prob ω * X ω) := by
          apply Finset.sum_congr rfl
          intro ω _
          ring
    _ = c * ∑ ω, P.prob ω * X ω := by
          rw [Finset.mul_sum]

lemma p17_centered_second_moment_le
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17VarianceRecursiveSumRun m Ω) :
    p17Expectation run.probability
        (fun ω =>
          (p17CenteredSummationError
            run.toP17LimitedPrecisionRecursiveSumRun ω) ^ 2) ≤
      (∑ i, |run.a i|) ^ 2 *
        p17Gamma m ((p17UnitRoundoff run.p) ^ 2) := by
  classical
  let L := run.toP17LimitedPrecisionRecursiveSumRun
  let Z : Fin (m + 1) → Ω → ℝ := fun i ω =>
    p17RecursiveCoefficient (fun k => p17Alpha L k ω) i - 1
  have hexpand :
      p17Expectation run.probability
          (fun ω => (p17CenteredSummationError L ω) ^ 2) =
        ∑ i, ∑ j,
          (run.a i * run.a j) *
            p17Expectation run.probability (fun ω => Z i ω * Z j ω) := by
    calc
      p17Expectation run.probability
          (fun ω => (p17CenteredSummationError L ω) ^ 2) =
          p17Expectation run.probability
            (fun ω => ∑ i, ∑ j,
              (run.a i * Z i ω) * (run.a j * Z j ω)) := by
                apply congrArg
                funext ω
                unfold p17CenteredSummationError
                change (∑ i, run.a i * Z i ω) ^ 2 = _
                rw [pow_two, Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro i _
                rw [Finset.mul_sum]
      _ = ∑ i, p17Expectation run.probability
            (fun ω => ∑ j,
              (run.a i * Z i ω) * (run.a j * Z j ω)) := by
                rw [p17_expectation_sum]
      _ = ∑ i, ∑ j, p17Expectation run.probability
            (fun ω =>
              (run.a i * Z i ω) * (run.a j * Z j ω)) := by
                apply Finset.sum_congr rfl
                intro i _
                rw [p17_expectation_sum]
      _ = ∑ i, ∑ j,
          (run.a i * run.a j) *
            p17Expectation run.probability (fun ω => Z i ω * Z j ω) := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              calc
                p17Expectation run.probability
                    (fun ω =>
                      (run.a i * Z i ω) * (run.a j * Z j ω)) =
                    p17Expectation run.probability
                      (fun ω =>
                        (run.a i * run.a j) * (Z i ω * Z j ω)) := by
                          apply congrArg
                          funext ω
                          ring
                _ = (run.a i * run.a j) *
                    p17Expectation run.probability
                      (fun ω => Z i ω * Z j ω) :=
                      p17_expectation_const_mul _ _ _
  rw [hexpand]
  calc
    (∑ i, ∑ j,
        (run.a i * run.a j) *
          p17Expectation run.probability (fun ω => Z i ω * Z j ω)) ≤
        ∑ i, ∑ j,
          |run.a i| * |run.a j| *
            p17Gamma m ((p17UnitRoundoff run.p) ^ 2) := by
              apply Finset.sum_le_sum
              intro i _
              apply Finset.sum_le_sum
              intro j _
              have hcov0 : 0 ≤ p17Expectation run.probability
                  (fun ω => Z i ω * Z j ω) := by
                simpa [Z, L] using
                  (run.alpha_product_covariance_bound i j).1
              have hcov1 : p17Expectation run.probability
                    (fun ω => Z i ω * Z j ω) ≤
                  p17Gamma m ((p17UnitRoundoff run.p) ^ 2) := by
                simpa [Z, L] using
                  (run.alpha_product_covariance_bound i j).2
              calc
                (run.a i * run.a j) *
                    p17Expectation run.probability
                      (fun ω => Z i ω * Z j ω) ≤
                    |run.a i * run.a j| *
                      p17Expectation run.probability
                        (fun ω => Z i ω * Z j ω) :=
                          mul_le_mul_of_nonneg_right
                            (le_abs_self (run.a i * run.a j)) hcov0
                _ = |run.a i| * |run.a j| *
                      p17Expectation run.probability
                        (fun ω => Z i ω * Z j ω) := by
                          rw [abs_mul]
                _ ≤ |run.a i| * |run.a j| *
                      p17Gamma m ((p17UnitRoundoff run.p) ^ 2) := by
                        exact mul_le_mul_of_nonneg_left hcov1
                          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (∑ i, |run.a i|) ^ 2 *
          p17Gamma m ((p17UnitRoundoff run.p) ^ 2) := by
            have hinner (i : Fin (m + 1)) :
                (∑ j, |run.a i| * |run.a j| *
                    p17Gamma m ((p17UnitRoundoff run.p) ^ 2)) =
                  |run.a i| * (∑ j, |run.a j|) *
                    p17Gamma m ((p17UnitRoundoff run.p) ^ 2) := by
              calc
                (∑ j, |run.a i| * |run.a j| *
                    p17Gamma m ((p17UnitRoundoff run.p) ^ 2)) =
                    (∑ j, |run.a i| * |run.a j|) *
                      p17Gamma m ((p17UnitRoundoff run.p) ^ 2) := by
                        rw [Finset.sum_mul]
                _ = |run.a i| * (∑ j, |run.a j|) *
                      p17Gamma m ((p17UnitRoundoff run.p) ^ 2) := by
                        rw [Finset.mul_sum]
            simp_rw [hinner]
            calc
              (∑ i, |run.a i| * (∑ j, |run.a j|) *
                  p17Gamma m ((p17UnitRoundoff run.p) ^ 2)) =
                  (∑ i, |run.a i| * (∑ j, |run.a j|)) *
                    p17Gamma m ((p17UnitRoundoff run.p) ^ 2) := by
                      rw [Finset.sum_mul]
              _ = ((∑ i, |run.a i|) * (∑ j, |run.a j|)) *
                    p17Gamma m ((p17UnitRoundoff run.p) ^ 2) := by
                      congr 1
                      symm
                      rw [Finset.sum_mul]
              _ = (∑ i, |run.a i|) ^ 2 *
                    p17Gamma m ((p17UnitRoundoff run.p) ^ 2) := by
                      ring

lemma p17_recursive_error_decomposition
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17LimitedPrecisionRecursiveSumRun m Ω) (ω : Ω) :
    p17RecursiveSum run.a (fun k => run.delta k ω) -
        p17ExactSum run.a =
      p17CenteredSummationError run ω +
        p17LimitedPrecisionRemainder run ω := by
  classical
  rw [p17_recursiveSum_eq_sum_coeff]
  unfold p17ExactSum p17CenteredSummationError
    p17LimitedPrecisionRemainder p17CoefficientRemainder p17Alpha
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma p17_limitedPrecisionRemainder_abs_le
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17VarianceRecursiveSumRun m Ω) (ω : Ω) :
    |p17LimitedPrecisionRemainder
        run.toP17LimitedPrecisionRecursiveSumRun ω| ≤
      (∑ i, |run.a i|) *
        (p17Gamma m
            (p17UnitRoundoff run.p +
              p17UnitRoundoff (run.p + run.r)) -
          p17Gamma m (p17UnitRoundoff run.p)) := by
  classical
  unfold p17LimitedPrecisionRemainder
  calc
    |∑ i, run.a i *
        p17CoefficientRemainder
          run.toP17LimitedPrecisionRecursiveSumRun i ω| ≤
        ∑ i, |run.a i *
          p17CoefficientRemainder
            run.toP17LimitedPrecisionRecursiveSumRun i ω| := by
              simpa using Finset.abs_sum_le_sum_abs
                (fun i => run.a i *
                  p17CoefficientRemainder
                    run.toP17LimitedPrecisionRecursiveSumRun i ω)
                Finset.univ
    _ ≤ ∑ i, |run.a i| *
          (p17Gamma m
              (p17UnitRoundoff run.p +
                p17UnitRoundoff (run.p + run.r)) -
            p17Gamma m (p17UnitRoundoff run.p)) := by
              apply Finset.sum_le_sum
              intro i _
              rw [abs_mul]
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
      have ha : run.a 0 ≠ 0 := by
        simpa [p17ExactSum] using hsum
      simp [p17RecursiveSum, p17ExactSum, p17SummationCondition,
        p17EventProb, p17Gamma, ha, run.probability.prob_sum,
        le_of_lt hlambda_pos]
  | succ m =>
      let L := run.toP17LimitedPrecisionRecursiveSumRun
      let S : ℝ := ∑ i, |run.a i|
      let G : ℝ :=
        p17Gamma (m + 1) ((p17UnitRoundoff run.p) ^ 2)
      let B : ℝ :=
        p17Gamma (m + 1)
            (p17UnitRoundoff run.p +
              p17UnitRoundoff (run.p + run.r)) -
          p17Gamma (m + 1) (p17UnitRoundoff run.p)
      let M : Ω → ℝ := fun ω => p17CenteredSummationError L ω
      let eta : ℝ := S * Real.sqrt (G / lambda)
      let P : NumStability.FiniteProbability Ω :=
        { prob := run.probability.prob
          prob_nonneg := run.probability.prob_nonneg
          prob_sum := run.probability.prob_sum }
      have hSpos : 0 < S := by
        have habs_sum : |p17ExactSum run.a| ≤ S := by
          unfold p17ExactSum
          dsimp [S]
          simpa using Finset.abs_sum_le_sum_abs run.a Finset.univ
        exact lt_of_lt_of_le (abs_pos.mpr hsum) habs_sum
      have hu : 0 < p17UnitRoundoff run.p := by
        unfold p17UnitRoundoff
        positivity
      have hGpos : 0 < G := by
        dsimp [G]
        unfold p17Gamma
        have hbase :
            1 < 1 + (p17UnitRoundoff run.p) ^ 2 := by
          nlinarith [sq_pos_of_pos hu]
        have hp := one_lt_pow₀ hbase (Nat.succ_ne_zero m)
        exact sub_pos.mpr (by
          simpa [Nat.succ_eq_add_one] using hp)
      have hquotpos : 0 < G / lambda :=
        div_pos hGpos hlambda_pos
      have heta : 0 < eta := by
        dsimp [eta]
        exact mul_pos hSpos (Real.sqrt_pos.2 hquotpos)
      have hmoment :
          p17Expectation run.probability (fun ω => (M ω) ^ 2) ≤
            S ^ 2 * G := by
        simpa [M, L, S, G] using
          (p17_centered_second_moment_le run)
      have hsqrt_sq :
          (Real.sqrt (G / lambda)) ^ 2 = G / lambda :=
        Real.sq_sqrt (le_of_lt hquotpos)
      have heta_sq : eta ^ 2 = S ^ 2 * G / lambda := by
        dsimp [eta]
        calc
          (S * Real.sqrt (G / lambda)) ^ 2 =
              S ^ 2 * (Real.sqrt (G / lambda)) ^ 2 := by ring
          _ = S ^ 2 * G / lambda := by
                rw [hsqrt_sq]
                ring
      have hratio :
          p17Expectation run.probability (fun ω => (M ω) ^ 2) /
              eta ^ 2 ≤ lambda := by
        calc
          p17Expectation run.probability (fun ω => (M ω) ^ 2) /
                eta ^ 2 ≤
              (S ^ 2 * G) / eta ^ 2 :=
                div_le_div_of_nonneg_right hmoment
                  (le_of_lt (sq_pos_of_pos heta))
          _ = lambda := by
            rw [heta_sq]
            field_simp [ne_of_gt hSpos, ne_of_gt hGpos,
              ne_of_gt hlambda_pos]
      have hratioP :
          P.expectationReal (fun ω => (M ω - 0) ^ 2) / eta ^ 2 ≤
            lambda := by
        change
          p17Expectation run.probability (fun ω => (M ω - 0) ^ 2) /
              eta ^ 2 ≤ lambda
        simpa using hratio
      have hcenter :
          1 - lambda ≤ P.eventProb {ω | |M ω - 0| ≤ eta} :=
        NumStability.FiniteProbability.eventProb_abs_sub_le_ge_one_sub_of_second_moment
            P M 0 eta lambda heta hratioP
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
        have hM : |M ω| ≤ eta := by simpa using hω
        have hrem :
            |p17LimitedPrecisionRemainder L ω| ≤ S * B := by
          simpa [L, S, B] using
            (p17_limitedPrecisionRemainder_abs_le run ω)
        have hdecomp := p17_recursive_error_decomposition L ω
        have herr :
            |p17RecursiveSum run.a (fun k => run.delta k ω) -
                p17ExactSum run.a| ≤
              S * (Real.sqrt (G / lambda) + B) := by
          calc
            |p17RecursiveSum run.a (fun k => run.delta k ω) -
                p17ExactSum run.a| =
                |M ω + p17LimitedPrecisionRemainder L ω| := by
                  rw [hdecomp]
            _ ≤ |M ω| + |p17LimitedPrecisionRemainder L ω| :=
                  abs_add_le _ _
            _ ≤ eta + S * B := add_le_add hM hrem
            _ = S * (Real.sqrt (G / lambda) + B) := by
                  dsimp [eta]
                  ring
        have hdenom : 0 < |p17ExactSum run.a| := abs_pos.mpr hsum
        calc
          |p17RecursiveSum run.a (fun k => run.delta k ω) -
                p17ExactSum run.a| / |p17ExactSum run.a| ≤
              (S * (Real.sqrt (G / lambda) + B)) /
                |p17ExactSum run.a| :=
                  div_le_div_of_nonneg_right herr (le_of_lt hdenom)
          _ = p17SummationCondition run.a *
                (Real.sqrt
                    (p17Gamma (m + 1)
                      ((p17UnitRoundoff run.p) ^ 2) / lambda) +
                  p17Gamma (m + 1)
                      (p17UnitRoundoff run.p +
                        p17UnitRoundoff (run.p + run.r)) -
                    p17Gamma (m + 1)
                      (p17UnitRoundoff run.p)) := by
                unfold p17SummationCondition
                dsimp [S, G, B]
                ring
      have hmono :=
        NumStability.FiniteProbability.eventProb_mono P hsubset
      change 1 - lambda ≤ P.eventProb
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
                    (p17UnitRoundoff run.p))}
      exact hcenter.trans hmono

end HighamBench
