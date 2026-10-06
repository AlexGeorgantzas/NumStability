import HighamBench.P17Definitions
import NumStability.Analysis.FiniteProbability

namespace HighamBench

theorem p17_t1_centered_error_probability_bound
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17VarianceRecursiveSumRun m Ω)
    (hsum : p17ExactSum run.a ≠ 0)
    (hsecond :
      p17Expectation run.probability
          (fun ω =>
            p17CenteredSummationError
                run.toP17LimitedPrecisionRecursiveSumRun ω ^ 2) ≤
        (∑ i, |run.a i|) ^ 2 *
          p17Gamma m ((p17UnitRoundoff run.p) ^ 2))
    (lambda : ℝ) (hlambda_pos : 0 < lambda) (hlambda_lt_one : lambda < 1) :
    1 - lambda ≤
      p17EventProb run.probability {ω |
        |p17CenteredSummationError
            run.toP17LimitedPrecisionRecursiveSumRun ω| ≤
          (∑ i, |run.a i|) *
            Real.sqrt
              (p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda)} := by
  -- PROOF_START P17-T1-H001
  classical
  rcases m with _ | m
  · simp [p17CenteredSummationError, p17RecursiveCoefficient,
      p17SuffixErrorProduct, p17EventProb, p17Gamma]
    rw [run.probability.prob_sum]
    exact le_add_of_nonneg_right hlambda_pos.le
  · let P : NumStability.FiniteProbability Ω :=
      { prob := run.probability.prob
        prob_nonneg := run.probability.prob_nonneg
        prob_sum := run.probability.prob_sum }
    let X : Ω → ℝ := fun ω =>
      p17CenteredSummationError
        run.toP17LimitedPrecisionRecursiveSumRun ω
    let S : ℝ := ∑ i, |run.a i|
    let G : ℝ := p17Gamma (m + 1) ((p17UnitRoundoff run.p) ^ 2)
    have hS_nonneg : 0 ≤ S := by
      exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
    have hS_pos : 0 < S := by
      have habs_sum : |p17ExactSum run.a| ≤ S := by
        simpa [p17ExactSum, S] using
          (Finset.abs_sum_le_sum_abs (fun i : Fin (m + 2) => run.a i)
            Finset.univ)
      have hexact_pos : 0 < |p17ExactSum run.a| := abs_pos.mpr hsum
      exact lt_of_lt_of_le hexact_pos habs_sum
    have hu_pos : 0 < (p17UnitRoundoff run.p) ^ 2 := by
      apply sq_pos_of_pos
      simp only [p17UnitRoundoff]
      positivity
    have hG_pos : 0 < G := by
      simp only [G, p17Gamma]
      have hbase : 1 < 1 + (p17UnitRoundoff run.p) ^ 2 := by linarith
      have hpow : 1 < (1 + (p17UnitRoundoff run.p) ^ 2) ^ (m + 1) := by
        exact one_lt_pow₀ hbase (Nat.succ_ne_zero m)
      linarith
    have hratio_pos : 0 < G / lambda := div_pos hG_pos hlambda_pos
    have heta_pos : 0 < S * Real.sqrt (G / lambda) :=
      mul_pos hS_pos (Real.sqrt_pos.2 hratio_pos)
    have hmoment :
        P.expectationReal (fun ω => |X ω| ^ 2) /
            (S * Real.sqrt (G / lambda)) ^ 2 ≤ lambda := by
      have hsecond' : P.expectationReal (fun ω => X ω ^ 2) ≤ S ^ 2 * G := by
        simpa [P, X, S, G, NumStability.FiniteProbability.expectationReal] using
          hsecond
      have hsquare :
          (S * Real.sqrt (G / lambda)) ^ 2 = S ^ 2 * (G / lambda) := by
        rw [mul_pow, Real.sq_sqrt (le_of_lt hratio_pos)]
      rw [hsquare]
      have hden_pos : 0 < S ^ 2 * (G / lambda) :=
        mul_pos (sq_pos_of_pos hS_pos) hratio_pos
      rw [div_le_iff₀ hden_pos]
      calc
        P.expectationReal (fun ω => |X ω| ^ 2)
            = P.expectationReal (fun ω => X ω ^ 2) := by
                congr 1
                funext ω
                exact sq_abs (X ω)
        _ ≤ S ^ 2 * G := hsecond'
        _ = lambda * (S ^ 2 * (G / lambda)) := by
              field_simp
    have hprob :=
      NumStability.FiniteProbability.eventProb_le_ge_one_sub_expectationReal_sq_div
        P (fun ω => |X ω|) (S * Real.sqrt (G / lambda))
        (fun ω => abs_nonneg _) heta_pos
    have hmain :
        1 - lambda ≤
          P.eventProb {ω | |X ω| ≤ S * Real.sqrt (G / lambda)} := by
      exact (sub_le_sub_left hmoment 1).trans hprob
    simpa [P, X, S, G, NumStability.FiniteProbability.eventProb,
      p17EventProb] using hmain

end HighamBench
