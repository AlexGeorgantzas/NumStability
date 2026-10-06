import HighamBench.P17Definitions

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
  cases m with
  | zero =>
      simp [p17CenteredSummationError, p17RecursiveCoefficient,
        p17SuffixErrorProduct, p17EventProb, p17Gamma,
        run.probability.prob_sum]
      exact le_of_lt hlambda_pos
  | succ n =>
      let X : Ω → ℝ := fun ω =>
        p17CenteredSummationError
          run.toP17LimitedPrecisionRecursiveSumRun ω
      let A : ℝ := ∑ i, |run.a i|
      let G : ℝ :=
        p17Gamma (n + 1) ((p17UnitRoundoff run.p) ^ 2)
      let t : ℝ := A * Real.sqrt (G / lambda)
      have hu : 0 < p17UnitRoundoff run.p := by
        simp [p17UnitRoundoff]
      have hG : 0 < G := by
        dsimp [G, p17Gamma]
        have hb : 1 < 1 + (p17UnitRoundoff run.p) ^ 2 := by
          nlinarith [sq_pos_of_pos hu]
        have hp : 1 <
            (1 + (p17UnitRoundoff run.p) ^ 2) ^ (n + 1) := by
          exact one_lt_pow₀ hb (by omega)
        linarith
      have hA : 0 < A := by
        have habs_sum :
            |p17ExactSum run.a| ≤ ∑ i, |run.a i| := by
          simpa [p17ExactSum] using
            (Finset.abs_sum_le_sum_abs (f := run.a) Finset.univ)
        have hexact_abs : 0 < |p17ExactSum run.a| := abs_pos.mpr hsum
        exact lt_of_lt_of_le hexact_abs habs_sum
      have ht : 0 < t := by
        dsimp [t]
        exact mul_pos hA (Real.sqrt_pos.2 (div_pos hG hlambda_pos))
      have hscale :
          A ^ 2 * G = lambda * t ^ 2 := by
        dsimp [t]
        rw [mul_pow, Real.sq_sqrt (div_nonneg (le_of_lt hG)
          (le_of_lt hlambda_pos))]
        field_simp
      have hmoment :
          p17Expectation run.probability (fun ω => X ω ^ 2) ≤
            lambda * t ^ 2 := by
        dsimp [X, A, G] at hsecond ⊢
        rw [← hscale]
        exact hsecond
      have htail :
          p17EventProb run.probability {ω | t < |X ω|} ≤ lambda := by
        have hweighted :
            t ^ 2 * p17EventProb run.probability {ω | t < |X ω|} ≤
              p17Expectation run.probability (fun ω => X ω ^ 2) := by
          unfold p17EventProb p17Expectation
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro ω _
          by_cases hω : t < |X ω|
          · simp only [Set.mem_setOf_eq, if_pos hω]
            rw [mul_comm]
            apply mul_le_mul_of_nonneg_left _ (run.probability.prob_nonneg ω)
            nlinarith [sq_abs (X ω)]
          · simp only [Set.mem_setOf_eq, if_neg hω, mul_zero]
            exact mul_nonneg (run.probability.prob_nonneg ω) (sq_nonneg (X ω))
        nlinarith [sq_pos_of_pos ht]
      have hpartition :
          p17EventProb run.probability {ω | |X ω| ≤ t} =
            1 - p17EventProb run.probability {ω | t < |X ω|} := by
        unfold p17EventProb
        rw [← run.probability.prob_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro ω _
        simp only [Set.mem_setOf_eq]
        by_cases hω : |X ω| ≤ t
        · simp [hω, not_lt.mpr hω]
        · have hω' : t < |X ω| := lt_of_not_ge hω
          simp [hω, hω']
      change 1 - lambda ≤
        p17EventProb run.probability {ω | |X ω| ≤ t}
      rw [hpartition]
      linarith

end HighamBench
