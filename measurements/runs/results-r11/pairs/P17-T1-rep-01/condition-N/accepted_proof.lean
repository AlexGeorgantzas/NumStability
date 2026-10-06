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
      simpa [p17CenteredSummationError, p17RecursiveCoefficient,
        p17SuffixErrorProduct, p17Gamma, p17EventProb,
        run.probability.prob_sum] using hlambda_pos.le
  | succ m =>
      let X : Ω → ℝ := fun ω =>
        p17CenteredSummationError
          run.toP17LimitedPrecisionRecursiveSumRun ω
      let S : ℝ := ∑ i, |run.a i|
      let G : ℝ :=
        p17Gamma (m + 1) ((p17UnitRoundoff run.p) ^ 2)
      let B : ℝ := S ^ 2 * G
      let good : Ω → Prop := fun ω =>
        |X ω| ≤ S * Real.sqrt (G / lambda)
      let badProb : ℝ :=
        ∑ ω, if good ω then 0 else run.probability.prob ω

      have hS : 0 < S := by
        have hexact : 0 < |p17ExactSum run.a| := abs_pos.mpr hsum
        have htriangle :
            |p17ExactSum run.a| ≤ ∑ i, |run.a i| := by
          simpa [p17ExactSum] using
            (Finset.abs_sum_le_sum_abs run.a Finset.univ)
        dsimp [S]
        linarith
      have hu : 0 < p17UnitRoundoff run.p := by
        unfold p17UnitRoundoff
        positivity
      have hG : 0 < G := by
        have hu2 : 0 < (p17UnitRoundoff run.p) ^ 2 := sq_pos_of_pos hu
        have hpow :
            1 < (1 + (p17UnitRoundoff run.p) ^ 2) ^ (m + 1) := by
          apply one_lt_pow₀
          · linarith
          · omega
        dsimp [G, p17Gamma]
        linarith
      have hB : 0 < B := by
        dsimp [B]
        positivity
      have hquot_nonneg : 0 ≤ G / lambda := (div_pos hG hlambda_pos).le
      have hthreshold_nonneg :
          0 ≤ S * Real.sqrt (G / lambda) := by positivity
      have hthreshold_sq :
          (S * Real.sqrt (G / lambda)) ^ 2 = B / lambda := by
        rw [mul_pow, Real.sq_sqrt hquot_nonneg]
        dsimp [B]
        ring

      have hpoint (omega : Ω) :
          (if good omega then 0 else run.probability.prob omega) *
              (B / lambda) ≤
            run.probability.prob omega * X omega ^ 2 := by
        by_cases homega : good omega
        · simp only [homega, if_true, zero_mul]
          exact mul_nonneg (run.probability.prob_nonneg omega) (sq_nonneg _)
        · simp only [homega, if_false]
          have hlt :
              S * Real.sqrt (G / lambda) < |X omega| := by
            exact lt_of_not_ge homega
          have hsq :
              (S * Real.sqrt (G / lambda)) ^ 2 < |X omega| ^ 2 :=
            (sq_lt_sq₀ hthreshold_nonneg (abs_nonneg _)).2 hlt
          rw [hthreshold_sq, sq_abs] at hsq
          exact mul_le_mul_of_nonneg_left hsq.le
            (run.probability.prob_nonneg omega)

      have hmarkov :
          badProb * (B / lambda) ≤
            p17Expectation run.probability (fun omega => X omega ^ 2) := by
        dsimp [badProb, p17Expectation]
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun omega _ => hpoint omega
      have hsecond' :
          p17Expectation run.probability (fun omega => X omega ^ 2) ≤ B := by
        simpa [X, S, G, B] using hsecond
      have hbad_times : badProb * (B / lambda) ≤ B :=
        hmarkov.trans hsecond'
      have hquot_pos : 0 < B / lambda := div_pos hB hlambda_pos
      have hbad : badProb ≤ lambda := by
        apply le_of_mul_le_mul_right _ hquot_pos
        calc
          badProb * (B / lambda) ≤ B := hbad_times
          _ = lambda * (B / lambda) := by field_simp

      have hpartition :
          p17EventProb run.probability {omega | good omega} + badProb = 1 := by
        rw [← run.probability.prob_sum]
        dsimp [p17EventProb, badProb]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro omega homega
        by_cases hgood : good omega <;> simp [hgood]

      change 1 - lambda ≤
        p17EventProb run.probability {omega | good omega}
      linarith

end HighamBench
