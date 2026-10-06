import HighamBench.P17Definitions

namespace HighamBench

private lemma p17_finite_chebyshev_of_second_moment
    {Ω : Type*} [Fintype Ω]
    (P : P17FiniteProbability Ω) (X : Ω → ℝ)
    (t lambda : ℝ) (ht : 0 ≤ t) (hlambda : 0 < lambda)
    (hsecond :
      p17Expectation P (fun ω => X ω ^ 2) ≤ lambda * t ^ 2) :
    1 - lambda ≤ p17EventProb P {ω | |X ω| ≤ t} := by
  classical
  have hmoment_nonneg :
      0 ≤ p17Expectation P (fun ω => X ω ^ 2) := by
    rw [p17Expectation]
    exact Finset.sum_nonneg fun ω _ =>
      mul_nonneg (P.prob_nonneg ω) (sq_nonneg (X ω))
  have hpartition :
      p17EventProb P {ω | |X ω| ≤ t} +
          p17EventProb P {ω | t < |X ω|} = 1 := by
    rw [p17EventProb, p17EventProb, ← Finset.sum_add_distrib,
      ← P.prob_sum]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hω : |X ω| ≤ t
    · have hω' : ¬t < |X ω| := not_lt_of_ge hω
      simp [hω, hω']
    · have hω' : t < |X ω| := lt_of_not_ge hω
      simp [hω, hω']
  have hbad : p17EventProb P {ω | t < |X ω|} ≤ lambda := by
    rcases ht.eq_or_lt with rfl | ht_pos
    · have hmoment_zero :
          p17Expectation P (fun ω => X ω ^ 2) = 0 := by
        apply le_antisymm
        · simpa using hsecond
        · exact hmoment_nonneg
      have hterm_zero (ω : Ω) : P.prob ω * X ω ^ 2 = 0 := by
        exact
          (Finset.sum_eq_zero_iff_of_nonneg
              (fun ξ (_ : ξ ∈ Finset.univ) =>
                mul_nonneg (P.prob_nonneg ξ) (sq_nonneg (X ξ)))).mp
            (by simpa [p17Expectation] using hmoment_zero) ω
            (Finset.mem_univ ω)
      have hbad_zero : p17EventProb P {ω | 0 < |X ω|} = 0 := by
        rw [p17EventProb]
        apply Finset.sum_eq_zero
        intro ω _
        by_cases hω : 0 < |X ω|
        · have hx : X ω ≠ 0 := (abs_pos.mp hω)
          have hp : P.prob ω = 0 :=
            (mul_eq_zero.mp (hterm_zero ω)).resolve_right (pow_ne_zero 2 hx)
          simp [hx, hp]
        · have hx : X ω = 0 := by
            apply abs_eq_zero.mp
            exact le_antisymm (le_of_not_gt hω) (abs_nonneg (X ω))
          simp [hx]
      rw [hbad_zero]
      exact le_of_lt hlambda
    · have hscaled :
          t ^ 2 * p17EventProb P {ω | t < |X ω|} ≤
            p17Expectation P (fun ω => X ω ^ 2) := by
        rw [p17EventProb, p17Expectation, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro ω _
        by_cases hω : t < |X ω|
        · have hsquare : t ^ 2 ≤ X ω ^ 2 := by
            nlinarith [sq_abs (X ω)]
          simpa [hω, mul_comm, mul_left_comm, mul_assoc] using
            mul_le_mul_of_nonneg_left hsquare (P.prob_nonneg ω)
        · simp [hω, mul_nonneg (P.prob_nonneg ω) (sq_nonneg (X ω))]
      have hscaled' :
          t ^ 2 * p17EventProb P {ω | t < |X ω|} ≤
            lambda * t ^ 2 := hscaled.trans hsecond
      nlinarith [sq_pos_of_pos ht_pos]
  linarith

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
  have hsum_abs : 0 ≤ ∑ i, |run.a i| :=
    Finset.sum_nonneg fun i _ => abs_nonneg (run.a i)
  have hgamma :
      0 ≤ p17Gamma m ((p17UnitRoundoff run.p) ^ 2) := by
    simp only [p17Gamma]
    have hbase : (1 : ℝ) ≤ 1 + (p17UnitRoundoff run.p) ^ 2 := by
      exact le_add_of_nonneg_right (sq_nonneg _)
    exact sub_nonneg.mpr (one_le_pow₀ hbase)
  have hquot :
      0 ≤ p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda :=
    div_nonneg hgamma hlambda_pos.le
  have hthreshold :
      0 ≤ (∑ i, |run.a i|) *
        Real.sqrt
          (p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda) :=
    mul_nonneg hsum_abs (Real.sqrt_nonneg _)
  have hsqrt_sq :
      (Real.sqrt
          (p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda)) ^ 2 =
        p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda :=
    Real.sq_sqrt hquot
  have hscale :
      lambda *
          ((∑ i, |run.a i|) *
            Real.sqrt
              (p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda)) ^ 2 =
        (∑ i, |run.a i|) ^ 2 *
          p17Gamma m ((p17UnitRoundoff run.p) ^ 2) := by
    rw [mul_pow, hsqrt_sq]
    field_simp [ne_of_gt hlambda_pos]
  apply p17_finite_chebyshev_of_second_moment
    run.probability
    (fun ω =>
      p17CenteredSummationError
        run.toP17LimitedPrecisionRecursiveSumRun ω)
    ((∑ i, |run.a i|) *
      Real.sqrt
        (p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda))
    lambda hthreshold hlambda_pos
  rw [hscale]
  exact hsecond

end HighamBench
