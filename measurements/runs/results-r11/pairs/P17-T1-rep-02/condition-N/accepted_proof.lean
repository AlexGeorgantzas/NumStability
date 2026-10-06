import HighamBench.P17Definitions

namespace HighamBench

private theorem p17_second_moment_event_bound
    {Ω : Type*} [Fintype Ω]
    (P : P17FiniteProbability Ω) (X : Ω → ℝ)
    (B t lambda : ℝ)
    (hB : 0 ≤ B) (ht : 0 ≤ t) (hlambda : 0 < lambda)
    (htsq : t ^ 2 = B / lambda)
    (hsecond : p17Expectation P (fun ω => X ω ^ 2) ≤ B) :
    1 - lambda ≤ p17EventProb P {ω | |X ω| ≤ t} := by
  classical
  let outside : Set Ω := {ω | ¬ |X ω| ≤ t}
  have hpartition :
      p17EventProb P {ω | |X ω| ≤ t} +
          p17EventProb P outside = 1 := by
    simp only [p17EventProb, outside, Set.mem_setOf_eq,
      ← Finset.sum_add_distrib]
    calc
      _ = ∑ x, P.prob x := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases h : |X x| ≤ t <;> simp [h]
      _ = 1 := P.prob_sum
  by_cases hBzero : B = 0
  · have htzero : t = 0 := by
      rw [hBzero, zero_div] at htsq
      nlinarith [sq_nonneg t]
    have hexpect_nonneg :
        0 ≤ p17Expectation P (fun ω => X ω ^ 2) := by
      apply Finset.sum_nonneg
      intro ω hω
      exact mul_nonneg (P.prob_nonneg ω) (sq_nonneg (X ω))
    have hexpect_zero :
        p17Expectation P (fun ω => X ω ^ 2) = 0 := by
      apply le_antisymm
      · simpa [hBzero] using hsecond
      · exact hexpect_nonneg
    have hall_terms_zero : ∀ ω, P.prob ω * X ω ^ 2 = 0 := by
      rw [p17Expectation] at hexpect_zero
      have hiff := Finset.sum_eq_zero_iff_of_nonneg
        (s := Finset.univ)
        (f := fun ω => P.prob ω * X ω ^ 2)
        (fun ω hω => mul_nonneg (P.prob_nonneg ω) (sq_nonneg (X ω)))
      exact fun ω => (hiff.mp hexpect_zero) ω (Finset.mem_univ ω)
    have houtside_zero : p17EventProb P outside = 0 := by
      unfold p17EventProb
      apply Finset.sum_eq_zero
      intro ω hω
      by_cases hout : t < |X ω|
      · have hx : X ω ≠ 0 := by
          intro hx
          rw [hx, abs_zero, htzero] at hout
          exact (lt_irrefl 0) hout
        have hp : P.prob ω = 0 :=
          (mul_eq_zero.mp (hall_terms_zero ω)).resolve_right
            (pow_ne_zero 2 hx)
        simp [outside, hout, hp]
      · simp [outside, hout]
    rw [houtside_zero, add_zero] at hpartition
    rw [hpartition]
    linarith
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hBzero)
    have hmarkov :
        t ^ 2 * p17EventProb P outside ≤
          p17Expectation P (fun ω => X ω ^ 2) := by
      simp only [p17EventProb, p17Expectation, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro ω hω
      by_cases hout : t < |X ω|
      · have habs : t < |X ω| := hout
        have hsquare : t ^ 2 ≤ X ω ^ 2 := by
          rw [← sq_abs (X ω)]
          nlinarith [sq_nonneg (|X ω| - t)]
        simpa [outside, hout, mul_comm] using
          (mul_le_mul_of_nonneg_left hsquare (P.prob_nonneg ω))
      · simp [outside, hout]
        exact mul_nonneg (P.prob_nonneg ω) (sq_nonneg (X ω))
    have hquot_pos : 0 < B / lambda := div_pos hBpos hlambda
    have hproduct :
        (B / lambda) * p17EventProb P outside ≤ B := by
      rw [← htsq]
      exact hmarkov.trans hsecond
    have hcancel : B = (B / lambda) * lambda := by
      field_simp
    have houtside_le : p17EventProb P outside ≤ lambda := by
      have hproduct' :
          (B / lambda) * p17EventProb P outside ≤
            (B / lambda) * lambda := by
        rw [← hcancel]
        exact hproduct
      exact le_of_mul_le_mul_left hproduct' hquot_pos
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
  have hsum_nonneg : 0 ≤ ∑ i, |run.a i| :=
    Finset.sum_nonneg fun i hi => abs_nonneg (run.a i)
  have hgamma_nonneg :
      0 ≤ p17Gamma m ((p17UnitRoundoff run.p) ^ 2) := by
    rw [p17Gamma]
    have hbase :
        (1 : ℝ) ≤ 1 + (p17UnitRoundoff run.p) ^ 2 := by
      nlinarith [sq_nonneg (p17UnitRoundoff run.p)]
    have hpow := one_le_pow₀ hbase (n := m)
    linarith
  apply p17_second_moment_event_bound
    run.probability
    (fun ω =>
      p17CenteredSummationError
        run.toP17LimitedPrecisionRecursiveSumRun ω)
    ((∑ i, |run.a i|) ^ 2 *
      p17Gamma m ((p17UnitRoundoff run.p) ^ 2))
    ((∑ i, |run.a i|) *
      Real.sqrt
        (p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda))
    lambda
  · exact mul_nonneg (sq_nonneg _) hgamma_nonneg
  · exact mul_nonneg hsum_nonneg (Real.sqrt_nonneg _)
  · exact hlambda_pos
  · have hquot_nonneg :
        0 ≤ p17Gamma m ((p17UnitRoundoff run.p) ^ 2) / lambda :=
      div_nonneg hgamma_nonneg (le_of_lt hlambda_pos)
    rw [mul_pow, Real.sq_sqrt hquot_nonneg]
    ring
  · exact hsecond

end HighamBench
