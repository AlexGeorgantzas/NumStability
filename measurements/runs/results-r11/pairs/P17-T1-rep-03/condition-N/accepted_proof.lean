import HighamBench.P17Definitions

namespace HighamBench

private theorem p17_finite_second_moment_bound
    {Ω : Type*} [Fintype Ω]
    (P : P17FiniteProbability Ω) (X : Ω → ℝ)
    (c lambda : ℝ) (hc : 0 ≤ c) (hlambda : 0 < lambda)
    (hsecond : p17Expectation P (fun ω => X ω ^ 2) ≤ lambda * c ^ 2) :
    1 - lambda ≤ p17EventProb P {ω | |X ω| ≤ c} := by
  classical
  let bad : Set Ω := {ω | c < |X ω|}
  have hsplit :
      p17EventProb P {ω | |X ω| ≤ c} + p17EventProb P bad = 1 := by
    rw [p17EventProb, p17EventProb, ← P.prob_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases hgood : |X ω| ≤ c
    · have hnotbad : ¬c < |X ω| := not_lt_of_ge hgood
      simp [bad, hgood, hnotbad]
    · have hbad : c < |X ω| := lt_of_not_ge hgood
      simp [bad, hgood, hbad]
  by_cases hc_zero : c = 0
  · have hexpect_nonneg :
        0 ≤ p17Expectation P (fun ω => X ω ^ 2) := by
      rw [p17Expectation]
      exact Finset.sum_nonneg fun ω hω =>
        mul_nonneg (P.prob_nonneg ω) (sq_nonneg (X ω))
    have hexpect_zero :
        p17Expectation P (fun ω => X ω ^ 2) = 0 := by
      apply le_antisymm
      · simpa [hc_zero] using hsecond
      · exact hexpect_nonneg
    have hterm_zero : ∀ ω : Ω, P.prob ω * X ω ^ 2 = 0 := by
      have hsum_zero : ∑ ω : Ω, P.prob ω * X ω ^ 2 = 0 := by
        simpa [p17Expectation] using hexpect_zero
      have hall :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun ω (_ : ω ∈ (Finset.univ : Finset Ω)) =>
            mul_nonneg (P.prob_nonneg ω) (sq_nonneg (X ω)))).mp hsum_zero
      intro ω
      exact hall ω (Finset.mem_univ ω)
    have hbad_zero : p17EventProb P bad = 0 := by
      rw [p17EventProb]
      apply Finset.sum_eq_zero
      intro ω hω
      by_cases hωbad : c < |X ω|
      · have habs_pos : 0 < |X ω| := by simpa [hc_zero] using hωbad
        have hx_sq_ne : X ω ^ 2 ≠ 0 :=
          pow_ne_zero 2 (abs_pos.mp habs_pos)
        have hp_zero : P.prob ω = 0 :=
          (mul_eq_zero.mp (hterm_zero ω)).resolve_right hx_sq_ne
        simp [bad, hωbad, hp_zero]
      · simp [bad, hωbad]
    rw [hbad_zero, add_zero] at hsplit
    rw [hsplit]
    linarith
  · have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc_zero)
    have hc_sq_pos : 0 < c ^ 2 := sq_pos_of_pos hc_pos
    have hmarkov :
        c ^ 2 * p17EventProb P bad ≤
          p17Expectation P (fun ω => X ω ^ 2) := by
      rw [p17EventProb, p17Expectation, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro ω hω
      by_cases hωbad : c < |X ω|
      · have hsquares : c ^ 2 ≤ |X ω| ^ 2 :=
          (sq_le_sq₀ hc (abs_nonneg (X ω))).2 (le_of_lt hωbad)
        calc
          c ^ 2 * (if ω ∈ bad then P.prob ω else 0) =
              P.prob ω * c ^ 2 := by simp [bad, hωbad, mul_comm]
          _ ≤ P.prob ω * |X ω| ^ 2 :=
              mul_le_mul_of_nonneg_left hsquares (P.prob_nonneg ω)
          _ = P.prob ω * X ω ^ 2 := by rw [sq_abs]
      · simp [bad, hωbad, mul_nonneg (P.prob_nonneg ω) (sq_nonneg (X ω))]
    have hbad_le : p17EventProb P bad ≤ lambda := by
      nlinarith
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
  let s : ℝ := ∑ i, |run.a i|
  let g : ℝ := p17Gamma m ((p17UnitRoundoff run.p) ^ 2)
  let X : Ω → ℝ := fun ω =>
    p17CenteredSummationError
      run.toP17LimitedPrecisionRecursiveSumRun ω
  let c : ℝ := s * Real.sqrt (g / lambda)
  have hs : 0 ≤ s := by
    dsimp [s]
    exact Finset.sum_nonneg fun i hi => abs_nonneg (run.a i)
  have hg : 0 ≤ g := by
    dsimp [g, p17Gamma]
    have hbase : (1 : ℝ) ≤ 1 + (p17UnitRoundoff run.p) ^ 2 := by
      nlinarith [sq_nonneg (p17UnitRoundoff run.p)]
    have hpow : (1 : ℝ) ≤ (1 + (p17UnitRoundoff run.p) ^ 2) ^ m :=
      one_le_pow₀ hbase
    linarith
  have hc : 0 ≤ c := by
    exact mul_nonneg hs (Real.sqrt_nonneg (g / lambda))
  have hsqrt_sq : Real.sqrt (g / lambda) ^ 2 = g / lambda := by
    exact Real.sq_sqrt (div_nonneg hg (le_of_lt hlambda_pos))
  have hc_sq : c ^ 2 = s ^ 2 * (g / lambda) := by
    dsimp [c]
    rw [mul_pow, hsqrt_sq]
  have hscale : s ^ 2 * g = lambda * c ^ 2 := by
    rw [hc_sq]
    field_simp
  have hsecond' :
      p17Expectation run.probability (fun ω => X ω ^ 2) ≤
        lambda * c ^ 2 := by
    change p17Expectation run.probability
        (fun ω =>
          p17CenteredSummationError
              run.toP17LimitedPrecisionRecursiveSumRun ω ^ 2) ≤
      lambda * c ^ 2
    exact hsecond.trans_eq hscale
  have hbound := p17_finite_second_moment_bound
    run.probability X c lambda hc hlambda_pos hsecond'
  simpa [X, c, s, g] using hbound

end HighamBench
