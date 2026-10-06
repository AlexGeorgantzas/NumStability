import NumStability.Algorithms.Summation.Recursive.Core
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace HighamBenchCandidate

open NumStability

/-- The exact, unshifted log-sum-exp value. -/
noncomputable def exactLogSumExp (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  Real.log (∑ i : Fin n, Real.exp (x i))

/-- The log-sum-exp output of Algorithm 3.1, with one relative-error
witness for each exponential evaluation and one for the final logarithm.
The additions are performed by the actual left-to-right rounded sum. -/
noncomputable def basicLogSumExpOutput
    (fp : FPModel) (n : ℕ) (x : Fin n → ℝ)
    (expError : Fin n → ℝ) (logError : ℝ) : ℝ :=
  Real.log
    (fl_recursiveSum fp n
      (fun i => Real.exp (x i) * (1 + expError i))) *
    (1 + logError)

private lemma log_error_of_relative
    {s t a : ℝ} (hs : 0 < s) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (herr : |t - s| ≤ a * s) :
    |Real.log t - Real.log s| ≤ a / (1 - a) := by
  have hden : 0 < 1 - a := by linarith
  have hlow : (1 - a) * s ≤ t := by
    have := (abs_le.mp herr).1
    nlinarith
  have ht : 0 < t := lt_of_lt_of_le (mul_pos hden hs) hlow
  have hupper : Real.log t - Real.log s ≤ a := by
    have h := Real.log_le_sub_one_of_pos (div_pos ht hs)
    rw [Real.log_div (ne_of_gt ht) (ne_of_gt hs)] at h
    have hd : (t - s) / s ≤ a := by
      apply (div_le_iff₀ hs).2
      exact (abs_le.mp herr).2
    have heq : t / s - 1 = (t - s) / s := by field_simp
    linarith
  have hrev : Real.log s - Real.log t ≤ a / (1 - a) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hs ht)
    rw [Real.log_div (ne_of_gt hs) (ne_of_gt ht)] at h
    have hd : (s - t) / t ≤ a / (1 - a) := by
      apply (div_le_iff₀ ht).2
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hden).2
      have hneg := (abs_le.mp herr).1
      nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hlow),
        mul_nonneg (le_of_lt hden) (by nlinarith : 0 ≤ a * s - (s - t))]
    have heq : s / t - 1 = (s - t) / t := by field_simp
    linarith
  have hua : a ≤ a / (1 - a) := by
    apply (le_div_iff₀ hden).2
    nlinarith
  exact abs_le.mpr ⟨by linarith, hupper.trans hua⟩

private lemma basic_sum_error
    (fp : FPModel) (n : ℕ) (x : Fin n → ℝ)
    (d : Fin n → ℝ) (hd : ∀ i, |d i| ≤ fp.u)
    (hu : fp.u ≤ 1) (hvalid : gammaValid fp (n - 1)) :
    let s := ∑ i : Fin n, Real.exp (x i)
    let t := fl_recursiveSum fp n (fun i => Real.exp (x i) * (1 + d i))
    |t - s| ≤ (fp.u + (1 + fp.u) * gamma fp (n - 1)) * s := by
  dsimp
  let e : Fin n → ℝ := fun i => Real.exp (x i)
  let w : Fin n → ℝ := fun i => e i * (1 + d i)
  let s : ℝ := ∑ i : Fin n, e i
  let sw : ℝ := ∑ i : Fin n, w i
  have hw_nonneg (i : Fin n) : 0 ≤ w i := by
    dsimp [w]
    apply mul_nonneg (le_of_lt (Real.exp_pos _))
    have := (abs_le.mp (hd i)).1
    linarith
  have hsum_exp : |sw - s| ≤ fp.u * s := by
    calc
      |sw - s| = |∑ i : Fin n, (w i - e i)| := by
        rw [Finset.sum_sub_distrib]
      _ ≤ ∑ i : Fin n, |w i - e i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, fp.u * e i := by
        apply Finset.sum_le_sum
        intro i _
        have he : 0 ≤ e i := le_of_lt (Real.exp_pos _)
        have hlocal : w i - e i = e i * d i := by dsimp [w]; ring
        rw [hlocal, abs_mul, abs_of_nonneg he]
        exact mul_le_mul_of_nonneg_left (hd i) he |>.trans_eq (mul_comm _ _)
      _ = fp.u * s := by simp [s, Finset.mul_sum]
  have hsum_w : (∑ i : Fin n, |w i|) ≤ (1 + fp.u) * s := by
    calc
      (∑ i : Fin n, |w i|) = ∑ i : Fin n, w i := by
        apply Finset.sum_congr rfl
        intro i _
        exact abs_of_nonneg (hw_nonneg i)
      _ ≤ ∑ i : Fin n, (1 + fp.u) * e i := by
        apply Finset.sum_le_sum
        intro i _
        dsimp [w]
        have he : 0 ≤ e i := le_of_lt (Real.exp_pos _)
        have := (abs_le.mp (hd i)).2
        nlinarith
      _ = (1 + fp.u) * s := by simp [s, Finset.mul_sum]
  have hgamma : 0 ≤ gamma fp (n - 1) := gamma_nonneg fp hvalid
  have hrec := recursiveSum_forward_error_bound fp n w hvalid
  calc
    |fl_recursiveSum fp n w - s| =
        |(fl_recursiveSum fp n w - sw) + (sw - s)| := by ring
    _ ≤ |fl_recursiveSum fp n w - sw| + |sw - s| := abs_add_le _ _
    _ ≤ gamma fp (n - 1) * (∑ i : Fin n, |w i|) + fp.u * s :=
      add_le_add hrec hsum_exp
    _ ≤ (fp.u + (1 + fp.u) * gamma fp (n - 1)) * s := by
      nlinarith [mul_nonneg hgamma (sub_nonneg.mpr hsum_w)]

private lemma scalar_log_budget (N u : ℝ)
    (hN : 1 ≤ N) (hu : 0 < u) (hsmall : N * u ≤ 1 / 4) :
    let a := N * u / (1 - (N - 1) * u)
    0 ≤ a ∧ a < 1 ∧
      (1 + u) * (a / (1 - a)) ≤ N * u + 6 * N ^ 2 * u ^ 2 := by
  dsimp
  let p : ℝ := N * u
  let q : ℝ := (2 * N - 1) * u
  let a : ℝ := p / (1 - (N - 1) * u)
  have hp : 0 < p := mul_pos (by linarith) hu
  have hq0 : 0 ≤ q := mul_nonneg (by linarith) (le_of_lt hu)
  have hqle : q ≤ 2 * p := by dsimp [p, q]; nlinarith
  have hqhalf : q ≤ 1 / 2 := by nlinarith [hsmall]
  have hd1 : 0 < 1 - (N - 1) * u := by
    dsimp [q] at hqhalf
    nlinarith [mul_nonneg (sub_nonneg.mpr hN) (le_of_lt hu)]
  have hd2 : 0 < 1 - q := by linarith
  have ha0 : 0 ≤ a := div_nonneg (le_of_lt hp) (le_of_lt hd1)
  have ha1 : a < 1 := by
    apply (div_lt_iff₀ hd1).2
    dsimp [a, p, q] at *
    nlinarith
  have haeq : a / (1 - a) = p / (1 - q) := by
    have hdn : 1 - (N - 1) * u ≠ 0 := ne_of_gt hd1
    have hqne : 1 - q ≠ 0 := ne_of_gt hd2
    have han : 1 - p / (1 - (N - 1) * u) ≠ 0 := by
      simpa [a] using (ne_of_gt (sub_pos.mpr ha1))
    have hidentity : q = (N - 1) * u + p := by dsimp [q, p]; ring
    have hdp : 1 - (N - 1) * u - p ≠ 0 := by
      have heq : 1 - (N - 1) * u - p = 1 - q := by linarith
      rw [heq]
      exact hqne
    dsimp [a]
    field_simp [hdn, hqne, han, hdp]
    nlinarith [hidentity]
  have hL1 : p / (1 - q) ≤ p + 2 * p * q := by
    apply (div_le_iff₀ hd2).2
    nlinarith [mul_nonneg (le_of_lt hp)
      (mul_nonneg hq0 (by linarith : 0 ≤ 1 - 2 * q))]
  have hL2 : p / (1 - q) ≤ 2 * p := by
    apply (div_le_iff₀ hd2).2
    nlinarith [mul_nonneg (le_of_lt hp) (by linarith : 0 ≤ 1 - 2 * q)]
  have hquad : 2 * p * q ≤ 4 * p ^ 2 := by
    nlinarith [mul_nonneg (le_of_lt hp) (sub_nonneg.mpr hqle)]
  have hu_le_p : u ≤ p := by dsimp [p]; nlinarith
  have hLnonneg : 0 ≤ p / (1 - q) := div_nonneg (le_of_lt hp) (le_of_lt hd2)
  refine ⟨ha0, ha1, ?_⟩
  rw [haeq]
  have hmul : u * (p / (1 - q)) ≤ 2 * p ^ 2 := by
    nlinarith [mul_nonneg (le_of_lt hu) (sub_nonneg.mpr hL2),
      mul_nonneg (sub_nonneg.mpr hu_le_p) (le_of_lt hp)]
  calc
    (1 + u) * (p / (1 - q)) ≤ p + 6 * p ^ 2 := by nlinarith [hL1, hquad, hmul]
    _ = N * u + 6 * N ^ 2 * u ^ 2 := by dsimp [p]; ring

/-- Absolute forward-error bound immediately preceding Theorem 3.2. The
quadratic remainder is uniform over all admissible executions for fixed
dimension and input. -/
theorem target :
    ∀ (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ),
      ∃ C : ℝ, 0 < C ∧
        ∃ u0 : ℝ, 0 < u0 ∧
          ∀ (fp : FPModel) (expError : Fin n → ℝ) (logError : ℝ),
            0 < fp.u → fp.u ≤ u0 →
            (∀ i : Fin n, |expError i| ≤ fp.u) →
            |logError| ≤ fp.u →
            |exactLogSumExp n x -
                basicLogSumExpOutput fp n x expError logError| ≤
              fp.u * |exactLogSumExp n x| +
                ((n : ℝ) + 1) * fp.u + C * fp.u ^ 2 := by
  intro n hn x
  let N : ℝ := n
  have hN : 1 ≤ N := by
    dsimp [N]
    exact_mod_cast hn
  have hNpos : 0 < N := by linarith
  refine ⟨6 * N ^ 2 + 1, by positivity, 1 / (4 * N), by positivity, ?_⟩
  intro fp d logError hu hcap hd hlogError
  have hsmall : N * fp.u ≤ 1 / 4 := by
    have h4N : 0 < 4 * N := by positivity
    have h := (le_div_iff₀ h4N).1 hcap
    nlinarith
  have hu1 : fp.u ≤ 1 := by
    have : fp.u ≤ N * fp.u := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hN) (le_of_lt hu)]
    linarith
  have hm : ((n - 1 : ℕ) : ℝ) = N - 1 := by
    have hnat : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have hcast : ((n - 1 : ℕ) : ℝ) + 1 = N := by
      dsimp [N]
      exact_mod_cast hnat
    linarith
  have hvalid : gammaValid fp (n - 1) := by
    unfold gammaValid
    rw [hm]
    nlinarith [mul_nonneg (sub_nonneg.mpr hN) (le_of_lt hu)]
  let s : ℝ := ∑ i : Fin n, Real.exp (x i)
  let t : ℝ := fl_recursiveSum fp n
    (fun i => Real.exp (x i) * (1 + d i))
  let a : ℝ := N * fp.u / (1 - (N - 1) * fp.u)
  have hs : 0 < s := by
    dsimp [s]
    have i0 : Fin n := ⟨0, hn⟩
    exact Finset.sum_pos (fun i _ => Real.exp_pos (x i))
      ⟨i0, Finset.mem_univ i0⟩
  obtain ⟨ha0, ha1, hbudget⟩ :=
    scalar_log_budget N fp.u hN hu hsmall
  have hfactor :
      fp.u + (1 + fp.u) * gamma fp (n - 1) = a := by
    dsimp [a]
    rw [gamma, hm]
    have hden : 1 - (N - 1) * fp.u ≠ 0 := by
      apply ne_of_gt
      nlinarith [mul_nonneg (sub_nonneg.mpr hN) (le_of_lt hu)]
    apply (eq_div_iff hden).2
    calc
      (fp.u + (1 + fp.u) *
          ((N - 1) * fp.u / (1 - (N - 1) * fp.u))) *
          (1 - (N - 1) * fp.u) =
        fp.u * (1 - (N - 1) * fp.u) +
          (1 + fp.u) * ((N - 1) * fp.u) := by
            rw [add_mul, mul_assoc, div_mul_cancel₀ _ hden]
      _ = N * fp.u := by ring
  have hsum : |t - s| ≤ a * s := by
    have h := basic_sum_error fp n x d hd hu1 hvalid
    simpa only [t, s, hfactor] using h
  have hlog : |Real.log t - Real.log s| ≤ a / (1 - a) :=
    log_error_of_relative hs ha0 ha1 hsum
  have hlog' : |Real.log s - Real.log t| ≤ a / (1 - a) := by
    rwa [abs_sub_comm]
  have haquot0 : 0 ≤ a / (1 - a) :=
    div_nonneg ha0 (by linarith)
  have hlogfac : |1 + logError| ≤ 1 + fp.u := by
    calc
      |1 + logError| ≤ |(1 : ℝ)| + |logError| := abs_add_le _ _
      _ ≤ 1 + fp.u := by simpa using add_le_add_left hlogError 1
  change |Real.log s - Real.log t * (1 + logError)| ≤
    fp.u * |Real.log s| + (N + 1) * fp.u +
      (6 * N ^ 2 + 1) * fp.u ^ 2
  have heq : Real.log s - Real.log t * (1 + logError) =
      -(Real.log s) * logError +
        (Real.log s - Real.log t) * (1 + logError) := by ring
  rw [heq]
  calc
    |-(Real.log s) * logError +
        (Real.log s - Real.log t) * (1 + logError)| ≤
      |-(Real.log s) * logError| +
        |(Real.log s - Real.log t) * (1 + logError)| := abs_add_le _ _
    _ = |Real.log s| * |logError| +
        |Real.log s - Real.log t| * |1 + logError| := by
          rw [abs_mul, abs_mul, abs_neg]
    _ ≤ |Real.log s| * fp.u +
        (a / (1 - a)) * (1 + fp.u) := by
          gcongr
    _ ≤ fp.u * |Real.log s| + N * fp.u +
        6 * N ^ 2 * fp.u ^ 2 := by
          nlinarith [hbudget]
    _ ≤ fp.u * |Real.log s| + (N + 1) * fp.u +
        (6 * N ^ 2 + 1) * fp.u ^ 2 := by nlinarith [sq_nonneg fp.u]

end HighamBenchCandidate
