import HighamBench.P14Definitions

namespace HighamBench

open scoped BigOperators

private def p14RoundCoeff : ℕ → ℝ
  | 0 => 0
  | n + 1 => (n : ℝ) + 2 * p14RoundCoeff n

private lemma p14RoundCoeff_nonneg (n : ℕ) :
    0 ≤ p14RoundCoeff n := by
  induction n with
  | zero => simp [p14RoundCoeff]
  | succ n ih =>
      simp only [p14RoundCoeff]
      positivity

private lemma p14_recursiveSum_rounding_bound
    (fp : StandardAddModel) (hfp : fp.u ≤ 1)
    {n : ℕ} (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) :
    |recursiveSum fp.fl_add n v - ∑ i, v i| ≤
      (n : ℝ) * fp.u * (∑ i, v i) +
        p14RoundCoeff n * fp.u ^ 2 * (∑ i, v i) := by
  induction n with
  | zero => simp [recursiveSum]
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        simpa [recursiveSum, p14RoundCoeff] using
          mul_nonneg fp.u_nonneg (hv (0 : Fin 1))
      · let v' : Fin n → ℝ := fun i => v i.castSucc
        let a : ℝ := recursiveSum fp.fl_add n v'
        let s : ℝ := ∑ i, v' i
        let b : ℝ := v (Fin.last n)
        have hv' : ∀ i, 0 ≤ v' i := fun i => hv i.castSucc
        have hs : 0 ≤ s := Finset.sum_nonneg fun i _ => hv' i
        have hb : 0 ≤ b := hv (Fin.last n)
        have hu : 0 ≤ fp.u := fp.u_nonneg
        have hc : 0 ≤ p14RoundCoeff n := p14RoundCoeff_nonneg n
        have hih : |a - s| ≤
            (n : ℝ) * fp.u * s +
              p14RoundCoeff n * fp.u ^ 2 * s := by
          simpa [a, s, v'] using ih v' hv'
        obtain ⟨δ, hδ, hadd⟩ := fp.model_add a b
        have habs : |a + b| ≤ |a - s| + (s + b) := by
          calc
            |a + b| = |(a - s) + (s + b)| := by ring_nf
            _ ≤ |a - s| + |s + b| := abs_add_le _ _
            _ = |a - s| + (s + b) := by rw [abs_of_nonneg (add_nonneg hs hb)]
        have hstep : |fp.fl_add a b - (s + b)| ≤
            |a - s| + fp.u * (|a - s| + (s + b)) := by
          rw [hadd]
          calc
            |(a + b) * (1 + δ) - (s + b)| =
                |(a - s) + δ * (a + b)| := by
                  congr 1
                  ring
            _ ≤ |a - s| + |δ * (a + b)| := abs_add_le _ _
            _ = |a - s| + |δ| * |a + b| := by rw [abs_mul]
            _ ≤ |a - s| + fp.u * (|a - s| + (s + b)) := by
              gcongr
        rw [recursiveSum, dif_neg hn, Fin.sum_univ_castSucc]
        simp only [Nat.cast_succ]
        change |fp.fl_add a b - (s + b)| ≤
          ((n : ℝ) + 1) * fp.u * (s + b) +
            p14RoundCoeff (n + 1) * fp.u ^ 2 * (s + b)
        rw [p14RoundCoeff]
        calc
          |fp.fl_add a b - (s + b)| ≤
              |a - s| + fp.u * (|a - s| + (s + b)) := hstep
          _ ≤ ((n : ℝ) * fp.u * s +
                  p14RoundCoeff n * fp.u ^ 2 * s) +
                fp.u * (((n : ℝ) * fp.u * s +
                  p14RoundCoeff n * fp.u ^ 2 * s) + (s + b)) := by
              gcongr
          _ ≤ ((n : ℝ) + 1) * fp.u * (s + b) +
                ((n : ℝ) + 2 * p14RoundCoeff n) * fp.u ^ 2 *
                  (s + b) := by
              have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
              have hu2 : fp.u ^ 2 ≤ fp.u := by nlinarith [sq_nonneg fp.u]
              have hu3 : fp.u ^ 3 ≤ fp.u ^ 2 := by
                nlinarith [sq_nonneg fp.u,
                  mul_nonneg (sq_nonneg fp.u) hu,
                  mul_le_mul_of_nonneg_left hfp (sq_nonneg fp.u)]
              nlinarith [mul_nonneg hu hs, mul_nonneg hu hb,
                mul_nonneg (sq_nonneg fp.u) hs,
                mul_nonneg (sq_nonneg fp.u) hb,
                mul_nonneg hc hs, mul_nonneg hc hb,
                mul_nonneg hn0 hs, mul_nonneg hn0 hb]

theorem p14_t1_positive_recursive_sum_relative_error
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (x : Fin n → ℝ)
    (u : ι → ℝ)
    (run : ∀ t, P14BasicSumExecution x (u t))
    (hu : Filter.Tendsto u l (nhds 0)) :
    let exactSum := p14ExpSum x
    0 < exactSum ∧
    (∀ t i,
      |p14ComputedExp (run t) i - Real.exp (x i)| ≤
        u t * Real.exp (x i)) ∧
    (∃ remainder : ι → ℝ,
      remainder =O[l] (fun t => (u t) ^ 2) ∧
      ∀ᶠ t in l,
        |p14BasicSumDelta (run t)| ≤
          (n + 1 : ℝ) * u t * exactSum + |remainder t|) ∧
    ∀ t,
      p14RecursiveComputedExpSum (run t) =
        exactSum + p14BasicSumDelta (run t) := by
  -- PROOF_START P14-T1-H001
  dsimp only
  have hexact : 0 < p14ExpSum x := by
    unfold p14ExpSum
    apply Finset.sum_pos
    · intro i hi
      exact Real.exp_pos (x i)
    · exact Finset.univ_nonempty_iff.mpr ⟨0, hn⟩
  have h_exp_error : ∀ t i,
      |p14ComputedExp (run t) i - Real.exp (x i)| ≤
        u t * Real.exp (x i) := by
    intro t i
    rw [p14ComputedExp]
    calc
      |Real.exp (x i) * (1 + (run t).expError i) - Real.exp (x i)| =
          Real.exp (x i) * |(run t).expError i| := by
            rw [show Real.exp (x i) * (1 + (run t).expError i) -
                Real.exp (x i) = Real.exp (x i) * (run t).expError i by ring,
              abs_mul, abs_of_pos (Real.exp_pos (x i))]
      _ ≤ Real.exp (x i) * u t := by
        gcongr
        exact (run t).expError_le i
      _ = u t * Real.exp (x i) := mul_comm _ _
  have hu_small : ∀ᶠ t in l, u t < 1 :=
    (tendsto_order.1 hu).2 1 zero_lt_one
  let K : ℝ := (n : ℝ) + 2 * p14RoundCoeff n
  let remainder : ι → ℝ := fun t => K * p14ExpSum x * (u t) ^ 2
  have hrem_bigO : remainder =O[l] (fun t => (u t) ^ 2) := by
    simpa [remainder] using
      (Asymptotics.isBigO_refl (fun t => (u t) ^ 2) l).const_mul_left
        (K * p14ExpSum x)
  have hdelta : ∀ᶠ t in l,
      |p14BasicSumDelta (run t)| ≤
        (n + 1 : ℝ) * u t * p14ExpSum x + |remainder t| := by
    filter_upwards [hu_small] with t hut_lt
    let v : Fin n → ℝ := fun i => p14ComputedExp (run t) i
    let s : ℝ := p14ExpSum x
    let sv : ℝ := ∑ i, v i
    have hut : 0 ≤ u t := by
      rw [← (run t).unit_eq]
      exact (run t).fp.u_nonneg
    have hut_le : u t ≤ 1 := le_of_lt hut_lt
    have hs : 0 ≤ s := le_of_lt hexact
    have hv : ∀ i, 0 ≤ v i := by
      intro i
      change 0 ≤ p14ComputedExp (run t) i
      rw [p14ComputedExp]
      apply mul_nonneg (Real.exp_pos (x i)).le
      have hlo : -(u t) ≤ (run t).expError i :=
        (abs_le.mp ((run t).expError_le i)).1
      nlinarith
    have hsv : 0 ≤ sv := Finset.sum_nonneg fun i _ => hv i
    have hsum_error : |sv - s| ≤ u t * s := by
      calc
        |sv - s| =
            |∑ i, (p14ComputedExp (run t) i - Real.exp (x i))| := by
              simp only [sv, v, s, p14ExpSum, Finset.sum_sub_distrib]
        _ ≤ ∑ i, |p14ComputedExp (run t) i - Real.exp (x i)| := by
              simpa using Finset.abs_sum_le_sum_abs
                (fun i : Fin n =>
                  p14ComputedExp (run t) i - Real.exp (x i)) Finset.univ
        _ ≤ ∑ i, u t * Real.exp (x i) := by
              exact Finset.sum_le_sum fun i _ => h_exp_error t i
        _ = u t * s := by
              simp only [s, p14ExpSum, Finset.mul_sum]
    have hsv_upper : sv ≤ (1 + u t) * s := by
      have hle : sv - s ≤ u t * s :=
        le_trans (le_abs_self (sv - s)) hsum_error
      nlinarith
    have hround :
        |p14RecursiveComputedExpSum (run t) - sv| ≤
          (n : ℝ) * u t * sv +
            p14RoundCoeff n * (u t) ^ 2 * sv := by
      have h := p14_recursiveSum_rounding_bound (run t).fp
        (by simpa [(run t).unit_eq] using hut_le) v hv
      simpa [p14RecursiveComputedExpSum, sv, v, (run t).unit_eq] using h
    have htotal :
        |p14RecursiveComputedExpSum (run t) - s| ≤
          (n + 1 : ℝ) * u t * s + K * (u t) ^ 2 * s := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      have hc : 0 ≤ p14RoundCoeff n := p14RoundCoeff_nonneg n
      have hu3 : (u t) ^ 3 ≤ (u t) ^ 2 := by
        nlinarith [sq_nonneg (u t),
          mul_nonneg (sq_nonneg (u t)) hut,
          mul_le_mul_of_nonneg_left hut_le (sq_nonneg (u t))]
      calc
        |p14RecursiveComputedExpSum (run t) - s| ≤
            |p14RecursiveComputedExpSum (run t) - sv| + |sv - s| := by
              rw [show p14RecursiveComputedExpSum (run t) - s =
                  (p14RecursiveComputedExpSum (run t) - sv) + (sv - s) by ring]
              exact abs_add_le _ _
        _ ≤ ((n : ℝ) * u t * sv +
              p14RoundCoeff n * (u t) ^ 2 * sv) + u t * s :=
                add_le_add hround hsum_error
        _ ≤ ((n : ℝ) * u t * ((1 + u t) * s) +
              p14RoundCoeff n * (u t) ^ 2 * ((1 + u t) * s)) +
              u t * s := by
                gcongr
        _ ≤ (n + 1 : ℝ) * u t * s + K * (u t) ^ 2 * s := by
          dsimp only [K]
          nlinarith [mul_nonneg hut hs,
            mul_nonneg (sq_nonneg (u t)) hs,
            mul_nonneg hc hs, mul_nonneg hn0 hs,
            mul_nonneg (mul_nonneg hc (sq_nonneg (u t))) hs]
    change |p14RecursiveComputedExpSum (run t) - p14ExpSum x| ≤ _
    rw [show |remainder t| = K * (u t) ^ 2 * s by
      change |K * p14ExpSum x * (u t) ^ 2| = _
      change |K * s * (u t) ^ 2| = _
      have hK : 0 ≤ K := by
        change 0 ≤ (n : ℝ) + 2 * p14RoundCoeff n
        exact add_nonneg (Nat.cast_nonneg n)
          (mul_nonneg (by norm_num) (p14RoundCoeff_nonneg n))
      rw [abs_of_nonneg
        (mul_nonneg (mul_nonneg hK hs) (sq_nonneg (u t)))]
      ring]
    simpa [s, mul_assoc, mul_left_comm, mul_comm] using htotal
  refine ⟨hexact, h_exp_error, ⟨remainder, hrem_bigO, hdelta⟩, ?_⟩
  intro t
  unfold p14BasicSumDelta
  ring

end HighamBench
