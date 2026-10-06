import HighamBench.P14Definitions

namespace HighamBench

open scoped BigOperators

private def p14PowRemainder : ℕ → ℝ → ℝ
  | 0, _ => 0
  | k + 1, z => (k : ℝ) + (1 + z) * p14PowRemainder k z

private lemma p14_one_add_pow_expansion (k : ℕ) (z : ℝ) :
    (1 + z) ^ k - 1 = (k : ℝ) * z + z ^ 2 * p14PowRemainder k z := by
  induction k with
  | zero => simp [p14PowRemainder]
  | succ k ih =>
      rw [pow_succ, show (1 + z) ^ k = ((1 + z) ^ k - 1) + 1 by ring, ih]
      simp only [p14PowRemainder, Nat.cast_add, Nat.cast_one]
      ring

private lemma p14PowRemainder_continuous (k : ℕ) :
    Continuous (p14PowRemainder k) := by
  induction k with
  | zero => exact continuous_const
  | succ k ih =>
      simp only [p14PowRemainder]
      fun_prop

private lemma p14_recursiveSum_error_bound
    {m : ℕ} (hm : 0 < m) (fp : StandardAddModel)
    (a v : Fin m → ℝ)
    (ha : ∀ i, 0 ≤ a i)
    (hv : ∀ i, |v i - a i| ≤ fp.u * a i) :
    |recursiveSum fp.fl_add m v - ∑ i, a i| ≤
      ((1 + fp.u) ^ m - 1) * ∑ i, a i := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hm0 : m = 0
      · subst m
        simpa [recursiveSum] using hv (0 : Fin 1)
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
        let A : ℝ := ∑ i : Fin m, a i.castSucc
        let B : ℝ := a (Fin.last m)
        let R : ℝ := recursiveSum fp.fl_add m (fun i => v i.castSucc)
        let W : ℝ := v (Fin.last m)
        let q : ℝ := (1 + fp.u) ^ m
        have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => ha i.castSucc
        have hB : 0 ≤ B := ha (Fin.last m)
        have hu0 : 0 ≤ fp.u := fp.u_nonneg
        have hbase : 1 ≤ 1 + fp.u := by linarith
        have hq : 1 + fp.u ≤ q := by
          dsimp [q]
          simpa only [pow_one] using
            (pow_le_pow_right₀ hbase (show 1 ≤ m by omega))
        have hRerr : |R - A| ≤ (q - 1) * A := by
          dsimp [R, A, q]
          apply ih hmpos (fun i => a i.castSucc) (fun i => v i.castSucc)
          · exact fun i => ha i.castSucc
          · exact fun i => hv i.castSucc
        have hWerr : |W - B| ≤ fp.u * B := by
          exact hv (Fin.last m)
        have hR : |R| ≤ q * A := by
          calc
            |R| = |(R - A) + A| := by ring
            _ ≤ |R - A| + |A| := abs_add_le _ _
            _ ≤ (q - 1) * A + A := by
              gcongr
              exact abs_of_nonneg hA |>.le
            _ = q * A := by ring
        have hWsmall : |W| ≤ (1 + fp.u) * B := by
          calc
            |W| = |(W - B) + B| := by ring
            _ ≤ |W - B| + |B| := abs_add_le _ _
            _ ≤ fp.u * B + B := by
              gcongr
              exact abs_of_nonneg hB |>.le
            _ = (1 + fp.u) * B := by ring
        have hW : |W| ≤ q * B :=
          hWsmall.trans (mul_le_mul_of_nonneg_right hq hB)
        obtain ⟨δ, hδ, hfl⟩ := fp.model_add R W
        rw [recursiveSum, dif_neg hm0, show
          recursiveSum fp.fl_add m (fun i => v i.castSucc) = R by rfl,
          show v (Fin.last m) = W by rfl, hfl, Fin.sum_univ_castSucc,
          show (∑ i : Fin m, a i.castSucc) = A by rfl,
          show a (Fin.last m) = B by rfl, pow_succ]
        have hadd : |R + W| ≤ q * (A + B) := by
          calc
            |R + W| ≤ |R| + |W| := abs_add_le _ _
            _ ≤ q * A + q * B := add_le_add hR hW
            _ = q * (A + B) := by ring
        have hround : |δ * (R + W)| ≤ fp.u * (q * (A + B)) := by
          rw [abs_mul]
          exact mul_le_mul hδ hadd (abs_nonneg _) hu0
        have htotal :
            |(R + W) * (1 + δ) - (A + B)| ≤
              (q - 1) * A + fp.u * B + fp.u * (q * (A + B)) := by
          calc
            |(R + W) * (1 + δ) - (A + B)| =
                |(R - A) + (W - B) + δ * (R + W)| := by ring
            _ ≤ |R - A| + |W - B| + |δ * (R + W)| :=
              abs_add_three _ _ _
            _ ≤ (q - 1) * A + fp.u * B + fp.u * (q * (A + B)) :=
              add_le_add (add_le_add hRerr hWerr) hround
        calc
          |(R + W) * (1 + δ) - (A + B)| ≤
              (q - 1) * A + fp.u * B + fp.u * (q * (A + B)) := htotal
          _ ≤ (q * (1 + fp.u) - 1) * (A + B) := by
            nlinarith

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
  have hexact_pos : 0 < p14ExpSum x := by
    unfold p14ExpSum
    apply Finset.sum_pos (fun i _ => Real.exp_pos (x i))
    exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  refine ⟨hexact_pos, ?_, ?_, ?_⟩
  · intro t i
    unfold p14ComputedExp
    rw [mul_add, mul_one]
    simp only [add_sub_cancel_left, abs_mul, abs_of_pos (Real.exp_pos (x i))]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right ((run t).expError_le i) (Real.exp_pos (x i)).le
  · let remainder : ι → ℝ := fun t =>
      p14ExpSum x * (u t) ^ 2 * p14PowRemainder n (u t)
    refine ⟨remainder, ?_, ?_⟩
    · have hpoly :
          (fun t => p14PowRemainder n (u t)) =O[l] (fun _ => (1 : ℝ)) := by
        apply Filter.Tendsto.isBigO_one ℝ
        exact (p14PowRemainder_continuous n).continuousAt.tendsto.comp hu
      have hsquare :
          (fun t => (u t) ^ 2 * p14PowRemainder n (u t)) =O[l]
            (fun t => (u t) ^ 2) := by
        simpa using (Asymptotics.isBigO_refl (fun t => (u t) ^ 2) l).mul hpoly
      simpa [remainder, mul_assoc] using hsquare.const_mul_left (p14ExpSum x)
    · have hu_nonneg : ∀ t, 0 ≤ u t := fun t => by
        rw [← (run t).unit_eq]
        exact (run t).fp.u_nonneg
      have hu_event : ∀ᶠ t in l, u t ≤ 1 := by
        have : ∀ᶠ t in l, u t ∈ Set.Iic (1 : ℝ) :=
          (hu.eventually
            (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : 0 < (1 : ℝ)))).mono
              (by
                intro y hy
                simp only [Real.dist_0_eq_abs] at hy
                exact (le_abs_self (u y)).trans (le_of_lt hy))
        exact this
      filter_upwards [hu_event] with t hut
      have hsum := p14_recursiveSum_error_bound (fp := (run t).fp)
        hn (fun i => Real.exp (x i)) (fun i => p14ComputedExp (run t) i)
        (fun i => (Real.exp_pos (x i)).le) (fun i => by
          change |Real.exp (x i) * (1 + (run t).expError i) - Real.exp (x i)| ≤
            (run t).fp.u * Real.exp (x i)
          rw [(run t).unit_eq]
          rw [mul_add, mul_one]
          simp only [add_sub_cancel_left, abs_mul, abs_of_pos (Real.exp_pos (x i))]
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right ((run t).expError_le i)
            (Real.exp_pos (x i)).le)
      rw [(run t).unit_eq] at hsum
      unfold p14BasicSumDelta p14RecursiveComputedExpSum p14ExpSum
      change |recursiveSum (run t).fp.fl_add n (p14ComputedExp (run t)) -
          ∑ i, Real.exp (x i)| ≤ _
      calc
        |recursiveSum (run t).fp.fl_add n (p14ComputedExp (run t)) -
            ∑ i, Real.exp (x i)| ≤
            ((1 + u t) ^ n - 1) * ∑ i, Real.exp (x i) := hsum
        _ = ((n : ℝ) * u t + (u t) ^ 2 * p14PowRemainder n (u t)) *
              ∑ i, Real.exp (x i) := by rw [p14_one_add_pow_expansion]
        _ ≤ (n + 1 : ℝ) * u t * ∑ i, Real.exp (x i) + |remainder t| := by
          dsimp [remainder]
          have hS : 0 ≤ ∑ i, Real.exp (x i) := hexact_pos.le
          have hu0 := hu_nonneg t
          have hleabs :
              (u t) ^ 2 * p14PowRemainder n (u t) ≤
                |(u t) ^ 2 * p14PowRemainder n (u t)| := le_abs_self _
          have hrem :
              (u t) ^ 2 * p14PowRemainder n (u t) ≤
                (u t) ^ 2 * |p14PowRemainder n (u t)| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) (sq_nonneg (u t))
          rw [show p14ExpSum x = ∑ i, Real.exp (x i) by rfl,
            abs_mul, abs_mul, abs_of_nonneg hS, abs_of_nonneg (sq_nonneg (u t))]
          nlinarith [mul_le_mul_of_nonneg_right hrem hS, mul_nonneg hu0 hS]
  · intro t
    unfold p14BasicSumDelta
    ring

end HighamBench
