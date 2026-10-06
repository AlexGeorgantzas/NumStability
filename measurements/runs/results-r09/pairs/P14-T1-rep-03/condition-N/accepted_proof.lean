import HighamBench.P14Definitions

namespace HighamBench

open scoped BigOperators

private lemma p14_recursiveSum_error_bound
    (fp : StandardAddModel) {n : ℕ} (v y : Fin n → ℝ)
    (hv : ∀ i, 0 ≤ v i)
    (hy : ∀ i, |y i - v i| ≤ fp.u * v i) :
    |recursiveSum fp.fl_add n y - ∑ i, v i| ≤
      ((1 + fp.u) ^ n - 1) * ∑ i, v i := by
  induction n with
  | zero => simp [recursiveSum]
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        simpa [recursiveSum] using hy (0 : Fin 1)
      · rw [recursiveSum]
        simp only [dif_neg hn]
        obtain ⟨δ, hδ, hadd⟩ := fp.model_add
          (recursiveSum fp.fl_add n (fun i => y i.castSucc)) (y (Fin.last n))
        rw [hadd, Fin.sum_univ_castSucc]
        let S : ℝ := ∑ i : Fin n, v i.castSucc
        let w : ℝ := v (Fin.last n)
        let A : ℝ := recursiveSum fp.fl_add n (fun i => y i.castSucc)
        let z : ℝ := y (Fin.last n)
        let b : ℝ := 1 + fp.u
        have hS : 0 ≤ S := by
          dsimp [S]
          exact Finset.sum_nonneg fun i _ => hv i.castSucc
        have hw : 0 ≤ w := hv (Fin.last n)
        have hu : 0 ≤ fp.u := fp.u_nonneg
        have hb : 1 ≤ b := by dsimp [b]; linarith
        have hcoef : 0 ≤ b ^ n - 1 := sub_nonneg.mpr (one_le_pow₀ hb)
        have hIH : |A - S| ≤ (b ^ n - 1) * S := by
          dsimp [A, S, b]
          exact ih (fun i => v i.castSucc) (fun i => y i.castSucc)
            (fun i => hv i.castSucc) (fun i => hy i.castSucc)
        have hz : |z - w| ≤ fp.u * w := hy (Fin.last n)
        have hA : |A| ≤ b ^ n * S := by
          calc
            |A| = |(A - S) + S| := by ring_nf
            _ ≤ |A - S| + |S| := abs_add_le _ _
            _ ≤ (b ^ n - 1) * S + S := by
              rw [abs_of_nonneg hS]
              gcongr
            _ = b ^ n * S := by ring
        have hzabs : |z| ≤ b * w := by
          calc
            |z| = |(z - w) + w| := by ring_nf
            _ ≤ |z - w| + |w| := abs_add_le _ _
            _ ≤ fp.u * w + w := by
              rw [abs_of_nonneg hw]
              gcongr
            _ = b * w := by simp [b]; ring
        have hAz : |A + z| ≤ b ^ n * S + b * w := by
          calc
            |A + z| ≤ |A| + |z| := abs_add_le _ _
            _ ≤ b ^ n * S + b * w := add_le_add hA hzabs
        have hpow : b ^ 2 ≤ b ^ (n + 1) := by
          exact pow_le_pow_right₀ hb (by omega)
        calc
          |(A + z) * (1 + δ) - (S + w)| =
              |(A - S) + (z - w) + δ * (A + z)| := by ring_nf
          _ ≤ |A - S| + |z - w| + |δ| * |A + z| := by
            calc
              |(A - S) + (z - w) + δ * (A + z)| ≤
                  |(A - S) + (z - w)| + |δ * (A + z)| := abs_add_le _ _
              _ ≤ (|A - S| + |z - w|) + |δ| * |A + z| := by
                rw [abs_mul]
                gcongr
                exact abs_add_le _ _
          _ ≤ (b ^ n - 1) * S + fp.u * w +
                fp.u * (b ^ n * S + b * w) := by
            gcongr
          _ = (b ^ (n + 1) - 1) * S + (b ^ 2 - 1) * w := by
            rw [pow_succ]
            simp [b]
            ring
          _ ≤ (b ^ (n + 1) - 1) * S + (b ^ (n + 1) - 1) * w := by
            gcongr
          _ = (b ^ (n + 1) - 1) * (S + w) := by ring

private lemma p14_pow_remainder_isBigO
    {ι : Type*} {l : Filter ι} (u : ι → ℝ)
    (hu : Filter.Tendsto u l (nhds 0)) (n : ℕ) :
    (fun t => (1 + u t) ^ n - 1 - (n : ℝ) * u t) =O[l]
      (fun t => (u t) ^ 2) := by
  induction n with
  | zero =>
      simpa using (Asymptotics.isBigO_zero (fun t => (u t) ^ 2) l)
  | succ n ih =>
      have hb_tend : Filter.Tendsto (fun t => 1 + u t) l (nhds 1) := by
        simpa using hu.const_add 1
      have hb : (fun t => 1 + u t) =O[l] (fun _ => (1 : ℝ)) :=
        hb_tend.isBigO_one ℝ
      have hmul := ih.mul hb
      have hmul' :
          (fun t => ((1 + u t) ^ n - 1 - (n : ℝ) * u t) * (1 + u t))
            =O[l] (fun t => (u t) ^ 2) := by
        simpa using hmul
      have hsq := Asymptotics.isBigO_refl (fun t => (u t) ^ 2) l
      have hconst : (fun t => (n : ℝ) * (u t) ^ 2) =O[l]
          (fun t => (u t) ^ 2) := hsq.const_mul_left (n : ℝ)
      have hadd := hmul'.add hconst
      apply hadd.congr
      · intro t
        simp only [Nat.cast_add, Nat.cast_one, pow_succ]
        ring
      · intro t
        rfl

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
  dsimp
  have hexact_pos : 0 < p14ExpSum x := by
    unfold p14ExpSum
    refine Finset.sum_pos' (fun i _ => (Real.exp_pos (x i)).le) ?_
    exact ⟨⟨0, hn⟩, Finset.mem_univ _, Real.exp_pos (x ⟨0, hn⟩)⟩
  have hexp_error : ∀ t i,
      |p14ComputedExp (run t) i - Real.exp (x i)| ≤
        u t * Real.exp (x i) := by
    intro t i
    have he := (run t).expError_le i
    have hep : 0 < Real.exp (x i) := Real.exp_pos _
    calc
      |p14ComputedExp (run t) i - Real.exp (x i)| =
          Real.exp (x i) * |(run t).expError i| := by
            rw [p14ComputedExp]
            rw [show Real.exp (x i) * (1 + (run t).expError i) -
                Real.exp (x i) = Real.exp (x i) * (run t).expError i by ring]
            rw [abs_mul, abs_of_pos hep]
      _ ≤ Real.exp (x i) * u t := mul_le_mul_of_nonneg_left he hep.le
      _ = u t * Real.exp (x i) := mul_comm _ _
  have hsum_bound : ∀ t,
      |p14BasicSumDelta (run t)| ≤
        ((1 + u t) ^ n - 1) * p14ExpSum x := by
    intro t
    have h := p14_recursiveSum_error_bound (run t).fp
      (fun i => Real.exp (x i)) (p14ComputedExp (run t))
      (fun i => (Real.exp_pos (x i)).le) (by
        intro i
        rw [(run t).unit_eq]
        exact hexp_error t i)
    rw [(run t).unit_eq] at h
    simpa only [p14BasicSumDelta, p14RecursiveComputedExpSum, p14ExpSum] using h
  let remainder : ι → ℝ := fun t =>
    ((1 + u t) ^ n - 1 - (n : ℝ) * u t) * p14ExpSum x
  refine ⟨hexact_pos, hexp_error, ?_, ?_⟩
  · refine ⟨remainder, ?_, ?_⟩
    · have hO := (p14_pow_remainder_isBigO u hu n).const_mul_left
          (p14ExpSum x)
      apply hO.congr
      · intro t
        dsimp [remainder]
        ring
      · intro t
        rfl
    · filter_upwards [] with t
      have hut : 0 ≤ u t := by
        rw [← (run t).unit_eq]
        exact (run t).fp.u_nonneg
      have hUS : 0 ≤ u t * p14ExpSum x :=
        mul_nonneg hut hexact_pos.le
      have hlin :
          (n : ℝ) * u t * p14ExpSum x ≤
            ((n : ℝ) + 1) * u t * p14ExpSum x := by
        nlinarith
      calc
        |p14BasicSumDelta (run t)| ≤
            ((1 + u t) ^ n - 1) * p14ExpSum x := hsum_bound t
        _ = (n : ℝ) * u t * p14ExpSum x + remainder t := by
          dsimp [remainder]
          ring
        _ ≤ ((n : ℝ) + 1) * u t * p14ExpSum x + |remainder t| :=
          add_le_add hlin (le_abs_self (remainder t))
  · intro t
    dsimp only [p14BasicSumDelta]
    ring

end HighamBench
