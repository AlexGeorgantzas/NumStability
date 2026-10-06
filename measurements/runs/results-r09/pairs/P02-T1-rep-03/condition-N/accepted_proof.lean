import HighamBench.P02Definitions

namespace HighamBench

open scoped BigOperators

private lemma gamma_nonneg {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hv : GammaValid u n) : 0 ≤ gamma u n := by
  unfold GammaValid at hv
  unfold gamma
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

private lemma one_add_gamma_nonneg {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hv : GammaValid u n) : 0 ≤ 1 + gamma u n := by
  have := gamma_nonneg hu hv
  linarith

private lemma gamma_valid_mono {u : ℝ} {m n : ℕ} (hu : 0 ≤ u)
    (hmn : m ≤ n) (hv : GammaValid u n) : GammaValid u m := by
  unfold GammaValid at *
  have hc : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  nlinarith

private lemma gamma_step_high {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hv : GammaValid u (n + 1)) :
    (1 + u) * (1 + gamma u n) ≤ 1 + gamma u (n + 1) := by
  have hvn := gamma_valid_mono hu (Nat.le_succ n) hv
  unfold GammaValid at hv hvn
  unfold gamma
  have hd0 : 0 < 1 - (n : ℝ) * u := by linarith
  have hd1 : 0 < 1 - ((n + 1 : ℕ) : ℝ) * u := by linarith
  have he0 : 1 + (n : ℝ) * u / (1 - (n : ℝ) * u) =
      1 / (1 - (n : ℝ) * u) := by field_simp; ring
  have he1 : 1 + ((n + 1 : ℕ) : ℝ) * u /
      (1 - ((n + 1 : ℕ) : ℝ) * u) =
      1 / (1 - ((n + 1 : ℕ) : ℝ) * u) := by field_simp; ring
  rw [he0, he1]
  rw [show (1 + u) * (1 / (1 - (n : ℝ) * u)) =
      (1 + u) / (1 - (n : ℝ) * u) by ring]
  rw [div_le_div_iff₀ hd0 hd1]
  push_cast
  have hn1 : 0 ≤ (n : ℝ) + 1 := by positivity
  have hs : 0 ≤ ((n : ℝ) + 1) * u ^ 2 := mul_nonneg hn1 (sq_nonneg u)
  nlinarith

private lemma gamma_step_correction {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hv : GammaValid u (n + 1)) :
    gamma u n + u * (1 + gamma u (n + 1)) ≤ gamma u (n + 1) := by
  have hvn := gamma_valid_mono hu (Nat.le_succ n) hv
  unfold GammaValid at hv hvn
  unfold gamma
  have hd0 : 0 < 1 - (n : ℝ) * u := by linarith
  have hd1 : 0 < 1 - ((n + 1 : ℕ) : ℝ) * u := by linarith
  have he1 : 1 + ((n + 1 : ℕ) : ℝ) * u /
      (1 - ((n + 1 : ℕ) : ℝ) * u) =
      1 / (1 - ((n + 1 : ℕ) : ℝ) * u) := by field_simp; ring
  rw [he1]
  have hfrac : (n : ℝ) * u / (1 - (n : ℝ) * u) ≤
      (n : ℝ) * u / (1 - ((n + 1 : ℕ) : ℝ) * u) := by
    rw [div_le_div_iff₀ hd0 hd1]
    push_cast
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hnuu : 0 ≤ (n : ℝ) * u * u := mul_nonneg (mul_nonneg hn hu) hu
    nlinarith
  calc
    (n : ℝ) * u / (1 - (n : ℝ) * u) +
        u * (1 / (1 - ((n + 1 : ℕ) : ℝ) * u)) ≤
      (n : ℝ) * u / (1 - ((n + 1 : ℕ) : ℝ) * u) +
        u * (1 / (1 - ((n + 1 : ℕ) : ℝ) * u)) :=
          add_le_add hfrac (le_refl _)
    _ = ((n + 1 : ℕ) : ℝ) * u /
        (1 - ((n + 1 : ℕ) : ℝ) * u) := by push_cast; ring

private lemma gamma_step_outer {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hv : GammaValid u (n + 1)) :
    (1 + u) * gamma u n ≤ gamma u (n + 1) := by
  have h := gamma_step_high hu hv
  nlinarith

private lemma chain_high_bound
    {u : ℝ} (hu : 0 ≤ u) (s x : ℕ → ℝ)
    (hstep : ∀ i : ℕ, ∃ d : ℝ, |d| ≤ u ∧
      s (i + 1) = (s i + x i) * (1 + d))
    (n : ℕ) (hv : GammaValid u n) :
    |s n| ≤ (1 + gamma u n) *
      (|s 0| + ∑ i ∈ Finset.range n, |x i|) := by
  induction n with
  | zero => simp [gamma]
  | succ n ih =>
      have hvn : GammaValid u n := gamma_valid_mono hu (Nat.le_succ n) hv
      have hi := ih hvn
      obtain ⟨d, hd, heq⟩ := hstep n
      have had : |1 + d| ≤ 1 + u := by
        calc
          |1 + d| ≤ |(1 : ℝ)| + |d| := abs_add_le _ _
          _ ≤ 1 + u := by simpa using add_le_add_left hd 1
      have hfac : 0 ≤ 1 + u := by linarith
      have hgn : 0 ≤ 1 + gamma u n :=
        one_add_gamma_nonneg hu hvn
      have hA : 0 ≤ |s 0| + ∑ i ∈ Finset.range n, |x i| := by positivity
      have hxn : 0 ≤ |x n| := abs_nonneg _
      rw [heq, abs_mul]
      calc
        |s n + x n| * |1 + d| ≤
            (|s n| + |x n|) * (1 + u) :=
          mul_le_mul (abs_add_le _ _) had (abs_nonneg _) (by positivity)
        _ ≤ ((1 + gamma u n) *
              (|s 0| + ∑ i ∈ Finset.range n, |x i|) + |x n|) *
              (1 + u) := by
          exact mul_le_mul_of_nonneg_right (add_le_add hi (le_refl _)) hfac
        _ ≤ ((1 + gamma u n) *
              (|s 0| + ∑ i ∈ Finset.range n, |x i| + |x n|)) *
              (1 + u) := by
          apply mul_le_mul_of_nonneg_right _ hfac
          have hg : 0 ≤ gamma u n := gamma_nonneg hu hvn
          have hgx : 0 ≤ gamma u n * |x n| := mul_nonneg hg hxn
          nlinarith
        _ ≤ (1 + gamma u (n + 1)) *
              (|s 0| + ∑ i ∈ Finset.range n, |x i| + |x n|) := by
          have hB : 0 ≤ |s 0| + ∑ i ∈ Finset.range n, |x i| + |x n| := by
            positivity
          have hh := mul_le_mul_of_nonneg_right (gamma_step_high hu hv) hB
          nlinarith
        _ = (1 + gamma u (n + 1)) *
              (|s 0| + ∑ i ∈ Finset.range (n + 1), |x i|) := by
          rw [Finset.sum_range_succ]
          ring

private lemma chain_correction_bound
    {u : ℝ} (hu : 0 ≤ u) (s x c : ℕ → ℝ)
    (hstep : ∀ i : ℕ, ∃ d : ℝ, |d| ≤ u ∧
      s (i + 1) = (s i + x i) * (1 + d))
    (hlow : ∀ i : ℕ, |c i| ≤ u * |s (i + 1)|)
    (n : ℕ) (hv : GammaValid u n) :
    ∑ i ∈ Finset.range n, |c i| ≤ gamma u n *
      (|s 0| + ∑ i ∈ Finset.range n, |x i|) := by
  induction n with
  | zero => simp [gamma]
  | succ n ih =>
      have hvn : GammaValid u n := gamma_valid_mono hu (Nat.le_succ n) hv
      have hih := ih hvn
      have hhigh := chain_high_bound hu s x hstep (n + 1) hv
      have hc := hlow n
      have hgn : 0 ≤ gamma u n := gamma_nonneg hu hvn
      have hA : 0 ≤ |s 0| + ∑ i ∈ Finset.range n, |x i| := by positivity
      have hx : 0 ≤ |x n| := abs_nonneg _
      have hAsub : |s 0| + ∑ i ∈ Finset.range n, |x i| ≤
          |s 0| + ∑ i ∈ Finset.range n, |x i| + |x n| := by linarith
      have hc' : |c n| ≤ u * (1 + gamma u (n + 1)) *
          (|s 0| + ∑ i ∈ Finset.range n, |x i| + |x n|) := by
        calc
          |c n| ≤ u * |s (n + 1)| := hc
          _ ≤ u * ((1 + gamma u (n + 1)) *
              (|s 0| + ∑ i ∈ Finset.range (n + 1), |x i|)) :=
            mul_le_mul_of_nonneg_left hhigh hu
          _ = u * (1 + gamma u (n + 1)) *
              (|s 0| + ∑ i ∈ Finset.range n, |x i| + |x n|) := by
            rw [Finset.sum_range_succ]
            ring
      rw [Finset.sum_range_succ]
      calc
        ∑ i ∈ Finset.range n, |c i| + |c n| ≤
            gamma u n *
                (|s 0| + ∑ i ∈ Finset.range n, |x i|) +
              (u * (1 + gamma u (n + 1))) *
                (|s 0| + ∑ i ∈ Finset.range n, |x i| + |x n|) :=
          add_le_add hih hc'
        _ ≤ (gamma u n + u * (1 + gamma u (n + 1))) *
              (|s 0| + ∑ i ∈ Finset.range n, |x i| + |x n|) := by
          have := mul_le_mul_of_nonneg_left hAsub hgn
          nlinarith
        _ ≤ gamma u (n + 1) *
              (|s 0| + ∑ i ∈ Finset.range n, |x i| + |x n|) :=
          mul_le_mul_of_nonneg_right (gamma_step_correction hu hv)
            (by positivity)
        _ = gamma u (n + 1) *
              (|s 0| + ∑ i ∈ Finset.range (n + 1), |x i|) := by
          rw [Finset.sum_range_succ]
          ring

private noncomputable def natPrefix (fl : ℝ → ℝ → ℝ)
    (a : ℝ) (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => a
  | k + 1 => fl (natPrefix fl a x k) (x k)

private lemma twoSumPrefix_succ (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : k + 1 ≤ n) :
    twoSumPrefix fp v (k + 1) hk =
      fp.fl_add (twoSumPrefix fp v k (by omega))
        (v ⟨k + 1, by omega⟩) := by
  unfold twoSumPrefix
  rw [Fin.foldl_succ_last]
  rw [fp.twoSum_high]
  congr 2 <;> simp

private lemma twoSumPrefix_eq_natPrefix (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (x : ℕ → ℝ)
    (hx : ∀ (i : ℕ) (hi : i < n),
      x i = v ⟨i + 1, Nat.succ_lt_succ hi⟩)
    (k : ℕ) (hk : k ≤ n) :
    twoSumPrefix fp v k hk = natPrefix fp.fl_add (v ⟨0, by omega⟩) x k := by
  induction k with
  | zero => simp [twoSumPrefix, natPrefix]
  | succ k ih =>
      rw [twoSumPrefix_succ]
      rw [ih (by omega)]
      simp only [natPrefix]
      rw [hx k (by omega)]

private lemma vecSum_correction_bound (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (hv : GammaValid fp.u n) :
    ∑ i : Fin n, |twoSumCorrection fp v i| ≤
      gamma fp.u n * ∑ i : Fin (n + 1), |v i| := by
  let x : ℕ → ℝ := fun i =>
    if hi : i < n then v ⟨i + 1, Nat.succ_lt_succ hi⟩ else 0
  let s : ℕ → ℝ := natPrefix fp.fl_add (v ⟨0, by omega⟩) x
  let c : ℕ → ℝ := fun i => (fp.twoSum (s i) (x i)).2
  have hx : ∀ (i : ℕ) (hi : i < n),
      x i = v ⟨i + 1, Nat.succ_lt_succ hi⟩ := by
    intro i hi
    simp [x, hi]
  have hs (k : ℕ) (hk : k ≤ n) :
      twoSumPrefix fp v k hk = s k := by
    exact twoSumPrefix_eq_natPrefix fp v x hx k hk
  have hstep : ∀ i : ℕ, ∃ d : ℝ, |d| ≤ fp.u ∧
      s (i + 1) = (s i + x i) * (1 + d) := by
    intro i
    obtain ⟨d, hd, he⟩ := fp.model_add (s i) (x i)
    refine ⟨d, hd, ?_⟩
    simpa [s, natPrefix] using he
  have hlow : ∀ i : ℕ, |c i| ≤ fp.u * |s (i + 1)| := by
    intro i
    have h := fp.twoSum_low_le (s i) (x i)
    rw [fp.twoSum_high] at h
    simpa [c, s, natPrefix] using h
  have hbound := chain_correction_bound fp.u_nonneg s x c hstep hlow n hv
  have hc (i : Fin n) : twoSumCorrection fp v i = c i.val := by
    unfold twoSumCorrection
    simp only [c]
    rw [hs i.val (Nat.le_of_lt i.isLt), hx i.val i.isLt]
  have hleft : (∑ i : Fin n, |twoSumCorrection fp v i|) =
      ∑ i ∈ Finset.range n, |c i| := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    simp [hin, hc ⟨i, hin⟩]
  have hright : |s 0| + ∑ i ∈ Finset.range n, |x i| =
      ∑ i : Fin (n + 1), |v i| := by
    rw [Fin.sum_univ_succ]
    congr 1
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    simp [x, hin]
  rw [hleft, ← hright]
  exact hbound

private lemma chain_exact (s x c : ℕ → ℝ)
    (hstep : ∀ i : ℕ, s (i + 1) + c i = s i + x i) (n : ℕ) :
    s n + ∑ i ∈ Finset.range n, c i =
      s 0 + ∑ i ∈ Finset.range n, x i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hs := hstep n
      linarith

private lemma vecSum_sum_exact (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) :
    ∑ i : Fin (n + 1), vecSum fp v i =
      ∑ i : Fin (n + 1), v i := by
  let x : ℕ → ℝ := fun i =>
    if hi : i < n then v ⟨i + 1, Nat.succ_lt_succ hi⟩ else 0
  let s : ℕ → ℝ := natPrefix fp.fl_add (v ⟨0, by omega⟩) x
  let c : ℕ → ℝ := fun i => (fp.twoSum (s i) (x i)).2
  have hx : ∀ (i : ℕ) (hi : i < n),
      x i = v ⟨i + 1, Nat.succ_lt_succ hi⟩ := by
    intro i hi
    simp [x, hi]
  have hs (k : ℕ) (hk : k ≤ n) :
      twoSumPrefix fp v k hk = s k := by
    exact twoSumPrefix_eq_natPrefix fp v x hx k hk
  have hstep : ∀ i : ℕ, s (i + 1) + c i = s i + x i := by
    intro i
    have h := fp.twoSum_exact (s i) (x i)
    rw [fp.twoSum_high] at h
    simpa [s, c, natPrefix] using h
  have hexact := chain_exact s x c hstep n
  have hc (i : Fin n) : twoSumCorrection fp v i = c i.val := by
    unfold twoSumCorrection
    simp only [c]
    rw [hs i.val (Nat.le_of_lt i.isLt), hx i.val i.isLt]
  have hcorr : (∑ i : Fin n, twoSumCorrection fp v i) =
      ∑ i ∈ Finset.range n, c i := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    simp [hin, hc ⟨i, hin⟩]
  have htotal : s 0 + ∑ i ∈ Finset.range n, x i =
      ∑ i : Fin (n + 1), v i := by
    rw [Fin.sum_univ_succ]
    congr 1
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    simp [x, hin]
  rw [Fin.sum_univ_castSucc]
  simp only [vecSum, Fin.lastCases_castSucc, Fin.lastCases_last]
  rw [hcorr, hs n (Nat.le_refl n)]
  rw [← htotal]
  linarith

private lemma recursiveSum_error_bound
    (fp : StandardAddModel) (m : ℕ) (w : Fin m → ℝ)
    (hv : GammaValid fp.u (m - 1)) :
    |recursiveSum fp.fl_add m w - ∑ i : Fin m, w i| ≤
      gamma fp.u (m - 1) * ∑ i : Fin m, |w i| := by
  induction m with
  | zero => simp [recursiveSum, gamma]
  | succ m ih =>
      cases m with
      | zero => simp [recursiveSum, gamma]
      | succ k =>
          have hvk : GammaValid fp.u k := by
            apply gamma_valid_mono fp.u_nonneg (Nat.le_succ k)
            simpa using hv
          let w₀ : Fin (k + 1) → ℝ := fun i => w i.castSucc
          have hih := ih w₀ (by simpa using hvk)
          let r := recursiveSum fp.fl_add (k + 1) w₀
          let t := ∑ i : Fin (k + 1), w₀ i
          let a := ∑ i : Fin (k + 1), |w₀ i|
          let z := w (Fin.last (k + 1))
          have hir : |r - t| ≤ gamma fp.u k * a := by
            simpa [r, t, a, w₀] using hih
          have hta : |t| ≤ a := by
            simpa [t, a] using
              (Finset.abs_sum_le_sum_abs w₀ (Finset.univ : Finset (Fin (k + 1))))
          have htza : |t + z| ≤ a + |z| := by
            calc
              |t + z| ≤ |t| + |z| := abs_add_le _ _
              _ ≤ a + |z| := add_le_add hta (le_refl _)
          obtain ⟨d, hd, he⟩ := fp.model_add r z
          have had : |1 + d| ≤ 1 + fp.u := by
            calc
              |1 + d| ≤ |(1 : ℝ)| + |d| := abs_add_le _ _
              _ ≤ 1 + fp.u := by simpa using add_le_add_left hd 1
          have hgu : 0 ≤ gamma fp.u k := gamma_nonneg fp.u_nonneg hvk
          have ha : 0 ≤ a := by dsimp [a]; positivity
          have hz : 0 ≤ |z| := abs_nonneg _
          have hfac : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
          have hcoef : (1 + fp.u) * gamma fp.u k + fp.u ≤
              gamma fp.u (k + 1) := by
            have hh := gamma_step_high fp.u_nonneg (by simpa using hv)
            nlinarith
          rw [recursiveSum]
          change |fp.fl_add r z - ∑ i : Fin (k + 2), w i| ≤
            gamma fp.u (k + 1) * ∑ i : Fin (k + 2), |w i|
          have hsum : (∑ i : Fin (k + 2), w i) = t + z := by
            rw [Fin.sum_univ_castSucc]
          have habs : (∑ i : Fin (k + 2), |w i|) = a + |z| := by
            rw [Fin.sum_univ_castSucc]
          rw [hsum, habs]
          change |fp.fl_add r z - (t + z)| ≤
            gamma fp.u (k + 1) * (a + |z|)
          rw [he]
          have herr : (r + z) * (1 + d) - (t + z) =
              (1 + d) * (r - t) + d * (t + z) := by ring
          rw [herr]
          calc
            |(1 + d) * (r - t) + d * (t + z)| ≤
                |(1 + d) * (r - t)| + |d * (t + z)| := abs_add_le _ _
            _ = |1 + d| * |r - t| + |d| * |t + z| := by
              rw [abs_mul, abs_mul]
            _ ≤ (1 + fp.u) * (gamma fp.u k * a) +
                fp.u * (a + |z|) := by
              apply add_le_add
              · exact mul_le_mul had hir (abs_nonneg _) hfac
              · exact mul_le_mul hd htza (abs_nonneg _) fp.u_nonneg
            _ ≤ ((1 + fp.u) * gamma fp.u k + fp.u) * (a + |z|) := by
              have hsub : a ≤ a + |z| := by linarith
              have hh := mul_le_mul_of_nonneg_left hsub
                (mul_nonneg hfac hgu)
              nlinarith
            _ ≤ gamma fp.u (k + 1) * (a + |z|) :=
              mul_le_mul_of_nonneg_right hcoef (by positivity)

theorem p02_t1_sum2_error_bound
    (fp : ErrorFreeAddModel) (n : ℕ) (v : Fin (n + 1) → ℝ)
    (hvalid : GammaValid fp.u (n + 1)) :
    |sum2 fp v - ∑ i : Fin (n + 1), v i| ≤
      fp.u * |∑ i : Fin (n + 1), v i| +
        (gamma fp.u n) ^ 2 * ∑ i : Fin (n + 1), |v i| := by
  -- PROOF_START P02-T1-H001
  cases n with
  | zero =>
      simp [sum2, sumK, iteratedVecSum, vecSum, twoSumPrefix,
        recursiveSum, gamma]
      rw [show (0 : Fin 1) = Fin.last 0 by rfl, Fin.lastCases_last]
      simp only [sub_self, abs_zero]
      exact mul_nonneg fp.u_nonneg (abs_nonneg _)
  | succ k =>
      have hvn : GammaValid fp.u (k + 1) :=
        gamma_valid_mono fp.u_nonneg (by omega) hvalid
      have hvk : GammaValid fp.u k :=
        gamma_valid_mono fp.u_nonneg (by omega) hvalid
      let q : Fin (k + 1) → ℝ := fun i => twoSumCorrection fp v i
      let h : ℝ := twoSumPrefix fp v (k + 1) (Nat.le_refl _)
      let r : ℝ := recursiveSum fp.fl_add (k + 1) q
      let t : ℝ := ∑ i : Fin (k + 1), q i
      let a : ℝ := ∑ i : Fin (k + 1), |q i|
      let s : ℝ := ∑ i : Fin (k + 2), v i
      let A : ℝ := ∑ i : Fin (k + 2), |v i|
      have hcorr : a ≤ gamma fp.u (k + 1) * A := by
        simpa [a, q, A] using vecSum_correction_bound fp v hvn
      have hr : |r - t| ≤ gamma fp.u k * a := by
        have hh := recursiveSum_error_bound fp.toStandardAddModel (k + 1) q
          (by simpa using hvk)
        simpa [r, t, a] using hh
      have hth : t + h = s := by
        have he := vecSum_sum_exact fp v
        rw [Fin.sum_univ_castSucc] at he
        simpa [vecSum, q, h, t, s] using he
      have hsum2 : sum2 fp v = fp.fl_add r h := by
        change recursiveSum fp.fl_add (k + 2) (vecSum fp v) = fp.fl_add r h
        rw [recursiveSum]
        change fp.fl_add
            (recursiveSum fp.fl_add (k + 1)
              (fun i => vecSum fp v i.castSucc))
            (vecSum fp v (Fin.last (k + 1))) = fp.fl_add r h
        simp only [vecSum, Fin.lastCases_castSucc, Fin.lastCases_last]
        rfl
      obtain ⟨d, hd, he⟩ := fp.model_add r h
      have had : |1 + d| ≤ 1 + fp.u := by
        calc
          |1 + d| ≤ |(1 : ℝ)| + |d| := abs_add_le _ _
          _ ≤ 1 + fp.u := by simpa using add_le_add_left hd 1
      have hgn : 0 ≤ gamma fp.u (k + 1) := gamma_nonneg fp.u_nonneg hvn
      have ha : 0 ≤ a := by dsimp [a]; positivity
      have hA : 0 ≤ A := by dsimp [A]; positivity
      have hfac : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
      have houter : (1 + fp.u) * gamma fp.u k ≤ gamma fp.u (k + 1) :=
        gamma_step_outer fp.u_nonneg hvn
      rw [hsum2, he]
      change |(r + h) * (1 + d) - s| ≤
        fp.u * |s| + gamma fp.u (k + 1) ^ 2 * A
      have herr : (r + h) * (1 + d) - s =
          (1 + d) * (r - t) + d * s := by
        rw [← hth]
        ring
      rw [herr]
      calc
        |(1 + d) * (r - t) + d * s| ≤
            |(1 + d) * (r - t)| + |d * s| := abs_add_le _ _
        _ = |1 + d| * |r - t| + |d| * |s| := by
          rw [abs_mul, abs_mul]
        _ ≤ (1 + fp.u) * (gamma fp.u k * a) + fp.u * |s| := by
          apply add_le_add
          · exact mul_le_mul had hr (abs_nonneg _) hfac
          · exact mul_le_mul_of_nonneg_right hd (abs_nonneg _)
        _ ≤ gamma fp.u (k + 1) ^ 2 * A + fp.u * |s| := by
          have hfirst : (1 + fp.u) * (gamma fp.u k * a) ≤
              gamma fp.u (k + 1) ^ 2 * A := by
            calc
              (1 + fp.u) * (gamma fp.u k * a) =
                  ((1 + fp.u) * gamma fp.u k) * a := by ring
              _ ≤ gamma fp.u (k + 1) * a :=
                mul_le_mul_of_nonneg_right houter ha
              _ ≤ gamma fp.u (k + 1) *
                    (gamma fp.u (k + 1) * A) :=
                mul_le_mul_of_nonneg_left hcorr hgn
              _ = gamma fp.u (k + 1) ^ 2 * A := by ring
          exact add_le_add hfirst (le_refl _)
        _ = fp.u * |s| + gamma fp.u (k + 1) ^ 2 * A := by ring

end HighamBench
