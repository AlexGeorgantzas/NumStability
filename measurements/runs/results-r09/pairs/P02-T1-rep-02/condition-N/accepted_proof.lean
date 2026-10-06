import HighamBench.P02Definitions

namespace HighamBench

open scoped BigOperators

private noncomputable def highSeq (fp : ErrorFreeAddModel)
    (a : ℝ) (b : ℕ → ℝ) : ℕ → ℝ
  | 0 => a
  | k + 1 => (fp.twoSum (highSeq fp a b k) (b k)).1

private noncomputable def tailVal {N : ℕ} (v : Fin (N + 1) → ℝ)
    (j : ℕ) : ℝ :=
  if h : j < N then v ⟨j + 1, Nat.succ_lt_succ h⟩ else 0

private lemma twoSum_high_abs (fp : ErrorFreeAddModel) (x y : ℝ) :
    |(fp.twoSum x y).1| ≤ (1 + fp.u) * (|x| + |y|) := by
  rcases fp.model_add x y with ⟨δ, hδ, hfl⟩
  rw [fp.twoSum_high, hfl, abs_mul]
  have hfac : |1 + δ| ≤ 1 + fp.u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
  have hsum : |x + y| ≤ |x| + |y| := abs_add_le _ _
  nlinarith [abs_nonneg (x + y), abs_nonneg (1 + δ),
    abs_nonneg x, abs_nonneg y, fp.u_nonneg]

private lemma gamma_nonneg_of_valid {u : ℝ} {k : ℕ}
    (hu : 0 ≤ u) (hv : GammaValid u k) : 0 ≤ gamma u k := by
  unfold GammaValid at hv
  rw [gamma]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

private lemma gammaValid_mono {u : ℝ} (hu : 0 ≤ u) {j k : ℕ}
    (hjk : j ≤ k) (hk : GammaValid u k) : GammaValid u j := by
  unfold GammaValid at hk ⊢
  have hc : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
  nlinarith [mul_le_mul_of_nonneg_right hc hu]

private lemma gamma_step {u : ℝ} (hu : 0 ≤ u) (k : ℕ)
    (hv : GammaValid u (k + 1)) :
    (1 + u) * gamma u k + u ≤ gamma u (k + 1) := by
  unfold GammaValid at hv
  have hk : (k : ℝ) * u < 1 := by
    push_cast at hv
    nlinarith
  have hd₀ : 0 < 1 - (k : ℝ) * u := by linarith
  have hd₁ : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := by
    simpa using sub_pos.mpr hv
  rw [gamma, gamma]
  have heq :
      (1 + u) * ((k : ℝ) * u / (1 - (k : ℝ) * u)) + u =
        (((k + 1 : ℕ) : ℝ) * u) / (1 - (k : ℝ) * u) := by
    have hd₀' : 1 - u * (k : ℝ) ≠ 0 := by nlinarith
    field_simp [ne_of_gt hd₀, hd₀']
    push_cast
    ring
  rw [heq]
  apply div_le_div_of_nonneg_left
  · exact mul_nonneg (Nat.cast_nonneg _) hu
  · exact hd₁
  · push_cast
    nlinarith

private lemma highSeq_abs_le (fp : ErrorFreeAddModel) (a : ℝ) (b : ℕ → ℝ)
    (k : ℕ) (hv : GammaValid fp.u k) :
    |highSeq fp a b k| ≤
      (|a| + ∑ i ∈ Finset.range k, |b i|) /
        (1 - (k : ℝ) * fp.u) := by
  induction k with
  | zero => simp [highSeq]
  | succ k ih =>
      unfold GammaValid at hv
      have hvk : GammaValid fp.u k := by
        unfold GammaValid
        push_cast at hv ⊢
        nlinarith [fp.u_nonneg]
      have hd : 0 < 1 - (k : ℝ) * fp.u := by
        have ht := hvk
        unfold GammaValid at ht
        linarith
      have hd' : 0 < 1 - ((k + 1 : ℕ) : ℝ) * fp.u := by
        simpa using sub_pos.mpr hv
      let S : ℝ := |a| + ∑ i ∈ Finset.range k, |b i|
      let B : ℝ := |b k|
      have hS : 0 ≤ S := by
        dsimp [S]
        positivity
      have hB : 0 ≤ B := by dsimp [B]; positivity
      have hku : 0 ≤ (k : ℝ) * fp.u :=
        mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg
      have hpre : |highSeq fp a b k| ≤ S / (1 - (k : ℝ) * fp.u) := by
        simpa [S] using ih hvk
      have hBden : B * (1 - (k : ℝ) * fp.u) ≤ B := by
        nlinarith [mul_nonneg hB hku]
      have hadd : |highSeq fp a b k| + B ≤
          (S + B) / (1 - (k : ℝ) * fp.u) := by
        apply (le_div_iff₀ hd).2
        have hp := (le_div_iff₀ hd).mp hpre
        nlinarith
      have hround := twoSum_high_abs fp (highSeq fp a b k) (b k)
      have hround' : |highSeq fp a b (k + 1)| ≤
          (1 + fp.u) * ((S + B) / (1 - (k : ℝ) * fp.u)) := by
        rw [highSeq]
        calc
          |(fp.twoSum (highSeq fp a b k) (b k)).1| ≤
              (1 + fp.u) * (|highSeq fp a b k| + |b k|) := hround
          _ ≤ (1 + fp.u) * ((S + B) / (1 - (k : ℝ) * fp.u)) := by
            apply mul_le_mul_of_nonneg_left
            · simpa [B] using hadd
            · linarith [fp.u_nonneg]
      have hSB : 0 ≤ S + B := by positivity
      have hcoef :
          (1 + fp.u) * ((S + B) / (1 - (k : ℝ) * fp.u)) ≤
            (S + B) / (1 - ((k + 1 : ℕ) : ℝ) * fp.u) := by
        rw [← mul_div_assoc]
        apply (div_le_div_iff₀ hd hd').2
        have hsq : 0 ≤ (S + B) * ((k + 1 : ℕ) : ℝ) * fp.u ^ 2 := by
          positivity
        push_cast at hsq ⊢
        nlinarith
      rw [Finset.sum_range_succ]
      simpa [S, B, add_assoc] using hround'.trans hcoef

private lemma twoSumPrefix_eq_highSeq (fp : ErrorFreeAddModel) {N : ℕ}
    (v : Fin (N + 1) → ℝ) (k : ℕ) (hk : k ≤ N) :
    twoSumPrefix fp v k hk = highSeq fp (v 0) (tailVal v) k := by
  induction k with
  | zero => simp [twoSumPrefix, highSeq]
  | succ k ih =>
      have hkN : k ≤ N := Nat.le_trans (Nat.le_succ k) hk
      have hlt : k < N := Nat.lt_of_succ_le hk
      rw [highSeq]
      unfold twoSumPrefix
      rw [Fin.foldl_succ_last]
      congr 2
      · simpa [twoSumPrefix] using ih hkN
      · simp [tailVal, hlt]

private lemma highSeq_exact (fp : ErrorFreeAddModel) (a : ℝ) (b : ℕ → ℝ)
    (k : ℕ) :
    highSeq fp a b k +
        ∑ i ∈ Finset.range k,
          (fp.twoSum (highSeq fp a b i) (b i)).2 =
      a + ∑ i ∈ Finset.range k, b i := by
  induction k with
  | zero => simp [highSeq]
  | succ k ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, highSeq]
      have he := fp.twoSum_exact (highSeq fp a b k) (b k)
      calc
        (fp.twoSum (highSeq fp a b k) (b k)).1 +
              ((∑ i ∈ Finset.range k,
                  (fp.twoSum (highSeq fp a b i) (b i)).2) +
                (fp.twoSum (highSeq fp a b k) (b k)).2) =
            (highSeq fp a b k +
                (∑ i ∈ Finset.range k,
                  (fp.twoSum (highSeq fp a b i) (b i)).2)) + b k := by
              linarith
        _ = a + (∑ i ∈ Finset.range k, b i) + b k := by rw [ih]
        _ = a + ((∑ i ∈ Finset.range k, b i) + b k) := by ring

private lemma twoSumCorrection_eq_highSeq (fp : ErrorFreeAddModel) {N : ℕ}
    (v : Fin (N + 1) → ℝ) (i : Fin N) :
    twoSumCorrection fp v i =
      (fp.twoSum (highSeq fp (v 0) (tailVal v) i.val)
        (tailVal v i.val)).2 := by
  rw [twoSumCorrection, twoSumPrefix_eq_highSeq]
  simp [tailVal, i.isLt]

private lemma correction_sum_eq_range (fp : ErrorFreeAddModel) {N : ℕ}
    (v : Fin (N + 1) → ℝ) :
    (∑ i : Fin N, twoSumCorrection fp v i) =
      ∑ j ∈ Finset.range N,
        (fp.twoSum (highSeq fp (v 0) (tailVal v) j)
          (tailVal v j)).2 := by
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  have hjN : j < N := Finset.mem_range.mp hj
  simp [hjN, twoSumCorrection_eq_highSeq]

private lemma tail_sum_eq_range {N : ℕ} (v : Fin (N + 1) → ℝ) :
    (∑ i : Fin N, v i.succ) =
      ∑ j ∈ Finset.range N, tailVal v j := by
  simpa [tailVal] using (Fin.sum_univ_eq_sum_range (tailVal v) N)

private lemma tail_abs_sum_eq_range {N : ℕ} (v : Fin (N + 1) → ℝ) :
    (∑ i : Fin N, |v i.succ|) =
      ∑ j ∈ Finset.range N, |tailVal v j| := by
  simpa [tailVal] using
    (Fin.sum_univ_eq_sum_range (fun j => |tailVal v j|) N)

private lemma vecSum_sum (fp : ErrorFreeAddModel) {N : ℕ}
    (v : Fin (N + 1) → ℝ) :
    (∑ i : Fin (N + 1), vecSum fp v i) = ∑ i, v i := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  simp only [vecSum, Fin.lastCases_castSucc, Fin.lastCases_last]
  rw [correction_sum_eq_range, twoSumPrefix_eq_highSeq,
    tail_sum_eq_range]
  have he := highSeq_exact fp (v 0) (tailVal v) N
  linarith

private lemma correction_abs_sum_eq_range (fp : ErrorFreeAddModel) {N : ℕ}
    (v : Fin (N + 1) → ℝ) :
    (∑ i : Fin N, |twoSumCorrection fp v i|) =
      ∑ j ∈ Finset.range N,
        |(fp.twoSum (highSeq fp (v 0) (tailVal v) j)
          (tailVal v j)).2| := by
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  have hjN : j < N := Finset.mem_range.mp hj
  simp [hjN, twoSumCorrection_eq_highSeq]

private lemma correction_abs_sum_le (fp : ErrorFreeAddModel) {N : ℕ}
    (v : Fin (N + 1) → ℝ) (hv : GammaValid fp.u N) :
    (∑ i : Fin N, |twoSumCorrection fp v i|) ≤
      gamma fp.u N * ∑ i : Fin (N + 1), |v i| := by
  let S : ℝ := |v 0| + ∑ j ∈ Finset.range N, |tailVal v j|
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hdN : 0 < 1 - (N : ℝ) * fp.u := by
    unfold GammaValid at hv
    linarith
  have hone : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
  rw [correction_abs_sum_eq_range]
  have heach : ∀ j ∈ Finset.range N,
      |(fp.twoSum (highSeq fp (v 0) (tailVal v) j)
          (tailVal v j)).2| ≤
        fp.u * (S / (1 - (N : ℝ) * fp.u)) := by
    intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    have hjle : j + 1 ≤ N := Nat.succ_le_iff.mpr hjN
    have hvj : GammaValid fp.u (j + 1) :=
      gammaValid_mono fp.u_nonneg hjle hv
    have hdj : 0 < 1 - ((j + 1 : ℕ) : ℝ) * fp.u := by
      unfold GammaValid at hvj
      linarith
    have hp := highSeq_abs_le fp (v 0) (tailVal v) (j + 1) hvj
    rw [Finset.sum_range_succ] at hp
    have hpart :
        |v 0| + ((∑ i ∈ Finset.range j, |tailVal v i|) + |tailVal v j|) ≤ S := by
      have hsub : Finset.range (j + 1) ⊆ Finset.range N :=
        Finset.range_mono hjle
      have hsum :
          (∑ i ∈ Finset.range (j + 1), |tailVal v i|) ≤
            ∑ i ∈ Finset.range N, |tailVal v i| :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (by
          intro i hi hnot
          exact abs_nonneg _)
      rw [Finset.sum_range_succ] at hsum
      dsimp [S]
      linarith
    have hdiv₁ :
        (|v 0| + ((∑ i ∈ Finset.range j, |tailVal v i|) + |tailVal v j|)) /
              (1 - ((j + 1 : ℕ) : ℝ) * fp.u) ≤
          S / (1 - ((j + 1 : ℕ) : ℝ) * fp.u) := by
      exact div_le_div_of_nonneg_right hpart (le_of_lt hdj)
    have hden :
        1 - (N : ℝ) * fp.u ≤ 1 - ((j + 1 : ℕ) : ℝ) * fp.u := by
      have hc : ((j + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hjle
      nlinarith [mul_le_mul_of_nonneg_right hc fp.u_nonneg]
    have hdiv₂ :
        S / (1 - ((j + 1 : ℕ) : ℝ) * fp.u) ≤
          S / (1 - (N : ℝ) * fp.u) :=
      div_le_div_of_nonneg_left hS hdN hden
    have hhigh : |highSeq fp (v 0) (tailVal v) (j + 1)| ≤
        S / (1 - (N : ℝ) * fp.u) := by
      exact hp.trans (hdiv₁.trans hdiv₂)
    calc
      |(fp.twoSum (highSeq fp (v 0) (tailVal v) j)
          (tailVal v j)).2| ≤
          fp.u * |(fp.twoSum (highSeq fp (v 0) (tailVal v) j)
            (tailVal v j)).1| := fp.twoSum_low_le _ _
      _ = fp.u * |highSeq fp (v 0) (tailVal v) (j + 1)| := by
        rw [highSeq]
      _ ≤ fp.u * (S / (1 - (N : ℝ) * fp.u)) :=
        mul_le_mul_of_nonneg_left hhigh fp.u_nonneg
  calc
    (∑ j ∈ Finset.range N,
        |(fp.twoSum (highSeq fp (v 0) (tailVal v) j)
          (tailVal v j)).2|) ≤
        ∑ _j ∈ Finset.range N,
          fp.u * (S / (1 - (N : ℝ) * fp.u)) :=
      Finset.sum_le_sum heach
    _ = gamma fp.u N * S := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, gamma]
      ring
    _ = gamma fp.u N * ∑ i : Fin (N + 1), |v i| := by
      rw [Fin.sum_univ_succ, tail_abs_sum_eq_range]

private lemma recursiveSum_error (fp : ErrorFreeAddModel) (m : ℕ)
    (w : Fin (m + 1) → ℝ) (hv : GammaValid fp.u m) :
    |recursiveSum fp.fl_add (m + 1) w - ∑ i, w i| ≤
      gamma fp.u m * ∑ i, |w i| := by
  induction m with
  | zero => simp [recursiveSum, gamma]
  | succ k ih =>
      let wp : Fin (k + 1) → ℝ := fun i => w i.castSucc
      let r : ℝ := recursiveSum fp.fl_add (k + 1) wp
      let s : ℝ := ∑ i, wp i
      let x : ℝ := w (Fin.last (k + 1))
      let A : ℝ := ∑ i, |wp i|
      let B : ℝ := |x|
      have hvk : GammaValid fp.u k :=
        gammaValid_mono fp.u_nonneg (Nat.le_succ k) hv
      have hrec : |r - s| ≤ gamma fp.u k * A := by
        simpa [r, s, A, wp] using ih wp hvk
      have hA : 0 ≤ A := by dsimp [A]; positivity
      have hB : 0 ≤ B := by dsimp [B]; positivity
      have hγ : 0 ≤ gamma fp.u k :=
        gamma_nonneg_of_valid fp.u_nonneg hvk
      have hsabs : |s| ≤ A := by
        dsimp [s, A]
        exact Finset.abs_sum_le_sum_abs _ _
      have hsx : |s + x| ≤ A + B := by
        calc
          |s + x| ≤ |s| + |x| := abs_add_le _ _
          _ ≤ A + B := by simpa [B] using add_le_add_right hsabs |x|
      rcases fp.model_add r x with ⟨δ, hδ, hfl⟩
      have hfac : |1 + δ| ≤ 1 + fp.u := by
        calc
          |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
          _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
      have hdecomp : fp.fl_add r x - (s + x) =
          (1 + δ) * (r - s) + δ * (s + x) := by
        rw [hfl]
        ring
      have hfirst : |1 + δ| * |r - s| ≤
          (1 + fp.u) * (gamma fp.u k * A) := by
        exact mul_le_mul hfac hrec (abs_nonneg _) (by linarith [fp.u_nonneg])
      have hsecond : |δ| * |s + x| ≤ fp.u * (A + B) := by
        exact mul_le_mul hδ hsx (abs_nonneg _) fp.u_nonneg
      have hstep := gamma_step fp.u_nonneg k hv
      have hcoef :
          (1 + fp.u) * (gamma fp.u k * A) + fp.u * (A + B) ≤
            gamma fp.u (k + 1) * (A + B) := by
        have hAle : A ≤ A + B := by linarith
        have hgAle : gamma fp.u k * A ≤ gamma fp.u k * (A + B) :=
          mul_le_mul_of_nonneg_left hAle hγ
        calc
          (1 + fp.u) * (gamma fp.u k * A) + fp.u * (A + B) ≤
              (1 + fp.u) * (gamma fp.u k * (A + B)) +
                fp.u * (A + B) := by
                  exact add_le_add
                    (mul_le_mul_of_nonneg_left hgAle (by linarith [fp.u_nonneg]))
                    le_rfl
          _ = ((1 + fp.u) * gamma fp.u k + fp.u) * (A + B) := by ring
          _ ≤ gamma fp.u (k + 1) * (A + B) :=
            mul_le_mul_of_nonneg_right hstep (by positivity)
      have hrs : recursiveSum fp.fl_add (k + 1 + 1) w = fp.fl_add r x := by
        simp [recursiveSum, r, x, wp]
      rw [hrs]
      rw [Fin.sum_univ_castSucc (fun i => w i)]
      rw [Fin.sum_univ_castSucc (fun i => |w i|)]
      change |fp.fl_add r x - (s + x)| ≤ gamma fp.u (k + 1) * (A + B)
      rw [hdecomp]
      calc
        |(1 + δ) * (r - s) + δ * (s + x)| ≤
            |(1 + δ) * (r - s)| + |δ * (s + x)| := abs_add_le _ _
        _ = |1 + δ| * |r - s| + |δ| * |s + x| := by rw [abs_mul, abs_mul]
        _ ≤ (1 + fp.u) * (gamma fp.u k * A) + fp.u * (A + B) :=
          add_le_add hfirst hsecond
        _ ≤ gamma fp.u (k + 1) * (A + B) := hcoef

theorem p02_t1_sum2_error_bound
    (fp : ErrorFreeAddModel) (n : ℕ) (v : Fin (n + 1) → ℝ)
    (hvalid : GammaValid fp.u (n + 1)) :
    |sum2 fp v - ∑ i : Fin (n + 1), v i| ≤
      fp.u * |∑ i : Fin (n + 1), v i| +
        (gamma fp.u n) ^ 2 * ∑ i : Fin (n + 1), |v i| := by
  -- PROOF_START P02-T1-H001
  cases n with
  | zero =>
      have hvs : vecSum fp v = v := by
        funext i
        have hi : i = Fin.last 0 := by
          apply Fin.ext
          omega
        rw [hi]
        change Fin.lastCases (twoSumPrefix fp v 0 (Nat.le_refl 0))
            (twoSumCorrection fp v) (Fin.last 0) = v (Fin.last 0)
        rw [Fin.lastCases_last]
        simp [twoSumPrefix]
      simp [sum2, sumK, iteratedVecSum, hvs, recursiveSum, gamma]
      exact mul_nonneg fp.u_nonneg (abs_nonneg _)
  | succ k =>
      let q : Fin (k + 1) → ℝ := fun i => twoSumCorrection fp v i
      let p : ℝ := twoSumPrefix fp v (k + 1) (Nat.le_refl (k + 1))
      let σ : ℝ := recursiveSum fp.fl_add (k + 1) q
      let s : ℝ := ∑ i : Fin (k + 1 + 1), v i
      let S : ℝ := ∑ i : Fin (k + 1 + 1), |v i|
      have hvn : GammaValid fp.u (k + 1) :=
        gammaValid_mono fp.u_nonneg (Nat.le_succ (k + 1)) hvalid
      have hvk : GammaValid fp.u k :=
        gammaValid_mono fp.u_nonneg (Nat.le_succ k) hvn
      have hq : (∑ i : Fin (k + 1), |q i|) ≤
          gamma fp.u (k + 1) * S := by
        simpa [q, S] using correction_abs_sum_le fp v hvn
      have hσ : |σ - ∑ i : Fin (k + 1), q i| ≤
          gamma fp.u k * ∑ i : Fin (k + 1), |q i| := by
        simpa [σ] using recursiveSum_error fp k q hvk
      have hγk : 0 ≤ gamma fp.u k :=
        gamma_nonneg_of_valid fp.u_nonneg hvk
      have hγn : 0 ≤ gamma fp.u (k + 1) :=
        gamma_nonneg_of_valid fp.u_nonneg hvn
      have hS : 0 ≤ S := by dsimp [S]; positivity
      have hσ' : |σ - ∑ i : Fin (k + 1), q i| ≤
          gamma fp.u k * (gamma fp.u (k + 1) * S) := by
        exact hσ.trans (mul_le_mul_of_nonneg_left hq hγk)
      have hexact : (∑ i : Fin (k + 1), q i) + p = s := by
        have ht := vecSum_sum fp v
        rw [Fin.sum_univ_castSucc] at ht
        simpa [q, p, s, vecSum] using ht
      have hsum2 : sum2 fp v = fp.fl_add σ p := by
        change recursiveSum fp.fl_add (k + 1 + 1) (vecSum fp v) =
          fp.fl_add σ p
        rw [recursiveSum.eq_2, dif_neg (Nat.succ_ne_zero k)]
        have hvpre : (fun i : Fin (k + 1) => (vecSum fp v) i.castSucc) = q := by
          funext i
          simp [vecSum, q]
        rw [hvpre]
        simp [σ, p, vecSum]
      rcases fp.model_add σ p with ⟨δ, hδ, hfl⟩
      have hfac : |1 + δ| ≤ 1 + fp.u := by
        calc
          |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
          _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
      have hdecomp : fp.fl_add σ p - s =
          (1 + δ) * (σ - ∑ i : Fin (k + 1), q i) + δ * s := by
        rw [hfl]
        rw [← hexact]
        ring
      have hfirst :
          |1 + δ| * |σ - ∑ i : Fin (k + 1), q i| ≤
            (1 + fp.u) *
              (gamma fp.u k * (gamma fp.u (k + 1) * S)) := by
        exact mul_le_mul hfac hσ' (abs_nonneg _) (by linarith [fp.u_nonneg])
      have hsecond : |δ| * |s| ≤ fp.u * |s| :=
        mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
      have hstep := gamma_step fp.u_nonneg k hvn
      have hcoef : (1 + fp.u) * gamma fp.u k ≤ gamma fp.u (k + 1) := by
        nlinarith [fp.u_nonneg]
      have hsquare :
          (1 + fp.u) * (gamma fp.u k * (gamma fp.u (k + 1) * S)) ≤
            (gamma fp.u (k + 1)) ^ 2 * S := by
        calc
          (1 + fp.u) * (gamma fp.u k * (gamma fp.u (k + 1) * S)) =
              ((1 + fp.u) * gamma fp.u k) *
                (gamma fp.u (k + 1) * S) := by ring
          _ ≤ gamma fp.u (k + 1) * (gamma fp.u (k + 1) * S) :=
            mul_le_mul_of_nonneg_right hcoef (mul_nonneg hγn hS)
          _ = (gamma fp.u (k + 1)) ^ 2 * S := by ring
      rw [hsum2]
      change |fp.fl_add σ p - s| ≤
        fp.u * |s| + (gamma fp.u (k + 1)) ^ 2 * S
      rw [hdecomp]
      calc
        |(1 + δ) * (σ - ∑ i : Fin (k + 1), q i) + δ * s| ≤
            |(1 + δ) * (σ - ∑ i : Fin (k + 1), q i)| + |δ * s| :=
          abs_add_le _ _
        _ = |1 + δ| * |σ - ∑ i : Fin (k + 1), q i| + |δ| * |s| := by
          rw [abs_mul, abs_mul]
        _ ≤ (1 + fp.u) * (gamma fp.u k * (gamma fp.u (k + 1) * S)) +
            fp.u * |s| := add_le_add hfirst hsecond
        _ ≤ fp.u * |s| + (gamma fp.u (k + 1)) ^ 2 * S := by
          linarith

end HighamBench
