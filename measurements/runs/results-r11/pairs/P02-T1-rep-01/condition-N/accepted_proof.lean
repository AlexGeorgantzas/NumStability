import HighamBench.P02Definitions

namespace HighamBench

open scoped BigOperators


private lemma gamma_nonneg_of_valid (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : GammaValid u k) : 0 ≤ gamma u k := by
  unfold GammaValid at hk
  unfold gamma
  have hd : 0 < 1 - (k : ℝ) * u := by linarith
  positivity

private lemma gamma_step (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : GammaValid u (k + 1)) :
    (1 + u) * gamma u k + u ≤ gamma u (k + 1) := by
  unfold GammaValid at hk
  have hd₀ : 0 < 1 - (k : ℝ) * u := by
    push_cast at hk
    nlinarith
  have hd₁ : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := by linarith
  have hn : 0 ≤ (k : ℝ) * u := mul_nonneg (by positivity) hu
  have hdle : 1 - ((k + 1 : ℕ) : ℝ) * u ≤ 1 - (k : ℝ) * u := by
    push_cast
    nlinarith
  have hg : gamma u k ≤
      (k : ℝ) * u / (1 - ((k + 1 : ℕ) : ℝ) * u) := by
    unfold gamma
    exact (div_le_div_iff₀ hd₀ hd₁).2 (mul_le_mul_of_nonneg_left hdle hn)
  calc
    (1 + u) * gamma u k + u ≤
        (1 + u) * ((k : ℝ) * u /
          (1 - ((k + 1 : ℕ) : ℝ) * u)) + u := by
            gcongr
    _ ≤ gamma u (k + 1) := by
      unfold gamma
      rw [show (1 + u) * ((k : ℝ) * u /
          (1 - ((k + 1 : ℕ) : ℝ) * u)) + u =
          ((1 + u) * ((k : ℝ) * u) +
            u * (1 - ((k + 1 : ℕ) : ℝ) * u)) /
              (1 - ((k + 1 : ℕ) : ℝ) * u) by
        have hd₁ne : 1 - ((k + 1 : ℕ) : ℝ) * u ≠ 0 := ne_of_gt hd₁
        norm_num [Nat.cast_add, Nat.cast_one] at hd₁ne ⊢
        apply (eq_div_iff hd₁ne).2
        rw [add_mul, mul_assoc,
          div_mul_cancel₀ ((k : ℝ) * u) hd₁ne]]
      apply (div_le_div_iff_of_pos_right hd₁).2
      push_cast
      nlinarith [sq_nonneg u]

private lemma gamma_correction_step (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : GammaValid u (k + 1)) :
    gamma u k + u * (1 + gamma u (k + 1)) ≤ gamma u (k + 1) := by
  unfold GammaValid at hk
  have hd₀ : 0 < 1 - (k : ℝ) * u := by
    push_cast at hk
    nlinarith
  have hd₁ : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := by linarith
  have hn : 0 ≤ (k : ℝ) * u := mul_nonneg (by positivity) hu
  have hdle : 1 - ((k + 1 : ℕ) : ℝ) * u ≤ 1 - (k : ℝ) * u := by
    push_cast
    nlinarith
  have hg : gamma u k ≤
      (k : ℝ) * u / (1 - ((k + 1 : ℕ) : ℝ) * u) := by
    unfold gamma
    exact (div_le_div_iff₀ hd₀ hd₁).2 (mul_le_mul_of_nonneg_left hdle hn)
  have hone : 1 + gamma u (k + 1) =
      1 / (1 - ((k + 1 : ℕ) : ℝ) * u) := by
    unfold gamma
    field_simp [ne_of_gt hd₁]
    ring
  rw [hone]
  calc
    gamma u k + u * (1 / (1 - ((k + 1 : ℕ) : ℝ) * u)) ≤
        (k : ℝ) * u / (1 - ((k + 1 : ℕ) : ℝ) * u) +
          u * (1 / (1 - ((k + 1 : ℕ) : ℝ) * u)) := by linarith
    _ = gamma u (k + 1) := by
      unfold gamma
      field_simp [ne_of_gt hd₁]
      push_cast
      ring

private lemma gammaValid_of_le (u : ℝ) (hu : 0 ≤ u) {k m : ℕ}
    (hkm : k ≤ m) (hm : GammaValid u m) : GammaValid u k := by
  unfold GammaValid at hm ⊢
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hkm) hu) hm

private lemma recursiveSum_error (fp : ErrorFreeAddModel) (n : ℕ)
    (v : Fin (n + 1) → ℝ) (hv : GammaValid fp.u (n + 1)) :
    |recursiveSum fp.fl_add (n + 1) v - ∑ i, v i| ≤
      gamma fp.u n * ∑ i, |v i| := by
  induction n with
  | zero =>
      simp [recursiveSum, gamma]
  | succ n ih =>
      let w : Fin (n + 1) → ℝ := fun i => v i.castSucc
      let r := recursiveSum fp.fl_add (n + 1) w
      let t := ∑ i : Fin (n + 1), w i
      let b := v (Fin.last (n + 1))
      let A := ∑ i : Fin (n + 1), |w i|
      have hv' : GammaValid fp.u (n + 1) :=
        gammaValid_of_le fp.u fp.u_nonneg (by omega) hv
      have hi : |r - t| ≤ gamma fp.u n * A := by
        simpa [w, r, t, A] using ih w hv'
      obtain ⟨δ, hδ, hround⟩ := fp.model_add r b
      have hfac : |1 + δ| ≤ 1 + fp.u := by
        calc
          |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le 1 δ
          _ ≤ 1 + fp.u := by norm_num; linarith
      have hsum : (∑ i, v i) = t + b := by
        simpa [w, t, b] using (Fin.sum_univ_castSucc v)
      have habs : (∑ i, |v i|) = A + |b| := by
        simpa [w, A, b] using (Fin.sum_univ_castSucc (fun i => |v i|))
      have hts : |t + b| ≤ A + |b| := by
        calc
          |t + b| ≤ |t| + |b| := abs_add_le t b
          _ ≤ A + |b| := by
            gcongr
            simpa [t, A] using
              (Finset.abs_sum_le_sum_abs w Finset.univ)
      have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hS : 0 ≤ A + |b| := add_nonneg hA (abs_nonneg _)
      have hgam : 0 ≤ gamma fp.u n :=
        gamma_nonneg_of_valid fp.u n fp.u_nonneg
          (gammaValid_of_le fp.u fp.u_nonneg (by omega) hv)
      have herr :
          |fp.fl_add r b - (t + b)| ≤
            (1 + fp.u) * (gamma fp.u n * A) + fp.u * (A + |b|) := by
        rw [hround]
        have hid : (r + b) * (1 + δ) - (t + b) =
            (1 + δ) * (r - t) + δ * (t + b) := by ring
        rw [hid]
        calc
          |(1 + δ) * (r - t) + δ * (t + b)| ≤
              |1 + δ| * |r - t| + |δ| * |t + b| := by
                simpa [abs_mul] using
                  (abs_add_le ((1 + δ) * (r - t)) (δ * (t + b)))
          _ ≤ (1 + fp.u) * (gamma fp.u n * A) +
              fp.u * (A + |b|) := by
                gcongr <;> nlinarith [fp.u_nonneg]
      have hcombine :
          (1 + fp.u) * (gamma fp.u n * A) + fp.u * (A + |b|) ≤
            ((1 + fp.u) * gamma fp.u n + fp.u) * (A + |b|) := by
        nlinarith [mul_nonneg hgam (abs_nonneg b), fp.u_nonneg]
      have hstep := gamma_step fp.u n fp.u_nonneg hv'
      rw [recursiveSum]
      simp only [show n + 1 ≠ 0 by omega, ↓reduceDIte]
      change |fp.fl_add r b - ∑ i, v i| ≤ _
      rw [hsum, habs]
      exact le_trans herr <| le_trans hcombine <|
        mul_le_mul_of_nonneg_right hstep hS

private lemma twoSumPrefix_eq_recursiveSum (fp : ErrorFreeAddModel)
    (n : ℕ) (v : Fin (n + 1) → ℝ) :
    twoSumPrefix fp v n (Nat.le_refl n) =
      recursiveSum fp.fl_add (n + 1) v := by
  induction n with
  | zero => simp [twoSumPrefix, recursiveSum]
  | succ n ih =>
      rw [twoSumPrefix, Fin.foldl_succ_last]
      rw [recursiveSum]
      simp only [show n + 1 ≠ 0 by omega, ↓reduceDIte]
      rw [← fp.twoSum_high]
      apply congrArg Prod.fst
      congr 1
      simpa [twoSumPrefix] using ih (fun i : Fin (n + 1) => v i.castSucc)

private lemma twoSumPrefix_succ (fp : ErrorFreeAddModel) (n : ℕ)
    (v : Fin (n + 2) → ℝ) :
    twoSumPrefix fp v (n + 1) (Nat.le_refl (n + 1)) =
      (fp.twoSum
        (twoSumPrefix fp (fun i : Fin (n + 1) => v i.castSucc)
          n (Nat.le_refl n))
        (v (Fin.last (n + 1)))).1 := by
  simp [twoSumPrefix, Fin.foldl_succ_last]
  congr 3

private lemma twoSumCorrection_castSucc (fp : ErrorFreeAddModel) (n : ℕ)
    (v : Fin (n + 2) → ℝ) (i : Fin n) :
    twoSumCorrection fp v i.castSucc =
      twoSumCorrection fp (fun j : Fin (n + 1) => v j.castSucc) i := by
  simp [twoSumCorrection, twoSumPrefix]

private lemma twoSumCorrection_last (fp : ErrorFreeAddModel) (n : ℕ)
    (v : Fin (n + 2) → ℝ) :
    twoSumCorrection fp v (Fin.last n) =
      (fp.twoSum
        (twoSumPrefix fp (fun i : Fin (n + 1) => v i.castSucc)
          n (Nat.le_refl n))
        (v (Fin.last (n + 1)))).2 := by
  simp [twoSumCorrection, twoSumPrefix]
  congr 3

private lemma twoSum_transform_exact (fp : ErrorFreeAddModel) (n : ℕ)
    (v : Fin (n + 1) → ℝ) :
    twoSumPrefix fp v n (Nat.le_refl n) +
        ∑ i : Fin n, twoSumCorrection fp v i =
      ∑ i : Fin (n + 1), v i := by
  induction n with
  | zero => simp [twoSumPrefix]
  | succ n ih =>
      let w : Fin (n + 1) → ℝ := fun i => v i.castSucc
      let p := twoSumPrefix fp w n (Nat.le_refl n)
      let b := v (Fin.last (n + 1))
      have hi : p + ∑ i : Fin n, twoSumCorrection fp w i = ∑ i, w i := by
        simpa [w, p] using ih w
      have he := fp.twoSum_exact p b
      rw [twoSumPrefix_succ]
      rw [Fin.sum_univ_castSucc]
      simp_rw [twoSumCorrection_castSucc]
      rw [twoSumCorrection_last]
      rw [Fin.sum_univ_castSucc]
      change (fp.twoSum p b).1 +
          ((∑ i : Fin n, twoSumCorrection fp w i) + (fp.twoSum p b).2) =
        (∑ i, w i) + b
      linarith

private lemma twoSum_corrections_bound (fp : ErrorFreeAddModel) (n : ℕ)
    (v : Fin (n + 1) → ℝ) (hv : GammaValid fp.u (n + 1)) :
    (∑ i : Fin n, |twoSumCorrection fp v i|) ≤
      gamma fp.u n * ∑ i : Fin (n + 1), |v i| := by
  induction n with
  | zero => simp [gamma]
  | succ n ih =>
      let w : Fin (n + 1) → ℝ := fun i => v i.castSucc
      let p := twoSumPrefix fp w n (Nat.le_refl n)
      let b := v (Fin.last (n + 1))
      let S₀ := ∑ i : Fin (n + 1), |w i|
      let S := ∑ i : Fin (n + 2), |v i|
      have hv' : GammaValid fp.u (n + 1) :=
        gammaValid_of_le fp.u fp.u_nonneg (by omega) hv
      have hi : (∑ i : Fin n, |twoSumCorrection fp w i|) ≤
          gamma fp.u n * S₀ := by
        simpa [w, S₀] using ih w hv'
      have hS : S = S₀ + |b| := by
        simpa [w, S₀, S, b] using
          (Fin.sum_univ_castSucc (fun i : Fin (n + 2) => |v i|))
      have hS₀ : 0 ≤ S₀ := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hSnonneg : 0 ≤ S := by rw [hS]; positivity
      have hS₀S : S₀ ≤ S := by rw [hS]; linarith [abs_nonneg b]
      have hpref :
          |twoSumPrefix fp v (n + 1) (Nat.le_refl (n + 1)) - ∑ i, v i| ≤
            gamma fp.u (n + 1) * S := by
        rw [twoSumPrefix_eq_recursiveSum]
        simpa [S] using recursiveSum_error fp (n + 1) v hv
      rw [twoSumPrefix_succ] at hpref
      have hsumabs : |∑ i, v i| ≤ S := by
        simpa [S] using (Finset.abs_sum_le_sum_abs v Finset.univ)
      have hhigh : |(fp.twoSum p b).1| ≤
          (1 + gamma fp.u (n + 1)) * S := by
        calc
          |(fp.twoSum p b).1| =
              |((fp.twoSum p b).1 - ∑ i, v i) + ∑ i, v i| := by ring_nf
          _ ≤ |(fp.twoSum p b).1 - ∑ i, v i| + |∑ i, v i| :=
            abs_add_le _ _
          _ ≤ gamma fp.u (n + 1) * S + S := by
            gcongr
          _ = (1 + gamma fp.u (n + 1)) * S := by ring
      have hlow : |(fp.twoSum p b).2| ≤
          fp.u * ((1 + gamma fp.u (n + 1)) * S) :=
        le_trans (fp.twoSum_low_le p b)
          (mul_le_mul_of_nonneg_left hhigh fp.u_nonneg)
      have hgam : 0 ≤ gamma fp.u n :=
        gamma_nonneg_of_valid fp.u n fp.u_nonneg
          (gammaValid_of_le fp.u fp.u_nonneg (by omega) hv)
      have hcoeff := gamma_correction_step fp.u n fp.u_nonneg hv'
      rw [Fin.sum_univ_castSucc]
      simp_rw [twoSumCorrection_castSucc]
      rw [twoSumCorrection_last]
      change (∑ i : Fin n, |twoSumCorrection fp w i|) +
          |(fp.twoSum p b).2| ≤ gamma fp.u (n + 1) * S
      calc
        (∑ i : Fin n, |twoSumCorrection fp w i|) +
              |(fp.twoSum p b).2| ≤
            gamma fp.u n * S₀ +
              fp.u * ((1 + gamma fp.u (n + 1)) * S) :=
          add_le_add hi hlow
        _ ≤ (gamma fp.u n +
              fp.u * (1 + gamma fp.u (n + 1))) * S := by
          nlinarith [mul_nonneg hgam (sub_nonneg.mpr hS₀S)]
        _ ≤ gamma fp.u (n + 1) * S :=
          mul_le_mul_of_nonneg_right hcoeff hSnonneg

private lemma vecSum_sum_eq (fp : ErrorFreeAddModel) (n : ℕ)
    (v : Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1), vecSum fp v i) = ∑ i, v i := by
  rw [Fin.sum_univ_castSucc]
  simp only [vecSum, Fin.lastCases_castSucc, Fin.lastCases_last]
  have h := twoSum_transform_exact fp n v
  linarith

private lemma vecSum_castSucc (fp : ErrorFreeAddModel) (n : ℕ)
    (v : Fin (n + 1) → ℝ) (i : Fin n) :
    vecSum fp v i.castSucc = twoSumCorrection fp v i := by
  simp [vecSum]

private lemma vecSum_last (fp : ErrorFreeAddModel) (n : ℕ)
    (v : Fin (n + 1) → ℝ) :
    vecSum fp v (Fin.last n) =
      twoSumPrefix fp v n (Nat.le_refl n) := by
  simp [vecSum]

theorem p02_t1_sum2_error_bound
    (fp : ErrorFreeAddModel) (n : ℕ) (v : Fin (n + 1) → ℝ)
    (hvalid : GammaValid fp.u (n + 1)) :
    |sum2 fp v - ∑ i : Fin (n + 1), v i| ≤
      fp.u * |∑ i : Fin (n + 1), v i| +
        (gamma fp.u n) ^ 2 * ∑ i : Fin (n + 1), |v i| := by
  -- PROOF_START P02-T1-H001
  cases n with
  | zero =>
      have he : sum2 fp v = ∑ i : Fin 1, vecSum fp v i := by
        simp [sum2, sumK, iteratedVecSum, recursiveSum]
      rw [he, vecSum_sum_eq]
      simp [gamma]
      exact mul_nonneg fp.u_nonneg (abs_nonneg _)
  | succ k =>
      let z : Fin (k + 2) → ℝ := vecSum fp v
      let q : Fin (k + 1) → ℝ := fun i => z i.castSucc
      let r := recursiveSum fp.fl_add (k + 1) q
      let p := z (Fin.last (k + 1))
      let s := ∑ i : Fin (k + 2), v i
      let S := ∑ i : Fin (k + 2), |v i|
      let tq := ∑ i : Fin (k + 1), q i
      let Q := ∑ i : Fin (k + 1), |q i|
      have hvq : GammaValid fp.u (k + 1) :=
        gammaValid_of_le fp.u fp.u_nonneg (by omega) hvalid
      have hr : |r - tq| ≤ gamma fp.u k * Q := by
        simpa [r, tq, Q] using recursiveSum_error fp k q hvq
      have hQid : Q =
          ∑ i : Fin (k + 1), |twoSumCorrection fp v i| := by
        simp only [Q, q, z, vecSum_castSucc]
      have hQ : Q ≤ gamma fp.u (k + 1) * S := by
        rw [hQid]
        simpa [S] using twoSum_corrections_bound fp (k + 1) v hvalid
      have hsumz : (∑ i : Fin (k + 2), z i) = s := by
        simpa [z, s] using vecSum_sum_eq fp (k + 1) v
      have hsplit : s = tq + p := by
        rw [← hsumz]
        simpa [q, tq, p] using (Fin.sum_univ_castSucc z)
      have hsum2 : sum2 fp v = fp.fl_add r p := by
        simp [sum2, sumK, iteratedVecSum, recursiveSum, z, q, r, p]
      obtain ⟨δ, hδ, hround⟩ := fp.model_add r p
      have hfac : |1 + δ| ≤ 1 + fp.u := by
        calc
          |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le 1 δ
          _ ≤ 1 + fp.u := by norm_num; linarith
      have hfirst : |sum2 fp v - s| ≤
          (1 + fp.u) * (gamma fp.u k * Q) + fp.u * |s| := by
        rw [hsum2, hround]
        have hid : (r + p) * (1 + δ) - s =
            (1 + δ) * (r - tq) + δ * s := by
          rw [hsplit]
          ring
        rw [hid]
        calc
          |(1 + δ) * (r - tq) + δ * s| ≤
              |1 + δ| * |r - tq| + |δ| * |s| := by
            simpa [abs_mul] using
              (abs_add_le ((1 + δ) * (r - tq)) (δ * s))
          _ ≤ (1 + fp.u) * (gamma fp.u k * Q) + fp.u * |s| := by
            gcongr <;> nlinarith [fp.u_nonneg]
      have hgamk : 0 ≤ gamma fp.u k :=
        gamma_nonneg_of_valid fp.u k fp.u_nonneg
          (gammaValid_of_le fp.u fp.u_nonneg (by omega) hvalid)
      have hgam : 0 ≤ gamma fp.u (k + 1) :=
        gamma_nonneg_of_valid fp.u (k + 1) fp.u_nonneg hvq
      have hstep := gamma_step fp.u k fp.u_nonneg hvq
      have hcoef : (1 + fp.u) * gamma fp.u k * gamma fp.u (k + 1) ≤
          (gamma fp.u (k + 1)) ^ 2 := by
        have hb : (1 + fp.u) * gamma fp.u k ≤ gamma fp.u (k + 1) := by
          linarith [fp.u_nonneg]
        calc
          (1 + fp.u) * gamma fp.u k * gamma fp.u (k + 1) ≤
              gamma fp.u (k + 1) * gamma fp.u (k + 1) :=
            mul_le_mul_of_nonneg_right hb hgam
          _ = (gamma fp.u (k + 1)) ^ 2 := by ring
      have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
      change |sum2 fp v - s| ≤
        fp.u * |s| + (gamma fp.u (k + 1)) ^ 2 * S
      calc
        |sum2 fp v - s| ≤
            (1 + fp.u) * (gamma fp.u k * Q) + fp.u * |s| := hfirst
        _ ≤ (1 + fp.u) *
              (gamma fp.u k * (gamma fp.u (k + 1) * S)) + fp.u * |s| := by
          gcongr <;> nlinarith [fp.u_nonneg]
        _ = ((1 + fp.u) * gamma fp.u k * gamma fp.u (k + 1)) * S +
              fp.u * |s| := by ring
        _ ≤ (gamma fp.u (k + 1)) ^ 2 * S + fp.u * |s| := by
          gcongr
        _ = fp.u * |s| + (gamma fp.u (k + 1)) ^ 2 * S := by ring

end HighamBench
