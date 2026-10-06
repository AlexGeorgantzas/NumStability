import HighamBench.P02Definitions

namespace HighamBench

open scoped BigOperators

lemma twoSumPrefix_zero (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) :
    twoSumPrefix fp v 0 (Nat.zero_le n) = v ⟨0, Nat.succ_pos n⟩ := by
  simp [twoSumPrefix]

lemma twoSumPrefix_succ (fp : ErrorFreeAddModel) {n k : ℕ}
    (v : Fin (n + 1) → ℝ) (hk : k + 1 ≤ n) :
    twoSumPrefix fp v (k + 1) hk =
      (fp.twoSum
        (twoSumPrefix fp v k (Nat.le_trans (Nat.le_succ k) hk))
        (v ⟨k + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)⟩)).1 := by
  simp only [twoSumPrefix, Fin.foldl_succ_last]
  congr 3

lemma twoSumPrefix_exact (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : k ≤ n) :
    twoSumPrefix fp v k hk +
        ∑ i : Fin k,
          twoSumCorrection fp v
            ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ =
      ∑ j : Fin (k + 1),
        v ⟨j.val,
          Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk)⟩ := by
  induction k with
  | zero =>
      simp [twoSumPrefix_zero]
  | succ k ih =>
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      rw [twoSumPrefix_succ]
      simp only [Fin.val_castSucc, Fin.val_last]
      have hih := ih (Nat.le_trans (Nat.le_succ k) hk)
      have hex := fp.twoSum_exact
        (twoSumPrefix fp v k (Nat.le_trans (Nat.le_succ k) hk))
        (v ⟨k + 1,
          Nat.succ_lt_succ (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)⟩)
      have hcorr :
          twoSumCorrection fp v ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩ =
            (fp.twoSum
              (twoSumPrefix fp v k (Nat.le_trans (Nat.le_succ k) hk))
              (v ⟨k + 1,
                Nat.succ_lt_succ
                  (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)⟩)).2 := by
        simp [twoSumCorrection]
      rw [hcorr]
      linarith [hih, hex]

lemma vecSum_sum (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) :
    ∑ i : Fin (n + 1), vecSum fp v i = ∑ i : Fin (n + 1), v i := by
  rw [Fin.sum_univ_castSucc]
  simp only [vecSum, Fin.lastCases_castSucc, Fin.lastCases_last]
  have h := twoSumPrefix_exact fp v n (Nat.le_refl n)
  linarith

lemma one_add_gamma (u : ℝ) (k : ℕ) (hvalid : GammaValid u k) :
    1 + gamma u k = 1 / (1 - (k : ℝ) * u) := by
  have hden : 1 - (k : ℝ) * u ≠ 0 := by
    unfold GammaValid at hvalid
    linarith
  unfold gamma
  field_simp
  ring

lemma gamma_nonneg (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hvalid : GammaValid u k) : 0 ≤ gamma u k := by
  unfold gamma GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg k) hu) (by linarith)

lemma gamma_step_round (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hvalid : GammaValid u (k + 1)) :
    (1 + u) * gamma u k + u ≤ gamma u (k + 1) := by
  have hkvalid : GammaValid u k := by
    unfold GammaValid at *
    push_cast at hvalid ⊢
    nlinarith [mul_nonneg (Nat.cast_nonneg k) hu]
  have hkpos : 0 < 1 - (k : ℝ) * u := by
    unfold GammaValid at hkvalid
    linarith
  have hspos : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := by
    unfold GammaValid at hvalid
    linarith
  have hkpos' : 0 < 1 - u * (k : ℝ) := by nlinarith
  have hnum : 0 ≤ ((k + 1 : ℕ) : ℝ) * u :=
    mul_nonneg (Nat.cast_nonneg _) hu
  have hid :
      (1 + u) * gamma u k + u =
        (((k + 1 : ℕ) : ℝ) * u) / (1 - (k : ℝ) * u) := by
    unfold gamma
    field_simp [ne_of_gt hkpos, ne_of_gt hkpos']
    push_cast
    ring
  rw [hid]
  unfold gamma
  apply div_le_div₀ hnum le_rfl hspos
  push_cast
  nlinarith

lemma gamma_step_correction (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hvalid : GammaValid u (k + 1)) :
    gamma u k + u * (1 + gamma u (k + 1)) ≤ gamma u (k + 1) := by
  have hkvalid : GammaValid u k := by
    unfold GammaValid at *
    push_cast at hvalid ⊢
    nlinarith [mul_nonneg (Nat.cast_nonneg k) hu]
  have hkpos : 0 < 1 - (k : ℝ) * u := by
    unfold GammaValid at hkvalid
    linarith
  have hspos : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := by
    unfold GammaValid at hvalid
    linarith
  have hspos' : 0 < 1 - u * ((k + 1 : ℕ) : ℝ) := by nlinarith
  have hknum : 0 ≤ (k : ℝ) * u :=
    mul_nonneg (Nat.cast_nonneg _) hu
  have hfrac :
      ((k : ℝ) * u) / (1 - (k : ℝ) * u) ≤
        ((k : ℝ) * u) / (1 - ((k + 1 : ℕ) : ℝ) * u) := by
    apply div_le_div₀ hknum le_rfl hspos
    push_cast
    nlinarith
  rw [one_add_gamma u (k + 1) hvalid]
  unfold gamma
  calc
    (k : ℝ) * u / (1 - (k : ℝ) * u) +
          u * (1 / (1 - ((k + 1 : ℕ) : ℝ) * u)) ≤
        (k : ℝ) * u / (1 - ((k + 1 : ℕ) : ℝ) * u) +
          u * (1 / (1 - ((k + 1 : ℕ) : ℝ) * u)) := by
            gcongr
    _ = ((k + 1 : ℕ) : ℝ) * u /
          (1 - ((k + 1 : ℕ) : ℝ) * u) := by
            field_simp [ne_of_gt hspos, ne_of_gt hspos']
            push_cast
            ring

lemma recursiveSum_error (fp : StandardAddModel) (k : ℕ)
    (w : Fin (k + 1) → ℝ) (hvalid : GammaValid fp.u k) :
    |recursiveSum fp.fl_add (k + 1) w - ∑ i, w i| ≤
      gamma fp.u k * ∑ i, |w i| := by
  induction k with
  | zero =>
      simp [recursiveSum, gamma]
  | succ k ih =>
      change
        |fp.fl_add
              (recursiveSum fp.fl_add (k + 1) (fun i => w i.castSucc))
              (w (Fin.last (k + 1))) - ∑ i, w i| ≤
          gamma fp.u (k + 1) * ∑ i, |w i|
      rw [Fin.sum_univ_castSucc (fun i => w i),
        Fin.sum_univ_castSucc (fun i => |w i|)]
      have hkvalid : GammaValid fp.u k := by
        unfold GammaValid at *
        push_cast at hvalid ⊢
        nlinarith [mul_nonneg (Nat.cast_nonneg k) fp.u_nonneg]
      have hi := ih (fun i => w i.castSucc) hkvalid
      obtain ⟨δ, hδ, hfl⟩ := fp.model_add
        (recursiveSum fp.fl_add (k + 1) (fun i => w i.castSucc))
        (w (Fin.last (k + 1)))
      rw [hfl]
      have hfac : |1 + δ| ≤ 1 + fp.u := by
        calc
          |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le 1 δ
          _ ≤ 1 + fp.u := by norm_num; linarith
      have hsum :
          |∑ i : Fin (k + 1), w i.castSucc| ≤
            ∑ i : Fin (k + 1), |w i.castSucc| := by
        simpa using
          (Finset.abs_sum_le_sum_abs
            (fun i : Fin (k + 1) => w i.castSucc) Finset.univ)
      have htotal :
          |(∑ i : Fin (k + 1), w i.castSucc) + w (Fin.last (k + 1))| ≤
            (∑ i : Fin (k + 1), |w i.castSucc|) +
              |w (Fin.last (k + 1))| := by
        calc
          |(∑ i : Fin (k + 1), w i.castSucc) + w (Fin.last (k + 1))| ≤
              |∑ i : Fin (k + 1), w i.castSucc| +
                |w (Fin.last (k + 1))| := abs_add_le _ _
          _ ≤ (∑ i : Fin (k + 1), |w i.castSucc|) +
                |w (Fin.last (k + 1))| := by gcongr
      have hmain :
          |(recursiveSum fp.fl_add (k + 1) (fun i => w i.castSucc) +
                  w (Fin.last (k + 1))) * (1 + δ) -
                ((∑ i : Fin (k + 1), w i.castSucc) +
                  w (Fin.last (k + 1)))| ≤
            (1 + fp.u) *
                (gamma fp.u k * ∑ i : Fin (k + 1), |w i.castSucc|) +
              fp.u * ((∑ i : Fin (k + 1), |w i.castSucc|) +
                |w (Fin.last (k + 1))|) := by
        calc
          |(recursiveSum fp.fl_add (k + 1) (fun i => w i.castSucc) +
                    w (Fin.last (k + 1))) * (1 + δ) -
                  ((∑ i : Fin (k + 1), w i.castSucc) +
                    w (Fin.last (k + 1)))| =
              |(1 + δ) *
                    (recursiveSum fp.fl_add (k + 1) (fun i => w i.castSucc) -
                      ∑ i : Fin (k + 1), w i.castSucc) +
                δ * ((∑ i : Fin (k + 1), w i.castSucc) +
                  w (Fin.last (k + 1)))| := by
                    congr 1
                    ring
          _ ≤ |1 + δ| *
                    |recursiveSum fp.fl_add (k + 1) (fun i => w i.castSucc) -
                      ∑ i : Fin (k + 1), w i.castSucc| +
                  |δ| * |(∑ i : Fin (k + 1), w i.castSucc) +
                    w (Fin.last (k + 1))| := by
                      calc
                        |_ + _| ≤ |(1 + δ) *
                              (recursiveSum fp.fl_add (k + 1)
                                  (fun i => w i.castSucc) -
                                ∑ i : Fin (k + 1), w i.castSucc)| +
                            |δ * ((∑ i : Fin (k + 1), w i.castSucc) +
                              w (Fin.last (k + 1)))| := abs_add_le _ _
                        _ = _ := by rw [abs_mul, abs_mul]
          _ ≤ (1 + fp.u) *
                    (gamma fp.u k * ∑ i : Fin (k + 1), |w i.castSucc|) +
                  fp.u * ((∑ i : Fin (k + 1), |w i.castSucc|) +
                    |w (Fin.last (k + 1))|) := by
                      gcongr
                      all_goals nlinarith [fp.u_nonneg]
      calc
        |(recursiveSum fp.fl_add (k + 1) (fun i => w i.castSucc) +
                w (Fin.last (k + 1))) * (1 + δ) -
              ((∑ i : Fin (k + 1), w i.castSucc) +
                w (Fin.last (k + 1)))| ≤
            (1 + fp.u) *
                (gamma fp.u k * ∑ i : Fin (k + 1), |w i.castSucc|) +
              fp.u * ((∑ i : Fin (k + 1), |w i.castSucc|) +
                |w (Fin.last (k + 1))|) := hmain
        _ ≤ ((1 + fp.u) * gamma fp.u k + fp.u) *
              ((∑ i : Fin (k + 1), |w i.castSucc|) +
                |w (Fin.last (k + 1))|) := by
                  have hg := gamma_nonneg fp.u k fp.u_nonneg hkvalid
                  have hs : 0 ≤ ∑ i : Fin (k + 1), |w i.castSucc| := by positivity
                  have hb : 0 ≤ |w (Fin.last (k + 1))| := abs_nonneg _
                  have hc : 0 ≤ (1 + fp.u) * gamma fp.u k :=
                    mul_nonneg (by linarith [fp.u_nonneg]) hg
                  nlinarith [mul_nonneg hc hb]
        _ ≤ gamma fp.u (k + 1) *
              ((∑ i : Fin (k + 1), |w i.castSucc|) +
                |w (Fin.last (k + 1))|) := by
                  exact mul_le_mul_of_nonneg_right
                    (gamma_step_round fp.u k fp.u_nonneg hvalid) (by positivity)

lemma twoSumPrefix_eq_recursiveSum (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : k ≤ n) :
    twoSumPrefix fp v k hk =
      recursiveSum fp.fl_add (k + 1)
        (fun j => v ⟨j.val,
          Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk)⟩) := by
  induction k with
  | zero =>
      simp [twoSumPrefix_zero, recursiveSum]
  | succ k ih =>
      rw [twoSumPrefix_succ, fp.twoSum_high]
      change fp.fl_add _ _ = fp.fl_add
        (recursiveSum fp.fl_add (k + 1)
          (fun i => v ⟨i.castSucc.val, _⟩))
        (v ⟨(Fin.last (k + 1)).val, _⟩)
      rw [ih (Nat.le_trans (Nat.le_succ k) hk)]
      congr 2

lemma twoSumPrefix_error (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : k ≤ n)
    (hvalid : GammaValid fp.u k) :
    |twoSumPrefix fp v k hk -
        ∑ j : Fin (k + 1),
          v ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk)⟩| ≤
      gamma fp.u k *
        ∑ j : Fin (k + 1),
          |v ⟨j.val,
            Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk)⟩| := by
  rw [twoSumPrefix_eq_recursiveSum]
  exact recursiveSum_error fp.toStandardAddModel k _ hvalid

lemma twoSumCorrection_abs_sum_le (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : k ≤ n)
    (hvalid : GammaValid fp.u k) :
    (∑ i : Fin k,
        |twoSumCorrection fp v
          ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩|) ≤
      gamma fp.u k *
        ∑ j : Fin (k + 1),
          |v ⟨j.val,
            Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk)⟩| := by
  induction k with
  | zero =>
      simp [gamma]
  | succ k ih =>
      rw [Fin.sum_univ_castSucc (fun i : Fin (k + 1) =>
        |twoSumCorrection fp v
          ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩|)]
      simp only [Fin.val_castSucc, Fin.val_last]
      have hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      have hkvalid : GammaValid fp.u k := by
        unfold GammaValid at *
        push_cast at hvalid ⊢
        nlinarith [mul_nonneg (Nat.cast_nonneg k) fp.u_nonneg]
      have hi := ih hk' hkvalid
      have hlow :
          |twoSumCorrection fp v
              ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩| ≤
            fp.u * |twoSumPrefix fp v (k + 1) hk| := by
        rw [twoSumPrefix_succ]
        simpa [twoSumCorrection] using
          (fp.twoSum_low_le
            (twoSumPrefix fp v k hk')
            (v ⟨k + 1,
              Nat.succ_lt_succ
                (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)⟩))
      have hpre := twoSumPrefix_error fp v (k + 1) hk hvalid
      have hsum :
          |∑ j : Fin (k + 2),
              v ⟨j.val,
                Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk)⟩| ≤
            ∑ j : Fin (k + 2),
              |v ⟨j.val,
                Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk)⟩| := by
        simpa using (Finset.abs_sum_le_sum_abs
          (fun j : Fin (k + 2) =>
            v ⟨j.val,
              Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk)⟩)
          Finset.univ)
      have hpabs :
          |twoSumPrefix fp v (k + 1) hk| ≤
            (1 + gamma fp.u (k + 1)) *
              ∑ j : Fin (k + 2),
                |v ⟨j.val,
                  Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk)⟩| := by
        calc
          |twoSumPrefix fp v (k + 1) hk| =
              |(twoSumPrefix fp v (k + 1) hk -
                    ∑ j : Fin (k + 2),
                      v ⟨j.val,
                        Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk)⟩) +
                ∑ j : Fin (k + 2),
                  v ⟨j.val,
                    Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk)⟩| := by
                      congr 1
                      ring
          _ ≤ |twoSumPrefix fp v (k + 1) hk -
                    ∑ j : Fin (k + 2),
                      v ⟨j.val,
                        Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk)⟩| +
                |∑ j : Fin (k + 2),
                  v ⟨j.val,
                    Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk)⟩| :=
                      abs_add_le _ _
          _ ≤ gamma fp.u (k + 1) *
                    (∑ j : Fin (k + 2),
                      |v ⟨j.val,
                        Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk)⟩|) +
                ∑ j : Fin (k + 2),
                  |v ⟨j.val,
                    Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk)⟩| := by
                      gcongr
          _ = (1 + gamma fp.u (k + 1)) *
                ∑ j : Fin (k + 2),
                  |v ⟨j.val,
                    Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk)⟩| := by
                      ring
      have hcurrent :
          |twoSumCorrection fp v
              ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩| ≤
            fp.u * (1 + gamma fp.u (k + 1)) *
              ∑ j : Fin (k + 2),
                |v ⟨j.val,
                  Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk)⟩| := by
        calc
          _ ≤ fp.u * |twoSumPrefix fp v (k + 1) hk| := hlow
          _ ≤ fp.u * ((1 + gamma fp.u (k + 1)) *
                ∑ j : Fin (k + 2),
                  |v ⟨j.val,
                    Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk)⟩|) := by
                      exact mul_le_mul_of_nonneg_left hpabs fp.u_nonneg
          _ = _ := by ring
      calc
        (∑ i : Fin k,
              |twoSumCorrection fp v
                ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk'⟩|) +
            |twoSumCorrection fp v
              ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩| ≤
          gamma fp.u k *
              (∑ j : Fin (k + 1),
                |v ⟨j.val,
                  Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk')⟩|) +
            fp.u * (1 + gamma fp.u (k + 1)) *
              ∑ j : Fin (k + 2),
                |v ⟨j.val,
                  Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk)⟩| :=
                    add_le_add hi hcurrent
        _ ≤ gamma fp.u k *
              (∑ j : Fin (k + 2),
                |v ⟨j.val,
                  Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk)⟩|) +
            fp.u * (1 + gamma fp.u (k + 1)) *
              ∑ j : Fin (k + 2),
                |v ⟨j.val,
                  Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk)⟩| := by
                    gcongr
                    · exact gamma_nonneg fp.u k fp.u_nonneg hkvalid
                    · rw [Fin.sum_univ_castSucc (fun j : Fin (k + 2) =>
                        |v ⟨j.val,
                          Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk)⟩|)]
                      simp
        _ = (gamma fp.u k +
              fp.u * (1 + gamma fp.u (k + 1))) *
              ∑ j : Fin (k + 2),
                |v ⟨j.val,
                  Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk)⟩| := by
                    ring
        _ ≤ gamma fp.u (k + 1) *
              ∑ j : Fin (k + 2),
                |v ⟨j.val,
                  Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk)⟩| := by
                    exact mul_le_mul_of_nonneg_right
                      (gamma_step_correction fp.u k fp.u_nonneg hvalid)
                      (by positivity)

lemma sum2_succ (fp : ErrorFreeAddModel) (m : ℕ)
    (v : Fin (m + 2) → ℝ) :
    sum2 fp v =
      fp.fl_add
        (recursiveSum fp.fl_add (m + 1)
          (fun i : Fin (m + 1) => twoSumCorrection fp v i))
        (twoSumPrefix fp v (m + 1) (Nat.le_refl (m + 1))) := by
  unfold sum2 sumK
  norm_num [iteratedVecSum]
  rw [recursiveSum]
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
      simp [sum2, sumK, iteratedVecSum, vecSum, twoSumPrefix,
        recursiveSum, gamma]
      change |v 0 - v 0| ≤ fp.u * |v 0|
      simpa using mul_nonneg fp.u_nonneg (abs_nonneg (v 0))
  | succ m =>
      rw [sum2_succ]
      change
        |fp.fl_add
              (recursiveSum fp.fl_add (m + 1)
                (fun i : Fin (m + 1) => twoSumCorrection fp v i))
              (twoSumPrefix fp v (m + 1) (Nat.le_refl (m + 1))) -
            ∑ i : Fin (m + 2), v i| ≤
          fp.u * |∑ i : Fin (m + 2), v i| +
            gamma fp.u (m + 1) ^ 2 *
              ∑ i : Fin (m + 2), |v i|
      have hnvalid : GammaValid fp.u (m + 1) := by
        unfold GammaValid at *
        push_cast at hvalid ⊢
        nlinarith [mul_nonneg (Nat.cast_nonneg m) fp.u_nonneg]
      have hmvalid : GammaValid fp.u m := by
        unfold GammaValid at *
        push_cast at hnvalid ⊢
        nlinarith [mul_nonneg (Nat.cast_nonneg m) fp.u_nonneg]
      have hqerr := recursiveSum_error fp.toStandardAddModel m
        (fun i : Fin (m + 1) => twoSumCorrection fp v i) hmvalid
      have hcorr := twoSumCorrection_abs_sum_le fp v (m + 1)
        (Nat.le_refl (m + 1)) hnvalid
      have hexact := twoSumPrefix_exact fp v (m + 1)
        (Nat.le_refl (m + 1))
      have hexact' :
          twoSumPrefix fp v (m + 1) (Nat.le_refl (m + 1)) +
              ∑ i : Fin (m + 1), twoSumCorrection fp v i =
            ∑ i : Fin (m + 2), v i := by
        simpa using hexact
      have hcorr' :
          (∑ i : Fin (m + 1), |twoSumCorrection fp v i|) ≤
            gamma fp.u (m + 1) *
              ∑ i : Fin (m + 2), |v i| := by
        simpa using hcorr
      obtain ⟨δ, hδ, hfl⟩ := fp.model_add
        (recursiveSum fp.fl_add (m + 1)
          (fun i : Fin (m + 1) => twoSumCorrection fp v i))
        (twoSumPrefix fp v (m + 1) (Nat.le_refl (m + 1)))
      rw [hfl]
      have hfac : |1 + δ| ≤ 1 + fp.u := by
        calc
          |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le 1 δ
          _ ≤ 1 + fp.u := by norm_num; linarith
      have hfirst :
          |(recursiveSum fp.fl_add (m + 1)
                  (fun i : Fin (m + 1) => twoSumCorrection fp v i) +
                twoSumPrefix fp v (m + 1) (Nat.le_refl (m + 1))) *
                (1 + δ) - ∑ i : Fin (m + 2), v i| ≤
            (1 + fp.u) *
                (gamma fp.u m *
                  ∑ i : Fin (m + 1), |twoSumCorrection fp v i|) +
              fp.u * |∑ i : Fin (m + 2), v i| := by
        calc
          |(recursiveSum fp.fl_add (m + 1)
                    (fun i : Fin (m + 1) => twoSumCorrection fp v i) +
                  twoSumPrefix fp v (m + 1) (Nat.le_refl (m + 1))) *
                  (1 + δ) - ∑ i : Fin (m + 2), v i| =
              |(1 + δ) *
                    (recursiveSum fp.fl_add (m + 1)
                        (fun i : Fin (m + 1) => twoSumCorrection fp v i) -
                      ∑ i : Fin (m + 1), twoSumCorrection fp v i) +
                δ * (∑ i : Fin (m + 2), v i)| := by
                  congr 1
                  rw [← hexact']
                  ring
          _ ≤ |1 + δ| *
                  |recursiveSum fp.fl_add (m + 1)
                      (fun i : Fin (m + 1) => twoSumCorrection fp v i) -
                    ∑ i : Fin (m + 1), twoSumCorrection fp v i| +
                |δ| * |∑ i : Fin (m + 2), v i| := by
                  calc
                    |_ + _| ≤
                        |(1 + δ) *
                          (recursiveSum fp.fl_add (m + 1)
                              (fun i : Fin (m + 1) => twoSumCorrection fp v i) -
                            ∑ i : Fin (m + 1), twoSumCorrection fp v i)| +
                        |δ * (∑ i : Fin (m + 2), v i)| := abs_add_le _ _
                    _ = _ := by rw [abs_mul, abs_mul]
          _ ≤ (1 + fp.u) *
                  (gamma fp.u m *
                    ∑ i : Fin (m + 1), |twoSumCorrection fp v i|) +
                fp.u * |∑ i : Fin (m + 2), v i| := by
                  gcongr
                  all_goals nlinarith [fp.u_nonneg]
      have hgm := gamma_nonneg fp.u m fp.u_nonneg hmvalid
      have hgn := gamma_nonneg fp.u (m + 1) fp.u_nonneg hnvalid
      have hcoef :
          (1 + fp.u) * gamma fp.u m ≤ gamma fp.u (m + 1) := by
        have hs := gamma_step_round fp.u m fp.u_nonneg hnvalid
        linarith [fp.u_nonneg]
      calc
        |(recursiveSum fp.fl_add (m + 1)
                (fun i : Fin (m + 1) => twoSumCorrection fp v i) +
              twoSumPrefix fp v (m + 1) (Nat.le_refl (m + 1))) *
              (1 + δ) - ∑ i : Fin (m + 2), v i| ≤
            (1 + fp.u) *
                (gamma fp.u m *
                  ∑ i : Fin (m + 1), |twoSumCorrection fp v i|) +
              fp.u * |∑ i : Fin (m + 2), v i| := hfirst
        _ = ((1 + fp.u) * gamma fp.u m) *
                (∑ i : Fin (m + 1), |twoSumCorrection fp v i|) +
              fp.u * |∑ i : Fin (m + 2), v i| := by ring
        _ ≤ ((1 + fp.u) * gamma fp.u m) *
                (gamma fp.u (m + 1) *
                  ∑ i : Fin (m + 2), |v i|) +
              fp.u * |∑ i : Fin (m + 2), v i| := by
                gcongr
                exact mul_nonneg (by nlinarith [fp.u_nonneg]) hgm
        _ ≤ gamma fp.u (m + 1) *
                (gamma fp.u (m + 1) *
                  ∑ i : Fin (m + 2), |v i|) +
              fp.u * |∑ i : Fin (m + 2), v i| := by
                gcongr
        _ = fp.u * |∑ i : Fin (m + 2), v i| +
              gamma fp.u (m + 1) ^ 2 *
                ∑ i : Fin (m + 2), |v i| := by ring

end HighamBench
