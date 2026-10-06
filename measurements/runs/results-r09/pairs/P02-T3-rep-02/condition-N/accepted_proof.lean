import HighamBench.P02Definitions

namespace HighamBench

open scoped BigOperators

private lemma fin_foldl_succ_last {α : Type*} {q : ℕ}
    (f : α → Fin (q + 1) → α) (a : α) :
    Fin.foldl (q + 1) f a =
      f (Fin.foldl q (fun s i => f s i.castSucc) a) (Fin.last q) := by
  induction q generalizing a with
  | zero => simp [Fin.foldl_succ, Fin.foldl_zero]
  | succ q ih =>
      rw [Fin.foldl_succ]
      rw [ih]
      have hf : (fun s (i : Fin q) => f s i.castSucc.succ) =
          (fun s (i : Fin q) => f s i.succ.castSucc) := by
        funext s i
        congr 1
      rw [hf]
      have hz : (0 : Fin (q + 1 + 1)) = (0 : Fin (q + 1)).castSucc := by
        apply Fin.ext
        rfl
      have hl : (Fin.last q).succ = Fin.last (q + 1) := by
        apply Fin.ext
        rfl
      rw [hz, hl]
      rw [Fin.foldl_succ]

private lemma twoSumPrefix_zero (fp : ErrorFreeAddModel) {q : ℕ}
    (v : Fin (q + 1) → ℝ) :
    twoSumPrefix fp v 0 (Nat.zero_le q) = v 0 := by
  simp [twoSumPrefix, Fin.foldl_zero]

private lemma twoSumPrefix_succ (fp : ErrorFreeAddModel) {q k : ℕ}
    (v : Fin (q + 1) → ℝ) (hk : k + 1 ≤ q) :
    twoSumPrefix fp v (k + 1) hk =
      (fp.twoSum
        (twoSumPrefix fp v k (Nat.le_trans (Nat.le_succ k) hk))
        (v ⟨k + 1, Nat.succ_lt_succ hk⟩)).1 := by
  simp only [twoSumPrefix]
  rw [fin_foldl_succ_last]
  congr 2

private lemma twoSumPrefix_castSucc (fp : ErrorFreeAddModel) {q k : ℕ}
    (v : Fin (q + 1 + 1) → ℝ) (hk : k ≤ q) :
    twoSumPrefix fp (fun i : Fin (q + 1) => v i.castSucc) k hk =
      twoSumPrefix fp v k (Nat.le_trans hk (Nat.le_succ q)) := by
  simp only [twoSumPrefix]
  congr 2

private lemma vecSum_exact_sum (fp : ErrorFreeAddModel) {q : ℕ}
    (v : Fin (q + 1) → ℝ) :
    ∑ i, vecSum fp v i = ∑ i, v i := by
  rw [Fin.sum_univ_castSucc]
  simp only [vecSum, Fin.lastCases_castSucc, Fin.lastCases_last]
  induction q with
  | zero =>
      simp [twoSumPrefix_zero]
  | succ q ih =>
      rw [Fin.sum_univ_castSucc]
      rw [twoSumPrefix_succ]
      have hlow : twoSumCorrection fp v (Fin.last q) =
          (fp.twoSum (twoSumPrefix fp v q (Nat.le_succ q))
            (v ⟨q + 1, by omega⟩)).2 := by
        simp only [twoSumCorrection]
        congr 2
      rw [hlow]
      rw [add_assoc]
      rw [add_comm
        ((fp.twoSum (twoSumPrefix fp v q (Nat.le_succ q))
          (v ⟨q + 1, by omega⟩)).2)]
      rw [fp.twoSum_exact]
      rw [← add_assoc]
      have hcorr : (fun i : Fin q => twoSumCorrection fp v i.castSucc) =
          (fun i : Fin q => twoSumCorrection fp
            (fun j : Fin (q + 1) => v j.castSucc) i) := by
        funext i
        simp only [twoSumCorrection]
        rw [twoSumPrefix_castSucc]
        congr 2
      rw [hcorr]
      rw [← twoSumPrefix_castSucc]
      rw [ih (fun i => v i.castSucc)]
      · rw [Fin.sum_univ_castSucc (fun i : Fin (q + 1 + 1) => v i)]
        rw [Fin.sum_univ_castSucc (fun i : Fin (q + 1) => v i.castSucc)]
        congr 2
      · exact Nat.le_refl q

private lemma fin_sum_castLE_le {a b : ℕ} (h : a ≤ b)
    (f : Fin b → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ i : Fin a, f (Fin.castLE h i) ≤ ∑ i : Fin b, f i := by
  let e : Fin a ↪ Fin b := Fin.castLEEmb h
  calc
    ∑ i : Fin a, f (Fin.castLE h i) =
        ∑ j ∈ Finset.univ.map e, f j := by
          rw [Finset.sum_map]
          rfl
    _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin b)), f j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i hi₁ hi₂
      exact hf i
    _ = ∑ i : Fin b, f i := by simp

private lemma twoSumPrefix_exact (fp : ErrorFreeAddModel) {q k : ℕ}
    (v : Fin (q + 1) → ℝ) (hk : k ≤ q) :
    twoSumPrefix fp v k hk +
        (∑ i : Fin k, twoSumCorrection fp v (Fin.castLE hk i)) =
      (∑ i : Fin (k + 1), v (Fin.castLE (Nat.succ_le_succ hk) i)) := by
  induction k with
  | zero =>
      simp [twoSumPrefix_zero]
  | succ k ih =>
      rw [twoSumPrefix_succ]
      rw [Fin.sum_univ_castSucc]
      rw [Fin.sum_univ_castSucc]
      have hc : twoSumCorrection fp v (Fin.castLE hk (Fin.last k)) =
          (fp.twoSum
            (twoSumPrefix fp v k (Nat.le_trans (Nat.le_succ k) hk))
            (v (Fin.castLE (Nat.succ_le_succ hk) (Fin.last (k + 1))))).2 := by
        simp only [twoSumCorrection]
        congr 2
      rw [hc]
      rw [add_comm (∑ i : Fin k,
        twoSumCorrection fp v (Fin.castLE hk i.castSucc))]
      rw [← add_assoc]
      have hv : v ⟨k + 1, by omega⟩ =
          v (Fin.castLE (Nat.succ_le_succ hk) (Fin.last (k + 1))) := by
        congr 1
      rw [hv]
      rw [fp.twoSum_exact]
      rw [add_assoc]
      have hcast : (fun i : Fin k =>
          twoSumCorrection fp v (Fin.castLE hk i.castSucc)) =
          (fun i : Fin k => twoSumCorrection fp v
            (Fin.castLE (Nat.le_trans (Nat.le_succ k) hk) i)) := by
        funext i
        congr 1
      rw [hcast]
      rw [add_comm
        (v (Fin.castLE (Nat.succ_le_succ hk) (Fin.last (k + 1))))]
      rw [← add_assoc]
      rw [ih (Nat.le_trans (Nat.le_succ k) hk)]
      congr 2

private lemma twoSumPrefix_abs_le (fp : ErrorFreeAddModel) {q k : ℕ}
    (v : Fin (q + 1) → ℝ) (hk : k ≤ q) :
    |twoSumPrefix fp v k hk| ≤
      (∑ i : Fin (q + 1), |v i|) +
        ∑ i : Fin q, |twoSumCorrection fp v i| := by
  let A := ∑ i : Fin (k + 1),
    v (Fin.castLE (Nat.succ_le_succ hk) i)
  let B := ∑ i : Fin k,
    twoSumCorrection fp v (Fin.castLE hk i)
  have he : twoSumPrefix fp v k hk = A - B := by
    have h := twoSumPrefix_exact fp v hk
    dsimp only [A, B]
    linarith
  rw [he]
  calc
    |A - B| ≤ |A| + |B| := abs_sub A B
    _ ≤ (∑ i : Fin (k + 1),
          |v (Fin.castLE (Nat.succ_le_succ hk) i)|) +
        ∑ i : Fin k,
          |twoSumCorrection fp v (Fin.castLE hk i)| := by
      apply add_le_add
      · exact Finset.abs_sum_le_sum_abs _ _
      · exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ i : Fin (q + 1), |v i|) +
        ∑ i : Fin q, |twoSumCorrection fp v i| := by
      apply add_le_add
      · simpa using (fin_sum_castLE_le (Nat.succ_le_succ hk)
          (fun i : Fin (q + 1) => |v i|) (fun i => abs_nonneg _))
      · simpa using (fin_sum_castLE_le hk
          (fun i : Fin q => |twoSumCorrection fp v i|)
          (fun i => abs_nonneg _))

private lemma vecSum_correction_bound (fp : ErrorFreeAddModel) {q : ℕ}
    (v : Fin (q + 1) → ℝ) (hvalid : (q : ℝ) * fp.u < 1) :
    (∑ i : Fin q, |twoSumCorrection fp v i|) ≤
      gamma fp.u q * ∑ i : Fin (q + 1), |v i| := by
  let M := ∑ i : Fin (q + 1), |v i|
  let C := ∑ i : Fin q, |twoSumCorrection fp v i|
  have hpoint (i : Fin q) :
      |twoSumCorrection fp v i| ≤ fp.u * (M + C) := by
    calc
      |twoSumCorrection fp v i| ≤
          fp.u * |twoSumPrefix fp v (i.val + 1)
            (Nat.succ_le_iff.mpr i.isLt)| := by
        simp only [twoSumCorrection]
        rw [twoSumPrefix_succ]
        exact fp.twoSum_low_le _ _
      _ ≤ fp.u * (M + C) := by
        apply mul_le_mul_of_nonneg_left _ fp.u_nonneg
        exact twoSumPrefix_abs_le fp v _
  have hsum : C ≤ (q : ℝ) * (fp.u * (M + C)) := by
    dsimp only [C]
    calc
      (∑ i : Fin q, |twoSumCorrection fp v i|) ≤
          ∑ _i : Fin q, fp.u * (M + C) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hpoint i
      _ = (q : ℝ) * (fp.u * (M + C)) := by simp
  have hden : 0 < 1 - (q : ℝ) * fp.u := sub_pos.mpr hvalid
  have hgamma : gamma fp.u q * (1 - (q : ℝ) * fp.u) =
      (q : ℝ) * fp.u := by
    rw [gamma]
    field_simp
  have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  dsimp only [M, C] at *
  nlinarith

private lemma gamma_nonneg_of_valid (u : ℝ) (q : ℕ) (hu : 0 ≤ u)
    (hv : (q : ℝ) * u < 1) : 0 ≤ gamma u q := by
  rw [gamma]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg q) hu)
    (le_of_lt (sub_pos.mpr hv))

private lemma gamma_step (u : ℝ) (q : ℕ) (hu : 0 ≤ u)
    (hv : ((q + 1 : ℕ) : ℝ) * u < 1) :
    u + (1 + u) * gamma u q ≤ gamma u (q + 1) := by
  norm_num only [Nat.cast_add, Nat.cast_one] at hv
  have hvq : (q : ℝ) * u < 1 := by nlinarith
  have hdq : 0 < 1 - (q : ℝ) * u := sub_pos.mpr hvq
  have hds : 0 < 1 - ((q : ℝ) + 1) * u := sub_pos.mpr hv
  rw [gamma, gamma]
  norm_num only [Nat.cast_add, Nat.cast_one]
  have heq : u + (1 + u) * ((q : ℝ) * u / (1 - (q : ℝ) * u)) =
      ((q : ℝ) + 1) * u / (1 - (q : ℝ) * u) := by
    have hn : 1 - u * (q : ℝ) ≠ 0 := by nlinarith
    field_simp [ne_of_gt hdq, hn]
    ring
  rw [heq]
  apply div_le_div_of_nonneg_left
  · positivity
  · exact hds
  · nlinarith

private lemma recursiveSum_error (fp : StandardAddModel) {q : ℕ}
    (v : Fin (q + 1) → ℝ) (hvalid : (q : ℝ) * fp.u < 1) :
    |recursiveSum fp.fl_add (q + 1) v - ∑ i, v i| ≤
      gamma fp.u q * ∑ i, |v i| := by
  induction q with
  | zero =>
      simp [recursiveSum, gamma]
  | succ q ih =>
      have hq : (q : ℝ) * fp.u < 1 := by
        norm_num at hvalid ⊢
        nlinarith [fp.u_nonneg]
      have hi := ih (fun i : Fin (q + 1) => v i.castSucc) hq
      obtain ⟨δ, hδ, hfl⟩ := fp.model_add
        (recursiveSum fp.fl_add (q + 1) (fun i => v i.castSucc))
        (v (Fin.last (q + 1)))
      rw [recursiveSum]
      simp only [show ¬q + 1 = 0 by omega, ↓reduceDIte]
      rw [hfl]
      rw [Fin.sum_univ_castSucc (fun i : Fin (q + 1 + 1) => v i)]
      rw [Fin.sum_univ_castSucc (fun i : Fin (q + 1 + 1) => |v i|)]
      let a := recursiveSum fp.fl_add (q + 1) (fun i => v i.castSucc)
      let s := ∑ i : Fin (q + 1), v i.castSucc
      let b := v (Fin.last (q + 1))
      let M := ∑ i : Fin (q + 1), |v i.castSucc|
      have hδ' : |δ| ≤ fp.u := hδ
      have h1δ : |1 + δ| ≤ 1 + fp.u := by
        calc
          |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
          _ ≤ 1 + fp.u := by norm_num; linarith
      have hs : |s| ≤ M := by
        dsimp only [s, M]
        exact Finset.abs_sum_le_sum_abs _ _
      have hM : 0 ≤ M := by
        dsimp only [M]
        exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have hγ : 0 ≤ gamma fp.u q :=
        gamma_nonneg_of_valid fp.u q fp.u_nonneg hq
      have hstep := gamma_step fp.u q fp.u_nonneg hvalid
      change |(a + b) * (1 + δ) - (s + b)| ≤
        gamma fp.u (q + 1) * (M + |b|)
      have hid : (a + b) * (1 + δ) - (s + b) =
          (1 + δ) * (a - s) + δ * (s + b) := by ring
      rw [hid]
      calc
        |(1 + δ) * (a - s) + δ * (s + b)| ≤
            |(1 + δ) * (a - s)| + |δ * (s + b)| := abs_add_le _ _
        _ = |1 + δ| * |a - s| + |δ| * |s + b| := by
          rw [abs_mul, abs_mul]
        _ ≤ (1 + fp.u) * (gamma fp.u q * M) +
            fp.u * (M + |b|) := by
          apply add_le_add
          · exact mul_le_mul h1δ hi (abs_nonneg _)
              (by linarith [fp.u_nonneg])
          · calc
              |δ| * |s + b| ≤ fp.u * (|s| + |b|) :=
                mul_le_mul hδ' (abs_add_le s b) (abs_nonneg _) fp.u_nonneg
              _ ≤ fp.u * (M + |b|) := by
                apply mul_le_mul_of_nonneg_left _ fp.u_nonneg
                linarith
        _ ≤ gamma fp.u (q + 1) * (M + |b|) := by
          have hγs : 0 ≤ gamma fp.u (q + 1) :=
            gamma_nonneg_of_valid fp.u (q + 1) fp.u_nonneg hvalid
          have huγ : fp.u ≤ gamma fp.u (q + 1) := by
            have hf : 0 ≤ (1 + fp.u) * gamma fp.u q :=
              mul_nonneg (by linarith [fp.u_nonneg]) hγ
            linarith
          calc
            (1 + fp.u) * (gamma fp.u q * M) +
                fp.u * (M + |b|) =
              (fp.u + (1 + fp.u) * gamma fp.u q) * M +
                fp.u * |b| := by ring
            _ ≤ gamma fp.u (q + 1) * M +
                gamma fp.u (q + 1) * |b| := by
              exact add_le_add
                (mul_le_mul_of_nonneg_right hstep hM)
                (mul_le_mul_of_nonneg_right huγ (abs_nonneg b))
            _ = gamma fp.u (q + 1) * (M + |b|) := by ring

private lemma vecSum_magnitude (fp : ErrorFreeAddModel) {q : ℕ}
    (v : Fin (q + 1) → ℝ) (hvalid : (q : ℝ) * fp.u < 1) :
    (∑ i, |vecSum fp v i|) ≤
      |∑ i, v i| + 2 * gamma fp.u q * ∑ i, |v i| := by
  let C := ∑ i : Fin q, |twoSumCorrection fp v i|
  let c := ∑ i : Fin q, twoSumCorrection fp v i
  let h := twoSumPrefix fp v q (Nat.le_refl q)
  have hC := vecSum_correction_bound fp v hvalid
  have he := vecSum_exact_sum fp v
  rw [Fin.sum_univ_castSucc] at he ⊢
  simp only [vecSum, Fin.lastCases_castSucc, Fin.lastCases_last] at he ⊢
  change C + |h| ≤ |∑ i, v i| + 2 * gamma fp.u q * ∑ i, |v i|
  have hh : |h| ≤ |∑ i, v i| + C := by
    have hcabs : |c| ≤ C := by
      dsimp only [c, C]
      exact Finset.abs_sum_le_sum_abs _ _
    change c + h = ∑ i, v i at he
    have : h = (∑ i, v i) - c := by linarith
    rw [this]
    have hab := abs_sub (∑ i, v i) c
    linarith
  dsimp only [C] at hC ⊢
  nlinarith

private lemma recursiveSum_vecSum_error (fp : ErrorFreeAddModel) {q : ℕ}
    (v : Fin (q + 1) → ℝ) (hvalid : (q : ℝ) * fp.u < 1) :
    |recursiveSum fp.fl_add (q + 1) (vecSum fp v) - ∑ i, v i| ≤
      fp.u * |∑ i, v i| +
        (gamma fp.u q) ^ 2 * ∑ i, |v i| := by
  cases q with
  | zero =>
      have hz : (0 : Fin 1) = Fin.last 0 := Subsingleton.elim _ _
      rw [show recursiveSum fp.fl_add 1 (vecSum fp v) =
        vecSum fp v 0 by simp [recursiveSum]]
      simp only [vecSum, gamma, Nat.cast_zero, zero_mul, sub_zero, zero_div,
        zero_pow (by omega : (2 : ℕ) ≠ 0), zero_mul, add_zero]
      have hv : Fin.lastCases (twoSumPrefix fp v 0 (Nat.le_refl 0))
          (twoSumCorrection fp v) 0 = v 0 := by
        rw [hz, Fin.lastCases_last]
        exact twoSumPrefix_zero fp v
      rw [hv]
      simpa using mul_nonneg fp.u_nonneg (abs_nonneg (v 0))
  | succ r =>
      let corr : Fin (r + 1) → ℝ := fun i => twoSumCorrection fp v i
      let A := recursiveSum fp.fl_add (r + 1) corr
      let c := ∑ i : Fin (r + 1), corr i
      let C := ∑ i : Fin (r + 1), |corr i|
      let h := twoSumPrefix fp v (r + 1) (Nat.le_refl (r + 1))
      let s := ∑ i : Fin (r + 1 + 1), v i
      let M := ∑ i : Fin (r + 1 + 1), |v i|
      have hrvalid : (r : ℝ) * fp.u < 1 := by
        norm_num at hvalid ⊢
        nlinarith [fp.u_nonneg]
      have hi := recursiveSum_error fp.toStandardAddModel corr hrvalid
      have hC := vecSum_correction_bound fp v hvalid
      have he := vecSum_exact_sum fp v
      rw [Fin.sum_univ_castSucc] at he
      simp only [vecSum, Fin.lastCases_castSucc, Fin.lastCases_last] at he
      change c + h = s at he
      obtain ⟨δ, hδ, hfl⟩ := fp.model_add A h
      rw [recursiveSum]
      simp only [show ¬r + 1 = 0 by omega, ↓reduceDIte]
      simp only [vecSum, Fin.lastCases_castSucc, Fin.lastCases_last]
      change |fp.fl_add A h - s| ≤
        fp.u * |s| + (gamma fp.u (r + 1)) ^ 2 * M
      rw [hfl]
      change |(A + h) * (1 + δ) - s| ≤
        fp.u * |s| + (gamma fp.u (r + 1)) ^ 2 * M
      change |A - c| ≤ gamma fp.u r * C at hi
      change C ≤ gamma fp.u (r + 1) * M at hC
      have hγr : 0 ≤ gamma fp.u r :=
        gamma_nonneg_of_valid fp.u r fp.u_nonneg hrvalid
      have hγ : 0 ≤ gamma fp.u (r + 1) :=
        gamma_nonneg_of_valid fp.u (r + 1) fp.u_nonneg hvalid
      have hstep := gamma_step fp.u r fp.u_nonneg hvalid
      have hcoef : (1 + fp.u) * gamma fp.u r ≤ gamma fp.u (r + 1) := by
        linarith [fp.u_nonneg]
      have h1δ : |1 + δ| ≤ 1 + fp.u := by
        calc
          |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
          _ ≤ 1 + fp.u := by norm_num; linarith
      have hid : (A + h) * (1 + δ) - s =
          (1 + δ) * (A - c) + δ * s := by
        rw [← he]
        ring
      rw [hid]
      calc
        |(1 + δ) * (A - c) + δ * s| ≤
            |(1 + δ) * (A - c)| + |δ * s| := abs_add_le _ _
        _ = |1 + δ| * |A - c| + |δ| * |s| := by
          rw [abs_mul, abs_mul]
        _ ≤ (1 + fp.u) * (gamma fp.u r * C) + fp.u * |s| := by
          apply add_le_add
          · exact mul_le_mul h1δ hi (abs_nonneg _)
              (by linarith [fp.u_nonneg])
          · exact mul_le_mul_of_nonneg_right hδ (abs_nonneg s)
        _ ≤ fp.u * |s| + (gamma fp.u (r + 1)) ^ 2 * M := by
          have hCM : gamma fp.u (r + 1) * C ≤
              (gamma fp.u (r + 1)) ^ 2 * M := by
            calc
              gamma fp.u (r + 1) * C ≤
                  gamma fp.u (r + 1) *
                    (gamma fp.u (r + 1) * M) :=
                mul_le_mul_of_nonneg_left hC hγ
              _ = (gamma fp.u (r + 1)) ^ 2 * M := by ring
          have hfirst : (1 + fp.u) * (gamma fp.u r * C) ≤
              gamma fp.u (r + 1) * C := by
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right hcoef
              (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
          linarith

private lemma iteratedVecSum_exact (fp : ErrorFreeAddModel) {q t : ℕ}
    (v : Fin (q + 1) → ℝ) :
    ∑ i, iteratedVecSum fp t v i = ∑ i, v i := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [iteratedVecSum]
      rw [vecSum_exact_sum]
      exact ih

private lemma iteratedVecSum_magnitude (fp : ErrorFreeAddModel) {q t : ℕ}
    (v : Fin (q + 1) → ℝ) (hvalid : (q : ℝ) * fp.u < 1)
    (hgamma : gamma fp.u q ≤ (1 : ℝ) / 3) :
    (∑ i, |iteratedVecSum fp t v i|) ≤
      3 * |∑ i, v i| +
        (2 * gamma fp.u q) ^ t * ∑ i, |v i| := by
  have hγ0 := gamma_nonneg_of_valid fp.u q fp.u_nonneg hvalid
  induction t with
  | zero =>
      simp only [iteratedVecSum, pow_zero, one_mul]
      nlinarith [abs_nonneg (∑ i, v i)]
  | succ t ih =>
      rw [iteratedVecSum]
      have hm := vecSum_magnitude fp (iteratedVecSum fp t v) hvalid
      rw [iteratedVecSum_exact fp v] at hm
      calc
        (∑ i, |vecSum fp (iteratedVecSum fp t v) i|) ≤
            |∑ i, v i| + 2 * gamma fp.u q *
              ∑ i, |iteratedVecSum fp t v i| := hm
        _ ≤ 3 * |∑ i, v i| +
            (2 * gamma fp.u q) ^ (t + 1) * ∑ i, |v i| := by
          rw [pow_succ]
          have ha : 0 ≤ 2 * gamma fp.u q := mul_nonneg (by norm_num) hγ0
          have hmul := mul_le_mul_of_nonneg_left ih ha
          nlinarith [abs_nonneg (∑ i, v i)]

private lemma gamma_le_one_third (u : ℝ) (q : ℕ) (hu : 0 ≤ u)
    (hsmall : 4 * (q : ℝ) * u ≤ 1) : gamma u q ≤ (1 : ℝ) / 3 := by
  have ha : 0 ≤ (q : ℝ) * u := mul_nonneg (Nat.cast_nonneg q) hu
  have hd : 0 < 1 - (q : ℝ) * u := by nlinarith
  rw [gamma]
  apply (div_le_iff₀ hd).2
  nlinarith

private lemma two_gamma_le_gamma_double (u : ℝ) (q : ℕ) (hu : 0 ≤ u)
    (hvalid : (2 * (q : ℝ)) * u < 1) :
    2 * gamma u q ≤ gamma u (2 * q) := by
  have ha : 0 ≤ (q : ℝ) * u := mul_nonneg (Nat.cast_nonneg q) hu
  have hd : 0 < 1 - (q : ℝ) * u := by nlinarith
  have hd2 : 0 < 1 - 2 * ((q : ℝ) * u) := by nlinarith
  rw [gamma, gamma]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    2 * ((q : ℝ) * u / (1 - (q : ℝ) * u)) =
        (2 * ((q : ℝ) * u)) / (1 - (q : ℝ) * u) := by ring
    _ ≤ (2 * ((q : ℝ) * u)) / (1 - 2 * ((q : ℝ) * u)) := by
      apply div_le_div_of_nonneg_left (by positivity) hd2
      nlinarith
    _ = (2 * (q : ℝ)) * u / (1 - (2 * (q : ℝ)) * u) := by ring

private lemma gamma_mono_nat (u : ℝ) {a b : ℕ} (hu : 0 ≤ u)
    (hab : a ≤ b) (hvalid : (b : ℝ) * u < 1) :
    gamma u a ≤ gamma u b := by
  have hcast : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hnum : (a : ℝ) * u ≤ (b : ℝ) * u :=
    mul_le_mul_of_nonneg_right hcast hu
  have hb0 : 0 ≤ (b : ℝ) * u := mul_nonneg (Nat.cast_nonneg b) hu
  have hdb : 0 < 1 - (b : ℝ) * u := sub_pos.mpr hvalid
  rw [gamma, gamma]
  apply div_le_div₀ hb0 hnum hdb
  linarith

private lemma gamma_le_one (u : ℝ) (q : ℕ) (hu : 0 ≤ u)
    (hsmall : 2 * (q : ℝ) * u ≤ 1) : gamma u q ≤ 1 := by
  have hq0 : 0 ≤ (q : ℝ) * u := mul_nonneg (Nat.cast_nonneg q) hu
  have hd : 0 < 1 - (q : ℝ) * u := by nlinarith
  rw [gamma]
  apply (div_le_iff₀ hd).2
  nlinarith

private lemma sumK_error (fp : ErrorFreeAddModel) {q J : ℕ}
    (v : Fin (q + 1) → ℝ) (hJ : 2 ≤ J)
    (hsmall : 4 * (q : ℝ) * fp.u ≤ 1) :
    |sumK fp J v - ∑ i, v i| ≤
      (fp.u + 3 * (gamma fp.u q) ^ 2) * |∑ i, v i| +
        (gamma fp.u (2 * q)) ^ J * ∑ i, |v i| := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hJ
  rw [Nat.add_comm 2 t]
  have hvalid : (q : ℝ) * fp.u < 1 := by
    have hq0 : 0 ≤ (q : ℝ) * fp.u :=
      mul_nonneg (Nat.cast_nonneg q) fp.u_nonneg
    nlinarith
  have hvalid2 : (2 * (q : ℝ)) * fp.u < 1 := by
    have hq0 : 0 ≤ (q : ℝ) * fp.u :=
      mul_nonneg (Nat.cast_nonneg q) fp.u_nonneg
    nlinarith
  have hγ := gamma_nonneg_of_valid fp.u q fp.u_nonneg hvalid
  have hγthird := gamma_le_one_third fp.u q fp.u_nonneg hsmall
  have hdouble := two_gamma_le_gamma_double fp.u q fp.u_nonneg hvalid2
  have hg0 : 0 ≤ gamma fp.u (2 * q) := by
    apply gamma_nonneg_of_valid fp.u (2 * q) fp.u_nonneg
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    exact hvalid2
  let z := iteratedVecSum fp t v
  have herr := recursiveSum_vecSum_error fp z hvalid
  have hmag := iteratedVecSum_magnitude fp (t := t) v hvalid hγthird
  have hex := iteratedVecSum_exact fp (t := t) v
  change |recursiveSum fp.fl_add (q + 1)
      (iteratedVecSum fp ((t + 2) - 1) v) - ∑ i, v i| ≤ _
  norm_num only [Nat.add_sub_cancel]
  rw [iteratedVecSum.eq_def]
  change |recursiveSum fp.fl_add (q + 1) (vecSum fp z) - ∑ i, v i| ≤ _
  change (∑ i, z i) = ∑ i, v i at hex
  rw [hex] at herr
  calc
    |recursiveSum fp.fl_add (q + 1) (vecSum fp z) - ∑ i, v i| ≤
        fp.u * |∑ i, v i| + (gamma fp.u q) ^ 2 * ∑ i, |z i| := herr
    _ ≤ (fp.u + 3 * (gamma fp.u q) ^ 2) * |∑ i, v i| +
        (gamma fp.u (2 * q)) ^ (t + 2) * ∑ i, |v i| := by
      have hr2 : 0 ≤ (gamma fp.u q) ^ 2 := sq_nonneg _
      have hmul := mul_le_mul_of_nonneg_left hmag hr2
      have hpow : (2 * gamma fp.u q) ^ t ≤
          (gamma fp.u (2 * q)) ^ t :=
        pow_le_pow_left₀ (mul_nonneg (by norm_num) hγ) hdouble t
      have hrle : gamma fp.u q ≤ gamma fp.u (2 * q) := by nlinarith
      have hrpow : (gamma fp.u q) ^ 2 ≤
          (gamma fp.u (2 * q)) ^ 2 :=
        pow_le_pow_left₀ hγ hrle 2
      have htail : (gamma fp.u q) ^ 2 *
            ((2 * gamma fp.u q) ^ t * ∑ i, |v i|) ≤
          (gamma fp.u (2 * q)) ^ (t + 2) * ∑ i, |v i| := by
        have hprod := mul_le_mul hrpow hpow (pow_nonneg (mul_nonneg (by norm_num) hγ) t)
          (pow_nonneg hg0 2)
        have hM : 0 ≤ ∑ i, |v i| :=
          Finset.sum_nonneg (fun _ _ => abs_nonneg _)
        rw [pow_add]
        nlinarith
      nlinarith [abs_nonneg (∑ i, v i)]

private lemma dotKTransform_exact (fp : ErrorFreeDotModel) {n : ℕ}
    (x y : Fin (n + 1) → ℝ) :
    ∑ j, dotKTransform fp x y j = exactDot x y := by
  let lo : Fin (n + 1) → ℝ := fun i => (fp.twoProduct (x i) (y i)).2
  let hi : Fin (n + 1) → ℝ := fun i => (fp.twoProduct (x i) (y i)).1
  let w : Fin ((n + 1) + (n + 1)) → ℝ :=
    Fin.addCases lo (vecSum fp.toErrorFreeAddModel hi)
  let e : Fin ((2 * n + 1) + 1) ≃ Fin ((n + 1) + (n + 1)) :=
    (Fin.castOrderIso (by omega)).toEquiv
  have he (j : Fin ((2 * n + 1) + 1)) :
      dotKTransform fp x y j = w (e j) := by
    simp only [dotKTransform, w, e]
    congr 2
  calc
    (∑ j, dotKTransform fp x y j) = ∑ j, w j :=
      Fintype.sum_equiv e _ _ he
    _ = (∑ i, lo i) + ∑ i, vecSum fp.toErrorFreeAddModel hi i := by
      rw [Fin.sum_univ_add]
      simp only [w, Fin.addCases_left, Fin.addCases_right]
    _ = (∑ i, lo i) + ∑ i, hi i := by
      rw [vecSum_exact_sum]
    _ = ∑ i, (lo i + hi i) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ i, x i * y i := by
      apply Finset.sum_congr rfl
      intro i hi_mem
      dsimp only [lo, hi]
      rw [add_comm]
      exact fp.twoProduct_exact _ _
    _ = exactDot x y := rfl

private lemma dotKTransform_magnitude (fp : ErrorFreeDotModel) {n : ℕ}
    (x y : Fin (n + 1) → ℝ)
    (hsmall : 8 * ((n + 1 : ℕ) : ℝ) * fp.u ≤ 1) :
    (∑ j, |dotKTransform fp x y j|) ≤
      |exactDot x y| + gamma fp.u (2 * (n + 1)) * dotMagnitude x y := by
  let lo : Fin (n + 1) → ℝ := fun i => (fp.twoProduct (x i) (y i)).2
  let hi : Fin (n + 1) → ℝ := fun i => (fp.twoProduct (x i) (y i)).1
  let w : Fin ((n + 1) + (n + 1)) → ℝ :=
    Fin.addCases lo (vecSum fp.toErrorFreeAddModel hi)
  let e : Fin ((2 * n + 1) + 1) ≃ Fin ((n + 1) + (n + 1)) :=
    (Fin.castOrderIso (by omega)).toEquiv
  let L := ∑ i : Fin (n + 1), |lo i|
  let H := ∑ i : Fin (n + 1), |hi i|
  let M := dotMagnitude x y
  have hnvalid : (n : ℝ) * fp.u < 1 := by
    have hn : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
    have hu := fp.u_nonneg
    nlinarith [mul_le_mul_of_nonneg_right hn hu]
  have hNvalid : (((n + 1 : ℕ) : ℝ)) * fp.u < 1 := by
    have hu := fp.u_nonneg
    have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    nlinarith [mul_nonneg (le_of_lt hNpos) hu]
  have h2Nvalid : (2 * (((n + 1 : ℕ) : ℝ))) * fp.u < 1 := by
    have hu := fp.u_nonneg
    have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    nlinarith [mul_nonneg (le_of_lt hNpos) hu]
  have hL : L ≤ fp.u * M := by
    dsimp only [L, M, lo, dotMagnitude]
    calc
      (∑ i : Fin (n + 1), |(fp.twoProduct (x i) (y i)).2|) ≤
          ∑ i : Fin (n + 1), fp.u * |x i * y i| := by
        apply Finset.sum_le_sum
        intro i hi_mem
        exact fp.twoProduct_low_le_exact _ _
      _ = fp.u * ∑ i : Fin (n + 1), |x i| * |y i| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi_mem
        rw [abs_mul]
  have hH : H ≤ M + L := by
    dsimp only [H, M, L, hi, lo, dotMagnitude]
    calc
      (∑ i : Fin (n + 1), |(fp.twoProduct (x i) (y i)).1|) ≤
          ∑ i : Fin (n + 1),
            (|x i * y i| + |(fp.twoProduct (x i) (y i)).2|) := by
        apply Finset.sum_le_sum
        intro i hi_mem
        have he := fp.twoProduct_exact (x i) (y i)
        have hh : (fp.twoProduct (x i) (y i)).1 =
            x i * y i - (fp.twoProduct (x i) (y i)).2 := by linarith
        rw [hh]
        exact abs_sub _ _
      _ = (∑ i : Fin (n + 1), |x i| * |y i|) +
          ∑ i : Fin (n + 1), |(fp.twoProduct (x i) (y i)).2| := by
        rw [Finset.sum_add_distrib]
        simp only [abs_mul]
  have hsumhi : |∑ i, hi i| ≤ |exactDot x y| + L := by
    have he : (∑ i, hi i) + ∑ i, lo i = exactDot x y := by
      calc
        (∑ i, hi i) + ∑ i, lo i = ∑ i, (hi i + lo i) := by
          rw [Finset.sum_add_distrib]
        _ = ∑ i, x i * y i := by
          apply Finset.sum_congr rfl
          intro i hi_mem
          exact fp.twoProduct_exact _ _
        _ = exactDot x y := rfl
    have hloabs : |∑ i, lo i| ≤ L := by
      dsimp only [L]
      exact Finset.abs_sum_le_sum_abs _ _
    have hh : (∑ i, hi i) = exactDot x y - ∑ i, lo i := by linarith
    rw [hh]
    exact le_trans (abs_sub _ _) (by linarith)
  have hvec := vecSum_magnitude fp.toErrorFreeAddModel hi hnvalid
  have hstep := gamma_step fp.u n fp.u_nonneg hNvalid
  have hdouble := two_gamma_le_gamma_double fp.u (n + 1) fp.u_nonneg h2Nvalid
  have hγn := gamma_nonneg_of_valid fp.u n fp.u_nonneg hnvalid
  have he (j : Fin ((2 * n + 1) + 1)) :
      |dotKTransform fp x y j| = |w (e j)| := by
    congr 1
  calc
    (∑ j, |dotKTransform fp x y j|) = ∑ j, |w j| :=
      Fintype.sum_equiv e _ _ he
    _ = L + ∑ i, |vecSum fp.toErrorFreeAddModel hi i| := by
      rw [Fin.sum_univ_add]
      simp only [w, Fin.addCases_left, Fin.addCases_right, L]
    _ ≤ L + (|∑ i, hi i| + 2 * gamma fp.u n * H) := by
      change (∑ i, |vecSum fp.toErrorFreeAddModel hi i|) ≤
        |∑ i, hi i| + 2 * gamma fp.u n * H at hvec
      linarith
    _ ≤ |exactDot x y| + gamma fp.u (2 * (n + 1)) * M := by
      have hcoef : 2 * (fp.u + (1 + fp.u) * gamma fp.u n) ≤
          gamma fp.u (2 * (n + 1)) := by
        nlinarith
      have hM : 0 ≤ M := by
        dsimp only [M, dotMagnitude]
        exact Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have hbound : L + (|∑ i, hi i| + 2 * gamma fp.u n * H) ≤
          |exactDot x y| +
            2 * (fp.u + (1 + fp.u) * gamma fp.u n) * M := by
        have ha : 0 ≤ 2 * gamma fp.u n := mul_nonneg (by norm_num) hγn
        have hγmul := mul_le_mul_of_nonneg_left hH ha
        nlinarith
      have hcoefM := mul_le_mul_of_nonneg_right hcoef hM
      linarith

theorem p02_t3_dotK_error_bound
    (fp : ErrorFreeDotModel) (n K : ℕ) (x y : Fin (n + 1) → ℝ)
    (hK : 3 ≤ K)
    (hsmall : (8 : ℝ) * ((n + 1 : ℕ) : ℝ) * fp.u ≤ 1) :
    |dotK fp K x y - exactDot x y| ≤
      (fp.u + 2 * (gamma fp.u (4 * (n + 1) - 2)) ^ 2) * |exactDot x y| +
        (gamma fp.u (4 * (n + 1) - 2)) ^ K * dotMagnitude x y := by
  -- PROOF_START P02-T3-H001
  rw [show 4 * (n + 1) - 2 = 2 * (2 * n + 1) by omega]
  have hJ : 2 ≤ K - 1 := by omega
  have hqsmall : 4 * ((2 * n + 1 : ℕ) : ℝ) * fp.u ≤ 1 := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one,
      Nat.cast_ofNat] at hsmall ⊢
    nlinarith [fp.u_nonneg]
  have hmvalid : ((2 * (2 * n + 1) : ℕ) : ℝ) * fp.u < 1 := by
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat]
    have hu := fp.u_nonneg
    norm_num only [Nat.cast_add, Nat.cast_one] at hsmall
    nlinarith
  have hs := sumK_error fp.toErrorFreeAddModel
    (v := dotKTransform fp x y) hJ hqsmall
  rw [dotKTransform_exact fp x y] at hs
  change |dotK fp K x y - exactDot x y| ≤ _ at hs
  have hmag := dotKTransform_magnitude fp x y hsmall
  let r := gamma fp.u (2 * n + 1)
  let g := gamma fp.u (2 * (2 * n + 1))
  let h := gamma fp.u (2 * (n + 1))
  have hr0 : 0 ≤ r := by
    apply gamma_nonneg_of_valid fp.u (2 * n + 1) fp.u_nonneg
    have hq0 : 0 ≤ (((2 * n + 1 : ℕ) : ℝ) * fp.u) :=
      mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg
    nlinarith
  have hg0 : 0 ≤ g := by
    exact gamma_nonneg_of_valid fp.u _ fp.u_nonneg hmvalid
  have hg1 : g ≤ 1 := by
    apply gamma_le_one fp.u (2 * (2 * n + 1)) fp.u_nonneg
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat] at hqsmall ⊢
    nlinarith
  have hdouble : 2 * r ≤ g := by
    apply two_gamma_le_gamma_double fp.u (2 * n + 1) fp.u_nonneg
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat] at hmvalid ⊢
    exact hmvalid
  have hhg : h ≤ g := by
    apply gamma_mono_nat fp.u fp.u_nonneg (by omega) hmvalid
  change (∑ j, |dotKTransform fp x y j|) ≤
    |exactDot x y| + h * dotMagnitude x y at hmag
  change |dotK fp K x y - exactDot x y| ≤
    (fp.u + 3 * r ^ 2) * |exactDot x y| +
      g ^ (K - 1) * ∑ i, |dotKTransform fp x y i| at hs
  have hgp0 : 0 ≤ g ^ (K - 1) := pow_nonneg hg0 _
  have hcombined : |dotK fp K x y - exactDot x y| ≤
      (fp.u + 3 * r ^ 2) * |exactDot x y| +
        g ^ (K - 1) *
          (|exactDot x y| + h * dotMagnitude x y) := by
    exact le_trans hs (add_le_add (le_refl _)
      (mul_le_mul_of_nonneg_left hmag hgp0))
  have hpow : g ^ (K - 1) ≤ g ^ 2 :=
    pow_le_pow_of_le_one hg0 hg1 hJ
  have hsquare : (2 * r) ^ 2 ≤ g ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by norm_num) hr0) hdouble 2
  have hcoeff : 3 * r ^ 2 + g ^ (K - 1) ≤ 2 * g ^ 2 := by
    nlinarith
  have htailcoef : g ^ (K - 1) * h ≤ g ^ K := by
    calc
      g ^ (K - 1) * h ≤ g ^ (K - 1) * g :=
        mul_le_mul_of_nonneg_left hhg hgp0
      _ = g ^ K := by
        rw [← pow_succ]
        congr 1
        omega
  have hS : 0 ≤ |exactDot x y| := abs_nonneg _
  have hM : 0 ≤ dotMagnitude x y := by
    unfold dotMagnitude
    exact Finset.sum_nonneg
      (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hcoeffS := mul_le_mul_of_nonneg_right hcoeff hS
  have htailM := mul_le_mul_of_nonneg_right htailcoef hM
  change |dotK fp K x y - exactDot x y| ≤
    (fp.u + 2 * g ^ 2) * |exactDot x y| +
      g ^ K * dotMagnitude x y
  nlinarith

end HighamBench
