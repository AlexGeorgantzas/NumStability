import HighamBench.P02Definitions

namespace HighamBench

open scoped BigOperators

private theorem fin_foldl_succ_last {α : Type*} {m : ℕ}
    (f : α → Fin (m + 1) → α) (a : α) :
    Fin.foldl (m + 1) f a =
      f (Fin.foldl m (fun a i => f a i.castSucc) a) (Fin.last m) := by
  induction m generalizing a with
  | zero => rw [Fin.foldl_succ]; simp
  | succ m ih =>
      rw [Fin.foldl_succ, ih]
      rw [Fin.foldl_succ]
      congr 2 <;> simp

private theorem twoSumPrefix_succ (fp : ErrorFreeAddModel) {m : ℕ}
    (v : Fin (m + 1) → ℝ) (k : ℕ) (hk : k < m) :
    twoSumPrefix fp v (k + 1) (Nat.succ_le_of_lt hk) =
      (fp.twoSum (twoSumPrefix fp v k (Nat.le_of_lt hk))
        (v ⟨k + 1, Nat.succ_lt_succ hk⟩)).1 := by
  unfold twoSumPrefix
  rw [fin_foldl_succ_last]
  congr 1

private theorem twoSumPrefix_zero (fp : ErrorFreeAddModel) {m : ℕ}
    (v : Fin (m + 1) → ℝ) :
    twoSumPrefix fp v 0 (Nat.zero_le m) = v ⟨0, Nat.succ_pos m⟩ := by
  simp [twoSumPrefix]

private theorem twoSumPrefix_castSucc (fp : ErrorFreeAddModel) {m : ℕ}
    (v : Fin (m + 2) → ℝ) (k : ℕ) (hk : k ≤ m) :
    twoSumPrefix fp (fun i : Fin (m + 1) => v i.castSucc) k hk =
      twoSumPrefix fp v k (Nat.le_trans hk (Nat.le_succ m)) := by
  unfold twoSumPrefix
  congr 1

private theorem twoSumCorrection_castSucc (fp : ErrorFreeAddModel) {m : ℕ}
    (v : Fin (m + 2) → ℝ) (i : Fin m) :
    twoSumCorrection fp (fun j : Fin (m + 1) => v j.castSucc) i =
      twoSumCorrection fp v i.castSucc := by
  unfold twoSumCorrection
  rw [twoSumPrefix_castSucc]
  congr

private theorem vecSum_sum (fp : ErrorFreeAddModel) {m : ℕ}
    (v : Fin (m + 1) → ℝ) :
    ∑ i, vecSum fp v i = ∑ i, v i := by
  simp only [vecSum, Fin.sum_univ_castSucc, Fin.lastCases_castSucc,
    Fin.lastCases_last]
  induction m with
  | zero => simp [twoSumPrefix_zero]
  | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      have hc :
          (∑ i : Fin m, twoSumCorrection fp v i.castSucc) =
            ∑ i : Fin m,
              twoSumCorrection fp (fun j : Fin (m + 1) => v j.castSucc) i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [twoSumCorrection_castSucc]
      rw [hc]
      have hi := ih (v := fun i : Fin (m + 1) => v i.castSucc)
      rw [twoSumPrefix_castSucc] at hi
      rw [Fin.sum_univ_castSucc
        (fun i : Fin (m + 1) => v i.castSucc)]
      have hp := twoSumPrefix_succ fp v m (by omega)
      have hlast : (⟨m + 1, by omega⟩ : Fin (m + 2)) =
          Fin.last (m + 1) := by ext; simp
      rw [hlast] at hp
      have hcLast : twoSumCorrection fp v (Fin.last m) =
          (fp.twoSum (twoSumPrefix fp v m (by omega))
            (v (Fin.last (m + 1)))).2 := by
        unfold twoSumCorrection
        congr
      have he := fp.twoSum_exact
        (twoSumPrefix fp v m (by omega)) (v (Fin.last (m + 1)))
      rw [hp, hcLast]
      linarith

private theorem iteratedVecSum_sum (fp : ErrorFreeAddModel) {m : ℕ}
    (k : ℕ) (v : Fin (m + 1) → ℝ) :
    ∑ i, iteratedVecSum fp k v i = ∑ i, v i := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [iteratedVecSum]
      rw [vecSum_sum, ih]

private theorem gamma_nonneg_of_valid (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hv : (m : ℝ) * u < 1) : 0 ≤ gamma u m := by
  unfold gamma
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg m) hu) (by linarith)

private theorem gamma_step (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hv : ((m + 1 : ℕ) : ℝ) * u < 1) :
    (1 + u) * gamma u m + u ≤ gamma u (m + 1) := by
  have hm : (m : ℝ) * u < 1 := by
    norm_num only [Nat.cast_add, Nat.cast_one] at hv ⊢
    nlinarith
  have hn : 0 ≤ ((m + 1 : ℕ) : ℝ) * u :=
    mul_nonneg (Nat.cast_nonneg _) hu
  have hd : 1 - ((m + 1 : ℕ) : ℝ) * u ≤ 1 - (m : ℝ) * u := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
  have heq : (1 + u) * gamma u m + u =
      (((m + 1 : ℕ) : ℝ) * u) / (1 - (m : ℝ) * u) := by
    unfold gamma
    norm_num only [Nat.cast_add, Nat.cast_one]
    have hd0 : 1 - (m : ℝ) * u ≠ 0 := by linarith
    have hd0' : 1 - u * (m : ℝ) ≠ 0 := by nlinarith
    field_simp [hd0, hd0']
    ring
  rw [heq]
  unfold gamma
  exact div_le_div_of_nonneg_left hn (by linarith) hd

private theorem gamma_mono (u : ℝ) {a b : ℕ} (hu : 0 ≤ u)
    (hab : a ≤ b) (hv : (b : ℝ) * u < 1) :
    gamma u a ≤ gamma u b := by
  have ha : (a : ℝ) * u ≤ (b : ℝ) * u := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hu
  have hda : 0 < 1 - (a : ℝ) * u := by linarith
  have hdb : 0 < 1 - (b : ℝ) * u := by linarith
  unfold gamma
  rw [div_le_div_iff₀ hda hdb]
  nlinarith

private theorem recursiveSum_error (fp : StandardAddModel) {m : ℕ}
    (v : Fin (m + 1) → ℝ) (hv : (m : ℝ) * fp.u < 1) :
    |recursiveSum fp.fl_add (m + 1) v - ∑ i, v i| ≤
      gamma fp.u m * ∑ i, |v i| := by
  induction m with
  | zero => simp [recursiveSum, gamma]
  | succ m ih =>
      have hm : (m : ℝ) * fp.u < 1 := by
        norm_num only [Nat.cast_add, Nat.cast_one] at hv ⊢
        nlinarith [fp.u_nonneg]
      have hi := ih (v := fun i : Fin (m + 1) => v i.castSucc) hm
      obtain ⟨δ, hδ, hfl⟩ := fp.model_add
        (recursiveSum fp.fl_add (m + 1)
          (fun i : Fin (m + 1) => v i.castSucc))
        (v (Fin.last (m + 1)))
      rw [Fin.sum_univ_castSucc v]
      rw [Fin.sum_univ_castSucc (fun i => |v i|)]
      rw [recursiveSum]
      rw [dif_neg (by omega)]
      rw [hfl]
      let A := recursiveSum fp.fl_add (m + 1)
        (fun i : Fin (m + 1) => v i.castSucc)
      let T := ∑ i : Fin (m + 1), v i.castSucc
      let C := ∑ i : Fin (m + 1), |v i.castSucc|
      let z := v (Fin.last (m + 1))
      have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have hz : 0 ≤ |z| := abs_nonneg _
      have hT : |T| ≤ C := by
        exact Finset.abs_sum_le_sum_abs _ _
      have hA : |A| ≤ gamma fp.u m * C + C := by
        calc
          |A| = |(A - T) + T| := by ring_nf
          _ ≤ |A - T| + |T| := abs_add_le _ _
          _ ≤ gamma fp.u m * C + C := add_le_add hi hT
      have hraw : |(A + z) * (1 + δ) - (T + z)| ≤
          gamma fp.u m * C + fp.u *
            (gamma fp.u m * C + C + |z|) := by
        calc
          |(A + z) * (1 + δ) - (T + z)| =
              |(A - T) + δ * (A + z)| := by ring_nf
          _ ≤ |A - T| + |δ * (A + z)| := abs_add_le _ _
          _ = |A - T| + |δ| * |A + z| := by rw [abs_mul]
          _ ≤ gamma fp.u m * C + fp.u * (|A| + |z|) := by
            apply add_le_add hi
            calc
              |δ| * |A + z| ≤ fp.u * |A + z| :=
                mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
              _ ≤ fp.u * (|A| + |z|) :=
                mul_le_mul_of_nonneg_left (abs_add_le _ _) fp.u_nonneg
          _ ≤ gamma fp.u m * C + fp.u *
                (gamma fp.u m * C + C + |z|) := by
            have hh := mul_le_mul_of_nonneg_left hA fp.u_nonneg
            nlinarith
      have hg0 : 0 ≤ gamma fp.u m :=
        gamma_nonneg_of_valid _ _ fp.u_nonneg hm
      have hstep := gamma_step fp.u m fp.u_nonneg hv
      calc
        |(A + z) * (1 + δ) - (T + z)|
            ≤ gamma fp.u m * C + fp.u *
                (gamma fp.u m * C + C + |z|) := hraw
        _ ≤ ((1 + fp.u) * gamma fp.u m + fp.u) * (C + |z|) := by
          nlinarith [mul_nonneg fp.u_nonneg hz]
        _ ≤ gamma fp.u (m + 1) * (C + |z|) := by
          exact mul_le_mul_of_nonneg_right hstep (add_nonneg hC hz)

private theorem twoSumPrefix_exact (fp : ErrorFreeAddModel) {m : ℕ}
    (v : Fin (m + 1) → ℝ) (k : ℕ) (hk : k ≤ m) :
    twoSumPrefix fp v k hk +
        ∑ i : Fin k,
          twoSumCorrection fp v (Fin.castLE hk i) =
      ∑ i : Fin (k + 1),
        v (Fin.castLE (Nat.succ_le_succ hk) i) := by
  induction k with
  | zero => simp [twoSumPrefix_zero]
  | succ k ih =>
      have hkm : k < m := Nat.lt_of_succ_le hk
      have hi := ih (Nat.le_of_lt hkm)
      rw [Fin.sum_univ_castSucc]
      rw [Fin.sum_univ_castSucc]
      have hp := twoSumPrefix_succ fp v k hkm
      have hc : twoSumCorrection fp v
          ⟨k, hkm⟩ =
          (fp.twoSum (twoSumPrefix fp v k (Nat.le_of_lt hkm))
            (v ⟨k + 1, Nat.succ_lt_succ hkm⟩)).2 := by
        unfold twoSumCorrection
        congr
      have he := fp.twoSum_exact
        (twoSumPrefix fp v k (Nat.le_of_lt hkm))
        (v ⟨k + 1, Nat.succ_lt_succ hkm⟩)
      rw [hp]
      have hcorr :
          (∑ i : Fin k,
              twoSumCorrection fp v (Fin.castLE hk i.castSucc)) =
            ∑ i : Fin k,
              twoSumCorrection fp v
                (Fin.castLE (Nat.le_of_lt hkm) i) := by
        apply Finset.sum_congr rfl
        intro i hi_mem
        rw [Fin.castLE_castSucc]
      have hval :
          (∑ i : Fin (k + 1),
              v (Fin.castLE (Nat.succ_le_succ hk) i.castSucc)) =
            ∑ i : Fin (k + 1),
              v (Fin.castLE
                (Nat.succ_le_succ (Nat.le_of_lt hkm)) i) := by
        apply Finset.sum_congr rfl
        intro i hi_mem
        rw [Fin.castLE_castSucc]
      rw [hcorr, hval]
      have hclast : Fin.castLE hk (Fin.last k) =
          (⟨k, hkm⟩ : Fin m) := by ext; simp
      have hvlast : Fin.castLE (Nat.succ_le_succ hk) (Fin.last (k + 1)) =
          (⟨k + 1, Nat.succ_lt_succ hkm⟩ : Fin (m + 1)) := by ext; simp
      rw [hclast, hvlast, hc]
      linarith

private theorem fin_sum_castLE_abs_le {k m : ℕ} (hk : k ≤ m)
    (f : Fin m → ℝ) :
    (∑ i : Fin k, |f (Fin.castLE hk i)|) ≤ ∑ i : Fin m, |f i| := by
  induction m generalizing k with
  | zero =>
      have hk0 : k = 0 := by omega
      subst k
      simp
  | succ m ih =>
      by_cases heq : k = m + 1
      · subst k
        apply le_of_eq
        apply Finset.sum_congr rfl
        intro i hi
        congr
      · have hkm : k ≤ m := by omega
        rw [Fin.sum_univ_castSucc]
        have hrec := ih hkm (fun i : Fin m => f i.castSucc)
        have hs : (∑ i : Fin k, |f (Fin.castLE hk i)|) =
            ∑ i : Fin k, |f (Fin.castLE hkm i).castSucc| := by
          apply Finset.sum_congr rfl
          intro i hi
          congr
        rw [hs]
        exact hrec.trans (le_add_of_nonneg_right (abs_nonneg _))

private theorem correctionNorm_le_gamma (fp : ErrorFreeAddModel) {m : ℕ}
    (v : Fin (m + 1) → ℝ) (hv : (m : ℝ) * fp.u < 1) :
    (∑ i : Fin m, |twoSumCorrection fp v i|) ≤
      gamma fp.u m * ∑ i, |v i| := by
  let C := ∑ i : Fin m, |twoSumCorrection fp v i|
  let V := ∑ i : Fin (m + 1), |v i|
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hV : 0 ≤ V := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hpoint (i : Fin m) :
      |twoSumCorrection fp v i| ≤ fp.u * (V + C) := by
    have hik : i.val + 1 ≤ m := Nat.succ_le_of_lt i.isLt
    have hp := twoSumPrefix_exact fp v (i.val + 1) hik
    let H := twoSumPrefix fp v (i.val + 1) hik
    let CV := ∑ j : Fin (i.val + 1),
      twoSumCorrection fp v (Fin.castLE hik j)
    let SV := ∑ j : Fin (i.val + 2),
      v (Fin.castLE (Nat.succ_le_succ hik) j)
    have hp' : H + CV = SV := hp
    have hSVabs : |SV| ≤ V := by
      calc
        |SV| ≤ ∑ j : Fin (i.val + 2),
            |v (Fin.castLE (Nat.succ_le_succ hik) j)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ V := fin_sum_castLE_abs_le (Nat.succ_le_succ hik) v
    have hCVabs : |CV| ≤ C := by
      calc
        |CV| ≤ ∑ j : Fin (i.val + 1),
            |twoSumCorrection fp v (Fin.castLE hik j)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ C := fin_sum_castLE_abs_le hik (twoSumCorrection fp v)
    have hH : |H| ≤ V + C := by
      rw [show H = SV - CV by linarith]
      exact (abs_sub _ _).trans (add_le_add hSVabs hCVabs)
    have hlo : |twoSumCorrection fp v i| ≤ fp.u * |H| := by
      dsimp only [H]
      unfold twoSumCorrection
      rw [twoSumPrefix_succ fp v i.val i.isLt]
      exact fp.twoSum_low_le _ _
    exact hlo.trans (mul_le_mul_of_nonneg_left hH fp.u_nonneg)
  have hsum : C ≤ (m : ℝ) * (fp.u * (V + C)) := by
    calc
      C ≤ ∑ _i : Fin m, fp.u * (V + C) :=
        Finset.sum_le_sum (fun i _ => hpoint i)
      _ = (m : ℝ) * (fp.u * (V + C)) := by simp
  have hden : 0 < 1 - (m : ℝ) * fp.u := by linarith
  unfold gamma
  change C ≤ ((m : ℝ) * fp.u / (1 - (m : ℝ) * fp.u)) * V
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hden).2
  nlinarith

private theorem vecSum_correction_norm (fp : ErrorFreeAddModel) {m : ℕ}
    (v : Fin (m + 1) → ℝ) :
    (∑ i : Fin m, |vecSum fp v i.castSucc|) =
      ∑ i : Fin m, |twoSumCorrection fp v i| := by
  apply Finset.sum_congr rfl
  intro i hi
  simp [vecSum]

private theorem vecSum_l1_le_correction (fp : ErrorFreeAddModel) {m : ℕ}
    (v : Fin (m + 1) → ℝ) :
    (∑ i, |vecSum fp v i|) ≤ |∑ i, v i| +
      2 * ∑ i : Fin m, |twoSumCorrection fp v i| := by
  let C := ∑ i : Fin m, |twoSumCorrection fp v i|
  let CS := ∑ i : Fin m, twoSumCorrection fp v i
  let S := ∑ i : Fin (m + 1), v i
  let H := twoSumPrefix fp v m (Nat.le_refl m)
  have hs := vecSum_sum fp v
  rw [Fin.sum_univ_castSucc] at hs ⊢
  simp only [vecSum, Fin.lastCases_castSucc, Fin.lastCases_last] at hs ⊢
  have hH : |H| ≤ |S| + C := by
    have he : H = S - CS := by
      dsimp only [H, S, CS]
      linarith
    rw [he]
    have habs : |CS| ≤ C := Finset.abs_sum_le_sum_abs _ _
    exact (abs_sub _ _).trans (by linarith)
  change C + |H| ≤ |S| + 2 * C
  linarith

private theorem vecSum_l1_le (fp : ErrorFreeAddModel) {m : ℕ}
    (v : Fin (m + 1) → ℝ) (hv : (m : ℝ) * fp.u < 1) :
    (∑ i, |vecSum fp v i|) ≤
      |∑ i, v i| + 2 * gamma fp.u m * ∑ i, |v i| := by
  let C := ∑ i : Fin m, |twoSumCorrection fp v i|
  let CS := ∑ i : Fin m, twoSumCorrection fp v i
  let S := ∑ i : Fin (m + 1), v i
  let H := twoSumPrefix fp v m (Nat.le_refl m)
  have hc := correctionNorm_le_gamma fp v hv
  have hs := vecSum_sum fp v
  rw [Fin.sum_univ_castSucc] at hs ⊢
  simp only [vecSum, Fin.lastCases_castSucc, Fin.lastCases_last] at hs ⊢
  have hH : |H| ≤ |S| + C := by
    have he : H = S - CS := by
      dsimp only [H, S, CS]
      linarith
    rw [he]
    have habs : |CS| ≤ C := Finset.abs_sum_le_sum_abs _ _
    exact (abs_sub _ _).trans (by linarith)
  change C + |H| ≤ |S| + 2 * gamma fp.u m * (∑ i, |v i|)
  calc
    C + |H| ≤ C + (|S| + C) := by linarith
    _ ≤ |S| + 2 * gamma fp.u m * (∑ i, |v i|) := by nlinarith

private theorem recursiveSum_last_error (fp : StandardAddModel) {r : ℕ}
    (v : Fin (r + 2) → ℝ)
    (hv : (((2 * (r + 1) : ℕ) : ℝ) * fp.u) < 1) :
    |recursiveSum fp.fl_add (r + 2) v - ∑ i, v i| ≤
      fp.u * |∑ i, v i| +
        gamma fp.u (2 * (r + 1)) * ∑ i : Fin (r + 1), |v i.castSucc| := by
  have hr : (r : ℝ) * fp.u < 1 := by
    have hu := fp.u_nonneg
    norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at hv
    nlinarith
  have hr1 : (((r + 1 : ℕ) : ℝ) * fp.u) < 1 := by
    have hu := fp.u_nonneg
    norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at hv ⊢
    nlinarith
  have hrec := recursiveSum_error fp
    (v := fun i : Fin (r + 1) => v i.castSucc) hr
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add
    (recursiveSum fp.fl_add (r + 1)
      (fun i : Fin (r + 1) => v i.castSucc))
    (v (Fin.last (r + 1)))
  rw [Fin.sum_univ_castSucc v]
  rw [recursiveSum]
  rw [dif_neg (by omega)]
  rw [hfl]
  let A := recursiveSum fp.fl_add (r + 1)
    (fun i : Fin (r + 1) => v i.castSucc)
  let T := ∑ i : Fin (r + 1), v i.castSucc
  let C := ∑ i : Fin (r + 1), |v i.castSucc|
  let z := v (Fin.last (r + 1))
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hraw : |(A + z) * (1 + δ) - (T + z)| ≤
      fp.u * |T + z| + (1 + fp.u) * (gamma fp.u r * C) := by
    calc
      |(A + z) * (1 + δ) - (T + z)| =
          |(A - T) + δ * ((T + z) + (A - T))| := by ring_nf
      _ ≤ |A - T| + |δ * ((T + z) + (A - T))| := abs_add_le _ _
      _ = |A - T| + |δ| * |(T + z) + (A - T)| := by rw [abs_mul]
      _ ≤ |A - T| + fp.u * (|T + z| + |A - T|) := by
        apply add_le_add (le_refl _)
        exact
          (mul_le_mul_of_nonneg_right hδ (abs_nonneg _)).trans
            (mul_le_mul_of_nonneg_left (abs_add_le _ _) fp.u_nonneg)
      _ ≤ fp.u * |T + z| + (1 + fp.u) * (gamma fp.u r * C) := by
        have hh := mul_le_mul_of_nonneg_left hrec
          (by linarith [fp.u_nonneg] : 0 ≤ 1 + fp.u)
        nlinarith
  have hstep := gamma_step fp.u r fp.u_nonneg hr1
  have hmono : gamma fp.u (r + 1) ≤ gamma fp.u (2 * (r + 1)) :=
    gamma_mono fp.u fp.u_nonneg (by omega) hv
  have hcoef : (1 + fp.u) * gamma fp.u r ≤
      gamma fp.u (2 * (r + 1)) := by
    linarith [fp.u_nonneg]
  calc
    |(A + z) * (1 + δ) - (T + z)|
        ≤ fp.u * |T + z| + (1 + fp.u) * (gamma fp.u r * C) := hraw
    _ ≤ fp.u * |T + z| + gamma fp.u (2 * (r + 1)) * C := by
      have := mul_le_mul_of_nonneg_right hcoef hC
      nlinarith

private theorem gamma_contract (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hsmall : (4 : ℝ) * (m : ℝ) * u < 1) :
    let a := gamma u m
    let q := gamma u (2 * m)
    0 ≤ q ∧ q ≤ 1 ∧ a ≤ q ∧ 2 * a ≤ q ∧
      a + 2 * a * q ≤ q := by
  dsimp only
  have hm : (m : ℝ) * u < 1 := by nlinarith
  have h2m : (((2 * m : ℕ) : ℝ) * u) < 1 := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have hq0 := gamma_nonneg_of_valid u (2 * m) hu h2m
  have hmq := gamma_mono u hu (show m ≤ 2 * m by omega) h2m
  have hq1 : gamma u (2 * m) ≤ 1 := by
    unfold gamma
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    apply (div_le_iff₀ (by nlinarith : 0 < 1 - 2 * (m : ℝ) * u)).2
    nlinarith
  have hd1 : 1 - (m : ℝ) * u ≠ 0 := by linarith
  have hd2 : 1 - 2 * (m : ℝ) * u ≠ 0 := by nlinarith
  have hdiff :
      gamma u (2 * m) - gamma u m -
          2 * gamma u m * gamma u (2 * m) =
        ((m : ℝ) * u * (1 - 4 * ((m : ℝ) * u))) /
          ((1 - (m : ℝ) * u) * (1 - 2 * ((m : ℝ) * u))) := by
    unfold gamma
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    field_simp [hd1, hd2]
    ring
  have hdiff2 : gamma u (2 * m) - 2 * gamma u m =
      (2 * ((m : ℝ) * u) ^ 2) /
        ((1 - (m : ℝ) * u) * (1 - 2 * ((m : ℝ) * u))) := by
    unfold gamma
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    field_simp [hd1, hd2]
    ring
  have hden : 0 ≤
      (1 - (m : ℝ) * u) * (1 - 2 * ((m : ℝ) * u)) := by
    exact mul_nonneg (by linarith) (by nlinarith)
  have h2a : 2 * gamma u m ≤ gamma u (2 * m) := by
    have : 0 ≤ gamma u (2 * m) - 2 * gamma u m := by
      rw [hdiff2]
      exact div_nonneg (by positivity) hden
    linarith
  refine ⟨hq0, hq1, hmq, h2a, ?_⟩
  have hnum : 0 ≤ (m : ℝ) * u * (1 - 4 * ((m : ℝ) * u)) := by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by nlinarith)
  have hnon : 0 ≤ gamma u (2 * m) - gamma u m -
      2 * gamma u m * gamma u (2 * m) := by
    rw [hdiff]
    exact div_nonneg hnum hden
  linarith

private theorem iteratedVecSum_correction_bound (fp : ErrorFreeAddModel)
    {m : ℕ} (v : Fin (m + 1) → ℝ) (j : ℕ)
    (hsmall : (4 : ℝ) * (m : ℝ) * fp.u < 1) :
    (∑ i : Fin m, |iteratedVecSum fp j v i.castSucc|) ≤
      gamma fp.u (2 * m) * |∑ i, v i| +
        (gamma fp.u (2 * m)) ^ j * ∑ i, |v i| := by
  let a := gamma fp.u m
  let q := gamma fp.u (2 * m)
  obtain ⟨hq0, hq1, haq, h2aq, hfix⟩ :=
    gamma_contract fp.u m fp.u_nonneg hsmall
  have hm : (m : ℝ) * fp.u < 1 := by nlinarith
  have ha0 : 0 ≤ a := gamma_nonneg_of_valid _ _ fp.u_nonneg hm
  induction j with
  | zero =>
      simp only [iteratedVecSum, pow_zero, one_mul]
      have hp : (∑ i : Fin m, |v i.castSucc|) ≤ ∑ i, |v i| := by
        have hh := fin_sum_castLE_abs_le (Nat.le_succ m) v
        convert hh using 1 <;> congr
      exact hp.trans (le_add_of_nonneg_left (mul_nonneg hq0 (abs_nonneg _)))
  | succ j ih =>
      simp only [iteratedVecSum]
      rw [vecSum_correction_norm]
      have hc := correctionNorm_le_gamma fp (iteratedVecSum fp j v) hm
      change (∑ i : Fin m,
          |twoSumCorrection fp (iteratedVecSum fp j v) i|) ≤
        q * |∑ i, v i| + q ^ (j + 1) * ∑ i, |v i|
      by_cases hj : j = 0
      · subst j
        simp only [iteratedVecSum, pow_one]
        calc
          (∑ i : Fin m, |twoSumCorrection fp v i|)
              ≤ a * ∑ i, |v i| := hc
          _ ≤ q * ∑ i, |v i| :=
            mul_le_mul_of_nonneg_right haq
              (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
          _ ≤ q * |∑ i, v i| + q * ∑ i, |v i| := by
            exact le_add_of_nonneg_left (mul_nonneg hq0 (abs_nonneg _))
          _ = q * |∑ i, v i| + q ^ (0 + 1) * ∑ i, |v i| := by simp
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
        have hl := vecSum_l1_le_correction fp
          (iteratedVecSum fp k v)
        have hsum := iteratedVecSum_sum fp k v
        rw [hsum] at hl
        have hcn := vecSum_correction_norm fp (iteratedVecSum fp k v)
        have hnorm : (∑ i, |iteratedVecSum fp (k + 1) v i|) ≤
            |∑ i, v i| +
              2 * ∑ i : Fin m,
                |iteratedVecSum fp (k + 1) v i.castSucc| := by
          simpa only [iteratedVecSum, hcn] using hl
        have hcorr := ih
        have hV : 0 ≤ ∑ i, |v i| :=
          Finset.sum_nonneg (fun _ _ => abs_nonneg _)
        have hS : 0 ≤ |∑ i, v i| := abs_nonneg _
        calc
          (∑ i : Fin m,
              |twoSumCorrection fp (iteratedVecSum fp (k + 1) v) i|)
              ≤ a * ∑ i, |iteratedVecSum fp (k + 1) v i| := hc
          _ ≤ a * (|∑ i, v i| +
                2 * ∑ i : Fin m,
                  |iteratedVecSum fp (k + 1) v i.castSucc|) :=
            mul_le_mul_of_nonneg_left hnorm ha0
          _ ≤ q * |∑ i, v i| + q ^ (k + 1 + 1) * ∑ i, |v i| := by
            have hpow : 0 ≤ q ^ (k + 1) := pow_nonneg hq0 _
            calc
              a * (|∑ i, v i| +
                    2 * ∑ i : Fin m,
                      |iteratedVecSum fp (k + 1) v i.castSucc|) =
                  a * |∑ i, v i| + 2 * a *
                    (∑ i : Fin m,
                      |iteratedVecSum fp (k + 1) v i.castSucc|) := by ring
              _ ≤ a * |∑ i, v i| + 2 * a *
                    (q * |∑ i, v i| + q ^ (k + 1) * ∑ i, |v i|) := by
                have hmul := mul_le_mul_of_nonneg_left hcorr
                  (show 0 ≤ 2 * a by nlinarith [ha0])
                exact add_le_add (le_refl _) hmul
              _ = (a + 2 * a * q) * |∑ i, v i| +
                    (2 * a) * (q ^ (k + 1) * ∑ i, |v i|) := by ring
              _ ≤ q * |∑ i, v i| +
                    q * (q ^ (k + 1) * ∑ i, |v i|) := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_right hfix hS)
                  (mul_le_mul_of_nonneg_right h2aq (mul_nonneg hpow hV))
              _ = q * |∑ i, v i| + q ^ (k + 1 + 1) * ∑ i, |v i| := by
                rw [pow_succ]
                ring

private theorem dotKTransform_sum (fp : ErrorFreeDotModel) {n : ℕ}
    (x y : Fin (n + 1) → ℝ) :
    ∑ i, dotKTransform fp x y i = exactDot x y := by
  unfold dotKTransform exactDot
  have hsplit := Fin.sum_univ_add
    (fun j : Fin ((n + 1) + (n + 1)) =>
      @Fin.addCases (n + 1) (n + 1) (fun _ => ℝ)
        (fun i : Fin (n + 1) => (fp.twoProduct (x i) (y i)).2)
        (vecSum fp.toErrorFreeAddModel
          (fun i : Fin (n + 1) => (fp.twoProduct (x i) (y i)).1)) j)
  simp only [Fin.addCases_left, Fin.addCases_right] at hsplit
  have hsplit' : (∑ j : Fin ((2 * n + 1) + 1),
      Fin.addCases
        (fun i : Fin (n + 1) => (fp.twoProduct (x i) (y i)).2)
        (vecSum fp.toErrorFreeAddModel
          (fun i : Fin (n + 1) => (fp.twoProduct (x i) (y i)).1))
        (Fin.cast (by omega) j)) =
      (∑ i : Fin (n + 1), (fp.twoProduct (x i) (y i)).2) +
      ∑ i : Fin (n + 1),
        vecSum fp.toErrorFreeAddModel
          (fun i : Fin (n + 1) => (fp.twoProduct (x i) (y i)).1) i := by
    calc
      _ = ∑ j : Fin ((n + 1) + (n + 1)),
          @Fin.addCases (n + 1) (n + 1) (fun _ => ℝ)
            (fun i : Fin (n + 1) => (fp.twoProduct (x i) (y i)).2)
            (vecSum fp.toErrorFreeAddModel
              (fun i : Fin (n + 1) => (fp.twoProduct (x i) (y i)).1)) j := by
        simpa using Equiv.sum_comp
          (Fin.castOrderIso (show ((2 * n + 1) + 1) =
            (n + 1) + (n + 1) by omega)).toEquiv
          (fun j : Fin ((n + 1) + (n + 1)) =>
            @Fin.addCases (n + 1) (n + 1) (fun _ => ℝ)
              (fun i : Fin (n + 1) => (fp.twoProduct (x i) (y i)).2)
              (vecSum fp.toErrorFreeAddModel
                (fun i : Fin (n + 1) => (fp.twoProduct (x i) (y i)).1)) j)
      _ = _ := hsplit
  rw [hsplit']
  rw [vecSum_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simpa [add_comm] using fp.twoProduct_exact (x i) (y i)

private theorem dotKTransform_l1_split (fp : ErrorFreeDotModel) {n : ℕ}
    (x y : Fin (n + 1) → ℝ) :
    (∑ i, |dotKTransform fp x y i|) =
      (∑ i : Fin (n + 1), |(fp.twoProduct (x i) (y i)).2|) +
        ∑ i : Fin (n + 1),
          |vecSum fp.toErrorFreeAddModel
            (fun i : Fin (n + 1) => (fp.twoProduct (x i) (y i)).1) i| := by
  unfold dotKTransform
  let g : Fin ((n + 1) + (n + 1)) → ℝ := fun j =>
    @Fin.addCases (n + 1) (n + 1) (fun _ => ℝ)
      (fun i => (fp.twoProduct (x i) (y i)).2)
      (vecSum fp.toErrorFreeAddModel
        (fun i => (fp.twoProduct (x i) (y i)).1)) j
  have ht : (∑ j : Fin ((2 * n + 1) + 1),
        |g (Fin.cast (by omega) j)|) =
      ∑ j : Fin ((n + 1) + (n + 1)), |g j| := by
    simpa using Equiv.sum_comp
      (Fin.castOrderIso (show ((2 * n + 1) + 1) =
        (n + 1) + (n + 1) by omega)).toEquiv (fun j => |g j|)
  dsimp only [g] at ht
  rw [ht]
  rw [Fin.sum_univ_add]
  simp only [g, Fin.addCases_left, Fin.addCases_right]

private theorem dotKTransform_l1_le (fp : ErrorFreeDotModel) {n : ℕ}
    (x y : Fin (n + 1) → ℝ)
    (hsmall : (8 : ℝ) * ((n + 1 : ℕ) : ℝ) * fp.u ≤ 1) :
    (∑ i, |dotKTransform fp x y i|) ≤
      |exactDot x y| +
        gamma fp.u (4 * (n + 1) - 2) * dotMagnitude x y := by
  let M := dotMagnitude x y
  let E := ∑ i : Fin (n + 1), |(fp.twoProduct (x i) (y i)).2|
  let P := ∑ i : Fin (n + 1), |(fp.twoProduct (x i) (y i)).1|
  let a := gamma fp.u n
  let q := gamma fp.u (4 * (n + 1) - 2)
  have hM : 0 ≤ M := by
    dsimp only [M, dotMagnitude]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hE : E ≤ fp.u * M := by
    dsimp only [E, M, dotMagnitude]
    calc
      (∑ i : Fin (n + 1), |(fp.twoProduct (x i) (y i)).2|)
          ≤ ∑ i : Fin (n + 1), fp.u * |x i * y i| :=
        Finset.sum_le_sum (fun i _ => fp.twoProduct_low_le_exact _ _)
      _ = fp.u * ∑ i : Fin (n + 1), |x i| * |y i| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul]
  have hP : P ≤ (1 + fp.u) * M := by
    dsimp only [P, M, dotMagnitude]
    calc
      (∑ i : Fin (n + 1), |(fp.twoProduct (x i) (y i)).1|)
          ≤ ∑ i : Fin (n + 1), (1 + fp.u) * |x i * y i| := by
        apply Finset.sum_le_sum
        intro i hi
        have he := fp.twoProduct_exact (x i) (y i)
        have hl := fp.twoProduct_low_le_exact (x i) (y i)
        rw [show (fp.twoProduct (x i) (y i)).1 =
            x i * y i - (fp.twoProduct (x i) (y i)).2 by linarith]
        calc
          |x i * y i - (fp.twoProduct (x i) (y i)).2|
              ≤ |x i * y i| + |(fp.twoProduct (x i) (y i)).2| := abs_sub _ _
          _ ≤ (1 + fp.u) * |x i * y i| := by nlinarith
      _ = (1 + fp.u) * ∑ i : Fin (n + 1), |x i| * |y i| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul]
  have hnvalid : (n : ℝ) * fp.u < 1 := by
    have hu := fp.u_nonneg
    norm_num only [Nat.cast_add, Nat.cast_one] at hsmall
    nlinarith
  have hn1valid : (((n + 1 : ℕ) : ℝ) * fp.u) < 1 := by
    have hu := fp.u_nonneg
    norm_num only [Nat.cast_add, Nat.cast_one] at hsmall ⊢
    nlinarith
  have htargetvalid : (((4 * (n + 1) - 2 : ℕ) : ℝ) * fp.u) < 1 := by
    have hu := fp.u_nonneg
    have harith : (4 * (n + 1) - 2 : ℕ) = 4 * n + 2 := by omega
    rw [harith]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one] at hsmall ⊢
    nlinarith
  have hfour : (4 : ℝ) * ((n + 1 : ℕ) : ℝ) * fp.u < 1 := by
    have hu := fp.u_nonneg
    nlinarith
  obtain ⟨_, _, _, hdouble, _⟩ :=
    gamma_contract fp.u (n + 1) fp.u_nonneg hfour
  have hmono : gamma fp.u (2 * (n + 1)) ≤
      gamma fp.u (4 * (n + 1) - 2) :=
    gamma_mono fp.u fp.u_nonneg (by omega) htargetvalid
  have hstep := gamma_step fp.u n fp.u_nonneg hn1valid
  have hcoef : 2 * fp.u + 2 * a * (1 + fp.u) ≤ q := by
    dsimp only [a, q]
    nlinarith
  let H := ∑ i : Fin (n + 1), (fp.twoProduct (x i) (y i)).1
  let L := ∑ i : Fin (n + 1), (fp.twoProduct (x i) (y i)).2
  have hHL : H + L = exactDot x y := by
    dsimp only [H, L, exactDot]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact fp.twoProduct_exact _ _
  have hH : |H| ≤ |exactDot x y| + E := by
    have hLabs : |L| ≤ E := by
      exact Finset.abs_sum_le_sum_abs _ _
    rw [show H = exactDot x y - L by linarith]
    exact (abs_sub _ _).trans (add_le_add (le_refl _) hLabs)
  have hvec := vecSum_l1_le fp.toErrorFreeAddModel
    (fun i : Fin (n + 1) => (fp.twoProduct (x i) (y i)).1) hnvalid
  change (∑ i : Fin (n + 1),
      |vecSum fp.toErrorFreeAddModel
        (fun i : Fin (n + 1) => (fp.twoProduct (x i) (y i)).1) i|) ≤
      |H| + 2 * a * P at hvec
  rw [dotKTransform_l1_split]
  calc
    E + (∑ i : Fin (n + 1),
        |vecSum fp.toErrorFreeAddModel
          (fun i : Fin (n + 1) => (fp.twoProduct (x i) (y i)).1) i|)
        ≤ E + (|H| + 2 * a * P) := add_le_add (le_refl _) hvec
    _ ≤ E + (|exactDot x y| + E + 2 * a * P) := by linarith
    _ ≤ |exactDot x y| +
          (2 * fp.u + 2 * a * (1 + fp.u)) * M := by
      have ha0 := gamma_nonneg_of_valid fp.u n fp.u_nonneg hnvalid
      have hmulP := mul_le_mul_of_nonneg_left hP (by nlinarith : 0 ≤ 2 * a)
      nlinarith
    _ ≤ |exactDot x y| + q * M := by
      exact add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_right hcoef hM)

theorem p02_t3_dotK_error_bound
    (fp : ErrorFreeDotModel) (n K : ℕ) (x y : Fin (n + 1) → ℝ)
    (hK : 3 ≤ K)
    (hsmall : (8 : ℝ) * ((n + 1 : ℕ) : ℝ) * fp.u ≤ 1) :
    |dotK fp K x y - exactDot x y| ≤
      (fp.u + 2 * (gamma fp.u (4 * (n + 1) - 2)) ^ 2) * |exactDot x y| +
        (gamma fp.u (4 * (n + 1) - 2)) ^ K * dotMagnitude x y := by
  -- PROOF_START P02-T3-H001
  let v := dotKTransform fp x y
  let m := 2 * n + 1
  let q := gamma fp.u (4 * (n + 1) - 2)
  let S := exactDot x y
  let M := dotMagnitude x y
  have hm_eq : 2 * m = 4 * (n + 1) - 2 := by
    dsimp only [m]
    omega
  have hfourm : (4 : ℝ) * (m : ℝ) * fp.u < 1 := by
    dsimp only [m]
    have hu := fp.u_nonneg
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one] at hsmall ⊢
    nlinarith
  have htwom : ((2 * m : ℕ) : ℝ) * fp.u < 1 := by
    have hu := fp.u_nonneg
    have hfm := hfourm
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hfm ⊢
    nlinarith
  obtain ⟨hq0, hq1, _, _, _⟩ :=
    gamma_contract fp.u m fp.u_nonneg hfourm
  have hq0' : 0 ≤ q := by simpa [q, hm_eq] using hq0
  have hq1' : q ≤ 1 := by simpa [q, hm_eq] using hq1
  have hsumv : ∑ i, v i = S := by
    exact dotKTransform_sum fp x y
  have hl1v : (∑ i, |v i|) ≤ |S| + q * M := by
    exact dotKTransform_l1_le fp x y hsmall
  have hcorr := iteratedVecSum_correction_bound
    fp.toErrorFreeAddModel v (K - 2) hfourm
  rw [hm_eq] at hcorr
  change (∑ i : Fin m,
      |iteratedVecSum fp.toErrorFreeAddModel (K - 2) v i.castSucc|) ≤
    q * |∑ i, v i| + q ^ (K - 2) * ∑ i, |v i| at hcorr
  rw [hsumv] at hcorr
  have hsumiter := iteratedVecSum_sum fp.toErrorFreeAddModel (K - 2) v
  rw [hsumv] at hsumiter
  have herr := recursiveSum_last_error fp.toStandardAddModel
    (r := 2 * n)
    (v := iteratedVecSum fp.toErrorFreeAddModel (K - 2) v)
    (by
      convert htwom using 1 <;> dsimp only [m] <;> norm_num <;> omega)
  have hidx : 2 * (2 * n + 1) = 4 * (n + 1) - 2 := by omega
  rw [hidx] at herr
  change
    |recursiveSum fp.fl_add ((2 * n + 1) + 1)
        (iteratedVecSum fp.toErrorFreeAddModel (K - 2) v) -
        ∑ i, iteratedVecSum fp.toErrorFreeAddModel (K - 2) v i| ≤
      fp.u * |∑ i, iteratedVecSum fp.toErrorFreeAddModel (K - 2) v i| +
        q * ∑ i : Fin m,
          |iteratedVecSum fp.toErrorFreeAddModel (K - 2) v i.castSucc| at herr
  rw [hsumiter] at herr
  have hraw :
      |recursiveSum fp.fl_add ((2 * n + 1) + 1)
          (iteratedVecSum fp.toErrorFreeAddModel (K - 2) v) - S| ≤
        fp.u * |S| + q *
          (q * |S| + q ^ (K - 2) * (|S| + q * M)) := by
    calc
      |recursiveSum fp.fl_add ((2 * n + 1) + 1)
          (iteratedVecSum fp.toErrorFreeAddModel (K - 2) v) - S|
          ≤ fp.u * |S| + q *
              (∑ i : Fin m,
                |iteratedVecSum fp.toErrorFreeAddModel (K - 2) v i.castSucc|) :=
        herr
      _ ≤ fp.u * |S| + q *
            (q * |S| + q ^ (K - 2) * ∑ i, |v i|) := by
        exact add_le_add (le_refl _)
          (mul_le_mul_of_nonneg_left hcorr hq0')
      _ ≤ fp.u * |S| + q *
            (q * |S| + q ^ (K - 2) * (|S| + q * M)) := by
        have hp0 : 0 ≤ q ^ (K - 2) := pow_nonneg hq0' _
        exact add_le_add (le_refl _)
          (mul_le_mul_of_nonneg_left
            (add_le_add (le_refl _)
              (mul_le_mul_of_nonneg_left hl1v hp0)) hq0')
  have hpow : q ^ (K - 1) ≤ q ^ 2 := by
    apply pow_le_pow_of_le_one hq0' hq1'
    omega
  have hM : 0 ≤ M := by
    dsimp only [M, dotMagnitude]
    exact Finset.sum_nonneg
      (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hS : 0 ≤ |S| := abs_nonneg _
  have hfinal :
      fp.u * |S| + q *
          (q * |S| + q ^ (K - 2) * (|S| + q * M)) ≤
        (fp.u + 2 * q ^ 2) * |S| + q ^ K * M := by
    have hk2 : K - 2 + 1 = K - 1 := by omega
    have hk1 : K - 1 + 1 = K := by omega
    have hp1 : q * q ^ (K - 2) = q ^ (K - 1) := by
      calc
        q * q ^ (K - 2) = q ^ (K - 2) * q := mul_comm _ _
        _ = q ^ (K - 2 + 1) := (pow_succ _ _).symm
        _ = q ^ (K - 1) := by rw [hk2]
    have hp2 : q ^ (K - 1) * q = q ^ K := by
      calc
        q ^ (K - 1) * q = q ^ (K - 1 + 1) := (pow_succ _ _).symm
        _ = q ^ K := by rw [hk1]
    have hexpand :
        fp.u * |S| + q *
            (q * |S| + q ^ (K - 2) * (|S| + q * M)) =
          (fp.u + q ^ 2 + q ^ (K - 1)) * |S| + q ^ K * M := by
      calc
        fp.u * |S| + q *
            (q * |S| + q ^ (K - 2) * (|S| + q * M)) =
          (fp.u + q ^ 2 + q * q ^ (K - 2)) * |S| +
            (q * q ^ (K - 2)) * q * M := by ring
        _ = (fp.u + q ^ 2 + q ^ (K - 1)) * |S| + q ^ K * M := by
          rw [hp1, hp2]
    rw [hexpand]
    have hpS := mul_le_mul_of_nonneg_right hpow hS
    nlinarith
  have hmain := hraw.trans hfinal
  dsimp only [v, S, M, q] at hmain ⊢
  have hsub : K - 1 - 1 = K - 2 := by omega
  simpa only [dotK, sumK, hsub] using hmain

end HighamBench
