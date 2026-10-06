import HighamBench.P02Definitions
import NumStability.Algorithms.Summation.Recursive.Core

namespace HighamBench

open scoped BigOperators

noncomputable def StandardAddModel.toFPModel (fp : StandardAddModel) :
    NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fun x y => x - y
  fl_mul := fun x y => x * y
  fl_div := fun x y => x / y
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := by
    intro x y
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_mul := by
    intro x y
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_div := by
    intro x y hy
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_sqrt := by
    intro x hx
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩

lemma recursiveSum_eq_fl_recursiveSum (fp : StandardAddModel) :
    ∀ (m : ℕ) (w : Fin m → ℝ),
      recursiveSum fp.fl_add m w =
        NumStability.fl_recursiveSum fp.toFPModel m w
  | 0, w => by simp [recursiveSum, NumStability.fl_recursiveSum]
  | m + 1, w => by
      rw [recursiveSum]
      split_ifs with hm
      · subst m
        rw [NumStability.fl_recursiveSum, Fin.foldl_succ_last]
        simp [StandardAddModel.toFPModel, fp.fl_add_zero]
      · rw [NumStability.fl_recursiveSum, Fin.foldl_succ_last]
        change fp.fl_add (recursiveSum fp.fl_add m fun i => w i.castSucc)
            (w (Fin.last m)) = _
        rw [recursiveSum_eq_fl_recursiveSum fp m]
        rfl

lemma recursiveSum_forward_error_bound (fp : StandardAddModel)
    (m : ℕ) (w : Fin m → ℝ) (hvalid : GammaValid fp.u (m - 1)) :
    |recursiveSum fp.fl_add m w - ∑ i : Fin m, w i| ≤
      gamma fp.u (m - 1) * ∑ i : Fin m, |w i| := by
  rw [recursiveSum_eq_fl_recursiveSum]
  simpa [GammaValid, gamma, NumStability.gammaValid, NumStability.gamma,
    StandardAddModel.toFPModel] using
      NumStability.recursiveSum_forward_error_bound fp.toFPModel m w hvalid

lemma recursiveSum_abs_bound (fp : StandardAddModel)
    (m : ℕ) (w : Fin m → ℝ) (hvalid : GammaValid fp.u (m - 1)) :
    |recursiveSum fp.fl_add m w| ≤
      (1 + gamma fp.u (m - 1)) * ∑ i : Fin m, |w i| := by
  rw [recursiveSum_eq_fl_recursiveSum]
  simpa [GammaValid, gamma, NumStability.gammaValid, NumStability.gamma,
    StandardAddModel.toFPModel] using
      NumStability.recursiveSum_abs_le_one_add_gamma_mul_sum_abs
        fp.toFPModel m w hvalid

lemma GammaValid.mono (fp : StandardAddModel) {k m : ℕ}
    (hkm : k ≤ m) (hm : GammaValid fp.u m) : GammaValid fp.u k := by
  simpa [GammaValid, NumStability.gammaValid, StandardAddModel.toFPModel] using
    NumStability.gammaValid_mono fp.toFPModel hkm hm

lemma gamma_mono (fp : StandardAddModel) {k m : ℕ}
    (hkm : k ≤ m) (hm : GammaValid fp.u m) :
    gamma fp.u k ≤ gamma fp.u m := by
  simpa [GammaValid, gamma, NumStability.gammaValid, NumStability.gamma,
    StandardAddModel.toFPModel] using
      NumStability.gamma_mono fp.toFPModel hkm hm

lemma gamma_nonneg (fp : StandardAddModel) {m : ℕ}
    (hm : GammaValid fp.u m) : 0 ≤ gamma fp.u m := by
  simpa [GammaValid, gamma, NumStability.gammaValid, NumStability.gamma,
    StandardAddModel.toFPModel] using
      NumStability.gamma_nonneg fp.toFPModel hm

lemma gamma_mul_one_add (u : ℝ) (m : ℕ) (hm : GammaValid u m) :
    (m : ℝ) * u * (1 + gamma u m) = gamma u m := by
  have hden : 1 - (m : ℝ) * u ≠ 0 := by
    unfold GammaValid at hm
    linarith
  unfold gamma
  field_simp [hden]
  ring

lemma one_add_u_mul_gamma_pred_le_gamma (fp : StandardAddModel)
    (m : ℕ) (hmpos : 0 < m) (hm : GammaValid fp.u m) :
    (1 + fp.u) * gamma fp.u (m - 1) ≤ gamma fp.u m := by
  have hpred : GammaValid fp.u (m - 1) :=
    GammaValid.mono fp (Nat.sub_le m 1) hm
  have hone : GammaValid fp.u 1 :=
    GammaValid.mono fp (by omega) hm
  have hsum :
      gamma fp.u (m - 1) + gamma fp.u 1 +
          gamma fp.u (m - 1) * gamma fp.u 1 ≤
        gamma fp.u ((m - 1) + 1) := by
    simpa [GammaValid, gamma, NumStability.gammaValid, NumStability.gamma,
      StandardAddModel.toFPModel] using
        NumStability.gamma_sum_le fp.toFPModel (m - 1) 1 (by
          simpa [Nat.sub_add_cancel hmpos] using hm)
  have hu : fp.u ≤ gamma fp.u 1 := by
    simpa [GammaValid, gamma, NumStability.gammaValid, NumStability.gamma,
      StandardAddModel.toFPModel] using
        NumStability.u_le_gamma fp.toFPModel (by omega : 0 < 1) hone
  have hgp : 0 ≤ gamma fp.u (m - 1) := gamma_nonneg fp hpred
  have hg1 : 0 ≤ gamma fp.u 1 := gamma_nonneg fp hone
  rw [Nat.sub_add_cancel hmpos] at hsum
  nlinarith [mul_le_mul_of_nonneg_left hu hgp]

lemma fin_prefix_abs_sum_le {n k : ℕ} (hk : k ≤ n)
    (v : Fin (n + 1) → ℝ) :
    (∑ i : Fin (k + 1),
        |v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩|) ≤
      ∑ i : Fin (n + 1), |v i| := by
  let f : ℕ → ℝ := fun i => if hi : i < n + 1 then |v ⟨i, hi⟩| else 0
  calc
    (∑ i : Fin (k + 1),
        |v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩|) =
        ∑ i : Fin (k + 1), f i := by
          apply Finset.sum_congr rfl
          intro i hi
          dsimp [f]
          rw [dif_pos (Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk))]
    _ = ∑ i ∈ Finset.range (k + 1), f i :=
      Fin.sum_univ_eq_sum_range f (k + 1)
    _ ≤ ∑ i ∈ Finset.range (n + 1), f i := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.succ_le_succ hk))
        (by
          intro i hi hnot
          have hil : i < n + 1 := Finset.mem_range.mp hi
          dsimp [f]
          rw [dif_pos hil]
          exact abs_nonneg _)
    _ = ∑ i : Fin (n + 1), f i :=
      (Fin.sum_univ_eq_sum_range f (n + 1)).symm
    _ = ∑ i : Fin (n + 1), |v i| := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [f]
      simp [i.isLt]

lemma twoSumPrefix_succ (fp : ErrorFreeAddModel) {n k : ℕ}
    (v : Fin (n + 1) → ℝ) (hk : k + 1 ≤ n) :
    twoSumPrefix fp v (k + 1) hk =
      (fp.twoSum
        (twoSumPrefix fp v k (Nat.le_trans (Nat.le_succ k) hk))
        (v ⟨k + 1, Nat.succ_lt_succ
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)⟩)).1 := by
  rw [twoSumPrefix, Fin.foldl_succ_last]
  rfl

lemma twoSumPrefix_eq_recursiveSum (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) : ∀ (k : ℕ) (hk : k ≤ n),
    twoSumPrefix fp v k hk =
      recursiveSum fp.fl_add (k + 1)
        (fun i => v ⟨i.val, Nat.lt_of_lt_of_le i.isLt
          (Nat.succ_le_succ hk)⟩)
  | 0, hk => by simp [twoSumPrefix, recursiveSum]
  | k + 1, hk => by
      rw [twoSumPrefix_succ, fp.twoSum_high]
      rw [recursiveSum]
      simp only [Nat.succ_ne_zero, ↓reduceDIte]
      rw [twoSumPrefix_eq_recursiveSum fp v k (Nat.le_trans (Nat.le_succ k) hk)]
      congr 1

lemma twoSumPrefix_abs_le (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (hvalid : GammaValid fp.u n)
    (k : ℕ) (hk : k ≤ n) :
    |twoSumPrefix fp v k hk| ≤
      (1 + gamma fp.u n) * ∑ i : Fin (n + 1), |v i| := by
  let w : Fin (k + 1) → ℝ := fun i =>
    v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩
  have hvalidk : GammaValid fp.u k :=
    GammaValid.mono fp.toStandardAddModel hk hvalid
  have hb := recursiveSum_abs_bound fp.toStandardAddModel (k + 1) w (by
    simpa using hvalidk)
  have hprefix : twoSumPrefix fp v k hk = recursiveSum fp.fl_add (k + 1) w := by
    simpa [w] using twoSumPrefix_eq_recursiveSum fp v k hk
  have hgamma : gamma fp.u k ≤ gamma fp.u n :=
    gamma_mono fp.toStandardAddModel hk hvalid
  have hsum : (∑ i : Fin (k + 1), |w i|) ≤
      ∑ i : Fin (n + 1), |v i| := by
    simpa [w] using fin_prefix_abs_sum_le hk v
  have hcoef : 0 ≤ 1 + gamma fp.u n := by
    linarith [gamma_nonneg fp.toStandardAddModel hvalid]
  calc
    |twoSumPrefix fp v k hk| = |recursiveSum fp.fl_add (k + 1) w| := by
      rw [hprefix]
    _ ≤ (1 + gamma fp.u k) * ∑ i : Fin (k + 1), |w i| := by
      simpa using hb
    _ ≤ (1 + gamma fp.u n) * ∑ i : Fin (k + 1), |w i| := by
      gcongr
    _ ≤ (1 + gamma fp.u n) * ∑ i : Fin (n + 1), |v i| := by
      exact mul_le_mul_of_nonneg_left hsum hcoef

lemma twoSumCorrection_abs_le (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (hvalid : GammaValid fp.u n) (i : Fin n) :
    |twoSumCorrection fp v i| ≤
      fp.u * ((1 + gamma fp.u n) * ∑ j : Fin (n + 1), |v j|) := by
  have hlow := fp.twoSum_low_le
    (twoSumPrefix fp v i.val (Nat.le_of_lt i.isLt))
    (v ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
  change |twoSumCorrection fp v i| ≤ _ at hlow
  rw [← twoSumPrefix_succ fp v i.isLt] at hlow
  exact le_trans hlow (mul_le_mul_of_nonneg_left
    (twoSumPrefix_abs_le fp v hvalid (i.val + 1) i.isLt)
    fp.u_nonneg)

lemma twoSumCorrections_abs_sum_le (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (hvalid : GammaValid fp.u n) :
    (∑ i : Fin n, |twoSumCorrection fp v i|) ≤
      gamma fp.u n * ∑ j : Fin (n + 1), |v j| := by
  calc
    (∑ i : Fin n, |twoSumCorrection fp v i|) ≤
        ∑ _i : Fin n,
          fp.u * ((1 + gamma fp.u n) * ∑ j : Fin (n + 1), |v j|) := by
      exact Finset.sum_le_sum fun i hi => twoSumCorrection_abs_le fp v hvalid i
    _ = (n : ℝ) *
          (fp.u * ((1 + gamma fp.u n) * ∑ j : Fin (n + 1), |v j|)) := by
      simp
    _ = ((n : ℝ) * fp.u * (1 + gamma fp.u n)) *
          ∑ j : Fin (n + 1), |v j| := by ring
    _ = gamma fp.u n * ∑ j : Fin (n + 1), |v j| := by
      rw [gamma_mul_one_add fp.u n hvalid]

lemma twoSumPrefix_add_corrections (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) : ∀ (k : ℕ) (hk : k ≤ n),
    twoSumPrefix fp v k hk +
        ∑ i : Fin k,
          twoSumCorrection fp v
            ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ =
      ∑ j : Fin (k + 1),
        v ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk)⟩
  | 0, hk => by simp [twoSumPrefix]
  | k + 1, hk => by
      have hk0 : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      have ih := twoSumPrefix_add_corrections fp v k hk0
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      have hp := twoSumPrefix_succ fp v hk
      have he := fp.twoSum_exact
        (twoSumPrefix fp v k hk0)
        (v ⟨k + 1, Nat.succ_lt_succ
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)⟩)
      have hc :
          twoSumCorrection fp v
              ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩ =
            (fp.twoSum (twoSumPrefix fp v k hk0)
              (v ⟨k + 1, Nat.succ_lt_succ
                (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)⟩)).2 := by
        rfl
      rw [hp]
      simp only [Fin.val_last, Fin.val_castSucc]
      rw [hc]
      have ih' :
          twoSumPrefix fp v k hk0 +
              ∑ i : Fin k,
                twoSumCorrection fp v
                  ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk0⟩ =
            ∑ j : Fin (k + 1),
              v ⟨j.val, Nat.lt_of_lt_of_le j.isLt
                (Nat.succ_le_succ hk0)⟩ := ih
      convert (show
        (fp.twoSum (twoSumPrefix fp v k hk0)
              (v ⟨k + 1, Nat.succ_lt_succ
                (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)⟩)).1 +
            ((∑ i : Fin k,
                twoSumCorrection fp v
                  ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk0⟩) +
             (fp.twoSum (twoSumPrefix fp v k hk0)
              (v ⟨k + 1, Nat.succ_lt_succ
                (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)⟩)).2) =
          (∑ j : Fin (k + 1),
              v ⟨j.val, Nat.lt_of_lt_of_le j.isLt
                (Nat.succ_le_succ hk0)⟩) +
            v ⟨k + 1, Nat.succ_lt_succ
              (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)⟩ by
          linarith [ih', he]) using 1 <;> simp

lemma vecSum_sum_eq (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1), vecSum fp v i) =
      ∑ i : Fin (n + 1), v i := by
  rw [Fin.sum_univ_castSucc]
  simpa [vecSum, add_comm] using
    twoSumPrefix_add_corrections fp v n (Nat.le_refl n)

lemma sum2_eq_final_add (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (hn : 0 < n) :
    sum2 fp v =
      fp.fl_add
        (recursiveSum fp.fl_add n (twoSumCorrection fp v))
        (twoSumPrefix fp v n (Nat.le_refl n)) := by
  change recursiveSum fp.fl_add (n + 1) (vecSum fp v) = _
  rw [recursiveSum]
  simp only [hn.ne', ↓reduceDIte]
  congr 1
  · apply congrArg (recursiveSum fp.fl_add n)
    funext i
    simp [vecSum]
  · simp [vecSum]

theorem p02_t1_sum2_error_bound
    (fp : ErrorFreeAddModel) (n : ℕ) (v : Fin (n + 1) → ℝ)
    (hvalid : GammaValid fp.u (n + 1)) :
    |sum2 fp v - ∑ i : Fin (n + 1), v i| ≤
      fp.u * |∑ i : Fin (n + 1), v i| +
        (gamma fp.u n) ^ 2 * ∑ i : Fin (n + 1), |v i| := by
  -- PROOF_START P02-T1-H001
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hvec : vecSum fp v = v := by
      funext i
      have hi : i = Fin.last 0 := Fin.eq_zero i
      rw [hi]
      change Fin.lastCases (twoSumPrefix fp v 0 (Nat.le_refl 0))
          (twoSumCorrection fp v) (Fin.last 0) = v (Fin.last 0)
      rw [Fin.lastCases_last]
      simp [twoSumPrefix]
    rw [show sum2 fp v = v 0 by
      simp [sum2, sumK, iteratedVecSum, recursiveSum, hvec]]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, zero_add, sub_self,
      abs_zero, zero_le, gamma, Nat.cast_zero, zero_mul, zero_div, zero_pow,
      add_zero]
    norm_num
    exact mul_nonneg fp.u_nonneg (abs_nonneg _)
  · let c : Fin n → ℝ := twoSumCorrection fp v
    let beta : ℝ := twoSumPrefix fp v n (Nat.le_refl n)
    let sigma : ℝ := recursiveSum fp.fl_add n c
    let s : ℝ := ∑ i : Fin (n + 1), v i
    let S : ℝ := ∑ i : Fin (n + 1), |v i|
    let C : ℝ := ∑ i : Fin n, |c i|
    have hvalidn : GammaValid fp.u n :=
      GammaValid.mono fp.toStandardAddModel (Nat.le_succ n) hvalid
    have hvalidpred : GammaValid fp.u (n - 1) :=
      GammaValid.mono fp.toStandardAddModel (Nat.sub_le n 1) hvalidn
    have hsigma :
        |sigma - ∑ i : Fin n, c i| ≤ gamma fp.u (n - 1) * C := by
      simpa [sigma, C, c] using
        recursiveSum_forward_error_bound fp.toStandardAddModel n c hvalidpred
    have hC : C ≤ gamma fp.u n * S := by
      simpa [C, S, c] using twoSumCorrections_abs_sum_le fp v hvalidn
    have hinv : beta + ∑ i : Fin n, c i = s := by
      simpa [beta, c, s] using
        twoSumPrefix_add_corrections fp v n (Nat.le_refl n)
    have hsum2 : sum2 fp v = fp.fl_add sigma beta := by
      simpa [sigma, beta, c] using sum2_eq_final_add fp v hn
    obtain ⟨delta, hdelta, hfl⟩ := fp.model_add sigma beta
    have hdecomp :
        (sigma + beta) * (1 + delta) - s =
          (1 + delta) * (sigma - ∑ i : Fin n, c i) + delta * s := by
      rw [← hinv]
      ring
    have hone_delta : |1 + delta| ≤ 1 + fp.u := by
      calc
        |1 + delta| ≤ |(1 : ℝ)| + |delta| := abs_add_le _ _
        _ ≤ 1 + fp.u := by simpa using add_le_add_left hdelta 1
    have hgamma_n : 0 ≤ gamma fp.u n :=
      gamma_nonneg fp.toStandardAddModel hvalidn
    have hgamma_pred : 0 ≤ gamma fp.u (n - 1) :=
      gamma_nonneg fp.toStandardAddModel hvalidpred
    have hC_nonneg : 0 ≤ C := by
      dsimp [C]
      positivity
    have hS_nonneg : 0 ≤ S := by
      dsimp [S]
      positivity
    have hfactor :
        (1 + fp.u) * gamma fp.u (n - 1) ≤ gamma fp.u n :=
      one_add_u_mul_gamma_pred_le_gamma fp.toStandardAddModel n hn hvalidn
    have hsecond :
        (1 + fp.u) * (gamma fp.u (n - 1) * C) ≤
          (gamma fp.u n) ^ 2 * S := by
      calc
        (1 + fp.u) * (gamma fp.u (n - 1) * C) =
            ((1 + fp.u) * gamma fp.u (n - 1)) * C := by ring
        _ ≤ gamma fp.u n * C :=
          mul_le_mul_of_nonneg_right hfactor hC_nonneg
        _ ≤ gamma fp.u n * (gamma fp.u n * S) :=
          mul_le_mul_of_nonneg_left hC hgamma_n
        _ = (gamma fp.u n) ^ 2 * S := by ring
    rw [hsum2, hfl, hdecomp]
    calc
      |(1 + delta) * (sigma - ∑ i : Fin n, c i) + delta * s| ≤
          |1 + delta| * |sigma - ∑ i : Fin n, c i| +
            |delta| * |s| := by
        simpa only [abs_mul] using
          abs_add_le ((1 + delta) * (sigma - ∑ i : Fin n, c i))
            (delta * s)
      _ ≤ (1 + fp.u) * |sigma - ∑ i : Fin n, c i| +
            fp.u * |s| := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hone_delta (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hdelta (abs_nonneg _))
      _ ≤ (1 + fp.u) * (gamma fp.u (n - 1) * C) +
            fp.u * |s| := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hsigma (by linarith [fp.u_nonneg]))
          le_rfl
      _ ≤ (gamma fp.u n) ^ 2 * S + fp.u * |s| :=
        add_le_add hsecond le_rfl
      _ = fp.u * |∑ i : Fin (n + 1), v i| +
            (gamma fp.u n) ^ 2 * ∑ i : Fin (n + 1), |v i| := by
        simp [s, S, add_comm]

end HighamBench
