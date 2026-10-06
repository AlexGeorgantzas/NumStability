import HighamBench.P02Definitions
import NumStability.Algorithms.Summation.Recursive.Core

namespace HighamBench

open scoped BigOperators

noncomputable def standardAddFPModel (fp : StandardAddModel) :
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
    intro x y _hy
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_sqrt := by
    intro x _hx
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩

lemma fin_prefix_sum_le_sum {N k : ℕ} (hk : k ≤ N) (f : Fin N → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    (∑ i : Fin k, f (Fin.castLE hk i)) ≤ ∑ i : Fin N, f i := by
  let e : Fin k ↪ Fin N := Fin.castLEEmb hk
  calc
    (∑ i : Fin k, f (Fin.castLE hk i)) =
        ∑ j ∈ Finset.univ.map e, f j := by
      rw [Finset.sum_map]
      rfl
    _ ≤ ∑ j ∈ Finset.univ, f j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => hf j)
    _ = ∑ i : Fin N, f i := by simp

lemma gamma_mul_one_add (u : ℝ) (n : ℕ) (h : GammaValid u n) :
    (n : ℝ) * u * (1 + gamma u n) = gamma u n := by
  unfold GammaValid at h
  have hden : 1 - (n : ℝ) * u ≠ 0 := by linarith
  unfold gamma
  field_simp [hden]
  ring

lemma twoSumPrefix_eq_fl_recursiveSum (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : k ≤ n) :
    twoSumPrefix fp v k hk =
      NumStability.fl_recursiveSum
        (standardAddFPModel fp.toStandardAddModel) (k + 1)
        (fun i : Fin (k + 1) =>
          v ⟨i.val,
            Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩) := by
  rw [NumStability.fl_recursiveSum, Fin.foldl_succ]
  simp only [standardAddFPModel, fp.fl_add_zero]
  unfold twoSumPrefix
  simp only [fp.twoSum_high]
  rfl

lemma twoSumPrefix_succ (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : k < n) :
    twoSumPrefix fp v (k + 1) (Nat.succ_le_iff.mpr hk) =
      (fp.twoSum (twoSumPrefix fp v k (Nat.le_of_lt hk))
        (v ⟨k + 1, Nat.succ_lt_succ hk⟩)).1 := by
  unfold twoSumPrefix
  rw [Fin.foldl_succ_last]
  rfl

lemma twoSumPrefix_add_corrections (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : k ≤ n) :
    twoSumPrefix fp v k hk +
        (∑ i : Fin k, twoSumCorrection fp v
          ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) =
      ∑ i : Fin (k + 1),
        v ⟨i.val,
          Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩ := by
  induction k with
  | zero =>
      simp [twoSumPrefix]
  | succ k ih =>
      have hklt : k < n := by omega
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      rw [twoSumPrefix_succ fp v k hklt]
      have hih := ih (Nat.le_of_lt hklt)
      have hexact := fp.twoSum_exact
        (twoSumPrefix fp v k (Nat.le_of_lt hklt))
        (v ⟨k + 1, Nat.succ_lt_succ hklt⟩)
      simp only [twoSumCorrection, Fin.val_castSucc, Fin.val_last] at *
      linarith

lemma vecSum_sum_eq (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) :
    ∑ i : Fin (n + 1), vecSum fp v i = ∑ i : Fin (n + 1), v i := by
  rw [Fin.sum_univ_castSucc]
  simp only [vecSum, Fin.lastCases_castSucc, Fin.lastCases_last]
  have h := twoSumPrefix_add_corrections fp v n (Nat.le_refl n)
  simpa [add_comm] using h

lemma twoSumPrefix_abs_le_global (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : k ≤ n)
    (hvalid : GammaValid fp.u n) :
    |twoSumPrefix fp v k hk| ≤
      (1 + gamma fp.u n) * ∑ i : Fin (n + 1), |v i| := by
  let afp := standardAddFPModel fp.toStandardAddModel
  have hn : NumStability.gammaValid afp n := by
    simpa [afp, standardAddFPModel, NumStability.gammaValid, GammaValid]
      using hvalid
  have hkvalid : NumStability.gammaValid afp k :=
    NumStability.gammaValid_mono afp hk hn
  let w : Fin (k + 1) → ℝ := fun i =>
    v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩
  have hrec := NumStability.recursiveSum_abs_le_one_add_gamma_mul_sum_abs
    afp (k + 1) w (by simpa using hkvalid)
  have hprefix :
      (∑ i : Fin (k + 1), |w i|) ≤
        ∑ i : Fin (n + 1), |v i| := by
    simpa [w] using
      (fin_prefix_sum_le_sum (Nat.succ_le_succ hk)
        (fun i : Fin (n + 1) => |v i|) (fun i => abs_nonneg (v i)))
  have hgamma : gamma fp.u k ≤ gamma fp.u n := by
    have h := NumStability.gamma_mono afp hk hn
    simpa [afp, standardAddFPModel, NumStability.gamma, gamma] using h
  have hgamma_nonneg : 0 ≤ gamma fp.u n := by
    have h := NumStability.gamma_nonneg afp hn
    simpa [afp, standardAddFPModel, NumStability.gamma, gamma] using h
  rw [twoSumPrefix_eq_fl_recursiveSum]
  calc
    |NumStability.fl_recursiveSum afp (k + 1) w| ≤
        (1 + gamma fp.u k) * ∑ i : Fin (k + 1), |w i| := by
      simpa [afp, standardAddFPModel, NumStability.gamma, gamma] using hrec
    _ ≤ (1 + gamma fp.u n) * ∑ i : Fin (k + 1), |w i| :=
      mul_le_mul_of_nonneg_right (by linarith) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    _ ≤ (1 + gamma fp.u n) * ∑ i : Fin (n + 1), |v i| :=
      mul_le_mul_of_nonneg_left hprefix (by linarith)

lemma twoSumCorrections_abs_le_gamma (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (hvalid : GammaValid fp.u n) :
    (∑ i : Fin n, |twoSumCorrection fp v i|) ≤
      gamma fp.u n * ∑ i : Fin (n + 1), |v i| := by
  have hterm : ∀ i : Fin n,
      |twoSumCorrection fp v i| ≤
        fp.u * ((1 + gamma fp.u n) * ∑ j : Fin (n + 1), |v j|) := by
    intro i
    have hp := twoSumPrefix_abs_le_global fp v (i.val + 1)
      (Nat.succ_le_iff.mpr i.isLt) hvalid
    calc
      |twoSumCorrection fp v i| ≤
          fp.u *
            |(fp.twoSum
              (twoSumPrefix fp v i.val (Nat.le_of_lt i.isLt))
              (v ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)).1| := by
        exact fp.twoSum_low_le _ _
      _ = fp.u *
          |twoSumPrefix fp v (i.val + 1)
            (Nat.succ_le_iff.mpr i.isLt)| := by
        rw [twoSumPrefix_succ fp v i.val i.isLt]
      _ ≤ fp.u *
          ((1 + gamma fp.u n) * ∑ j : Fin (n + 1), |v j|) :=
        mul_le_mul_of_nonneg_left hp fp.u_nonneg
  calc
    (∑ i : Fin n, |twoSumCorrection fp v i|) ≤
        ∑ _i : Fin n,
          fp.u * ((1 + gamma fp.u n) * ∑ j : Fin (n + 1), |v j|) :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = (n : ℝ) *
          (fp.u * ((1 + gamma fp.u n) * ∑ j : Fin (n + 1), |v j|)) := by
      simp
    _ = ((n : ℝ) * fp.u * (1 + gamma fp.u n)) *
          ∑ j : Fin (n + 1), |v j| := by ring
    _ = gamma fp.u n * ∑ j : Fin (n + 1), |v j| := by
      rw [gamma_mul_one_add fp.u n hvalid]

lemma recursiveSum_eq_fl_recursiveSum (fp : StandardAddModel) :
    ∀ (m : ℕ) (w : Fin m → ℝ),
      recursiveSum fp.fl_add m w =
        NumStability.fl_recursiveSum (standardAddFPModel fp) m w
  | 0, w => by simp [recursiveSum, NumStability.fl_recursiveSum]
  | m + 1, w => by
      rw [NumStability.fl_recursiveSum, Fin.foldl_succ_last]
      by_cases hm : m = 0
      · subst m
        simp [recursiveSum, standardAddFPModel, fp.fl_add_zero,
          NumStability.fl_recursiveSum]
      · rw [recursiveSum]
        simp only [hm, ↓reduceDIte, standardAddFPModel]
        rw [recursiveSum_eq_fl_recursiveSum fp m
          (fun i : Fin m => w i.castSucc)]
        rfl

lemma one_add_u_mul_gamma_le_gamma_succ (fp : StandardAddModel) (m : ℕ)
    (hvalid : GammaValid fp.u (m + 1)) :
    (1 + fp.u) * gamma fp.u m ≤ gamma fp.u (m + 1) := by
  let afp := standardAddFPModel fp
  have hv : NumStability.gammaValid afp (m + 1) := by
    simpa [afp, standardAddFPModel, NumStability.gammaValid, GammaValid]
      using hvalid
  have hv1 : NumStability.gammaValid afp 1 :=
    NumStability.gammaValid_mono afp (by omega) hv
  have hvm : NumStability.gammaValid afp m :=
    NumStability.gammaValid_mono afp (by omega) hv
  have hu : fp.u ≤ gamma fp.u 1 := by
    have h := NumStability.u_le_gamma afp (by omega : 0 < 1) hv1
    simpa [afp, standardAddFPModel, NumStability.gamma, gamma] using h
  have hg1 : 0 ≤ gamma fp.u 1 := by
    have h := NumStability.gamma_nonneg afp hv1
    simpa [afp, standardAddFPModel, NumStability.gamma, gamma] using h
  have hgm : 0 ≤ gamma fp.u m := by
    have h := NumStability.gamma_nonneg afp hvm
    simpa [afp, standardAddFPModel, NumStability.gamma, gamma] using h
  have hmul : fp.u * gamma fp.u m ≤ gamma fp.u 1 * gamma fp.u m :=
    mul_le_mul_of_nonneg_right hu hgm
  have hsum :
      gamma fp.u 1 + gamma fp.u m + gamma fp.u 1 * gamma fp.u m ≤
        gamma fp.u (m + 1) := by
    have h := NumStability.gamma_sum_le afp 1 m (by simpa [Nat.add_comm] using hv)
    simpa [afp, standardAddFPModel, NumStability.gamma, gamma, Nat.add_comm]
      using h
  calc
    (1 + fp.u) * gamma fp.u m =
        gamma fp.u m + fp.u * gamma fp.u m := by ring
    _ ≤ gamma fp.u m + gamma fp.u 1 * gamma fp.u m :=
      add_le_add_right hmul _
    _ ≤ gamma fp.u 1 + gamma fp.u m + gamma fp.u 1 * gamma fp.u m := by
      linarith
    _ ≤ gamma fp.u (m + 1) := hsum

theorem p02_t1_sum2_error_bound
    (fp : ErrorFreeAddModel) (n : ℕ) (v : Fin (n + 1) → ℝ)
    (hvalid : GammaValid fp.u (n + 1)) :
    |sum2 fp v - ∑ i : Fin (n + 1), v i| ≤
      fp.u * |∑ i : Fin (n + 1), v i| +
        (gamma fp.u n) ^ 2 * ∑ i : Fin (n + 1), |v i| := by
  -- PROOF_START P02-T1-H001
  cases n with
  | zero =>
      have hv : vecSum fp v = v := by
        funext i
        unfold vecSum
        simp only [twoSumPrefix, Fin.foldl_zero]
        have hi : i = Fin.last 0 := by apply Fin.ext; simp
        exact hi ▸ Fin.lastCases_last
      simp [sum2, sumK, iteratedVecSum, recursiveSum, hv, gamma,
        fp.u_nonneg]
      exact mul_nonneg fp.u_nonneg (abs_nonneg _)
  | succ m =>
      let q : Fin (m + 1) → ℝ := fun i => twoSumCorrection fp v i
      let high : ℝ := twoSumPrefix fp v (m + 1) (Nat.le_refl (m + 1))
      let corr : ℝ := recursiveSum fp.fl_add (m + 1) q
      let s : ℝ := ∑ i : Fin (m + 2), v i
      let S : ℝ := ∑ i : Fin (m + 2), |v i|
      have hrun : sum2 fp v = fp.fl_add corr high := by
        change recursiveSum fp.fl_add ((m + 1) + 1) (vecSum fp v) = _
        rw [recursiveSum]
        simp only [Nat.succ_ne_zero, ↓reduceDIte]
        simp only [vecSum, Fin.lastCases_castSucc, Fin.lastCases_last,
          q, high, corr]
      have hvalidN : GammaValid fp.u (m + 1) := by
        unfold GammaValid at hvalid ⊢
        have hm : (m + 1 : ℕ) ≤ m + 1 + 1 := by omega
        have hmR : ((m + 1 : ℕ) : ℝ) ≤ ((m + 1 + 1 : ℕ) : ℝ) := by
          exact_mod_cast hm
        exact lt_of_le_of_lt
          (mul_le_mul_of_nonneg_right hmR fp.u_nonneg) hvalid
      have hvalidm : GammaValid fp.u m := by
        unfold GammaValid at hvalidN ⊢
        have hm : (m : ℕ) ≤ m + 1 := Nat.le_succ m
        have hmR : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hm
        exact lt_of_le_of_lt
          (mul_le_mul_of_nonneg_right hmR fp.u_nonneg) hvalidN
      have hq : (∑ i : Fin (m + 1), |q i|) ≤ gamma fp.u (m + 1) * S := by
        simpa [q, S] using twoSumCorrections_abs_le_gamma fp v hvalidN
      have hcorr :
          |corr - ∑ i : Fin (m + 1), q i| ≤
            gamma fp.u m * ∑ i : Fin (m + 1), |q i| := by
        let afp := standardAddFPModel fp.toStandardAddModel
        have hm : NumStability.gammaValid afp m := by
          simpa [afp, standardAddFPModel, NumStability.gammaValid, GammaValid]
            using hvalidm
        have hr := NumStability.recursiveSum_forward_error_bound
          afp (m + 1) q (by simpa using hm)
        dsimp only [corr]
        rw [recursiveSum_eq_fl_recursiveSum]
        simpa [afp, standardAddFPModel, NumStability.gamma, gamma] using hr
      have hexact : high + ∑ i : Fin (m + 1), q i = s := by
        simpa [high, q, s] using
          (twoSumPrefix_add_corrections fp v (m + 1) (Nat.le_refl (m + 1)))
      have hgammaN : 0 ≤ gamma fp.u (m + 1) := by
        let afp := standardAddFPModel fp.toStandardAddModel
        have hv : NumStability.gammaValid afp (m + 1) := by
          simpa [afp, standardAddFPModel, NumStability.gammaValid, GammaValid]
            using hvalidN
        have hg := NumStability.gamma_nonneg afp hv
        simpa [afp, standardAddFPModel, NumStability.gamma, gamma] using hg
      have hq_nonneg : 0 ≤ ∑ i : Fin (m + 1), |q i| :=
        Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hstep :
          (1 + fp.u) * gamma fp.u m ≤ gamma fp.u (m + 1) :=
        one_add_u_mul_gamma_le_gamma_succ fp.toStandardAddModel m hvalidN
      have hsecond :
          (1 + fp.u) *
              (gamma fp.u m * ∑ i : Fin (m + 1), |q i|) ≤
            (gamma fp.u (m + 1)) ^ 2 * S := by
        calc
          (1 + fp.u) *
                (gamma fp.u m * ∑ i : Fin (m + 1), |q i|) =
              ((1 + fp.u) * gamma fp.u m) *
                ∑ i : Fin (m + 1), |q i| := by ring
          _ ≤ gamma fp.u (m + 1) *
                ∑ i : Fin (m + 1), |q i| :=
            mul_le_mul_of_nonneg_right hstep hq_nonneg
          _ ≤ gamma fp.u (m + 1) *
                (gamma fp.u (m + 1) * S) :=
            mul_le_mul_of_nonneg_left hq hgammaN
          _ = (gamma fp.u (m + 1)) ^ 2 * S := by ring
      obtain ⟨δ, hδ, hfl⟩ := fp.model_add corr high
      have h1δ : |1 + δ| ≤ 1 + fp.u := by
        calc
          |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
          _ = 1 + |δ| := by norm_num
          _ ≤ 1 + fp.u := by linarith
      have herrid :
          fp.fl_add corr high - s =
            (1 + δ) * (corr - ∑ i : Fin (m + 1), q i) + δ * s := by
        rw [hfl]
        linear_combination (1 + δ) * hexact
      change |sum2 fp v - s| ≤
        fp.u * |s| + (gamma fp.u (m + 1)) ^ 2 * S
      rw [hrun, herrid]
      calc
        |(1 + δ) * (corr - ∑ i : Fin (m + 1), q i) + δ * s| ≤
            |1 + δ| * |corr - ∑ i : Fin (m + 1), q i| + |δ| * |s| := by
          simpa only [abs_mul] using
            (abs_add_le
              ((1 + δ) * (corr - ∑ i : Fin (m + 1), q i)) (δ * s))
        _ ≤ (1 + fp.u) *
              (gamma fp.u m * ∑ i : Fin (m + 1), |q i|) + fp.u * |s| := by
          exact add_le_add
            (mul_le_mul h1δ hcorr (abs_nonneg _) (by linarith [fp.u_nonneg]))
            (mul_le_mul_of_nonneg_right hδ (abs_nonneg s))
        _ ≤ fp.u * |s| + (gamma fp.u (m + 1)) ^ 2 * S := by
          linarith

end HighamBench
