import HighamBench.P02Definitions
import NumStability.Algorithms.Summation.Recursive.Core

namespace HighamBench

open scoped BigOperators

private noncomputable def toFPModel (fp : StandardAddModel) :
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
    intro x y _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_sqrt := by
    intro x _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩

private lemma gamma_toFPModel (fp : StandardAddModel) (k : ℕ) :
    NumStability.gamma (toFPModel fp) k = gamma fp.u k := by
  rfl

private lemma gammaValid_toFPModel (fp : StandardAddModel) (k : ℕ) :
    NumStability.gammaValid (toFPModel fp) k ↔ GammaValid fp.u k := by
  rfl

private lemma recursiveSum_eq_fl_recursiveSum (fp : StandardAddModel) :
    ∀ (m : ℕ) (x : Fin m → ℝ),
      recursiveSum fp.fl_add m x =
        NumStability.fl_recursiveSum (toFPModel fp) m x := by
  intro m
  induction m with
  | zero =>
      intro x
      simp [recursiveSum, NumStability.fl_recursiveSum]
  | succ m ih =>
      intro x
      change recursiveSum fp.fl_add (m + 1) x =
        Fin.foldl (m + 1) (fun acc i => fp.fl_add acc (x i)) 0
      rw [Fin.foldl_succ_last]
      change recursiveSum fp.fl_add (m + 1) x =
        fp.fl_add
          (NumStability.fl_recursiveSum (toFPModel fp) m
            (fun i : Fin m => x i.castSucc))
          (x (Fin.last m))
      by_cases hm : m = 0
      · subst m
        simp [recursiveSum, NumStability.fl_recursiveSum, fp.fl_add_zero]
      · rw [recursiveSum, dif_neg hm, ih]

private lemma twoSumPrefix_eq_recursiveSum (fp : ErrorFreeAddModel)
    {n : ℕ} (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : k ≤ n) :
    twoSumPrefix fp v k hk =
      recursiveSum fp.fl_add (k + 1)
        (fun i : Fin (k + 1) =>
          v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩) := by
  rw [recursiveSum_eq_fl_recursiveSum]
  unfold NumStability.fl_recursiveSum twoSumPrefix
  rw [Fin.foldl_succ]
  simp only [toFPModel, fp.fl_add_zero]
  congr 1
  funext s i
  rw [fp.twoSum_high]
  congr 2

private lemma prefix_abs_sum_le_total {N k : ℕ} (hk : k ≤ N)
    (x : Fin N → ℝ) :
    (∑ i : Fin k,
        |x ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩|) ≤
      ∑ i : Fin N, |x i| := by
  classical
  let e : Fin k → Fin N :=
    fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    simpa [e] using congrArg (fun z : Fin N => z.val) hij
  calc
    (∑ i : Fin k, |x ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩|) =
        ∑ i : Fin k, |x (e i)| := by rfl
    _ = ∑ j ∈ Finset.image e Finset.univ, |x j| := by
      symm
      exact Finset.sum_image (fun _ _ _ _ hij => he hij)
    _ ≤ ∑ j : Fin N, |x j| :=
      Finset.sum_le_univ_sum_of_nonneg (fun j => abs_nonneg (x j))

private lemma twoSumPrefix_abs_le (fp : ErrorFreeAddModel)
    {n : ℕ} (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : k ≤ n)
    (hvalid : GammaValid fp.u n) :
    |twoSumPrefix fp v k hk| ≤
      (1 + gamma fp.u n) * ∑ i : Fin (n + 1), |v i| := by
  let pref : Fin (k + 1) → ℝ :=
    fun i => v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩
  have hvalid' : NumStability.gammaValid (toFPModel fp.toStandardAddModel) k :=
    NumStability.gammaValid_mono _ hk (gammaValid_toFPModel _ n |>.2 hvalid)
  have hrec :=
    NumStability.recursiveSum_abs_le_one_add_gamma_mul_sum_abs
      (toFPModel fp.toStandardAddModel) (k + 1) pref (by simpa using hvalid')
  have hprefix :
      |twoSumPrefix fp v k hk| ≤
        (1 + gamma fp.u k) * ∑ i : Fin (k + 1), |pref i| := by
    rw [twoSumPrefix_eq_recursiveSum, recursiveSum_eq_fl_recursiveSum]
    simpa [gamma_toFPModel] using hrec
  have hgamma_le : gamma fp.u k ≤ gamma fp.u n := by
    simpa [gamma_toFPModel] using
      NumStability.gamma_mono (toFPModel fp.toStandardAddModel) hk
        (gammaValid_toFPModel _ n |>.2 hvalid)
  have hpref_nonneg : 0 ≤ ∑ i : Fin (k + 1), |pref i| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg (pref i))
  have htotal_nonneg : 0 ≤ ∑ i : Fin (n + 1), |v i| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg (v i))
  have hpref_total :
      (∑ i : Fin (k + 1), |pref i|) ≤
        ∑ i : Fin (n + 1), |v i| := by
    simpa [pref] using
      prefix_abs_sum_le_total (Nat.succ_le_succ hk) v
  have hfactor_nonneg : 0 ≤ 1 + gamma fp.u n := by
    have hg : 0 ≤ gamma fp.u n := by
      simpa [gamma_toFPModel] using
        NumStability.gamma_nonneg (toFPModel fp.toStandardAddModel)
          (gammaValid_toFPModel _ n |>.2 hvalid)
    linarith
  calc
    |twoSumPrefix fp v k hk|
        ≤ (1 + gamma fp.u k) * ∑ i : Fin (k + 1), |pref i| := hprefix
    _ ≤ (1 + gamma fp.u n) * ∑ i : Fin (k + 1), |pref i| := by
      exact mul_le_mul_of_nonneg_right (by linarith) hpref_nonneg
    _ ≤ (1 + gamma fp.u n) * ∑ i : Fin (n + 1), |v i| := by
      exact mul_le_mul_of_nonneg_left hpref_total hfactor_nonneg

private lemma twoSumPrefix_succ (fp : ErrorFreeAddModel)
    {n k : ℕ} (v : Fin (n + 1) → ℝ) (hk : k + 1 ≤ n) :
    twoSumPrefix fp v (k + 1) hk =
      (fp.twoSum
        (twoSumPrefix fp v k (Nat.le_trans (Nat.le_succ k) hk))
        (v ⟨k + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)⟩)).1 := by
  unfold twoSumPrefix
  rw [Fin.foldl_succ_last]
  congr 3

private lemma twoSumCorrection_abs_sum_le (fp : ErrorFreeAddModel)
    {n : ℕ} (v : Fin (n + 1) → ℝ)
    (hvalid : GammaValid fp.u n) :
    (∑ i : Fin n, |twoSumCorrection fp v i|) ≤
      gamma fp.u n * ∑ i : Fin (n + 1), |v i| := by
  let S : ℝ := ∑ i : Fin (n + 1), |v i|
  have hpoint : ∀ i : Fin n,
      |twoSumCorrection fp v i| ≤ fp.u * ((1 + gamma fp.u n) * S) := by
    intro i
    have hk : i.val + 1 ≤ n := i.isLt
    have hstep := twoSumPrefix_succ fp v hk
    have hlow := fp.twoSum_low_le
      (twoSumPrefix fp v i.val (Nat.le_of_lt i.isLt))
      (v ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    have hprefix := twoSumPrefix_abs_le fp v (i.val + 1) hk hvalid
    unfold twoSumCorrection
    calc
      |(fp.twoSum
          (twoSumPrefix fp v i.val (Nat.le_of_lt i.isLt))
          (v ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)).2|
          ≤ fp.u *
              |(fp.twoSum
                (twoSumPrefix fp v i.val (Nat.le_of_lt i.isLt))
                (v ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)).1| := hlow
      _ = fp.u * |twoSumPrefix fp v (i.val + 1) hk| := by
        rw [hstep]
      _ ≤ fp.u * ((1 + gamma fp.u n) * S) := by
        exact mul_le_mul_of_nonneg_left (by simpa [S] using hprefix) fp.u_nonneg
  have hsum :
      (∑ i : Fin n, |twoSumCorrection fp v i|) ≤
        ∑ _i : Fin n, fp.u * ((1 + gamma fp.u n) * S) := by
    exact Finset.sum_le_sum (fun i _ => hpoint i)
  have hden : 1 - (n : ℝ) * fp.u ≠ 0 := by
    unfold GammaValid at hvalid
    linarith
  have hid : (n : ℝ) * fp.u * (1 + gamma fp.u n) = gamma fp.u n := by
    unfold gamma
    field_simp [hden]
    ring
  calc
    (∑ i : Fin n, |twoSumCorrection fp v i|)
        ≤ ∑ _i : Fin n, fp.u * ((1 + gamma fp.u n) * S) := hsum
    _ = (n : ℝ) * (fp.u * ((1 + gamma fp.u n) * S)) := by
      simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
    _ = ((n : ℝ) * fp.u * (1 + gamma fp.u n)) * S := by ring
    _ = gamma fp.u n * ∑ i : Fin (n + 1), |v i| := by
      rw [hid]

private lemma twoSumPrefix_add_corrections_eq_sum (fp : ErrorFreeAddModel)
    {n : ℕ} (v : Fin (n + 1) → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n),
      twoSumPrefix fp v k hk +
          ∑ i : Fin k,
            twoSumCorrection fp v
              ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ =
        ∑ i : Fin (k + 1),
          v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩ := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp [twoSumPrefix]
  | succ k ih =>
      intro hk
      have hk0 : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      have hih := ih hk0
      let a := twoSumPrefix fp v k hk0
      let b := v ⟨k + 1, Nat.succ_lt_succ
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)⟩
      have hcorr_sum :
          (∑ i : Fin (k + 1),
              twoSumCorrection fp v
                ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) =
            (∑ i : Fin k,
              twoSumCorrection fp v
                ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk0⟩) +
              (fp.twoSum a b).2 := by
        rw [Fin.sum_univ_castSucc]
        congr 1
      have hsource_sum :
          (∑ i : Fin (k + 2),
              v ⟨i.val,
                Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩) =
            (∑ i : Fin (k + 1),
              v ⟨i.val, Nat.lt_of_lt_of_le i.isLt
                (Nat.succ_le_succ hk0)⟩) + b := by
        rw [Fin.sum_univ_castSucc]
        congr 1
      rw [hcorr_sum, hsource_sum, twoSumPrefix_succ fp v hk]
      have hexact := fp.twoSum_exact
        (twoSumPrefix fp v k hk0)
        (v ⟨k + 1, Nat.succ_lt_succ
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)⟩)
      change (fp.twoSum a b).1 +
          ((∑ i : Fin k,
            twoSumCorrection fp v
              ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk0⟩) +
            (fp.twoSum a b).2) =
        (∑ i : Fin (k + 1),
          v ⟨i.val, Nat.lt_of_lt_of_le i.isLt
            (Nat.succ_le_succ hk0)⟩) + b
      change (fp.twoSum a b).1 + (fp.twoSum a b).2 = a + b at hexact
      change a +
          ∑ i : Fin k,
            twoSumCorrection fp v
              ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk0⟩ =
        ∑ i : Fin (k + 1),
          v ⟨i.val, Nat.lt_of_lt_of_le i.isLt
            (Nat.succ_le_succ hk0)⟩ at hih
      linarith

private lemma vecSum_castSucc (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (i : Fin n) :
    vecSum fp v i.castSucc = twoSumCorrection fp v i := by
  simp [vecSum]

private lemma vecSum_last (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) :
    vecSum fp v (Fin.last n) = twoSumPrefix fp v n (Nat.le_refl n) := by
  simp [vecSum]

private lemma vecSum_sum_eq (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) :
    ∑ i : Fin (n + 1), vecSum fp v i = ∑ i : Fin (n + 1), v i := by
  rw [Fin.sum_univ_castSucc]
  simp_rw [vecSum_castSucc, vecSum_last]
  simpa [add_comm] using
    twoSumPrefix_add_corrections_eq_sum fp v n (Nat.le_refl n)

theorem p02_t1_sum2_error_bound
    (fp : ErrorFreeAddModel) (n : ℕ) (v : Fin (n + 1) → ℝ)
    (hvalid : GammaValid fp.u (n + 1)) :
    |sum2 fp v - ∑ i : Fin (n + 1), v i| ≤
      fp.u * |∑ i : Fin (n + 1), v i| +
        (gamma fp.u n) ^ 2 * ∑ i : Fin (n + 1), |v i| := by
  -- PROOF_START P02-T1-H001
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hzero : sum2 fp v = v 0 := by
      change recursiveSum fp.fl_add 1 (vecSum fp v) = v 0
      rw [show recursiveSum fp.fl_add 1 (vecSum fp v) = vecSum fp v 0 by
        simp [recursiveSum]]
      have hi : (0 : Fin 1) = Fin.last 0 := Subsingleton.elim _ _
      rw [hi, vecSum_last]
      simp [twoSumPrefix]
    rw [hzero]
    simp [gamma]
    exact mul_nonneg fp.u_nonneg (abs_nonneg (v 0))
  · let c : Fin n → ℝ := fun i => twoSumCorrection fp v i
    let p : ℝ := twoSumPrefix fp v n (Nat.le_refl n)
    let σ : ℝ := recursiveSum fp.fl_add n c
    let s : ℝ := ∑ i : Fin (n + 1), v i
    let S : ℝ := ∑ i : Fin (n + 1), |v i|
    have hvalid_n : GammaValid fp.u n := by
      unfold GammaValid at hvalid ⊢
      have hcast : (n : ℝ) ≤ (n + 1 : ℕ) := by norm_num
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcast fp.u_nonneg) hvalid
    have hvalid_pred :
        NumStability.gammaValid (toFPModel fp.toStandardAddModel) (n - 1) := by
      exact NumStability.gammaValid_mono
        (toFPModel fp.toStandardAddModel)
        (show n - 1 ≤ n + 1 by omega)
        (gammaValid_toFPModel _ (n + 1) |>.2 hvalid)
    have hsum2 : sum2 fp v = fp.fl_add σ p := by
      change recursiveSum fp.fl_add (n + 1) (vecSum fp v) = fp.fl_add σ p
      rw [recursiveSum, dif_neg (Nat.ne_of_gt hn)]
      congr 1
      · dsimp [σ, c]
        congr 1
        funext i
        exact vecSum_castSucc fp v i
      · exact vecSum_last fp v
    have hinvariant : p + ∑ i : Fin n, c i = s := by
      dsimp [p, c, s]
      simpa using
        twoSumPrefix_add_corrections_eq_sum fp v n (Nat.le_refl n)
    have hrecursive :
        |σ - ∑ i : Fin n, c i| ≤
          gamma fp.u (n - 1) * ∑ i : Fin n, |c i| := by
      have h := NumStability.recursiveSum_forward_error_bound
        (toFPModel fp.toStandardAddModel) n c hvalid_pred
      dsimp [σ]
      rw [recursiveSum_eq_fl_recursiveSum]
      simpa [gamma_toFPModel] using h
    have hcorrection :
        (∑ i : Fin n, |c i|) ≤ gamma fp.u n * S := by
      simpa [c, S] using twoSumCorrection_abs_sum_le fp v hvalid_n
    have hgamma_pred_nonneg : 0 ≤ gamma fp.u (n - 1) := by
      simpa [gamma_toFPModel] using
        NumStability.gamma_nonneg (toFPModel fp.toStandardAddModel) hvalid_pred
    have hgamma_n_nonneg : 0 ≤ gamma fp.u n := by
      simpa [gamma_toFPModel] using
        NumStability.gamma_nonneg (toFPModel fp.toStandardAddModel)
          (gammaValid_toFPModel _ n |>.2 hvalid_n)
    have hS_nonneg : 0 ≤ S := by
      dsimp [S]
      exact Finset.sum_nonneg (fun i _ => abs_nonneg (v i))
    have hgamma_step :
        (1 + fp.u) * gamma fp.u (n - 1) ≤ gamma fp.u n := by
      let fpm := toFPModel fp.toStandardAddModel
      have hvalid_one : NumStability.gammaValid fpm 1 :=
        NumStability.gammaValid_mono fpm (by omega)
          (gammaValid_toFPModel _ n |>.2 hvalid_n)
      have hu : fp.u ≤ NumStability.gamma fpm 1 := by
        simpa [fpm, toFPModel] using
          NumStability.u_le_gamma fpm (k := 1) (by omega) hvalid_one
      have hsum := NumStability.gamma_sum_le fpm (n - 1) 1 (by
        simpa [Nat.sub_add_cancel hn] using
          (gammaValid_toFPModel _ n |>.2 hvalid_n))
      have hg1 : 0 ≤ NumStability.gamma fpm 1 :=
        NumStability.gamma_nonneg fpm hvalid_one
      have hmul :
          gamma fp.u (n - 1) * fp.u ≤
            gamma fp.u (n - 1) * NumStability.gamma fpm 1 :=
        mul_le_mul_of_nonneg_left hu hgamma_pred_nonneg
      have hbase :
          gamma fp.u (n - 1) + gamma fp.u (n - 1) * fp.u ≤
            gamma fp.u n := by
        have hsum' :
            gamma fp.u (n - 1) + NumStability.gamma fpm 1 +
                gamma fp.u (n - 1) * NumStability.gamma fpm 1 ≤
              gamma fp.u n := by
          simpa [fpm, gamma_toFPModel, Nat.sub_add_cancel hn] using hsum
        linarith
      calc
        (1 + fp.u) * gamma fp.u (n - 1) =
            gamma fp.u (n - 1) + gamma fp.u (n - 1) * fp.u := by ring
        _ ≤ gamma fp.u n := hbase
    obtain ⟨δ, hδ, hfl⟩ := fp.model_add σ p
    have honeδ : |1 + δ| ≤ 1 + fp.u := by
      calc
        |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
        _ ≤ 1 + fp.u := by norm_num; linarith
    have honeu_nonneg : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
    have hrec_scaled :
        |σ - ∑ i : Fin n, c i| ≤
          gamma fp.u (n - 1) * (gamma fp.u n * S) := by
      exact hrecursive.trans
        (mul_le_mul_of_nonneg_left hcorrection hgamma_pred_nonneg)
    have hmain :
        |1 + δ| * |σ - ∑ i : Fin n, c i| ≤
          (gamma fp.u n) ^ 2 * S := by
      calc
        |1 + δ| * |σ - ∑ i : Fin n, c i|
            ≤ (1 + fp.u) *
                (gamma fp.u (n - 1) * (gamma fp.u n * S)) := by
              exact mul_le_mul honeδ hrec_scaled (abs_nonneg _)
                honeu_nonneg
        _ = ((1 + fp.u) * gamma fp.u (n - 1)) *
              (gamma fp.u n * S) := by ring
        _ ≤ gamma fp.u n * (gamma fp.u n * S) := by
              exact mul_le_mul_of_nonneg_right hgamma_step
                (mul_nonneg hgamma_n_nonneg hS_nonneg)
        _ = (gamma fp.u n) ^ 2 * S := by ring
    have herr :
        sum2 fp v - s =
          (1 + δ) * (σ - ∑ i : Fin n, c i) + δ * s := by
      rw [hsum2, hfl, ← hinvariant]
      ring
    rw [show (∑ i : Fin (n + 1), v i) = s by rfl,
      show (∑ i : Fin (n + 1), |v i|) = S by rfl, herr]
    calc
      |(1 + δ) * (σ - ∑ i : Fin n, c i) + δ * s|
          ≤ |(1 + δ) * (σ - ∑ i : Fin n, c i)| + |δ * s| :=
            abs_add_le _ _
      _ = |1 + δ| * |σ - ∑ i : Fin n, c i| + |δ| * |s| := by
            rw [abs_mul, abs_mul]
      _ ≤ (gamma fp.u n) ^ 2 * S + fp.u * |s| :=
            add_le_add hmain
              (mul_le_mul_of_nonneg_right hδ (abs_nonneg s))
      _ = fp.u * |s| + (gamma fp.u n) ^ 2 * S := by ring

end HighamBench
