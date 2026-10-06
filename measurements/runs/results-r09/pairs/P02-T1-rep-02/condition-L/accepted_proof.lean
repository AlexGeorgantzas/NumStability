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
    intro x y _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_sqrt := by
    intro x _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩

lemma gamma_standardAddFPModel (fp : StandardAddModel) (k : ℕ) :
    NumStability.gamma (standardAddFPModel fp) k = gamma fp.u k := by
  rfl

lemma gammaValid_standardAddFPModel (fp : StandardAddModel) (k : ℕ) :
    NumStability.gammaValid (standardAddFPModel fp) k ↔ GammaValid fp.u k := by
  rfl

lemma recursiveSum_eq_fl_recursiveSum (fp : StandardAddModel) :
    ∀ (k : ℕ) (w : Fin k → ℝ),
      recursiveSum fp.fl_add k w =
        NumStability.fl_recursiveSum (standardAddFPModel fp) k w := by
  intro k
  induction k with
  | zero => simp [recursiveSum, NumStability.fl_recursiveSum]
  | succ k ih =>
      intro w
      by_cases hk : k = 0
      · subst k
        simp only [recursiveSum, dif_pos rfl, NumStability.fl_recursiveSum,
          Fin.foldl_succ, Fin.foldl_zero]
        change w 0 = fp.fl_add 0 (w 0)
        exact (fp.fl_add_zero _).symm
      · rw [recursiveSum, dif_neg hk, ih]
        unfold NumStability.fl_recursiveSum
        rw [Fin.foldl_succ_last]
        rfl

lemma twoSumPrefix_eq_recursiveSum (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : k ≤ n) :
    twoSumPrefix fp v k hk =
      recursiveSum fp.fl_add (k + 1)
        (fun j => v ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk)⟩) := by
  rw [recursiveSum_eq_fl_recursiveSum]
  unfold NumStability.fl_recursiveSum twoSumPrefix
  rw [Fin.foldl_succ]
  simp only [standardAddFPModel, fp.fl_add_zero]
  congr 1
  funext s i
  rw [fp.twoSum_high]
  congr 2

lemma twoSumPrefix_succ (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : k + 1 ≤ n) :
    twoSumPrefix fp v (k + 1) hk =
      (fp.twoSum
        (twoSumPrefix fp v k (Nat.le_trans (Nat.le_succ k) hk))
        (v ⟨k + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)⟩)).1 := by
  unfold twoSumPrefix
  rw [Fin.foldl_succ_last]
  rfl

lemma sum_abs_castLE_le {m n : ℕ} (h : m ≤ n) (v : Fin n → ℝ) :
    ∑ i : Fin m, |v (Fin.castLE h i)| ≤ ∑ i : Fin n, |v i| := by
  let e : Fin m ↪ Fin n := ⟨Fin.castLE h, Fin.castLE_injective h⟩
  calc
    ∑ i : Fin m, |v (Fin.castLE h i)| =
        ∑ j ∈ Finset.univ.map e, |v j| := by
          rw [Finset.sum_map]
          rfl
    _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin n)), |v j| := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro i _ _
          exact abs_nonneg _
    _ = ∑ i : Fin n, |v i| := by simp

lemma twoSumPrefix_add_corrections (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n),
      twoSumPrefix fp v k hk +
          ∑ i : Fin k,
            (fp.twoSum
              (twoSumPrefix fp v i.val
                (Nat.le_trans (Nat.le_of_lt i.isLt) hk))
              (v ⟨i.val + 1,
                Nat.succ_lt_succ (Nat.lt_of_lt_of_le i.isLt hk)⟩)).2 =
        v ⟨0, Nat.succ_pos n⟩ +
          ∑ i : Fin k,
            v ⟨i.val + 1,
              Nat.succ_lt_succ (Nat.lt_of_lt_of_le i.isLt hk)⟩ := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp [twoSumPrefix]
  | succ k ih =>
      intro hk
      have hk0 : k ≤ n := by omega
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      rw [twoSumPrefix_succ fp v k hk]
      have hex := fp.twoSum_exact
        (twoSumPrefix fp v k hk0)
        (v ⟨k + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)⟩)
      change
        (fp.twoSum
            (twoSumPrefix fp v k hk0)
            (v ⟨k + 1, _⟩)).1 +
          ((∑ i : Fin k,
              (fp.twoSum
                (twoSumPrefix fp v i.val
                  (Nat.le_trans (Nat.le_of_lt i.isLt) hk0))
                (v ⟨i.val + 1, _⟩)).2) +
            (fp.twoSum
              (twoSumPrefix fp v k hk0)
              (v ⟨k + 1, _⟩)).2) =
          v ⟨0, Nat.succ_pos n⟩ +
            ((∑ i : Fin k,
                v ⟨i.val + 1,
                  Nat.succ_lt_succ (Nat.lt_of_lt_of_le i.isLt hk0)⟩) +
              v ⟨k + 1, _⟩)
      linarith [hex, ih hk0]

lemma vecSum_sum_eq (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) :
    ∑ i : Fin (n + 1), vecSum fp v i = ∑ i : Fin (n + 1), v i := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  simp only [vecSum, Fin.lastCases_castSucc, Fin.lastCases_last]
  change
    (∑ i : Fin n, twoSumCorrection fp v i) +
        twoSumPrefix fp v n (Nat.le_refl n) =
      v ⟨0, Nat.succ_pos n⟩ + ∑ i : Fin n, v i.succ
  have h := twoSumPrefix_add_corrections fp v n (Nat.le_refl n)
  unfold twoSumCorrection at *
  have h' :
      twoSumPrefix fp v n (Nat.le_refl n) +
          ∑ i : Fin n,
            (fp.twoSum
              (twoSumPrefix fp v i.val (Nat.le_of_lt i.isLt))
              (v i.succ)).2 =
        v ⟨0, Nat.succ_pos n⟩ + ∑ i : Fin n, v i.succ := by
    convert h using 1 <;> simp [Fin.succ]
  rw [add_comm]
  convert h' using 1 <;> simp [Fin.succ]

lemma recursiveSum_forward_error_bound_standard (fp : StandardAddModel)
    (k : ℕ) (w : Fin k → ℝ) (hvalid : GammaValid fp.u (k - 1)) :
    |recursiveSum fp.fl_add k w - ∑ i : Fin k, w i| ≤
      gamma fp.u (k - 1) * ∑ i : Fin k, |w i| := by
  rw [recursiveSum_eq_fl_recursiveSum]
  simpa only [gamma_standardAddFPModel] using
    (NumStability.recursiveSum_forward_error_bound
      (standardAddFPModel fp) k w
      ((gammaValid_standardAddFPModel fp (k - 1)).2 hvalid))

lemma twoSumPrefix_abs_le (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : k ≤ n)
    (hvalid : GammaValid fp.u n) :
    |twoSumPrefix fp v k hk| ≤
      (1 + gamma fp.u n) * ∑ i : Fin (n + 1), |v i| := by
  let w : Fin (k + 1) → ℝ := fun j =>
    v ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ hk)⟩
  have hvn : NumStability.gammaValid (standardAddFPModel fp.toStandardAddModel) n :=
    (gammaValid_standardAddFPModel fp.toStandardAddModel n).2 hvalid
  have hvk : NumStability.gammaValid (standardAddFPModel fp.toStandardAddModel) k :=
    NumStability.gammaValid_mono (standardAddFPModel fp.toStandardAddModel) hk hvn
  have hrec := NumStability.recursiveSum_abs_le_one_add_gamma_mul_sum_abs
    (standardAddFPModel fp.toStandardAddModel) (k + 1) w (by simpa using hvk)
  have hgamma : gamma fp.u k ≤ gamma fp.u n := by
    simpa only [gamma_standardAddFPModel] using
      (NumStability.gamma_mono (standardAddFPModel fp.toStandardAddModel) hk hvn)
  have hgamma_nonneg : 0 ≤ gamma fp.u n := by
    simpa only [gamma_standardAddFPModel] using
      (NumStability.gamma_nonneg (standardAddFPModel fp.toStandardAddModel) hvn)
  have hpartial :
      ∑ j : Fin (k + 1), |w j| ≤ ∑ i : Fin (n + 1), |v i| := by
    simpa only [w] using
      (sum_abs_castLE_le (Nat.succ_le_succ hk) v)
  rw [twoSumPrefix_eq_recursiveSum]
  change |recursiveSum fp.fl_add (k + 1) w| ≤ _
  calc
    |recursiveSum fp.fl_add (k + 1) w| ≤
        (1 + gamma fp.u k) * ∑ j : Fin (k + 1), |w j| := by
          rw [recursiveSum_eq_fl_recursiveSum fp.toStandardAddModel]
          simpa only [gamma_standardAddFPModel] using hrec
    _ ≤ (1 + gamma fp.u n) * ∑ j : Fin (k + 1), |w j| := by
          exact mul_le_mul_of_nonneg_right (by linarith) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    _ ≤ (1 + gamma fp.u n) * ∑ i : Fin (n + 1), |v i| := by
          exact mul_le_mul_of_nonneg_left hpartial (by linarith)

lemma nat_mul_u_mul_one_add_gamma (u : ℝ) (n : ℕ)
    (hvalid : GammaValid u n) :
    (n : ℝ) * u * (1 + gamma u n) = gamma u n := by
  have hden : 1 - (n : ℝ) * u ≠ 0 := by
    unfold GammaValid at hvalid
    linarith
  unfold gamma
  field_simp [hden]
  ring

lemma twoSumCorrection_sum_abs_le (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (hvalid : GammaValid fp.u n) :
    ∑ i : Fin n, |twoSumCorrection fp v i| ≤
      gamma fp.u n * ∑ i : Fin (n + 1), |v i| := by
  have hpoint : ∀ i : Fin n,
      |twoSumCorrection fp v i| ≤
        fp.u * ((1 + gamma fp.u n) * ∑ j : Fin (n + 1), |v j|) := by
    intro i
    have hi : i.val + 1 ≤ n := by omega
    have hp := twoSumPrefix_abs_le fp v (i.val + 1) hi hvalid
    have hs := twoSumPrefix_succ fp v i.val hi
    unfold twoSumCorrection
    calc
      |(fp.twoSum
          (twoSumPrefix fp v i.val (Nat.le_of_lt i.isLt))
          (v ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)).2| ≤
          fp.u * |(fp.twoSum
            (twoSumPrefix fp v i.val (Nat.le_of_lt i.isLt))
            (v ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)).1| :=
        fp.twoSum_low_le _ _
      _ = fp.u * |twoSumPrefix fp v (i.val + 1) hi| := by
        rw [hs]
      _ ≤ fp.u * ((1 + gamma fp.u n) * ∑ j : Fin (n + 1), |v j|) :=
        mul_le_mul_of_nonneg_left hp fp.u_nonneg
  calc
    ∑ i : Fin n, |twoSumCorrection fp v i| ≤
        ∑ _i : Fin n,
          fp.u * ((1 + gamma fp.u n) * ∑ j : Fin (n + 1), |v j|) := by
            exact Finset.sum_le_sum fun i _ => hpoint i
    _ = (n : ℝ) *
          (fp.u * ((1 + gamma fp.u n) * ∑ j : Fin (n + 1), |v j|)) := by
            simp
    _ = gamma fp.u n * ∑ j : Fin (n + 1), |v j| := by
          rw [show (n : ℝ) *
              (fp.u * ((1 + gamma fp.u n) * ∑ j : Fin (n + 1), |v j|)) =
            ((n : ℝ) * fp.u * (1 + gamma fp.u n)) *
              ∑ j : Fin (n + 1), |v j| by ring,
            nat_mul_u_mul_one_add_gamma fp.u n hvalid]

lemma one_add_u_mul_gamma_pred_le_gamma (fp : StandardAddModel) (n : ℕ)
    (hn : 0 < n) (hvalid : GammaValid fp.u n) :
    (1 + fp.u) * gamma fp.u (n - 1) ≤ gamma fp.u n := by
  let F := standardAddFPModel fp
  have hvn : NumStability.gammaValid F n := by
    exact (gammaValid_standardAddFPModel fp n).2 hvalid
  have hvp : NumStability.gammaValid F (n - 1) :=
    NumStability.gammaValid_mono F (Nat.sub_le n 1) hvn
  have hv1 : NumStability.gammaValid F 1 :=
    NumStability.gammaValid_mono F hn hvn
  have hsum :
      NumStability.gamma F (n - 1) + NumStability.gamma F 1 +
          NumStability.gamma F (n - 1) * NumStability.gamma F 1 ≤
        NumStability.gamma F n := by
    have h := NumStability.gamma_sum_le F (n - 1) 1 (by
      rw [Nat.sub_add_cancel hn]
      exact hvn)
    simpa [Nat.sub_add_cancel hn] using h
  have hu : fp.u ≤ NumStability.gamma F 1 :=
    NumStability.u_le_gamma F Nat.zero_lt_one hv1
  have hgp : 0 ≤ NumStability.gamma F (n - 1) :=
    NumStability.gamma_nonneg F hvp
  have hg1 : 0 ≤ NumStability.gamma F 1 :=
    NumStability.gamma_nonneg F hv1
  have hprod :
      NumStability.gamma F (n - 1) * fp.u ≤
        NumStability.gamma F (n - 1) * NumStability.gamma F 1 :=
    mul_le_mul_of_nonneg_left hu hgp
  change fp.u ≤ gamma fp.u 1 at hu
  change 0 ≤ gamma fp.u 1 at hg1
  simp only [F, gamma_standardAddFPModel] at hsum hgp hprod ⊢
  calc
    (1 + fp.u) * gamma fp.u (n - 1) =
        gamma fp.u (n - 1) + gamma fp.u (n - 1) * fp.u := by ring
    _ ≤ gamma fp.u (n - 1) +
        gamma fp.u (n - 1) * gamma fp.u 1 :=
      add_le_add (le_refl _) hprod
    _ ≤ gamma fp.u (n - 1) + gamma fp.u 1 +
        gamma fp.u (n - 1) * gamma fp.u 1 := by linarith
    _ ≤ gamma fp.u n := hsum

lemma sum2_eq_final_add (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (hn : n ≠ 0) :
    sum2 fp v =
      fp.fl_add
        (recursiveSum fp.fl_add n (twoSumCorrection fp v))
        (twoSumPrefix fp v n (Nat.le_refl n)) := by
  unfold sum2 sumK
  norm_num
  change recursiveSum fp.fl_add (n + 1) (vecSum fp v) = _
  rw [recursiveSum, dif_neg hn]
  congr 1
  · congr 1
    funext i
    simp [vecSum, twoSumCorrection]
  · simp [vecSum]

theorem p02_t1_sum2_error_bound
    (fp : ErrorFreeAddModel) (n : ℕ) (v : Fin (n + 1) → ℝ)
    (hvalid : GammaValid fp.u (n + 1)) :
    |sum2 fp v - ∑ i : Fin (n + 1), v i| ≤
      fp.u * |∑ i : Fin (n + 1), v i| +
        (gamma fp.u n) ^ 2 * ∑ i : Fin (n + 1), |v i| := by
  -- PROOF_START P02-T1-H001
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sum2, sumK, iteratedVecSum, vecSum, twoSumPrefix,
      recursiveSum, gamma]
    rw [show (0 : Fin 1) = Fin.last 0 by rfl, Fin.lastCases_last]
    simp only [sub_self, abs_zero]
    exact mul_nonneg fp.u_nonneg (abs_nonneg _)
  · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    let q : Fin n → ℝ := twoSumCorrection fp v
    let p : ℝ := twoSumPrefix fp v n (Nat.le_refl n)
    let σ : ℝ := recursiveSum fp.fl_add n q
    let s : ℝ := ∑ i : Fin (n + 1), v i
    let S : ℝ := ∑ i : Fin (n + 1), |v i|
    have hvnp1 :
        NumStability.gammaValid (standardAddFPModel fp.toStandardAddModel) (n + 1) :=
      (gammaValid_standardAddFPModel fp.toStandardAddModel (n + 1)).2 hvalid
    have hvn :
        NumStability.gammaValid (standardAddFPModel fp.toStandardAddModel) n :=
      NumStability.gammaValid_mono (standardAddFPModel fp.toStandardAddModel)
        (Nat.le_succ n) hvnp1
    have hvalid_n : GammaValid fp.u n :=
      (gammaValid_standardAddFPModel fp.toStandardAddModel n).1 hvn
    have hvalid_pred : GammaValid fp.u (n - 1) := by
      exact (gammaValid_standardAddFPModel fp.toStandardAddModel (n - 1)).1
        (NumStability.gammaValid_mono (standardAddFPModel fp.toStandardAddModel)
          (Nat.sub_le n 1) hvn)
    have hQ : ∑ i : Fin n, |q i| ≤ gamma fp.u n * S := by
      simpa only [q, S] using twoSumCorrection_sum_abs_le fp v hvalid_n
    have hE : |σ - ∑ i : Fin n, q i| ≤
        gamma fp.u (n - 1) * ∑ i : Fin n, |q i| := by
      simpa only [σ, q] using
        recursiveSum_forward_error_bound_standard fp.toStandardAddModel n q hvalid_pred
    have hgp : 0 ≤ gamma fp.u (n - 1) := by
      simpa only [gamma_standardAddFPModel] using
        (NumStability.gamma_nonneg (standardAddFPModel fp.toStandardAddModel)
          ((gammaValid_standardAddFPModel fp.toStandardAddModel (n - 1)).2
            hvalid_pred))
    have hgn : 0 ≤ gamma fp.u n := by
      simpa only [gamma_standardAddFPModel] using
        (NumStability.gamma_nonneg (standardAddFPModel fp.toStandardAddModel) hvn)
    have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hcoeff :
        (1 + fp.u) * gamma fp.u (n - 1) ≤ gamma fp.u n :=
      one_add_u_mul_gamma_pred_le_gamma fp.toStandardAddModel n hn hvalid_n
    have hE' : |σ - ∑ i : Fin n, q i| ≤
        gamma fp.u (n - 1) * (gamma fp.u n * S) :=
      le_trans hE (mul_le_mul_of_nonneg_left hQ hgp)
    have hmain :
        (1 + fp.u) * |σ - ∑ i : Fin n, q i| ≤
          (gamma fp.u n) ^ 2 * S := by
      calc
        (1 + fp.u) * |σ - ∑ i : Fin n, q i| ≤
            (1 + fp.u) *
              (gamma fp.u (n - 1) * (gamma fp.u n * S)) :=
          mul_le_mul_of_nonneg_left hE' (by linarith [fp.u_nonneg])
        _ = ((1 + fp.u) * gamma fp.u (n - 1)) *
              (gamma fp.u n * S) := by ring
        _ ≤ gamma fp.u n * (gamma fp.u n * S) :=
          mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hgn hS)
        _ = (gamma fp.u n) ^ 2 * S := by ring
    have hexact : p + ∑ i : Fin n, q i = s := by
      have hsum := vecSum_sum_eq fp v
      rw [Fin.sum_univ_castSucc] at hsum
      simp only [vecSum, Fin.lastCases_castSucc, Fin.lastCases_last] at hsum
      change (∑ i : Fin n, q i) + p = s at hsum
      linarith
    have hsum2 : sum2 fp v = fp.fl_add σ p := by
      simpa only [σ, p, q] using sum2_eq_final_add fp v hn0
    obtain ⟨δ, hδ, hfl⟩ := fp.model_add σ p
    have h1δ : |1 + δ| ≤ 1 + fp.u := by
      calc
        |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
        _ ≤ 1 + fp.u := by norm_num; linarith
    have herr :
        (σ + p) * (1 + δ) - s =
          (1 + δ) * (σ - ∑ i : Fin n, q i) + δ * s := by
      rw [← hexact]
      ring
    change |sum2 fp v - s| ≤ fp.u * |s| + (gamma fp.u n) ^ 2 * S
    rw [hsum2, hfl, herr]
    calc
      |(1 + δ) * (σ - ∑ i : Fin n, q i) + δ * s| ≤
          |1 + δ| * |σ - ∑ i : Fin n, q i| + |δ| * |s| := by
            simpa only [abs_mul] using
              (abs_add_le
                ((1 + δ) * (σ - ∑ i : Fin n, q i)) (δ * s))
      _ ≤ (1 + fp.u) * |σ - ∑ i : Fin n, q i| + fp.u * |s| := by
            exact add_le_add
              (mul_le_mul h1δ (le_refl _) (abs_nonneg _)
                (by linarith [fp.u_nonneg]))
              (mul_le_mul_of_nonneg_right hδ (abs_nonneg _))
      _ ≤ (gamma fp.u n) ^ 2 * S + fp.u * |s| :=
            add_le_add hmain (le_refl _)
      _ = fp.u * |s| + (gamma fp.u n) ^ 2 * S := by ring

end HighamBench
