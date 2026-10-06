import HighamBench.P02Definitions
import NumStability.Algorithms.Summation.Recursive.Core

namespace HighamBench

open scoped BigOperators

private noncomputable def addFPModel (fp : StandardAddModel) :
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

private lemma prefix_abs_sum_le {N k : ℕ} (hk : k ≤ N)
    (v : Fin N → ℝ) :
    (∑ i : Fin k, |v (Fin.castLE hk i)|) ≤ ∑ i : Fin N, |v i| := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Fin.sum_univ_add]
  have heq :
      (∑ i : Fin k, |v (Fin.castLE (Nat.le_add_right k d) i)|) =
        ∑ i : Fin k, |v (Fin.castAdd d i)| := by
    apply Finset.sum_congr rfl
    intro i _
    congr 2
  rw [heq]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _))

private lemma gamma_nonneg_of_valid (fp : StandardAddModel) {k : ℕ}
    (hvalid : (k : ℝ) * fp.u < 1) : 0 ≤ gamma fp.u k := by
  have hvalid' : NumStability.gammaValid (addFPModel fp) k := by
    simpa [NumStability.gammaValid, addFPModel] using hvalid
  simpa [NumStability.gamma, addFPModel, gamma] using
    NumStability.gamma_nonneg (addFPModel fp) hvalid'

private lemma gamma_mono_of_valid (fp : StandardAddModel) {j k : ℕ}
    (hjk : j ≤ k) (hvalid : (k : ℝ) * fp.u < 1) :
    gamma fp.u j ≤ gamma fp.u k := by
  have hvalid' : NumStability.gammaValid (addFPModel fp) k := by
    simpa [NumStability.gammaValid, addFPModel] using hvalid
  simpa [NumStability.gamma, addFPModel, gamma] using
    NumStability.gamma_mono (addFPModel fp) hjk hvalid'

private lemma gamma_sum_le_of_valid (fp : StandardAddModel) (j k : ℕ)
    (hvalid : ((j + k : ℕ) : ℝ) * fp.u < 1) :
    gamma fp.u j + gamma fp.u k + gamma fp.u j * gamma fp.u k ≤
      gamma fp.u (j + k) := by
  have hvalid' : NumStability.gammaValid (addFPModel fp) (j + k) := by
    simpa [NumStability.gammaValid, addFPModel] using hvalid
  simpa [NumStability.gamma, addFPModel, gamma] using
    NumStability.gamma_sum_le (addFPModel fp) j k hvalid'

private theorem recursiveSum_eq_ns (fp : StandardAddModel) :
    ∀ (n : ℕ) (v : Fin n → ℝ),
      recursiveSum fp.fl_add n v =
        NumStability.fl_recursiveSum (addFPModel fp) n v
  | 0, v => by simp [recursiveSum, NumStability.fl_recursiveSum]
  | n + 1, v => by
      unfold NumStability.fl_recursiveSum
      rw [Fin.foldl_succ_last]
      change recursiveSum fp.fl_add (n + 1) v =
        fp.fl_add
          (NumStability.fl_recursiveSum (addFPModel fp) n
            (fun i => v i.castSucc))
          (v (Fin.last n))
      rw [← recursiveSum_eq_ns fp n (fun i => v i.castSucc)]
      by_cases hn : n = 0
      · subst n
        simp [recursiveSum, fp.fl_add_zero]
      · simp [recursiveSum, hn, addFPModel]

private theorem recursiveSum_forward_error_bound_local (fp : StandardAddModel)
    (n : ℕ) (v : Fin n → ℝ)
    (hn : ((n - 1 : ℕ) : ℝ) * fp.u < 1) :
    |recursiveSum fp.fl_add n v - ∑ i, v i| ≤
      gamma fp.u (n - 1) * ∑ i, |v i| := by
  rw [recursiveSum_eq_ns]
  have hn' : NumStability.gammaValid (addFPModel fp) (n - 1) := by
    simpa [NumStability.gammaValid, addFPModel] using hn
  simpa [NumStability.gamma, addFPModel, gamma] using
    NumStability.recursiveSum_forward_error_bound
      (addFPModel fp) n v hn'

private lemma twoSumPrefix_abs_le (fp : ErrorFreeAddModel) {N : ℕ}
    (v : Fin (N + 1) → ℝ) (k : ℕ) (hk : k ≤ N)
    (hvalid : (k : ℝ) * fp.u < 1) :
    |twoSumPrefix fp v k hk| ≤
      (1 + gamma fp.u k) * ∑ i : Fin (N + 1), |v i| := by
  have hvalid' : NumStability.gammaValid (addFPModel fp.toStandardAddModel) k := by
    simpa [NumStability.gammaValid, addFPModel] using hvalid
  obtain ⟨Theta, theta, hTheta, htheta, hfold⟩ :=
    NumStability.fl_sum_error_init (addFPModel fp.toStandardAddModel) k
      (fun i : Fin k =>
        v ⟨i.val + 1,
          Nat.succ_lt_succ (Nat.lt_of_lt_of_le i.isLt hk)⟩)
      (v ⟨0, Nat.succ_pos N⟩) hvalid'
  have hgamma : 0 ≤ gamma fp.u k := by
    simpa [NumStability.gamma, addFPModel, gamma] using
      NumStability.gamma_nonneg (addFPModel fp.toStandardAddModel) hvalid'
  have hTheta' : |1 + Theta| ≤ 1 + gamma fp.u k := by
    have hTheta0 : |Theta| ≤ gamma fp.u k := by
      change |Theta| ≤ (k : ℝ) * fp.u / (1 - (k : ℝ) * fp.u)
      simpa [NumStability.gamma, addFPModel] using hTheta
    calc
      |1 + Theta| ≤ 1 + |Theta| := by simpa using abs_add_le (1 : ℝ) Theta
      _ ≤ 1 + gamma fp.u k := by linarith
  have htheta' : ∀ i, |1 + theta i| ≤ 1 + gamma fp.u k := by
    intro i
    have htheta0 : |theta i| ≤ gamma fp.u k := by
      change |theta i| ≤ (k : ℝ) * fp.u / (1 - (k : ℝ) * fp.u)
      simpa [NumStability.gamma, addFPModel] using htheta i
    calc
      |1 + theta i| ≤ 1 + |theta i| := by
        simpa using abs_add_le (1 : ℝ) (theta i)
      _ ≤ 1 + gamma fp.u k := by linarith
  have hprefix :
      |v ⟨0, Nat.succ_pos N⟩| +
          ∑ i : Fin k,
            |v ⟨i.val + 1,
              Nat.succ_lt_succ (Nat.lt_of_lt_of_le i.isLt hk)⟩| =
        ∑ j : Fin (k + 1),
          |v (Fin.castLE (Nat.succ_le_succ hk) j)| := by
    rw [Fin.sum_univ_succ]
    congr 1
  rw [twoSumPrefix]
  simp_rw [fp.twoSum_high]
  have hfold' :
      Fin.foldl k
          (fun acc i => fp.fl_add acc
            (v ⟨i.val + 1,
              Nat.succ_lt_succ (Nat.lt_of_lt_of_le i.isLt hk)⟩))
          (v ⟨0, Nat.succ_pos N⟩) =
        v ⟨0, Nat.succ_pos N⟩ * (1 + Theta) +
          ∑ i : Fin k,
            v ⟨i.val + 1,
              Nat.succ_lt_succ (Nat.lt_of_lt_of_le i.isLt hk)⟩ *
                (1 + theta i) := by
    simpa [addFPModel] using hfold
  rw [hfold']
  calc
    |v ⟨0, Nat.succ_pos N⟩ * (1 + Theta) +
        ∑ i : Fin k,
          v ⟨i.val + 1,
            Nat.succ_lt_succ (Nat.lt_of_lt_of_le i.isLt hk)⟩ *
              (1 + theta i)|
        ≤ |v ⟨0, Nat.succ_pos N⟩ * (1 + Theta)| +
            ∑ i : Fin k,
              |v ⟨i.val + 1,
                Nat.succ_lt_succ (Nat.lt_of_lt_of_le i.isLt hk)⟩ *
                  (1 + theta i)| := by
          exact le_trans (abs_add_le _ _)
            (add_le_add_right (Finset.abs_sum_le_sum_abs _ _) _)
    _ ≤ |v ⟨0, Nat.succ_pos N⟩| * (1 + gamma fp.u k) +
          ∑ i : Fin k,
            |v ⟨i.val + 1,
              Nat.succ_lt_succ (Nat.lt_of_lt_of_le i.isLt hk)⟩| *
                (1 + gamma fp.u k) := by
          rw [abs_mul]
          gcongr with i
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (htheta' i) (abs_nonneg _)
    _ = (1 + gamma fp.u k) *
          (|v ⟨0, Nat.succ_pos N⟩| +
            ∑ i : Fin k,
              |v ⟨i.val + 1,
                Nat.succ_lt_succ (Nat.lt_of_lt_of_le i.isLt hk)⟩|) := by
          rw [← Finset.sum_mul]
          ring
    _ = (1 + gamma fp.u k) *
          ∑ j : Fin (k + 1),
            |v (Fin.castLE (Nat.succ_le_succ hk) j)| := by rw [hprefix]
    _ ≤ (1 + gamma fp.u k) * ∑ i : Fin (N + 1), |v i| := by
          exact mul_le_mul_of_nonneg_left
            (prefix_abs_sum_le (Nat.succ_le_succ hk) v)
            (by linarith)

private lemma twoSumPrefix_succ (fp : ErrorFreeAddModel) {N : ℕ}
    (v : Fin (N + 1) → ℝ) (k : ℕ) (hk : k < N) :
    twoSumPrefix fp v (k + 1) (Nat.succ_le_iff.mpr hk) =
      (fp.twoSum
        (twoSumPrefix fp v k (Nat.le_of_lt hk))
        (v ⟨k + 1, Nat.succ_lt_succ hk⟩)).1 := by
  rw [twoSumPrefix, Fin.foldl_succ_last]
  rfl

private lemma correctionMagnitude_le_gamma (fp : ErrorFreeAddModel) {N : ℕ}
    (v : Fin (N + 1) → ℝ) (hvalid : (N : ℝ) * fp.u < 1) :
    (∑ i : Fin N, |twoSumCorrection fp v i|) ≤
      gamma fp.u N * ∑ i : Fin (N + 1), |v i| := by
  have hgamma : 0 ≤ gamma fp.u N :=
    gamma_nonneg_of_valid fp.toStandardAddModel hvalid
  have hden : 1 - (N : ℝ) * fp.u ≠ 0 := by linarith
  calc
    (∑ i : Fin N, |twoSumCorrection fp v i|) ≤
        ∑ _i : Fin N,
          fp.u * ((1 + gamma fp.u N) *
            ∑ j : Fin (N + 1), |v j|) := by
      apply Finset.sum_le_sum
      intro i _
      have hik : i.val + 1 ≤ N := i.isLt
      have hki : ((i.val + 1 : ℕ) : ℝ) * fp.u < 1 := by
        have hcast : ((i.val + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
          exact_mod_cast hik
        exact lt_of_le_of_lt
          (mul_le_mul_of_nonneg_right hcast fp.u_nonneg) hvalid
      have hpref := twoSumPrefix_abs_le fp v (i.val + 1) hik hki
      have hgmono : gamma fp.u (i.val + 1) ≤ gamma fp.u N :=
        gamma_mono_of_valid fp.toStandardAddModel hik hvalid
      rw [twoSumCorrection]
      calc
        |(fp.twoSum
            (twoSumPrefix fp v i.val (Nat.le_of_lt i.isLt))
            (v ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)).2| ≤
            fp.u *
              |(fp.twoSum
                (twoSumPrefix fp v i.val (Nat.le_of_lt i.isLt))
                (v ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)).1| :=
          fp.twoSum_low_le _ _
        _ = fp.u * |twoSumPrefix fp v (i.val + 1) hik| := by
          rw [twoSumPrefix_succ fp v i.val i.isLt]
        _ ≤ fp.u *
              ((1 + gamma fp.u (i.val + 1)) *
                ∑ j : Fin (N + 1), |v j|) :=
          mul_le_mul_of_nonneg_left hpref fp.u_nonneg
        _ ≤ fp.u *
              ((1 + gamma fp.u N) *
                ∑ j : Fin (N + 1), |v j|) := by
          apply mul_le_mul_of_nonneg_left _ fp.u_nonneg
          apply mul_le_mul_of_nonneg_right _
            (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
          linarith
    _ = ((N : ℝ) * fp.u * (1 + gamma fp.u N)) *
          ∑ j : Fin (N + 1), |v j| := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring
    _ = gamma fp.u N * ∑ j : Fin (N + 1), |v j| := by
      congr 1
      unfold gamma
      field_simp [hden]
      ring

private theorem twoSumPrefix_add_corrections (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n),
      twoSumPrefix fp v k hk +
          ∑ i : Fin k,
            twoSumCorrection fp v
              ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ =
        ∑ i : Fin (k + 1),
          v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩
  | 0, hk => by simp [twoSumPrefix]
  | k + 1, hk => by
      have hk' : k ≤ n := by omega
      have hp :
          twoSumPrefix fp v (k + 1) hk =
            (fp.twoSum (twoSumPrefix fp v k hk') (v ⟨k + 1, by omega⟩)).1 := by
        unfold twoSumPrefix
        rw [Fin.foldl_succ_last]
        rfl
      have hc :
          twoSumCorrection fp v ⟨k, by omega⟩ =
            (fp.twoSum (twoSumPrefix fp v k hk') (v ⟨k + 1, by omega⟩)).2 := by
        rfl
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      have ih := twoSumPrefix_add_corrections fp v k hk'
      have hex := fp.twoSum_exact (twoSumPrefix fp v k hk')
        (v ⟨k + 1, by omega⟩)
      simp only [Fin.castSucc, Fin.last, Fin.castAdd, Fin.val_castLE]
      rw [hp, hc]
      linarith [ih, hex]

private theorem vecSum_sum_eq (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) :
    (∑ i, vecSum fp v i) = ∑ i, v i := by
  rw [Fin.sum_univ_castSucc]
  simp only [vecSum, Fin.lastCases_castSucc, Fin.lastCases_last]
  simpa [add_comm] using
    twoSumPrefix_add_corrections fp v n (Nat.le_refl n)

private lemma vecSum_magnitude_le (fp : ErrorFreeAddModel) {N : ℕ}
    (v : Fin (N + 1) → ℝ) (hvalid : (N : ℝ) * fp.u < 1) :
    (∑ i : Fin (N + 1), |vecSum fp v i|) ≤
      |∑ i : Fin (N + 1), v i| +
        2 * gamma fp.u N * ∑ i : Fin (N + 1), |v i| := by
  let C : ℝ := ∑ i : Fin N, |twoSumCorrection fp v i|
  have hC : C ≤ gamma fp.u N * ∑ i : Fin (N + 1), |v i| := by
    simpa [C] using correctionMagnitude_le_gamma fp v hvalid
  have hcorr :
      |∑ i : Fin N, twoSumCorrection fp v i| ≤ C := by
    exact Finset.abs_sum_le_sum_abs _ _
  have hexact := twoSumPrefix_add_corrections fp v N (Nat.le_refl N)
  have htop :
      |twoSumPrefix fp v N (Nat.le_refl N)| ≤
        |∑ i : Fin (N + 1), v i| + C := by
    have hid :
        twoSumPrefix fp v N (Nat.le_refl N) =
          (∑ i : Fin (N + 1), v i) -
            ∑ i : Fin N, twoSumCorrection fp v i := by
      linarith
    rw [hid]
    calc
      |(∑ i : Fin (N + 1), v i) -
          ∑ i : Fin N, twoSumCorrection fp v i| ≤
          |∑ i : Fin (N + 1), v i| +
            |∑ i : Fin N, twoSumCorrection fp v i| := abs_sub _ _
      _ ≤ |∑ i : Fin (N + 1), v i| + C := by linarith
  rw [Fin.sum_univ_castSucc]
  simp only [vecSum, Fin.lastCases_castSucc, Fin.lastCases_last]
  change C + |twoSumPrefix fp v N (Nat.le_refl N)| ≤ _
  calc
    C + |twoSumPrefix fp v N (Nat.le_refl N)| ≤
        C + (|∑ i : Fin (N + 1), v i| + C) :=
      by linarith
    _ = |∑ i : Fin (N + 1), v i| + 2 * C := by ring
    _ ≤ |∑ i : Fin (N + 1), v i| +
          2 * (gamma fp.u N * ∑ i : Fin (N + 1), |v i|) := by
      gcongr
    _ = |∑ i : Fin (N + 1), v i| +
          2 * gamma fp.u N * ∑ i : Fin (N + 1), |v i| := by ring

private lemma iteratedVecSum_sum_eq (fp : ErrorFreeAddModel) {N : ℕ}
    (j : ℕ) (v : Fin (N + 1) → ℝ) :
    (∑ i, iteratedVecSum fp j v i) = ∑ i, v i := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [iteratedVecSum, vecSum_sum_eq, ih]

private lemma gamma_le_one_third_of_quarter (fp : StandardAddModel) (N : ℕ)
    (hquarter : (N : ℝ) * fp.u ≤ 1 / 4) :
    gamma fp.u N ≤ 1 / 3 := by
  have hnonneg : 0 ≤ (N : ℝ) * fp.u :=
    mul_nonneg (by positivity) fp.u_nonneg
  have hden : 0 < 1 - (N : ℝ) * fp.u := by linarith
  unfold gamma
  rw [div_le_iff₀ hden]
  nlinarith

private lemma iteratedVecSum_magnitude_le (fp : ErrorFreeAddModel) {N : ℕ}
    (j : ℕ) (v : Fin (N + 1) → ℝ)
    (hquarter : (N : ℝ) * fp.u ≤ 1 / 4) :
    (∑ i : Fin (N + 1), |iteratedVecSum fp j v i|) ≤
      3 * |∑ i : Fin (N + 1), v i| +
        (gamma fp.u (2 * N)) ^ j * ∑ i : Fin (N + 1), |v i| := by
  have hvalidN : (N : ℝ) * fp.u < 1 := by linarith
  have hvalid2N : ((2 * N : ℕ) : ℝ) * fp.u < 1 := by
    push_cast
    nlinarith
  have hg : 0 ≤ gamma fp.u N :=
    gamma_nonneg_of_valid fp.toStandardAddModel hvalidN
  have hG : 0 ≤ gamma fp.u (2 * N) :=
    gamma_nonneg_of_valid fp.toStandardAddModel hvalid2N
  have hgthird : gamma fp.u N ≤ 1 / 3 :=
    gamma_le_one_third_of_quarter fp.toStandardAddModel N hquarter
  have htwog : 2 * gamma fp.u N ≤ gamma fp.u (2 * N) := by
    have hv : (((N + N : ℕ) : ℝ) * fp.u) < 1 := by
      norm_num [Nat.cast_add, Nat.cast_mul] at hvalid2N ⊢
      nlinarith
    have hsum := gamma_sum_le_of_valid fp.toStandardAddModel N N hv
    have hsum' :
        gamma fp.u N + gamma fp.u N + gamma fp.u N * gamma fp.u N ≤
          gamma fp.u (2 * N) := by
      simpa only [two_mul] using hsum
    nlinarith [hsum', mul_nonneg hg hg]
  induction j with
  | zero =>
      simp only [iteratedVecSum, pow_zero, one_mul]
      have hs : 0 ≤ |∑ i : Fin (N + 1), v i| := abs_nonneg _
      linarith
  | succ j ih =>
      have hstep := vecSum_magnitude_le fp (iteratedVecSum fp j v) hvalidN
      rw [iteratedVecSum_sum_eq fp j v] at hstep
      rw [iteratedVecSum]
      calc
        (∑ i : Fin (N + 1),
            |vecSum fp (iteratedVecSum fp j v) i|) ≤
            |∑ i : Fin (N + 1), v i| +
              2 * gamma fp.u N *
                ∑ i : Fin (N + 1), |iteratedVecSum fp j v i| := hstep
        _ ≤ |∑ i : Fin (N + 1), v i| +
              2 * gamma fp.u N *
                (3 * |∑ i : Fin (N + 1), v i| +
                  gamma fp.u (2 * N) ^ j *
                    ∑ i : Fin (N + 1), |v i|) := by
            gcongr
        _ ≤ 3 * |∑ i : Fin (N + 1), v i| +
              gamma fp.u (2 * N) ^ (j + 1) *
                ∑ i : Fin (N + 1), |v i| := by
            rw [pow_succ]
            have hsumabs : 0 ≤ ∑ i : Fin (N + 1), |v i| :=
              Finset.sum_nonneg (fun _ _ => abs_nonneg _)
            have hp : 0 ≤ gamma fp.u (2 * N) ^ j := pow_nonneg hG _
            have hlead0 := mul_le_mul_of_nonneg_right hgthird
              (abs_nonneg (∑ i : Fin (N + 1), v i))
            have hlead :
                |∑ i : Fin (N + 1), v i| +
                    2 * gamma fp.u N *
                      (3 * |∑ i : Fin (N + 1), v i|) ≤
                  3 * |∑ i : Fin (N + 1), v i| := by
              nlinarith
            have htail := mul_le_mul_of_nonneg_right htwog
              (mul_nonneg hp hsumabs)
            calc
              |∑ i : Fin (N + 1), v i| +
                  2 * gamma fp.u N *
                    (3 * |∑ i : Fin (N + 1), v i| +
                      gamma fp.u (2 * N) ^ j *
                        ∑ i : Fin (N + 1), |v i|) =
                (|∑ i : Fin (N + 1), v i| +
                    2 * gamma fp.u N *
                      (3 * |∑ i : Fin (N + 1), v i|)) +
                  (2 * gamma fp.u N) *
                    (gamma fp.u (2 * N) ^ j *
                      ∑ i : Fin (N + 1), |v i|) := by ring
              _ ≤ 3 * |∑ i : Fin (N + 1), v i| +
                    gamma fp.u (2 * N) *
                      (gamma fp.u (2 * N) ^ j *
                        ∑ i : Fin (N + 1), |v i|) :=
                add_le_add hlead htail
              _ = 3 * |∑ i : Fin (N + 1), v i| +
                    gamma fp.u (2 * N) ^ j * gamma fp.u (2 * N) *
                      ∑ i : Fin (N + 1), |v i| := by ring

private lemma one_add_u_mul_gamma_pred_le_gamma
    (fp : StandardAddModel) (N : ℕ) (hN : 1 ≤ N)
    (hvalid : (N : ℝ) * fp.u < 1) :
    (1 + fp.u) * gamma fp.u (N - 1) ≤ gamma fp.u N := by
  have hpredNat : N - 1 + 1 = N := Nat.sub_add_cancel hN
  have hpredLe : N - 1 ≤ N := Nat.sub_le N 1
  have honeLe : 1 ≤ N := hN
  have hvalidPred : ((N - 1 : ℕ) : ℝ) * fp.u < 1 := by
    have hc : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hpredLe
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc fp.u_nonneg) hvalid
  have hvalidOne : (1 : ℝ) * fp.u < 1 := by
    have hc : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast honeLe
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc fp.u_nonneg) hvalid
  have hgp : 0 ≤ gamma fp.u (N - 1) :=
    gamma_nonneg_of_valid fp hvalidPred
  have hg1 : 0 ≤ gamma fp.u 1 :=
    gamma_nonneg_of_valid fp (by simpa using hvalidOne)
  have hu1 : fp.u ≤ gamma fp.u 1 := by
    have hv : NumStability.gammaValid (addFPModel fp) 1 := by
      simpa [NumStability.gammaValid, addFPModel] using hvalidOne
    simpa [NumStability.gamma, addFPModel, gamma] using
      NumStability.u_le_gamma (addFPModel fp) (by omega) hv
  have hsum := gamma_sum_le_of_valid fp (N - 1) 1 (by
    simpa [hpredNat] using hvalid)
  rw [hpredNat] at hsum
  have hmul : gamma fp.u (N - 1) * fp.u ≤
      gamma fp.u (N - 1) * gamma fp.u 1 :=
    mul_le_mul_of_nonneg_left hu1 hgp
  nlinarith

private lemma recursiveSum_vecSum_error (fp : ErrorFreeAddModel) {N : ℕ}
    (hN : 1 ≤ N) (v : Fin (N + 1) → ℝ)
    (hvalid : (N : ℝ) * fp.u < 1) :
    |recursiveSum fp.fl_add (N + 1) (vecSum fp v) -
        ∑ i : Fin (N + 1), v i| ≤
      fp.u * |∑ i : Fin (N + 1), v i| +
        (gamma fp.u N) ^ 2 * ∑ i : Fin (N + 1), |v i| := by
  let c : Fin N → ℝ := fun i => twoSumCorrection fp v i
  let A : ℝ := recursiveSum fp.fl_add N c
  let W : ℝ := ∑ i : Fin N, c i
  let C : ℝ := ∑ i : Fin N, |c i|
  let H : ℝ := twoSumPrefix fp v N (Nat.le_refl N)
  let S : ℝ := ∑ i : Fin (N + 1), v i
  let M : ℝ := ∑ i : Fin (N + 1), |v i|
  have hpred : ((N - 1 : ℕ) : ℝ) * fp.u < 1 := by
    have hc : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.sub_le N 1
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc fp.u_nonneg) hvalid
  have hA : |A - W| ≤ gamma fp.u (N - 1) * C := by
    simpa [A, W, C, c] using
      recursiveSum_forward_error_bound_local fp.toStandardAddModel N c hpred
  have hC : C ≤ gamma fp.u N * M := by
    simpa [C, c, M] using correctionMagnitude_le_gamma fp v hvalid
  have hC0 : 0 ≤ C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hg : 0 ≤ gamma fp.u N :=
    gamma_nonneg_of_valid fp.toStandardAddModel hvalid
  have hcoef :
      (1 + fp.u) * gamma fp.u (N - 1) ≤ gamma fp.u N :=
    one_add_u_mul_gamma_pred_le_gamma fp.toStandardAddModel N hN hvalid
  have hE :
      (1 + fp.u) * |A - W| ≤ (gamma fp.u N) ^ 2 * M := by
    calc
      (1 + fp.u) * |A - W| ≤
          (1 + fp.u) * (gamma fp.u (N - 1) * C) :=
        mul_le_mul_of_nonneg_left hA (by linarith [fp.u_nonneg])
      _ = ((1 + fp.u) * gamma fp.u (N - 1)) * C := by ring
      _ ≤ gamma fp.u N * C :=
        mul_le_mul_of_nonneg_right hcoef hC0
      _ ≤ gamma fp.u N * (gamma fp.u N * M) :=
        mul_le_mul_of_nonneg_left hC hg
      _ = (gamma fp.u N) ^ 2 * M := by ring
  have hHS : H + W = S := by
    simpa [H, W, S, c] using
      twoSumPrefix_add_corrections fp v N (Nat.le_refl N)
  obtain ⟨delta, hdelta, hfl⟩ := fp.model_add A H
  have hN0 : N ≠ 0 := by omega
  have hrec :
      recursiveSum fp.fl_add (N + 1) (vecSum fp v) = fp.fl_add A H := by
    simp [recursiveSum, hN0, vecSum, A, H, c]
  have hid :
      recursiveSum fp.fl_add (N + 1) (vecSum fp v) - S =
        (A - W) + delta * (S + (A - W)) := by
    rw [hrec, hfl]
    rw [← hHS]
    ring
  change |recursiveSum fp.fl_add (N + 1) (vecSum fp v) - S| ≤
    fp.u * |S| + gamma fp.u N ^ 2 * M
  rw [hid]
  calc
    |(A - W) + delta * (S + (A - W))| ≤
        |A - W| + |delta * (S + (A - W))| := abs_add_le _ _
    _ = |A - W| + |delta| * |S + (A - W)| := by rw [abs_mul]
    _ ≤ |A - W| + |delta| * (|S| + |A - W|) := by
      gcongr
      exact abs_add_le _ _
    _ ≤ |A - W| + fp.u * (|S| + |A - W|) := by
      gcongr
    _ = fp.u * |S| + (1 + fp.u) * |A - W| := by ring
    _ ≤ fp.u * |S| + gamma fp.u N ^ 2 * M := by linarith

private lemma sumK_error_bound (fp : ErrorFreeAddModel) {N : ℕ}
    (L : ℕ) (hL : 2 ≤ L) (v : Fin (N + 1) → ℝ) (hN : 1 ≤ N)
    (hquarter : (N : ℝ) * fp.u ≤ 1 / 4) :
    |sumK fp L v - ∑ i : Fin (N + 1), v i| ≤
      (fp.u + 3 * (gamma fp.u N) ^ 2) *
          |∑ i : Fin (N + 1), v i| +
        (gamma fp.u (2 * N)) ^ L * ∑ i : Fin (N + 1), |v i| := by
  let z : Fin (N + 1) → ℝ := iteratedVecSum fp (L - 2) v
  have hvalid : (N : ℝ) * fp.u < 1 := by linarith
  have hbase := recursiveSum_vecSum_error fp hN z hvalid
  have hzsum : (∑ i : Fin (N + 1), z i) = ∑ i, v i := by
    simpa [z] using iteratedVecSum_sum_eq fp (L - 2) v
  have hzmag := iteratedVecSum_magnitude_le fp (L - 2) v hquarter
  change (∑ i : Fin (N + 1), |z i|) ≤ _ at hzmag
  have hvalid2N : ((2 * N : ℕ) : ℝ) * fp.u < 1 := by
    push_cast
    nlinarith
  have hg : 0 ≤ gamma fp.u N :=
    gamma_nonneg_of_valid fp.toStandardAddModel hvalid
  have hG : 0 ≤ gamma fp.u (2 * N) :=
    gamma_nonneg_of_valid fp.toStandardAddModel hvalid2N
  have htwog : 2 * gamma fp.u N ≤ gamma fp.u (2 * N) := by
    have hv : (((N + N : ℕ) : ℝ) * fp.u) < 1 := by
      norm_num [Nat.cast_add, Nat.cast_mul] at hvalid2N ⊢
      nlinarith
    have hsum := gamma_sum_le_of_valid fp.toStandardAddModel N N hv
    have hsum' :
        gamma fp.u N + gamma fp.u N + gamma fp.u N * gamma fp.u N ≤
          gamma fp.u (2 * N) := by
      simpa only [two_mul] using hsum
    nlinarith [hsum', mul_nonneg hg hg]
  have hgG : gamma fp.u N ≤ gamma fp.u (2 * N) := by linarith
  have hsq : (gamma fp.u N) ^ 2 ≤ (gamma fp.u (2 * N)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hgG) (add_nonneg hG hg)]
  have hsumabs : 0 ≤ ∑ i : Fin (N + 1), |v i| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hpow : 0 ≤ gamma fp.u (2 * N) ^ (L - 2) := pow_nonneg hG _
  have htail :
      (gamma fp.u N) ^ 2 *
          (gamma fp.u (2 * N) ^ (L - 2) *
            ∑ i : Fin (N + 1), |v i|) ≤
        gamma fp.u (2 * N) ^ L * ∑ i : Fin (N + 1), |v i| := by
    calc
      gamma fp.u N ^ 2 *
          (gamma fp.u (2 * N) ^ (L - 2) *
            ∑ i : Fin (N + 1), |v i|) ≤
        gamma fp.u (2 * N) ^ 2 *
          (gamma fp.u (2 * N) ^ (L - 2) *
            ∑ i : Fin (N + 1), |v i|) :=
          mul_le_mul_of_nonneg_right hsq (mul_nonneg hpow hsumabs)
      _ = gamma fp.u (2 * N) ^ L *
            ∑ i : Fin (N + 1), |v i| := by
          calc
            gamma fp.u (2 * N) ^ 2 *
                (gamma fp.u (2 * N) ^ (L - 2) *
                  ∑ i : Fin (N + 1), |v i|) =
              (gamma fp.u (2 * N) ^ 2 *
                gamma fp.u (2 * N) ^ (L - 2)) *
                  ∑ i : Fin (N + 1), |v i| := by ring
            _ = gamma fp.u (2 * N) ^ (2 + (L - 2)) *
                  ∑ i : Fin (N + 1), |v i| := by rw [pow_add]
            _ = gamma fp.u (2 * N) ^ L *
                  ∑ i : Fin (N + 1), |v i| := by congr 2 <;> omega
  have hiter : iteratedVecSum fp (L - 1) v = vecSum fp z := by
    have he : L - 1 = (L - 2) + 1 := by omega
    rw [he, iteratedVecSum]
  rw [hzsum] at hbase
  rw [sumK, hiter]
  calc
    |recursiveSum fp.fl_add (N + 1) (vecSum fp z) -
        ∑ i : Fin (N + 1), v i| ≤
      fp.u * |∑ i : Fin (N + 1), v i| +
        gamma fp.u N ^ 2 * ∑ i : Fin (N + 1), |z i| := hbase
    _ ≤ fp.u * |∑ i : Fin (N + 1), v i| +
        gamma fp.u N ^ 2 *
          (3 * |∑ i : Fin (N + 1), v i| +
            gamma fp.u (2 * N) ^ (L - 2) *
              ∑ i : Fin (N + 1), |v i|) := by
          gcongr
    _ = (fp.u + 3 * gamma fp.u N ^ 2) *
          |∑ i : Fin (N + 1), v i| +
        gamma fp.u N ^ 2 *
          (gamma fp.u (2 * N) ^ (L - 2) *
            ∑ i : Fin (N + 1), |v i|) := by ring
    _ ≤ (fp.u + 3 * gamma fp.u N ^ 2) *
          |∑ i : Fin (N + 1), v i| +
        gamma fp.u (2 * N) ^ L *
          ∑ i : Fin (N + 1), |v i| := by linarith

private lemma fin_sum_cast {a b : ℕ} (h : a = b) (f : Fin b → ℝ) :
    (∑ i : Fin a, f (Fin.cast h i)) = ∑ j : Fin b, f j := by
  subst b
  rfl

private lemma fin_sum_addCases {a b : ℕ} (f : Fin a → ℝ) (g : Fin b → ℝ) :
    (∑ i : Fin (a + b), Fin.addCases f g i) =
      (∑ i : Fin a, f i) + ∑ j : Fin b, g j := by
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp
  · apply Finset.sum_congr rfl
    intro j _
    simp

private lemma fin_sum_abs_addCases {a b : ℕ}
    (f : Fin a → ℝ) (g : Fin b → ℝ) :
    (∑ i : Fin (a + b), |Fin.addCases f g i|) =
      (∑ i : Fin a, |f i|) + ∑ j : Fin b, |g j| := by
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp
  · apply Finset.sum_congr rfl
    intro j _
    simp

private lemma dotKTransform_sum_eq (fp : ErrorFreeDotModel) {n : ℕ}
    (x y : Fin (n + 1) → ℝ) :
    (∑ j, dotKTransform fp x y j) = exactDot x y := by
  unfold dotKTransform
  rw [fin_sum_cast, fin_sum_addCases]
  rw [vecSum_sum_eq]
  unfold exactDot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [add_comm] using fp.twoProduct_exact (x i) (y i)

private lemma dotKTransform_magnitude_le (fp : ErrorFreeDotModel) {n : ℕ}
    (x y : Fin (n + 1) → ℝ) (hvalid : GammaValid fp.u n) :
    (∑ j, |dotKTransform fp x y j|) ≤
      |exactDot x y| +
        (2 * fp.u + 2 * gamma fp.u n * (1 + fp.u)) *
          dotMagnitude x y := by
  let lo : Fin (n + 1) → ℝ := fun i => (fp.twoProduct (x i) (y i)).2
  let hi : Fin (n + 1) → ℝ := fun i => (fp.twoProduct (x i) (y i)).1
  let L : ℝ := ∑ i, |lo i|
  let P : ℝ := ∑ i, |hi i|
  let M : ℝ := dotMagnitude x y
  let s : ℝ := exactDot x y
  have hM0 : 0 ≤ M := by
    dsimp only [M, dotMagnitude]
    exact Finset.sum_nonneg
      (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hL : L ≤ fp.u * M := by
    dsimp only [L, lo, M, dotMagnitude]
    calc
      (∑ i, |(fp.twoProduct (x i) (y i)).2|) ≤
          ∑ i, fp.u * |x i * y i| := by
        apply Finset.sum_le_sum
        intro i _
        exact fp.twoProduct_low_le_exact _ _
      _ = fp.u * ∑ i, |x i| * |y i| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_mul]
  have hP : P ≤ (1 + fp.u) * M := by
    calc
      P ≤ M + L := by
        dsimp only [P, hi, M, dotMagnitude, L, lo]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro i _
        have he := fp.twoProduct_exact (x i) (y i)
        have hh : (fp.twoProduct (x i) (y i)).1 =
            x i * y i - (fp.twoProduct (x i) (y i)).2 := by linarith
        rw [hh]
        exact le_trans (abs_sub _ _) (by rw [abs_mul])
      _ ≤ M + fp.u * M := add_le_add_right hL _
      _ = (1 + fp.u) * M := by ring
  have hlosum : |∑ i, lo i| ≤ L := Finset.abs_sum_le_sum_abs _ _
  have hhisum : |∑ i, hi i| ≤ |s| + L := by
    have heq : (∑ i, lo i) + ∑ i, hi i = s := by
      dsimp only [lo, hi, s, exactDot]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simpa only [add_comm] using fp.twoProduct_exact (x i) (y i)
    have hrewrite : (∑ i, hi i) = s - ∑ i, lo i := by linarith
    rw [hrewrite]
    exact le_trans (abs_sub _ _) (add_le_add_right hlosum _)
  have hvec := vecSum_magnitude_le fp.toErrorFreeAddModel hi hvalid
  calc
    (∑ j, |dotKTransform fp x y j|) =
        L + ∑ i, |vecSum fp.toErrorFreeAddModel hi i| := by
      unfold dotKTransform
      have hdim : (2 * n + 1) + 1 = (n + 1) + (n + 1) := by omega
      let F : Fin ((n + 1) + (n + 1)) → ℝ :=
        Fin.addCases
          (fun i : Fin (n + 1) => (fp.twoProduct (x i) (y i)).2)
          (vecSum fp.toErrorFreeAddModel
            (fun i : Fin (n + 1) => (fp.twoProduct (x i) (y i)).1))
      change (∑ j : Fin ((2 * n + 1) + 1), |F (Fin.cast hdim j)|) = _
      have hc : (∑ j : Fin ((2 * n + 1) + 1), |F (Fin.cast hdim j)|) =
          ∑ z : Fin ((n + 1) + (n + 1)), |F z| :=
        fin_sum_cast hdim (fun z => |F z|)
      rw [hc]
      dsimp only [F]
      simpa only [L, lo, hi] using
        fin_sum_abs_addCases
          (fun i : Fin (n + 1) => (fp.twoProduct (x i) (y i)).2)
          (vecSum fp.toErrorFreeAddModel
            (fun i : Fin (n + 1) => (fp.twoProduct (x i) (y i)).1))
    _ ≤ L + (|∑ i, hi i| + 2 * gamma fp.u n * P) := by
      exact add_le_add_right hvec _
    _ ≤ L + (|s| + L + 2 * gamma fp.u n * P) := by
      gcongr
    _ ≤ fp.u * M +
        (|s| + fp.u * M + 2 * gamma fp.u n * ((1 + fp.u) * M)) := by
      have ha0 : 0 ≤ gamma fp.u n :=
        gamma_nonneg_of_valid fp.toStandardAddModel hvalid
      gcongr
    _ = |s| + (2 * fp.u + 2 * gamma fp.u n * (1 + fp.u)) * M := by
      ring
    _ = _ := by rfl

private lemma scalar_bounds (u : ℝ) (hu : 0 ≤ u) (n : ℕ)
    (hsmall : (8 : ℝ) * ((n + 1 : ℕ) : ℝ) * u ≤ 1) :
    let q := 2 * n + 1
    let Q := 4 * (n + 1) - 2
    GammaValid u n ∧ GammaValid u q ∧ GammaValid u Q ∧
      2 * gamma u q ≤ (2 : ℝ) / 3 ∧
      2 * gamma u q ≤ gamma u Q ∧
      gamma u Q ≤ 1 ∧
      1 + u ≤ 2 ∧
      2 * u + 2 * gamma u n * (1 + u) ≤ gamma u Q := by
  dsimp only
  have hm : (1 : ℝ) ≤ (n + 1 : ℕ) := by norm_num
  have hu8 : u ≤ (1 : ℝ) / 8 := by
    have hmpos : 0 < (n + 1 : ℕ) := by positivity
    have hmul : 8 * u ≤ 8 * ((n + 1 : ℕ) : ℝ) * u := by
      nlinarith
    linarith
  have hncast : (0 : ℝ) ≤ n := by positivity
  have hqcast : (((2 * n + 1 : ℕ) : ℝ)) = 2 * (n : ℝ) + 1 := by
    norm_num
  have hQcast : (((4 * (n + 1) - 2 : ℕ) : ℝ)) = 4 * (n : ℝ) + 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ 4 * (n + 1))]
    norm_num
    ring
  have hs : 8 * ((n : ℝ) + 1) * u ≤ 1 := by
    norm_num at hsmall ⊢
    exact hsmall
  have hn_u : (n : ℝ) * u ≤ 1 / 8 := by
    have hnle : (n : ℝ) ≤ (n + 1 : ℕ) := by norm_num
    nlinarith
  have hq_u : ((2 * n + 1 : ℕ) : ℝ) * u ≤ 1 / 4 := by
    rw [hqcast]
    nlinarith [hs]
  have hQ_u : ((4 * (n + 1) - 2 : ℕ) : ℝ) * u ≤ 1 / 2 := by
    rw [hQcast]
    nlinarith [hs]
  have hvn : GammaValid u n := by unfold GammaValid; linarith
  have hvq : GammaValid u (2 * n + 1) := by unfold GammaValid; linarith
  have hvQ : GammaValid u (4 * (n + 1) - 2) := by
    unfold GammaValid
    linarith
  have hdenn : 0 < 1 - (n : ℝ) * u := by linarith
  have hdenq : 0 < 1 - ((2 * n + 1 : ℕ) : ℝ) * u := by linarith
  have hdenQ : 0 < 1 - ((4 * (n + 1) - 2 : ℕ) : ℝ) * u := by
    linarith
  refine ⟨hvn, hvq, hvQ, ?_, ?_, ?_, by linarith, ?_⟩
  · unfold gamma
    calc
      2 * (((2 * n + 1 : ℕ) : ℝ) * u /
          (1 - ((2 * n + 1 : ℕ) : ℝ) * u)) =
          (2 * (((2 * n + 1 : ℕ) : ℝ) * u)) /
            (1 - ((2 * n + 1 : ℕ) : ℝ) * u) := by ring
      _ ≤ (2 : ℝ) / 3 := (div_le_iff₀ hdenq).2 (by nlinarith)
  · unfold gamma
    calc
      2 * (((2 * n + 1 : ℕ) : ℝ) * u /
          (1 - ((2 * n + 1 : ℕ) : ℝ) * u)) =
          (2 * (((2 * n + 1 : ℕ) : ℝ) * u)) /
            (1 - ((2 * n + 1 : ℕ) : ℝ) * u) := by ring
      _ ≤ (((4 * (n + 1) - 2 : ℕ) : ℝ) * u) /
            (1 - ((4 * (n + 1) - 2 : ℕ) : ℝ) * u) := by
        rw [div_le_div_iff₀ hdenq hdenQ]
        rw [hqcast, hQcast]
        rw [← sub_nonneg]
        have heq :
            (4 * (n : ℝ) + 2) * u * (1 - (2 * (n : ℝ) + 1) * u) -
              2 * ((2 * (n : ℝ) + 1) * u) *
                (1 - (4 * (n : ℝ) + 2) * u) =
              2 * ((2 * (n : ℝ) + 1) * u) ^ 2 := by ring
        rw [heq]
        positivity
  · unfold gamma
    exact (div_le_iff₀ hdenQ).2 (by nlinarith)
  · unfold gamma
    calc
      2 * u + 2 * ((n : ℝ) * u / (1 - (n : ℝ) * u)) * (1 + u) =
          (2 * ((n : ℝ) + 1) * u) / (1 - (n : ℝ) * u) := by
        apply (eq_div_iff (ne_of_gt hdenn)).2
        have hfrac :
            ((n : ℝ) * u / (1 - (n : ℝ) * u)) *
                (1 - (n : ℝ) * u) = (n : ℝ) * u := by
          exact div_mul_cancel₀ ((n : ℝ) * u) (ne_of_gt hdenn)
        calc
          (2 * u + 2 * ((n : ℝ) * u / (1 - (n : ℝ) * u)) *
              (1 + u)) * (1 - (n : ℝ) * u) =
            2 * u * (1 - (n : ℝ) * u) +
              2 * (((n : ℝ) * u / (1 - (n : ℝ) * u)) *
                (1 - (n : ℝ) * u)) * (1 + u) := by ring
          _ = 2 * u * (1 - (n : ℝ) * u) +
                2 * ((n : ℝ) * u) * (1 + u) := by rw [hfrac]
          _ = 2 * ((n : ℝ) + 1) * u := by ring
      _ ≤ (((4 * (n + 1) - 2 : ℕ) : ℝ) * u) /
            (1 - ((4 * (n + 1) - 2 : ℕ) : ℝ) * u) := by
        rw [div_le_div_iff₀ hdenn hdenQ]
        rw [hQcast]
        rw [← sub_nonneg]
        have heq :
            (4 * (n : ℝ) + 2) * u * (1 - (n : ℝ) * u) -
              2 * ((n : ℝ) + 1) * u *
                (1 - (4 * (n : ℝ) + 2) * u) =
              2 * (n : ℝ) * u +
                (4 * (n : ℝ) + 2) * ((n : ℝ) + 2) * u ^ 2 := by ring
        rw [heq]
        positivity

theorem p02_t3_dotK_error_bound
    (fp : ErrorFreeDotModel) (n K : ℕ) (x y : Fin (n + 1) → ℝ)
    (hK : 3 ≤ K)
    (hsmall : (8 : ℝ) * ((n + 1 : ℕ) : ℝ) * fp.u ≤ 1) :
    |dotK fp K x y - exactDot x y| ≤
      (fp.u + 2 * (gamma fp.u (4 * (n + 1) - 2)) ^ 2) * |exactDot x y| +
        (gamma fp.u (4 * (n + 1) - 2)) ^ K * dotMagnitude x y := by
  -- PROOF_START P02-T3-H001
  let q : ℕ := 2 * n + 1
  let Q : ℕ := 4 * (n + 1) - 2
  obtain ⟨hvn, hvq, hvQ, _hgtwoThird, htwog, hGone, _huTwo, hraw⟩ :=
    scalar_bounds fp.u fp.u_nonneg n hsmall
  have hqquarter : (q : ℝ) * fp.u ≤ 1 / 4 := by
    have hs : 8 * ((n : ℝ) + 1) * fp.u ≤ 1 := by
      norm_num at hsmall ⊢
      exact hsmall
    have hqcast : (q : ℝ) = 2 * (n : ℝ) + 1 := by
      simp [q]
    rw [hqcast]
    nlinarith
  have hqpos : 1 ≤ q := by simp [q]
  have hL : 2 ≤ K - 1 := by omega
  have hindex : 2 * q = Q := by
    dsimp [q, Q]
    omega
  have hmain := sumK_error_bound fp.toErrorFreeAddModel (N := q)
    (K - 1) hL (dotKTransform fp x y) hqpos hqquarter
  have hdotsum := dotKTransform_sum_eq fp x y
  rw [hdotsum, hindex] at hmain
  have hmain' :
      |dotK fp K x y - exactDot x y| ≤
        (fp.u + 3 * gamma fp.u q ^ 2) * |exactDot x y| +
          gamma fp.u Q ^ (K - 1) *
            ∑ i, |dotKTransform fp x y i| := by
    simpa [dotK, q] using hmain
  have htransformRaw := dotKTransform_magnitude_le fp x y hvn
  have hmag0 : 0 ≤ dotMagnitude x y := by
    unfold dotMagnitude
    exact Finset.sum_nonneg
      (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have htransform :
      (∑ i, |dotKTransform fp x y i|) ≤
        |exactDot x y| + gamma fp.u Q * dotMagnitude x y := by
    calc
      (∑ i, |dotKTransform fp x y i|) ≤
          |exactDot x y| +
            (2 * fp.u + 2 * gamma fp.u n * (1 + fp.u)) *
              dotMagnitude x y := htransformRaw
      _ ≤ |exactDot x y| + gamma fp.u Q * dotMagnitude x y := by
        have hm := mul_le_mul_of_nonneg_right hraw hmag0
        linarith
  have hG0 : 0 ≤ gamma fp.u Q := by
    exact gamma_nonneg_of_valid fp.toStandardAddModel hvQ
  have hg0 : 0 ≤ gamma fp.u q := by
    exact gamma_nonneg_of_valid fp.toStandardAddModel hvq
  have hfour : 4 * gamma fp.u q ^ 2 ≤ gamma fp.u Q ^ 2 := by
    have hdiff : 0 ≤ gamma fp.u Q - 2 * gamma fp.u q := sub_nonneg.mpr htwog
    have hplus : 0 ≤ gamma fp.u Q + 2 * gamma fp.u q := by positivity
    nlinarith [mul_nonneg hdiff hplus]
  have hpowle : gamma fp.u Q ^ (K - 1) ≤ gamma fp.u Q ^ 2 := by
    have hpowOne : gamma fp.u Q ^ (K - 3) ≤ 1 :=
      pow_le_one₀ hG0 hGone
    have he : K - 1 = 2 + (K - 3) := by omega
    rw [he, pow_add]
    nlinarith [mul_nonneg (sq_nonneg (gamma fp.u Q))
      (sub_nonneg.mpr hpowOne)]
  have hcoefficient :
      fp.u + 3 * gamma fp.u q ^ 2 + gamma fp.u Q ^ (K - 1) ≤
        fp.u + 2 * gamma fp.u Q ^ 2 := by
    nlinarith
  have hpowstep :
      gamma fp.u Q ^ (K - 1) * gamma fp.u Q = gamma fp.u Q ^ K := by
    rw [← pow_succ]
    congr 1
    omega
  calc
    |dotK fp K x y - exactDot x y| ≤
        (fp.u + 3 * gamma fp.u q ^ 2) * |exactDot x y| +
          gamma fp.u Q ^ (K - 1) *
            ∑ i, |dotKTransform fp x y i| := hmain'
    _ ≤ (fp.u + 3 * gamma fp.u q ^ 2) * |exactDot x y| +
          gamma fp.u Q ^ (K - 1) *
            (|exactDot x y| + gamma fp.u Q * dotMagnitude x y) := by
      gcongr
    _ = (fp.u + 3 * gamma fp.u q ^ 2 + gamma fp.u Q ^ (K - 1)) *
          |exactDot x y| + gamma fp.u Q ^ K * dotMagnitude x y := by
      rw [← hpowstep]
      ring
    _ ≤ (fp.u + 2 * gamma fp.u Q ^ 2) * |exactDot x y| +
          gamma fp.u Q ^ K * dotMagnitude x y := by
      have hm := mul_le_mul_of_nonneg_right hcoefficient
        (abs_nonneg (exactDot x y))
      linarith
    _ = (fp.u + 2 * (gamma fp.u (4 * (n + 1) - 2)) ^ 2) *
          |exactDot x y| +
        (gamma fp.u (4 * (n + 1) - 2)) ^ K * dotMagnitude x y := by
      rfl

end HighamBench
