import HighamBench.P02Definitions
import NumStability.Algorithms.Summation.Recursive.Core

namespace HighamBench

open scoped BigOperators

lemma fin_prefix_abs_sum_le {m n : ℕ} (h : m ≤ n) (v : Fin n → ℝ) :
    (∑ i : Fin m, |v ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩|) ≤
      ∑ i : Fin n, |v i| := by
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      simp
  | succ n ih =>
      by_cases hm : m = n + 1
      · subst m
        apply le_of_eq
        apply Finset.sum_congr rfl
        intro i _
        congr
      · have hmn : m ≤ n := by omega
        calc
          (∑ i : Fin m, |v ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩|) =
              ∑ i : Fin m,
                |(fun j : Fin n => v j.castSucc)
                  ⟨i.val, Nat.lt_of_lt_of_le i.isLt hmn⟩| := by
                    apply Finset.sum_congr rfl
                    intro i _
                    congr
          _ ≤ ∑ i : Fin n, |v i.castSucc| :=
            ih hmn (fun i : Fin n => v i.castSucc)
          _ ≤ (∑ i : Fin n, |v i.castSucc|) + |v (Fin.last n)| :=
            le_add_of_nonneg_right (abs_nonneg _)
          _ = ∑ i : Fin (n + 1), |v i| :=
            (Fin.sum_univ_castSucc (fun i : Fin (n + 1) => |v i|)).symm

noncomputable def ErrorFreeAddModel.toFPModel (fp : ErrorFreeAddModel) :
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

lemma recursiveSum_eq_fl_recursiveSum (fp : ErrorFreeAddModel) :
    ∀ (m : ℕ) (w : Fin m → ℝ),
      recursiveSum fp.fl_add m w =
        NumStability.fl_recursiveSum fp.toFPModel m w
  | 0, w => by simp [recursiveSum, NumStability.fl_recursiveSum]
  | 1, w => by
      simp only [recursiveSum, NumStability.fl_recursiveSum, Fin.foldl_succ,
        ErrorFreeAddModel.toFPModel, Fin.isValue, ↓reduceDIte, Fin.foldl_zero]
      exact (fp.fl_add_zero (w 0)).symm
  | m + 2, w => by
      rw [recursiveSum]
      simp only [show m + 1 ≠ 0 by omega, ↓reduceDIte]
      rw [NumStability.fl_recursiveSum, Fin.foldl_succ_last]
      change fp.fl_add
          (recursiveSum fp.fl_add (m + 1) (fun i => w i.castSucc))
          (w (Fin.last (m + 1))) =
        fp.fl_add
          (NumStability.fl_recursiveSum fp.toFPModel (m + 1)
            (fun i => w i.castSucc))
          (w (Fin.last (m + 1)))
      rw [recursiveSum_eq_fl_recursiveSum fp (m + 1)]

lemma recursiveSum_forward_error_bound (fp : ErrorFreeAddModel)
    (m : ℕ) (w : Fin m → ℝ) (hvalid : GammaValid fp.u (m - 1)) :
    |recursiveSum fp.fl_add m w - ∑ i : Fin m, w i| ≤
      gamma fp.u (m - 1) * ∑ i : Fin m, |w i| := by
  rw [recursiveSum_eq_fl_recursiveSum fp m w]
  simpa [GammaValid, gamma, NumStability.gammaValid, NumStability.gamma,
    ErrorFreeAddModel.toFPModel] using
    (NumStability.recursiveSum_forward_error_bound fp.toFPModel m w
      (by simpa [GammaValid, NumStability.gammaValid,
        ErrorFreeAddModel.toFPModel] using hvalid))

lemma twoSumPrefix_eq_fl_recursiveSum (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : k ≤ n) :
    twoSumPrefix fp v k hk =
      NumStability.fl_recursiveSum fp.toFPModel (k + 1)
        (fun i => v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩) := by
  rw [NumStability.fl_recursiveSum, Fin.foldl_succ]
  simp only [ErrorFreeAddModel.toFPModel, fp.fl_add_zero]
  unfold twoSumPrefix
  congr 1
  funext s i
  rw [fp.twoSum_high]
  congr 2

lemma twoSumPrefix_abs_le (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : k ≤ n)
    (hvalid : GammaValid fp.u (n + 1)) :
    |twoSumPrefix fp v k hk| ≤
      (1 + gamma fp.u n) * ∑ i : Fin (n + 1), |v i| := by
  let pref : Fin (k + 1) → ℝ := fun i =>
    v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩
  have hnvalid : NumStability.gammaValid fp.toFPModel n := by
    unfold GammaValid at hvalid
    unfold NumStability.gammaValid
    dsimp [ErrorFreeAddModel.toFPModel]
    have hle : (n : ℝ) * fp.u ≤ ((n + 1 : ℕ) : ℝ) * fp.u := by
      gcongr
      · exact fp.u_nonneg
      · omega
    linarith
  have hkvalid : NumStability.gammaValid fp.toFPModel k :=
    NumStability.gammaValid_mono fp.toFPModel hk hnvalid
  have hrec := NumStability.recursiveSum_abs_le_one_add_gamma_mul_sum_abs
    fp.toFPModel (k + 1) pref (by simpa using hkvalid)
  have hgam : gamma fp.u k ≤ gamma fp.u n := by
    simpa [gamma, NumStability.gamma, ErrorFreeAddModel.toFPModel] using
      (NumStability.gamma_mono fp.toFPModel hk hnvalid)
  have hgam_nonneg : 0 ≤ gamma fp.u n := by
    simpa [gamma, NumStability.gamma, ErrorFreeAddModel.toFPModel] using
      (NumStability.gamma_nonneg fp.toFPModel hnvalid)
  have hpref : (∑ i : Fin (k + 1), |pref i|) ≤
      ∑ i : Fin (n + 1), |v i| := by
    exact fin_prefix_abs_sum_le (Nat.succ_le_succ hk) v
  rw [twoSumPrefix_eq_fl_recursiveSum fp v k hk]
  calc
    |NumStability.fl_recursiveSum fp.toFPModel (k + 1) pref| ≤
        (1 + gamma fp.u k) * ∑ i : Fin (k + 1), |pref i| := by
          simpa [pref, gamma, NumStability.gamma,
            ErrorFreeAddModel.toFPModel] using hrec
    _ ≤ (1 + gamma fp.u n) * ∑ i : Fin (k + 1), |pref i| :=
      mul_le_mul_of_nonneg_right (by linarith) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    _ ≤ (1 + gamma fp.u n) * ∑ i : Fin (n + 1), |v i| :=
      mul_le_mul_of_nonneg_left hpref (by linarith)

lemma twoSumPrefix_succ (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : k < n) :
    twoSumPrefix fp v (k + 1) (Nat.succ_le_iff.mpr hk) =
      (fp.twoSum
        (twoSumPrefix fp v k (Nat.le_of_lt hk))
        (v ⟨k + 1, Nat.succ_lt_succ hk⟩)).1 := by
  unfold twoSumPrefix
  rw [Fin.foldl_succ_last]
  congr 2

lemma twoSumCorrection_abs_le (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (i : Fin n)
    (hvalid : GammaValid fp.u (n + 1)) :
    |twoSumCorrection fp v i| ≤
      fp.u * (1 + gamma fp.u n) * ∑ j : Fin (n + 1), |v j| := by
  have hs := twoSumPrefix_succ fp v i.val i.isLt
  have hp := twoSumPrefix_abs_le fp v (i.val + 1)
    (Nat.succ_le_iff.mpr i.isLt) hvalid
  unfold twoSumCorrection
  calc
    |(fp.twoSum
        (twoSumPrefix fp v i.val (Nat.le_of_lt i.isLt))
        (v ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)).2| ≤
        fp.u * |(fp.twoSum
          (twoSumPrefix fp v i.val (Nat.le_of_lt i.isLt))
          (v ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)).1| :=
      fp.twoSum_low_le _ _
    _ = fp.u *
        |twoSumPrefix fp v (i.val + 1) (Nat.succ_le_iff.mpr i.isLt)| := by
      rw [hs]
    _ ≤ fp.u *
        ((1 + gamma fp.u n) * ∑ j : Fin (n + 1), |v j|) :=
      mul_le_mul_of_nonneg_left hp fp.u_nonneg
    _ = fp.u * (1 + gamma fp.u n) *
        ∑ j : Fin (n + 1), |v j| := by ring

lemma nat_mul_u_mul_one_add_gamma (u : ℝ) (n : ℕ)
    (hvalid : GammaValid u n) :
    (n : ℝ) * u * (1 + gamma u n) = gamma u n := by
  unfold GammaValid at hvalid
  have hden : 1 - (n : ℝ) * u ≠ 0 := by linarith
  unfold gamma
  field_simp [hden]
  ring

lemma twoSumCorrections_abs_sum_le (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (hvalid : GammaValid fp.u (n + 1)) :
    (∑ i : Fin n, |twoSumCorrection fp v i|) ≤
      gamma fp.u n * ∑ j : Fin (n + 1), |v j| := by
  have hnvalid : GammaValid fp.u n := by
    unfold GammaValid at hvalid ⊢
    have hle : (n : ℝ) * fp.u ≤ ((n + 1 : ℕ) : ℝ) * fp.u := by
      gcongr
      · exact fp.u_nonneg
      · omega
    linarith
  calc
    (∑ i : Fin n, |twoSumCorrection fp v i|) ≤
        ∑ _i : Fin n,
          (fp.u * (1 + gamma fp.u n) * ∑ j : Fin (n + 1), |v j|) :=
      Finset.sum_le_sum fun i _ => twoSumCorrection_abs_le fp v i hvalid
    _ = ((n : ℝ) * fp.u * (1 + gamma fp.u n)) *
        ∑ j : Fin (n + 1), |v j| := by
      simp
      ring
    _ = gamma fp.u n * ∑ j : Fin (n + 1), |v j| := by
      rw [nat_mul_u_mul_one_add_gamma fp.u n hnvalid]

lemma twoSumPrefix_add_corrections_eq_sum (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) : ∀ (k : ℕ) (hk : k ≤ n),
    twoSumPrefix fp v k hk +
        ∑ i : Fin k,
          twoSumCorrection fp v
            ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ =
      ∑ i : Fin (k + 1),
        v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩
  | 0, hk => by
      simp [twoSumPrefix]
  | k + 1, hk => by
      have hkn : k < n := by omega
      have hk0 : k ≤ n := Nat.le_of_lt hkn
      have ih := twoSumPrefix_add_corrections_eq_sum fp v k hk0
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      have hs := twoSumPrefix_succ fp v k hkn
      have hex := fp.twoSum_exact
        (twoSumPrefix fp v k hk0)
        (v ⟨k + 1, Nat.succ_lt_succ hkn⟩)
      simp only [twoSumCorrection, Fin.val_last, Fin.coe_castSucc]
      rw [hs]
      simp only [twoSumCorrection] at ih
      nlinarith [hex, ih]

lemma vecSum_sum_eq (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1), vecSum fp v i) = ∑ i : Fin (n + 1), v i := by
  rw [Fin.sum_univ_castSucc]
  simp only [vecSum, Fin.lastCases_castSucc, Fin.lastCases_last]
  have h := twoSumPrefix_add_corrections_eq_sum fp v n (Nat.le_refl n)
  linarith

lemma one_add_u_mul_gamma_le_succ (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hvalid : GammaValid u (k + 1)) :
    (1 + u) * gamma u k ≤ gamma u (k + 1) := by
  unfold GammaValid at hvalid
  have hk : (0 : ℝ) < 1 - (k : ℝ) * u := by
    have hku : (k : ℝ) * u ≤ ((k + 1 : ℕ) : ℝ) * u := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ k) hu
    linarith
  have hks : (0 : ℝ) < 1 - ((k + 1 : ℕ) : ℝ) * u := by linarith
  have hks' : (0 : ℝ) < 1 - ((k : ℝ) + 1) * u := by
    exact_mod_cast hks
  have hid :
      gamma u (k + 1) - (1 + u) * gamma u k =
        (u * (1 - (k : ℝ) * u +
          (k : ℝ) * ((k + 1 : ℕ) : ℝ) * u ^ 2)) /
          ((1 - (k : ℝ) * u) *
            (1 - ((k + 1 : ℕ) : ℝ) * u)) := by
    unfold gamma
    push_cast
    field_simp [ne_of_gt hk, ne_of_gt hks']
    ring
  rw [← sub_nonneg, hid]
  exact div_nonneg
    (mul_nonneg hu (add_nonneg (le_of_lt hk)
      (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (sq_nonneg u))))
    (mul_nonneg (le_of_lt hk) (le_of_lt hks))

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
      rw [show (0 : Fin 1) = Fin.last 0 by ext; simp,
        Fin.lastCases_last]
      simpa using mul_nonneg fp.u_nonneg (abs_nonneg (v (Fin.last 0)))
  | succ k =>
      let w : Fin (k + 2) → ℝ := vecSum fp v
      let c : Fin (k + 1) → ℝ := fun i => w i.castSucc
      let sigma : ℝ := recursiveSum fp.fl_add (k + 1) c
      let p : ℝ := w (Fin.last (k + 1))
      let q : ℝ := ∑ i : Fin (k + 1), c i
      let s : ℝ := ∑ i : Fin (k + 2), v i
      let A : ℝ := ∑ i : Fin (k + 1), |c i|
      let S : ℝ := ∑ i : Fin (k + 2), |v i|
      have hsum2 : sum2 fp v = fp.fl_add sigma p := by
        dsimp [sigma, p, c, w]
        simp only [sum2, sumK, iteratedVecSum, Nat.reduceSubDiff]
        rw [recursiveSum]
        simp only [show k + 1 ≠ 0 by omega, ↓reduceDIte]
      have hpres0 := vecSum_sum_eq fp v
      rw [Fin.sum_univ_castSucc] at hpres0
      have hpres : q + p = s := by
        simpa [q, p, s, c, w] using hpres0
      have hcorr0 := twoSumCorrections_abs_sum_le fp v hvalid
      have hcorr : A ≤ gamma fp.u (k + 1) * S := by
        simpa [A, S, c, w, vecSum] using hcorr0
      have hkvalid : GammaValid fp.u k := by
        unfold GammaValid at hvalid ⊢
        have hle : (k : ℝ) * fp.u ≤ ((k + 2 : ℕ) : ℝ) * fp.u := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show k ≤ k + 2 by omega))
            fp.u_nonneg
        linarith
      have hnvalid : GammaValid fp.u (k + 1) := by
        unfold GammaValid at hvalid ⊢
        have hle : ((k + 1 : ℕ) : ℝ) * fp.u ≤
            ((k + 2 : ℕ) : ℝ) * fp.u := by
          exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast (show k + 1 ≤ k + 2 by omega)) fp.u_nonneg
        linarith
      have hrec0 := recursiveSum_forward_error_bound fp (k + 1) c
        (by simpa using hkvalid)
      have hrec : |sigma - q| ≤ gamma fp.u k * A := by
        simpa [sigma, q, A] using hrec0
      have hcoef : (1 + fp.u) * gamma fp.u k ≤ gamma fp.u (k + 1) :=
        one_add_u_mul_gamma_le_succ fp.u k fp.u_nonneg hnvalid
      have hgam_nonneg : 0 ≤ gamma fp.u (k + 1) := by
        let m := fp.toFPModel
        have hmvalid : NumStability.gammaValid m (k + 1) := by
          simpa [m, GammaValid, NumStability.gammaValid,
            ErrorFreeAddModel.toFPModel] using hnvalid
        simpa [m, gamma, NumStability.gamma,
          ErrorFreeAddModel.toFPModel] using
          (NumStability.gamma_nonneg m hmvalid)
      have hA_nonneg : 0 ≤ A := by
        dsimp [A]
        positivity
      obtain ⟨δ, hδ, hfl⟩ := fp.model_add sigma p
      have hone : |1 + δ| ≤ 1 + fp.u := by
        calc
          |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
          _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
      have herr : sum2 fp v - s =
          (1 + δ) * (sigma - q) + δ * s := by
        rw [hsum2, hfl, ← hpres]
        ring
      have hfirst :
          (1 + fp.u) * (gamma fp.u k * A) ≤
            (gamma fp.u (k + 1)) ^ 2 * S := by
        calc
          (1 + fp.u) * (gamma fp.u k * A) =
              ((1 + fp.u) * gamma fp.u k) * A := by ring
          _ ≤ gamma fp.u (k + 1) * A :=
            mul_le_mul_of_nonneg_right hcoef hA_nonneg
          _ ≤ gamma fp.u (k + 1) *
              (gamma fp.u (k + 1) * S) :=
            mul_le_mul_of_nonneg_left hcorr hgam_nonneg
          _ = (gamma fp.u (k + 1)) ^ 2 * S := by ring
      change |sum2 fp v - s| ≤
        fp.u * |s| + (gamma fp.u (k + 1)) ^ 2 * S
      rw [herr]
      calc
        |(1 + δ) * (sigma - q) + δ * s| ≤
            |1 + δ| * |sigma - q| + |δ| * |s| := by
          simpa only [abs_mul] using
            (abs_add_le ((1 + δ) * (sigma - q)) (δ * s))
        _ ≤ (1 + fp.u) * (gamma fp.u k * A) + fp.u * |s| := by
          exact add_le_add
            (mul_le_mul hone hrec (abs_nonneg _) (by linarith [fp.u_nonneg]))
            (mul_le_mul_of_nonneg_right hδ (abs_nonneg _))
        _ ≤ fp.u * |s| + (gamma fp.u (k + 1)) ^ 2 * S := by
          linarith

end HighamBench
