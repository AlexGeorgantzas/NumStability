import HighamBench.P02Definitions

namespace HighamBench

open scoped BigOperators

private lemma gamma_nonneg_of_valid {u : ℝ} {m : ℕ}
    (hu : 0 ≤ u) (h : GammaValid u m) : 0 ≤ gamma u m := by
  unfold GammaValid at h
  unfold gamma
  have hd : 0 < 1 - (m : ℝ) * u := by linarith
  positivity

private lemma one_add_gamma_nonneg {u : ℝ} {m : ℕ}
    (hu : 0 ≤ u) (h : GammaValid u m) : 0 ≤ 1 + gamma u m := by
  have := gamma_nonneg_of_valid hu h
  linarith

private lemma gamma_mag_step {u : ℝ} {m : ℕ}
    (hu : 0 ≤ u) (h : GammaValid u (m + 1)) :
    (1 + u) * (1 + gamma u m) ≤ 1 + gamma u (m + 1) := by
  unfold GammaValid at h
  unfold gamma
  push_cast at h ⊢
  have hd0 : 0 < 1 - (m : ℝ) * u := by linarith
  have hd1 : 0 < 1 - ((m : ℝ) + 1) * u := by linarith
  have he0 : 1 + (m : ℝ) * u / (1 - (m : ℝ) * u) =
      1 / (1 - (m : ℝ) * u) := by
    field_simp [ne_of_gt hd0]
    ring
  have he1 : 1 + ((m : ℝ) + 1) * u /
      (1 - ((m : ℝ) + 1) * u) =
      1 / (1 - ((m : ℝ) + 1) * u) := by
    field_simp [ne_of_gt hd1]
    ring
  rw [he0, he1]
  rw [show (1 + u) * (1 / (1 - (m : ℝ) * u)) =
      (1 + u) / (1 - (m : ℝ) * u) by ring]
  rw [div_le_div_iff₀ hd0 hd1]
  have hid : (1 - (m : ℝ) * u) -
      (1 + u) * (1 - ((m : ℝ) + 1) * u) =
      ((m : ℝ) + 1) * u ^ 2 := by ring
  have hsq : 0 ≤ ((m : ℝ) + 1) * u ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg u)
  nlinarith

private lemma gamma_correction_step {u : ℝ} {m : ℕ}
    (hu : 0 ≤ u) (h : GammaValid u (m + 1)) :
    gamma u m + u * (1 + gamma u (m + 1)) ≤ gamma u (m + 1) := by
  unfold GammaValid at h
  unfold gamma
  push_cast at h ⊢
  have hd0 : 0 < 1 - (m : ℝ) * u := by linarith
  have hd1 : 0 < 1 - ((m : ℝ) + 1) * u := by linarith
  have hn : 0 ≤ (m : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hden : 1 - ((m : ℝ) + 1) * u ≤
      1 - (m : ℝ) * u := by nlinarith
  have hfrac : (m : ℝ) * u / (1 - (m : ℝ) * u) ≤
      (m : ℝ) * u / (1 - ((m : ℝ) + 1) * u) :=
    div_le_div_of_nonneg_left hn hd1 hden
  have he1 : 1 + ((m : ℝ) + 1) * u /
      (1 - ((m : ℝ) + 1) * u) =
      1 / (1 - ((m : ℝ) + 1) * u) := by
    field_simp [ne_of_gt hd1]
    ring
  rw [he1]
  calc
    (m : ℝ) * u / (1 - (m : ℝ) * u) +
        u * (1 / (1 - ((m : ℝ) + 1) * u)) ≤
      (m : ℝ) * u / (1 - ((m : ℝ) + 1) * u) +
        u * (1 / (1 - ((m : ℝ) + 1) * u)) := add_le_add hfrac le_rfl
    _ = ((m : ℝ) + 1) * u /
        (1 - ((m : ℝ) + 1) * u) := by
      field_simp [ne_of_gt hd1]

private lemma gamma_final_step {u : ℝ} {m : ℕ}
    (hu : 0 ≤ u) (h : GammaValid u (m + 1)) :
    (1 + u) * gamma u m ≤ gamma u (m + 1) := by
  unfold GammaValid at h
  have hs := gamma_mag_step hu (show GammaValid u (m + 1) by
    exact h)
  nlinarith

private lemma gamma_sum_step {u : ℝ} {m : ℕ}
    (hu : 0 ≤ u) (h : GammaValid u (m + 1)) :
    (1 + u) * gamma u m + u ≤ gamma u (m + 1) := by
  have hs := gamma_mag_step hu h
  nlinarith

private lemma twoSumPrefix_zero (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) :
    twoSumPrefix fp v 0 (Nat.zero_le n) = v ⟨0, Nat.succ_pos n⟩ := by
  simp [twoSumPrefix]

private lemma twoSumPrefix_succ (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 2) → ℝ) :
    twoSumPrefix fp v (n + 1) (by omega) =
      (fp.twoSum
        (twoSumPrefix fp (fun i : Fin (n + 1) ↦ v i.castSucc)
          n (Nat.le_refl n))
        (v (Fin.last (n + 1)))).1 := by
  unfold twoSumPrefix
  rw [Fin.foldl_succ_last]
  congr 3 <;> apply Fin.ext <;> rfl

private lemma twoSumCorrection_castSucc (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 2) → ℝ) (i : Fin n) :
    twoSumCorrection fp v i.castSucc =
      twoSumCorrection fp (fun j : Fin (n + 1) ↦ v j.castSucc) i := by
  rfl

private lemma twoSumCorrection_last (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 2) → ℝ) :
    twoSumCorrection fp v (Fin.last n) =
      (fp.twoSum
        (twoSumPrefix fp (fun i : Fin (n + 1) ↦ v i.castSucc)
          n (Nat.le_refl n))
        (v (Fin.last (n + 1)))).2 := by
  rfl

private lemma twoSumPrefix_abs_le (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (hvalid : GammaValid fp.u n) :
    |twoSumPrefix fp v n (Nat.le_refl n)| ≤
      (1 + gamma fp.u n) * ∑ i : Fin (n + 1), |v i| := by
  induction n with
  | zero =>
      simp [twoSumPrefix, gamma]
  | succ n ih =>
      let w : Fin (n + 1) → ℝ := fun i ↦ v i.castSucc
      have hvalid' : GammaValid fp.u n := by
        unfold GammaValid at hvalid ⊢
        push_cast at hvalid ⊢
        nlinarith [fp.u_nonneg]
      have hi := ih w hvalid'
      obtain ⟨δ, hδ, heq⟩ := fp.model_add
        (twoSumPrefix fp w n (Nat.le_refl n)) (v (Fin.last (n + 1)))
      have hfac : |1 + δ| ≤ 1 + fp.u := by
        calc
          |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
          _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
      have hfac0 : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
      have hgn : 0 ≤ gamma fp.u n :=
        gamma_nonneg_of_valid fp.u_nonneg hvalid'
      have hsum : 0 ≤ ∑ i : Fin (n + 1), |w i| := by positivity
      have hlast : 0 ≤ |v (Fin.last (n + 1))| := abs_nonneg _
      rw [twoSumPrefix_succ, fp.twoSum_high, heq, abs_mul]
      calc
        |twoSumPrefix fp w n (Nat.le_refl n) + v (Fin.last (n + 1))| *
            |1 + δ| ≤
          (|twoSumPrefix fp w n (Nat.le_refl n)| +
            |v (Fin.last (n + 1))|) * (1 + fp.u) :=
              mul_le_mul (abs_add_le _ _) hfac (abs_nonneg _)
                (by positivity)
        _ ≤ ((1 + gamma fp.u n) * (∑ i : Fin (n + 1), |w i|) +
              |v (Fin.last (n + 1))|) * (1 + fp.u) :=
            mul_le_mul_of_nonneg_right (add_le_add hi le_rfl) hfac0
        _ ≤ ((1 + gamma fp.u n) *
              ((∑ i : Fin (n + 1), |w i|) + |v (Fin.last (n + 1))|)) *
              (1 + fp.u) := by
            gcongr
            nlinarith
        _ = ((1 + fp.u) * (1 + gamma fp.u n)) *
              ((∑ i : Fin (n + 1), |w i|) + |v (Fin.last (n + 1))|) := by
            ring
        _ ≤ (1 + gamma fp.u (n + 1)) *
              ((∑ i : Fin (n + 1), |w i|) + |v (Fin.last (n + 1))|) := by
            gcongr
            exact gamma_mag_step fp.u_nonneg hvalid
        _ = (1 + gamma fp.u (n + 1)) *
              ∑ i : Fin (n + 2), |v i| := by
            congr 1
            rw [Fin.sum_univ_castSucc (fun i ↦ |v i|)]

private lemma twoSum_exact_sum (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) :
    twoSumPrefix fp v n (Nat.le_refl n) +
        ∑ i : Fin n, twoSumCorrection fp v i =
      ∑ i : Fin (n + 1), v i := by
  induction n with
  | zero =>
      simp [twoSumPrefix]
  | succ n ih =>
      let w : Fin (n + 1) → ℝ := fun i ↦ v i.castSucc
      have hi := ih w
      have he := fp.twoSum_exact
        (twoSumPrefix fp w n (Nat.le_refl n)) (v (Fin.last (n + 1)))
      rw [twoSumPrefix_succ]
      rw [Fin.sum_univ_castSucc
        (fun i : Fin (n + 1) ↦ twoSumCorrection fp v i)]
      simp_rw [twoSumCorrection_castSucc]
      rw [twoSumCorrection_last]
      rw [Fin.sum_univ_castSucc (fun i ↦ v i)]
      calc
        (fp.twoSum (twoSumPrefix fp w n (Nat.le_refl n))
              (v (Fin.last (n + 1)))).1 +
            ((∑ i : Fin n, twoSumCorrection fp w i) +
              (fp.twoSum (twoSumPrefix fp w n (Nat.le_refl n))
                (v (Fin.last (n + 1)))).2) =
          ((fp.twoSum (twoSumPrefix fp w n (Nat.le_refl n))
              (v (Fin.last (n + 1)))).1 +
            (fp.twoSum (twoSumPrefix fp w n (Nat.le_refl n))
              (v (Fin.last (n + 1)))).2) +
              ∑ i : Fin n, twoSumCorrection fp w i := by ring
        _ = (twoSumPrefix fp w n (Nat.le_refl n) +
              v (Fin.last (n + 1))) +
              ∑ i : Fin n, twoSumCorrection fp w i := by rw [he]
        _ = (twoSumPrefix fp w n (Nat.le_refl n) +
              ∑ i : Fin n, twoSumCorrection fp w i) +
              v (Fin.last (n + 1)) := by ring
        _ = (∑ i : Fin (n + 1), w i) + v (Fin.last (n + 1)) := by rw [hi]

private lemma twoSum_corrections_abs_le (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (hvalid : GammaValid fp.u n) :
    (∑ i : Fin n, |twoSumCorrection fp v i|) ≤
      gamma fp.u n * ∑ i : Fin (n + 1), |v i| := by
  induction n with
  | zero =>
      simp [gamma]
  | succ n ih =>
      let w : Fin (n + 1) → ℝ := fun i ↦ v i.castSucc
      have hvalid' : GammaValid fp.u n := by
        unfold GammaValid at hvalid ⊢
        push_cast at hvalid ⊢
        nlinarith [fp.u_nonneg]
      have hi := ih w hvalid'
      have hp := twoSumPrefix_abs_le fp v hvalid
      rw [twoSumPrefix_succ] at hp
      have hlow := fp.twoSum_low_le
        (twoSumPrefix fp w n (Nat.le_refl n)) (v (Fin.last (n + 1)))
      have hlow' :
          |(fp.twoSum (twoSumPrefix fp w n (Nat.le_refl n))
              (v (Fin.last (n + 1)))).2| ≤
            fp.u * ((1 + gamma fp.u (n + 1)) *
              ∑ i : Fin (n + 2), |v i|) :=
        hlow.trans (mul_le_mul_of_nonneg_left hp fp.u_nonneg)
      have hgn : 0 ≤ gamma fp.u n :=
        gamma_nonneg_of_valid fp.u_nonneg hvalid'
      have hsumw : 0 ≤ ∑ i : Fin (n + 1), |w i| := by positivity
      have hlast : 0 ≤ |v (Fin.last (n + 1))| := abs_nonneg _
      have hsum : 0 ≤ ∑ i : Fin (n + 2), |v i| := by positivity
      rw [Fin.sum_univ_castSucc
        (fun i : Fin (n + 1) ↦ |twoSumCorrection fp v i|)]
      simp_rw [twoSumCorrection_castSucc]
      rw [twoSumCorrection_last]
      calc
        (∑ i : Fin n, |twoSumCorrection fp w i|) +
            |(fp.twoSum (twoSumPrefix fp w n (Nat.le_refl n))
              (v (Fin.last (n + 1)))).2| ≤
          gamma fp.u n * (∑ i : Fin (n + 1), |w i|) +
            fp.u * ((1 + gamma fp.u (n + 1)) *
              ∑ i : Fin (n + 2), |v i|) := add_le_add hi hlow'
        _ ≤ gamma fp.u n * (∑ i : Fin (n + 2), |v i|) +
            fp.u * ((1 + gamma fp.u (n + 1)) *
              ∑ i : Fin (n + 2), |v i|) := by
          gcongr
          rw [Fin.sum_univ_castSucc (fun i ↦ |v i|)]
          exact le_add_of_nonneg_right hlast
        _ = (gamma fp.u n + fp.u * (1 + gamma fp.u (n + 1))) *
              ∑ i : Fin (n + 2), |v i| := by ring
        _ ≤ gamma fp.u (n + 1) * ∑ i : Fin (n + 2), |v i| :=
          mul_le_mul_of_nonneg_right
            (gamma_correction_step fp.u_nonneg hvalid) hsum

private lemma recursiveSum_succ (flAdd : ℝ → ℝ → ℝ) (n : ℕ)
    (v : Fin (n + 2) → ℝ) :
    recursiveSum flAdd (n + 2) v =
      flAdd (recursiveSum flAdd (n + 1) (fun i ↦ v i.castSucc))
        (v (Fin.last (n + 1))) := by
  simp [recursiveSum]

private lemma recursiveSum_error_le (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (hvalid : GammaValid fp.u n) :
    |recursiveSum fp.fl_add (n + 1) v - ∑ i : Fin (n + 1), v i| ≤
      gamma fp.u n * ∑ i : Fin (n + 1), |v i| := by
  induction n with
  | zero =>
      simp [recursiveSum, gamma]
  | succ n ih =>
      let w : Fin (n + 1) → ℝ := fun i ↦ v i.castSucc
      have hvalid' : GammaValid fp.u n := by
        unfold GammaValid at hvalid ⊢
        push_cast at hvalid ⊢
        nlinarith [fp.u_nonneg]
      have hi := ih w hvalid'
      obtain ⟨δ, hδ, heq⟩ := fp.model_add
        (recursiveSum fp.fl_add (n + 1) w) (v (Fin.last (n + 1)))
      have hfac : |1 + δ| ≤ 1 + fp.u := by
        calc
          |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
          _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
      have hfac0 : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
      have hgn : 0 ≤ gamma fp.u n :=
        gamma_nonneg_of_valid fp.u_nonneg hvalid'
      have hsumw : 0 ≤ ∑ i : Fin (n + 1), |w i| := by positivity
      have hlast : 0 ≤ |v (Fin.last (n + 1))| := abs_nonneg _
      have habsw : |∑ i : Fin (n + 1), w i| ≤
          ∑ i : Fin (n + 1), |w i| := by
        simpa using Finset.abs_sum_le_sum_abs w Finset.univ
      have habsall :
          |(∑ i : Fin (n + 1), w i) + v (Fin.last (n + 1))| ≤
            (∑ i : Fin (n + 1), |w i|) + |v (Fin.last (n + 1))| :=
        (abs_add_le _ _).trans (add_le_add habsw le_rfl)
      rw [recursiveSum_succ]
      rw [Fin.sum_univ_castSucc (fun i ↦ v i), heq]
      calc
        |(recursiveSum fp.fl_add (n + 1) w + v (Fin.last (n + 1))) *
              (1 + δ) -
            ((∑ i : Fin (n + 1), w i) + v (Fin.last (n + 1)))| =
          |(1 + δ) * (recursiveSum fp.fl_add (n + 1) w -
              ∑ i : Fin (n + 1), w i) +
            δ * ((∑ i : Fin (n + 1), w i) +
              v (Fin.last (n + 1)))| := by
                congr 1
                ring
        _ ≤ |1 + δ| *
              |recursiveSum fp.fl_add (n + 1) w -
                ∑ i : Fin (n + 1), w i| +
            |δ| * |(∑ i : Fin (n + 1), w i) +
              v (Fin.last (n + 1))| := by
                simpa only [abs_mul] using
                  (abs_add_le
                    ((1 + δ) * (recursiveSum fp.fl_add (n + 1) w -
                      ∑ i : Fin (n + 1), w i))
                    (δ * ((∑ i : Fin (n + 1), w i) +
                      v (Fin.last (n + 1)))))
        _ ≤ (1 + fp.u) *
              (gamma fp.u n * ∑ i : Fin (n + 1), |w i|) +
            fp.u * ((∑ i : Fin (n + 1), |w i|) +
              |v (Fin.last (n + 1))|) := by
                exact add_le_add
                  (mul_le_mul hfac hi (abs_nonneg _)
                    hfac0)
                  (mul_le_mul hδ habsall (abs_nonneg _) fp.u_nonneg)
        _ ≤ (1 + fp.u) *
              (gamma fp.u n * ((∑ i : Fin (n + 1), |w i|) +
                |v (Fin.last (n + 1))|)) +
            fp.u * ((∑ i : Fin (n + 1), |w i|) +
              |v (Fin.last (n + 1))|) := by
                gcongr
                exact le_add_of_nonneg_right hlast
        _ = ((1 + fp.u) * gamma fp.u n + fp.u) *
              ((∑ i : Fin (n + 1), |w i|) +
                |v (Fin.last (n + 1))|) := by ring
        _ ≤ gamma fp.u (n + 1) *
              ((∑ i : Fin (n + 1), |w i|) +
                |v (Fin.last (n + 1))|) := by
              gcongr
              exact gamma_sum_step fp.u_nonneg hvalid
        _ = gamma fp.u (n + 1) * ∑ i : Fin (n + 2), |v i| := by
              congr 1
              rw [Fin.sum_univ_castSucc (fun i ↦ |v i|)]

@[simp] private lemma vecSum_castSucc (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (i : Fin n) :
    vecSum fp v i.castSucc = twoSumCorrection fp v i := by
  simp [vecSum]

@[simp] private lemma vecSum_last (fp : ErrorFreeAddModel) {n : ℕ}
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
      have hv : vecSum fp v 0 = v 0 := by
        unfold vecSum
        have hz : (0 : Fin (0 + 1)) = Fin.last 0 := by ext; rfl
        calc
          Fin.lastCases (twoSumPrefix fp v 0 (Nat.le_refl 0))
              (twoSumCorrection fp v) 0 =
            Fin.lastCases (twoSumPrefix fp v 0 (Nat.le_refl 0))
              (twoSumCorrection fp v) (Fin.last 0) := congrArg _ hz
          _ = twoSumPrefix fp v 0 (Nat.le_refl 0) := Fin.lastCases_last
          _ = v 0 := by simp [twoSumPrefix]
      simp [sum2, sumK, iteratedVecSum, recursiveSum, gamma, hv]
      exact mul_nonneg fp.u_nonneg (abs_nonneg _)
  | succ n =>
      let c : Fin (n + 1) → ℝ := fun i ↦ twoSumCorrection fp v i
      let H : ℝ := twoSumPrefix fp v (n + 1) (Nat.le_refl (n + 1))
      let r : ℝ := recursiveSum fp.fl_add (n + 1) c
      let s : ℝ := ∑ i : Fin (n + 2), v i
      let S : ℝ := ∑ i : Fin (n + 2), |v i|
      have hvalidCorr : GammaValid fp.u (n + 1) := by
        unfold GammaValid at hvalid ⊢
        push_cast at hvalid ⊢
        nlinarith [fp.u_nonneg]
      have hvalidRec : GammaValid fp.u n := by
        unfold GammaValid at hvalid ⊢
        push_cast at hvalid ⊢
        nlinarith [fp.u_nonneg]
      have hre : |r - ∑ i : Fin (n + 1), c i| ≤
          gamma fp.u n * ∑ i : Fin (n + 1), |c i| := by
        exact recursiveSum_error_le fp c hvalidRec
      have hc : (∑ i : Fin (n + 1), |c i|) ≤
          gamma fp.u (n + 1) * S := by
        exact twoSum_corrections_abs_le fp v hvalidCorr
      have hexact : H + ∑ i : Fin (n + 1), c i = s := by
        exact twoSum_exact_sum fp v
      obtain ⟨δ, hδ, heq⟩ := fp.model_add r H
      have hfac : |1 + δ| ≤ 1 + fp.u := by
        calc
          |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
          _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
      have hfac0 : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
      have hgn : 0 ≤ gamma fp.u n :=
        gamma_nonneg_of_valid fp.u_nonneg hvalidRec
      have hgn1 : 0 ≤ gamma fp.u (n + 1) :=
        gamma_nonneg_of_valid fp.u_nonneg hvalidCorr
      have hcabs0 : 0 ≤ ∑ i : Fin (n + 1), |c i| := by positivity
      have hS0 : 0 ≤ S := by positivity
      change |recursiveSum fp.fl_add (n + 2) (vecSum fp v) - s| ≤
        fp.u * |s| + (gamma fp.u (n + 1)) ^ 2 * S
      rw [recursiveSum_succ]
      rw [show (fun i : Fin (n + 1) ↦ vecSum fp v i.castSucc) = c by
        funext i
        simp [c]]
      rw [show vecSum fp v (Fin.last (n + 1)) = H by simp [H]]
      change |fp.fl_add r H - s| ≤
        fp.u * |s| + (gamma fp.u (n + 1)) ^ 2 * S
      rw [heq]
      calc
        |(r + H) * (1 + δ) - s| =
          |(1 + δ) * (r - ∑ i : Fin (n + 1), c i) + δ * s| := by
            congr 1
            rw [← hexact]
            ring
        _ ≤ |1 + δ| * |r - ∑ i : Fin (n + 1), c i| +
            |δ| * |s| := by
              simpa only [abs_mul] using
                (abs_add_le
                  ((1 + δ) * (r - ∑ i : Fin (n + 1), c i)) (δ * s))
        _ ≤ (1 + fp.u) *
              (gamma fp.u n * ∑ i : Fin (n + 1), |c i|) +
            fp.u * |s| := by
              exact add_le_add
                (mul_le_mul hfac hre (abs_nonneg _) hfac0)
                (mul_le_mul_of_nonneg_right hδ (abs_nonneg s))
        _ = ((1 + fp.u) * gamma fp.u n) *
              (∑ i : Fin (n + 1), |c i|) + fp.u * |s| := by ring
        _ ≤ gamma fp.u (n + 1) *
              (∑ i : Fin (n + 1), |c i|) + fp.u * |s| := by
              exact add_le_add
                (mul_le_mul_of_nonneg_right
                  (gamma_final_step fp.u_nonneg hvalidCorr) hcabs0) le_rfl
        _ ≤ gamma fp.u (n + 1) *
              (gamma fp.u (n + 1) * S) + fp.u * |s| := by
              exact add_le_add (mul_le_mul_of_nonneg_left hc hgn1) le_rfl
        _ = fp.u * |s| + (gamma fp.u (n + 1)) ^ 2 * S := by ring

end HighamBench
