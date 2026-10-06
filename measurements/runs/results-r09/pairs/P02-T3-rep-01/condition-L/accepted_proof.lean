import HighamBench.P02Definitions

namespace HighamBench

open scoped BigOperators

lemma twoSumPrefix_succ_eq (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : k + 1 ≤ n) :
    twoSumPrefix fp v (k + 1) hk =
      (fp.twoSum (twoSumPrefix fp v k (Nat.le_trans (Nat.le_succ k) hk))
        (v ⟨k + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)⟩)).1 := by
  unfold twoSumPrefix
  rw [Fin.foldl_succ_last]
  rfl

lemma twoSumPrefix_exact_aux (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : k ≤ n) :
    twoSumPrefix fp v k hk +
        ∑ i : Fin k,
          twoSumCorrection fp v
            ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ =
      ∑ i : Fin (k + 1),
        v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩ := by
  induction k with
  | zero =>
      simp [twoSumPrefix]
  | succ k ih =>
      have hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      rw [twoSumPrefix_succ_eq fp v k hk]
      simp only [Fin.coe_castSucc, Fin.val_last]
      unfold twoSumCorrection
      have hex := fp.twoSum_exact
        (twoSumPrefix fp v k hk')
        (v ⟨k + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)⟩)
      have hih := ih hk'
      simp only [twoSumCorrection] at hih
      linear_combination hex + hih

lemma gamma_nonneg_of_lt (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : (k : ℝ) * u < 1) : 0 ≤ gamma u k := by
  unfold gamma
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg k) hu) (sub_nonneg.mpr (le_of_lt hk))

lemma gamma_succ_increment_bound (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : ((k + 1 : ℕ) : ℝ) * u < 1) :
    u * (1 + u) * (1 + gamma u k) ≤ gamma u (k + 1) - gamma u k := by
  have hk0 : (k : ℝ) * u < 1 := by
    have hcast : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by norm_num
    nlinarith [mul_le_mul_of_nonneg_right hcast hu]
  have hd0 : 0 < 1 - (k : ℝ) * u := sub_pos.mpr hk0
  have hd1 : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := sub_pos.mpr hk
  have hd1' : 0 < 1 - ((k : ℝ) + 1) * u := by
    simpa only [Nat.cast_add, Nat.cast_one] using hd1
  unfold gamma
  rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by norm_num]
  have hone : 1 + (k : ℝ) * u / (1 - (k : ℝ) * u) =
      1 / (1 - (k : ℝ) * u) := by
    field_simp [ne_of_gt hd0]
    ring
  have hdiff :
      ((k : ℝ) + 1) * u / (1 - ((k : ℝ) + 1) * u) -
          (k : ℝ) * u / (1 - (k : ℝ) * u) =
        u / ((1 - ((k : ℝ) + 1) * u) * (1 - (k : ℝ) * u)) := by
    field_simp [ne_of_gt hd0, ne_of_gt hd1']
    ring
  rw [hone, hdiff]
  have hbase : u * (1 + u) ≤ u / (1 - ((k : ℝ) + 1) * u) := by
    apply (le_div_iff₀ hd1').2
    have hku : 0 ≤ (k : ℝ) * u := mul_nonneg (Nat.cast_nonneg k) hu
    have hsq : 0 ≤ ((k : ℝ) + 1) * u ^ 2 :=
      mul_nonneg (by positivity) (sq_nonneg u)
    have hf : (1 + u) * (1 - ((k : ℝ) + 1) * u) ≤ 1 := by
      nlinarith
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hf hu
  calc
    u * (1 + u) * (1 / (1 - (k : ℝ) * u)) =
        (u * (1 + u)) / (1 - (k : ℝ) * u) := by ring
    _ ≤ (u / (1 - ((k : ℝ) + 1) * u)) /
        (1 - (k : ℝ) * u) := (div_le_div_iff_of_pos_right hd0).2 hbase
    _ = u / ((1 - ((k : ℝ) + 1) * u) * (1 - (k : ℝ) * u)) := by
      field_simp [ne_of_gt hd0, ne_of_gt hd1']

lemma twoSumPrefix_abs_le (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : k ≤ n) :
    |twoSumPrefix fp v k hk| ≤
      (∑ i : Fin (k + 1),
        |v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩|) +
      ∑ i : Fin k,
        |twoSumCorrection fp v
          ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩| := by
  have he := twoSumPrefix_exact_aux fp v k hk
  have hp : twoSumPrefix fp v k hk =
      (∑ i : Fin (k + 1),
        v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩) -
      ∑ i : Fin k,
        twoSumCorrection fp v
          ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ := by
    linarith
  rw [hp]
  calc
    |(∑ i : Fin (k + 1),
        v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩) -
        ∑ i : Fin k,
          twoSumCorrection fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩| ≤
      |∑ i : Fin (k + 1),
        v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩| +
      |∑ i : Fin k,
        twoSumCorrection fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩| :=
          abs_sub _ _
    _ ≤ (∑ i : Fin (k + 1),
        |v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩|) +
      ∑ i : Fin k,
        |twoSumCorrection fp v
          ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩| :=
      add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)

lemma twoSumCorrections_abs_le_gamma (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : k ≤ n)
    (hvalid : (k : ℝ) * fp.u < 1) :
    (∑ i : Fin k,
        |twoSumCorrection fp v
          ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩|) ≤
      gamma fp.u k *
        ∑ i : Fin (k + 1),
          |v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩| := by
  induction k with
  | zero => simp [gamma]
  | succ k ih =>
      have hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      have hvalid' : (k : ℝ) * fp.u < 1 := by
        have hc : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by norm_num
        nlinarith [mul_le_mul_of_nonneg_right hc fp.u_nonneg]
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      let C : ℝ := ∑ i : Fin k,
        |twoSumCorrection fp v
          ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk'⟩|
      let S : ℝ := ∑ i : Fin (k + 1),
        |v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk')⟩|
      let P : ℝ := twoSumPrefix fp v k hk'
      let z : ℝ := v
        ⟨k + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)⟩
      let L : ℝ := (fp.twoSum P z).2
      change C + |L| ≤ gamma fp.u (k + 1) * (S + |z|)
      have hC : C ≤ gamma fp.u k * S := by
        dsimp only [C, S]
        simpa only using ih hk' hvalid'
      have hP : |P| ≤ S + C := by
        dsimp only [P, S, C]
        simpa only using twoSumPrefix_abs_le fp v k hk'
      have hPz : |P + z| ≤ S + |z| + C := by
        calc
          |P + z| ≤ |P| + |z| := abs_add_le P z
          _ ≤ (S + C) + |z| := add_le_add hP (le_refl _)
          _ = S + |z| + C := by ring
      obtain ⟨δ, hδ, hfl⟩ := fp.model_add P z
      have hfac : |1 + δ| ≤ 1 + fp.u := by
        calc
          |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le 1 δ
          _ ≤ 1 + fp.u := by norm_num; linarith
      have hhigh : |(fp.twoSum P z).1| ≤ (1 + fp.u) * |P + z| := by
        rw [fp.twoSum_high, hfl, abs_mul]
        nlinarith [abs_nonneg (P + z)]
      have hL0 : |L| ≤ fp.u * (1 + fp.u) * |P + z| := by
        dsimp only [L]
        calc
          |(fp.twoSum P z).2| ≤ fp.u * |(fp.twoSum P z).1| :=
            fp.twoSum_low_le P z
          _ ≤ fp.u * ((1 + fp.u) * |P + z|) :=
            mul_le_mul_of_nonneg_left hhigh fp.u_nonneg
          _ = fp.u * (1 + fp.u) * |P + z| := by ring
      have hL1 : |L| ≤ fp.u * (1 + fp.u) * (S + |z| + C) := by
        exact hL0.trans (mul_le_mul_of_nonneg_left hPz
          (mul_nonneg fp.u_nonneg (by linarith [fp.u_nonneg])))
      have hS : 0 ≤ S := by
        dsimp only [S]
        positivity
      have hSz : 0 ≤ S + |z| := add_nonneg hS (abs_nonneg z)
      have hg : 0 ≤ gamma fp.u k :=
        gamma_nonneg_of_lt fp.u k fp.u_nonneg hvalid'
      have hC' : C ≤ gamma fp.u k * (S + |z|) := by
        exact hC.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (abs_nonneg z)) hg)
      have hinside : S + |z| + C ≤
          (1 + gamma fp.u k) * (S + |z|) := by
        nlinarith
      have hL2 : |L| ≤
          (gamma fp.u (k + 1) - gamma fp.u k) * (S + |z|) := by
        calc
          |L| ≤ fp.u * (1 + fp.u) * (S + |z| + C) := hL1
          _ ≤ fp.u * (1 + fp.u) *
              ((1 + gamma fp.u k) * (S + |z|)) :=
            mul_le_mul_of_nonneg_left hinside
              (mul_nonneg fp.u_nonneg (by linarith [fp.u_nonneg]))
          _ = (fp.u * (1 + fp.u) * (1 + gamma fp.u k)) *
              (S + |z|) := by ring
          _ ≤ (gamma fp.u (k + 1) - gamma fp.u k) *
              (S + |z|) :=
            mul_le_mul_of_nonneg_right
              (gamma_succ_increment_bound fp.u k fp.u_nonneg hvalid) hSz
      calc
        C + |L| ≤ gamma fp.u k * (S + |z|) +
            (gamma fp.u (k + 1) - gamma fp.u k) * (S + |z|) :=
          add_le_add hC' hL2
        _ = gamma fp.u (k + 1) * (S + |z|) := by ring

lemma vecSum_sum_eq (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) :
    ∑ i, vecSum fp v i = ∑ i, v i := by
  rw [Fin.sum_univ_castSucc]
  simp only [vecSum, Fin.lastCases_castSucc, Fin.lastCases_last]
  have he := twoSumPrefix_exact_aux fp v n (Nat.le_refl n)
  simpa [add_comm] using he

lemma vecSum_abs_sum_le (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (hvalid : (n : ℝ) * fp.u < 1) :
    (∑ i, |vecSum fp v i|) ≤
      |∑ i, v i| + 2 * gamma fp.u n * ∑ i, |v i| := by
  rw [Fin.sum_univ_castSucc]
  simp only [vecSum, Fin.lastCases_castSucc, Fin.lastCases_last]
  let C : ℝ := ∑ i : Fin n, |twoSumCorrection fp v i|
  let A : ℝ := ∑ i : Fin (n + 1), |v i|
  let s : ℝ := ∑ i : Fin (n + 1), v i
  let P : ℝ := twoSumPrefix fp v n (Nat.le_refl n)
  change C + |P| ≤ |s| + 2 * gamma fp.u n * A
  have hC : C ≤ gamma fp.u n * A := by
    dsimp only [C, A]
    simpa only using
      twoSumCorrections_abs_le_gamma fp v n (Nat.le_refl n) hvalid
  have he := twoSumPrefix_exact_aux fp v n (Nat.le_refl n)
  have hPs : P = s - ∑ i : Fin n, twoSumCorrection fp v i := by
    dsimp only [P, s]
    linarith
  have hP : |P| ≤ |s| + C := by
    rw [hPs]
    calc
      |s - ∑ i : Fin n, twoSumCorrection fp v i| ≤
          |s| + |∑ i : Fin n, twoSumCorrection fp v i| := abs_sub _ _
      _ ≤ |s| + C := add_le_add_right (Finset.abs_sum_le_sum_abs _ _) _
  linarith

lemma recursiveSum_error_le_gamma (fp : StandardAddModel) (m : ℕ)
    (v : Fin (m + 1) → ℝ) (hvalid : (m : ℝ) * fp.u < 1) :
    |recursiveSum fp.fl_add (m + 1) v - ∑ i, v i| ≤
      gamma fp.u m * ∑ i, |v i| := by
  induction m with
  | zero => simp [recursiveSum, gamma]
  | succ m ih =>
      have hmvalid : (m : ℝ) * fp.u < 1 := by
        have hc : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by norm_num
        nlinarith [mul_le_mul_of_nonneg_right hc fp.u_nonneg]
      rw [Fin.sum_univ_castSucc (fun i => v i)]
      rw [Fin.sum_univ_castSucc (fun i => |v i|)]
      rw [recursiveSum]
      simp only [Nat.succ_ne_zero, ↓reduceDIte]
      let r : ℝ := recursiveSum fp.fl_add (m + 1) (fun i => v i.castSucc)
      let s : ℝ := ∑ i : Fin (m + 1), v i.castSucc
      let z : ℝ := v (Fin.last (m + 1))
      let A : ℝ := ∑ i : Fin (m + 1), |v i.castSucc|
      change |fp.fl_add r z - (s + z)| ≤ gamma fp.u (m + 1) * (A + |z|)
      have hE : |r - s| ≤ gamma fp.u m * A := by
        dsimp only [r, s, A]
        simpa only using ih (fun i => v i.castSucc) hmvalid
      have hs : |s| ≤ A := by
        dsimp only [s, A]
        exact Finset.abs_sum_le_sum_abs _ _
      have hA : 0 ≤ A := by dsimp only [A]; positivity
      have hAz : 0 ≤ A + |z| := add_nonneg hA (abs_nonneg z)
      have hg : 0 ≤ gamma fp.u m :=
        gamma_nonneg_of_lt fp.u m fp.u_nonneg hmvalid
      have hE' : |r - s| ≤ gamma fp.u m * (A + |z|) :=
        hE.trans (mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (abs_nonneg z)) hg)
      have hr : |r + z| ≤ (1 + gamma fp.u m) * (A + |z|) := by
        have hrs : |r + z| ≤ |s| + |z| + |r - s| := by
          have hrrep : r + z = (r - s) + (s + z) := by ring
          rw [hrrep]
          calc
            |r - s + (s + z)| ≤ |r - s| + |s + z| := abs_add_le _ _
            _ ≤ |r - s| + (|s| + |z|) :=
              add_le_add_right (abs_add_le s z) _
            _ = |s| + |z| + |r - s| := by ring
        calc
          |r + z| ≤ |s| + |z| + |r - s| := hrs
          _ ≤ (A + |z|) + gamma fp.u m * (A + |z|) :=
            add_le_add (add_le_add hs (le_refl _)) hE'
          _ = (1 + gamma fp.u m) * (A + |z|) := by ring
      obtain ⟨δ, hδ, hfl⟩ := fp.model_add r z
      have hdecomp : fp.fl_add r z - (s + z) =
          (r - s) + (r + z) * δ := by rw [hfl]; ring
      have herr : |fp.fl_add r z - (s + z)| ≤
          |r - s| + fp.u * |r + z| := by
        rw [hdecomp]
        calc
          |r - s + (r + z) * δ| ≤ |r - s| + |(r + z) * δ| :=
            abs_add_le _ _
          _ = |r - s| + |r + z| * |δ| := by rw [abs_mul]
          _ ≤ |r - s| + |r + z| * fp.u :=
            add_le_add_right (mul_le_mul_of_nonneg_left hδ (abs_nonneg _)) _
          _ = |r - s| + fp.u * |r + z| := by ring
      have huinc : fp.u * (1 + gamma fp.u m) ≤
          gamma fp.u (m + 1) - gamma fp.u m := by
        have hbig := gamma_succ_increment_bound fp.u m fp.u_nonneg hvalid
        have hone : fp.u * (1 + gamma fp.u m) ≤
            fp.u * (1 + fp.u) * (1 + gamma fp.u m) := by
          have h1g : 0 ≤ 1 + gamma fp.u m := by linarith
          nlinarith [mul_nonneg fp.u_nonneg h1g]
        exact hone.trans hbig
      calc
        |fp.fl_add r z - (s + z)| ≤ |r - s| + fp.u * |r + z| := herr
        _ ≤ gamma fp.u m * (A + |z|) +
            fp.u * ((1 + gamma fp.u m) * (A + |z|)) :=
          add_le_add hE' (mul_le_mul_of_nonneg_left hr fp.u_nonneg)
        _ = (gamma fp.u m + fp.u * (1 + gamma fp.u m)) *
            (A + |z|) := by ring
        _ ≤ gamma fp.u (m + 1) * (A + |z|) := by
          apply mul_le_mul_of_nonneg_right _ hAz
          linarith

lemma gamma_le_one_third (u : ℝ) (N : ℕ) (hu : 0 ≤ u)
    (hquarter : (N : ℝ) * u ≤ (1 : ℝ) / 4) :
    gamma u N ≤ (1 : ℝ) / 3 := by
  have hd : 0 < 1 - (N : ℝ) * u := by linarith
  unfold gamma
  apply (div_le_iff₀ hd).2
  linarith

lemma two_gamma_le_gamma_double (u : ℝ) (N : ℕ) (hu : 0 ≤ u)
    (hquarter : (N : ℝ) * u ≤ (1 : ℝ) / 4) :
    2 * gamma u N ≤ gamma u (2 * N) := by
  have ht : 0 ≤ (N : ℝ) * u := mul_nonneg (Nat.cast_nonneg N) hu
  have hd1 : 0 < 1 - (N : ℝ) * u := by linarith
  have hd2 : 0 < 1 - 2 * ((N : ℝ) * u) := by linarith
  unfold gamma
  rw [show ((2 * N : ℕ) : ℝ) * u = 2 * ((N : ℝ) * u) by norm_num; ring]
  rw [show 2 * ((N : ℝ) * u / (1 - (N : ℝ) * u)) =
      (2 * ((N : ℝ) * u)) / (1 - (N : ℝ) * u) by ring]
  apply (div_le_div_iff₀ hd1 hd2).2
  nlinarith

lemma one_add_u_mul_gamma_pred_le (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hvalid : ((m + 1 : ℕ) : ℝ) * u < 1) :
    (1 + u) * gamma u m ≤ gamma u (m + 1) := by
  have hmvalid : (m : ℝ) * u < 1 := by
    have hc : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by norm_num
    nlinarith [mul_le_mul_of_nonneg_right hc hu]
  have hg : 0 ≤ gamma u m := gamma_nonneg_of_lt u m hu hmvalid
  have hinc := gamma_succ_increment_bound u m hu hvalid
  have hsmall : u * gamma u m ≤ u * (1 + u) * (1 + gamma u m) := by
    have h1 : 0 ≤ 1 + u := by linarith
    nlinarith [mul_nonneg hu hg, mul_nonneg h1 (by linarith : 0 ≤ 1 + gamma u m)]
  nlinarith

lemma iteratedVecSum_sum_eq (fp : ErrorFreeAddModel) {n : ℕ}
    (k : ℕ) (v : Fin (n + 1) → ℝ) :
    ∑ i, iteratedVecSum fp k v i = ∑ i, v i := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show iteratedVecSum fp (k + 1) v =
        vecSum fp (iteratedVecSum fp k v) by rfl]
      rw [vecSum_sum_eq, ih]

lemma iteratedVecSum_abs_sum_le (fp : ErrorFreeAddModel) {N : ℕ}
    (k : ℕ) (v : Fin (N + 1) → ℝ)
    (hquarter : (N : ℝ) * fp.u ≤ (1 : ℝ) / 4) :
    (∑ i, |iteratedVecSum fp k v i|) ≤
      3 * |∑ i, v i| +
        (gamma fp.u (2 * N)) ^ k * ∑ i, |v i| := by
  have hvalid : (N : ℝ) * fp.u < 1 := by linarith
  have hgN : 0 ≤ gamma fp.u N :=
    gamma_nonneg_of_lt fp.u N fp.u_nonneg hvalid
  have htwo : 2 * gamma fp.u N ≤ gamma fp.u (2 * N) :=
    two_gamma_le_gamma_double fp.u N fp.u_nonneg hquarter
  have hthird : 2 * gamma fp.u N ≤ (2 : ℝ) / 3 := by
    have := gamma_le_one_third fp.u N fp.u_nonneg hquarter
    linarith
  have hdoubleValid : ((2 * N : ℕ) : ℝ) * fp.u < 1 := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have hG : 0 ≤ gamma fp.u (2 * N) :=
    gamma_nonneg_of_lt fp.u (2 * N) fp.u_nonneg hdoubleValid
  induction k with
  | zero =>
      simp only [iteratedVecSum, pow_zero, one_mul]
      nlinarith [abs_nonneg (∑ i, v i)]
  | succ k ih =>
      rw [show iteratedVecSum fp (k + 1) v =
        vecSum fp (iteratedVecSum fp k v) by rfl]
      have hv := vecSum_abs_sum_le fp (iteratedVecSum fp k v) hvalid
      rw [iteratedVecSum_sum_eq fp k v] at hv
      have ha : 0 ≤ 2 * gamma fp.u N := by positivity
      have hmul := mul_le_mul_of_nonneg_left ih ha
      have hfirst :
          (1 + 3 * (2 * gamma fp.u N)) * |∑ i, v i| ≤
            3 * |∑ i, v i| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        nlinarith
      have htail :
          (2 * gamma fp.u N) *
              ((gamma fp.u (2 * N)) ^ k * ∑ i, |v i|) ≤
            gamma fp.u (2 * N) *
              ((gamma fp.u (2 * N)) ^ k * ∑ i, |v i|) := by
        apply mul_le_mul_of_nonneg_right htwo
        positivity
      calc
        ∑ i, |vecSum fp (iteratedVecSum fp k v) i| ≤
            |∑ i, v i| + 2 * gamma fp.u N *
              ∑ i, |iteratedVecSum fp k v i| := hv
        _ ≤ |∑ i, v i| + 2 * gamma fp.u N *
            (3 * |∑ i, v i| +
              (gamma fp.u (2 * N)) ^ k * ∑ i, |v i|) :=
          add_le_add_right hmul _
        _ = (1 + 3 * (2 * gamma fp.u N)) * |∑ i, v i| +
            (2 * gamma fp.u N) *
              ((gamma fp.u (2 * N)) ^ k * ∑ i, |v i|) := by ring
        _ ≤ 3 * |∑ i, v i| + gamma fp.u (2 * N) *
              ((gamma fp.u (2 * N)) ^ k * ∑ i, |v i|) :=
          add_le_add hfirst htail
        _ = 3 * |∑ i, v i| +
            (gamma fp.u (2 * N)) ^ (k + 1) * ∑ i, |v i| := by
          rw [pow_succ]
          ring

lemma sumK_error_bound_aux (fp : ErrorFreeAddModel) (m L : ℕ)
    (v : Fin ((m + 1) + 1) → ℝ) (hL : 2 ≤ L)
    (hquarter : ((m + 1 : ℕ) : ℝ) * fp.u ≤ (1 : ℝ) / 4) :
    |sumK fp L v - ∑ i, v i| ≤
      (fp.u + 3 * (gamma fp.u (m + 1)) ^ 2) * |∑ i, v i| +
        (gamma fp.u (2 * (m + 1))) ^ L * ∑ i, |v i| := by
  let N : ℕ := m + 1
  let q : ℕ := L - 2
  let prev : Fin (N + 1) → ℝ := iteratedVecSum fp q v
  let c : Fin N → ℝ := fun i => twoSumCorrection fp prev i
  let P : ℝ := twoSumPrefix fp prev N (Nat.le_refl N)
  let r : ℝ := recursiveSum fp.fl_add N c
  let E : ℝ := ∑ i : Fin N, c i
  let C : ℝ := ∑ i : Fin N, |c i|
  let s : ℝ := ∑ i, v i
  let A : ℝ := ∑ i, |v i|
  let Aprev : ℝ := ∑ i, |prev i|
  have hNpos : 0 < N := by dsimp only [N]; omega
  have hNm : N = m + 1 := rfl
  have hiter : iteratedVecSum fp (L - 1) v = vecSum fp prev := by
    have hsub : L - 1 = q + 1 := by dsimp only [q]; omega
    rw [hsub]
    rfl
  have hsumprev : ∑ i, prev i = s := by
    dsimp only [prev, s]
    exact iteratedVecSum_sum_eq fp q v
  have hvalidN : (N : ℝ) * fp.u < 1 := by
    dsimp only [N] at hquarter ⊢
    linarith
  have hvalidm : (m : ℝ) * fp.u < 1 := by
    have hc : (m : ℝ) ≤ (N : ℝ) := by dsimp only [N]; norm_num
    nlinarith [mul_le_mul_of_nonneg_right hc fp.u_nonneg]
  have hrec : |r - E| ≤ gamma fp.u m * C := by
    dsimp only [r, E, C, c, N]
    simpa only using recursiveSum_error_le_gamma fp.toStandardAddModel m
      (fun i => twoSumCorrection fp prev i) hvalidm
  have hC : C ≤ gamma fp.u N * Aprev := by
    dsimp only [C, c, Aprev]
    simpa only using twoSumCorrections_abs_le_gamma fp prev N (Nat.le_refl N) hvalidN
  have hgm : 0 ≤ gamma fp.u m :=
    gamma_nonneg_of_lt fp.u m fp.u_nonneg hvalidm
  have hgN : 0 ≤ gamma fp.u N :=
    gamma_nonneg_of_lt fp.u N fp.u_nonneg hvalidN
  have hD : |r - E| ≤ gamma fp.u m * (gamma fp.u N * Aprev) :=
    hrec.trans (mul_le_mul_of_nonneg_left hC hgm)
  have hcoef : (1 + fp.u) * gamma fp.u m ≤ gamma fp.u N := by
    dsimp only [N]
    exact one_add_u_mul_gamma_pred_le fp.u m fp.u_nonneg hvalidN
  have hDscaled : (1 + fp.u) * |r - E| ≤
      (gamma fp.u N) ^ 2 * Aprev := by
    calc
      (1 + fp.u) * |r - E| ≤
          (1 + fp.u) * (gamma fp.u m * (gamma fp.u N * Aprev)) :=
        mul_le_mul_of_nonneg_left hD (by linarith [fp.u_nonneg])
      _ = ((1 + fp.u) * gamma fp.u m) * (gamma fp.u N * Aprev) := by ring
      _ ≤ gamma fp.u N * (gamma fp.u N * Aprev) := by
        apply mul_le_mul_of_nonneg_right hcoef
        exact mul_nonneg hgN (by dsimp only [Aprev]; positivity)
      _ = (gamma fp.u N) ^ 2 * Aprev := by ring
  have hexact := twoSumPrefix_exact_aux fp prev N (Nat.le_refl N)
  have hPE : P + E = s := by
    dsimp only [P, E, c]
    rw [hexact, hsumprev]
  unfold sumK
  rw [hiter]
  rw [recursiveSum]
  simp only [show m + 1 ≠ 0 by omega, ↓reduceDIte]
  simp only [vecSum, N, Fin.lastCases_castSucc, Fin.lastCases_last]
  change |fp.fl_add r P - s| ≤
    (fp.u + 3 * (gamma fp.u N) ^ 2) * |s| +
      (gamma fp.u (2 * N)) ^ L * A
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add r P
  have hdecomp : fp.fl_add r P - s = (r - E) + (r + P) * δ := by
    rw [hfl]
    nlinarith [hPE]
  have hrP : |r + P| ≤ |s| + |r - E| := by
    have heq : r + P = s + (r - E) := by linarith [hPE]
    rw [heq]
    exact abs_add_le _ _
  have herr : |fp.fl_add r P - s| ≤ fp.u * |s| + (1 + fp.u) * |r - E| := by
    rw [hdecomp]
    calc
      |r - E + (r + P) * δ| ≤ |r - E| + |(r + P) * δ| := abs_add_le _ _
      _ = |r - E| + |r + P| * |δ| := by rw [abs_mul]
      _ ≤ |r - E| + |r + P| * fp.u :=
        add_le_add_right (mul_le_mul_of_nonneg_left hδ (abs_nonneg _)) _
      _ ≤ |r - E| + (|s| + |r - E|) * fp.u :=
        add_le_add_right (mul_le_mul_of_nonneg_right hrP fp.u_nonneg) _
      _ = fp.u * |s| + (1 + fp.u) * |r - E| := by ring
  have hprev : Aprev ≤ 3 * |s| +
      (gamma fp.u (2 * N)) ^ q * A := by
    dsimp only [Aprev, prev, A, q]
    have h := iteratedVecSum_abs_sum_le fp (L - 2) v hquarter
    simpa only [s, N] using h
  have hvalid2 : ((2 * N : ℕ) : ℝ) * fp.u < 1 := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
    dsimp only [N] at hquarter ⊢
    nlinarith
  have hG : 0 ≤ gamma fp.u (2 * N) :=
    gamma_nonneg_of_lt fp.u (2 * N) fp.u_nonneg hvalid2
  have hsq : (gamma fp.u N) ^ 2 ≤ (gamma fp.u (2 * N)) ^ 2 := by
    have htwo := two_gamma_le_gamma_double fp.u N fp.u_nonneg hquarter
    have hle : gamma fp.u N ≤ gamma fp.u (2 * N) := by linarith
    exact (sq_le_sq₀ hgN hG).2 hle
  have hpow : (gamma fp.u N) ^ 2 * (gamma fp.u (2 * N)) ^ q ≤
      (gamma fp.u (2 * N)) ^ L := by
    have hnon : 0 ≤ (gamma fp.u (2 * N)) ^ q := pow_nonneg hG _
    calc
      (gamma fp.u N) ^ 2 * (gamma fp.u (2 * N)) ^ q ≤
          (gamma fp.u (2 * N)) ^ 2 * (gamma fp.u (2 * N)) ^ q :=
        mul_le_mul_of_nonneg_right hsq hnon
      _ = (gamma fp.u (2 * N)) ^ L := by
        rw [show L = 2 + q by dsimp only [q]; omega, pow_add]
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  calc
    |fp.fl_add r P - s| ≤ fp.u * |s| + (1 + fp.u) * |r - E| := herr
    _ ≤ fp.u * |s| + (gamma fp.u N) ^ 2 * Aprev :=
      add_le_add_right hDscaled _
    _ ≤ fp.u * |s| + (gamma fp.u N) ^ 2 *
        (3 * |s| + (gamma fp.u (2 * N)) ^ q * A) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hprev (sq_nonneg _)) _
    _ = (fp.u + 3 * (gamma fp.u N) ^ 2) * |s| +
        ((gamma fp.u N) ^ 2 * (gamma fp.u (2 * N)) ^ q) * A := by ring
    _ ≤ (fp.u + 3 * (gamma fp.u N) ^ 2) * |s| +
        (gamma fp.u (2 * N)) ^ L * A :=
      add_le_add_right (mul_le_mul_of_nonneg_right hpow hA) _

lemma dotKTransform_sum_eq (fp : ErrorFreeDotModel) {n : ℕ}
    (x y : Fin (n + 1) → ℝ) :
    ∑ j, dotKTransform fp x y j = exactDot x y := by
  let lo : Fin (n + 1) → ℝ := fun i => (fp.twoProduct (x i) (y i)).2
  let hi : Fin (n + 1) → ℝ := fun i => (fp.twoProduct (x i) (y i)).1
  let z : Fin ((n + 1) + (n + 1)) → ℝ :=
    Fin.addCases lo (vecSum fp.toErrorFreeAddModel hi)
  have hcast : (2 * n + 1) + 1 = (n + 1) + (n + 1) := by omega
  have hsumcast :
      (∑ j : Fin ((2 * n + 1) + 1),
        z (Fin.cast hcast j)) = ∑ j : Fin ((n + 1) + (n + 1)), z j := by
    exact Fin.sum_congr' _ hcast
  unfold dotKTransform
  change (∑ j : Fin ((2 * n + 1) + 1),
    z (Fin.cast hcast j)) = _
  rw [hsumcast, Fin.sum_univ_add]
  dsimp only [z]
  simp only [Fin.addCases_left, Fin.addCases_right]
  rw [vecSum_sum_eq]
  unfold exactDot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi_mem
  dsimp only [lo, hi]
  simpa only [add_comm] using fp.twoProduct_exact (x i) (y i)

lemma dotKTransform_abs_sum_le (fp : ErrorFreeDotModel) {n : ℕ}
    (x y : Fin (n + 1) → ℝ)
    (hquarter : ((n + 1 : ℕ) : ℝ) * fp.u ≤ (1 : ℝ) / 4) :
    (∑ j, |dotKTransform fp x y j|) ≤
      |exactDot x y| + gamma fp.u (2 * (n + 1)) * dotMagnitude x y := by
  let lo : Fin (n + 1) → ℝ := fun i => (fp.twoProduct (x i) (y i)).2
  let hi : Fin (n + 1) → ℝ := fun i => (fp.twoProduct (x i) (y i)).1
  let z : Fin ((n + 1) + (n + 1)) → ℝ :=
    Fin.addCases lo (vecSum fp.toErrorFreeAddModel hi)
  let L : ℝ := ∑ i, |lo i|
  let H : ℝ := ∑ i, |hi i|
  let M : ℝ := dotMagnitude x y
  let V : ℝ := ∑ i, |vecSum fp.toErrorFreeAddModel hi i|
  have hcast : (2 * n + 1) + 1 = (n + 1) + (n + 1) := by omega
  have hsumcast :
      (∑ j : Fin ((2 * n + 1) + 1), |z (Fin.cast hcast j)|) =
        ∑ j : Fin ((n + 1) + (n + 1)), |z j| := by
    exact Fin.sum_congr' (M := ℝ) (fun j => |z j|) hcast
  have htransform : (∑ j, |dotKTransform fp x y j|) = L + V := by
    unfold dotKTransform
    change (∑ j : Fin ((2 * n + 1) + 1), |z (Fin.cast hcast j)|) = L + V
    rw [hsumcast, Fin.sum_univ_add]
    dsimp only [z]
    simp only [Fin.addCases_left, Fin.addCases_right]
    rfl
  have hM : 0 ≤ M := by
    dsimp only [M, dotMagnitude]
    positivity
  have hL : L ≤ fp.u * M := by
    dsimp only [L, M, lo, dotMagnitude]
    calc
      ∑ i : Fin (n + 1), |(fp.twoProduct (x i) (y i)).2| ≤
          ∑ i : Fin (n + 1), fp.u * |x i * y i| := by
        apply Finset.sum_le_sum
        intro i hi_mem
        exact fp.twoProduct_low_le_exact (x i) (y i)
      _ = fp.u * ∑ i : Fin (n + 1), |x i| * |y i| := by
        simp_rw [abs_mul, Finset.mul_sum]
  have hH : H ≤ (1 + fp.u) * M := by
    dsimp only [H, M, hi, dotMagnitude]
    calc
      ∑ i : Fin (n + 1), |(fp.twoProduct (x i) (y i)).1| ≤
          ∑ i : Fin (n + 1), (1 + fp.u) * (|x i| * |y i|) := by
        apply Finset.sum_le_sum
        intro i hi_mem
        have he := fp.twoProduct_exact (x i) (y i)
        have hh : (fp.twoProduct (x i) (y i)).1 =
            x i * y i - (fp.twoProduct (x i) (y i)).2 := by linarith
        rw [hh]
        calc
          |x i * y i - (fp.twoProduct (x i) (y i)).2| ≤
              |x i * y i| + |(fp.twoProduct (x i) (y i)).2| := abs_sub _ _
          _ ≤ |x i * y i| + fp.u * |x i * y i| :=
            add_le_add_right (fp.twoProduct_low_le_exact (x i) (y i)) _
          _ = (1 + fp.u) * (|x i| * |y i|) := by rw [abs_mul]; ring
      _ = (1 + fp.u) * ∑ i : Fin (n + 1), |x i| * |y i| := by
        rw [Finset.mul_sum]
  have hvalidn : (n : ℝ) * fp.u < 1 := by
    have hc : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
    nlinarith [mul_le_mul_of_nonneg_right hc fp.u_nonneg]
  have hV : V ≤ |∑ i, hi i| + 2 * gamma fp.u n * H := by
    dsimp only [V, H]
    exact vecSum_abs_sum_le fp.toErrorFreeAddModel hi hvalidn
  have hsumprod : (∑ i, hi i) + (∑ i, lo i) = exactDot x y := by
    unfold exactDot
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi_mem
    dsimp only [hi, lo]
    exact fp.twoProduct_exact (x i) (y i)
  have hsumhi : |∑ i, hi i| ≤ |exactDot x y| + L := by
    have heq : (∑ i, hi i) = exactDot x y - ∑ i, lo i := by
      linarith [hsumprod]
    rw [heq]
    calc
      |exactDot x y - ∑ i, lo i| ≤ |exactDot x y| + |∑ i, lo i| := abs_sub _ _
      _ ≤ |exactDot x y| + L := by
        apply add_le_add_right
        dsimp only [L]
        exact Finset.abs_sum_le_sum_abs _ _
  have hg : 0 ≤ gamma fp.u n :=
    gamma_nonneg_of_lt fp.u n fp.u_nonneg hvalidn
  have hLV : L + V ≤ |exactDot x y| +
      (2 * fp.u + 2 * gamma fp.u n * (1 + fp.u)) * M := by
    calc
      L + V ≤ L + (|∑ i, hi i| + 2 * gamma fp.u n * H) :=
        add_le_add_right hV _
      _ ≤ L + ((|exactDot x y| + L) + 2 * gamma fp.u n *
          ((1 + fp.u) * M)) := by
        gcongr
      _ ≤ |exactDot x y| +
          (2 * fp.u + 2 * gamma fp.u n * (1 + fp.u)) * M := by
        have h2L : 2 * L ≤ 2 * fp.u * M := by nlinarith [hL]
        nlinarith
  have hvalidN : (((n + 1 : ℕ) : ℝ) * fp.u) < 1 := by linarith
  have hadj : (1 + fp.u) * gamma fp.u n ≤ gamma fp.u (n + 1) :=
    one_add_u_mul_gamma_pred_le fp.u n fp.u_nonneg hvalidN
  have hdouble : 2 * gamma fp.u (n + 1) ≤ gamma fp.u (2 * (n + 1)) :=
    two_gamma_le_gamma_double fp.u (n + 1) fp.u_nonneg hquarter
  have hcoef : 2 * fp.u + 2 * gamma fp.u n * (1 + fp.u) ≤
      gamma fp.u (2 * (n + 1)) := by
    have hinc := gamma_succ_increment_bound fp.u n fp.u_nonneg hvalidN
    have hinc' : fp.u * (1 + gamma fp.u n) ≤
        fp.u * (1 + fp.u) * (1 + gamma fp.u n) := by
      have h1g : 0 ≤ 1 + gamma fp.u n := by linarith
      nlinarith [mul_nonneg fp.u_nonneg h1g]
    have hsumadj : fp.u + (1 + fp.u) * gamma fp.u n ≤
        gamma fp.u (n + 1) := by
      nlinarith
    nlinarith
  rw [htransform]
  exact hLV.trans (add_le_add_right (mul_le_mul_of_nonneg_right hcoef hM) _)

lemma gamma_mono_nat (u : ℝ) (a b : ℕ) (hu : 0 ≤ u) (hab : a ≤ b)
    (hb : (b : ℝ) * u < 1) : gamma u a ≤ gamma u b := by
  have hcast : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hxy : (a : ℝ) * u ≤ (b : ℝ) * u :=
    mul_le_mul_of_nonneg_right hcast hu
  have ha : (a : ℝ) * u < 1 := lt_of_le_of_lt hxy hb
  have hda : 0 < 1 - (a : ℝ) * u := sub_pos.mpr ha
  have hdb : 0 < 1 - (b : ℝ) * u := sub_pos.mpr hb
  unfold gamma
  apply (div_le_div_iff₀ hda hdb).2
  nlinarith

lemma gamma_double_le_one (u : ℝ) (N : ℕ) (hu : 0 ≤ u)
    (hquarter : (N : ℝ) * u ≤ (1 : ℝ) / 4) :
    gamma u (2 * N) ≤ 1 := by
  have hd : 0 < 1 - 2 * ((N : ℝ) * u) := by linarith
  unfold gamma
  rw [show ((2 * N : ℕ) : ℝ) * u = 2 * ((N : ℝ) * u) by norm_num; ring]
  apply (div_le_iff₀ hd).2
  nlinarith

theorem p02_t3_dotK_error_bound
    (fp : ErrorFreeDotModel) (n K : ℕ) (x y : Fin (n + 1) → ℝ)
    (hK : 3 ≤ K)
    (hsmall : (8 : ℝ) * ((n + 1 : ℕ) : ℝ) * fp.u ≤ 1) :
    |dotK fp K x y - exactDot x y| ≤
      (fp.u + 2 * (gamma fp.u (4 * (n + 1) - 2)) ^ 2) * |exactDot x y| +
        (gamma fp.u (4 * (n + 1) - 2)) ^ K * dotMagnitude x y := by
  -- PROOF_START P02-T3-H001
  let N : ℕ := 2 * n + 1
  let v : Fin (N + 1) → ℝ := dotKTransform fp x y
  let a : ℝ := gamma fp.u N
  let G : ℝ := gamma fp.u (2 * N)
  let b : ℝ := gamma fp.u (2 * (n + 1))
  let s : ℝ := exactDot x y
  let M : ℝ := dotMagnitude x y
  let S : ℝ := ∑ i, |v i|
  have hquarter0 : (((n + 1 : ℕ) : ℝ) * fp.u) ≤ (1 : ℝ) / 8 := by
    nlinarith
  have hquarterN : (N : ℝ) * fp.u ≤ (1 : ℝ) / 4 := by
    have hindex : (N : ℝ) ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
      dsimp only [N]
      norm_num
      linarith
    have hmul := mul_le_mul_of_nonneg_right hindex fp.u_nonneg
    nlinarith
  have hL : 2 ≤ K - 1 := by omega
  have hsum := sumK_error_bound_aux fp.toErrorFreeAddModel (2 * n) (K - 1)
    (dotKTransform fp x y) hL hquarterN
  have hvsum : ∑ i, v i = s := by
    dsimp only [v, s]
    exact dotKTransform_sum_eq fp x y
  have hS : S ≤ |s| + b * M := by
    dsimp only [S, v, s, b, M]
    exact dotKTransform_abs_sum_le fp x y (by linarith)
  have hmain : |dotK fp K x y - s| ≤
      (fp.u + 3 * a ^ 2) * |s| + G ^ (K - 1) * S := by
    dsimp only [dotK]
    rw [hvsum] at hsum
    simpa only [N, a, G, v, s] using hsum
  have hvalidG : ((2 * N : ℕ) : ℝ) * fp.u < 1 := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    have hv : (N : ℝ) * fp.u < 1 := by linarith
    exact gamma_nonneg_of_lt fp.u N fp.u_nonneg hv
  have hG0 : 0 ≤ G := by
    dsimp only [G]
    exact gamma_nonneg_of_lt fp.u (2 * N) fp.u_nonneg hvalidG
  have hG1 : G ≤ 1 := by
    dsimp only [G]
    exact gamma_double_le_one fp.u N fp.u_nonneg hquarterN
  have htwo : 2 * a ≤ G := by
    dsimp only [a, G]
    exact two_gamma_le_gamma_double fp.u N fp.u_nonneg hquarterN
  have hsquares : 4 * a ^ 2 ≤ G ^ 2 := by
    have hsq := (sq_le_sq₀ (by positivity : 0 ≤ 2 * a) hG0).2 htwo
    nlinarith
  have hKpow : G ^ (K - 1) ≤ G ^ 2 := by
    apply pow_le_pow_of_le_one hG0 hG1
    omega
  have hcoeff : 3 * a ^ 2 + G ^ (K - 1) ≤ 2 * G ^ 2 := by
    nlinarith
  have hbG : b ≤ G := by
    dsimp only [b, G]
    apply gamma_mono_nat fp.u (2 * (n + 1)) (2 * N) fp.u_nonneg
    · dsimp only [N]
      omega
    · exact hvalidG
  have hM : 0 ≤ M := by
    dsimp only [M, dotMagnitude]
    positivity
  have hpow0 : 0 ≤ G ^ (K - 1) := pow_nonneg hG0 _
  have hmag : G ^ (K - 1) * b * M ≤ G ^ K * M := by
    have hbmul : G ^ (K - 1) * b ≤ G ^ (K - 1) * G :=
      mul_le_mul_of_nonneg_left hbG hpow0
    have hpowe : G ^ (K - 1) * G = G ^ K := by
      calc
        G ^ (K - 1) * G = G ^ ((K - 1) + 1) := (pow_succ G (K - 1)).symm
        _ = G ^ K := by congr 1 <;> omega
    rw [hpowe] at hbmul
    exact mul_le_mul_of_nonneg_right hbmul hM
  have hindexTarget : 4 * (n + 1) - 2 = 2 * N := by
    dsimp only [N]
    omega
  change |dotK fp K x y - s| ≤
    (fp.u + 2 * (gamma fp.u (4 * (n + 1) - 2)) ^ 2) * |s| +
      (gamma fp.u (4 * (n + 1) - 2)) ^ K * M
  rw [hindexTarget]
  change |dotK fp K x y - s| ≤
    (fp.u + 2 * G ^ 2) * |s| + G ^ K * M
  calc
    |dotK fp K x y - s| ≤
        (fp.u + 3 * a ^ 2) * |s| + G ^ (K - 1) * S := hmain
    _ ≤ (fp.u + 3 * a ^ 2) * |s| +
        G ^ (K - 1) * (|s| + b * M) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hS hpow0) _
    _ = (fp.u + (3 * a ^ 2 + G ^ (K - 1))) * |s| +
        G ^ (K - 1) * b * M := by ring
    _ ≤ (fp.u + 2 * G ^ 2) * |s| + G ^ K * M := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (add_le_add_right hcoeff fp.u) (abs_nonneg s)) hmag

end HighamBench
