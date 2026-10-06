import HighamBench.P02Definitions

namespace HighamBench

open scoped BigOperators

lemma gammaValid_mono_nat {u : ℝ} {k n : ℕ} (hu : 0 ≤ u)
    (hkn : k ≤ n) (h : GammaValid u n) : GammaValid u k := by
  unfold GammaValid at h ⊢
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hkn) hu) h

lemma gamma_nonneg_of_valid {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (h : GammaValid u n) : 0 ≤ gamma u n := by
  unfold gamma GammaValid at *
  have hd : 0 < 1 - (n : ℝ) * u := by linarith
  positivity

lemma gamma_mono_nat {u : ℝ} {k n : ℕ} (hu : 0 ≤ u)
    (hkn : k ≤ n) (h : GammaValid u n) : gamma u k ≤ gamma u n := by
  have hk := gammaValid_mono_nat hu hkn h
  unfold gamma GammaValid at *
  have hdk : 0 < 1 - (k : ℝ) * u := by linarith
  have hdn : 0 < 1 - (n : ℝ) * u := by linarith
  apply (div_le_div_iff₀ hdk hdn).2
  have hcast : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
  nlinarith

lemma gamma_step_bound {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (h : GammaValid u (n + 1)) :
    (1 + u) * gamma u n + u ≤ gamma u (n + 1) := by
  have hn : GammaValid u n :=
    gammaValid_mono_nat hu (Nat.le_succ n) h
  unfold gamma GammaValid at *
  have hdn : 0 < 1 - (n : ℝ) * u := by linarith
  have hdns : 0 < 1 - ((n + 1 : ℕ) : ℝ) * u := by linarith
  have hid :
      (1 + u) * ((n : ℝ) * u / (1 - (n : ℝ) * u)) + u =
        ((n + 1 : ℕ) : ℝ) * u / (1 - (n : ℝ) * u) := by
    apply (eq_div_iff (ne_of_gt hdn)).2
    rw [add_mul, mul_assoc, div_mul_cancel₀ _ (ne_of_gt hdn)]
    push_cast
    ring
  rw [hid]
  apply (div_le_div_iff₀ hdn hdns).2
  push_cast
  apply mul_le_mul_of_nonneg_left (by nlinarith) (mul_nonneg (by positivity) hu)

lemma gamma_eq_nat_mul (u : ℝ) (n : ℕ) (h : GammaValid u n) :
    (n : ℝ) * u * (1 + gamma u n) = gamma u n := by
  unfold gamma GammaValid at *
  have hd : 1 - (n : ℝ) * u ≠ 0 := by linarith
  field_simp [hd]
  ring

lemma recursiveSum_error_bound (fp : StandardAddModel) (n : ℕ)
    (v : Fin (n + 1) → ℝ) (hvalid : GammaValid fp.u (n + 1)) :
    |recursiveSum fp.fl_add (n + 1) v - ∑ i, v i| ≤
      gamma fp.u n * ∑ i, |v i| := by
  induction n with
  | zero =>
      simp [recursiveSum, gamma]
  | succ n ih =>
      let w : Fin (n + 1) → ℝ := fun i => v i.castSucc
      let a : ℝ := recursiveSum fp.fl_add (n + 1) w
      let t : ℝ := ∑ i, w i
      let x : ℝ := v (Fin.last (n + 1))
      let A : ℝ := ∑ i, |w i|
      have hsmall : GammaValid fp.u (n + 1) :=
        gammaValid_mono_nat fp.u_nonneg (by omega) hvalid
      have hi : |a - t| ≤ gamma fp.u n * A := by
        simpa [a, t, A, w] using ih w hsmall
      obtain ⟨δ, hδ, hround⟩ := fp.model_add a x
      have hrec : recursiveSum fp.fl_add (n + 2) v = fp.fl_add a x := by
        simp [recursiveSum, a, x, w]
      have habsone : |1 + δ| ≤ 1 + fp.u := by
        calc
          |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le 1 δ
          _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
      have ht : |t + x| ≤ A + |x| := by
        calc
          |t + x| ≤ |t| + |x| := abs_add_le t x
          _ ≤ A + |x| := by
            gcongr
            exact Finset.abs_sum_le_sum_abs _ _
      have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hAx : 0 ≤ A + |x| := add_nonneg hA (abs_nonneg _)
      have hstep := gamma_step_bound fp.u_nonneg hsmall
      rw [hrec, hround, Fin.sum_univ_castSucc v,
        Fin.sum_univ_castSucc (fun i => |v i|)]
      change |(a + x) * (1 + δ) - (t + x)| ≤
        gamma fp.u (n + 1) * (A + |x|)
      calc
        |(a + x) * (1 + δ) - (t + x)| =
            |(1 + δ) * (a - t) + δ * (t + x)| := by
              congr 1
              ring
        _ ≤ |1 + δ| * |a - t| + |δ| * |t + x| := by
              simpa [abs_mul] using
                (abs_add_le ((1 + δ) * (a - t)) (δ * (t + x)))
        _ ≤ (1 + fp.u) * (gamma fp.u n * A) + fp.u * (A + |x|) := by
              apply add_le_add
              · exact mul_le_mul habsone hi (abs_nonneg _) (by linarith [fp.u_nonneg])
              · exact mul_le_mul hδ ht (abs_nonneg _) fp.u_nonneg
        _ ≤ ((1 + fp.u) * gamma fp.u n + fp.u) * (A + |x|) := by
              have hnvalid : GammaValid fp.u n :=
                gammaValid_mono_nat fp.u_nonneg (by omega) hsmall
              have hg : 0 ≤ gamma fp.u n :=
                gamma_nonneg_of_valid fp.u_nonneg hnvalid
              have hextra : 0 ≤ (1 + fp.u) * gamma fp.u n * |x| := by
                exact mul_nonneg (mul_nonneg (by linarith [fp.u_nonneg]) hg) (abs_nonneg _)
              nlinarith
        _ ≤ gamma fp.u (n + 1) * (A + |x|) := by
              exact mul_le_mul_of_nonneg_right hstep hAx

lemma twoSumPrefix_eq_recursiveSum (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : k ≤ n) :
    twoSumPrefix fp v k hk =
      recursiveSum fp.fl_add (k + 1)
        (fun i : Fin (k + 1) =>
          v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩) := by
  induction k with
  | zero =>
      simp [twoSumPrefix, recursiveSum]
  | succ k ih =>
      have hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      rw [twoSumPrefix, Fin.foldl_succ_last]
      rw [fp.twoSum_high]
      change fp.fl_add (twoSumPrefix fp v k hk')
          (v ⟨k + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le (Fin.last k).isLt hk)⟩) = _
      simp only [recursiveSum]
      split <;> rename_i h
      · omega
      rw [ih hk']
      congr 1

lemma twoSumPrefix_succ (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : k + 1 ≤ n) :
    twoSumPrefix fp v (k + 1) hk =
      (fp.twoSum
        (twoSumPrefix fp v k (Nat.le_trans (Nat.le_succ k) hk))
        (v ⟨k + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le (Fin.last k).isLt hk)⟩)).1 := by
  rw [twoSumPrefix, Fin.foldl_succ_last]
  rfl

lemma fin_prefix_abs_sum_le {n : ℕ} (v : Fin (n + 1) → ℝ)
    (k : ℕ) (hk : k ≤ n) :
    (∑ i : Fin (k + 1),
      |v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩|) ≤
      ∑ i : Fin (n + 1), |v i| := by
  induction n generalizing k with
  | zero =>
      have : k = 0 := by omega
      subst k
      rfl
  | succ n ih =>
      by_cases htop : k = n + 1
      · subst k
        rfl
      · have hk' : k ≤ n := by omega
        have hsmall := ih (fun i : Fin (n + 1) => v i.castSucc) k hk'
        calc
          (∑ i : Fin (k + 1),
              |v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩|) ≤
              ∑ i : Fin (n + 1), |v i.castSucc| := by
                simpa using hsmall
          _ ≤ ∑ i : Fin (n + 2), |v i| := by
                rw [Fin.sum_univ_castSucc (fun i : Fin (n + 2) => |v i|)]
                exact le_add_of_nonneg_right
                  (abs_nonneg (v (Fin.last (n + 1))))

lemma twoSumPrefix_abs_le (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : k ≤ n)
    (hvalid : GammaValid fp.u (n + 1)) :
    |twoSumPrefix fp v k hk| ≤
      (1 + gamma fp.u n) * ∑ i, |v i| := by
  let w : Fin (k + 1) → ℝ := fun i =>
    v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩
  let p : ℝ := twoSumPrefix fp v k hk
  let t : ℝ := ∑ i, w i
  let A : ℝ := ∑ i, |w i|
  have hkvalid : GammaValid fp.u (k + 1) :=
    gammaValid_mono_nat fp.u_nonneg (by omega) hvalid
  have hp : p = recursiveSum fp.fl_add (k + 1) w := by
    simpa [p, w] using twoSumPrefix_eq_recursiveSum fp v k hk
  have herr : |p - t| ≤ gamma fp.u k * A := by
    rw [hp]
    simpa [t, A] using
      recursiveSum_error_bound fp.toStandardAddModel k w hkvalid
  have ht : |t| ≤ A := by
    exact Finset.abs_sum_le_sum_abs _ _
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hApart : A ≤ ∑ i, |v i| := by
    simpa [A, w] using fin_prefix_abs_sum_le v k hk
  have hnvalid : GammaValid fp.u n :=
    gammaValid_mono_nat fp.u_nonneg (by omega) hvalid
  have hgk : 0 ≤ gamma fp.u k :=
    gamma_nonneg_of_valid fp.u_nonneg
      (gammaValid_mono_nat fp.u_nonneg hk hnvalid)
  have hgn : 0 ≤ gamma fp.u n :=
    gamma_nonneg_of_valid fp.u_nonneg hnvalid
  have hgmono : gamma fp.u k ≤ gamma fp.u n :=
    gamma_mono_nat fp.u_nonneg hk hnvalid
  calc
    |p| = |(p - t) + t| := by ring_nf
    _ ≤ |p - t| + |t| := abs_add_le _ _
    _ ≤ gamma fp.u k * A + A := add_le_add herr ht
    _ = (1 + gamma fp.u k) * A := by ring
    _ ≤ (1 + gamma fp.u n) * A := by
      exact mul_le_mul_of_nonneg_right (by linarith) hA
    _ ≤ (1 + gamma fp.u n) * ∑ i, |v i| := by
      exact mul_le_mul_of_nonneg_left hApart (by linarith)

lemma twoSumCorrection_sum_abs_le (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (hvalid : GammaValid fp.u (n + 1)) :
    (∑ i : Fin n, |twoSumCorrection fp v i|) ≤
      gamma fp.u n * ∑ i : Fin (n + 1), |v i| := by
  let S : ℝ := ∑ i : Fin (n + 1), |v i|
  have hnvalid : GammaValid fp.u n :=
    gammaValid_mono_nat fp.u_nonneg (by omega) hvalid
  have hpoint : ∀ i : Fin n,
      |twoSumCorrection fp v i| ≤ fp.u * (1 + gamma fp.u n) * S := by
    intro i
    have hi : i.val + 1 ≤ n := Nat.succ_le_iff.mpr i.isLt
    have hp := twoSumPrefix_abs_le fp v (i.val + 1) hi hvalid
    calc
      |twoSumCorrection fp v i| ≤
          fp.u *
            |(fp.twoSum
              (twoSumPrefix fp v i.val (Nat.le_of_lt i.isLt))
              (v ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)).1| :=
        fp.twoSum_low_le _ _
      _ = fp.u * |twoSumPrefix fp v (i.val + 1) hi| := by
        rw [twoSumPrefix_succ fp v i.val hi]
      _ ≤ fp.u * ((1 + gamma fp.u n) * S) := by
        exact mul_le_mul_of_nonneg_left (by simpa [S] using hp) fp.u_nonneg
      _ = fp.u * (1 + gamma fp.u n) * S := by ring
  calc
    (∑ i : Fin n, |twoSumCorrection fp v i|) ≤
        ∑ _i : Fin n, fp.u * (1 + gamma fp.u n) * S := by
          exact Finset.sum_le_sum fun i _ => hpoint i
    _ = (n : ℝ) * fp.u * (1 + gamma fp.u n) * S := by
          simp
          ring
    _ = gamma fp.u n * ∑ i : Fin (n + 1), |v i| := by
          rw [gamma_eq_nat_mul fp.u n hnvalid]

lemma twoSumPrefix_add_corrections (fp : ErrorFreeAddModel) {n : ℕ}
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
      have hih := ih hk'
      have hpair := fp.twoSum_exact
        (twoSumPrefix fp v k hk')
        (v ⟨k + 1,
          Nat.succ_lt_succ (Nat.lt_of_lt_of_le (Fin.last k).isLt hk)⟩)
      have hp := twoSumPrefix_succ fp v k hk
      rw [Fin.sum_univ_castSucc
          (fun i : Fin (k + 1) =>
            twoSumCorrection fp v
              ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩),
        Fin.sum_univ_castSucc
          (fun i : Fin (k + 2) =>
            v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩)]
      change twoSumPrefix fp v (k + 1) hk +
          ((∑ i : Fin k,
              twoSumCorrection fp v
                ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk'⟩) +
            twoSumCorrection fp v
              ⟨k, Nat.lt_of_succ_le hk⟩) =
        (∑ i : Fin (k + 1),
            v ⟨i.val,
              Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk')⟩) +
          v ⟨k + 1,
            Nat.succ_lt_succ (Nat.lt_of_lt_of_le (Fin.last k).isLt hk)⟩
      change twoSumPrefix fp v (k + 1) hk +
          ((∑ i : Fin k,
              twoSumCorrection fp v
                ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk'⟩) +
            (fp.twoSum
              (twoSumPrefix fp v k hk')
              (v ⟨k + 1,
                Nat.succ_lt_succ
                  (Nat.lt_of_lt_of_le (Fin.last k).isLt hk)⟩)).2) = _
      rw [hp]
      linarith

lemma vecSum_exact (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) :
    ∑ i : Fin (n + 1), vecSum fp v i = ∑ i : Fin (n + 1), v i := by
  rw [Fin.sum_univ_castSucc (fun i : Fin (n + 1) => vecSum fp v i)]
  simp only [vecSum, Fin.lastCases_castSucc, Fin.lastCases_last]
  rw [add_comm]
  exact twoSumPrefix_add_corrections fp v n (Nat.le_refl n)

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
      rw [show (0 : Fin 1) = Fin.last 0 by rfl, Fin.lastCases_last]
      simp only [sub_self, abs_zero]
      exact mul_nonneg fp.u_nonneg (abs_nonneg _)
  | succ m =>
      let q : Fin (m + 1) → ℝ := fun i => twoSumCorrection fp v i
      let p : ℝ := twoSumPrefix fp v (m + 1) (Nat.le_refl (m + 1))
      let r : ℝ := recursiveSum fp.fl_add (m + 1) q
      let s : ℝ := ∑ i : Fin (m + 2), v i
      let S : ℝ := ∑ i : Fin (m + 2), |v i|
      let Q : ℝ := ∑ i : Fin (m + 1), |q i|
      have hsmall : GammaValid fp.u (m + 1) :=
        gammaValid_mono_nat fp.u_nonneg (by omega) hvalid
      have hmvalid : GammaValid fp.u m :=
        gammaValid_mono_nat fp.u_nonneg (by omega) hsmall
      have hr : |r - ∑ i, q i| ≤ gamma fp.u m * Q := by
        simpa [r, Q] using
          recursiveSum_error_bound fp.toStandardAddModel m q hsmall
      have hQ : Q ≤ gamma fp.u (m + 1) * S := by
        simpa [Q, q, S] using twoSumCorrection_sum_abs_le fp v hvalid
      have hexact : p + ∑ i, q i = s := by
        simpa [p, q, s] using
          twoSumPrefix_add_corrections fp v (m + 1) (Nat.le_refl (m + 1))
      have hsum2 : sum2 fp v = fp.fl_add r p := by
        simp only [sum2, sumK, iteratedVecSum]
        change recursiveSum fp.fl_add (m + 2) (vecSum fp v) = fp.fl_add r p
        rw [show recursiveSum fp.fl_add (m + 2) (vecSum fp v) =
            fp.fl_add
              (recursiveSum fp.fl_add (m + 1)
                (fun i => vecSum fp v i.castSucc))
              (vecSum fp v (Fin.last (m + 1))) by
                simp [recursiveSum]]
        simp only [vecSum, Fin.lastCases_castSucc, Fin.lastCases_last]
        rfl
      obtain ⟨δ, hδ, hround⟩ := fp.model_add r p
      have habsone : |1 + δ| ≤ 1 + fp.u := by
        calc
          |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le 1 δ
          _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
      have hQnonneg : 0 ≤ Q := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hSnonneg : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hgm : 0 ≤ gamma fp.u m :=
        gamma_nonneg_of_valid fp.u_nonneg hmvalid
      have hgn : 0 ≤ gamma fp.u (m + 1) :=
        gamma_nonneg_of_valid fp.u_nonneg hsmall
      have hstep := gamma_step_bound fp.u_nonneg hsmall
      have hcoef : (1 + fp.u) * gamma fp.u m ≤ gamma fp.u (m + 1) := by
        linarith [fp.u_nonneg]
      have hcorr :
          (1 + fp.u) * (gamma fp.u m * Q) ≤
            (gamma fp.u (m + 1)) ^ 2 * S := by
        calc
          (1 + fp.u) * (gamma fp.u m * Q) =
              ((1 + fp.u) * gamma fp.u m) * Q := by ring
          _ ≤ gamma fp.u (m + 1) * Q :=
              mul_le_mul_of_nonneg_right hcoef hQnonneg
          _ ≤ gamma fp.u (m + 1) *
              (gamma fp.u (m + 1) * S) :=
              mul_le_mul_of_nonneg_left hQ hgn
          _ = (gamma fp.u (m + 1)) ^ 2 * S := by ring
      rw [hsum2, hround]
      change |(r + p) * (1 + δ) - s| ≤
        fp.u * |s| + (gamma fp.u (m + 1)) ^ 2 * S
      calc
        |(r + p) * (1 + δ) - s| =
            |(1 + δ) * (r - ∑ i, q i) + δ * s| := by
              congr 1
              rw [← hexact]
              ring
        _ ≤ |1 + δ| * |r - ∑ i, q i| + |δ| * |s| := by
              simpa [abs_mul] using
                (abs_add_le
                  ((1 + δ) * (r - ∑ i, q i)) (δ * s))
        _ ≤ (1 + fp.u) * (gamma fp.u m * Q) + fp.u * |s| := by
              apply add_le_add
              · exact mul_le_mul habsone hr (abs_nonneg _) (by linarith [fp.u_nonneg])
              · exact mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
        _ ≤ (gamma fp.u (m + 1)) ^ 2 * S + fp.u * |s| :=
              add_le_add hcorr le_rfl
        _ = fp.u * |s| + (gamma fp.u (m + 1)) ^ 2 * S := by ring

end HighamBench
