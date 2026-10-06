import HighamBench.P02Definitions

namespace HighamBench

open scoped BigOperators

private lemma gamma_nonneg' (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (hv : GammaValid u n) : 0 ≤ gamma u n := by
  unfold GammaValid at hv
  unfold gamma
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) hu) (le_of_lt (sub_pos.mpr hv))

private lemma one_add_gamma_eq' (u : ℝ) (n : ℕ)
    (hv : GammaValid u n) :
    1 + gamma u n = 1 / (1 - (n : ℝ) * u) := by
  unfold GammaValid at hv
  unfold gamma
  have hd : 1 - (n : ℝ) * u ≠ 0 := ne_of_gt (sub_pos.mpr hv)
  field_simp
  ring

private lemma gamma_eq_one_div_sub_one' (u : ℝ) (n : ℕ)
    (hv : GammaValid u n) :
    gamma u n = 1 / (1 - (n : ℝ) * u) - 1 := by
  linarith [one_add_gamma_eq' u n hv]

private lemma gammaValid_mono' (u : ℝ) {m n : ℕ} (hu : 0 ≤ u)
    (hmn : m ≤ n) (hv : GammaValid u n) : GammaValid u m := by
  unfold GammaValid at hv ⊢
  have hc : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  nlinarith

private lemma one_add_gamma_step' (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (hv : GammaValid u (n + 1)) :
    (1 + u) * (1 + gamma u n) ≤ 1 + gamma u (n + 1) := by
  have hvn : GammaValid u n :=
    gammaValid_mono' u hu (Nat.le_succ n) hv
  rw [one_add_gamma_eq' u n hvn, one_add_gamma_eq' u (n + 1) hv]
  have hd₀ : 0 < 1 - (n : ℝ) * u := by
    exact sub_pos.mpr (show (n : ℝ) * u < 1 from hvn)
  have hd₁ : 0 < 1 - ((n + 1 : ℕ) : ℝ) * u := by
    exact sub_pos.mpr (show ((n + 1 : ℕ) : ℝ) * u < 1 from hv)
  have hcross :
      (1 + u) / (1 - (n : ℝ) * u) ≤
        1 / (1 - ((n + 1 : ℕ) : ℝ) * u) := by
    apply (div_le_div_iff₀ hd₀ hd₁).2
    norm_num [Nat.cast_add, Nat.cast_one]
    have hs : 0 ≤ ((n : ℝ) + 1) * u ^ 2 :=
      mul_nonneg (by positivity) (sq_nonneg u)
    nlinarith
  simpa [div_eq_mul_inv] using hcross

private lemma gamma_correction_step' (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (hv : GammaValid u (n + 1)) :
    gamma u n + u * (1 + gamma u (n + 1)) ≤ gamma u (n + 1) := by
  have hvn : GammaValid u n :=
    gammaValid_mono' u hu (Nat.le_succ n) hv
  rw [one_add_gamma_eq' u (n + 1) hv,
    gamma_eq_one_div_sub_one' u n hvn,
    gamma_eq_one_div_sub_one' u (n + 1) hv,
    ]
  have hd₀ : 0 < 1 - (n : ℝ) * u := by
    exact sub_pos.mpr (show (n : ℝ) * u < 1 from hvn)
  have hd₁ : 0 < 1 - ((n + 1 : ℕ) : ℝ) * u := by
    exact sub_pos.mpr (show ((n + 1 : ℕ) : ℝ) * u < 1 from hv)
  have hfrac :
      1 / (1 - (n : ℝ) * u) ≤
        (1 - u) / (1 - ((n + 1 : ℕ) : ℝ) * u) := by
    apply (div_le_div_iff₀ hd₀ hd₁).2
    norm_num [Nat.cast_add, Nat.cast_one]
    have hs : 0 ≤ (n : ℝ) * u ^ 2 :=
      mul_nonneg (Nat.cast_nonneg n) (sq_nonneg u)
    nlinarith
  calc
    1 / (1 - (n : ℝ) * u) - 1 +
          u * (1 / (1 - ((n + 1 : ℕ) : ℝ) * u))
        ≤ (1 - u) / (1 - ((n + 1 : ℕ) : ℝ) * u) - 1 +
          u * (1 / (1 - ((n + 1 : ℕ) : ℝ) * u)) := by linarith
    _ = 1 / (1 - ((n + 1 : ℕ) : ℝ) * u) - 1 := by ring

private lemma gamma_recursive_step' (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (hv : GammaValid u (n + 1)) :
    (1 + u) * gamma u n + u ≤ gamma u (n + 1) := by
  have h := one_add_gamma_step' u n hu hv
  nlinarith

private lemma gamma_mul_step' (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (hv : GammaValid u (n + 1)) :
    (1 + u) * gamma u n ≤ gamma u (n + 1) := by
  have h := gamma_recursive_step' u n hu hv
  linarith

private lemma twoSumPrefix_init (fp : ErrorFreeAddModel) {n k : ℕ}
    (v : Fin (n + 2) → ℝ) (hk : k ≤ n) :
    twoSumPrefix fp v k (hk.trans (Nat.le_succ n)) =
      twoSumPrefix fp (fun i : Fin (n + 1) => v i.castSucc) k hk := by
  simp only [twoSumPrefix]
  congr 1

private lemma twoSumPrefix_succ (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 2) → ℝ) :
    twoSumPrefix fp v (n + 1) (Nat.le_refl (n + 1)) =
      (fp.twoSum
        (twoSumPrefix fp (fun i : Fin (n + 1) => v i.castSucc) n (Nat.le_refl n))
        (v (Fin.last (n + 1)))).1 := by
  simp only [twoSumPrefix, Fin.foldl_succ_last]
  congr 2

private lemma twoSumCorrection_castSucc (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 2) → ℝ) (i : Fin n) :
    twoSumCorrection fp v i.castSucc =
      twoSumCorrection fp (fun j : Fin (n + 1) => v j.castSucc) i := by
  simp only [twoSumCorrection, Fin.coe_castSucc]
  rw [twoSumPrefix_init fp v (Nat.le_of_lt i.isLt)]
  congr 2

private lemma twoSumCorrection_last (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 2) → ℝ) :
    twoSumCorrection fp v (Fin.last n) =
      (fp.twoSum
        (twoSumPrefix fp (fun j : Fin (n + 1) => v j.castSucc) n (Nat.le_refl n))
        (v (Fin.last (n + 1)))).2 := by
  simp only [twoSumCorrection, Fin.val_last]
  rw [twoSumPrefix_init fp v (Nat.le_refl n)]
  congr 2

private lemma twoSumPrefix_abs_le (fp : ErrorFreeAddModel) :
    ∀ (n : ℕ) (v : Fin (n + 1) → ℝ), GammaValid fp.u n →
      |twoSumPrefix fp v n (Nat.le_refl n)| ≤
        (1 + gamma fp.u n) * ∑ i : Fin (n + 1), |v i| := by
  intro n
  induction n with
  | zero =>
      intro v hv
      simp [twoSumPrefix, gamma]
  | succ n ih =>
      intro v hv
      let w : Fin (n + 1) → ℝ := fun i => v i.castSucc
      have hvn : GammaValid fp.u n :=
        gammaValid_mono' fp.u fp.u_nonneg (Nat.le_succ n) hv
      have hpre := ih w hvn
      let p := twoSumPrefix fp w n (Nat.le_refl n)
      let x := v (Fin.last (n + 1))
      obtain ⟨δ, hδ, hadd⟩ := fp.model_add p x
      have hδ' : |1 + δ| ≤ 1 + fp.u := by
        calc
          |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
          _ ≤ 1 + fp.u := by norm_num; linarith
      have hfac : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
      have hsum0 : 0 ≤ ∑ i : Fin (n + 1), |w i| :=
        Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hγ0 : 0 ≤ gamma fp.u n :=
        gamma_nonneg' fp.u n fp.u_nonneg hvn
      have hcoef :
          (1 + fp.u) * (1 + gamma fp.u n) ≤
            1 + gamma fp.u (n + 1) :=
        one_add_gamma_step' fp.u n fp.u_nonneg hv
      have hxcoef : 1 + fp.u ≤ 1 + gamma fp.u (n + 1) := by
        calc
          1 + fp.u = (1 + fp.u) * 1 := by ring
          _ ≤ (1 + fp.u) * (1 + gamma fp.u n) := by
            exact mul_le_mul_of_nonneg_left (by linarith) hfac
          _ ≤ 1 + gamma fp.u (n + 1) := hcoef
      rw [twoSumPrefix_succ fp v, fp.twoSum_high, hadd, abs_mul]
      calc
        |p + x| * |1 + δ| ≤ (|p| + |x|) * (1 + fp.u) := by
          exact mul_le_mul (abs_add_le _ _) hδ' (abs_nonneg _)
            (add_nonneg (abs_nonneg _) (abs_nonneg _))
        _ ≤ ((1 + gamma fp.u n) * (∑ i : Fin (n + 1), |w i|) + |x|) *
              (1 + fp.u) := by
          exact mul_le_mul_of_nonneg_right (add_le_add hpre (le_refl _)) hfac
        _ = ((1 + fp.u) * (1 + gamma fp.u n)) *
                (∑ i : Fin (n + 1), |w i|) +
              (1 + fp.u) * |x| := by ring
        _ ≤ (1 + gamma fp.u (n + 1)) *
                (∑ i : Fin (n + 1), |w i|) +
              (1 + gamma fp.u (n + 1)) * |x| := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right hcoef hsum0)
            (mul_le_mul_of_nonneg_right hxcoef (abs_nonneg x))
        _ = (1 + gamma fp.u (n + 1)) *
              ∑ i : Fin (n + 2), |v i| := by
          have hsum :
              ∑ i : Fin (n + 2), |v i| =
                (∑ i : Fin (n + 1), |w i|) + |x| := by
            simpa [w, x] using
              (Fin.sum_univ_castSucc (fun i : Fin (n + 2) => |v i|))
          rw [hsum]
          ring

private lemma twoSumCorrection_abs_sum_le (fp : ErrorFreeAddModel) :
    ∀ (n : ℕ) (v : Fin (n + 1) → ℝ), GammaValid fp.u (n + 1) →
      (∑ i : Fin n, |twoSumCorrection fp v i|) ≤
        gamma fp.u n * ∑ i : Fin (n + 1), |v i| := by
  intro n
  induction n with
  | zero =>
      intro v hv
      simp [gamma]
  | succ n ih =>
      intro v hv
      let w : Fin (n + 1) → ℝ := fun i => v i.castSucc
      let p := twoSumPrefix fp w n (Nat.le_refl n)
      let x := v (Fin.last (n + 1))
      let hi := (fp.twoSum p x).1
      let lo := (fp.twoSum p x).2
      have hv₁ : GammaValid fp.u (n + 1) :=
        gammaValid_mono' fp.u fp.u_nonneg (Nat.le_succ (n + 1)) hv
      have hprior := ih w hv₁
      have hprefix := twoSumPrefix_abs_le fp (n + 1) v hv₁
      have hlow : |lo| ≤ fp.u * |hi| := fp.twoSum_low_le p x
      have hhigh :
          |hi| ≤ (1 + gamma fp.u (n + 1)) *
            ∑ i : Fin (n + 2), |v i| := by
        simpa [hi, p, x, twoSumPrefix_succ fp v] using hprefix
      have hlast :
          |lo| ≤ fp.u * (1 + gamma fp.u (n + 1)) *
            ∑ i : Fin (n + 2), |v i| := by
        calc
          |lo| ≤ fp.u * |hi| := hlow
          _ ≤ fp.u * ((1 + gamma fp.u (n + 1)) *
              ∑ i : Fin (n + 2), |v i|) :=
            mul_le_mul_of_nonneg_left hhigh fp.u_nonneg
          _ = fp.u * (1 + gamma fp.u (n + 1)) *
              ∑ i : Fin (n + 2), |v i| := by ring
      have hγ0 : 0 ≤ gamma fp.u n :=
        gamma_nonneg' fp.u n fp.u_nonneg
          (gammaValid_mono' fp.u fp.u_nonneg (Nat.le_succ n) hv₁)
      have hsum :
          ∑ i : Fin (n + 2), |v i| =
            (∑ i : Fin (n + 1), |w i|) + |x| := by
        simpa [w, x] using
          (Fin.sum_univ_castSucc (fun i : Fin (n + 2) => |v i|))
      have hinit_le :
          (∑ i : Fin (n + 1), |w i|) ≤
            ∑ i : Fin (n + 2), |v i| := by
        rw [hsum]
        exact le_add_of_nonneg_right (abs_nonneg x)
      have hcoef := gamma_correction_step' fp.u n fp.u_nonneg hv₁
      rw [Fin.sum_univ_castSucc]
      simp only [twoSumCorrection_castSucc fp v,
        twoSumCorrection_last fp v]
      change (∑ i : Fin n, |twoSumCorrection fp w i|) + |lo| ≤
        gamma fp.u (n + 1) * ∑ i : Fin (n + 2), |v i|
      calc
        (∑ i : Fin n, |twoSumCorrection fp w i|) + |lo|
            ≤ gamma fp.u n * (∑ i : Fin (n + 1), |w i|) +
                (fp.u * (1 + gamma fp.u (n + 1)) *
                  ∑ i : Fin (n + 2), |v i|) := add_le_add hprior hlast
        _ ≤ gamma fp.u n * (∑ i : Fin (n + 2), |v i|) +
                (fp.u * (1 + gamma fp.u (n + 1)) *
                  ∑ i : Fin (n + 2), |v i|) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hinit_le hγ0) (le_refl _)
        _ = (gamma fp.u n + fp.u * (1 + gamma fp.u (n + 1))) *
              ∑ i : Fin (n + 2), |v i| := by ring
        _ ≤ gamma fp.u (n + 1) * ∑ i : Fin (n + 2), |v i| := by
          exact mul_le_mul_of_nonneg_right hcoef
            (Finset.sum_nonneg fun _ _ => abs_nonneg _)

private lemma twoSum_exact_sum (fp : ErrorFreeAddModel) :
    ∀ (n : ℕ) (v : Fin (n + 1) → ℝ),
      (∑ i : Fin n, twoSumCorrection fp v i) +
          twoSumPrefix fp v n (Nat.le_refl n) =
        ∑ i : Fin (n + 1), v i := by
  intro n
  induction n with
  | zero =>
      intro v
      simp [twoSumPrefix]
  | succ n ih =>
      intro v
      let w : Fin (n + 1) → ℝ := fun i => v i.castSucc
      let p := twoSumPrefix fp w n (Nat.le_refl n)
      let x := v (Fin.last (n + 1))
      let hi := (fp.twoSum p x).1
      let lo := (fp.twoSum p x).2
      have hold :
          (∑ i : Fin n, twoSumCorrection fp w i) + p =
            ∑ i : Fin (n + 1), w i := ih w
      have hpair : hi + lo = p + x := fp.twoSum_exact p x
      have hsum :
          ∑ i : Fin (n + 2), v i =
            (∑ i : Fin (n + 1), w i) + x := by
        simpa [w, x] using
          (Fin.sum_univ_castSucc (fun i : Fin (n + 2) => v i))
      rw [Fin.sum_univ_castSucc]
      simp only [twoSumCorrection_castSucc fp v,
        twoSumCorrection_last fp v, twoSumPrefix_succ fp v]
      change (∑ i : Fin n, twoSumCorrection fp w i) + lo + hi =
        ∑ i : Fin (n + 2), v i
      rw [hsum]
      linarith

private lemma vecSum_exact_sum (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) :
    ∑ i : Fin (n + 1), vecSum fp v i = ∑ i : Fin (n + 1), v i := by
  rw [Fin.sum_univ_castSucc]
  simp only [vecSum, Fin.lastCases_castSucc, Fin.lastCases_last]
  exact twoSum_exact_sum fp n v

private lemma vecSum_abs_init_le (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (hv : GammaValid fp.u (n + 1)) :
    (∑ i : Fin n, |vecSum fp v i.castSucc|) ≤
      gamma fp.u n * ∑ i : Fin (n + 1), |v i| := by
  simpa [vecSum] using twoSumCorrection_abs_sum_le fp n v hv

private lemma recursiveSum_forward_error (fp : StandardAddModel) :
    ∀ (k : ℕ) (v : Fin k → ℝ), GammaValid fp.u k →
      |recursiveSum fp.fl_add k v - ∑ i : Fin k, v i| ≤
        gamma fp.u (k - 1) * ∑ i : Fin k, |v i| := by
  intro k
  induction k with
  | zero =>
      intro v hv
      simp [recursiveSum, gamma]
  | succ k ih =>
      cases k with
      | zero =>
          intro v hv
          simp [recursiveSum, gamma]
      | succ k =>
          intro v hv
          let w : Fin (k + 1) → ℝ := fun i => v i.castSucc
          let r := recursiveSum fp.fl_add (k + 1) w
          let t := ∑ i : Fin (k + 1), w i
          let x := v (Fin.last (k + 1))
          let a := ∑ i : Fin (k + 1), |w i|
          let A := ∑ i : Fin (k + 2), |v i|
          have hv₁ : GammaValid fp.u (k + 1) :=
            gammaValid_mono' fp.u fp.u_nonneg (Nat.le_succ (k + 1)) hv
          have hir : |r - t| ≤ gamma fp.u k * a := by
            simpa [r, t, a] using ih w hv₁
          obtain ⟨δ, hδ, hadd⟩ := fp.model_add r x
          have hδone : |1 + δ| ≤ 1 + fp.u := by
            calc
              |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
              _ ≤ 1 + fp.u := by norm_num; linarith
          have hfac : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
          have ha0 : 0 ≤ a := by
            exact Finset.sum_nonneg fun _ _ => abs_nonneg _
          have hγ0 : 0 ≤ gamma fp.u k :=
            gamma_nonneg' fp.u k fp.u_nonneg
              (gammaValid_mono' fp.u fp.u_nonneg (Nat.le_succ k) hv₁)
          have ht : |t| ≤ a := by
            simpa [t, a] using
              (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := w))
          have htx : |t + x| ≤ A := by
            have hsumA : A = a + |x| := by
              simpa [A, a, w, x] using
                (Fin.sum_univ_castSucc (fun i : Fin (k + 2) => |v i|))
            rw [hsumA]
            exact (abs_add_le t x).trans (add_le_add ht (le_refl _))
          have haA : a ≤ A := by
            have hsumA : A = a + |x| := by
              simpa [A, a, w, x] using
                (Fin.sum_univ_castSucc (fun i : Fin (k + 2) => |v i|))
            rw [hsumA]
            exact le_add_of_nonneg_right (abs_nonneg x)
          have hA0 : 0 ≤ A := by
            exact Finset.sum_nonneg fun _ _ => abs_nonneg _
          have hfirst :
              |1 + δ| * |r - t| ≤
                ((1 + fp.u) * gamma fp.u k) * a := by
            calc
              |1 + δ| * |r - t| ≤ (1 + fp.u) * (gamma fp.u k * a) := by
                exact mul_le_mul hδone hir (abs_nonneg _)
                  hfac
              _ = ((1 + fp.u) * gamma fp.u k) * a := by ring
          have hsecond : |δ| * |t + x| ≤ fp.u * A := by
            exact mul_le_mul hδ htx (abs_nonneg _)
              fp.u_nonneg
          have hsum :
              ∑ i : Fin (k + 2), v i = t + x := by
            simpa [t, w, x] using
              (Fin.sum_univ_castSucc (fun i : Fin (k + 2) => v i))
          have hcoef := gamma_recursive_step' fp.u k fp.u_nonneg hv₁
          have hrec :
              recursiveSum fp.fl_add (k + 2) v = fp.fl_add r x := by
            rw [recursiveSum]
            simp only [reduceCtorEq, ↓reduceDIte]
            congr 2
          rw [hrec]
          change |fp.fl_add r x - ∑ i : Fin (k + 2), v i| ≤
            gamma fp.u (k + 1) * A
          rw [hadd, hsum]
          calc
            |(r + x) * (1 + δ) - (t + x)| =
                |(1 + δ) * (r - t) + δ * (t + x)| := by
              congr 1
              ring
            _ ≤ |1 + δ| * |r - t| + |δ| * |t + x| := by
              simpa [abs_mul] using
                (abs_add_le ((1 + δ) * (r - t)) (δ * (t + x)))
            _ ≤ ((1 + fp.u) * gamma fp.u k) * a + fp.u * A :=
              add_le_add hfirst hsecond
            _ ≤ ((1 + fp.u) * gamma fp.u k) * A + fp.u * A := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left haA (mul_nonneg hfac hγ0))
                (le_refl _)
            _ = ((1 + fp.u) * gamma fp.u k + fp.u) * A := by ring
            _ ≤ gamma fp.u (k + 1) * A :=
              mul_le_mul_of_nonneg_right hcoef hA0

theorem p02_t1_sum2_error_bound
    (fp : ErrorFreeAddModel) (n : ℕ) (v : Fin (n + 1) → ℝ)
    (hvalid : GammaValid fp.u (n + 1)) :
    |sum2 fp v - ∑ i : Fin (n + 1), v i| ≤
      fp.u * |∑ i : Fin (n + 1), v i| +
        (gamma fp.u n) ^ 2 * ∑ i : Fin (n + 1), |v i| := by
  -- PROOF_START P02-T1-H001
  cases n with
  | zero =>
      simp [sum2, sumK, iteratedVecSum, recursiveSum, vecSum,
        twoSumPrefix, gamma]
      rw [show (0 : Fin 1) = Fin.last 0 by ext <;> simp,
        Fin.lastCases_last]
      simpa using mul_nonneg fp.u_nonneg (abs_nonneg (v (Fin.last 0)))
  | succ n =>
      let q : Fin (n + 2) → ℝ := vecSum fp v
      let c : Fin (n + 1) → ℝ := fun i => q i.castSucc
      let r := recursiveSum fp.fl_add (n + 1) c
      let hi := q (Fin.last (n + 1))
      let cs := ∑ i : Fin (n + 1), c i
      let s := ∑ i : Fin (n + 2), v i
      let C := ∑ i : Fin (n + 1), |c i|
      let S := ∑ i : Fin (n + 2), |v i|
      have hv₁ : GammaValid fp.u (n + 1) :=
        gammaValid_mono' fp.u fp.u_nonneg (Nat.le_succ (n + 1)) hvalid
      have herr : |r - cs| ≤ gamma fp.u n * C := by
        simpa [r, cs, C, c] using
          recursiveSum_forward_error fp.toStandardAddModel (n + 1) c hv₁
      have hcorr : C ≤ gamma fp.u (n + 1) * S := by
        simpa [C, S, c, q] using vecSum_abs_init_le fp v hvalid
      have hexact : s = cs + hi := by
        calc
          s = ∑ i : Fin (n + 2), q i := by
            simpa [s, q] using (vecSum_exact_sum fp v).symm
          _ = cs + hi := by
            simpa [cs, hi, c] using
              (Fin.sum_univ_castSucc (fun i : Fin (n + 2) => q i))
      have hrec :
          recursiveSum fp.fl_add (n + 2) q = fp.fl_add r hi := by
        rw [recursiveSum]
        simp only [reduceCtorEq, ↓reduceDIte]
        congr 2
      have hsum2 : sum2 fp v = fp.fl_add r hi := by
        rw [sum2, sumK]
        change recursiveSum fp.fl_add (n + 2) q = fp.fl_add r hi
        exact hrec
      obtain ⟨δ, hδ, hadd⟩ := fp.model_add r hi
      have hδone : |1 + δ| ≤ 1 + fp.u := by
        calc
          |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
          _ ≤ 1 + fp.u := by norm_num; linarith
      have hfac : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
      have hγn0 : 0 ≤ gamma fp.u n :=
        gamma_nonneg' fp.u n fp.u_nonneg
          (gammaValid_mono' fp.u fp.u_nonneg (Nat.le_succ n) hv₁)
      have hγ0 : 0 ≤ gamma fp.u (n + 1) :=
        gamma_nonneg' fp.u (n + 1) fp.u_nonneg hv₁
      have hC0 : 0 ≤ C := by
        exact Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hS0 : 0 ≤ S := by
        exact Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hfirst :
          |1 + δ| * |r - cs| ≤
            ((1 + fp.u) * gamma fp.u n) * C := by
        calc
          |1 + δ| * |r - cs| ≤ (1 + fp.u) * (gamma fp.u n * C) := by
            exact mul_le_mul hδone herr (abs_nonneg _) hfac
          _ = ((1 + fp.u) * gamma fp.u n) * C := by ring
      have hmain :
          ((1 + fp.u) * gamma fp.u n) * C ≤
            (gamma fp.u (n + 1)) ^ 2 * S := by
        have hstep := gamma_mul_step' fp.u n fp.u_nonneg hv₁
        calc
          ((1 + fp.u) * gamma fp.u n) * C
              ≤ ((1 + fp.u) * gamma fp.u n) *
                  (gamma fp.u (n + 1) * S) :=
            mul_le_mul_of_nonneg_left hcorr (mul_nonneg hfac hγn0)
          _ = (((1 + fp.u) * gamma fp.u n) * gamma fp.u (n + 1)) * S := by
            ring
          _ ≤ (gamma fp.u (n + 1) * gamma fp.u (n + 1)) * S := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hstep hγ0) hS0
          _ = (gamma fp.u (n + 1)) ^ 2 * S := by ring
      rw [hsum2, hadd]
      change |(r + hi) * (1 + δ) - s| ≤
        fp.u * |s| + (gamma fp.u (n + 1)) ^ 2 * S
      rw [hexact]
      calc
        |(r + hi) * (1 + δ) - (cs + hi)| =
            |(1 + δ) * (r - cs) + δ * (cs + hi)| := by
          congr 1
          ring
        _ ≤ |1 + δ| * |r - cs| + |δ| * |cs + hi| := by
          simpa [abs_mul] using
            (abs_add_le ((1 + δ) * (r - cs)) (δ * (cs + hi)))
        _ ≤ ((1 + fp.u) * gamma fp.u n) * C + fp.u * |cs + hi| := by
          exact add_le_add hfirst
            (mul_le_mul_of_nonneg_right hδ (abs_nonneg _))
        _ ≤ (gamma fp.u (n + 1)) ^ 2 * S + fp.u * |cs + hi| :=
          add_le_add hmain (le_refl _)
        _ = fp.u * |cs + hi| + (gamma fp.u (n + 1)) ^ 2 * S := by ring

end HighamBench
