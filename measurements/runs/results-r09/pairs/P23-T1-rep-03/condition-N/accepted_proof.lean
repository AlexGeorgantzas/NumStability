import HighamBench.P23Definitions
import Mathlib

namespace HighamBench

open scoped BigOperators

private lemma p23_gamma_nonneg {u : ℝ} {m : ℕ} (hu : 0 ≤ u)
    (hv : P23GammaValid u m) : 0 ≤ p23Gamma u m := by
  unfold p23Gamma P23GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (le_of_lt (sub_pos.mpr hv))

private lemma p23_gamma_step_coeff {u : ℝ} {m : ℕ} (hu : 0 ≤ u)
    (hv : P23GammaValid u (m + 1)) :
    p23Gamma u m * (1 + u) + u ≤ p23Gamma u (m + 1) := by
  have hv' : ((m + 1 : ℕ) : ℝ) * u < 1 := hv
  have hm : (m : ℝ) * u < 1 := by
    push_cast at hv'
    nlinarith [mul_nonneg (Nat.cast_nonneg m) hu]
  have hd : 0 < 1 - (m : ℝ) * u := sub_pos.mpr hm
  have hd' : 0 < 1 - ((m + 1 : ℕ) : ℝ) * u := sub_pos.mpr hv'
  have heq :
      p23Gamma u m * (1 + u) + u =
        (((m + 1 : ℕ) : ℝ) * u) / (1 - (m : ℝ) * u) := by
    unfold p23Gamma
    field_simp [ne_of_gt hd]
    push_cast
    ring
  rw [heq]
  unfold p23Gamma
  apply div_le_div_of_nonneg_left
  · exact mul_nonneg (Nat.cast_nonneg _) hu
  · exact hd'
  · push_cast
    nlinarith

private lemma p23_gamma_mono {u : ℝ} {a b : ℕ} (hu : 0 ≤ u)
    (hab : a ≤ b) (hv : P23GammaValid u b) :
    p23Gamma u a ≤ p23Gamma u b := by
  have hb : (b : ℝ) * u < 1 := hv
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have ha : (a : ℝ) * u < 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hab' hu]
  unfold p23Gamma
  apply (div_le_div_iff₀ (sub_pos.mpr ha) (sub_pos.mpr hb)).2
  nlinarith [mul_le_mul_of_nonneg_right hab' hu]

private lemma p23_valid_of_le {u : ℝ} {a b : ℕ} (hu : 0 ≤ u)
    (hab : a ≤ b) (hv : P23GammaValid u b) : P23GammaValid u a := by
  unfold P23GammaValid at hv ⊢
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hab' hu) hv

private lemma p23_two_rounds_coeff {u : ℝ} {m : ℕ} (hu : 0 ≤ u)
    (hm : 1 ≤ m) (hv : P23GammaValid u (m + 1)) :
    2 * u + u ^ 2 ≤ p23Gamma u (m + 1) := by
  have htwo : 2 ≤ m + 1 := by omega
  have hv2 : P23GammaValid u 2 := by
    unfold P23GammaValid at hv ⊢
    norm_num at hv ⊢
    have hc : (2 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast htwo
    have hv' : (((m + 1 : ℕ) : ℝ) * u) < 1 := by
      simpa [Nat.cast_add, Nat.cast_one] using hv
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc hu) hv'
  have hv1 : P23GammaValid u 1 := by
    unfold P23GammaValid at hv2 ⊢
    norm_num at hv2 ⊢
    nlinarith
  have h1 := p23_gamma_step_coeff hu hv1
  have h2 := p23_gamma_step_coeff hu hv2
  have hmono := p23_gamma_mono hu htwo hv
  have hg0 : p23Gamma u 0 = 0 := by simp [p23Gamma]
  rw [hg0] at h1
  norm_num at h1 h2
  have hmul := mul_le_mul_of_nonneg_right h1 (show 0 ≤ 1 + u by linarith)
  nlinarith

private lemma p23_round_extend {u r s z dm da S : ℝ} {m : ℕ}
    (hu : 0 ≤ u) (hm : 1 ≤ m) (hv : P23GammaValid u (m + 1))
    (hS : 0 ≤ S) (hs : |s| ≤ S)
    (herr : |r - s| ≤ p23Gamma u m * S)
    (hdm : |dm| ≤ u) (hda : |da| ≤ u) :
    |(r + z * (1 + dm)) * (1 + da) - (s + z)| ≤
      p23Gamma u (m + 1) * (S + |z|) := by
  have hvm : P23GammaValid u m := by
    unfold P23GammaValid at hv ⊢
    have hc : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ m
    have hv' : (((m + 1 : ℕ) : ℝ) * u) < 1 := hv
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc hu) hv'
  have hg : 0 ≤ p23Gamma u m := p23_gamma_nonneg hu hvm
  have hga : 0 ≤ p23Gamma u (m + 1) := p23_gamma_nonneg hu hv
  have hone : |1 + da| ≤ 1 + u := by
    calc
      |1 + da| ≤ |(1 : ℝ)| + |da| := abs_add_le _ _
      _ ≤ 1 + u := by norm_num; linarith
  have holdterm :
      |(r - s) * (1 + da)| ≤ p23Gamma u m * S * (1 + u) := by
    rw [abs_mul]
    exact mul_le_mul herr hone (abs_nonneg _) (mul_nonneg hg hS)
  have hsterm : |s * da| ≤ S * u := by
    rw [abs_mul]
    exact mul_le_mul hs hda (abs_nonneg _) hS
  have hprod : |dm| * |da| ≤ u * u :=
    mul_le_mul hdm hda (abs_nonneg _) hu
  have hcoef : |(1 + dm) * (1 + da) - 1| ≤ 2 * u + u ^ 2 := by
    calc
      |(1 + dm) * (1 + da) - 1| = |dm + da + dm * da| := by
        congr 1
        ring
      _ ≤ |dm| + |da| + |dm * da| := by
        calc
          |dm + da + dm * da| ≤ |dm + da| + |dm * da| := abs_add_le _ _
          _ ≤ (|dm| + |da|) + |dm * da| := by
            gcongr
            exact abs_add_le _ _
      _ ≤ 2 * u + u ^ 2 := by
        rw [abs_mul]
        nlinarith
  have hnewcoeff : |(1 + dm) * (1 + da) - 1| ≤ p23Gamma u (m + 1) :=
    hcoef.trans (p23_two_rounds_coeff hu hm hv)
  have hnewterm :
      |z * ((1 + dm) * (1 + da) - 1)| ≤
        |z| * p23Gamma u (m + 1) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hnewcoeff (abs_nonneg z)
  have hstep := p23_gamma_step_coeff hu hv
  have hold :
      |(r - s) * (1 + da)| + |s * da| ≤
        p23Gamma u (m + 1) * S := by
    calc
      |(r - s) * (1 + da)| + |s * da| ≤
          p23Gamma u m * S * (1 + u) + S * u := add_le_add holdterm hsterm
      _ = (p23Gamma u m * (1 + u) + u) * S := by ring
      _ ≤ p23Gamma u (m + 1) * S :=
        mul_le_mul_of_nonneg_right hstep hS
  calc
    |(r + z * (1 + dm)) * (1 + da) - (s + z)| =
        |(r - s) * (1 + da) + s * da +
          z * ((1 + dm) * (1 + da) - 1)| := by
            congr 1
            ring
    _ ≤ |(r - s) * (1 + da)| + |s * da| +
          |z * ((1 + dm) * (1 + da) - 1)| := by
            calc
              _ ≤ |(r - s) * (1 + da) + s * da| +
                    |z * ((1 + dm) * (1 + da) - 1)| := abs_add_le _ _
              _ ≤ (|(r - s) * (1 + da)| + |s * da|) +
                    |z * ((1 + dm) * (1 + da) - 1)| := by
                      gcongr
                      exact abs_add_le _ _
    _ ≤ p23Gamma u (m + 1) * S +
          |z| * p23Gamma u (m + 1) := add_le_add hold hnewterm
    _ = p23Gamma u (m + 1) * (S + |z|) := by ring

private lemma p23_roundedDot_succ (fp : P23FPModel) (n : ℕ)
    (x y : Fin (n + 1) → ℝ) :
    p23RoundedDotProduct fp (n + 1) x y =
      fp.fl_add
        (p23RoundedDotProduct fp n
          (fun i => x i.castSucc) (fun i => y i.castSucc))
        (fp.fl_mul (x (Fin.last n)) (y (Fin.last n))) := by
  cases n <;>
    simp [p23RoundedDotProduct, Fin.foldl_succ_last, fp.fl_add_zero]

private lemma p23_roundedDot_bound (fp : P23FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hv : P23GammaValid fp.u n) :
    |p23RoundedDotProduct fp n x y - ∑ i : Fin n, x i * y i| ≤
      p23Gamma fp.u n * ∑ i : Fin n, |x i| * |y i| := by
  induction n with
  | zero =>
      simp [p23RoundedDotProduct, p23Gamma]
  | succ n ih =>
      cases n with
      | zero =>
          obtain ⟨dm, hdm, hmul⟩ := fp.model_mul (x 0) (y 0)
          have hstep := p23_gamma_step_coeff fp.u_nonneg hv
          have hg0 : p23Gamma fp.u 0 = 0 := by simp [p23Gamma]
          rw [hg0] at hstep
          norm_num at hstep
          rw [show p23RoundedDotProduct fp 1 x y = fp.fl_mul (x 0) (y 0) by
            simp [p23RoundedDotProduct], hmul]
          rw [Fin.sum_univ_one, Fin.sum_univ_one]
          calc
            |x 0 * y 0 * (1 + dm) - x 0 * y 0| =
                |x 0 * y 0| * |dm| := by
                  rw [← abs_mul]
                  congr 1
                  ring
            _ ≤ |x 0 * y 0| * fp.u :=
              mul_le_mul_of_nonneg_left hdm (abs_nonneg _)
            _ ≤ |x 0 * y 0| * p23Gamma fp.u 1 :=
              mul_le_mul_of_nonneg_left hstep (abs_nonneg _)
            _ = p23Gamma fp.u 1 * (|x 0| * |y 0|) := by
              rw [abs_mul]
              ring
      | succ m =>
          let xp : Fin (m + 1) → ℝ := fun i => x i.castSucc
          let yp : Fin (m + 1) → ℝ := fun i => y i.castSucc
          let s : ℝ := ∑ i : Fin (m + 1), xp i * yp i
          let S : ℝ := ∑ i : Fin (m + 1), |xp i| * |yp i|
          let z : ℝ := x (Fin.last (m + 1)) * y (Fin.last (m + 1))
          let r : ℝ := p23RoundedDotProduct fp (m + 1) xp yp
          have hvp : P23GammaValid fp.u (m + 1) := by
            unfold P23GammaValid at hv ⊢
            have hc : ((m + 1 : ℕ) : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by
              exact_mod_cast Nat.le_succ (m + 1)
            have hv' : ((m + 2 : ℕ) : ℝ) * fp.u < 1 := by
              convert hv using 1 <;> push_cast <;> ring
            exact lt_of_le_of_lt
              (mul_le_mul_of_nonneg_right hc fp.u_nonneg) hv'
          have herr : |r - s| ≤ p23Gamma fp.u (m + 1) * S := by
            exact ih xp yp hvp
          have hS : 0 ≤ S := by
            exact Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
          have hs : |s| ≤ S := by
            dsimp [s, S, xp, yp]
            calc
              |∑ i : Fin (m + 1), x i.castSucc * y i.castSucc| ≤
                  ∑ i : Fin (m + 1), |x i.castSucc * y i.castSucc| :=
                    Finset.abs_sum_le_sum_abs _ _
              _ = ∑ i : Fin (m + 1), |x i.castSucc| * |y i.castSucc| := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    exact abs_mul _ _
          obtain ⟨dm, hdm, hmul⟩ :=
            fp.model_mul (x (Fin.last (m + 1))) (y (Fin.last (m + 1)))
          obtain ⟨da, hda, hadd⟩ :=
            fp.model_add r (fp.fl_mul
              (x (Fin.last (m + 1))) (y (Fin.last (m + 1))))
          have hext := p23_round_extend (z := z) fp.u_nonneg
            (show 1 ≤ m + 1 by omega) hv hS hs herr hdm hda
          have hsum : (∑ i : Fin (m + 2), x i * y i) = s + z := by
            rw [Fin.sum_univ_castSucc]
          have hsumabs :
              (∑ i : Fin (m + 2), |x i| * |y i|) = S + |z| := by
            rw [Fin.sum_univ_castSucc]
            simp only [S, z, xp, yp, abs_mul]
          rw [p23_roundedDot_succ, hadd, hmul]
          rw [hsum, hsumabs]
          change |(r + z * (1 + dm)) * (1 + da) - (s + z)| ≤ _
          simpa using hext

private lemma p23_one_add_gamma {u : ℝ} {a : ℕ}
    (hv : P23GammaValid u a) :
    1 + p23Gamma u a = 1 / (1 - (a : ℝ) * u) := by
  have ha : (a : ℝ) * u < 1 := hv
  have hn : 1 - (a : ℝ) * u ≠ 0 := ne_of_gt (sub_pos.mpr ha)
  unfold p23Gamma
  calc
    1 + (a : ℝ) * u / (1 - (a : ℝ) * u) =
        (1 - (a : ℝ) * u) / (1 - (a : ℝ) * u) +
          (a : ℝ) * u / (1 - (a : ℝ) * u) := by rw [div_self hn]
    _ = ((1 - (a : ℝ) * u) + (a : ℝ) * u) /
          (1 - (a : ℝ) * u) := by rw [add_div]
    _ = 1 / (1 - (a : ℝ) * u) := by ring

private lemma p23_gamma_combine {u : ℝ} {a b : ℕ} (hu : 0 ≤ u)
    (hv : P23GammaValid u (a + b)) :
    p23Gamma u a + p23Gamma u b + p23Gamma u a * p23Gamma u b ≤
      p23Gamma u (a + b) := by
  have hv' : (((a + b : ℕ) : ℝ) * u) < 1 := hv
  have ha : (a : ℝ) * u < 1 := by
    have hc : (a : ℝ) ≤ ((a + b : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_right a b
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc hu) hv'
  have hb : (b : ℝ) * u < 1 := by
    have hc : (b : ℝ) ≤ ((a + b : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left b a
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc hu) hv'
  have hva : P23GammaValid u a := ha
  have hvb : P23GammaValid u b := hb
  have hga := p23_one_add_gamma hva
  have hgb := p23_one_add_gamma hvb
  have hgab : 1 + p23Gamma u (a + b) =
      1 / (1 - ((a + b : ℕ) : ℝ) * u) := p23_one_add_gamma hv
  have hden :
      1 - ((a + b : ℕ) : ℝ) * u ≤
        (1 - (a : ℝ) * u) * (1 - (b : ℝ) * u) := by
    push_cast
    have hn : 0 ≤ (a : ℝ) * (b : ℝ) * u ^ 2 := by positivity
    nlinarith
  have hrecip :
      1 / ((1 - (a : ℝ) * u) * (1 - (b : ℝ) * u)) ≤
        1 / (1 - ((a + b : ℕ) : ℝ) * u) := by
    exact one_div_le_one_div_of_le (sub_pos.mpr hv') hden
  calc
    p23Gamma u a + p23Gamma u b + p23Gamma u a * p23Gamma u b =
        (1 + p23Gamma u a) * (1 + p23Gamma u b) - 1 := by ring
    _ = 1 / ((1 - (a : ℝ) * u) * (1 - (b : ℝ) * u)) - 1 := by
      rw [hga, hgb]
      field_simp [ne_of_gt (sub_pos.mpr ha), ne_of_gt (sub_pos.mpr hb)]
    _ ≤ 1 / (1 - ((a + b : ℕ) : ℝ) * u) - 1 :=
      sub_le_sub_right hrecip 1
    _ = p23Gamma u (a + b) := by linarith

private lemma p23_roundedMatMul_bound (fp : P23FPModel) (n : ℕ)
    (A B : P23Matrix n) (hv : P23GammaValid fp.u n) (i j : Fin n) :
    |p23RoundedMatMul fp A B i j - p23MatMul A B i j| ≤
      p23Gamma fp.u n * p23MatMul (p23AbsMatrix A) (p23AbsMatrix B) i j := by
  simpa [p23RoundedMatMul, p23MatMul, p23AbsMatrix] using
    p23_roundedDot_bound fp n (A i) (fun q => B q j) hv

private lemma p23_power_abs_nonneg {n : ℕ} (X : P23Matrix n) :
    ∀ k i j, 0 ≤ p23PowerSteps (p23AbsMatrix X) k i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      exact abs_nonneg _
  | succ k ih =>
      intro i j
      simp only [p23PowerSteps, p23MatMul, p23AbsMatrix]
      exact Finset.sum_nonneg fun q _ =>
        mul_nonneg (ih i q) (abs_nonneg (X q j))

private lemma p23_power_abs_bound {n : ℕ} (X : P23Matrix n) :
    ∀ k i j, |p23PowerSteps X k i j| ≤
      p23PowerSteps (p23AbsMatrix X) k i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      exact le_rfl
  | succ k ih =>
      intro i j
      simp only [p23PowerSteps, p23MatMul]
      calc
        |∑ q : Fin n, p23PowerSteps X k i q * X q j| ≤
            ∑ q : Fin n, |p23PowerSteps X k i q * X q j| :=
              Finset.abs_sum_le_sum_abs _ _
        _ = ∑ q : Fin n, |p23PowerSteps X k i q| * |X q j| := by
              apply Finset.sum_congr rfl
              intro q hq
              exact abs_mul _ _
        _ ≤ ∑ q : Fin n,
              p23PowerSteps (p23AbsMatrix X) k i q * |X q j| := by
              apply Finset.sum_le_sum
              intro q hq
              exact mul_le_mul_of_nonneg_right (ih i q) (abs_nonneg _)

/-- P23-T1: Lemma 2.2, reindexed so `k` counts the rounded matrix
multiplications after the supplied matrix `X`. -/
theorem p23_t1_lemma_2_2
    (fp : P23FPModel) (n k : ℕ) (X : P23Matrix n)
    (hvalid : P23GammaValid fp.u (k * n)) :
    ∀ i j,
      |p23RoundedPowerSteps fp X k i j - p23PowerSteps X k i j| ≤
        p23Gamma fp.u (k * n) * p23PowerSteps (p23AbsMatrix X) k i j := by
  -- PROOF_START P23-T1-H001
  induction k with
  | zero =>
      intro i j
      simp [p23RoundedPowerSteps, p23PowerSteps, p23Gamma]
  | succ k ih =>
      intro i j
      have hsplit : (k + 1) * n = k * n + n := by
        simp [Nat.add_mul]
      have hvsum : P23GammaValid fp.u (k * n + n) := by
        simpa [hsplit] using hvalid
      have hvprev : P23GammaValid fp.u (k * n) :=
        p23_valid_of_le fp.u_nonneg (Nat.le_add_right (k * n) n) hvsum
      have hvn : P23GammaValid fp.u n :=
        p23_valid_of_le fp.u_nonneg (Nat.le_add_left n (k * n)) hvsum
      have ih' := ih hvprev
      let H : P23Matrix n := p23RoundedPowerSteps fp X k
      let P : P23Matrix n := p23PowerSteps X k
      let A : P23Matrix n := p23PowerSteps (p23AbsMatrix X) k
      let G : ℝ := p23Gamma fp.u (k * n)
      let T : ℝ := p23MatMul A (p23AbsMatrix X) i j
      have hG : 0 ≤ G := p23_gamma_nonneg fp.u_nonneg hvprev
      have hGn : 0 ≤ p23Gamma fp.u n := p23_gamma_nonneg fp.u_nonneg hvn
      have hT : 0 ≤ T := by
        exact Finset.sum_nonneg fun q _ =>
          mul_nonneg (p23_power_abs_nonneg X k i q) (abs_nonneg (X q j))
      have hHabs (q : Fin n) : |H i q| ≤ (1 + G) * A i q := by
        calc
          |H i q| = |(H i q - P i q) + P i q| := by
            congr 1
            ring
          _ ≤ |H i q - P i q| + |P i q| := abs_add_le _ _
          _ ≤ G * A i q + A i q := by
            exact add_le_add (ih' i q) (p23_power_abs_bound X k i q)
          _ = (1 + G) * A i q := by ring
      have hmulabs :
          p23MatMul (p23AbsMatrix H) (p23AbsMatrix X) i j ≤
            (1 + G) * T := by
        dsimp [p23MatMul, p23AbsMatrix, T]
        calc
          ∑ q : Fin n, |H i q| * |X q j| ≤
              ∑ q : Fin n, ((1 + G) * A i q) * |X q j| := by
                apply Finset.sum_le_sum
                intro q hq
                exact mul_le_mul_of_nonneg_right (hHabs q) (abs_nonneg _)
          _ = (1 + G) * ∑ q : Fin n, A i q * |X q j| := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro q hq
                ring
      have hround :
          |p23RoundedMatMul fp H X i j - p23MatMul H X i j| ≤
            p23Gamma fp.u n * ((1 + G) * T) := by
        exact (p23_roundedMatMul_bound fp n H X hvn i j).trans
          (mul_le_mul_of_nonneg_left hmulabs hGn)
      have hprop :
          |p23MatMul H X i j - p23MatMul P X i j| ≤ G * T := by
        have heq :
            p23MatMul H X i j - p23MatMul P X i j =
              ∑ q : Fin n, (H i q - P i q) * X q j := by
          dsimp [p23MatMul]
          calc
            (∑ q : Fin n, H i q * X q j) - (∑ q : Fin n, P i q * X q j) =
                ∑ q : Fin n, (H i q * X q j - P i q * X q j) :=
                  by rw [Finset.sum_sub_distrib]
            _ = ∑ q : Fin n, (H i q - P i q) * X q j := by
                  apply Finset.sum_congr rfl
                  intro q hq
                  ring
        rw [heq]
        calc
          |∑ q : Fin n, (H i q - P i q) * X q j| ≤
              ∑ q : Fin n, |(H i q - P i q) * X q j| :=
                Finset.abs_sum_le_sum_abs _ _
          _ = ∑ q : Fin n, |H i q - P i q| * |X q j| := by
                apply Finset.sum_congr rfl
                intro q hq
                exact abs_mul _ _
          _ ≤ ∑ q : Fin n, (G * A i q) * |X q j| := by
                apply Finset.sum_le_sum
                intro q hq
                exact mul_le_mul_of_nonneg_right (ih' i q) (abs_nonneg _)
          _ = G * T := by
                dsimp [T, p23MatMul, p23AbsMatrix]
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro q hq
                ring
      have hcombine :
          p23Gamma fp.u n * (1 + G) + G ≤
            p23Gamma fp.u (k * n + n) := by
        have hc := p23_gamma_combine fp.u_nonneg hvsum
        dsimp [G]
        nlinarith
      simp only [p23RoundedPowerSteps, p23PowerSteps]
      change |p23RoundedMatMul fp H X i j - p23MatMul P X i j| ≤
        p23Gamma fp.u ((k + 1) * n) * T
      calc
        |p23RoundedMatMul fp H X i j - p23MatMul P X i j| =
            |(p23RoundedMatMul fp H X i j - p23MatMul H X i j) +
              (p23MatMul H X i j - p23MatMul P X i j)| := by
                congr 1
                ring
        _ ≤ |p23RoundedMatMul fp H X i j - p23MatMul H X i j| +
              |p23MatMul H X i j - p23MatMul P X i j| := abs_add_le _ _
        _ ≤ p23Gamma fp.u n * ((1 + G) * T) + G * T :=
              add_le_add hround hprop
        _ = (p23Gamma fp.u n * (1 + G) + G) * T := by ring
        _ ≤ p23Gamma fp.u (k * n + n) * T :=
              mul_le_mul_of_nonneg_right hcombine hT
        _ = p23Gamma fp.u ((k + 1) * n) * T := by rw [hsplit]

end HighamBench
