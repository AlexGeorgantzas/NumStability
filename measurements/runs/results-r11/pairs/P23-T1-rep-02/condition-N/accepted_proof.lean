import HighamBench.P23Definitions
import Mathlib

namespace HighamBench

private lemma gamma_core_add (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x + y < 1) :
    x / (1 - x) + y / (1 - y) +
        (x / (1 - x)) * (y / (1 - y)) ≤
      (x + y) / (1 - (x + y)) := by
  have hx1 : 0 < 1 - x := by linarith
  have hy1 : 0 < 1 - y := by linarith
  have hxy1 : 0 < 1 - (x + y) := by linarith
  apply (le_div_iff₀ hxy1).2
  field_simp
  nlinarith [mul_nonneg hx hy]

private lemma p23_gamma_nonneg (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hvalid : P23GammaValid u m) : 0 ≤ p23Gamma u m := by
  have hn : 0 ≤ (m : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hd : 0 < 1 - (m : ℝ) * u := by
    simpa [P23GammaValid] using sub_pos.mpr hvalid
  exact div_nonneg hn hd.le

private lemma p23_gamma_add (u : ℝ) (a b : ℕ) (hu : 0 ≤ u)
    (hvalid : P23GammaValid u (a + b)) :
    p23Gamma u a + p23Gamma u b + p23Gamma u a * p23Gamma u b ≤
      p23Gamma u (a + b) := by
  have hx : 0 ≤ (a : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hy : 0 ≤ (b : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hxy : (a : ℝ) * u + (b : ℝ) * u < 1 := by
    simpa [P23GammaValid, Nat.cast_add, add_mul] using hvalid
  simpa [p23Gamma, Nat.cast_add, add_mul] using
    gamma_core_add ((a : ℝ) * u) ((b : ℝ) * u) hx hy hxy

private lemma p23_u_le_gamma (u : ℝ) (m : ℕ) (hu : 0 ≤ u) (hm : 1 ≤ m)
    (hvalid : P23GammaValid u m) : u ≤ p23Gamma u m := by
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hd : 0 < 1 - (m : ℝ) * u := by
    simpa [P23GammaValid] using sub_pos.mpr hvalid
  rw [p23Gamma]
  apply (le_div_iff₀ hd).2
  have h₁ : 0 ≤ ((m : ℝ) - 1) * u := mul_nonneg (sub_nonneg.mpr hm') hu
  have h₂ : 0 ≤ (m : ℝ) * (u * u) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_self_nonneg _)
  nlinarith

private lemma p23_mul_error (fp : P23FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * |x * y| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul x y
  rw [hfl]
  have heq : (x * y) * (1 + δ) - x * y = (x * y) * δ := by ring
  rw [heq, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (x * y))

private lemma p23_add_error (fp : P23FPModel) (x y : ℝ) :
    |fp.fl_add x y - (x + y)| ≤ fp.u * |x + y| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add x y
  rw [hfl]
  have heq : (x + y) * (1 + δ) - (x + y) = (x + y) * δ := by ring
  rw [heq, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (x + y))

private lemma p23_accumulate_one (fp : P23FPModel) (q : ℕ)
    (r s T x y : ℝ) (hq : 1 ≤ q)
    (hvalid : P23GammaValid fp.u (q + 1))
    (hT : 0 ≤ T) (hs : |s| ≤ T)
    (hr : |r - s| ≤ p23Gamma fp.u q * T) :
    |fp.fl_add r (fp.fl_mul x y) - (s + x * y)| ≤
      p23Gamma fp.u (q + 1) * (T + |x * y|) := by
  have hvq : P23GammaValid fp.u q := by
    rw [P23GammaValid] at hvalid ⊢
    have huq : (q : ℝ) * fp.u ≤ ((q + 1 : ℕ) : ℝ) * fp.u := by
      apply mul_le_mul_of_nonneg_right _ fp.u_nonneg
      norm_num
    exact lt_of_le_of_lt huq hvalid
  have hv1 : P23GammaValid fp.u 1 := by
    rw [P23GammaValid] at hvalid ⊢
    have hu1 : (1 : ℝ) * fp.u ≤ ((q + 1 : ℕ) : ℝ) * fp.u := by
      apply mul_le_mul_of_nonneg_right _ fp.u_nonneg
      norm_num
    exact lt_of_le_of_lt (by simpa using hu1) hvalid
  let gq := p23Gamma fp.u q
  let g1 := p23Gamma fp.u 1
  let gn := p23Gamma fp.u (q + 1)
  have hgq : 0 ≤ gq := p23_gamma_nonneg fp.u q fp.u_nonneg hvq
  have hg1 : 0 ≤ g1 := p23_gamma_nonneg fp.u 1 fp.u_nonneg hv1
  have hug1 : fp.u ≤ g1 := p23_u_le_gamma fp.u 1 fp.u_nonneg (by omega) hv1
  have hugq : fp.u ≤ gq := p23_u_le_gamma fp.u q fp.u_nonneg hq hvq
  have hcomp : gq + g1 + gq * g1 ≤ gn := by
    simpa [gq, g1, gn] using p23_gamma_add fp.u q 1 fp.u_nonneg hvalid
  have hugu : fp.u * gq ≤ g1 * gq :=
    mul_le_mul_of_nonneg_right hug1 hgq
  have hcoefT : fp.u * (1 + gq) + gq ≤ gn := by
    nlinarith [hcomp, hugu]
  have huug : fp.u * fp.u ≤ fp.u * gq :=
    mul_le_mul_of_nonneg_left hugq fp.u_nonneg
  have hcoefA : fp.u * (1 + fp.u) + fp.u ≤ gn := by
    nlinarith [hcoefT, huug, hugq]
  have hmul := p23_mul_error fp x y
  have hadd := p23_add_error fp r (fp.fl_mul x y)
  have htriangle :
      |r + fp.fl_mul x y| ≤
        |s| + |r - s| + |x * y| + |fp.fl_mul x y - x * y| := by
    calc
      |r + fp.fl_mul x y| =
          |(s + (r - s)) + (x * y + (fp.fl_mul x y - x * y))| := by
            congr 1 <;> ring
      _ ≤ |s + (r - s)| + |x * y + (fp.fl_mul x y - x * y)| :=
        abs_add_le _ _
      _ ≤ (|s| + |r - s|) + (|x * y| + |fp.fl_mul x y - x * y|) :=
        add_le_add (abs_add_le _ _) (abs_add_le _ _)
      _ = |s| + |r - s| + |x * y| + |fp.fl_mul x y - x * y| := by ring
  have hmag :
      |r + fp.fl_mul x y| ≤
        T + gq * T + |x * y| + fp.u * |x * y| := by
    dsimp [gq] at hr ⊢
    linarith
  have hadd' :
      |fp.fl_add r (fp.fl_mul x y) - (r + fp.fl_mul x y)| ≤
        fp.u * (T + gq * T + |x * y| + fp.u * |x * y|) :=
    le_trans hadd (mul_le_mul_of_nonneg_left hmag fp.u_nonneg)
  have hdiff :
      |(r + fp.fl_mul x y) - (s + x * y)| ≤
        gq * T + fp.u * |x * y| := by
    calc
      |(r + fp.fl_mul x y) - (s + x * y)| =
          |(r - s) + (fp.fl_mul x y - x * y)| := by ring_nf
      _ ≤ |r - s| + |fp.fl_mul x y - x * y| := abs_add_le _ _
      _ ≤ gq * T + fp.u * |x * y| := add_le_add (by simpa [gq] using hr) hmul
  have hall :
      |fp.fl_add r (fp.fl_mul x y) - (s + x * y)| ≤
        (fp.u * (1 + gq) + gq) * T +
          (fp.u * (1 + fp.u) + fp.u) * |x * y| := by
    calc
      |fp.fl_add r (fp.fl_mul x y) - (s + x * y)| ≤
          |fp.fl_add r (fp.fl_mul x y) - (r + fp.fl_mul x y)| +
            |(r + fp.fl_mul x y) - (s + x * y)| := by
              have heq :
                  fp.fl_add r (fp.fl_mul x y) - (s + x * y) =
                    (fp.fl_add r (fp.fl_mul x y) - (r + fp.fl_mul x y)) +
                      ((r + fp.fl_mul x y) - (s + x * y)) := by ring
              rw [heq]
              exact abs_add_le _ _
      _ ≤ fp.u * (T + gq * T + |x * y| + fp.u * |x * y|) +
            (gq * T + fp.u * |x * y|) := add_le_add hadd' hdiff
      _ = (fp.u * (1 + gq) + gq) * T +
          (fp.u * (1 + fp.u) + fp.u) * |x * y| := by ring
  have hTA := mul_le_mul_of_nonneg_right hcoefT hT
  have hAA := mul_le_mul_of_nonneg_right hcoefA (abs_nonneg (x * y))
  calc
    |fp.fl_add r (fp.fl_mul x y) - (s + x * y)| ≤
        (fp.u * (1 + gq) + gq) * T +
          (fp.u * (1 + fp.u) + fp.u) * |x * y| := hall
    _ ≤ p23Gamma fp.u (q + 1) * T +
          p23Gamma fp.u (q + 1) * |x * y| := add_le_add hTA hAA
    _ = p23Gamma fp.u (q + 1) * (T + |x * y|) := by ring

private lemma p23_fold_bound (fp : P23FPModel) :
    ∀ (m q : ℕ) (x y : Fin m → ℝ) (r s T : ℝ),
      1 ≤ q →
      P23GammaValid fp.u (q + m) →
      0 ≤ T → |s| ≤ T →
      |r - s| ≤ p23Gamma fp.u q * T →
      |Fin.foldl m
          (fun acc i => fp.fl_add acc (fp.fl_mul (x i) (y i))) r -
          (s + ∑ i, x i * y i)| ≤
        p23Gamma fp.u (q + m) * (T + ∑ i, |x i * y i|) := by
  intro m
  induction m with
  | zero =>
      intro q x y r s T hq hvalid hT hs hr
      simpa using hr
  | succ m ih =>
      intro q x y r s T hq hvalid hT hs hr
      let xp : Fin m → ℝ := fun i => x i.castSucc
      let yp : Fin m → ℝ := fun i => y i.castSucc
      let rp := Fin.foldl m
        (fun acc i => fp.fl_add acc (fp.fl_mul (xp i) (yp i))) r
      let sp := s + ∑ i, xp i * yp i
      let Tp := T + ∑ i, |xp i * yp i|
      have hvp : P23GammaValid fp.u (q + m) := by
        rw [P23GammaValid] at hvalid ⊢
        have hle : ((q + m : ℕ) : ℝ) * fp.u ≤
            ((q + (m + 1) : ℕ) : ℝ) * fp.u := by
          apply mul_le_mul_of_nonneg_right _ fp.u_nonneg
          norm_num
        exact lt_of_le_of_lt hle hvalid
      have ihr : |rp - sp| ≤ p23Gamma fp.u (q + m) * Tp := by
        dsimp [rp, sp, Tp, xp, yp]
        exact ih q (fun i => x i.castSucc) (fun i => y i.castSucc)
          r s T hq hvp hT hs hr
      have hTp : 0 ≤ Tp := by
        dsimp [Tp]
        positivity
      have hsp : |sp| ≤ Tp := by
        dsimp [sp, Tp]
        calc
          |s + ∑ i, xp i * yp i| ≤ |s| + |∑ i, xp i * yp i| := abs_add_le _ _
          _ ≤ T + ∑ i, |xp i * yp i| :=
            add_le_add hs (Finset.abs_sum_le_sum_abs _ _)
      have hstep := p23_accumulate_one fp (q + m) rp sp Tp
        (x (Fin.last m)) (y (Fin.last m)) (by omega)
        (by simpa [Nat.add_assoc] using hvalid) hTp hsp ihr
      rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      dsimp [rp, sp, Tp, xp, yp] at hstep ⊢
      simpa [Nat.add_assoc, add_assoc] using hstep

private lemma p23_rounded_dot_bound (fp : P23FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hvalid : P23GammaValid fp.u n) :
    |p23RoundedDotProduct fp n x y - ∑ i, x i * y i| ≤
      p23Gamma fp.u n * ∑ i, |x i * y i| := by
  cases n with
  | zero => simp [p23RoundedDotProduct, p23Gamma]
  | succ m =>
      have hv1 : P23GammaValid fp.u 1 := by
        rw [P23GammaValid] at hvalid ⊢
        have hle : (1 : ℝ) * fp.u ≤ ((m + 1 : ℕ) : ℝ) * fp.u := by
          apply mul_le_mul_of_nonneg_right _ fp.u_nonneg
          norm_num
        exact lt_of_le_of_lt (by simpa using hle) hvalid
      have hug : fp.u ≤ p23Gamma fp.u 1 :=
        p23_u_le_gamma fp.u 1 fp.u_nonneg (by omega) hv1
      have hmul := p23_mul_error fp (x 0) (y 0)
      have hinit :
          |fp.fl_mul (x 0) (y 0) - x 0 * y 0| ≤
            p23Gamma fp.u 1 * |x 0 * y 0| := by
        exact le_trans hmul
          (mul_le_mul_of_nonneg_right hug (abs_nonneg (x 0 * y 0)))
      have hfold := p23_fold_bound fp m 1
        (fun i => x i.succ) (fun i => y i.succ)
        (fp.fl_mul (x 0) (y 0)) (x 0 * y 0) |x 0 * y 0|
        (by omega) (by simpa [Nat.add_comm] using hvalid)
        (abs_nonneg _) (le_rfl) hinit
      simpa [p23RoundedDotProduct, Fin.sum_univ_succ, Nat.add_comm,
        add_assoc] using hfold

private lemma p23_rounded_mat_mul_bound (fp : P23FPModel) (n : ℕ)
    (A B : P23Matrix n) (hvalid : P23GammaValid fp.u n) (i j : Fin n) :
    |p23RoundedMatMul fp A B i j - p23MatMul A B i j| ≤
      p23Gamma fp.u n * p23MatMul (p23AbsMatrix A) (p23AbsMatrix B) i j := by
  have h := p23_rounded_dot_bound fp n (A i) (fun t => B t j) hvalid
  simpa [p23RoundedMatMul, p23MatMul, p23AbsMatrix, abs_mul] using h

private lemma p23_abs_power_nonneg (n : ℕ) (X : P23Matrix n) :
    ∀ (k : ℕ) (i j : Fin n),
      0 ≤ p23PowerSteps (p23AbsMatrix X) k i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      exact abs_nonneg _
  | succ k ih =>
      intro i j
      rw [p23PowerSteps]
      apply Finset.sum_nonneg
      intro t ht
      exact mul_nonneg (ih i t) (abs_nonneg _)

private lemma p23_power_abs_le (n : ℕ) (X : P23Matrix n) :
    ∀ (k : ℕ) (i j : Fin n),
      |p23PowerSteps X k i j| ≤
        p23PowerSteps (p23AbsMatrix X) k i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      exact le_rfl
  | succ k ih =>
      intro i j
      rw [p23PowerSteps, p23PowerSteps, p23MatMul, p23MatMul]
      calc
        |∑ t, p23PowerSteps X k i t * X t j| ≤
            ∑ t, |p23PowerSteps X k i t * X t j| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ t, p23PowerSteps (p23AbsMatrix X) k i t * |X t j| := by
          apply Finset.sum_le_sum
          intro t ht
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (ih i t) (abs_nonneg _)
        _ = ∑ t, p23PowerSteps (p23AbsMatrix X) k i t *
              p23AbsMatrix X t j := by
          rfl

/-- P23-T1: Lemma 2.2, reindexed so `k` counts the rounded matrix
multiplications after the supplied matrix `X`. -/
theorem p23_t1_lemma_2_2
    (fp : P23FPModel) (n k : ℕ) (X : P23Matrix n)
    (hvalid : P23GammaValid fp.u (k * n)) :
    ∀ i j,
      |p23RoundedPowerSteps fp X k i j - p23PowerSteps X k i j| ≤
        p23Gamma fp.u (k * n) * p23PowerSteps (p23AbsMatrix X) k i j := by
  -- PROOF_START P23-T1-H001
  revert hvalid
  induction k with
  | zero =>
      intro hvalid i j
      simp [p23RoundedPowerSteps, p23PowerSteps, p23Gamma]
  | succ k ih =>
      intro hvalid i j
      have hvn : P23GammaValid fp.u n := by
        rw [P23GammaValid] at hvalid ⊢
        have hn : n ≤ (k + 1) * n := by
          simpa using Nat.mul_le_mul_right n (Nat.succ_le_succ (Nat.zero_le k))
        have hn' : (n : ℝ) ≤ (((k + 1) * n : ℕ) : ℝ) := by exact_mod_cast hn
        exact lt_of_le_of_lt
          (mul_le_mul_of_nonneg_right hn' fp.u_nonneg) hvalid
      have hvk : P23GammaValid fp.u (k * n) := by
        rw [P23GammaValid] at hvalid ⊢
        have hn : k * n ≤ (k + 1) * n :=
          Nat.mul_le_mul_right n (Nat.le_succ k)
        have hn' : ((k * n : ℕ) : ℝ) ≤ (((k + 1) * n : ℕ) : ℝ) := by
          exact_mod_cast hn
        exact lt_of_le_of_lt
          (mul_le_mul_of_nonneg_right hn' fp.u_nonneg) hvalid
      let R := p23RoundedPowerSteps fp X k
      let P := p23PowerSteps X k
      let Q := p23PowerSteps (p23AbsMatrix X) k
      let gk := p23Gamma fp.u (k * n)
      let gn := p23Gamma fp.u n
      have hgk : 0 ≤ gk := p23_gamma_nonneg fp.u (k * n) fp.u_nonneg hvk
      have hgn : 0 ≤ gn := p23_gamma_nonneg fp.u n fp.u_nonneg hvn
      have hR (t : Fin n) : |R i t| ≤ (1 + gk) * Q i t := by
        calc
          |R i t| = |(R i t - P i t) + P i t| := by ring_nf
          _ ≤ |R i t - P i t| + |P i t| := abs_add_le _ _
          _ ≤ gk * Q i t + Q i t := by
            apply add_le_add
            · simpa [R, P, Q, gk] using ih hvk i t
            · simpa [P, Q] using p23_power_abs_le n X k i t
          _ = (1 + gk) * Q i t := by ring
      have hsumR :
          p23MatMul (p23AbsMatrix R) (p23AbsMatrix X) i j ≤
            (1 + gk) * p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by
        rw [p23MatMul]
        calc
          ∑ t, p23AbsMatrix R i t * p23AbsMatrix X t j ≤
              ∑ t, ((1 + gk) * Q i t) * |X t j| := by
            apply Finset.sum_le_sum
            intro t ht
            exact mul_le_mul_of_nonneg_right (by simpa [p23AbsMatrix] using hR t)
              (abs_nonneg _)
          _ = (1 + gk) * ∑ t, Q i t * |X t j| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro t ht
            ring
          _ = (1 + gk) * p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by
            rfl
      have hround0 := p23_rounded_mat_mul_bound fp n R X hvn i j
      have hround :
          |p23RoundedMatMul fp R X i j - p23MatMul R X i j| ≤
            gn * ((1 + gk) * p23PowerSteps (p23AbsMatrix X) (k + 1) i j) := by
        exact le_trans (by simpa [gn] using hround0)
          (mul_le_mul_of_nonneg_left hsumR hgn)
      have hprop :
          |p23MatMul R X i j - p23MatMul P X i j| ≤
            gk * p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by
        rw [p23MatMul, p23MatMul]
        calc
          |(∑ t, R i t * X t j) - ∑ t, P i t * X t j| =
              |∑ t, (R i t - P i t) * X t j| := by
            congr 1
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro t ht
            ring
          _ ≤ ∑ t, |(R i t - P i t) * X t j| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ t, (gk * Q i t) * |X t j| := by
            apply Finset.sum_le_sum
            intro t ht
            rw [abs_mul]
            apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
            simpa [R, P, Q, gk] using ih hvk i t
          _ = gk * ∑ t, Q i t * |X t j| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro t ht
            ring
          _ = gk * p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by
            rfl
      have htotal :
          |p23RoundedMatMul fp R X i j - p23MatMul P X i j| ≤
            (gn * (1 + gk) + gk) *
              p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by
        calc
          |p23RoundedMatMul fp R X i j - p23MatMul P X i j| ≤
              |p23RoundedMatMul fp R X i j - p23MatMul R X i j| +
                |p23MatMul R X i j - p23MatMul P X i j| := by
            have heq :
                p23RoundedMatMul fp R X i j - p23MatMul P X i j =
                  (p23RoundedMatMul fp R X i j - p23MatMul R X i j) +
                    (p23MatMul R X i j - p23MatMul P X i j) := by ring
            rw [heq]
            exact abs_add_le _ _
          _ ≤ gn * ((1 + gk) *
                p23PowerSteps (p23AbsMatrix X) (k + 1) i j) +
              gk * p23PowerSteps (p23AbsMatrix X) (k + 1) i j :=
            add_le_add hround hprop
          _ = (gn * (1 + gk) + gk) *
              p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by ring
      have haddvalid : P23GammaValid fp.u (k * n + n) := by
        simpa [Nat.add_mul] using hvalid
      have hgamma := p23_gamma_add fp.u (k * n) n fp.u_nonneg haddvalid
      have hcoef : gn * (1 + gk) + gk ≤ p23Gamma fp.u (k * n + n) := by
        dsimp [gn, gk]
        nlinarith [hgamma]
      have hQ : 0 ≤ p23PowerSteps (p23AbsMatrix X) (k + 1) i j :=
        p23_abs_power_nonneg n X (k + 1) i j
      rw [p23RoundedPowerSteps, p23PowerSteps]
      exact le_trans (by simpa [R, P] using htotal)
        (by
          simpa [Nat.add_mul] using
            mul_le_mul_of_nonneg_right hcoef hQ)

end HighamBench
