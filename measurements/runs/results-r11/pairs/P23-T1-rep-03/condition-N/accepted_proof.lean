import Mathlib
import HighamBench.P23Definitions

namespace HighamBench

private lemma p23_valid_mono {u : ℝ} (hu : 0 ≤ u) {a b : ℕ}
    (hab : a ≤ b) (hb : P23GammaValid u b) : P23GammaValid u a := by
  unfold P23GammaValid at hb ⊢
  have hc : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  nlinarith [mul_le_mul_of_nonneg_right hc hu]

private lemma p23_gamma_nonneg {u : ℝ} (hu : 0 ≤ u) (a : ℕ)
    (hvalid : P23GammaValid u a) :
    0 ≤ p23Gamma u a := by
  unfold P23GammaValid at hvalid
  unfold p23Gamma
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

private lemma p23_u_le_gamma_one {u : ℝ} (hu : 0 ≤ u)
    (hvalid : P23GammaValid u 1) : u ≤ p23Gamma u 1 := by
  unfold P23GammaValid at hvalid
  unfold p23Gamma
  norm_num at hvalid ⊢
  apply (le_div_iff₀ (by linarith)).2
  nlinarith [sq_nonneg u]

private lemma p23_gamma_mono {u : ℝ} (hu : 0 ≤ u) {a b : ℕ}
    (hab : a ≤ b) (hvalid : P23GammaValid u b) :
    p23Gamma u a ≤ p23Gamma u b := by
  unfold P23GammaValid at hvalid
  have hc : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hmul : (a : ℝ) * u ≤ (b : ℝ) * u :=
    mul_le_mul_of_nonneg_right hc hu
  have hda : 0 < 1 - (a : ℝ) * u := by linarith
  have hdb : 0 < 1 - (b : ℝ) * u := by linarith
  unfold p23Gamma
  apply (div_le_div_iff₀ hda hdb).2
  nlinarith

private lemma p23_gamma_step {u : ℝ} (hu : 0 ≤ u) (p : ℕ)
    (hvalid : P23GammaValid u (p + 1)) :
    (1 + u) * p23Gamma u p + u ≤ p23Gamma u (p + 1) := by
  unfold P23GammaValid at hvalid
  have hdp : 0 < 1 - (p : ℝ) * u := by
    norm_num [Nat.cast_add] at hvalid
    nlinarith [mul_nonneg (Nat.cast_nonneg p) hu]
  have hds : 0 < 1 - ((p : ℝ) + 1) * u := by
    norm_num [Nat.cast_add] at hvalid
    exact sub_pos.mpr hvalid
  have heq :
      (1 + u) * p23Gamma u p + u =
        (((p : ℝ) + 1) * u) / (1 - (p : ℝ) * u) := by
    unfold p23Gamma
    have hn : 1 - u * (p : ℝ) ≠ 0 := by nlinarith
    field_simp [hn]
    ring
  rw [heq]
  unfold p23Gamma
  norm_num [Nat.cast_add]
  apply (div_le_div_iff₀ hdp hds).2
  have hn : 0 ≤ ((p : ℝ) + 1) * u :=
    mul_nonneg (by positivity) hu
  nlinarith [mul_nonneg hn hu]

private lemma p23_two_error_coeff {u : ℝ} (hu : 0 ≤ u) (p : ℕ)
    (hp : 1 ≤ p) (hvalid : P23GammaValid u (p + 1)) :
    2 * u + u ^ 2 ≤ p23Gamma u (p + 1) := by
  have htwo : 2 ≤ p + 1 := by omega
  have hv2 : P23GammaValid u 2 :=
    p23_valid_mono hu htwo hvalid
  have hv1 : P23GammaValid u 1 :=
    p23_valid_mono hu (by omega) hv2
  have h1 := p23_u_le_gamma_one hu hv1
  have hs := p23_gamma_step hu 1 hv2
  have hc : 2 * u + u ^ 2 ≤ (1 + u) * p23Gamma u 1 + u := by
    have hfac : 0 ≤ 1 + u := by positivity
    calc
      2 * u + u ^ 2 = (1 + u) * u + u := by ring
      _ ≤ (1 + u) * p23Gamma u 1 + u := by
        gcongr
  exact hc.trans (hs.trans (p23_gamma_mono hu htwo hvalid))

private lemma p23_gamma_add {u : ℝ} (hu : 0 ≤ u) (a b : ℕ)
    (hvalid : P23GammaValid u (a + b)) :
    p23Gamma u a + p23Gamma u b * (1 + p23Gamma u a) ≤
      p23Gamma u (a + b) := by
  unfold P23GammaValid at hvalid
  have hab : ((a + b : ℕ) : ℝ) * u =
      (a : ℝ) * u + (b : ℝ) * u := by
    norm_num [Nat.cast_add]
    ring
  have hsum : (a : ℝ) * u + (b : ℝ) * u < 1 := by
    rw [← hab]
    exact hvalid
  have hda : 0 < 1 - (a : ℝ) * u := by
    nlinarith [mul_nonneg (Nat.cast_nonneg b) hu]
  have hdb : 0 < 1 - (b : ℝ) * u := by
    nlinarith [mul_nonneg (Nat.cast_nonneg a) hu]
  have hds : 0 < 1 - ((a : ℝ) * u + (b : ℝ) * u) := by
    linarith
  have hprod : 0 < (1 - (a : ℝ) * u) * (1 - (b : ℝ) * u) :=
    mul_pos hda hdb
  have hrecip :
      1 / ((1 - (a : ℝ) * u) * (1 - (b : ℝ) * u)) ≤
        1 / (1 - ((a : ℝ) * u + (b : ℝ) * u)) := by
    apply (div_le_div_iff₀ hprod hds).2
    nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg a) hu)
      (mul_nonneg (Nat.cast_nonneg b) hu)]
  have haid : 1 + p23Gamma u a = 1 / (1 - (a : ℝ) * u) := by
    unfold p23Gamma
    field_simp
    ring
  have hbid : 1 + p23Gamma u b = 1 / (1 - (b : ℝ) * u) := by
    unfold p23Gamma
    field_simp
    ring
  have habid : 1 + p23Gamma u (a + b) =
      1 / (1 - ((a : ℝ) * u + (b : ℝ) * u)) := by
    unfold p23Gamma
    rw [Nat.cast_add]
    rw [show 1 - ((a : ℝ) + (b : ℝ)) * u =
      1 - (a : ℝ) * u - (b : ℝ) * u by ring]
    rw [show 1 - ((a : ℝ) * u + (b : ℝ) * u) =
      1 - (a : ℝ) * u - (b : ℝ) * u by ring]
    have hn : 1 - (a : ℝ) * u - (b : ℝ) * u ≠ 0 := by
      nlinarith
    field_simp [hn]
    ring
  calc
    p23Gamma u a + p23Gamma u b * (1 + p23Gamma u a)
        = (1 + p23Gamma u a) * (1 + p23Gamma u b) - 1 := by ring
    _ ≤ (1 + p23Gamma u (a + b)) - 1 := by
      rw [haid, hbid, habid]
      rw [one_div_mul_one_div]
      linarith
    _ = p23Gamma u (a + b) := by ring

private lemma p23_mul_error (fp : P23FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * |x * y| := by
  rcases fp.model_mul x y with ⟨δ, hδ, hmul⟩
  rw [hmul]
  have heq : (x * y) * (1 + δ) - x * y = (x * y) * δ := by ring
  rw [heq, abs_mul]
  have h := mul_le_mul_of_nonneg_left hδ (abs_nonneg (x * y))
  simpa [mul_comm] using h

private lemma p23_rounded_add_extend
    (fp : P23FPModel) (p : ℕ) (hp : 1 ≤ p)
    (hvalid : P23GammaValid fp.u (p + 1))
    (r s q v B : ℝ)
    (hr : |r - s| ≤ p23Gamma fp.u p * B)
    (hs : |s| ≤ B)
    (hq : |q - v| ≤ fp.u * |v|) :
    |fp.fl_add r q - (s + v)| ≤
      p23Gamma fp.u (p + 1) * (B + |v|) := by
  have hu := fp.u_nonneg
  have hB : 0 ≤ B := (abs_nonneg s).trans hs
  have hrabs : |r| ≤ B + p23Gamma fp.u p * B := by
    calc
      |r| = |(r - s) + s| := by ring_nf
      _ ≤ |r - s| + |s| := abs_add_le _ _
      _ ≤ p23Gamma fp.u p * B + B := add_le_add hr hs
      _ = B + p23Gamma fp.u p * B := by ring
  have hqabs : |q| ≤ |v| + fp.u * |v| := by
    calc
      |q| = |(q - v) + v| := by ring_nf
      _ ≤ |q - v| + |v| := abs_add_le _ _
      _ ≤ fp.u * |v| + |v| := add_le_add_left hq _
      _ = |v| + fp.u * |v| := by ring
  rcases fp.model_add r q with ⟨δ, hδ, hadd⟩
  have herr :
      |fp.fl_add r q - (s + v)| ≤
        |r - s| + |q - v| + (|r| + |q|) * fp.u := by
    rw [hadd]
    have heq : (r + q) * (1 + δ) - (s + v) =
        (r - s) + (q - v) + (r + q) * δ := by ring
    rw [heq]
    calc
      |(r - s) + (q - v) + (r + q) * δ| ≤
          |r - s| + |q - v| + |(r + q) * δ| :=
        abs_add_three _ _ _
      _ = |r - s| + |q - v| + |r + q| * |δ| := by
        rw [abs_mul]
      _ ≤ |r - s| + |q - v| + (|r| + |q|) * fp.u := by
        gcongr
        exact abs_add_le _ _
  have hraw :
      |fp.fl_add r q - (s + v)| ≤
        p23Gamma fp.u p * B + fp.u * |v| +
          ((B + p23Gamma fp.u p * B) +
            (|v| + fp.u * |v|)) * fp.u := by
    refine herr.trans ?_
    apply add_le_add
    · exact add_le_add hr hq
    · apply mul_le_mul_of_nonneg_right _ hu
      exact add_le_add hrabs hqabs
  have hcB := p23_gamma_step hu p hvalid
  have hcV := p23_two_error_coeff hu p hp hvalid
  calc
    |fp.fl_add r q - (s + v)| ≤
        p23Gamma fp.u p * B + fp.u * |v| +
          ((B + p23Gamma fp.u p * B) +
            (|v| + fp.u * |v|)) * fp.u := hraw
    _ = ((1 + fp.u) * p23Gamma fp.u p + fp.u) * B +
          (2 * fp.u + fp.u ^ 2) * |v| := by ring
    _ ≤ p23Gamma fp.u (p + 1) * B +
          p23Gamma fp.u (p + 1) * |v| := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hcB hB)
        (mul_le_mul_of_nonneg_right hcV (abs_nonneg v))
    _ = p23Gamma fp.u (p + 1) * (B + |v|) := by ring

private lemma p23_fold_bound
    (fp : P23FPModel) (m p : ℕ) (hp : 1 ≤ p)
    (hvalid : P23GammaValid fp.u (p + m))
    (r s B : ℝ) (q v : Fin m → ℝ)
    (hr : |r - s| ≤ p23Gamma fp.u p * B)
    (hs : |s| ≤ B)
    (hq : ∀ i, |q i - v i| ≤ fp.u * |v i|) :
    |Fin.foldl m (fun acc i => fp.fl_add acc (q i)) r -
        (s + ∑ i, v i)| ≤
      p23Gamma fp.u (p + m) * (B + ∑ i, |v i|) := by
  induction m generalizing p r s B with
  | zero =>
      simpa using hr
  | succ m ih =>
      have hvstep : P23GammaValid fp.u (p + 1) :=
        p23_valid_mono fp.u_nonneg (by omega) hvalid
      have hfirst := p23_rounded_add_extend fp p hp hvstep r s (q 0) (v 0) B
        hr hs (hq 0)
      have hsfirst : |s + v 0| ≤ B + |v 0| := by
        exact (abs_add_le s (v 0)).trans (add_le_add_left hs _)
      have htail := ih (p := p + 1) (by omega)
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hvalid)
        (r := fp.fl_add r (q 0)) (s := s + v 0) (B := B + |v 0|)
        (q := fun i => q i.succ) (v := fun i => v i.succ)
        hfirst hsfirst (fun i => hq i.succ)
      simpa [Fin.foldl_succ, Fin.sum_univ_succ, add_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

private lemma p23_rounded_dot_bound
    (fp : P23FPModel) (n : ℕ) (x y : Fin n → ℝ)
    (hvalid : P23GammaValid fp.u n) :
    |p23RoundedDotProduct fp n x y - ∑ i, x i * y i| ≤
      p23Gamma fp.u n * ∑ i, |x i * y i| := by
  cases n with
  | zero =>
      simp [p23RoundedDotProduct, p23Gamma]
  | succ m =>
      have hv1 : P23GammaValid fp.u 1 :=
        p23_valid_mono fp.u_nonneg (by omega) hvalid
      have hgu := p23_u_le_gamma_one fp.u_nonneg hv1
      have hmul0 :
          |fp.fl_mul (x 0) (y 0) - x 0 * y 0| ≤
            p23Gamma fp.u 1 * |x 0 * y 0| := by
        calc
          |fp.fl_mul (x 0) (y 0) - x 0 * y 0| ≤
              fp.u * |x 0 * y 0| := p23_mul_error fp _ _
          _ ≤ p23Gamma fp.u 1 * |x 0 * y 0| :=
            mul_le_mul_of_nonneg_right hgu (abs_nonneg _)
      have hfold := p23_fold_bound fp m 1 (by omega)
        (by simpa [Nat.add_comm] using hvalid)
        (r := fp.fl_mul (x 0) (y 0)) (s := x 0 * y 0)
        (B := |x 0 * y 0|)
        (q := fun i => fp.fl_mul (x i.succ) (y i.succ))
        (v := fun i => x i.succ * y i.succ)
        hmul0 (le_refl _)
        (fun i => p23_mul_error fp (x i.succ) (y i.succ))
      simpa [p23RoundedDotProduct, Fin.sum_univ_succ, Nat.add_comm]
        using hfold

private lemma p23_abs_power_nonneg {n : ℕ} (X : P23Matrix n) :
    ∀ k i j, 0 ≤ p23PowerSteps (p23AbsMatrix X) k i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      simp [p23PowerSteps, p23AbsMatrix]
  | succ k ih =>
      intro i j
      simp only [p23PowerSteps, p23MatMul]
      apply Finset.sum_nonneg
      intro l hl
      exact mul_nonneg (ih i l) (by simp [p23AbsMatrix])

private lemma p23_exact_power_abs_le {n : ℕ} (X : P23Matrix n) :
    ∀ k i j,
      |p23PowerSteps X k i j| ≤
        p23PowerSteps (p23AbsMatrix X) k i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      simp [p23PowerSteps, p23AbsMatrix]
  | succ k ih =>
      intro i j
      simp only [p23PowerSteps, p23MatMul]
      calc
        |∑ l, p23PowerSteps X k i l * X l j| ≤
            ∑ l, |p23PowerSteps X k i l * X l j| := by
          simpa using Finset.abs_sum_le_sum_abs
            (fun l : Fin n => p23PowerSteps X k i l * X l j) Finset.univ
        _ = ∑ l, |p23PowerSteps X k i l| * |X l j| := by
          apply Finset.sum_congr rfl
          intro l hl
          exact abs_mul _ _
        _ ≤ ∑ l,
            p23PowerSteps (p23AbsMatrix X) k i l * |X l j| := by
          apply Finset.sum_le_sum
          intro l hl
          exact mul_le_mul_of_nonneg_right (ih i l) (abs_nonneg _)
        _ = ∑ l,
            p23PowerSteps (p23AbsMatrix X) k i l *
              p23AbsMatrix X l j := by
          apply Finset.sum_congr rfl
          intro l hl
          rfl

private lemma p23_rounded_matmul_bound
    (fp : P23FPModel) {n : ℕ} (A B : P23Matrix n)
    (hvalid : P23GammaValid fp.u n) (i j : Fin n) :
    |p23RoundedMatMul fp A B i j - p23MatMul A B i j| ≤
      p23Gamma fp.u n * p23MatMul (p23AbsMatrix A) (p23AbsMatrix B) i j := by
  simpa [p23RoundedMatMul, p23MatMul, p23AbsMatrix, abs_mul]
    using p23_rounded_dot_bound fp n (A i) (fun l => B l j) hvalid

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
      have hkn_le : k * n ≤ (k + 1) * n :=
        Nat.mul_le_mul_right n (Nat.le_succ k)
      have hn_le : n ≤ (k + 1) * n := by
        have h := Nat.mul_le_mul_right n (show 1 ≤ k + 1 by omega)
        simpa using h
      have hvkn : P23GammaValid fp.u (k * n) :=
        p23_valid_mono fp.u_nonneg hkn_le hvalid
      have hvn : P23GammaValid fp.u n :=
        p23_valid_mono fp.u_nonneg hn_le hvalid
      let R : P23Matrix n := p23RoundedPowerSteps fp X k
      let E : P23Matrix n := p23PowerSteps X k
      let A : P23Matrix n := p23PowerSteps (p23AbsMatrix X) k
      have hentry (l : Fin n) :
          |R i l - E i l| ≤ p23Gamma fp.u (k * n) * A i l := by
        simpa [R, E, A] using ih hvkn i l
      have hexact (l : Fin n) : |E i l| ≤ A i l := by
        simpa [E, A] using p23_exact_power_abs_le X k i l
      have hRabs (l : Fin n) :
          |R i l| ≤ (1 + p23Gamma fp.u (k * n)) * A i l := by
        calc
          |R i l| = |(R i l - E i l) + E i l| := by ring_nf
          _ ≤ |R i l - E i l| + |E i l| := abs_add_le _ _
          _ ≤ p23Gamma fp.u (k * n) * A i l + A i l :=
            add_le_add (hentry l) (hexact l)
          _ = (1 + p23Gamma fp.u (k * n)) * A i l := by ring
      have hpow :
          p23PowerSteps (p23AbsMatrix X) (k + 1) i j =
            ∑ l, A i l * |X l j| := by
        simp [p23PowerSteps, p23MatMul, p23AbsMatrix, A]
      have habsmul :
          p23MatMul (p23AbsMatrix R) (p23AbsMatrix X) i j ≤
            (1 + p23Gamma fp.u (k * n)) *
              p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by
        change (∑ l, |R i l| * |X l j|) ≤
          (1 + p23Gamma fp.u (k * n)) *
            p23PowerSteps (p23AbsMatrix X) (k + 1) i j
        rw [hpow, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro l hl
        calc
          |R i l| * |X l j| ≤
              ((1 + p23Gamma fp.u (k * n)) * A i l) * |X l j| :=
            mul_le_mul_of_nonneg_right (hRabs l) (abs_nonneg _)
          _ = (1 + p23Gamma fp.u (k * n)) * (A i l * |X l j|) := by
            ring
      have hgn : 0 ≤ p23Gamma fp.u n :=
        p23_gamma_nonneg fp.u_nonneg n hvn
      have hround0 := p23_rounded_matmul_bound fp R X hvn i j
      have hround :
          |p23RoundedMatMul fp R X i j - p23MatMul R X i j| ≤
            (p23Gamma fp.u n * (1 + p23Gamma fp.u (k * n))) *
              p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by
        calc
          |p23RoundedMatMul fp R X i j - p23MatMul R X i j| ≤
              p23Gamma fp.u n *
                p23MatMul (p23AbsMatrix R) (p23AbsMatrix X) i j := hround0
          _ ≤ p23Gamma fp.u n *
              ((1 + p23Gamma fp.u (k * n)) *
                p23PowerSteps (p23AbsMatrix X) (k + 1) i j) :=
            mul_le_mul_of_nonneg_left habsmul hgn
          _ = (p23Gamma fp.u n * (1 + p23Gamma fp.u (k * n))) *
              p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by ring
      have hdiff :
          p23MatMul R X i j - p23MatMul E X i j =
            ∑ l, (R i l - E i l) * X l j := by
        simp only [p23MatMul]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro l hl
        ring
      have hprop :
          |p23MatMul R X i j - p23MatMul E X i j| ≤
            p23Gamma fp.u (k * n) *
              p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by
        rw [hdiff]
        calc
          |∑ l, (R i l - E i l) * X l j| ≤
              ∑ l, |(R i l - E i l) * X l j| := by
            simpa using Finset.abs_sum_le_sum_abs
              (fun l : Fin n => (R i l - E i l) * X l j) Finset.univ
          _ = ∑ l, |R i l - E i l| * |X l j| := by
            apply Finset.sum_congr rfl
            intro l hl
            exact abs_mul _ _
          _ ≤ ∑ l,
              (p23Gamma fp.u (k * n) * A i l) * |X l j| := by
            apply Finset.sum_le_sum
            intro l hl
            exact mul_le_mul_of_nonneg_right (hentry l) (abs_nonneg _)
          _ = p23Gamma fp.u (k * n) * (∑ l, A i l * |X l j|) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro l hl
            ring
          _ = p23Gamma fp.u (k * n) *
              p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by
            rw [hpow]
      have hvsum : P23GammaValid fp.u (k * n + n) := by
        simpa [Nat.succ_mul] using hvalid
      have hcoeff :
          p23Gamma fp.u n * (1 + p23Gamma fp.u (k * n)) +
              p23Gamma fp.u (k * n) ≤
            p23Gamma fp.u ((k + 1) * n) := by
        calc
          p23Gamma fp.u n * (1 + p23Gamma fp.u (k * n)) +
              p23Gamma fp.u (k * n) =
            p23Gamma fp.u (k * n) +
              p23Gamma fp.u n * (1 + p23Gamma fp.u (k * n)) := by ring
          _ ≤ p23Gamma fp.u (k * n + n) :=
            p23_gamma_add fp.u_nonneg (k * n) n hvsum
          _ = p23Gamma fp.u ((k + 1) * n) := by
            rw [Nat.succ_mul]
      have hA :
          0 ≤ p23PowerSteps (p23AbsMatrix X) (k + 1) i j :=
        p23_abs_power_nonneg X (k + 1) i j
      change
        |p23RoundedMatMul fp R X i j - p23MatMul E X i j| ≤
          p23Gamma fp.u ((k + 1) * n) *
            p23PowerSteps (p23AbsMatrix X) (k + 1) i j
      calc
        |p23RoundedMatMul fp R X i j - p23MatMul E X i j| ≤
            |p23RoundedMatMul fp R X i j - p23MatMul R X i j| +
              |p23MatMul R X i j - p23MatMul E X i j| := by
          rw [show p23RoundedMatMul fp R X i j - p23MatMul E X i j =
            (p23RoundedMatMul fp R X i j - p23MatMul R X i j) +
              (p23MatMul R X i j - p23MatMul E X i j) by ring]
          exact abs_add_le _ _
        _ ≤ (p23Gamma fp.u n * (1 + p23Gamma fp.u (k * n))) *
              p23PowerSteps (p23AbsMatrix X) (k + 1) i j +
            p23Gamma fp.u (k * n) *
              p23PowerSteps (p23AbsMatrix X) (k + 1) i j :=
          add_le_add hround hprop
        _ = (p23Gamma fp.u n * (1 + p23Gamma fp.u (k * n)) +
              p23Gamma fp.u (k * n)) *
            p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by ring
        _ ≤ p23Gamma fp.u ((k + 1) * n) *
            p23PowerSteps (p23AbsMatrix X) (k + 1) i j :=
          mul_le_mul_of_nonneg_right hcoeff hA

end HighamBench
