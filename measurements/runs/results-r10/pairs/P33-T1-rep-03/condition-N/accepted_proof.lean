import HighamBench.P33Definitions

namespace HighamBench

open scoped BigOperators

private lemma p33_gamma_nonneg
    (u : ℝ) (n : ℕ) (hu : 0 ≤ u) (hvalid : P33GammaValid u n) :
    0 ≤ p33Gamma u n := by
  unfold p33Gamma P33GammaValid at *
  have hd : 0 < 1 - (n : ℝ) * u := by linarith
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) hu) hd.le

private lemma p33_gamma_step_acc
    (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (hvalid : P33GammaValid u (n + 1)) :
    u + (1 + u) * p33Gamma u n ≤ p33Gamma u (n + 1) := by
  unfold p33Gamma P33GammaValid at *
  norm_num [Nat.cast_add, Nat.cast_one] at hvalid ⊢
  have hnu : (n : ℝ) * u ≤ ((n : ℝ) + 1) * u := by
    nlinarith
  have hd : 0 < 1 - (n : ℝ) * u := by linarith
  have hd' : 0 < 1 - ((n : ℝ) + 1) * u := by linarith
  have heq :
      u + (1 + u) * ((n : ℝ) * u / (1 - (n : ℝ) * u)) =
        ((n : ℝ) + 1) * u / (1 - (n : ℝ) * u) := by
    have hdcomm : 1 - u * (n : ℝ) ≠ 0 := by nlinarith
    field_simp [ne_of_gt hd, hdcomm]
    ring
  rw [heq]
  apply (div_le_div_iff₀ hd hd').2
  have hnum : 0 ≤ ((n : ℝ) + 1) * u := by positivity
  nlinarith [mul_nonneg hnum (sub_nonneg.mpr hnu)]

private lemma p33_gamma_step_new
    (u : ℝ) (n : ℕ) (hu : 0 ≤ u) (hn : 1 ≤ n)
    (hvalid : P33GammaValid u (n + 1)) :
    2 * u + u ^ 2 ≤ p33Gamma u (n + 1) := by
  unfold p33Gamma P33GammaValid at *
  norm_num [Nat.cast_add, Nat.cast_one] at hvalid ⊢
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd : 0 < 1 - ((n : ℝ) + 1) * u := by linarith
  apply (le_div_iff₀ hd).2
  have hnm1 : 0 ≤ (n : ℝ) - 1 := by linarith
  have hcoef : 0 ≤ 2 * ((n : ℝ) + 1) - 1 := by linarith
  have hpoly :
      0 ≤ ((n : ℝ) - 1) * u +
        (2 * ((n : ℝ) + 1) - 1) * u ^ 2 +
        ((n : ℝ) + 1) * u ^ 3 := by
    positivity
  nlinarith

private lemma p33_u_le_gamma
    (u : ℝ) (n : ℕ) (hu : 0 ≤ u) (hn : 1 ≤ n)
    (hvalid : P33GammaValid u n) :
    u ≤ p33Gamma u n := by
  unfold p33Gamma P33GammaValid at *
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd : 0 < 1 - (n : ℝ) * u := by linarith
  apply (le_div_iff₀ hd).2
  have hnm1 : 0 ≤ (n : ℝ) - 1 := by linarith
  have hpoly : 0 ≤ ((n : ℝ) - 1) * u + (n : ℝ) * u ^ 2 := by
    positivity
  nlinarith

private lemma p33_gammaValid_of_le
    (u : ℝ) (m n : ℕ) (hu : 0 ≤ u) (hmn : m ≤ n)
    (hvalid : P33GammaValid u n) :
    P33GammaValid u m := by
  unfold P33GammaValid at *
  have hcast : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  nlinarith [mul_le_mul_of_nonneg_right hcast hu]

private lemma p33_row_product_append
    (fp : P33FPModel) (n : ℕ) (a x : Fin (n + 2) → ℝ) :
    p33RoundedSparseRowProduct fp (n + 2) a x =
      fp.fl_add
        (p33RoundedSparseRowProduct fp (n + 1)
          (fun i ↦ a i.castSucc) (fun i ↦ x i.castSucc))
        (fp.fl_mul (a (Fin.last (n + 1))) (x (Fin.last (n + 1)))) := by
  simp only [p33RoundedSparseRowProduct, Fin.foldl_succ_last]
  congr 2

private lemma p33_rounded_append_bound
    (fp : P33FPModel) (n : ℕ) (hn : 1 ≤ n)
    (hvalid : P33GammaValid fp.u (n + 1))
    (q T S y x : ℝ)
    (hS : 0 ≤ S) (hT : |T| ≤ S)
    (hq : |q - T| ≤ p33Gamma fp.u n * S) :
    |fp.fl_add q (fp.fl_mul y x) - (T + y * x)| ≤
      p33Gamma fp.u (n + 1) * (S + |y| * |x|) := by
  obtain ⟨dm, hdm, hmul⟩ := fp.model_mul y x
  obtain ⟨da, hda, hadd⟩ := fp.model_add q (fp.fl_mul y x)
  rw [hadd, hmul]
  have hgamma : 0 ≤ p33Gamma fp.u n :=
    p33_gamma_nonneg fp.u n fp.u_nonneg
      (p33_gammaValid_of_le fp.u n (n + 1) fp.u_nonneg (Nat.le_succ n) hvalid)
  have hone : |1 + da| ≤ 1 + fp.u := by
    calc
      |1 + da| ≤ |(1 : ℝ)| + |da| := abs_add_le 1 da
      _ ≤ 1 + fp.u := by norm_num; linarith
  have hdmda : |dm| * |da| ≤ fp.u * fp.u :=
    mul_le_mul hdm hda (abs_nonneg da) fp.u_nonneg
  have htheta : |dm + da + dm * da| ≤ 2 * fp.u + fp.u ^ 2 := by
    calc
      |dm + da + dm * da| ≤ |dm| + |da| + |dm * da| := by
        exact (abs_add_le (dm + da) (dm * da)).trans
          (add_le_add (abs_add_le dm da) (le_refl _))
      _ = |dm| + |da| + |dm| * |da| := by rw [abs_mul]
      _ ≤ 2 * fp.u + fp.u ^ 2 := by nlinarith
  have hdecomp :
      (q + y * x * (1 + dm)) * (1 + da) - (T + y * x) =
        (1 + da) * (q - T) + da * T + (dm + da + dm * da) * (y * x) := by
    ring
  rw [hdecomp]
  have htriangle :
      |(1 + da) * (q - T) + da * T + (dm + da + dm * da) * (y * x)| ≤
        |1 + da| * |q - T| + |da| * |T| +
          |dm + da + dm * da| * |y * x| := by
    calc
      |(1 + da) * (q - T) + da * T + (dm + da + dm * da) * (y * x)| ≤
          |(1 + da) * (q - T) + da * T| +
            |(dm + da + dm * da) * (y * x)| := abs_add_le _ _
      _ ≤ (|(1 + da) * (q - T)| + |da * T|) +
            |(dm + da + dm * da) * (y * x)| := by
          gcongr
          exact abs_add_le _ _
      _ = |1 + da| * |q - T| + |da| * |T| +
            |dm + da + dm * da| * |y * x| := by simp only [abs_mul]
  calc
    |(1 + da) * (q - T) + da * T + (dm + da + dm * da) * (y * x)| ≤
        |1 + da| * |q - T| + |da| * |T| +
          |dm + da + dm * da| * |y * x| := htriangle
    _ ≤ ((1 + fp.u) * p33Gamma fp.u n + fp.u) * S +
          (2 * fp.u + fp.u ^ 2) * (|y| * |x|) := by
      rw [abs_mul]
      have h1 : |1 + da| * |q - T| ≤
          (1 + fp.u) * (p33Gamma fp.u n * S) :=
        mul_le_mul hone hq (abs_nonneg _) (by linarith [fp.u_nonneg])
      have h2 : |da| * |T| ≤ fp.u * S :=
        mul_le_mul hda hT (abs_nonneg _) fp.u_nonneg
      have h3 : |dm + da + dm * da| * (|y| * |x|) ≤
          (2 * fp.u + fp.u ^ 2) * (|y| * |x|) :=
        mul_le_mul_of_nonneg_right htheta (by positivity)
      nlinarith
    _ ≤ p33Gamma fp.u (n + 1) * (S + |y| * |x|) := by
      have ha : (1 + fp.u) * p33Gamma fp.u n + fp.u ≤
          p33Gamma fp.u (n + 1) := by
        simpa [add_comm] using p33_gamma_step_acc fp.u n fp.u_nonneg hvalid
      have hb : 2 * fp.u + fp.u ^ 2 ≤ p33Gamma fp.u (n + 1) :=
        p33_gamma_step_new fp.u n fp.u_nonneg hn hvalid
      have ha' := mul_le_mul_of_nonneg_right ha hS
      have hb' := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ |y| * |x|)
      nlinarith

private lemma p33_row_product_error
    (fp : P33FPModel) (s : ℕ) (a x : Fin s → ℝ)
    (hvalid : P33GammaValid fp.u s) :
    |p33RoundedSparseRowProduct fp s a x - ∑ i : Fin s, a i * x i| ≤
      p33Gamma fp.u s * ∑ i : Fin s, |a i| * |x i| := by
  induction s with
  | zero =>
      simp [p33RoundedSparseRowProduct, p33Gamma]
  | succ n ih =>
      cases n with
      | zero =>
          obtain ⟨d, hd, hmul⟩ := fp.model_mul (a 0) (x 0)
          have hug : fp.u ≤ p33Gamma fp.u 1 :=
            p33_u_le_gamma fp.u 1 fp.u_nonneg (by omega) hvalid
          simp only [p33RoundedSparseRowProduct, Fin.sum_univ_succ,
            Fin.sum_univ_zero, Fin.foldl_zero, add_zero, Nat.zero_add]
          rw [hmul]
          have heq : a 0 * x 0 * (1 + d) - a 0 * x 0 = (a 0 * x 0) * d := by
            ring
          rw [heq, abs_mul]
          calc
            |a 0 * x 0| * |d| ≤ |a 0 * x 0| * fp.u :=
              mul_le_mul_of_nonneg_left hd (abs_nonneg _)
            _ ≤ |a 0 * x 0| * p33Gamma fp.u 1 :=
              mul_le_mul_of_nonneg_left hug (abs_nonneg _)
            _ = p33Gamma fp.u 1 * (|a 0| * |x 0|) := by
              rw [abs_mul]
              ring
      | succ k =>
          let ap : Fin (k + 1) → ℝ := fun i ↦ a i.castSucc
          let xp : Fin (k + 1) → ℝ := fun i ↦ x i.castSucc
          let q := p33RoundedSparseRowProduct fp (k + 1) ap xp
          let T := ∑ i : Fin (k + 1), ap i * xp i
          let S := ∑ i : Fin (k + 1), |ap i| * |xp i|
          have hprev : P33GammaValid fp.u (k + 1) :=
            p33_gammaValid_of_le fp.u (k + 1) (Nat.succ (Nat.succ k))
              fp.u_nonneg (by omega) hvalid
          have hq : |q - T| ≤ p33Gamma fp.u (k + 1) * S := by
            exact ih ap xp hprev
          have hS : 0 ≤ S := by
            dsimp [S]
            positivity
          have hT : |T| ≤ S := by
            dsimp [T, S]
            calc
              |∑ i : Fin (k + 1), ap i * xp i| ≤
                  ∑ i : Fin (k + 1), |ap i * xp i| := by
                    simpa using
                      (Finset.abs_sum_le_sum_abs
                        (fun i : Fin (k + 1) ↦ ap i * xp i) Finset.univ)
              _ = ∑ i : Fin (k + 1), |ap i| * |xp i| := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    exact abs_mul (ap i) (xp i)
          have happ := p33_rounded_append_bound fp (k + 1) (by omega) hvalid
            q T S (a (Fin.last (k + 1))) (x (Fin.last (k + 1))) hS hT hq
          dsimp [q, T, S, ap, xp] at happ
          have hexact := Fin.sum_univ_castSucc
            (fun i : Fin (k + 2) ↦ a i * x i)
          have habs := Fin.sum_univ_castSucc
            (fun i : Fin (k + 2) ↦ |a i| * |x i|)
          rw [p33_row_product_append]
          rw [hexact, habs]
          exact happ

/-- P33-T1: the sparse-row computed-residual error bound in Section 2.2. -/
theorem p33_t1_sparse_residual_error
    (fp : P33FPModel) (s : ℕ) (a x : Fin s → ℝ) (b : ℝ)
    (hvalid : P33GammaValid fp.u (s + 1)) :
    |p33RoundedResidual fp s a x b - p33ExactResidual s a x b| ≤
      p33ResidualErrorMajorant fp s a x b := by
  -- PROOF_START P33-T1-H001
  let q := p33RoundedSparseRowProduct fp s a x
  let T := ∑ i : Fin s, a i * x i
  let S := ∑ i : Fin s, |a i| * |x i|
  have hvalid_s : P33GammaValid fp.u s :=
    p33_gammaValid_of_le fp.u s (s + 1) fp.u_nonneg (Nat.le_succ s) hvalid
  have hq : |q - T| ≤ p33Gamma fp.u s * S := by
    exact p33_row_product_error fp s a x hvalid_s
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hT : |T| ≤ S := by
    dsimp [T, S]
    calc
      |∑ i : Fin s, a i * x i| ≤ ∑ i : Fin s, |a i * x i| := by
        simpa using
          (Finset.abs_sum_le_sum_abs (fun i : Fin s ↦ a i * x i) Finset.univ)
      _ = ∑ i : Fin s, |a i| * |x i| := by
        apply Finset.sum_congr rfl
        intro i hi
        exact abs_mul (a i) (x i)
  obtain ⟨d, hd, hsub⟩ := fp.model_sub b q
  change |fp.fl_sub b q - (b - T)| ≤
    p33Gamma fp.u (s + 1) * (|b| + S)
  rw [hsub]
  have hone : |1 + d| ≤ 1 + fp.u := by
    calc
      |1 + d| ≤ |(1 : ℝ)| + |d| := abs_add_le 1 d
      _ ≤ 1 + fp.u := by norm_num; linarith
  have hbT : |b - T| ≤ |b| + S := by
    exact (abs_sub b T).trans (add_le_add (le_refl _) hT)
  have hdecomp :
      (b - q) * (1 + d) - (b - T) =
        d * (b - T) - (1 + d) * (q - T) := by
    ring
  rw [hdecomp]
  calc
    |d * (b - T) - (1 + d) * (q - T)| ≤
        |d| * |b - T| + |1 + d| * |q - T| := by
      calc
        |d * (b - T) - (1 + d) * (q - T)| =
            |d * (b - T) + (-(1 + d) * (q - T))| := by ring_nf
        _ ≤ |d * (b - T)| + |-(1 + d) * (q - T)| := abs_add_le _ _
        _ = |d| * |b - T| + |1 + d| * |q - T| := by
          simp only [abs_mul, abs_neg]
    _ ≤ fp.u * (|b| + S) +
          (1 + fp.u) * (p33Gamma fp.u s * S) := by
      have h1 : |d| * |b - T| ≤ fp.u * (|b| + S) :=
        mul_le_mul hd hbT (abs_nonneg _) fp.u_nonneg
      have h2 : |1 + d| * |q - T| ≤
          (1 + fp.u) * (p33Gamma fp.u s * S) :=
        mul_le_mul hone hq (abs_nonneg _) (by linarith [fp.u_nonneg])
      linarith
    _ ≤ p33Gamma fp.u (s + 1) * (|b| + S) := by
      have hub : fp.u ≤ p33Gamma fp.u (s + 1) :=
        p33_u_le_gamma fp.u (s + 1) fp.u_nonneg (by omega) hvalid
      have hcoef : fp.u + (1 + fp.u) * p33Gamma fp.u s ≤
          p33Gamma fp.u (s + 1) :=
        p33_gamma_step_acc fp.u s fp.u_nonneg hvalid
      have hb := mul_le_mul_of_nonneg_right hub (abs_nonneg b)
      have hs := mul_le_mul_of_nonneg_right hcoef hS
      nlinarith

end HighamBench
