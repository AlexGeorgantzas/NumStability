import HighamBench.P33Definitions

namespace HighamBench

open scoped BigOperators

private lemma p33_gamma_nonneg (u : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (hv : P33GammaValid u n) :
    0 ≤ p33Gamma u n := by
  unfold P33GammaValid at hv
  unfold p33Gamma
  have hd : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hv
  positivity

private lemma p33_u_le_gamma (u : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (hn : 1 ≤ n) (hv : P33GammaValid u n) :
    u ≤ p33Gamma u n := by
  unfold P33GammaValid at hv
  unfold p33Gamma
  have hd : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hv
  rw [le_div_iff₀ hd]
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  calc
    u * (1 - (n : ℝ) * u) ≤ u * 1 := by
      have hnu : 0 ≤ (n : ℝ) * u :=
        mul_nonneg (Nat.cast_nonneg n) hu
      exact mul_le_mul_of_nonneg_left (by linarith) hu
    _ ≤ (n : ℝ) * u := by
      simpa only [mul_one, one_mul] using mul_le_mul_of_nonneg_right hn' hu

private lemma p33_gamma_step (u : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (hv : P33GammaValid u (n + 1)) :
    (1 + u) * p33Gamma u n + u ≤ p33Gamma u (n + 1) := by
  unfold P33GammaValid at hv
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
  rw [hcast] at hv
  have hdn : 0 < 1 - (n : ℝ) * u := by nlinarith
  have hdnext : 0 < 1 - ((n : ℝ) + 1) * u := sub_pos.mpr hv
  unfold p33Gamma
  rw [hcast]
  have heq :
      (1 + u) * ((n : ℝ) * u / (1 - (n : ℝ) * u)) + u =
        (((n : ℝ) + 1) * u) / (1 - (n : ℝ) * u) := by
    have hdn' : 1 - u * (n : ℝ) ≠ 0 := by nlinarith
    field_simp [hdn']
    ring
  rw [heq, div_le_div_iff₀ hdn hdnext]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) hu)
  nlinarith

private lemma p33_rounded_row_succ
    (fp : P33FPModel) (n : ℕ) (a x : Fin (n + 1) → ℝ) :
    p33RoundedSparseRowProduct fp (n + 1) a x =
      fp.fl_add
        (p33RoundedSparseRowProduct fp n
          (fun i ↦ a i.castSucc) (fun i ↦ x i.castSucc))
        (fp.fl_mul (a (Fin.last n)) (x (Fin.last n))) := by
  cases n with
  | zero =>
      simp [p33RoundedSparseRowProduct, fp.fl_add_zero]
  | succ n =>
      simp only [p33RoundedSparseRowProduct]
      rw [Fin.foldl_succ_last]
      congr 1

private lemma p33_rounded_row_error
    (fp : P33FPModel) (s : ℕ) (a x : Fin s → ℝ)
    (hv : P33GammaValid fp.u s) :
    |p33RoundedSparseRowProduct fp s a x - ∑ i : Fin s, a i * x i| ≤
      p33Gamma fp.u s * ∑ i : Fin s, |a i| * |x i| := by
  induction s with
  | zero =>
      simp [p33RoundedSparseRowProduct, p33Gamma]
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        obtain ⟨d, hd, hmul⟩ := fp.model_mul (a 0) (x 0)
        have hu_gamma : fp.u ≤ p33Gamma fp.u 1 :=
          p33_u_le_gamma fp.u 1 fp.u_nonneg (by omega) hv
        rw [p33_rounded_row_succ]
        simp only [p33RoundedSparseRowProduct, fp.fl_add_zero]
        simp only [Fin.last_zero]
        rw [hmul]
        simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty,
          add_zero, Fin.last_zero, Fin.isValue, abs_mul]
        have hax : 0 ≤ |a 0| * |x 0| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
        calc
          |a 0 * x 0 * (1 + d) - a 0 * x 0| =
              (|a 0| * |x 0|) * |d| := by rw [show a 0 * x 0 * (1 + d) - a 0 * x 0 =
                (a 0 * x 0) * d by ring, abs_mul, abs_mul]
          _ ≤ (|a 0| * |x 0|) * fp.u :=
            mul_le_mul_of_nonneg_left hd hax
          _ ≤ (|a 0| * |x 0|) * p33Gamma fp.u 1 :=
            mul_le_mul_of_nonneg_left hu_gamma hax
          _ = p33Gamma fp.u 1 * (|a 0| * |x 0|) := by ring
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        let ap : Fin n → ℝ := fun i ↦ a i.castSucc
        let xp : Fin n → ℝ := fun i ↦ x i.castSucc
        let R : ℝ := p33RoundedSparseRowProduct fp n ap xp
        let S : ℝ := ∑ i : Fin n, ap i * xp i
        let A : ℝ := ∑ i : Fin n, |ap i| * |xp i|
        let y : ℝ := a (Fin.last n) * x (Fin.last n)
        let Y : ℝ := |a (Fin.last n)| * |x (Fin.last n)|
        let q : ℝ := fp.fl_mul (a (Fin.last n)) (x (Fin.last n))
        have hvn : P33GammaValid fp.u n := by
          unfold P33GammaValid at hv ⊢
          have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
          rw [hcast] at hv
          nlinarith [fp.u_nonneg]
        have herr : |R - S| ≤ p33Gamma fp.u n * A := by
          simpa [R, S, A, ap, xp] using ih ap xp hvn
        have hA : 0 ≤ A := by
          dsimp [A]
          positivity
        have hY : 0 ≤ Y := by
          dsimp [Y]
          positivity
        have hS : |S| ≤ A := by
          dsimp [S, A]
          simpa only [abs_mul] using
            (Finset.abs_sum_le_sum_abs (fun i : Fin n ↦ ap i * xp i) Finset.univ)
        have hyabs : |y| = Y := by simp [y, Y, abs_mul]
        obtain ⟨dm, hdm, hmul⟩ :=
          fp.model_mul (a (Fin.last n)) (x (Fin.last n))
        obtain ⟨da, hda, hadd⟩ := fp.model_add R q
        have hq : |q - y| ≤ fp.u * Y := by
          have hmul' : q = y * (1 + dm) := by simpa [q, y] using hmul
          calc
            |q - y| = |y * dm| := by
              rw [hmul']
              congr 1
              ring
            _ = |y| * |dm| := abs_mul _ _
            _ ≤ Y * fp.u := by
              rw [hyabs]
              exact mul_le_mul_of_nonneg_left hdm hY
            _ = fp.u * Y := by ring
        have hfac : |1 + da| ≤ 1 + fp.u := by
          calc
            |1 + da| ≤ |(1 : ℝ)| + |da| := abs_add_le _ _
            _ ≤ 1 + fp.u := by simpa using add_le_add_left hda 1
        have hfac0 : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
        have hSy : |S + y| ≤ A + Y := by
          calc
            |S + y| ≤ |S| + |y| := abs_add_le _ _
            _ ≤ A + Y := by rw [hyabs]; linarith
        have hgamma0 : 0 ≤ p33Gamma fp.u n :=
          p33_gamma_nonneg fp.u n fp.u_nonneg hvn
        have hugamma : fp.u ≤ p33Gamma fp.u n :=
          p33_u_le_gamma fp.u n fp.u_nonneg hn1 hvn
        have hstep :
            (1 + fp.u) * p33Gamma fp.u n + fp.u ≤
              p33Gamma fp.u (n + 1) :=
          p33_gamma_step fp.u n fp.u_nonneg hv
        have hsum : (∑ i : Fin (n + 1), a i * x i) = S + y := by
          rw [Fin.sum_univ_castSucc]
        have habssum : (∑ i : Fin (n + 1), |a i| * |x i|) = A + Y := by
          rw [Fin.sum_univ_castSucc]
        rw [p33_rounded_row_succ, hsum, habssum]
        change |fp.fl_add R q - (S + y)| ≤
          p33Gamma fp.u (n + 1) * (A + Y)
        rw [hadd]
        have hdecomp :
            (R + q) * (1 + da) - (S + y) =
              (R - S) * (1 + da) + (q - y) * (1 + da) + (S + y) * da := by
          ring
        rw [hdecomp]
        calc
          |(R - S) * (1 + da) + (q - y) * (1 + da) + (S + y) * da| ≤
              |(R - S) * (1 + da)| + |(q - y) * (1 + da)| +
                |(S + y) * da| := abs_add_three _ _ _
          _ = |R - S| * |1 + da| + |q - y| * |1 + da| +
                |S + y| * |da| := by rw [abs_mul, abs_mul, abs_mul]
          _ ≤ (p33Gamma fp.u n * A) * (1 + fp.u) +
                (fp.u * Y) * (1 + fp.u) + (A + Y) * fp.u := by
            gcongr
            exact mul_nonneg fp.u_nonneg hY
          _ ≤ ((1 + fp.u) * p33Gamma fp.u n + fp.u) * (A + Y) := by
            have haux : 0 ≤
                (p33Gamma fp.u n - fp.u) * (1 + fp.u) * Y :=
              mul_nonneg
                (mul_nonneg (sub_nonneg.mpr hugamma) hfac0) hY
            nlinarith
          _ ≤ p33Gamma fp.u (n + 1) * (A + Y) := by
            exact mul_le_mul_of_nonneg_right hstep (add_nonneg hA hY)

/-- P33-T1: the sparse-row computed-residual error bound in Section 2.2. -/
theorem p33_t1_sparse_residual_error
    (fp : P33FPModel) (s : ℕ) (a x : Fin s → ℝ) (b : ℝ)
    (hvalid : P33GammaValid fp.u (s + 1)) :
    |p33RoundedResidual fp s a x b - p33ExactResidual s a x b| ≤
      p33ResidualErrorMajorant fp s a x b := by
  -- PROOF_START P33-T1-H001
  let R : ℝ := p33RoundedSparseRowProduct fp s a x
  let S : ℝ := ∑ i : Fin s, a i * x i
  let A : ℝ := ∑ i : Fin s, |a i| * |x i|
  have hvalid_s : P33GammaValid fp.u s := by
    unfold P33GammaValid at hvalid ⊢
    have hcast : ((s + 1 : ℕ) : ℝ) = (s : ℝ) + 1 := by norm_num
    rw [hcast] at hvalid
    nlinarith [fp.u_nonneg]
  have herr : |R - S| ≤ p33Gamma fp.u s * A := by
    simpa [R, S, A] using p33_rounded_row_error fp s a x hvalid_s
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hS : |S| ≤ A := by
    dsimp [S, A]
    simpa only [abs_mul] using
      (Finset.abs_sum_le_sum_abs (fun i : Fin s ↦ a i * x i) Finset.univ)
  have hgamma_s : 0 ≤ p33Gamma fp.u s :=
    p33_gamma_nonneg fp.u s fp.u_nonneg hvalid_s
  have hstep :
      (1 + fp.u) * p33Gamma fp.u s + fp.u ≤ p33Gamma fp.u (s + 1) :=
    p33_gamma_step fp.u s fp.u_nonneg hvalid
  have hu_next : fp.u ≤ p33Gamma fp.u (s + 1) :=
    p33_u_le_gamma fp.u (s + 1) fp.u_nonneg (by omega) hvalid
  obtain ⟨d, hd, hsub⟩ := fp.model_sub b R
  have hfac : |1 + d| ≤ 1 + fp.u := by
    calc
      |1 + d| ≤ |(1 : ℝ)| + |d| := abs_add_le _ _
      _ ≤ 1 + fp.u := by simpa using add_le_add_left hd 1
  have hfac0 : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
  have hbS : |b - S| ≤ |b| + A := by
    calc
      |b - S| ≤ |b| + |S| := abs_sub _ _
      _ ≤ |b| + A := by gcongr
  unfold p33RoundedResidual p33ExactResidual p33ResidualErrorMajorant
  change |fp.fl_sub b R - (b - S)| ≤
    p33Gamma fp.u (s + 1) * (|b| + A)
  rw [hsub]
  have hdecomp :
      (b - R) * (1 + d) - (b - S) =
        (S - R) * (1 + d) + (b - S) * d := by
    ring
  rw [hdecomp]
  calc
    |(S - R) * (1 + d) + (b - S) * d| ≤
        |(S - R) * (1 + d)| + |(b - S) * d| := abs_add_le _ _
    _ = |S - R| * |1 + d| + |b - S| * |d| := by
      rw [abs_mul, abs_mul]
    _ ≤ (p33Gamma fp.u s * A) * (1 + fp.u) +
          (|b| + A) * fp.u := by
      have herr' : |S - R| ≤ p33Gamma fp.u s * A := by
        simpa [abs_sub_comm] using herr
      gcongr
    _ = ((1 + fp.u) * p33Gamma fp.u s + fp.u) * A + fp.u * |b| := by
      ring
    _ ≤ p33Gamma fp.u (s + 1) * A +
          p33Gamma fp.u (s + 1) * |b| := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hstep hA)
        (mul_le_mul_of_nonneg_right hu_next (abs_nonneg b))
    _ = p33Gamma fp.u (s + 1) * (|b| + A) := by ring

end HighamBench
