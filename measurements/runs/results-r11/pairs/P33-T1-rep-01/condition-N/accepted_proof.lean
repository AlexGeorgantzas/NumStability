import HighamBench.P33Definitions

namespace HighamBench

open scoped BigOperators

private lemma gamma_nonneg (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (h : P33GammaValid u n) : 0 ≤ p33Gamma u n := by
  unfold P33GammaValid at h
  rw [p33Gamma]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (le_of_lt (sub_pos.mpr h))

private lemma gamma_step (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (h : P33GammaValid u (n + 1)) :
    (1 + u) * p33Gamma u n + u ≤ p33Gamma u (n + 1) := by
  unfold P33GammaValid at h
  have hn : (n : ℝ) * u < 1 := by
    push_cast at h
    nlinarith [mul_nonneg (Nat.cast_nonneg n) hu]
  have hdn : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hn
  have hds : 0 < 1 - ((n + 1 : ℕ) : ℝ) * u := sub_pos.mpr h
  rw [p33Gamma, p33Gamma]
  have hrearrange :
      (1 + u) * ((n : ℝ) * u / (1 - (n : ℝ) * u)) + u =
        ((1 + u) * ((n : ℝ) * u) + u * (1 - (n : ℝ) * u)) /
          (1 - (n : ℝ) * u) := by
    rw [add_div, mul_div_cancel_right₀ u hdn.ne']
    simp only [div_eq_mul_inv]
    ring
  rw [hrearrange]
  apply (div_le_div_iff₀ hdn hds).2
  push_cast
  nlinarith [sq_nonneg u]

private lemma u_le_gamma (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (hn : 1 ≤ n) (h : P33GammaValid u n) : u ≤ p33Gamma u n := by
  unfold P33GammaValid at h
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [p33Gamma, le_div_iff₀ (sub_pos.mpr h)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hnreal) hu, sq_nonneg u]

private lemma two_mul_errors_le_gamma_succ (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (hn : 1 ≤ n) (h : P33GammaValid u (n + 1)) :
    u * (2 + u) ≤ p33Gamma u (n + 1) := by
  have hgn : u ≤ p33Gamma u n := by
    apply u_le_gamma u n hu hn
    unfold P33GammaValid at h ⊢
    push_cast at h
    nlinarith
  calc
    u * (2 + u) ≤ (1 + u) * p33Gamma u n + u := by
      have hu1 : 0 ≤ 1 + u := by positivity
      have hmul := mul_le_mul_of_nonneg_left hgn hu1
      nlinarith
    _ ≤ p33Gamma u (n + 1) := gamma_step u n hu h

private lemma rounded_sparse_succ_succ
    (fp : P33FPModel) (n : ℕ) (a x : Fin (n + 2) → ℝ) :
    p33RoundedSparseRowProduct fp (n + 2) a x =
      fp.fl_add
        (p33RoundedSparseRowProduct fp (n + 1)
          (fun j => a j.castSucc) (fun j => x j.castSucc))
        (fp.fl_mul (a (Fin.last (n + 1))) (x (Fin.last (n + 1)))) := by
  simp only [p33RoundedSparseRowProduct, Fin.foldl_succ_last]
  congr 2

private lemma rounded_add_mul_error
    (u g g' q T A y dm da : ℝ)
    (hu : 0 ≤ u) (hA : 0 ≤ A)
    (hdm : |dm| ≤ u) (hda : |da| ≤ u)
    (hq : |q - T| ≤ g * A) (hT : |T| ≤ A)
    (hstep : (1 + u) * g + u ≤ g')
    (htwo : u * (2 + u) ≤ g') :
    |(q + y * (1 + dm)) * (1 + da) - (T + y)| ≤ g' * (A + |y|) := by
  have h_one_da : |1 + da| ≤ 1 + u := by
    calc
      |1 + da| ≤ |(1 : ℝ)| + |da| := abs_add_le _ _
      _ ≤ 1 + u := by norm_num; linarith
  have hgA : 0 ≤ g * A := le_trans (abs_nonneg _) hq
  have hfirst : |q - T| * |1 + da| ≤ (g * A) * (1 + u) :=
    mul_le_mul hq h_one_da (abs_nonneg _) hgA
  have hsecond : |T| * |da| ≤ A * u :=
    mul_le_mul hT hda (abs_nonneg _) hA
  have hdmterm : |dm| * |1 + da| ≤ u * (1 + u) :=
    mul_le_mul hdm h_one_da (abs_nonneg _) hu
  have hinner : |dm * (1 + da) + da| ≤ u * (1 + u) + u := by
    calc
      |dm * (1 + da) + da| ≤ |dm * (1 + da)| + |da| := abs_add_le _ _
      _ = |dm| * |1 + da| + |da| := by rw [abs_mul]
      _ ≤ u * (1 + u) + u := add_le_add hdmterm hda
  have hthird : |y| * |dm * (1 + da) + da| ≤ |y| * (u * (1 + u) + u) :=
    mul_le_mul_of_nonneg_left hinner (abs_nonneg _)
  have hraw :
      |(q + y * (1 + dm)) * (1 + da) - (T + y)| ≤
        (g * A) * (1 + u) + A * u + |y| * (u * (1 + u) + u) := by
    rw [show (q + y * (1 + dm)) * (1 + da) - (T + y) =
        (q - T) * (1 + da) + T * da + y * (dm * (1 + da) + da) by ring]
    calc
      |(q - T) * (1 + da) + T * da + y * (dm * (1 + da) + da)| ≤
          |(q - T) * (1 + da) + T * da| + |y * (dm * (1 + da) + da)| :=
        abs_add_le _ _
      _ ≤ (|(q - T) * (1 + da)| + |T * da|) +
          |y * (dm * (1 + da) + da)| := by
        gcongr
        exact abs_add_le _ _
      _ = (|q - T| * |1 + da| + |T| * |da|) +
          |y| * |dm * (1 + da) + da| := by simp only [abs_mul]
      _ ≤ ((g * A) * (1 + u) + A * u) +
          |y| * (u * (1 + u) + u) := add_le_add (add_le_add hfirst hsecond) hthird
  have hAcoeff : (g * A) * (1 + u) + A * u ≤ g' * A := by
    have hm := mul_le_mul_of_nonneg_right hstep hA
    nlinarith
  have hycoeff : |y| * (u * (1 + u) + u) ≤ g' * |y| := by
    have hm := mul_le_mul_of_nonneg_right htwo (abs_nonneg y)
    nlinarith
  calc
    |(q + y * (1 + dm)) * (1 + da) - (T + y)| ≤
        (g * A) * (1 + u) + A * u + |y| * (u * (1 + u) + u) := hraw
    _ ≤ g' * A + g' * |y| := add_le_add hAcoeff hycoeff
    _ = g' * (A + |y|) := by ring

private lemma rounded_sparse_error
    (fp : P33FPModel) (s : ℕ) (a x : Fin s → ℝ)
    (hvalid : P33GammaValid fp.u s) :
    |p33RoundedSparseRowProduct fp s a x - ∑ j : Fin s, a j * x j| ≤
      p33Gamma fp.u s * ∑ j : Fin s, |a j| * |x j| := by
  induction s using Nat.twoStepInduction with
  | zero =>
      simp [p33RoundedSparseRowProduct, p33Gamma]
  | one =>
      obtain ⟨dm, hdm, hm⟩ := fp.model_mul (a 0) (x 0)
      have hgu : fp.u ≤ p33Gamma fp.u 1 :=
        u_le_gamma fp.u 1 fp.u_nonneg (by omega) hvalid
      simp only [p33RoundedSparseRowProduct, Fin.foldl_zero, Fin.sum_univ_one]
      rw [hm]
      calc
        |a 0 * x 0 * (1 + dm) - a 0 * x 0| = |a 0 * x 0| * |dm| := by
          rw [show a 0 * x 0 * (1 + dm) - a 0 * x 0 = (a 0 * x 0) * dm by ring,
            abs_mul]
        _ ≤ |a 0 * x 0| * fp.u :=
          mul_le_mul_of_nonneg_left hdm (abs_nonneg _)
        _ = fp.u * (|a 0| * |x 0|) := by rw [abs_mul]; ring
        _ ≤ p33Gamma fp.u 1 * (|a 0| * |x 0|) :=
          mul_le_mul_of_nonneg_right hgu (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  | more n ih_n ih_succ =>
      let ap : Fin (n + 1) → ℝ := fun j => a j.castSucc
      let xp : Fin (n + 1) → ℝ := fun j => x j.castSucc
      let q := p33RoundedSparseRowProduct fp (n + 1) ap xp
      let T := ∑ j : Fin (n + 1), ap j * xp j
      let A := ∑ j : Fin (n + 1), |ap j| * |xp j|
      let k : Fin (n + 2) := Fin.last (n + 1)
      let y := a k * x k
      have hpvalid : P33GammaValid fp.u (n + 1) := by
        unfold P33GammaValid at hvalid ⊢
        push_cast at hvalid ⊢
        nlinarith [fp.u_nonneg]
      have hq : |q - T| ≤ p33Gamma fp.u (n + 1) * A := by
        exact ih_succ ap xp hpvalid
      have hA : 0 ≤ A := by
        exact Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
      have hT : |T| ≤ A := by
        calc
          |T| ≤ ∑ j : Fin (n + 1), |ap j * xp j| := by
            exact Finset.abs_sum_le_sum_abs (fun j : Fin (n + 1) => ap j * xp j) Finset.univ
          _ = A := by simp only [A, abs_mul]
      obtain ⟨dm, hdm, hm⟩ := fp.model_mul (a k) (x k)
      obtain ⟨da, hda, ha⟩ := fp.model_add q (fp.fl_mul (a k) (x k))
      have hstep :
          (1 + fp.u) * p33Gamma fp.u (n + 1) + fp.u ≤
            p33Gamma fp.u (n + 2) := by
        simpa only [Nat.add_assoc, Nat.reduceAdd] using
          gamma_step fp.u (n + 1) fp.u_nonneg hvalid
      have htwo : fp.u * (2 + fp.u) ≤ p33Gamma fp.u (n + 2) := by
        simpa only [Nat.add_assoc, Nat.reduceAdd] using
          two_mul_errors_le_gamma_succ fp.u (n + 1) fp.u_nonneg (by omega) hvalid
      rw [rounded_sparse_succ_succ]
      change |fp.fl_add q (fp.fl_mul (a k) (x k)) -
          ∑ j : Fin (n + 2), a j * x j| ≤
        p33Gamma fp.u (n + 2) * ∑ j : Fin (n + 2), |a j| * |x j|
      rw [ha, hm]
      rw [Fin.sum_univ_castSucc (n := n + 1) (f := fun j => a j * x j)]
      rw [Fin.sum_univ_castSucc (n := n + 1) (f := fun j => |a j| * |x j|)]
      change |(q + y * (1 + dm)) * (1 + da) - (T + y)| ≤
        p33Gamma fp.u (n + 2) * (A + |a k| * |x k|)
      simpa only [y, abs_mul] using
        rounded_add_mul_error fp.u (p33Gamma fp.u (n + 1))
          (p33Gamma fp.u (n + 2)) q T A y dm da fp.u_nonneg hA hdm hda hq hT hstep htwo

private lemma rounded_sub_error
    (u g g' q T A b d : ℝ)
    (hu : 0 ≤ u) (hA : 0 ≤ A) (hd : |d| ≤ u)
    (hq : |q - T| ≤ g * A) (hT : |T| ≤ A)
    (hstep : (1 + u) * g + u ≤ g') (hug : u ≤ g') :
    |(b - q) * (1 + d) - (b - T)| ≤ g' * (|b| + A) := by
  have h_one_d : |1 + d| ≤ 1 + u := by
    calc
      |1 + d| ≤ |(1 : ℝ)| + |d| := abs_add_le _ _
      _ ≤ 1 + u := by norm_num; linarith
  have hgA : 0 ≤ g * A := le_trans (abs_nonneg _) hq
  have hfirst : |q - T| * |1 + d| ≤ (g * A) * (1 + u) :=
    mul_le_mul hq h_one_d (abs_nonneg _) hgA
  have hbT : |b - T| ≤ |b| + A := by
    calc
      |b - T| = |b + -T| := by ring
      _ ≤ |b| + |-T| := abs_add_le _ _
      _ = |b| + |T| := by rw [abs_neg]
      _ ≤ |b| + A := add_le_add (le_refl _) hT
  have hsecond : |b - T| * |d| ≤ (|b| + A) * u :=
    mul_le_mul hbT hd (abs_nonneg _) (by positivity)
  have hraw :
      |(b - q) * (1 + d) - (b - T)| ≤
        (g * A) * (1 + u) + (|b| + A) * u := by
    rw [show (b - q) * (1 + d) - (b - T) =
        -(q - T) * (1 + d) + (b - T) * d by ring]
    calc
      |-(q - T) * (1 + d) + (b - T) * d| ≤
          |-(q - T) * (1 + d)| + |(b - T) * d| := abs_add_le _ _
      _ = |q - T| * |1 + d| + |b - T| * |d| := by
        simp only [abs_mul, abs_neg]
      _ ≤ (g * A) * (1 + u) + (|b| + A) * u := add_le_add hfirst hsecond
  have hAcoeff : (g * A) * (1 + u) + A * u ≤ g' * A := by
    have hm := mul_le_mul_of_nonneg_right hstep hA
    nlinarith
  have hbcoeff : |b| * u ≤ |b| * g' :=
    mul_le_mul_of_nonneg_left hug (abs_nonneg _)
  calc
    |(b - q) * (1 + d) - (b - T)| ≤
        (g * A) * (1 + u) + (|b| + A) * u := hraw
    _ ≤ |b| * g' + g' * A := by nlinarith
    _ = g' * (|b| + A) := by ring

/-- P33-T1: the sparse-row computed-residual error bound in Section 2.2. -/
theorem p33_t1_sparse_residual_error
    (fp : P33FPModel) (s : ℕ) (a x : Fin s → ℝ) (b : ℝ)
    (hvalid : P33GammaValid fp.u (s + 1)) :
    |p33RoundedResidual fp s a x b - p33ExactResidual s a x b| ≤
      p33ResidualErrorMajorant fp s a x b := by
  -- PROOF_START P33-T1-H001
  let q := p33RoundedSparseRowProduct fp s a x
  let T := ∑ j : Fin s, a j * x j
  let A := ∑ j : Fin s, |a j| * |x j|
  have hsvalid : P33GammaValid fp.u s := by
    unfold P33GammaValid at hvalid ⊢
    push_cast at hvalid
    nlinarith [fp.u_nonneg]
  have hq : |q - T| ≤ p33Gamma fp.u s * A :=
    rounded_sparse_error fp s a x hsvalid
  have hA : 0 ≤ A := by
    exact Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hT : |T| ≤ A := by
    calc
      |T| ≤ ∑ j : Fin s, |a j * x j| := by
        exact Finset.abs_sum_le_sum_abs (fun j : Fin s => a j * x j) Finset.univ
      _ = A := by simp only [A, abs_mul]
  obtain ⟨d, hd, hsub⟩ := fp.model_sub b q
  have hstep :
      (1 + fp.u) * p33Gamma fp.u s + fp.u ≤ p33Gamma fp.u (s + 1) :=
    gamma_step fp.u s fp.u_nonneg hvalid
  have hug : fp.u ≤ p33Gamma fp.u (s + 1) :=
    u_le_gamma fp.u (s + 1) fp.u_nonneg (by omega) hvalid
  rw [p33RoundedResidual, p33ExactResidual, p33ResidualErrorMajorant]
  change |fp.fl_sub b q - (b - T)| ≤ p33Gamma fp.u (s + 1) * (|b| + A)
  rw [hsub]
  exact rounded_sub_error fp.u (p33Gamma fp.u s) (p33Gamma fp.u (s + 1))
    q T A b d fp.u_nonneg hA hd hq hT hstep hug

end HighamBench
