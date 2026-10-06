import HighamBench.P28Definitions

namespace HighamBench

private lemma p28_gamma_nonneg {u : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hvalid : P28GammaValid u n) :
    0 ≤ p28Gamma u n := by
  unfold p28Gamma P28GammaValid at *
  have hden : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hvalid
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) hden.le

private lemma p28_gamma_step_old {u : ℝ} (m : ℕ)
    (hu : 0 ≤ u) (hvalid : P28GammaValid u (m + 1)) :
    (1 + u) * p28Gamma u m + u ≤ p28Gamma u (m + 1) := by
  unfold p28Gamma P28GammaValid at *
  have hm : (m : ℝ) * u ≤ ((m + 1 : ℕ) : ℝ) * u := by
    gcongr
    norm_num
  have hdenm : 0 < 1 - (m : ℝ) * u := sub_pos.mpr (lt_of_le_of_lt hm hvalid)
  have hdens : 0 < 1 - ((m + 1 : ℕ) : ℝ) * u := sub_pos.mpr hvalid
  have heq :
      (1 + u) * ((m : ℝ) * u / (1 - (m : ℝ) * u)) + u =
        ((m + 1 : ℕ) : ℝ) * u / (1 - (m : ℝ) * u) := by
    have hdenm' : 1 - u * (m : ℝ) ≠ 0 := by nlinarith
    field_simp [ne_of_gt hdenm, hdenm']
    push_cast
    ring
  rw [heq]
  apply div_le_div_of_nonneg_left (mul_nonneg (by positivity) hu) hdens
  push_cast
  nlinarith

private lemma p28_gamma_step_new {u : ℝ} (m : ℕ)
    (hu : 0 ≤ u) (hm : 1 ≤ m) (hvalid : P28GammaValid u (m + 1)) :
    u * (2 + u) ≤ p28Gamma u (m + 1) := by
  unfold p28Gamma P28GammaValid at *
  have hdens : 0 < 1 - ((m + 1 : ℕ) : ℝ) * u := sub_pos.mpr hvalid
  apply (le_div_iff₀ hdens).2
  have hm2 : (2 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ hm
  have hcoef : 0 ≤ (2 * ((m + 1 : ℕ) : ℝ) - 1) * u :=
    mul_nonneg (by nlinarith) hu
  have hsq : 0 ≤ ((m + 1 : ℕ) : ℝ) * u ^ 2 := by positivity
  have hbracket :
      0 ≤ ((m + 1 : ℕ) : ℝ) - (2 + u) * (1 - ((m + 1 : ℕ) : ℝ) * u) := by
    nlinarith
  nlinarith [mul_nonneg hu hbracket]

private lemma p28_fl_mul_error (fp : P28FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * |x * y| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul x y
  rw [hfl]
  have heq : (x * y) * (1 + δ) - x * y = (x * y) * δ := by ring
  rw [heq, abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left hδ (abs_nonneg (x * y))]

private lemma p28_fl_add_error (fp : P28FPModel) (a b A B : ℝ) :
    |fp.fl_add a b - (A + B)| ≤
      (1 + fp.u) * (|a - A| + |b - B|) +
        fp.u * (|A| + |B|) := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add a b
  rw [hfl]
  have hid :
      (a + b) * (1 + δ) - (A + B) =
        ((a - A) + (b - B)) + δ * (a + b) := by ring
  rw [hid]
  have h₁ := abs_add_le ((a - A) + (b - B)) (δ * (a + b))
  have h₂ := abs_add_le (a - A) (b - B)
  have ha := abs_add_le (a - A) A
  have hb := abs_add_le (b - B) B
  have ha' : |a| ≤ |a - A| + |A| := by
    convert ha using 1 <;> ring
  have hb' : |b| ≤ |b - B| + |B| := by
    convert hb using 1 <;> ring
  rw [abs_mul] at h₁
  have hab := abs_add_le a b
  have hδmul : |δ| * |a + b| ≤ fp.u * (|a| + |b|) := by
    exact mul_le_mul hδ hab (abs_nonneg _) fp.u_nonneg
  have hab' :
      |a| + |b| ≤ (|a - A| + |b - B|) + (|A| + |B|) := by
    linarith
  have huab := mul_le_mul_of_nonneg_left hab' fp.u_nonneg
  calc
    |(a - A) + (b - B) + δ * (a + b)|
        ≤ |(a - A) + (b - B)| + |δ| * |a + b| := h₁
    _ ≤ (|a - A| + |b - B|) + fp.u * (|a| + |b|) :=
      add_le_add h₂ hδmul
    _ ≤ (|a - A| + |b - B|) +
        fp.u * ((|a - A| + |b - B|) + (|A| + |B|)) :=
      by linarith
    _ = (1 + fp.u) * (|a - A| + |b - B|) +
        fp.u * (|A| + |B|) := by ring

private lemma p28_rounded_dot_succ (fp : P28FPModel) (m : ℕ)
    (x y : Fin (m + 1) → ℝ) :
    p28RoundedDotProduct fp (m + 1) x y =
      fp.fl_add
        (p28RoundedDotProduct fp m (fun i => x i.castSucc) (fun i => y i.castSucc))
        (fp.fl_mul (x (Fin.last m)) (y (Fin.last m))) := by
  cases m with
  | zero =>
      simpa [p28RoundedDotProduct] using
        (fp.fl_add_zero (fp.fl_mul (x 0) (y 0))).symm
  | succ m =>
      simp only [p28RoundedDotProduct]
      rw [Fin.foldl_succ_last]
      rfl

private lemma p28_rounded_dot_error (fp : P28FPModel) :
    ∀ (n : ℕ) (x y : Fin n → ℝ), P28GammaValid fp.u n →
      |p28RoundedDotProduct fp n x y - ∑ k, x k * y k| ≤
        p28Gamma fp.u n * ∑ k, |x k| * |y k| := by
  intro n
  induction n with
  | zero =>
      intro x y hvalid
      simp [p28RoundedDotProduct, p28Gamma]
  | succ n ih =>
      cases n with
      | zero =>
          intro x y hvalid
          have hmul := p28_fl_mul_error fp (x 0) (y 0)
          have hgamma := p28_gamma_step_old 0 fp.u_nonneg hvalid
          have hgamma' : fp.u ≤ p28Gamma fp.u 1 := by
            simpa [p28Gamma] using hgamma
          have hab : 0 ≤ |x 0| * |y 0| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
          simp only [p28RoundedDotProduct, Fin.sum_univ_succ, Finset.univ_eq_empty,
            Finset.sum_empty, add_zero]
          rw [abs_mul] at hmul
          simpa [p28Gamma] using
            (hmul.trans (mul_le_mul_of_nonneg_right hgamma' hab))
      | succ m =>
          intro x y hvalid
          let x' : Fin (m + 1) → ℝ := fun i => x i.castSucc
          let y' : Fin (m + 1) → ℝ := fun i => y i.castSucc
          let A : ℝ := ∑ k, x' k * y' k
          let S : ℝ := ∑ k, |x' k| * |y' k|
          let B : ℝ := x (Fin.last (m + 1)) * y (Fin.last (m + 1))
          let T : ℝ := |x (Fin.last (m + 1))| * |y (Fin.last (m + 1))|
          have hvalid' : P28GammaValid fp.u (m + 1) := by
            unfold P28GammaValid at *
            have hcast : ((m + 1 : ℕ) : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by norm_num
            exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcast fp.u_nonneg) hvalid
          have hold :
              |p28RoundedDotProduct fp (m + 1) x' y' - A| ≤
                p28Gamma fp.u (m + 1) * S := by
            exact ih x' y' hvalid'
          have hmul :
              |fp.fl_mul (x (Fin.last (m + 1))) (y (Fin.last (m + 1))) - B| ≤
                fp.u * T := by
            simpa [B, T, abs_mul] using
              p28_fl_mul_error fp (x (Fin.last (m + 1))) (y (Fin.last (m + 1)))
          have hA : |A| ≤ S := by
            dsimp [A, S, x', y']
            calc
              |∑ k : Fin (m + 1), x k.castSucc * y k.castSucc| ≤
                  ∑ k : Fin (m + 1), |x k.castSucc * y k.castSucc| :=
                Finset.abs_sum_le_sum_abs _ _
              _ = ∑ k : Fin (m + 1), |x k.castSucc| * |y k.castSucc| := by
                apply Finset.sum_congr rfl
                intro k hk
                exact abs_mul _ _
          have hS : 0 ≤ S := by
            dsimp [S]
            positivity
          have hT : 0 ≤ T := by
            dsimp [T]
            positivity
          have hgamma : 0 ≤ p28Gamma fp.u (m + 1) :=
            p28_gamma_nonneg fp.u_nonneg hvalid'
          have hadd := p28_fl_add_error fp
            (p28RoundedDotProduct fp (m + 1) x' y')
            (fp.fl_mul (x (Fin.last (m + 1))) (y (Fin.last (m + 1)))) A B
          have hcoarse :
              |fp.fl_add (p28RoundedDotProduct fp (m + 1) x' y')
                    (fp.fl_mul (x (Fin.last (m + 1))) (y (Fin.last (m + 1)))) -
                  (A + B)| ≤
                ((1 + fp.u) * p28Gamma fp.u (m + 1) + fp.u) * S +
                  (fp.u * (2 + fp.u)) * T := by
            have hu1 : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
            have h₁ := add_le_add hold hmul
            have h₂ := mul_le_mul_of_nonneg_left h₁ hu1
            have hBT : |B| = T := by simp [B, T, abs_mul]
            have hAB : |A| + |B| ≤ S + T := by
              rw [hBT]
              exact add_le_add hA (le_refl T)
            calc
              |fp.fl_add (p28RoundedDotProduct fp (m + 1) x' y')
                    (fp.fl_mul (x (Fin.last (m + 1))) (y (Fin.last (m + 1)))) -
                  (A + B)|
                  ≤ (1 + fp.u) *
                      (|p28RoundedDotProduct fp (m + 1) x' y' - A| +
                        |fp.fl_mul (x (Fin.last (m + 1)))
                          (y (Fin.last (m + 1))) - B|) +
                      fp.u * (|A| + |B|) := hadd
              _ ≤ (1 + fp.u) *
                      (p28Gamma fp.u (m + 1) * S + fp.u * T) +
                    fp.u * (S + T) := by
                exact add_le_add h₂ (mul_le_mul_of_nonneg_left hAB fp.u_nonneg)
              _ = ((1 + fp.u) * p28Gamma fp.u (m + 1) + fp.u) * S +
                    (fp.u * (2 + fp.u)) * T := by ring
          have hstep₁ := p28_gamma_step_old (m + 1) fp.u_nonneg hvalid
          have hstep₂ := p28_gamma_step_new (m + 1) fp.u_nonneg (by omega) hvalid
          have hfinal :
              ((1 + fp.u) * p28Gamma fp.u (m + 1) + fp.u) * S +
                  (fp.u * (2 + fp.u)) * T ≤
                p28Gamma fp.u (m + 2) * (S + T) := by
            nlinarith [mul_le_mul_of_nonneg_right hstep₁ hS,
              mul_le_mul_of_nonneg_right hstep₂ hT]
          have hExact : (∑ k, x k * y k) = A + B := by
            rw [Fin.sum_univ_castSucc]
          have hAbs : (∑ k, |x k| * |y k|) = S + T := by
            rw [Fin.sum_univ_castSucc]
          rw [p28_rounded_dot_succ, hExact, hAbs]
          change
            |fp.fl_add (p28RoundedDotProduct fp (m + 1) x' y')
                (fp.fl_mul (x (Fin.last (m + 1))) (y (Fin.last (m + 1)))) -
              (A + B)| ≤
              p28Gamma fp.u (m + 2) * (S + T)
          exact hcoarse.trans hfinal

/-- P28-T1: the forward-error term from forming `XXᵀX` in equation (6.6). -/
theorem p28_t1_newton_schulz_triple_product_error
    (fp : P28FPModel) (n : ℕ) (X : P28RealMatrix n)
    (hvalid : P28GammaValid fp.u n) :
    ∀ i j,
      |p28RoundedGramTriple fp X i j - p28ExactGramTriple X i j| ≤
        p28GramTripleErrorMajorant fp X i j := by
  -- PROOF_START P28-T1-H001
  intro i j
  let R : P28RealMatrix n := p28RoundedMatMul fp X (p28Transpose X)
  have houter :
      |p28RoundedDotProduct fp n (R i) (fun k => X k j) -
          ∑ k, R i k * X k j| ≤
        p28Gamma fp.u n * ∑ k, |R i k| * |X k j| :=
    p28_rounded_dot_error fp n (R i) (fun k => X k j) hvalid
  have hinner : ∀ k,
      |R i k - ∑ l, X i l * X k l| ≤
        p28Gamma fp.u n * ∑ l, |X i l| * |X k l| := by
    intro k
    simpa [R, p28RoundedMatMul, p28Transpose] using
      p28_rounded_dot_error fp n (X i) (fun l => X k l) hvalid
  have htransport :
      |(∑ k, R i k * X k j) -
          ∑ k, (∑ l, X i l * X k l) * X k j| ≤
        p28Gamma fp.u n *
          ∑ k, (∑ l, |X i l| * |X k l|) * |X k j| := by
    rw [← Finset.sum_sub_distrib]
    have hsum := Finset.abs_sum_le_sum_abs
      (fun k : Fin n => R i k * X k j - (∑ l, X i l * X k l) * X k j)
      Finset.univ
    calc
      |∑ k, (R i k * X k j - (∑ l, X i l * X k l) * X k j)|
          ≤ ∑ k, |R i k * X k j - (∑ l, X i l * X k l) * X k j| := hsum
      _ = ∑ k, |R i k - ∑ l, X i l * X k l| * |X k j| := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [← sub_mul, abs_mul]
      _ ≤ ∑ k, (p28Gamma fp.u n * ∑ l, |X i l| * |X k l|) * |X k j| := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_right (hinner k) (abs_nonneg _)
      _ = p28Gamma fp.u n *
          ∑ k, (∑ l, |X i l| * |X k l|) * |X k j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
  change
    |p28RoundedDotProduct fp n (R i) (fun k => X k j) -
        ∑ k, (∑ l, X i l * X k l) * X k j| ≤
      p28Gamma fp.u n * (∑ k, |R i k| * |X k j|) +
        p28Gamma fp.u n *
          ∑ k, (∑ l, |X i l| * |X k l|) * |X k j|
  exact (abs_sub_le _ (∑ k, R i k * X k j) _).trans
    (add_le_add houter htransport)

end HighamBench
