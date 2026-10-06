import HighamBench.P33Definitions

namespace HighamBench

open scoped BigOperators

private lemma p33_gamma_mono
    (u : ℝ) (m n : ℕ) (hu : 0 ≤ u) (hmn : m ≤ n)
    (hn : P33GammaValid u n) :
    p33Gamma u m ≤ p33Gamma u n := by
  have hcast : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hmul : (m : ℝ) * u ≤ (n : ℝ) * u :=
    mul_le_mul_of_nonneg_right hcast hu
  have hmvalid : (m : ℝ) * u < 1 := lt_of_le_of_lt hmul hn
  have hmden : 0 < 1 - (m : ℝ) * u := sub_pos.mpr hmvalid
  have hnden : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hn
  unfold p33Gamma
  apply (div_le_div_iff₀ hmden hnden).2
  nlinarith

private lemma p33_gamma_step
    (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (hvalid : P33GammaValid u (n + 1)) :
    u + (1 + u) * p33Gamma u n ≤ p33Gamma u (n + 1) := by
  have hcast : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
  have hmul : (n : ℝ) * u ≤ ((n + 1 : ℕ) : ℝ) * u :=
    mul_le_mul_of_nonneg_right hcast hu
  have hnvalid : (n : ℝ) * u < 1 := lt_of_le_of_lt hmul hvalid
  have hnden : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hnvalid
  have htden : 0 < 1 - ((n + 1 : ℕ) : ℝ) * u := sub_pos.mpr hvalid
  have hid :
      u + (1 + u) * (((n : ℝ) * u) / (1 - (n : ℝ) * u)) =
        (((n + 1 : ℕ) : ℝ) * u) / (1 - (n : ℝ) * u) := by
    have hden' : 1 - u * (n : ℝ) ≠ 0 := by
      simpa [mul_comm] using ne_of_gt hnden
    apply (eq_div_iff (ne_of_gt hnden)).2
    field_simp [hden']
    push_cast
    ring
  unfold p33Gamma
  rw [hid]
  apply div_le_div_of_nonneg_left
  · positivity
  · exact htden
  · push_cast
    ring_nf
    nlinarith

private lemma p33_two_error_le_gamma
    (u : ℝ) (n : ℕ) (hu : 0 ≤ u) (hn : 2 ≤ n)
    (hvalid : P33GammaValid u n) :
    2 * u + u ^ 2 ≤ p33Gamma u n := by
  have h2n := p33_gamma_mono u 2 n hu hn hvalid
  have h2valid : P33GammaValid u 2 := by
    have hcast : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcast hu) hvalid
  have hden : 0 < 1 - (2 : ℝ) * u := sub_pos.mpr h2valid
  have hbase : 2 * u + u ^ 2 ≤ p33Gamma u 2 := by
    unfold p33Gamma
    apply (le_div_iff₀ hden).2
    have hcube : 0 ≤ u ^ 2 * u := mul_nonneg (sq_nonneg u) hu
    norm_num
    nlinarith [sq_nonneg u]
  exact hbase.trans h2n

private lemma p33_rounded_product_error
    (fp : P33FPModel) : ∀ (s : ℕ) (a x : Fin s → ℝ),
      P33GammaValid fp.u s →
      |p33RoundedSparseRowProduct fp s a x - ∑ j : Fin s, a j * x j| ≤
        p33Gamma fp.u s * ∑ j : Fin s, |a j| * |x j| := by
  intro s
  induction s with
  | zero =>
      intro a x hvalid
      simp [p33RoundedSparseRowProduct, p33Gamma]
  | succ s ih =>
      intro a x hvalid
      cases s with
      | zero =>
          obtain ⟨δ, hδ, hmul⟩ := fp.model_mul (a 0) (x 0)
          have hu_gamma : fp.u ≤ p33Gamma fp.u 1 := by
            simpa [p33Gamma] using
              (p33_gamma_step fp.u 0 fp.u_nonneg hvalid)
          simp only [p33RoundedSparseRowProduct, Fin.foldl_zero,
            Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
          rw [hmul]
          have herr :
              |(a 0 * x 0) * (1 + δ) - a 0 * x 0| =
                (|a 0| * |x 0|) * |δ| := by
            rw [show (a 0 * x 0) * (1 + δ) - a 0 * x 0 =
                (a 0 * x 0) * δ by ring]
            simp only [abs_mul]
          rw [herr]
          calc
            (|a 0| * |x 0|) * |δ| ≤ (|a 0| * |x 0|) * fp.u :=
              mul_le_mul_of_nonneg_left hδ
                (mul_nonneg (abs_nonneg _) (abs_nonneg _))
            _ = fp.u * (|a 0| * |x 0|) := by ring
            _ ≤ p33Gamma fp.u 1 * (|a 0| * |x 0|) :=
              mul_le_mul_of_nonneg_right hu_gamma
                (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      | succ k =>
          let a' : Fin (k + 1) → ℝ := fun i ↦ a i.castSucc
          let x' : Fin (k + 1) → ℝ := fun i ↦ x i.castSucc
          have hprev_valid : P33GammaValid fp.u (k + 1) := by
            have hc : ((k + 1 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by norm_num
            exact lt_of_le_of_lt
              (mul_le_mul_of_nonneg_right hc fp.u_nonneg) hvalid
          have ih' := ih a' x' hprev_valid
          have hfold :
              p33RoundedSparseRowProduct fp (k + 2) a x =
                fp.fl_add (p33RoundedSparseRowProduct fp (k + 1) a' x')
                  (fp.fl_mul (a (Fin.last (k + 1)))
                    (x (Fin.last (k + 1)))) := by
            simp [p33RoundedSparseRowProduct, Fin.foldl_succ_last, a', x']
          let d : ℝ := p33RoundedSparseRowProduct fp (k + 1) a' x'
          let S : ℝ := ∑ j : Fin (k + 1), a' j * x' j
          let A : ℝ := ∑ j : Fin (k + 1), |a' j| * |x' j|
          let y : ℝ := a (Fin.last (k + 1)) * x (Fin.last (k + 1))
          let Y : ℝ := |a (Fin.last (k + 1))| * |x (Fin.last (k + 1))|
          have ihd : |d - S| ≤ p33Gamma fp.u (k + 1) * A := by
            simpa [d, S, A] using ih'
          have hA : 0 ≤ A := by
            apply Finset.sum_nonneg
            intro i hi
            exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
          have hY : 0 ≤ Y := mul_nonneg (abs_nonneg _) (abs_nonneg _)
          have hS : |S| ≤ A := by
            calc
              |S| = |∑ j : Fin (k + 1), a' j * x' j| := by rfl
              _ ≤ ∑ j : Fin (k + 1), |a' j * x' j| :=
                Finset.abs_sum_le_sum_abs _ _
              _ = A := by simp [A, abs_mul]
          obtain ⟨δm, hδm, hmul⟩ :=
            fp.model_mul (a (Fin.last (k + 1))) (x (Fin.last (k + 1)))
          obtain ⟨δa, hδa, hadd⟩ :=
            fp.model_add d
              (fp.fl_mul (a (Fin.last (k + 1)))
                (x (Fin.last (k + 1))))
          have hyabs : |y| = Y := by simp [y, Y, abs_mul]
          have hfactor : |1 + δm| ≤ 1 + fp.u := by
            calc
              |1 + δm| ≤ |(1 : ℝ)| + |δm| := abs_add_le _ _
              _ ≤ 1 + fp.u := by simpa using add_le_add_left hδm 1
          have hmabs : |y * (1 + δm)| ≤ (1 + fp.u) * Y := by
            rw [abs_mul, hyabs]
            calc
              Y * |1 + δm| ≤ Y * (1 + fp.u) :=
                mul_le_mul_of_nonneg_left hfactor hY
              _ = (1 + fp.u) * Y := by ring
          have habsd : |d| ≤ A + p33Gamma fp.u (k + 1) * A := by
            calc
              |d| = |(d - S) + S| := by ring_nf
              _ ≤ |d - S| + |S| := abs_add_le _ _
              _ ≤ p33Gamma fp.u (k + 1) * A + A := add_le_add ihd hS
              _ = A + p33Gamma fp.u (k + 1) * A := by ring
          have hinside :
              |d + y * (1 + δm)| ≤
                A + p33Gamma fp.u (k + 1) * A + (1 + fp.u) * Y := by
            exact (abs_add_le _ _).trans (add_le_add habsd hmabs)
          have hem : |y * δm| ≤ fp.u * Y := by
            rw [abs_mul, hyabs]
            calc
              Y * |δm| ≤ Y * fp.u := mul_le_mul_of_nonneg_left hδm hY
              _ = fp.u * Y := by ring
          have hea :
              |δa * (d + y * (1 + δm))| ≤
                fp.u * (A + p33Gamma fp.u (k + 1) * A +
                  (1 + fp.u) * Y) := by
            rw [abs_mul]
            exact mul_le_mul hδa hinside (abs_nonneg _) fp.u_nonneg
          have hsum :
              (∑ j : Fin (k + 2), a j * x j) = S + y := by
            simp [Fin.sum_univ_castSucc, S, y, a', x']
          have habssum :
              (∑ j : Fin (k + 2), |a j| * |x j|) = A + Y := by
            simp [Fin.sum_univ_castSucc, A, Y, a', x']
          have hdecomp :
              (d + y * (1 + δm)) * (1 + δa) - (S + y) =
                (d - S) + y * δm + δa * (d + y * (1 + δm)) := by
            ring
          have htri :
              |(d + y * (1 + δm)) * (1 + δa) - (S + y)| ≤
                |d - S| + |y * δm| +
                  |δa * (d + y * (1 + δm))| := by
            rw [hdecomp]
            exact (abs_add_le _ _).trans
              (add_le_add (abs_add_le _ _) (le_refl _))
          have hstep := p33_gamma_step fp.u (k + 1) fp.u_nonneg hvalid
          have htwo := p33_two_error_le_gamma fp.u (k + 2) fp.u_nonneg
            (by omega) hvalid
          rw [hfold]
          change
            |fp.fl_add d
                (fp.fl_mul (a (Fin.last (k + 1)))
                  (x (Fin.last (k + 1)))) -
              (∑ j : Fin (k + 2), a j * x j)| ≤
              p33Gamma fp.u (k + 2) *
                ∑ j : Fin (k + 2), |a j| * |x j|
          rw [hadd, hmul, hsum, habssum]
          change
            |(d + y * (1 + δm)) * (1 + δa) - (S + y)| ≤
              p33Gamma fp.u (k + 2) * (A + Y)
          calc
            |(d + y * (1 + δm)) * (1 + δa) - (S + y)| ≤
                |d - S| + |y * δm| +
                  |δa * (d + y * (1 + δm))| := htri
            _ ≤ p33Gamma fp.u (k + 1) * A + fp.u * Y +
                fp.u * (A + p33Gamma fp.u (k + 1) * A +
                  (1 + fp.u) * Y) :=
              add_le_add (add_le_add ihd hem) hea
            _ = (fp.u + (1 + fp.u) * p33Gamma fp.u (k + 1)) * A +
                (2 * fp.u + fp.u ^ 2) * Y := by ring
            _ ≤ p33Gamma fp.u (k + 2) * A +
                p33Gamma fp.u (k + 2) * Y :=
              add_le_add
                (mul_le_mul_of_nonneg_right hstep hA)
                (mul_le_mul_of_nonneg_right htwo hY)
            _ = p33Gamma fp.u (k + 2) * (A + Y) := by ring

/-- P33-T1: the sparse-row computed-residual error bound in Section 2.2. -/
theorem p33_t1_sparse_residual_error
    (fp : P33FPModel) (s : ℕ) (a x : Fin s → ℝ) (b : ℝ)
    (hvalid : P33GammaValid fp.u (s + 1)) :
    |p33RoundedResidual fp s a x b - p33ExactResidual s a x b| ≤
      p33ResidualErrorMajorant fp s a x b := by
  -- PROOF_START P33-T1-H001
  let d : ℝ := p33RoundedSparseRowProduct fp s a x
  let S : ℝ := ∑ j : Fin s, a j * x j
  let A : ℝ := ∑ j : Fin s, |a j| * |x j|
  have hs_valid : P33GammaValid fp.u s := by
    have hc : (s : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by norm_num
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right hc fp.u_nonneg) hvalid
  have hd : |d - S| ≤ p33Gamma fp.u s * A := by
    simpa [d, S, A] using p33_rounded_product_error fp s a x hs_valid
  have hA : 0 ≤ A := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hS : |S| ≤ A := by
    calc
      |S| = |∑ j : Fin s, a j * x j| := by rfl
      _ ≤ ∑ j : Fin s, |a j * x j| := Finset.abs_sum_le_sum_abs _ _
      _ = A := by simp [A, abs_mul]
  have hgamma : 0 ≤ p33Gamma fp.u s := by
    unfold p33Gamma
    have hden : 0 < 1 - (s : ℝ) * fp.u := sub_pos.mpr hs_valid
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg) (le_of_lt hden)
  have habsd : |d| ≤ A + p33Gamma fp.u s * A := by
    calc
      |d| = |(d - S) + S| := by ring_nf
      _ ≤ |d - S| + |S| := abs_add_le _ _
      _ ≤ p33Gamma fp.u s * A + A := add_le_add hd hS
      _ = A + p33Gamma fp.u s * A := by ring
  obtain ⟨δ, hδ, hsub⟩ := fp.model_sub b d
  have hbd :
      |b - d| ≤ |b| + (A + p33Gamma fp.u s * A) := by
    exact (abs_sub b d).trans (add_le_add (le_refl _) habsd)
  have hround :
      |δ * (b - d)| ≤
        fp.u * (|b| + (A + p33Gamma fp.u s * A)) := by
    rw [abs_mul]
    exact mul_le_mul hδ hbd (abs_nonneg _) fp.u_nonneg
  have hdecomp :
      (b - d) * (1 + δ) - (b - S) = (S - d) + δ * (b - d) := by
    ring
  have htri :
      |(b - d) * (1 + δ) - (b - S)| ≤
        |d - S| + |δ * (b - d)| := by
    rw [hdecomp]
    calc
      |(S - d) + δ * (b - d)| ≤ |S - d| + |δ * (b - d)| :=
        abs_add_le _ _
      _ = |d - S| + |δ * (b - d)| := by rw [abs_sub_comm S d]
  have hstep := p33_gamma_step fp.u s fp.u_nonneg hvalid
  have hu_target : fp.u ≤ p33Gamma fp.u (s + 1) := by
    calc
      fp.u ≤ fp.u + (1 + fp.u) * p33Gamma fp.u s := by
        exact le_add_of_nonneg_right
          (mul_nonneg (by linarith [fp.u_nonneg]) hgamma)
      _ ≤ p33Gamma fp.u (s + 1) := hstep
  change |fp.fl_sub b d - (b - S)| ≤
    p33Gamma fp.u (s + 1) * (|b| + A)
  rw [hsub]
  calc
    |(b - d) * (1 + δ) - (b - S)| ≤
        |d - S| + |δ * (b - d)| := htri
    _ ≤ p33Gamma fp.u s * A +
        fp.u * (|b| + (A + p33Gamma fp.u s * A)) :=
      add_le_add hd hround
    _ = fp.u * |b| +
        (fp.u + (1 + fp.u) * p33Gamma fp.u s) * A := by ring
    _ ≤ p33Gamma fp.u (s + 1) * |b| +
        p33Gamma fp.u (s + 1) * A :=
      add_le_add
        (mul_le_mul_of_nonneg_right hu_target (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hstep hA)
    _ = p33Gamma fp.u (s + 1) * (|b| + A) := by ring

end HighamBench
