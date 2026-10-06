import HighamBench.P33Definitions

namespace HighamBench

open scoped BigOperators

private lemma p33_gamma_mono
    (u : ℝ) (m n : ℕ) (hu : 0 ≤ u) (hmn : m ≤ n)
    (hn : (n : ℝ) * u < 1) :
    p33Gamma u m ≤ p33Gamma u n := by
  unfold p33Gamma
  have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hmu : 0 ≤ (m : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hle : (m : ℝ) * u ≤ (n : ℝ) * u :=
    mul_le_mul_of_nonneg_right hmn' hu
  have hdm : 0 < 1 - (m : ℝ) * u := by linarith
  have hdn : 0 < 1 - (n : ℝ) * u := by linarith
  rw [div_le_div_iff₀ hdm hdn]
  nlinarith

private lemma p33_gamma_valid_of_le
    (u : ℝ) (m n : ℕ) (hu : 0 ≤ u) (hmn : m ≤ n)
    (hn : P33GammaValid u n) : P33GammaValid u m := by
  unfold P33GammaValid at hn ⊢
  have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hmn' hu) hn

private lemma p33_gamma_step
    (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (hvalid : ((n + 1 : ℕ) : ℝ) * u < 1) :
    (1 + u) * p33Gamma u n + u ≤ p33Gamma u (n + 1) := by
  unfold p33Gamma
  push_cast at hvalid ⊢
  have hdn : 0 < 1 - (n : ℝ) * u := by
    have hn : (n : ℝ) * u ≤ ((n : ℝ) + 1) * u := by
      nlinarith
    linarith
  have hdnext : 0 < 1 - ((n : ℝ) + 1) * u := by linarith
  have heq :
      (1 + u) * ((n : ℝ) * u / (1 - (n : ℝ) * u)) + u =
        ((n : ℝ) + 1) * u / (1 - (n : ℝ) * u) := by
    have hdne : 1 - (n : ℝ) * u ≠ 0 := ne_of_gt hdn
    have hdne' : 1 - u * (n : ℝ) ≠ 0 := by
      nlinarith [hdn]
    field_simp [hdne, hdne']
    ring
  rw [heq]
  exact div_le_div_of_nonneg_left (by positivity) hdnext (by nlinarith)

private lemma p33_gamma_nonneg
    (u : ℝ) (n : ℕ) (hu : 0 ≤ u) (hvalid : (n : ℝ) * u < 1) :
    0 ≤ p33Gamma u n := by
  unfold p33Gamma
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

private lemma p33_two_roundings_le_gamma_two
    (u : ℝ) (hu : 0 ≤ u) (hvalid : (2 : ℝ) * u < 1) :
    (1 + u) * u + u ≤ p33Gamma u 2 := by
  have h := p33_gamma_step u 1 hu (by norm_num at hvalid ⊢; exact hvalid)
  have hg1 : u ≤ p33Gamma u 1 := by
    unfold p33Gamma
    norm_num
    have hd : 0 < 1 - u := by nlinarith
    rw [le_div_iff₀ hd]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hg1 (by linarith : 0 ≤ 1 + u)]

private lemma p33_rounded_add_mul_step
    (u gamma gamma' acc z M v dm da : ℝ)
    (hu : 0 ≤ u) (hgamma : 0 ≤ gamma) (hM : 0 ≤ M)
    (hdm : |dm| ≤ u) (hda : |da| ≤ u)
    (hacc : |acc - z| ≤ gamma * M) (hz : |z| ≤ M)
    (hrec : (1 + u) * gamma + u ≤ gamma')
    (hnew : (1 + u) * u + u ≤ gamma') :
    |(acc + v * (1 + dm)) * (1 + da) - (z + v)| ≤
      gamma' * (M + |v|) := by
  have hone : |1 + da| ≤ 1 + u := by
    calc
      |1 + da| ≤ |(1 : ℝ)| + |da| := abs_add_le _ _
      _ ≤ 1 + u := by norm_num; linarith
  have hcoeff : |dm * (1 + da) + da| ≤ (1 + u) * u + u := by
    calc
      |dm * (1 + da) + da| ≤ |dm * (1 + da)| + |da| := abs_add_le _ _
      _ = |dm| * |1 + da| + |da| := by rw [abs_mul]
      _ ≤ u * (1 + u) + u := by gcongr
      _ = (1 + u) * u + u := by ring
  have hid :
      (acc + v * (1 + dm)) * (1 + da) - (z + v) =
        (acc - z) * (1 + da) + z * da +
          v * (dm * (1 + da) + da) := by
    ring
  rw [hid]
  calc
    |(acc - z) * (1 + da) + z * da + v * (dm * (1 + da) + da)| ≤
        |(acc - z) * (1 + da) + z * da| +
          |v * (dm * (1 + da) + da)| := abs_add_le _ _
    _ ≤ (|(acc - z) * (1 + da)| + |z * da|) +
          |v * (dm * (1 + da) + da)| := by gcongr; exact abs_add_le _ _
    _ = |acc - z| * |1 + da| + |z| * |da| +
          |v| * |dm * (1 + da) + da| := by simp only [abs_mul]
    _ ≤ (gamma * M) * (1 + u) + M * u +
          |v| * ((1 + u) * u + u) := by gcongr
    _ = ((1 + u) * gamma + u) * M +
          ((1 + u) * u + u) * |v| := by ring
    _ ≤ gamma' * M + gamma' * |v| := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hrec hM)
        (mul_le_mul_of_nonneg_right hnew (abs_nonneg v))
    _ = gamma' * (M + |v|) := by ring

private lemma p33_rounded_sparse_sum_error
    (fp : P33FPModel) (n : ℕ) (a x : Fin n → ℝ)
    (hvalid : P33GammaValid fp.u n) :
    |Fin.foldl n
          (fun acc j ↦ fp.fl_add acc (fp.fl_mul (a j) (x j))) 0 -
        ∑ j : Fin n, a j * x j| ≤
      p33Gamma fp.u n * ∑ j : Fin n, |a j| * |x j| := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
      obtain ⟨dm, hdm, hmul⟩ := fp.model_mul (a 0) (x 0)
      have hstep := p33_gamma_step fp.u 0 fp.u_nonneg (by
        simpa [P33GammaValid] using hvalid)
      have hu_gamma : fp.u ≤ p33Gamma fp.u 1 := by
        simpa [p33Gamma] using hstep
      have hfold :
          Fin.foldl 1
              (fun acc j ↦ fp.fl_add acc (fp.fl_mul (a j) (x j))) 0 =
            fp.fl_mul (a 0) (x 0) := by
        rw [Fin.foldl_succ]
        simp [fp.fl_add_zero]
      rw [hfold, Fin.sum_univ_succ]
      simp only [Fin.sum_univ_zero, add_zero]
      rw [hmul]
      calc
        |a 0 * x 0 * (1 + dm) - a 0 * x 0| =
            |a 0| * |x 0| * |dm| := by
              have heq : a 0 * x 0 * (1 + dm) - a 0 * x 0 =
                  (a 0 * x 0) * dm := by ring
              rw [heq, abs_mul, abs_mul]
        _ ≤ |a 0| * |x 0| * fp.u := by gcongr
        _ ≤ |a 0| * |x 0| * p33Gamma fp.u 1 := by gcongr
        _ = p33Gamma fp.u 1 * ∑ j : Fin 1, |a j| * |x j| := by
          rw [Fin.sum_univ_succ]
          simp
          ring
  | more n ih0 ih1 =>
      let a' : Fin (n + 1) → ℝ := fun j ↦ a j.castSucc
      let x' : Fin (n + 1) → ℝ := fun j ↦ x j.castSucc
      let acc : ℝ :=
        Fin.foldl (n + 1)
          (fun q j ↦ fp.fl_add q (fp.fl_mul (a' j) (x' j))) 0
      let z : ℝ := ∑ j : Fin (n + 1), a' j * x' j
      let M : ℝ := ∑ j : Fin (n + 1), |a' j| * |x' j|
      let v : ℝ := a (Fin.last (n + 1)) * x (Fin.last (n + 1))
      have hprior_valid : P33GammaValid fp.u (n + 1) :=
        p33_gamma_valid_of_le fp.u (n + 1) (n + 2) fp.u_nonneg (by omega) hvalid
      have htwo_valid : (2 : ℝ) * fp.u < 1 := by
        have := p33_gamma_valid_of_le fp.u 2 (n + 2) fp.u_nonneg (by omega) hvalid
        simpa [P33GammaValid] using this
      have hacc : |acc - z| ≤ p33Gamma fp.u (n + 1) * M := by
        simpa [acc, z, M, a', x'] using ih1 a' x' hprior_valid
      have hM : 0 ≤ M := by
        dsimp [M]
        positivity
      have hz : |z| ≤ M := by
        dsimp [z, M]
        simpa only [abs_mul] using
          (Finset.abs_sum_le_sum_abs
            (fun j : Fin (n + 1) ↦ a' j * x' j) Finset.univ)
      have hgamma : 0 ≤ p33Gamma fp.u (n + 1) :=
        p33_gamma_nonneg fp.u (n + 1) fp.u_nonneg (by
          simpa [P33GammaValid] using hprior_valid)
      have hrec :
          (1 + fp.u) * p33Gamma fp.u (n + 1) + fp.u ≤
            p33Gamma fp.u (n + 2) := by
        simpa [Nat.add_assoc] using
          p33_gamma_step fp.u (n + 1) fp.u_nonneg (by
            simpa [P33GammaValid, Nat.add_assoc] using hvalid)
      have hnew :
          (1 + fp.u) * fp.u + fp.u ≤ p33Gamma fp.u (n + 2) := by
        exact le_trans
          (p33_two_roundings_le_gamma_two fp.u fp.u_nonneg htwo_valid)
          (p33_gamma_mono fp.u 2 (n + 2) fp.u_nonneg (by omega) (by
            simpa [P33GammaValid] using hvalid))
      obtain ⟨dm, hdm, hmul⟩ :=
        fp.model_mul (a (Fin.last (n + 1))) (x (Fin.last (n + 1)))
      have hmul' :
          fp.fl_mul (a (Fin.last (n + 1))) (x (Fin.last (n + 1))) =
            v * (1 + dm) := by simpa [v] using hmul
      obtain ⟨da, hda, hadd⟩ :=
        fp.model_add acc
          (fp.fl_mul (a (Fin.last (n + 1))) (x (Fin.last (n + 1))) )
      have hadd' :
          fp.fl_add acc (v * (1 + dm)) =
            (acc + v * (1 + dm)) * (1 + da) := by
        simpa [hmul'] using hadd
      have hmain := p33_rounded_add_mul_step
        fp.u (p33Gamma fp.u (n + 1)) (p33Gamma fp.u (n + 2))
        acc z M v dm da fp.u_nonneg hgamma hM hdm hda hacc hz hrec hnew
      have hsum :
          (∑ j : Fin (n + 2), a j * x j) =
            (∑ j : Fin (n + 1), a j.castSucc * x j.castSucc) +
              a (Fin.last (n + 1)) * x (Fin.last (n + 1)) :=
        Fin.sum_univ_castSucc (fun j : Fin (n + 2) ↦ a j * x j)
      have habssum :
          (∑ j : Fin (n + 2), |a j| * |x j|) =
            (∑ j : Fin (n + 1), |a j.castSucc| * |x j.castSucc|) +
              |a (Fin.last (n + 1))| * |x (Fin.last (n + 1))| :=
        Fin.sum_univ_castSucc (fun j : Fin (n + 2) ↦ |a j| * |x j|)
      rw [Fin.foldl_succ_last, hsum, habssum]
      simpa [a', x', acc, z, M, v, hmul', hadd', abs_mul] using hmain

private lemma p33_rounded_sparse_row_product_eq_fold
    (fp : P33FPModel) (s : ℕ) (a x : Fin s → ℝ) :
    p33RoundedSparseRowProduct fp s a x =
      Fin.foldl s
        (fun acc j ↦ fp.fl_add acc (fp.fl_mul (a j) (x j))) 0 := by
  cases s with
  | zero =>
      unfold p33RoundedSparseRowProduct
      rw [Fin.foldl_zero]
  | succ n =>
      unfold p33RoundedSparseRowProduct
      rw [Fin.foldl_succ, fp.fl_add_zero]

/-- P33-T1: the sparse-row computed-residual error bound in Section 2.2. -/
theorem p33_t1_sparse_residual_error
    (fp : P33FPModel) (s : ℕ) (a x : Fin s → ℝ) (b : ℝ)
    (hvalid : P33GammaValid fp.u (s + 1)) :
    |p33RoundedResidual fp s a x b - p33ExactResidual s a x b| ≤
      p33ResidualErrorMajorant fp s a x b := by
  -- PROOF_START P33-T1-H001
  let R : ℝ := p33RoundedSparseRowProduct fp s a x
  let S : ℝ := ∑ j : Fin s, a j * x j
  let M : ℝ := ∑ j : Fin s, |a j| * |x j|
  have hs_valid : P33GammaValid fp.u s :=
    p33_gamma_valid_of_le fp.u s (s + 1) fp.u_nonneg (by omega) hvalid
  have hdot : |R - S| ≤ p33Gamma fp.u s * M := by
    simpa [R, S, M, p33_rounded_sparse_row_product_eq_fold] using
      p33_rounded_sparse_sum_error fp s a x hs_valid
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hS : |S| ≤ M := by
    dsimp [S, M]
    simpa only [abs_mul] using
      (Finset.abs_sum_le_sum_abs
        (fun j : Fin s ↦ a j * x j) Finset.univ)
  have hgamma : 0 ≤ p33Gamma fp.u s :=
    p33_gamma_nonneg fp.u s fp.u_nonneg (by
      simpa [P33GammaValid] using hs_valid)
  have hrec :
      (1 + fp.u) * p33Gamma fp.u s + fp.u ≤
        p33Gamma fp.u (s + 1) :=
    p33_gamma_step fp.u s fp.u_nonneg (by
      simpa [P33GammaValid] using hvalid)
  have hu_gamma : fp.u ≤ p33Gamma fp.u (s + 1) := by
    have hnonneg : 0 ≤ (1 + fp.u) * p33Gamma fp.u s :=
      mul_nonneg (by linarith [fp.u_nonneg]) hgamma
    linarith
  obtain ⟨d, hd, hsub⟩ := fp.model_sub b R
  have hone : |1 + d| ≤ 1 + fp.u := by
    calc
      |1 + d| ≤ |(1 : ℝ)| + |d| := abs_add_le _ _
      _ ≤ 1 + fp.u := by norm_num; linarith
  have hbS : |b - S| ≤ |b| + M := by
    rw [sub_eq_add_neg]
    calc
      |b + -S| ≤ |b| + |-S| := abs_add_le _ _
      _ = |b| + |S| := by rw [abs_neg]
      _ ≤ |b| + M := by linarith
  change |fp.fl_sub b R - (b - S)| ≤
    p33Gamma fp.u (s + 1) * (|b| + M)
  rw [hsub]
  have hid :
      (b - R) * (1 + d) - (b - S) =
        -(R - S) * (1 + d) + (b - S) * d := by
    ring
  rw [hid]
  calc
    |-(R - S) * (1 + d) + (b - S) * d| ≤
        |-(R - S) * (1 + d)| + |(b - S) * d| := abs_add_le _ _
    _ = |R - S| * |1 + d| + |b - S| * |d| := by
      simp only [abs_mul, abs_neg]
    _ ≤ (p33Gamma fp.u s * M) * (1 + fp.u) +
          (|b| + M) * fp.u := by gcongr
    _ = ((1 + fp.u) * p33Gamma fp.u s + fp.u) * M +
          fp.u * |b| := by ring
    _ ≤ p33Gamma fp.u (s + 1) * M +
          p33Gamma fp.u (s + 1) * |b| := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hrec hM)
        (mul_le_mul_of_nonneg_right hu_gamma (abs_nonneg b))
    _ = p33Gamma fp.u (s + 1) * (|b| + M) := by ring

end HighamBench
