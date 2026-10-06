import HighamBench.P33Definitions

namespace HighamBench

open scoped BigOperators

private lemma p33_gamma_nonneg (u : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (hvalid : P33GammaValid u n) :
    0 ≤ p33Gamma u n := by
  unfold p33Gamma P33GammaValid at *
  have hd : 0 < 1 - (n : ℝ) * u := by linarith
  positivity

private lemma p33_u_le_gamma (u : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (hn : 1 ≤ n) (hvalid : P33GammaValid u n) :
    u ≤ p33Gamma u n := by
  unfold p33Gamma P33GammaValid at *
  have hd : 0 < 1 - (n : ℝ) * u := by linarith
  rw [le_div_iff₀ hd]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hun : u ≤ (n : ℝ) * u :=
    by simpa using mul_le_mul_of_nonneg_right hn' hu
  have hsq : 0 ≤ (n : ℝ) * u ^ 2 := by positivity
  nlinarith

private lemma p33_two_u_le_gamma (u : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (hn : 2 ≤ n) (hvalid : P33GammaValid u n) :
    2 * u + u ^ 2 ≤ p33Gamma u n := by
  unfold p33Gamma P33GammaValid at *
  have hd : 0 < 1 - (n : ℝ) * u := by linarith
  rw [le_div_iff₀ hd]
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnu : 2 * u ≤ (n : ℝ) * u :=
    mul_le_mul_of_nonneg_right hn' hu
  have hdle : 1 - (n : ℝ) * u ≤ 1 - 2 * u := by linarith
  have hf : 0 ≤ 2 * u + u ^ 2 := by positivity
  calc
    (2 * u + u ^ 2) * (1 - (n : ℝ) * u) ≤
        (2 * u + u ^ 2) * (1 - 2 * u) :=
      mul_le_mul_of_nonneg_left hdle hf
    _ ≤ 2 * u := by
      nlinarith [sq_nonneg u, mul_nonneg hu (sq_nonneg u)]
    _ ≤ (n : ℝ) * u := hnu

private lemma p33_gamma_step (u : ℝ) (m : ℕ)
    (hu : 0 ≤ u) (hvalid : P33GammaValid u (m + 1)) :
    p33Gamma u m * (1 + u) + u ≤ p33Gamma u (m + 1) := by
  unfold p33Gamma P33GammaValid at *
  have hdm : 0 < 1 - (m : ℝ) * u := by
    push_cast at hvalid
    nlinarith
  have hds : 0 < 1 - ((m + 1 : ℕ) : ℝ) * u := by linarith
  have heq :
      ((m : ℝ) * u) / (1 - (m : ℝ) * u) * (1 + u) + u =
        (((m : ℝ) + 1) * u) / (1 - (m : ℝ) * u) := by
    field_simp
    ring
  rw [heq]
  push_cast
  apply div_le_div_of_nonneg_left
  · positivity
  · exact_mod_cast hds
  · nlinarith

private lemma p33_add_mul_error_step
    (fp : P33FPModel) (m : ℕ) (q T A c d : ℝ)
    (hm : 1 ≤ m) (hvalid : P33GammaValid fp.u (m + 1))
    (hq : |q - T| ≤ p33Gamma fp.u m * A)
    (hT : |T| ≤ A) (hA : 0 ≤ A) :
    |fp.fl_add q (fp.fl_mul c d) - (T + c * d)| ≤
      p33Gamma fp.u (m + 1) * (A + |c| * |d|) := by
  have hvalid_m : P33GammaValid fp.u m := by
    unfold P33GammaValid at *
    have hcast : (m : ℝ) ≤ (m + 1 : ℕ) := by
      norm_num
    have hmul := mul_le_mul_of_nonneg_right hcast fp.u_nonneg
    exact lt_of_le_of_lt hmul hvalid
  have hgm : 0 ≤ p33Gamma fp.u m :=
    p33_gamma_nonneg fp.u m fp.u_nonneg hvalid_m
  have hgs : 0 ≤ p33Gamma fp.u (m + 1) :=
    p33_gamma_nonneg fp.u (m + 1) fp.u_nonneg hvalid
  have hgstep :
      p33Gamma fp.u m * (1 + fp.u) + fp.u ≤
        p33Gamma fp.u (m + 1) :=
    p33_gamma_step fp.u m fp.u_nonneg hvalid
  have htwo : 2 * fp.u + fp.u ^ 2 ≤ p33Gamma fp.u (m + 1) := by
    apply p33_two_u_le_gamma fp.u (m + 1) fp.u_nonneg
    · omega
    · exact hvalid
  rcases fp.model_mul c d with ⟨dm, hdm, hmul⟩
  rcases fp.model_add q (fp.fl_mul c d) with ⟨da, hda, hadd⟩
  rw [hadd, hmul]
  have hone : |1 + da| ≤ 1 + fp.u := by
    calc
      |1 + da| ≤ |(1 : ℝ)| + |da| := abs_add_le 1 da
      _ ≤ 1 + fp.u := by norm_num; linarith
  have hdelta : |dm + da + dm * da| ≤ 2 * fp.u + fp.u ^ 2 := by
    calc
      |dm + da + dm * da| ≤ |dm| + |da| + |dm * da| :=
        abs_add_three dm da (dm * da)
      _ = |dm| + |da| + |dm| * |da| := by rw [abs_mul]
      _ ≤ fp.u + fp.u + fp.u * fp.u := by
        gcongr
        exact fp.u_nonneg
      _ = 2 * fp.u + fp.u ^ 2 := by ring
  have hid :
      (q + c * d * (1 + dm)) * (1 + da) - (T + c * d) =
        (q - T) * (1 + da) + T * da +
          (c * d) * (dm + da + dm * da) := by ring
  rw [hid]
  calc
    |(q - T) * (1 + da) + T * da +
        c * d * (dm + da + dm * da)| ≤
        |(q - T) * (1 + da)| + |T * da| +
          |c * d * (dm + da + dm * da)| :=
      abs_add_three _ _ _
    _ = |q - T| * |1 + da| + |T| * |da| +
          (|c| * |d|) * |dm + da + dm * da| := by
      simp only [abs_mul]
    _ ≤ (p33Gamma fp.u m * A) * (1 + fp.u) + A * fp.u +
          (|c| * |d|) * (2 * fp.u + fp.u ^ 2) := by
      gcongr
    _ ≤ p33Gamma fp.u (m + 1) * A +
          p33Gamma fp.u (m + 1) * (|c| * |d|) := by
      have hAstep :
          (p33Gamma fp.u m * A) * (1 + fp.u) + A * fp.u ≤
            p33Gamma fp.u (m + 1) * A := by
        calc
          (p33Gamma fp.u m * A) * (1 + fp.u) + A * fp.u =
              (p33Gamma fp.u m * (1 + fp.u) + fp.u) * A := by ring
          _ ≤ p33Gamma fp.u (m + 1) * A :=
            mul_le_mul_of_nonneg_right hgstep hA
      have hp : 0 ≤ |c| * |d| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
      nlinarith [mul_le_mul_of_nonneg_left htwo hp]
    _ = p33Gamma fp.u (m + 1) * (A + |c| * |d|) := by ring

private lemma p33_gamma_valid_of_le (u : ℝ) {k n : ℕ}
    (hu : 0 ≤ u) (hkn : k ≤ n) (hvalid : P33GammaValid u n) :
    P33GammaValid u k := by
  unfold P33GammaValid at *
  have hcast : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hmul := mul_le_mul_of_nonneg_right hcast hu
  exact lt_of_le_of_lt hmul hvalid

private lemma p33_fold_error
    (fp : P33FPModel) (n m : ℕ) (c d : Fin n → ℝ)
    (q T A : ℝ) (hm : 1 ≤ m)
    (hvalid : P33GammaValid fp.u (m + n))
    (hq : |q - T| ≤ p33Gamma fp.u m * A)
    (hT : |T| ≤ A) (hA : 0 ≤ A) :
    |Fin.foldl n
          (fun acc j ↦ fp.fl_add acc (fp.fl_mul (c j) (d j))) q -
        (T + ∑ j : Fin n, c j * d j)| ≤
      p33Gamma fp.u (m + n) *
        (A + ∑ j : Fin n, |c j| * |d j|) := by
  induction n generalizing m q T A with
  | zero =>
      simpa using hq
  | succ n ih =>
      have hvalid_one : P33GammaValid fp.u (m + 1) := by
        apply p33_gamma_valid_of_le fp.u fp.u_nonneg (n := m + (n + 1))
        · omega
        · simpa [Nat.add_assoc] using hvalid
      have hfirst := p33_add_mul_error_step fp m q T A (c 0) (d 0)
        hm hvalid_one hq hT hA
      have hTfirst : |T + c 0 * d 0| ≤ A + |c 0| * |d 0| := by
        calc
          |T + c 0 * d 0| ≤ |T| + |c 0 * d 0| := abs_add_le _ _
          _ = |T| + |c 0| * |d 0| := by rw [abs_mul]
          _ ≤ A + |c 0| * |d 0| := by linarith
      have hAfirst : 0 ≤ A + |c 0| * |d 0| := by positivity
      have hvalid_tail : P33GammaValid fp.u ((m + 1) + n) := by
        convert hvalid using 1 <;> omega
      have htail := ih (m := m + 1)
        (c := fun j ↦ c j.succ) (d := fun j ↦ d j.succ)
        (q := fp.fl_add q (fp.fl_mul (c 0) (d 0)))
        (T := T + c 0 * d 0) (A := A + |c 0| * |d 0|)
        (by omega) hvalid_tail hfirst hTfirst hAfirst
      rw [Fin.foldl_succ]
      simpa only [Fin.sum_univ_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm, add_assoc] using htail

private lemma p33_sparse_product_error
    (fp : P33FPModel) (s : ℕ) (a x : Fin s → ℝ)
    (hvalid : P33GammaValid fp.u s) :
    |p33RoundedSparseRowProduct fp s a x - ∑ j : Fin s, a j * x j| ≤
      p33Gamma fp.u s * ∑ j : Fin s, |a j| * |x j| := by
  cases s with
  | zero =>
      simp [p33RoundedSparseRowProduct]
  | succ s =>
      have hvalid_one : P33GammaValid fp.u 1 :=
        p33_gamma_valid_of_le fp.u fp.u_nonneg (by omega) hvalid
      have hugamma : fp.u ≤ p33Gamma fp.u 1 :=
        p33_u_le_gamma fp.u 1 fp.u_nonneg (by omega) hvalid_one
      rcases fp.model_mul (a 0) (x 0) with ⟨dm, hdm, hmul⟩
      have hinit :
          |fp.fl_mul (a 0) (x 0) - a 0 * x 0| ≤
            p33Gamma fp.u 1 * (|a 0| * |x 0|) := by
        rw [hmul]
        have hid : a 0 * x 0 * (1 + dm) - a 0 * x 0 =
            (a 0 * x 0) * dm := by ring
        rw [hid, abs_mul, abs_mul]
        calc
          |a 0| * |x 0| * |dm| ≤ |a 0| * |x 0| * fp.u := by
            gcongr
          _ ≤ |a 0| * |x 0| * p33Gamma fp.u 1 := by
            gcongr
          _ = p33Gamma fp.u 1 * (|a 0| * |x 0|) := by ring
      have hfold := p33_fold_error fp s 1
        (fun j ↦ a j.succ) (fun j ↦ x j.succ)
        (fp.fl_mul (a 0) (x 0)) (a 0 * x 0) (|a 0| * |x 0|)
        (by omega) (by simpa [Nat.add_comm] using hvalid) hinit
        (by rw [abs_mul]) (by positivity)
      simpa [p33RoundedSparseRowProduct, Fin.sum_univ_succ,
        Nat.add_comm] using hfold

/-- P33-T1: the sparse-row computed-residual error bound in Section 2.2. -/
theorem p33_t1_sparse_residual_error
    (fp : P33FPModel) (s : ℕ) (a x : Fin s → ℝ) (b : ℝ)
    (hvalid : P33GammaValid fp.u (s + 1)) :
    |p33RoundedResidual fp s a x b - p33ExactResidual s a x b| ≤
      p33ResidualErrorMajorant fp s a x b := by
  -- PROOF_START P33-T1-H001
  let q := p33RoundedSparseRowProduct fp s a x
  let P := ∑ j : Fin s, a j * x j
  let S := ∑ j : Fin s, |a j| * |x j|
  have hvalid_s : P33GammaValid fp.u s :=
    p33_gamma_valid_of_le fp.u fp.u_nonneg (by omega) hvalid
  have hprod : |q - P| ≤ p33Gamma fp.u s * S := by
    simpa [q, P, S] using p33_sparse_product_error fp s a x hvalid_s
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hP : |P| ≤ S := by
    calc
      |P| ≤ ∑ j : Fin s, |a j * x j| := by
        dsimp [P]
        exact Finset.abs_sum_le_sum_abs _ _
      _ = S := by simp [S, abs_mul]
  have hbP : |b - P| ≤ |b| + S := by
    calc
      |b - P| = |b + -P| := by rw [sub_eq_add_neg]
      _ ≤ |b| + |-P| := abs_add_le _ _
      _ = |b| + |P| := by rw [abs_neg]
      _ ≤ |b| + S := by linarith
  have hgamma_s : 0 ≤ p33Gamma fp.u s :=
    p33_gamma_nonneg fp.u s fp.u_nonneg hvalid_s
  have hgamma_next : 0 ≤ p33Gamma fp.u (s + 1) :=
    p33_gamma_nonneg fp.u (s + 1) fp.u_nonneg hvalid
  have hugamma : fp.u ≤ p33Gamma fp.u (s + 1) :=
    p33_u_le_gamma fp.u (s + 1) fp.u_nonneg (by omega) hvalid
  have hgstep :
      p33Gamma fp.u s * (1 + fp.u) + fp.u ≤
        p33Gamma fp.u (s + 1) :=
    p33_gamma_step fp.u s fp.u_nonneg hvalid
  rcases fp.model_sub b q with ⟨dr, hdr, hsub⟩
  have hone : |1 + dr| ≤ 1 + fp.u := by
    calc
      |1 + dr| ≤ |(1 : ℝ)| + |dr| := abs_add_le _ _
      _ ≤ 1 + fp.u := by norm_num; linarith
  change |fp.fl_sub b q - (b - P)| ≤
    p33Gamma fp.u (s + 1) * (|b| + S)
  rw [hsub]
  have hid :
      (b - q) * (1 + dr) - (b - P) =
        -(q - P) * (1 + dr) + (b - P) * dr := by ring
  rw [hid]
  calc
    |-(q - P) * (1 + dr) + (b - P) * dr| ≤
        |-(q - P) * (1 + dr)| + |(b - P) * dr| := abs_add_le _ _
    _ = |q - P| * |1 + dr| + |b - P| * |dr| := by
      simp only [abs_mul, abs_neg]
    _ ≤ (p33Gamma fp.u s * S) * (1 + fp.u) +
          (|b| + S) * fp.u := by
      gcongr
    _ = (p33Gamma fp.u s * (1 + fp.u) + fp.u) * S +
          fp.u * |b| := by ring
    _ ≤ p33Gamma fp.u (s + 1) * S +
          p33Gamma fp.u (s + 1) * |b| := by
      have hscoeff := mul_le_mul_of_nonneg_right hgstep hS
      have hbcoeff := mul_le_mul_of_nonneg_right hugamma (abs_nonneg b)
      linarith
    _ = p33Gamma fp.u (s + 1) * (|b| + S) := by ring

end HighamBench
