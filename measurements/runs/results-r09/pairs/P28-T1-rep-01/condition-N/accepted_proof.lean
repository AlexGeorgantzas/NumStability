import HighamBench.P28Definitions

namespace HighamBench

open scoped BigOperators

private lemma p28_gamma_nonneg_of_valid (u : ℝ) (k : ℕ)
    (hu : 0 ≤ u) (hvalid : (k : ℝ) * u < 1) :
    0 ≤ p28Gamma u k := by
  rw [p28Gamma]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (le_of_lt (sub_pos.mpr hvalid))

private lemma p28_gamma_one_ge (u : ℝ) (hu : 0 ≤ u) (hvalid : u < 1) :
    u ≤ p28Gamma u 1 := by
  rw [p28Gamma]
  norm_num
  rw [le_div_iff₀ (sub_pos.mpr hvalid)]
  nlinarith

private lemma p28_gamma_step_old (u : ℝ) (q : ℕ) (hu : 0 ≤ u)
    (hvalid : ((q + 1 : ℕ) : ℝ) * u < 1) :
    (1 + u) * p28Gamma u q + u ≤ p28Gamma u (q + 1) := by
  norm_num at hvalid ⊢
  have hqle : (q : ℝ) * u ≤ ((q + 1 : ℕ) : ℝ) * u := by
    norm_num
    exact mul_le_mul_of_nonneg_right (by norm_num) hu
  norm_num at hqle
  have hq : (q : ℝ) * u < 1 := lt_of_le_of_lt hqle hvalid
  have hdq : 0 < 1 - (q : ℝ) * u := sub_pos.mpr hq
  have hdqs : 0 < 1 - ((q : ℝ) + 1) * u := sub_pos.mpr hvalid
  rw [p28Gamma, p28Gamma]
  norm_num
  have heq :
      (1 + u) * (↑q * u / (1 - ↑q * u)) + u =
        ((↑q + 1) * u) / (1 - ↑q * u) := by
    have hden : 1 - u * (q : ℝ) ≠ 0 := by nlinarith
    apply (eq_div_iff (ne_of_gt hdq)).2
    field_simp [ne_of_gt hdq, hden]
    ring
  rw [heq]
  apply (div_le_div_iff₀ hdq hdqs).2
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) hu)
  nlinarith

private lemma p28_two_errors_le_gamma (u : ℝ) (q : ℕ) (hu : 0 ≤ u)
    (hq : 1 ≤ q) (hvalid : ((q + 1 : ℕ) : ℝ) * u < 1) :
    2 * u + u ^ 2 ≤ p28Gamma u (q + 1) := by
  have htwo : (2 : ℝ) * u ≤ ((q + 1 : ℕ) : ℝ) * u := by
    apply mul_le_mul_of_nonneg_right _ hu
    exact_mod_cast Nat.succ_le_succ hq
  have hv2 : 2 * u < 1 := lt_of_le_of_lt htwo hvalid
  have hd : 0 < 1 - ((q + 1 : ℕ) : ℝ) * u := sub_pos.mpr hvalid
  rw [p28Gamma, le_div_iff₀ hd]
  norm_num at *
  nlinarith [sq_nonneg u]

private lemma p28_rounded_step_bound
    (fp : P28FPModel) (q : ℕ) (hq : 1 ≤ q)
    (hvalid : ((q + 1 : ℕ) : ℝ) * fp.u < 1)
    (a s A x y : ℝ)
    (he : |a - s| ≤ p28Gamma fp.u q * A)
    (hs : |s| ≤ A) (hA : 0 ≤ A) :
    |fp.fl_add a (fp.fl_mul x y) - (s + x * y)| ≤
      p28Gamma fp.u (q + 1) * (A + |x * y|) := by
  obtain ⟨dm, hdm, hmul⟩ := fp.model_mul x y
  obtain ⟨da, hda, hadd⟩ := fp.model_add a (fp.fl_mul x y)
  rw [hadd, hmul]
  have hqvalid : (q : ℝ) * fp.u < 1 := by
    have hle : (q : ℝ) * fp.u ≤ ((q + 1 : ℕ) : ℝ) * fp.u := by
      norm_num
      exact mul_le_mul_of_nonneg_right (by norm_num) fp.u_nonneg
    exact lt_of_le_of_lt hle hvalid
  have hgamma : 0 ≤ p28Gamma fp.u q :=
    p28_gamma_nonneg_of_valid fp.u q fp.u_nonneg hqvalid
  have hda1 : |1 + da| ≤ 1 + fp.u := by
    calc
      |1 + da| ≤ |(1 : ℝ)| + |da| := abs_add_le _ _
      _ ≤ 1 + fp.u := by simpa using add_le_add_left hda 1
  have hdmda : |dm * da| ≤ fp.u * fp.u := by
    rw [abs_mul]
    exact mul_le_mul hdm hda (abs_nonneg _) fp.u_nonneg
  have hfac : |(1 + dm) * (1 + da) - 1| ≤ 2 * fp.u + fp.u ^ 2 := by
    have hid : (1 + dm) * (1 + da) - 1 = dm + da + dm * da := by ring
    rw [hid]
    calc
      |dm + da + dm * da| ≤ |dm + da| + |dm * da| := abs_add_le _ _
      _ ≤ (|dm| + |da|) + |dm * da| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ ≤ fp.u + fp.u + fp.u * fp.u := by gcongr
      _ = 2 * fp.u + fp.u ^ 2 := by ring
  have hold := p28_gamma_step_old fp.u q fp.u_nonneg hvalid
  have hnew := p28_two_errors_le_gamma fp.u q fp.u_nonneg hq hvalid
  have hdecomp :
      (a + x * y * (1 + dm)) * (1 + da) - (s + x * y) =
        (a - s) * (1 + da) + s * da +
          (x * y) * ((1 + dm) * (1 + da) - 1) := by ring
  rw [hdecomp]
  calc
    |(a - s) * (1 + da) + s * da +
        (x * y) * ((1 + dm) * (1 + da) - 1)|
        ≤ |(a - s) * (1 + da) + s * da| +
            |(x * y) * ((1 + dm) * (1 + da) - 1)| := abs_add_le _ _
    _ ≤ (|(a - s) * (1 + da)| + |s * da|) +
            |(x * y) * ((1 + dm) * (1 + da) - 1)| :=
          add_le_add (abs_add_le _ _) le_rfl
    _ = |a - s| * |1 + da| + |s| * |da| +
            |x * y| * |(1 + dm) * (1 + da) - 1| := by
          simp only [abs_mul]
    _ ≤ (p28Gamma fp.u q * A) * (1 + fp.u) + A * fp.u +
          |x * y| * (2 * fp.u + fp.u ^ 2) := by gcongr
    _ ≤ p28Gamma fp.u (q + 1) * A +
          p28Gamma fp.u (q + 1) * |x * y| := by
        have hAold :
            (p28Gamma fp.u q * A) * (1 + fp.u) + A * fp.u ≤
              p28Gamma fp.u (q + 1) * A := by
          calc
            (p28Gamma fp.u q * A) * (1 + fp.u) + A * fp.u =
                ((1 + fp.u) * p28Gamma fp.u q + fp.u) * A := by ring
            _ ≤ p28Gamma fp.u (q + 1) * A :=
              mul_le_mul_of_nonneg_right hold hA
        have ht := mul_le_mul_of_nonneg_left hnew (abs_nonneg (x * y))
        rw [mul_comm |x * y| (p28Gamma fp.u (q + 1))] at ht
        exact add_le_add hAold ht
    _ = p28Gamma fp.u (q + 1) * (A + |x * y|) := by ring

private lemma p28_rounded_fold_bound
    (fp : P28FPModel) :
    ∀ (m q : ℕ), 1 ≤ q → ((q + m : ℕ) : ℝ) * fp.u < 1 →
      ∀ (x y : Fin m → ℝ) (a s A : ℝ),
        |a - s| ≤ p28Gamma fp.u q * A → |s| ≤ A → 0 ≤ A →
        |Fin.foldl m
              (fun acc i ↦ fp.fl_add acc (fp.fl_mul (x i) (y i))) a -
            (s + ∑ i, x i * y i)| ≤
          p28Gamma fp.u (q + m) * (A + ∑ i, |x i * y i|) := by
  intro m
  induction m with
  | zero =>
      intro q hq hvalid x y a s A he hs hA
      simpa using he
  | succ m ih =>
      intro q hq hvalid x y a s A he hs hA
      rw [Fin.foldl_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
      have hvstep : ((q + 1 : ℕ) : ℝ) * fp.u < 1 := by
        have hle : ((q + 1 : ℕ) : ℝ) * fp.u ≤ ((q + (m + 1) : ℕ) : ℝ) * fp.u := by
          apply mul_le_mul_of_nonneg_right _ fp.u_nonneg
          exact_mod_cast Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le m)) q
        exact lt_of_le_of_lt hle hvalid
      have hstep := p28_rounded_step_bound fp q hq hvstep a s A (x 0) (y 0) he hs hA
      have hs' : |s + x 0 * y 0| ≤ A + |x 0 * y 0| :=
        le_trans (abs_add_le _ _) (add_le_add hs le_rfl)
      have hA' : 0 ≤ A + |x 0 * y 0| := add_nonneg hA (abs_nonneg _)
      have hvalid' : (((q + 1) + m : ℕ) : ℝ) * fp.u < 1 := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hvalid
      have htail := ih (q + 1) (by omega) hvalid'
        (fun i ↦ x i.succ) (fun i ↦ y i.succ)
        (fp.fl_add a (fp.fl_mul (x 0) (y 0)))
        (s + x 0 * y 0) (A + |x 0 * y 0|) hstep hs' hA'
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, add_assoc] using htail

private lemma p28_rounded_dot_error
    (fp : P28FPModel) (n : ℕ) (x y : Fin n → ℝ)
    (hvalid : P28GammaValid fp.u n) :
    |p28RoundedDotProduct fp n x y - ∑ k, x k * y k| ≤
      p28Gamma fp.u n * ∑ k, |x k| * |y k| := by
  cases n with
  | zero => simp [p28RoundedDotProduct]
  | succ m =>
      have hv : fp.u < 1 := by
        have hle : fp.u ≤ ((m + 1 : ℕ) : ℝ) * fp.u := by
          have hc : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by norm_num
          simpa using mul_le_mul_of_nonneg_right hc fp.u_nonneg
        exact lt_of_le_of_lt hle hvalid
      obtain ⟨d, hd, hmul⟩ := fp.model_mul (x 0) (y 0)
      have hinit :
          |fp.fl_mul (x 0) (y 0) - x 0 * y 0| ≤
            p28Gamma fp.u 1 * |x 0 * y 0| := by
        rw [hmul]
        have heq : x 0 * y 0 * (1 + d) - x 0 * y 0 = (x 0 * y 0) * d := by ring
        rw [heq, abs_mul]
        calc
          |x 0 * y 0| * |d| ≤ |x 0 * y 0| * fp.u :=
            mul_le_mul_of_nonneg_left hd (abs_nonneg _)
          _ ≤ |x 0 * y 0| * p28Gamma fp.u 1 :=
            mul_le_mul_of_nonneg_left (p28_gamma_one_ge fp.u fp.u_nonneg hv) (abs_nonneg _)
          _ = p28Gamma fp.u 1 * |x 0 * y 0| := mul_comm _ _
      have hvfold : (((1 + m : ℕ) : ℝ) * fp.u < 1) := by
        simpa [P28GammaValid, Nat.add_comm] using hvalid
      have hfold := p28_rounded_fold_bound fp m 1 (by omega) hvfold
        (fun i ↦ x i.succ) (fun i ↦ y i.succ)
        (fp.fl_mul (x 0) (y 0)) (x 0 * y 0) |x 0 * y 0|
        hinit le_rfl (abs_nonneg _)
      simp only [p28RoundedDotProduct]
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simpa [Nat.add_comm, abs_mul, mul_add, add_mul] using hfold

/-- P28-T1: the forward-error term from forming `XXᵀX` in equation (6.6). -/
theorem p28_t1_newton_schulz_triple_product_error
    (fp : P28FPModel) (n : ℕ) (X : P28RealMatrix n)
    (hvalid : P28GammaValid fp.u n) :
    ∀ i j,
      |p28RoundedGramTriple fp X i j - p28ExactGramTriple X i j| ≤
        p28GramTripleErrorMajorant fp X i j := by
  -- PROOF_START P28-T1-H001
  intro i j
  let R := p28RoundedMatMul fp X (p28Transpose X)
  let G := p28MatMul X (p28Transpose X)
  have hout := p28_rounded_dot_error fp n (fun k ↦ R i k) (fun k ↦ X k j) hvalid
  have hinner : ∀ k,
      |R i k - G i k| ≤
        p28Gamma fp.u n * ∑ l, |X i l| * |X k l| := by
    intro k
    simpa [R, G, p28RoundedMatMul, p28MatMul, p28Transpose] using
      (p28_rounded_dot_error fp n (X i) (fun l ↦ X k l) hvalid)
  have htransport :
      |∑ k, R i k * X k j - ∑ k, G i k * X k j| ≤
        p28Gamma fp.u n *
          ∑ k, (∑ l, |X i l| * |X k l|) * |X k j| := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ k, (R i k * X k j - G i k * X k j)| ≤
          ∑ k, |R i k * X k j - G i k * X k j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k, |R i k - G i k| * |X k j| := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [← sub_mul, abs_mul]
      _ ≤ ∑ k,
          (p28Gamma fp.u n * ∑ l, |X i l| * |X k l|) * |X k j| := by
        gcongr with k
        exact hinner k
      _ = p28Gamma fp.u n *
          ∑ k, (∑ l, |X i l| * |X k l|) * |X k j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
  change |p28RoundedDotProduct fp n (R i) (fun k ↦ X k j) -
      ∑ k, G i k * X k j| ≤ _
  calc
    |p28RoundedDotProduct fp n (R i) (fun k ↦ X k j) -
        ∑ k, G i k * X k j| ≤
      |p28RoundedDotProduct fp n (R i) (fun k ↦ X k j) -
        ∑ k, R i k * X k j| +
      |∑ k, R i k * X k j - ∑ k, G i k * X k j| := by
        exact abs_sub_le _ _ _
    _ ≤ p28Gamma fp.u n * (∑ k, |R i k| * |X k j|) +
        p28Gamma fp.u n *
          ∑ k, (∑ l, |X i l| * |X k l|) * |X k j| :=
      add_le_add hout htransport
    _ = p28GramTripleErrorMajorant fp X i j := by
      rfl

end HighamBench
