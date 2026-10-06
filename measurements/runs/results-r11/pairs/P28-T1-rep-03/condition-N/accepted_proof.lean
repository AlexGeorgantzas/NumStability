import HighamBench.P28Definitions

namespace HighamBench

private lemma p28_pow_mul_one_sub_le_one (u : ℝ) (hu : 0 ≤ u) :
    ∀ n : ℕ, (1 + u) ^ n * (1 - (n : ℝ) * u) ≤ 1 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hpow : 0 ≤ (1 + u) ^ n := by positivity
      have hterm : 0 ≤ (n + 1 : ℝ) * u ^ 2 * (1 + u) ^ n := by positivity
      have heq :
          (1 + u) ^ (n + 1) * (1 - (n + 1 : ℕ) * u) =
            (1 + u) ^ n * (1 - (n : ℝ) * u) -
              (n + 1 : ℝ) * u ^ 2 * (1 + u) ^ n := by
        push_cast
        rw [pow_succ]
        ring
      rw [heq]
      linarith

private lemma p28_pow_error_le_gamma (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (hvalid : P28GammaValid u n) :
    (1 + u) ^ n - 1 ≤ p28Gamma u n := by
  have hden : 0 < 1 - (n : ℝ) * u := by
    exact sub_pos.mpr hvalid
  rw [p28Gamma]
  apply (le_div_iff₀ hden).2
  have hp := p28_pow_mul_one_sub_le_one u hu n
  nlinarith

private lemma p28_accumulation_step (fp : P28FPModel) (q : ℕ)
    (z s A x y : ℝ) (hq : 1 ≤ q) (hA : 0 ≤ A) (hs : |s| ≤ A)
    (hz : |z - s| ≤ ((1 + fp.u) ^ q - 1) * A) :
    |fp.fl_add z (fp.fl_mul x y) - (s + x * y)| ≤
      ((1 + fp.u) ^ (q + 1) - 1) * (A + |x * y|) := by
  rcases fp.model_mul x y with ⟨δm, hδm, hmul⟩
  rcases fp.model_add z (fp.fl_mul x y) with ⟨δa, hδa, hadd⟩
  have hu := fp.u_nonneg
  have hbase : 1 ≤ 1 + fp.u := by linarith
  have hfac : |1 + δa| ≤ 1 + fp.u := by
    calc
      |1 + δa| ≤ |(1 : ℝ)| + |δa| := abs_add_le _ _
      _ ≤ 1 + fp.u := by simpa using add_le_add_left hδa 1
  have hδmul : |δm * δa| ≤ fp.u * fp.u := by
    rw [abs_mul]
    exact mul_le_mul hδm hδa (abs_nonneg _) hu
  have hcoef : |(1 + δm) * (1 + δa) - 1| ≤ (1 + fp.u) ^ 2 - 1 := by
    have heq : (1 + δm) * (1 + δa) - 1 = δm + δa + δm * δa := by ring
    rw [heq]
    calc
      |δm + δa + δm * δa| ≤ |δm + δa| + |δm * δa| := abs_add_le _ _
      _ ≤ (|δm| + |δa|) + |δm * δa| :=
        add_le_add_left (abs_add_le _ _) _
      _ ≤ (fp.u + fp.u) + fp.u * fp.u :=
        add_le_add (add_le_add hδm hδa) hδmul
      _ = (1 + fp.u) ^ 2 - 1 := by ring
  have hbq : 0 ≤ (1 + fp.u) ^ q - 1 := by
    exact sub_nonneg.mpr (one_le_pow₀ hbase)
  have hbA : 0 ≤ ((1 + fp.u) ^ q - 1) * A := mul_nonneg hbq hA
  have hb2next : (1 + fp.u) ^ 2 - 1 ≤ (1 + fp.u) ^ (q + 1) - 1 := by
    apply sub_le_sub_right
    exact pow_le_pow_right₀ hbase (by omega)
  have heq :
      (z + (x * y) * (1 + δm)) * (1 + δa) - (s + x * y) =
        (1 + δa) * (z - s) + δa * s +
          (((1 + δm) * (1 + δa) - 1) * (x * y)) := by
    ring
  rw [hadd, hmul, heq]
  calc
    |(1 + δa) * (z - s) + δa * s +
        ((1 + δm) * (1 + δa) - 1) * (x * y)| ≤
        |(1 + δa) * (z - s) + δa * s| +
          |((1 + δm) * (1 + δa) - 1) * (x * y)| := abs_add_le _ _
    _ ≤ (|(1 + δa) * (z - s)| + |δa * s|) +
          |((1 + δm) * (1 + δa) - 1) * (x * y)| :=
        add_le_add_left (abs_add_le _ _) _
    _ = (|1 + δa| * |z - s| + |δa| * |s|) +
          |(1 + δm) * (1 + δa) - 1| * |x * y| := by
        simp only [abs_mul]
    _ ≤ ((1 + fp.u) * (((1 + fp.u) ^ q - 1) * A) + fp.u * A) +
          ((1 + fp.u) ^ 2 - 1) * |x * y| := by
        gcongr
    _ = ((1 + fp.u) ^ (q + 1) - 1) * A +
          ((1 + fp.u) ^ 2 - 1) * |x * y| := by
        rw [pow_succ]
        ring
    _ ≤ ((1 + fp.u) ^ (q + 1) - 1) * A +
          ((1 + fp.u) ^ (q + 1) - 1) * |x * y| := by
        exact add_le_add_right (mul_le_mul_of_nonneg_right hb2next (abs_nonneg _)) _
    _ = ((1 + fp.u) ^ (q + 1) - 1) * (A + |x * y|) := by ring

private lemma p28_foldl_error (fp : P28FPModel) :
    ∀ (m q : ℕ) (x y : Fin m → ℝ) (z s A : ℝ),
      1 ≤ q → 0 ≤ A → |s| ≤ A →
      |z - s| ≤ ((1 + fp.u) ^ q - 1) * A →
      |Fin.foldl m
          (fun acc i ↦ fp.fl_add acc (fp.fl_mul (x i) (y i))) z -
          (s + ∑ i, x i * y i)| ≤
        ((1 + fp.u) ^ (q + m) - 1) * (A + ∑ i, |x i * y i|) := by
  intro m
  induction m with
  | zero =>
      intro q x y z s A hq hA hs hz
      simpa using hz
  | succ m ih =>
      intro q x y z s A hq hA hs hz
      let z' := fp.fl_add z (fp.fl_mul (x 0) (y 0))
      let s' := s + x 0 * y 0
      let A' := A + |x 0 * y 0|
      have hA' : 0 ≤ A' := add_nonneg hA (abs_nonneg _)
      have hs' : |s'| ≤ A' := by
        dsimp [s', A']
        exact (abs_add_le _ _).trans (add_le_add_left hs _)
      have hz' : |z' - s'| ≤ ((1 + fp.u) ^ (q + 1) - 1) * A' := by
        exact p28_accumulation_step fp q z s A (x 0) (y 0) hq hA hs hz
      have hrest := ih (q + 1) (fun i ↦ x i.succ) (fun i ↦ y i.succ)
        z' s' A' (by omega) hA' hs' hz'
      rw [Fin.foldl_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
      simpa only [z', s', A', add_assoc, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using hrest

private lemma p28_rounded_dot_product_error (fp : P28FPModel) (n : ℕ)
    (hvalid : P28GammaValid fp.u n) (x y : Fin n → ℝ) :
    |p28RoundedDotProduct fp n x y - ∑ i, x i * y i| ≤
      p28Gamma fp.u n * ∑ i, |x i * y i| := by
  cases n with
  | zero => simp [p28RoundedDotProduct]
  | succ m =>
      rcases fp.model_mul (x 0) (y 0) with ⟨δ, hδ, hmul⟩
      have hfirst :
          |fp.fl_mul (x 0) (y 0) - x 0 * y 0| ≤
            ((1 + fp.u) ^ 1 - 1) * |x 0 * y 0| := by
        rw [hmul]
        have heq : (x 0 * y 0) * (1 + δ) - x 0 * y 0 = (x 0 * y 0) * δ := by ring
        rw [heq, abs_mul]
        have hmulbound := mul_le_mul_of_nonneg_left hδ (abs_nonneg (x 0 * y 0))
        calc
          |x 0 * y 0| * |δ| ≤ |x 0 * y 0| * fp.u := hmulbound
          _ = ((1 + fp.u) ^ 1 - 1) * |x 0 * y 0| := by
            rw [pow_one]
            ring
      have hfold := p28_foldl_error fp m 1
        (fun i ↦ x i.succ) (fun i ↦ y i.succ)
        (fp.fl_mul (x 0) (y 0)) (x 0 * y 0) |x 0 * y 0|
        (by omega) (abs_nonneg _) le_rfl hfirst
      have hbeta :
          (1 + fp.u) ^ (m + 1) - 1 ≤ p28Gamma fp.u (m + 1) :=
        p28_pow_error_le_gamma fp.u (m + 1) fp.u_nonneg hvalid
      have hsum_nonneg : 0 ≤ ∑ i : Fin (m + 1), |x i * y i| :=
        Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
      calc
        |p28RoundedDotProduct fp (m + 1) x y - ∑ i, x i * y i| ≤
            ((1 + fp.u) ^ (m + 1) - 1) * ∑ i, |x i * y i| := by
              simpa only [p28RoundedDotProduct, Fin.sum_univ_succ, add_assoc,
                Nat.add_comm] using hfold
        _ ≤ p28Gamma fp.u (m + 1) * ∑ i, |x i * y i| :=
          mul_le_mul_of_nonneg_right hbeta hsum_nonneg

/-- P28-T1: the forward-error term from forming `XXᵀX` in equation (6.6). -/
theorem p28_t1_newton_schulz_triple_product_error
    (fp : P28FPModel) (n : ℕ) (X : P28RealMatrix n)
    (hvalid : P28GammaValid fp.u n) :
    ∀ i j,
      |p28RoundedGramTriple fp X i j - p28ExactGramTriple X i j| ≤
        p28GramTripleErrorMajorant fp X i j := by
  -- PROOF_START P28-T1-H001
  intro i j
  have houter := p28_rounded_dot_product_error fp n hvalid
    (fun k ↦ p28RoundedMatMul fp X (p28Transpose X) i k) (fun k ↦ X k j)
  have houter' :
      |p28RoundedGramTriple fp X i j -
          ∑ k, p28RoundedMatMul fp X (p28Transpose X) i k * X k j| ≤
        p28Gamma fp.u n *
          ∑ k, |p28RoundedMatMul fp X (p28Transpose X) i k| * |X k j| := by
    simpa only [p28RoundedGramTriple, p28RoundedMatMul, abs_mul] using houter
  have hinner (k : Fin n) :
      |p28RoundedMatMul fp X (p28Transpose X) i k -
          p28MatMul X (p28Transpose X) i k| ≤
        p28Gamma fp.u n * ∑ l, |X i l| * |X k l| := by
    have h := p28_rounded_dot_product_error fp n hvalid
      (fun l ↦ X i l) (fun l ↦ p28Transpose X l k)
    simpa only [p28RoundedMatMul, p28MatMul, p28Transpose, abs_mul] using h
  have htransport :
      |∑ k, p28RoundedMatMul fp X (p28Transpose X) i k * X k j -
          ∑ k, p28MatMul X (p28Transpose X) i k * X k j| ≤
        p28Gamma fp.u n *
          ∑ k, (∑ l, |X i l| * |X k l|) * |X k j| := by
    calc
      |∑ k, p28RoundedMatMul fp X (p28Transpose X) i k * X k j -
          ∑ k, p28MatMul X (p28Transpose X) i k * X k j| =
          |∑ k, (p28RoundedMatMul fp X (p28Transpose X) i k -
            p28MatMul X (p28Transpose X) i k) * X k j| := by
              congr 1
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro k _
              ring
      _ ≤ ∑ k, |(p28RoundedMatMul fp X (p28Transpose X) i k -
            p28MatMul X (p28Transpose X) i k) * X k j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k, |p28RoundedMatMul fp X (p28Transpose X) i k -
            p28MatMul X (p28Transpose X) i k| * |X k j| := by
          apply Finset.sum_congr rfl
          intro k _
          rw [abs_mul]
      _ ≤ ∑ k, (p28Gamma fp.u n * ∑ l, |X i l| * |X k l|) * |X k j| := by
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_of_nonneg_right (hinner k) (abs_nonneg _)
      _ = p28Gamma fp.u n *
          ∑ k, (∑ l, |X i l| * |X k l|) * |X k j| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
  rw [p28ExactGramTriple, p28MatMul]
  calc
    |p28RoundedGramTriple fp X i j -
        ∑ k, p28MatMul X (p28Transpose X) i k * X k j| =
        |(p28RoundedGramTriple fp X i j -
            ∑ k, p28RoundedMatMul fp X (p28Transpose X) i k * X k j) +
          ((∑ k, p28RoundedMatMul fp X (p28Transpose X) i k * X k j) -
            ∑ k, p28MatMul X (p28Transpose X) i k * X k j)| := by ring
    _ ≤ |p28RoundedGramTriple fp X i j -
            ∑ k, p28RoundedMatMul fp X (p28Transpose X) i k * X k j| +
          |(∑ k, p28RoundedMatMul fp X (p28Transpose X) i k * X k j) -
            ∑ k, p28MatMul X (p28Transpose X) i k * X k j| := abs_add_le _ _
    _ ≤ p28Gamma fp.u n *
          (∑ k, |p28RoundedMatMul fp X (p28Transpose X) i k| * |X k j|) +
        p28Gamma fp.u n *
          ∑ k, (∑ l, |X i l| * |X k l|) * |X k j| :=
      add_le_add houter' htransport
    _ = p28GramTripleErrorMajorant fp X i j := rfl

end HighamBench
