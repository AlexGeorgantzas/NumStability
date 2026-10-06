import HighamBench.P28Definitions

namespace HighamBench

private lemma p28_gamma_step_old (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (hvalid : P28GammaValid u (n + 1)) :
    p28Gamma u n * (1 + u) + u ≤ p28Gamma u (n + 1) := by
  simp only [p28Gamma, P28GammaValid, Nat.cast_add, Nat.cast_one] at *
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd : 0 < 1 - (n : ℝ) * u := by nlinarith
  have hd' : 0 < 1 - ((n : ℝ) + 1) * u := by nlinarith
  have heq :
      (n : ℝ) * u / (1 - (n : ℝ) * u) * (1 + u) + u =
        ((n : ℝ) + 1) * u / (1 - (n : ℝ) * u) := by
    field_simp
    ring
  rw [heq]
  exact div_le_div_of_nonneg_left (by positivity) hd'
    (by nlinarith : 1 - ((n : ℝ) + 1) * u ≤ 1 - (n : ℝ) * u)

private lemma p28_gamma_step_new (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (hn : 1 ≤ n) (hvalid : P28GammaValid u (n + 1)) :
    u * (1 + u) + u ≤ p28Gamma u (n + 1) := by
  simp only [p28Gamma, P28GammaValid, Nat.cast_add, Nat.cast_one] at *
  have hnr : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hd : 0 < 1 - ((n : ℝ) + 1) * u := by nlinarith
  rw [le_div_iff₀ hd]
  have hc : 0 ≤ u * (1 + u) + u := by positivity
  have hdle : 1 - ((n : ℝ) + 1) * u ≤ 1 - 2 * u := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hnr) hu]
  calc
    (u * (1 + u) + u) * (1 - ((n : ℝ) + 1) * u) ≤
        (u * (1 + u) + u) * (1 - 2 * u) :=
      mul_le_mul_of_nonneg_left hdle hc
    _ ≤ 2 * u := by nlinarith [mul_nonneg hu (sq_nonneg u)]
    _ ≤ ((n : ℝ) + 1) * u := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hnr) hu]

private lemma p28_mul_error (fp : P28FPModel) (a b : ℝ) :
    |fp.fl_mul a b - a * b| ≤ fp.u * |a * b| := by
  obtain ⟨δ, hδ, hmul⟩ := fp.model_mul a b
  rw [hmul]
  have heq : a * b * (1 + δ) - a * b = (a * b) * δ := by ring
  rw [heq, abs_mul]
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_left hδ (abs_nonneg (a * b)))

private lemma p28_rounded_dot_succ (fp : P28FPModel) (n : ℕ)
    (x y : Fin (n + 1) → ℝ) :
    p28RoundedDotProduct fp (n + 1) x y =
      fp.fl_add
        (p28RoundedDotProduct fp n (fun i ↦ x i.castSucc) (fun i ↦ y i.castSucc))
        (fp.fl_mul (x (Fin.last n)) (y (Fin.last n))) := by
  cases n with
  | zero => simp [p28RoundedDotProduct, fp.fl_add_zero]
  | succ n =>
      simp only [p28RoundedDotProduct]
      rw [Fin.foldl_succ_last]
      congr 3 <;> simp

private lemma p28_accumulation_step (u : ℝ) (n : ℕ)
    (acc s m a S δ : ℝ) (hu : 0 ≤ u) (hn : 1 ≤ n)
    (hvalid : P28GammaValid u (n + 1))
    (hacc : |acc - s| ≤ p28Gamma u n * S)
    (hmul : |m - a| ≤ u * |a|) (hs : |s| ≤ S) (hS : 0 ≤ S)
    (hδ : |δ| ≤ u) :
    |(acc + m) * (1 + δ) - (s + a)| ≤
      p28Gamma u (n + 1) * (S + |a|) := by
  have hden : 0 < 1 - (n : ℝ) * u := by
    simp only [P28GammaValid, Nat.cast_add, Nat.cast_one] at hvalid
    have hnr : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hgamma : 0 ≤ p28Gamma u n := by
    rw [p28Gamma]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) hu) hden.le
  have hone : |1 + δ| ≤ 1 + u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le 1 δ
      _ ≤ 1 + u := by simpa using add_le_add_left hδ 1
  have hsa : |s + a| ≤ S + |a| := by
    nlinarith [abs_add_le s a]
  have hsplit :
      (acc + m) * (1 + δ) - (s + a) =
        (acc - s) * (1 + δ) + (m - a) * (1 + δ) + (s + a) * δ := by
    ring
  rw [hsplit]
  calc
    |(acc - s) * (1 + δ) + (m - a) * (1 + δ) + (s + a) * δ| ≤
        |acc - s| * |1 + δ| + |m - a| * |1 + δ| + |s + a| * |δ| := by
      have houter :=
        abs_add_le ((acc - s) * (1 + δ) + (m - a) * (1 + δ)) ((s + a) * δ)
      have hinner := abs_add_le ((acc - s) * (1 + δ)) ((m - a) * (1 + δ))
      simp only [abs_mul] at houter hinner
      nlinarith
    _ ≤ (p28Gamma u n * S) * (1 + u) +
        (u * |a|) * (1 + u) + (S + |a|) * u := by
      gcongr
    _ = (p28Gamma u n * (1 + u) + u) * S +
        (u * (1 + u) + u) * |a| := by ring
    _ ≤ p28Gamma u (n + 1) * S + p28Gamma u (n + 1) * |a| := by
      gcongr
      · exact p28_gamma_step_old u n hu hvalid
      · exact p28_gamma_step_new u n hu hn hvalid
    _ = p28Gamma u (n + 1) * (S + |a|) := by ring

private lemma p28_rounded_dot_product_error (fp : P28FPModel) :
    ∀ (n : ℕ) (x y : Fin n → ℝ), P28GammaValid fp.u n →
      |p28RoundedDotProduct fp n x y - ∑ k : Fin n, x k * y k| ≤
        p28Gamma fp.u n * ∑ k : Fin n, |x k| * |y k| := by
  intro n
  induction n with
  | zero =>
      intro x y hvalid
      simp [p28RoundedDotProduct, p28Gamma]
  | succ n ih =>
      intro x y hvalid
      by_cases hn0 : n = 0
      · subst n
        have hmul := p28_mul_error fp (x 0) (y 0)
        have hgamma := p28_gamma_step_old fp.u 0 fp.u_nonneg hvalid
        have hgamma' : fp.u ≤ p28Gamma fp.u (0 + 1) := by
          simpa [p28Gamma] using hgamma
        have hres : |fp.fl_mul (x 0) (y 0) - x 0 * y 0| ≤
            p28Gamma fp.u (0 + 1) * (|x 0| * |y 0|) := calc
          |fp.fl_mul (x 0) (y 0) - x 0 * y 0| ≤
              fp.u * |x 0 * y 0| := hmul
          _ = fp.u * (|x 0| * |y 0|) := by rw [abs_mul]
          _ ≤ p28Gamma fp.u (0 + 1) * (|x 0| * |y 0|) := by
            gcongr
        simpa [p28RoundedDotProduct] using hres
      · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        have hvalid_n : P28GammaValid fp.u n := by
          simp only [P28GammaValid, Nat.cast_add, Nat.cast_one] at hvalid ⊢
          have hnr : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
          nlinarith [mul_le_mul_of_nonneg_right hnr fp.u_nonneg]
        have hacc := ih (fun k ↦ x k.castSucc) (fun k ↦ y k.castSucc) hvalid_n
        have hmul := p28_mul_error fp (x (Fin.last n)) (y (Fin.last n))
        obtain ⟨δ, hδ, hadd⟩ := fp.model_add
          (p28RoundedDotProduct fp n (fun k ↦ x k.castSucc) (fun k ↦ y k.castSucc))
          (fp.fl_mul (x (Fin.last n)) (y (Fin.last n)))
        rw [p28_rounded_dot_succ, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, hadd]
        have hsum :
            |∑ k : Fin n, x k.castSucc * y k.castSucc| ≤
              ∑ k : Fin n, |x k.castSucc| * |y k.castSucc| := by
          simpa only [abs_mul] using
            (Finset.abs_sum_le_sum_abs (s := Finset.univ)
              (f := fun k : Fin n ↦ x k.castSucc * y k.castSucc))
        simpa only [abs_mul] using
          p28_accumulation_step fp.u n
            (p28RoundedDotProduct fp n (fun k ↦ x k.castSucc) (fun k ↦ y k.castSucc))
            (∑ k : Fin n, x k.castSucc * y k.castSucc)
            (fp.fl_mul (x (Fin.last n)) (y (Fin.last n)))
            (x (Fin.last n) * y (Fin.last n))
            (∑ k : Fin n, |x k.castSucc| * |y k.castSucc|) δ
            fp.u_nonneg hn hvalid hacc hmul hsum (by positivity) hδ

/-- P28-T1: the forward-error term from forming `XXᵀX` in equation (6.6). -/
theorem p28_t1_newton_schulz_triple_product_error
    (fp : P28FPModel) (n : ℕ) (X : P28RealMatrix n)
    (hvalid : P28GammaValid fp.u n) :
    ∀ i j,
      |p28RoundedGramTriple fp X i j - p28ExactGramTriple X i j| ≤
        p28GramTripleErrorMajorant fp X i j := by
  -- PROOF_START P28-T1-H001
  intro i j
  have houter :
      |p28RoundedGramTriple fp X i j -
          ∑ k : Fin n, p28RoundedMatMul fp X (p28Transpose X) i k * X k j| ≤
        p28Gamma fp.u n *
          ∑ k : Fin n, |p28RoundedMatMul fp X (p28Transpose X) i k| * |X k j| := by
    simpa only [p28RoundedGramTriple, p28RoundedMatMul] using
      p28_rounded_dot_product_error fp n
        (p28RoundedMatMul fp X (p28Transpose X) i) (fun k ↦ X k j) hvalid
  have hinner (k : Fin n) :
      |p28RoundedMatMul fp X (p28Transpose X) i k -
          ∑ l : Fin n, X i l * X k l| ≤
        p28Gamma fp.u n * ∑ l : Fin n, |X i l| * |X k l| := by
    simpa only [p28RoundedMatMul, p28Transpose] using
      p28_rounded_dot_product_error fp n (X i) (fun l ↦ X k l) hvalid
  have htransport :
      |(∑ k : Fin n, p28RoundedMatMul fp X (p28Transpose X) i k * X k j) -
          ∑ k : Fin n, (∑ l : Fin n, X i l * X k l) * X k j| ≤
        p28Gamma fp.u n *
          ∑ k : Fin n, (∑ l : Fin n, |X i l| * |X k l|) * |X k j| := by
    calc
      |(∑ k : Fin n, p28RoundedMatMul fp X (p28Transpose X) i k * X k j) -
          ∑ k : Fin n, (∑ l : Fin n, X i l * X k l) * X k j| =
          |∑ k : Fin n,
            (p28RoundedMatMul fp X (p28Transpose X) i k -
              ∑ l : Fin n, X i l * X k l) * X k j| := by
        congr 1
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ ∑ k : Fin n,
          |(p28RoundedMatMul fp X (p28Transpose X) i k -
            ∑ l : Fin n, X i l * X k l) * X k j| :=
        by
          simpa using
            (Finset.abs_sum_le_sum_abs (s := Finset.univ)
              (f := fun k : Fin n ↦
                (p28RoundedMatMul fp X (p28Transpose X) i k -
                  ∑ l : Fin n, X i l * X k l) * X k j))
      _ = ∑ k : Fin n,
          |p28RoundedMatMul fp X (p28Transpose X) i k -
            ∑ l : Fin n, X i l * X k l| * |X k j| := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [abs_mul]
      _ ≤ ∑ k : Fin n,
          (p28Gamma fp.u n * ∑ l : Fin n, |X i l| * |X k l|) * |X k j| := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_right (hinner k) (abs_nonneg (X k j))
      _ = p28Gamma fp.u n *
          ∑ k : Fin n, (∑ l : Fin n, |X i l| * |X k l|) * |X k j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
  have htotal :
      |p28RoundedGramTriple fp X i j -
          ∑ k : Fin n, (∑ l : Fin n, X i l * X k l) * X k j| ≤
        p28Gamma fp.u n *
            ∑ k : Fin n, |p28RoundedMatMul fp X (p28Transpose X) i k| * |X k j| +
          p28Gamma fp.u n *
            ∑ k : Fin n, (∑ l : Fin n, |X i l| * |X k l|) * |X k j| := by
    calc
      |p28RoundedGramTriple fp X i j -
          ∑ k : Fin n, (∑ l : Fin n, X i l * X k l) * X k j| =
          |(p28RoundedGramTriple fp X i j -
              ∑ k : Fin n, p28RoundedMatMul fp X (p28Transpose X) i k * X k j) +
            ((∑ k : Fin n, p28RoundedMatMul fp X (p28Transpose X) i k * X k j) -
              ∑ k : Fin n, (∑ l : Fin n, X i l * X k l) * X k j)| := by
        congr 1
        ring
      _ ≤
          |p28RoundedGramTriple fp X i j -
            ∑ k : Fin n, p28RoundedMatMul fp X (p28Transpose X) i k * X k j| +
          |(∑ k : Fin n, p28RoundedMatMul fp X (p28Transpose X) i k * X k j) -
            ∑ k : Fin n, (∑ l : Fin n, X i l * X k l) * X k j| := abs_add_le _ _
      _ ≤
          p28Gamma fp.u n *
              ∑ k : Fin n, |p28RoundedMatMul fp X (p28Transpose X) i k| * |X k j| +
            p28Gamma fp.u n *
              ∑ k : Fin n, (∑ l : Fin n, |X i l| * |X k l|) * |X k j| :=
        add_le_add houter htransport
  simpa only [p28ExactGramTriple, p28MatMul, p28Transpose,
    p28GramTripleErrorMajorant] using htotal

end HighamBench
