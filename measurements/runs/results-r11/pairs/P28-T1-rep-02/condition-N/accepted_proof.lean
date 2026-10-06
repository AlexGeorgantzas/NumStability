import HighamBench.P28Definitions

namespace HighamBench

lemma p28RoundedDotProduct_succ_last
    (fp : P28FPModel) (n : ℕ) (x y : Fin (n + 2) → ℝ) :
    p28RoundedDotProduct fp (n + 2) x y =
      fp.fl_add
        (p28RoundedDotProduct fp (n + 1)
          (fun i ↦ x i.castSucc) (fun i ↦ y i.castSucc))
        (fp.fl_mul (x (Fin.last (n + 1))) (y (Fin.last (n + 1)))) := by
  simp only [p28RoundedDotProduct, Fin.foldl_succ_last]
  congr 1

lemma p28GammaValid_mono {u : ℝ} (hu : 0 ≤ u) {m n : ℕ}
    (hmn : m ≤ n) (h : P28GammaValid u n) : P28GammaValid u m := by
  unfold P28GammaValid at *
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (mod_cast hmn) hu) h

lemma p28Gamma_nonneg {u : ℝ} (hu : 0 ≤ u) {n : ℕ}
    (h : P28GammaValid u n) : 0 ≤ p28Gamma u n := by
  unfold p28Gamma P28GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (le_of_lt (sub_pos.mpr h))

lemma p28Gamma_step_old (u : ℝ) (hu : 0 ≤ u) (n : ℕ)
    (h : P28GammaValid u (n + 1)) :
    (1 + u) * p28Gamma u n + u ≤ p28Gamma u (n + 1) := by
  have hn := p28GammaValid_mono hu (Nat.le_succ n) h
  have dn : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hn
  have dns : 0 < 1 - ((n + 1 : ℕ) : ℝ) * u := sub_pos.mpr h
  unfold p28Gamma
  have dns' : 0 < 1 - ((n : ℝ) + 1) * u := by
    simpa [Nat.cast_add, Nat.cast_one] using dns
  norm_num [Nat.cast_add, Nat.cast_one] at ⊢
  have hid :
      (1 + u) * ((n : ℝ) * u / (1 - (n : ℝ) * u)) + u =
        (((n : ℝ) + 1) * u) / (1 - (n : ℝ) * u) := by
    have dne : 1 - u * (n : ℝ) ≠ 0 := by nlinarith
    field_simp [dne]
    ring
  rw [hid]
  rw [div_le_div_iff₀ dn dns']
  have hnum : 0 ≤ ((n : ℝ) + 1) * u :=
    mul_nonneg (by positivity) hu
  nlinarith

lemma p28Gamma_step_new (u : ℝ) (hu : 0 ≤ u) (n : ℕ)
    (hn : 1 ≤ n) (h : P28GammaValid u (n + 1)) :
    u * (2 + u) ≤ p28Gamma u (n + 1) := by
  have dns : 0 < 1 - ((n + 1 : ℕ) : ℝ) * u := sub_pos.mpr h
  unfold p28Gamma
  have dns' : 0 < 1 - ((n : ℝ) + 1) * u := by
    simpa [Nat.cast_add, Nat.cast_one] using dns
  norm_num [Nat.cast_add, Nat.cast_one] at ⊢
  rw [le_div_iff₀ dns']
  have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hfirst : 0 ≤ u * ((n : ℝ) - 1) :=
    mul_nonneg hu (by linarith)
  have hsecond : 0 ≤ (2 * (n : ℝ) + 1) * u ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg u)
  have hthird : 0 ≤ (((n : ℝ) + 1) * u) * u ^ 2 :=
    mul_nonneg (mul_nonneg (by positivity) hu) (sq_nonneg u)
  nlinarith

lemma p28_two_factor_error {u a b : ℝ} (hu : 0 ≤ u)
    (ha : |a| ≤ u) (hb : |b| ≤ u) :
    |(1 + a) * (1 + b) - 1| ≤ u * (2 + u) := by
  have hab : |a * b| ≤ u * u := by
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg b) hu
  calc
    |(1 + a) * (1 + b) - 1| = |a + b + a * b| := by congr 1 <;> ring
    _ ≤ |a + b| + |a * b| := abs_add_le _ _
    _ ≤ (|a| + |b|) + |a * b| :=
      add_le_add (abs_add_le a b) (le_refl _)
    _ ≤ u * (2 + u) := by nlinarith

lemma p28RoundedDotProduct_error
    (fp : P28FPModel) (n : ℕ) (x y : Fin n → ℝ)
    (hvalid : P28GammaValid fp.u n) :
    |p28RoundedDotProduct fp n x y - ∑ k, x k * y k| ≤
      p28Gamma fp.u n * ∑ k, |x k| * |y k| := by
  induction n using Nat.twoStepInduction with
  | zero =>
      simp [p28RoundedDotProduct, p28Gamma]
  | one =>
      rcases fp.model_mul (x 0) (y 0) with ⟨d, hd, hmul⟩
      have hu_gamma : fp.u ≤ p28Gamma fp.u 1 := by
        simpa [p28Gamma] using
          (p28Gamma_step_old fp.u fp.u_nonneg 0 hvalid)
      have herr :
          p28RoundedDotProduct fp 1 x y - ∑ k, x k * y k =
            (x 0 * y 0) * d := by
        simp [p28RoundedDotProduct, hmul, Fin.sum_univ_succ]
        ring
      rw [herr, abs_mul, abs_mul]
      have hxy : 0 ≤ |x 0| * |y 0| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
      calc
        |x 0| * |y 0| * |d| ≤ |x 0| * |y 0| * fp.u :=
          mul_le_mul_of_nonneg_left hd hxy
        _ ≤ |x 0| * |y 0| * p28Gamma fp.u 1 :=
          mul_le_mul_of_nonneg_left hu_gamma hxy
        _ = p28Gamma fp.u 1 * ∑ k : Fin 1, |x k| * |y k| := by
          simp [Fin.sum_univ_succ]
          ring
  | more n _ ih =>
      let xp : Fin (n + 1) → ℝ := fun k ↦ x k.castSucc
      let yp : Fin (n + 1) → ℝ := fun k ↦ y k.castSucc
      let r : ℝ := p28RoundedDotProduct fp (n + 1) xp yp
      let s : ℝ := ∑ k, xp k * yp k
      let c : ℝ := x (Fin.last (n + 1)) * y (Fin.last (n + 1))
      let A : ℝ := ∑ k, |xp k| * |yp k|
      have hprevvalid : P28GammaValid fp.u (n + 1) :=
        p28GammaValid_mono fp.u_nonneg (by omega) hvalid
      have hpreverr : |r - s| ≤ p28Gamma fp.u (n + 1) * A := by
        exact ih xp yp hprevvalid
      rcases fp.model_mul (x (Fin.last (n + 1)))
          (y (Fin.last (n + 1))) with ⟨dm, hdm, hmul⟩
      rcases fp.model_add r
          (fp.fl_mul (x (Fin.last (n + 1)))
            (y (Fin.last (n + 1)))) with ⟨da, hda, hadd⟩
      have hrounded :
          p28RoundedDotProduct fp (n + 2) x y =
            (r + c * (1 + dm)) * (1 + da) := by
        rw [p28RoundedDotProduct_succ_last, hadd, hmul]
      have hexact : (∑ k, x k * y k) = s + c := by
        rw [Fin.sum_univ_castSucc]
      have hA : 0 ≤ A := by
        dsimp [A]
        positivity
      have hs : |s| ≤ A := by
        dsimp [s, A]
        calc
          |∑ k, xp k * yp k| ≤ ∑ k, |xp k * yp k| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = ∑ k, |xp k| * |yp k| := by
            apply Finset.sum_congr rfl
            intro k _
            rw [abs_mul]
      have hg : 0 ≤ p28Gamma fp.u (n + 1) :=
        p28Gamma_nonneg fp.u_nonneg hprevvalid
      have hOne : |1 + da| ≤ 1 + fp.u := by
        calc
          |1 + da| ≤ |(1 : ℝ)| + |da| := abs_add_le _ _
          _ ≤ 1 + fp.u := by simpa using add_le_add_left hda 1
      have hfac : |(1 + dm) * (1 + da) - 1| ≤ fp.u * (2 + fp.u) :=
        p28_two_factor_error fp.u_nonneg hdm hda
      have ht1 :
          |r - s| * |1 + da| ≤
            (p28Gamma fp.u (n + 1) * A) * (1 + fp.u) := by
        exact mul_le_mul hpreverr hOne (abs_nonneg _) (mul_nonneg hg hA)
      have ht2 : |s| * |da| ≤ A * fp.u := by
        exact mul_le_mul hs hda (abs_nonneg _) hA
      have ht3 : |c| * |(1 + dm) * (1 + da) - 1| ≤
          |c| * (fp.u * (2 + fp.u)) :=
        mul_le_mul_of_nonneg_left hfac (abs_nonneg _)
      rw [hrounded, hexact]
      calc
        |(r + c * (1 + dm)) * (1 + da) - (s + c)| =
            |(r - s) * (1 + da) + s * da +
              c * ((1 + dm) * (1 + da) - 1)| := by
                congr 1 <;> ring
        _ ≤ |(r - s) * (1 + da) + s * da| +
              |c * ((1 + dm) * (1 + da) - 1)| := abs_add_le _ _
        _ ≤ (|(r - s) * (1 + da)| + |s * da|) +
              |c * ((1 + dm) * (1 + da) - 1)| :=
                add_le_add (abs_add_le _ _) (le_refl _)
        _ = (|r - s| * |1 + da| + |s| * |da|) +
              |c| * |(1 + dm) * (1 + da) - 1| := by
                rw [abs_mul, abs_mul, abs_mul]
        _ ≤ ((p28Gamma fp.u (n + 1) * A) * (1 + fp.u) + A * fp.u) +
              |c| * (fp.u * (2 + fp.u)) := by
                exact add_le_add (add_le_add ht1 ht2) ht3
        _ ≤ p28Gamma fp.u (n + 2) * A +
              p28Gamma fp.u (n + 2) * |c| := by
                have hold := p28Gamma_step_old fp.u fp.u_nonneg (n + 1) hvalid
                have hnew := p28Gamma_step_new fp.u fp.u_nonneg (n + 1)
                  (by omega) hvalid
                have hleft :
                    ((p28Gamma fp.u (n + 1) * A) * (1 + fp.u) + A * fp.u) ≤
                      p28Gamma fp.u (n + 2) * A := by
                  rw [show (p28Gamma fp.u (n + 1) * A) * (1 + fp.u) + A * fp.u =
                    ((1 + fp.u) * p28Gamma fp.u (n + 1) + fp.u) * A by ring]
                  exact mul_le_mul_of_nonneg_right hold hA
                have hright : |c| * (fp.u * (2 + fp.u)) ≤
                    p28Gamma fp.u (n + 2) * |c| := by
                  rw [mul_comm |c|]
                  exact mul_le_mul_of_nonneg_right hnew (abs_nonneg c)
                exact add_le_add hleft hright
        _ = p28Gamma fp.u (n + 2) *
              ∑ k : Fin (n + 2), |x k| * |y k| := by
                rw [Fin.sum_univ_castSucc]
                dsimp [A, c, xp, yp]
                rw [abs_mul]
                ring

/-- P28-T1: the forward-error term from forming `XXᵀX` in equation (6.6). -/
theorem p28_t1_newton_schulz_triple_product_error
    (fp : P28FPModel) (n : ℕ) (X : P28RealMatrix n)
    (hvalid : P28GammaValid fp.u n) :
    ∀ i j,
      |p28RoundedGramTriple fp X i j - p28ExactGramTriple X i j| ≤
        p28GramTripleErrorMajorant fp X i j := by
  -- PROOF_START P28-T1-H001
  intro i j
  simp only [p28RoundedGramTriple, p28ExactGramTriple, p28MatMul,
    p28RoundedMatMul, p28Transpose, p28GramTripleErrorMajorant]
  have houter :
      |(p28RoundedDotProduct fp n
          (p28RoundedMatMul fp X (p28Transpose X) i) (fun k ↦ X k j)) -
          ∑ k, p28RoundedDotProduct fp n (X i) (fun l ↦ X k l) * X k j| ≤
        p28Gamma fp.u n *
          ∑ k, |p28RoundedDotProduct fp n (X i) (fun l ↦ X k l)| * |X k j| := by
    simpa only [p28RoundedMatMul, p28Transpose] using
      (p28RoundedDotProduct_error fp n
        (p28RoundedMatMul fp X (p28Transpose X) i) (fun k ↦ X k j) hvalid)
  have hinner (k : Fin n) :
      |p28RoundedDotProduct fp n (X i) (fun l ↦ X k l) -
          ∑ l, X i l * X k l| ≤
        p28Gamma fp.u n * ∑ l, |X i l| * |X k l| := by
    exact p28RoundedDotProduct_error fp n (X i) (fun l ↦ X k l) hvalid
  have htransport :
      |(∑ k, p28RoundedDotProduct fp n (X i) (fun l ↦ X k l) * X k j) -
          ∑ k, (∑ l, X i l * X k l) * X k j| ≤
        p28Gamma fp.u n *
          ∑ k, (∑ l, |X i l| * |X k l|) * |X k j| := by
    calc
      |(∑ k, p28RoundedDotProduct fp n (X i) (fun l ↦ X k l) * X k j) -
          ∑ k, (∑ l, X i l * X k l) * X k j| =
          |∑ k, (p28RoundedDotProduct fp n (X i) (fun l ↦ X k l) -
            ∑ l, X i l * X k l) * X k j| := by
              congr 1
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro k _
              ring
      _ ≤ ∑ k, |(p28RoundedDotProduct fp n (X i) (fun l ↦ X k l) -
            ∑ l, X i l * X k l) * X k j| :=
              Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k, |p28RoundedDotProduct fp n (X i) (fun l ↦ X k l) -
            ∑ l, X i l * X k l| * |X k j| := by
              apply Finset.sum_congr rfl
              intro k _
              rw [abs_mul]
      _ ≤ ∑ k, (p28Gamma fp.u n * ∑ l, |X i l| * |X k l|) *
            |X k j| := by
              apply Finset.sum_le_sum
              intro k _
              exact mul_le_mul_of_nonneg_right (hinner k) (abs_nonneg _)
      _ = p28Gamma fp.u n *
          ∑ k, (∑ l, |X i l| * |X k l|) * |X k j| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
  exact le_trans
    (abs_sub_le
      (p28RoundedDotProduct fp n
        (p28RoundedMatMul fp X (p28Transpose X) i) (fun k ↦ X k j))
      (∑ k, p28RoundedDotProduct fp n (X i) (fun l ↦ X k l) * X k j)
      (∑ k, (∑ l, X i l * X k l) * X k j))
    (add_le_add houter htransport)

end HighamBench
