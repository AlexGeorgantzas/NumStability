import HighamBench.P28Definitions

namespace HighamBench

private lemma p28_fl_mul_error (fp : P28FPModel) (a b : ℝ) :
    |fp.fl_mul a b - a * b| ≤ fp.u * |a * b| := by
  rcases fp.model_mul a b with ⟨δ, hδ, hfl⟩
  rw [hfl, show a * b * (1 + δ) - a * b = a * b * δ by ring, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (a * b))

private lemma p28_fl_add_error (fp : P28FPModel) (a b : ℝ) :
    |fp.fl_add a b - (a + b)| ≤ fp.u * |a + b| := by
  rcases fp.model_add a b with ⟨δ, hδ, hfl⟩
  rw [hfl, show (a + b) * (1 + δ) - (a + b) = (a + b) * δ by ring,
    abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (a + b))

private lemma p28_fl_mul_abs (fp : P28FPModel) (a b : ℝ) :
    |fp.fl_mul a b| ≤ (1 + fp.u) * |a * b| := by
  have h := p28_fl_mul_error fp a b
  have ht := abs_add_le (fp.fl_mul a b - a * b) (a * b)
  rw [sub_add_cancel] at ht
  nlinarith [abs_nonneg (fp.fl_mul a b - a * b), abs_nonneg (a * b)]

private lemma p28_gamma_nonneg (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hvalid : P28GammaValid u k) : 0 ≤ p28Gamma u k := by
  rw [p28Gamma]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (le_of_lt (sub_pos.mpr hvalid))

private lemma p28_dot_error
    (fp : P28FPModel) (n : ℕ) (x y : Fin n → ℝ)
    (hvalid : P28GammaValid fp.u n) :
    |p28RoundedDotProduct fp n x y - ∑ k, x k * y k| ≤
      p28Gamma fp.u n * ∑ k, |x k * y k| := by
  induction n with
  | zero =>
      simp [p28RoundedDotProduct, p28Gamma]
  | succ n ih =>
      cases n with
      | zero =>
          have hu_lt : fp.u < 1 := by
            simpa [P28GammaValid] using hvalid
          have hden : 0 < 1 - fp.u := sub_pos.mpr hu_lt
          have hu_gamma : fp.u ≤ p28Gamma fp.u 1 := by
            rw [p28Gamma]
            norm_num
            apply (le_div_iff₀ hden).2
            nlinarith [sq_nonneg fp.u]
          simpa [p28RoundedDotProduct, Fin.sum_univ_succ] using
            (le_trans (p28_fl_mul_error fp (x 0) (y 0))
              (mul_le_mul_of_nonneg_right hu_gamma (abs_nonneg _)))
      | succ m =>
          let x' : Fin (m + 1) → ℝ := fun k ↦ x k.castSucc
          let y' : Fin (m + 1) → ℝ := fun k ↦ y k.castSucc
          let old : ℝ := p28RoundedDotProduct fp (m + 1) x' y'
          let s : ℝ := ∑ k, x' k * y' k
          let S : ℝ := ∑ k, |x' k * y' k|
          let t : ℝ := x (Fin.last (m + 1)) * y (Fin.last (m + 1))
          let T : ℝ := |t|
          let mulLast : ℝ := fp.fl_mul (x (Fin.last (m + 1))) (y (Fin.last (m + 1)))
          let result : ℝ := fp.fl_add old mulLast
          have hvalid' : P28GammaValid fp.u (m + 1) := by
            rw [P28GammaValid] at hvalid ⊢
            norm_num at hvalid ⊢
            nlinarith [fp.u_nonneg]
          have hold : |old - s| ≤ p28Gamma fp.u (m + 1) * S := by
            exact ih x' y' hvalid'
          have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
          have hT : 0 ≤ T := abs_nonneg _
          have hgamma : 0 ≤ p28Gamma fp.u (m + 1) :=
            p28_gamma_nonneg fp.u (m + 1) fp.u_nonneg hvalid'
          have hs_abs : |s| ≤ S := by
            exact Finset.abs_sum_le_sum_abs (f := fun k ↦ x' k * y' k) Finset.univ
          have hold_abs : |old| ≤ (1 + p28Gamma fp.u (m + 1)) * S := by
            have htri := abs_add_le (old - s) s
            rw [sub_add_cancel] at htri
            nlinarith [abs_nonneg (old - s), abs_nonneg s]
          have hmul_err : |mulLast - t| ≤ fp.u * T := by
            exact p28_fl_mul_error fp _ _
          have hmul_abs : |mulLast| ≤ (1 + fp.u) * T := by
            exact p28_fl_mul_abs fp _ _
          have hadd_err : |result - (old + mulLast)| ≤ fp.u * |old + mulLast| := by
            exact p28_fl_add_error fp _ _
          have hsum_abs : |old + mulLast| ≤ |old| + |mulLast| := abs_add_le _ _
          have hdecomp :
              |result - (s + t)| ≤
                |result - (old + mulLast)| + |old - s| + |mulLast - t| := by
            calc
              |result - (s + t)| ≤
                  |result - (old + mulLast)| + |(old + mulLast) - (s + t)| :=
                    abs_sub_le _ _ _
              _ ≤ |result - (old + mulLast)| + (|old - s| + |mulLast - t|) := by
                    gcongr
                    convert abs_add_le (old - s) (mulLast - t) using 1 <;> ring
              _ = |result - (old + mulLast)| + |old - s| + |mulLast - t| := by ring
          have hraw :
              |result - (s + t)| ≤
                (p28Gamma fp.u (m + 1) + fp.u *
                    (1 + p28Gamma fp.u (m + 1))) * S +
                  (2 * fp.u + fp.u ^ 2) * T := by
            calc
              |result - (s + t)| ≤
                  |result - (old + mulLast)| + |old - s| + |mulLast - t| := hdecomp
              _ ≤ fp.u * (|old| + |mulLast|) +
                    p28Gamma fp.u (m + 1) * S + fp.u * T := by
                    gcongr
                    exact hadd_err.trans (mul_le_mul_of_nonneg_left hsum_abs fp.u_nonneg)
              _ ≤ fp.u * ((1 + p28Gamma fp.u (m + 1)) * S +
                    (1 + fp.u) * T) +
                    p28Gamma fp.u (m + 1) * S + fp.u * T := by
                    gcongr
                    exact fp.u_nonneg
              _ = (p28Gamma fp.u (m + 1) + fp.u *
                    (1 + p28Gamma fp.u (m + 1))) * S +
                  (2 * fp.u + fp.u ^ 2) * T := by ring
          have hcoeff_old :
              p28Gamma fp.u (m + 1) + fp.u *
                  (1 + p28Gamma fp.u (m + 1)) ≤
                p28Gamma fp.u (m + 2) := by
            rw [P28GammaValid] at hvalid' hvalid
            norm_num at hvalid' hvalid
            rw [p28Gamma, p28Gamma]
            norm_num
            have hd1 : 0 < 1 - ((m : ℝ) + 1) * fp.u := sub_pos.mpr hvalid'
            have hvalid2 : ((m : ℝ) + 2) * fp.u < 1 := by
              convert hvalid using 1 <;> ring
            have hd2 : 0 < 1 - ((m : ℝ) + 2) * fp.u := sub_pos.mpr hvalid2
            have heq :
                ((m : ℝ) + 1) * fp.u / (1 - ((m : ℝ) + 1) * fp.u) +
                    fp.u *
                      (1 + ((m : ℝ) + 1) * fp.u /
                        (1 - ((m : ℝ) + 1) * fp.u)) =
                  ((m : ℝ) + 2) * fp.u / (1 - ((m : ℝ) + 1) * fp.u) := by
              field_simp [ne_of_gt hd1]
              ring
            rw [heq]
            apply div_le_div_of_nonneg_left
            · exact mul_nonneg (by positivity) fp.u_nonneg
            · exact hd2
            · nlinarith [fp.u_nonneg]
          have hcoeff_new : 2 * fp.u + fp.u ^ 2 ≤ p28Gamma fp.u (m + 2) := by
            rw [P28GammaValid] at hvalid
            norm_num at hvalid
            rw [p28Gamma]
            norm_num
            have hvalid2 : ((m : ℝ) + 2) * fp.u < 1 := by
              convert hvalid using 1 <;> ring
            have hd2 : 0 < 1 - ((m : ℝ) + 2) * fp.u := sub_pos.mpr hvalid2
            apply (le_div_iff₀ hd2).2
            have hm0 : 0 ≤ (m : ℝ) * fp.u :=
              mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg
            have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
            have hm1 : 0 ≤ (2 * ((m : ℝ) + 2) - 1) * fp.u ^ 2 :=
              mul_nonneg (by nlinarith [hmnonneg]) (sq_nonneg fp.u)
            have hm2 : 0 ≤ ((m : ℝ) + 2) * (fp.u ^ 2 * fp.u) :=
              mul_nonneg (by positivity) (mul_nonneg (sq_nonneg fp.u) fp.u_nonneg)
            nlinarith
          have hfinal :
              |result - (s + t)| ≤ p28Gamma fp.u (m + 2) * (S + T) := by
            calc
              |result - (s + t)| ≤
                  (p28Gamma fp.u (m + 1) + fp.u *
                      (1 + p28Gamma fp.u (m + 1))) * S +
                    (2 * fp.u + fp.u ^ 2) * T := hraw
              _ ≤ p28Gamma fp.u (m + 2) * S +
                    p28Gamma fp.u (m + 2) * T := by gcongr
              _ = p28Gamma fp.u (m + 2) * (S + T) := by ring
          simpa [result, old, mulLast, s, S, t, T, x', y', p28RoundedDotProduct,
            Fin.foldl_succ_last, Fin.sum_univ_castSucc] using hfinal

/-- P28-T1: the forward-error term from forming `XXᵀX` in equation (6.6). -/
theorem p28_t1_newton_schulz_triple_product_error
    (fp : P28FPModel) (n : ℕ) (X : P28RealMatrix n)
    (hvalid : P28GammaValid fp.u n) :
    ∀ i j,
      |p28RoundedGramTriple fp X i j - p28ExactGramTriple X i j| ≤
        p28GramTripleErrorMajorant fp X i j := by
  -- PROOF_START P28-T1-H001
  intro i j
  let Ahat : Fin n → ℝ := fun k ↦
    p28RoundedMatMul fp X (p28Transpose X) i k
  let A : Fin n → ℝ := fun k ↦ ∑ l, X i l * X k l
  have hgamma : 0 ≤ p28Gamma fp.u n :=
    p28_gamma_nonneg fp.u n fp.u_nonneg hvalid
  have houter :
      |p28RoundedGramTriple fp X i j - ∑ k, Ahat k * X k j| ≤
        p28Gamma fp.u n * ∑ k, |Ahat k| * |X k j| := by
    simpa only [p28RoundedGramTriple, p28RoundedMatMul, Ahat, abs_mul] using
      p28_dot_error fp n Ahat (fun k ↦ X k j) hvalid
  have hinner (k : Fin n) :
      |Ahat k - A k| ≤
        p28Gamma fp.u n * ∑ l, |X i l| * |X k l| := by
    simpa only [Ahat, A, p28RoundedMatMul, p28Transpose, abs_mul] using
      p28_dot_error fp n (X i) (fun l ↦ X k l) hvalid
  have htransport :
      |(∑ k, Ahat k * X k j) - ∑ k, A k * X k j| ≤
        p28Gamma fp.u n *
          ∑ k, (∑ l, |X i l| * |X k l|) * |X k j| := by
    calc
      |(∑ k, Ahat k * X k j) - ∑ k, A k * X k j| =
          |∑ k, (Ahat k - A k) * X k j| := by
            congr 1
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ ≤ ∑ k, |(Ahat k - A k) * X k j| :=
        Finset.abs_sum_le_sum_abs (f := fun k ↦ (Ahat k - A k) * X k j) Finset.univ
      _ = ∑ k, |Ahat k - A k| * |X k j| := by
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
  have htriangle :
      |p28RoundedGramTriple fp X i j - ∑ k, A k * X k j| ≤
        |p28RoundedGramTriple fp X i j - ∑ k, Ahat k * X k j| +
          |(∑ k, Ahat k * X k j) - ∑ k, A k * X k j| :=
    abs_sub_le _ _ _
  have htotal := htriangle.trans (add_le_add houter htransport)
  simpa only [p28ExactGramTriple, p28MatMul, p28Transpose, A,
    p28GramTripleErrorMajorant] using htotal

end HighamBench
