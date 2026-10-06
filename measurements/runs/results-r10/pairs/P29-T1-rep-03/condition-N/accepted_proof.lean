import HighamBench.P29Definitions

namespace HighamBench

open scoped BigOperators

private lemma p29_gamma_nonneg (u : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (hvalid : P29GammaValid u n) :
    0 ≤ p29Gamma u n := by
  unfold P29GammaValid at hvalid
  unfold p29Gamma
  have hden : 0 ≤ 1 - (n : ℝ) * u := by linarith
  exact div_nonneg (mul_nonneg (by positivity) hu) hden

private lemma p29_gamma_step_old (u : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (hvalid : P29GammaValid u (n + 1)) :
    (1 + u) * p29Gamma u n + u ≤ p29Gamma u (n + 1) := by
  unfold P29GammaValid at hvalid
  unfold p29Gamma
  push_cast at hvalid ⊢
  have hn : (0 : ℝ) ≤ n := by positivity
  have hden : 0 < 1 - (n : ℝ) * u := by nlinarith
  have hden' : 0 < 1 - ((n : ℝ) + 1) * u := by nlinarith
  have hu_div :
      u = u * (1 - (n : ℝ) * u) / (1 - (n : ℝ) * u) := by
    apply (eq_div_iff (ne_of_gt hden)).2
    ring
  have heq :
      (1 + u) * ((n : ℝ) * u / (1 - (n : ℝ) * u)) + u =
        ((n : ℝ) + 1) * u / (1 - (n : ℝ) * u) := by
    calc
      (1 + u) * ((n : ℝ) * u / (1 - (n : ℝ) * u)) + u =
          ((1 + u) * ((n : ℝ) * u)) / (1 - (n : ℝ) * u) + u := by ring
      _ = ((1 + u) * ((n : ℝ) * u)) / (1 - (n : ℝ) * u) +
          u * (1 - (n : ℝ) * u) / (1 - (n : ℝ) * u) := by rw [← hu_div]
      _ = (((n : ℝ) + 1) * u) / (1 - (n : ℝ) * u) := by
        rw [← add_div]
        congr 1
        ring
  rw [heq]
  apply (div_le_div_iff₀ hden hden').2
  apply mul_le_mul_of_nonneg_left (by nlinarith)
  exact mul_nonneg (by positivity) hu

private lemma p29_gamma_step_new (u : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (hn : 1 ≤ n)
    (hvalid : P29GammaValid u (n + 1)) :
    2 * u + u ^ 2 ≤ p29Gamma u (n + 1) := by
  unfold P29GammaValid at hvalid
  unfold p29Gamma
  push_cast at hvalid ⊢
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < 1 - ((n : ℝ) + 1) * u := by nlinarith
  rw [le_div_iff₀ hden]
  have htwo : (2 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hden_le : 1 - ((n : ℝ) + 1) * u ≤ 1 - 2 * u := by
    nlinarith [mul_le_mul_of_nonneg_right htwo hu]
  have hcoef : 0 ≤ 2 * u + u ^ 2 := by positivity
  calc
    (2 * u + u ^ 2) * (1 - ((n : ℝ) + 1) * u) ≤
        (2 * u + u ^ 2) * (1 - 2 * u) :=
      mul_le_mul_of_nonneg_left hden_le hcoef
    _ ≤ 2 * u := by
      have hcube : 0 ≤ u ^ 2 * u := mul_nonneg (sq_nonneg u) hu
      nlinarith [sq_nonneg u]
    _ ≤ ((n : ℝ) + 1) * u := mul_le_mul_of_nonneg_right htwo hu

private lemma p29_rounded_dot_one (fp : P29FPModel)
    (x y : Fin 1 → ℝ) :
    p29RoundedDotProduct fp 1 x y = fp.fl_mul (x 0) (y 0) := by
  simp [p29RoundedDotProduct]

private lemma p29_rounded_dot_succ_succ (fp : P29FPModel) (n : ℕ)
    (x y : Fin (n + 2) → ℝ) :
    p29RoundedDotProduct fp (n + 2) x y =
      fp.fl_add
        (p29RoundedDotProduct fp (n + 1)
          (fun i => x i.castSucc) (fun i => y i.castSucc))
        (fp.fl_mul (x (Fin.last (n + 1))) (y (Fin.last (n + 1)))) := by
  simp [p29RoundedDotProduct, Fin.foldl_succ_last]

private lemma p29_rounded_dot_error (fp : P29FPModel) (n : ℕ)
    (hvalid : P29GammaValid fp.u n) (x y : Fin n → ℝ) :
    |p29RoundedDotProduct fp n x y - ∑ k : Fin n, x k * y k| ≤
      p29Gamma fp.u n * ∑ k : Fin n, |x k| * |y k| := by
  induction n using Nat.twoStepInduction with
  | zero => simp [p29RoundedDotProduct, p29Gamma]
  | one =>
      rw [p29_rounded_dot_one]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      obtain ⟨δ, hδ, hmul⟩ := fp.model_mul (x 0) (y 0)
      rw [hmul]
      have hu_gamma : fp.u ≤ p29Gamma fp.u 1 := by
        simpa [p29Gamma] using
          (p29_gamma_step_old fp.u 0 fp.u_nonneg hvalid)
      calc
        |(x 0 * y 0) * (1 + δ) - x 0 * y 0| =
            |x 0 * y 0| * |δ| := by
          rw [show (x 0 * y 0) * (1 + δ) - x 0 * y 0 =
            (x 0 * y 0) * δ by ring, abs_mul]
        _ ≤ |x 0 * y 0| * fp.u :=
          mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
        _ ≤ |x 0 * y 0| * p29Gamma fp.u 1 :=
          mul_le_mul_of_nonneg_left hu_gamma (abs_nonneg _)
        _ = p29Gamma fp.u 1 * (|x 0| * |y 0|) := by
          rw [abs_mul]
          ring
  | more n ihn ihprev =>
      have hvalid_prev : P29GammaValid fp.u (n + 1) := by
        unfold P29GammaValid at hvalid ⊢
        push_cast at hvalid ⊢
        nlinarith [fp.u_nonneg]
      let xp : Fin (n + 1) → ℝ := fun i => x i.castSucc
      let yp : Fin (n + 1) → ℝ := fun i => y i.castSucc
      let R : ℝ := p29RoundedDotProduct fp (n + 1) xp yp
      let a : ℝ := ∑ i : Fin (n + 1), xp i * yp i
      let S : ℝ := ∑ i : Fin (n + 1), |xp i| * |yp i|
      let q : ℝ := x (Fin.last (n + 1)) * y (Fin.last (n + 1))
      let T : ℝ := |x (Fin.last (n + 1))| * |y (Fin.last (n + 1))|
      have ih := ihprev hvalid_prev xp yp
      have ha : |a| ≤ S := by
        dsimp [a, S]
        simpa only [abs_mul] using
          (Finset.abs_sum_le_sum_abs
            (f := fun i : Fin (n + 1) => xp i * yp i)
            (s := Finset.univ))
      have hS : 0 ≤ S := by
        dsimp [S]
        positivity
      have hT : 0 ≤ T := by
        dsimp [T]
        positivity
      obtain ⟨δm, hδm, hmul⟩ :=
        fp.model_mul (x (Fin.last (n + 1))) (y (Fin.last (n + 1)))
      obtain ⟨δa, hδa, hadd⟩ :=
        fp.model_add R (fp.fl_mul
          (x (Fin.last (n + 1))) (y (Fin.last (n + 1))))
      have hone : |1 + δa| ≤ 1 + fp.u := by
        calc
          |1 + δa| ≤ |(1 : ℝ)| + |δa| := abs_add_le _ _
          _ ≤ 1 + fp.u := by simpa using add_le_add_left hδa 1
      have hrounds : |δm + δa + δm * δa| ≤ 2 * fp.u + fp.u ^ 2 := by
        calc
          |δm + δa + δm * δa| ≤ |δm| + |δa| + |δm * δa| :=
            abs_add_three _ _ _
          _ = |δm| + |δa| + |δm| * |δa| := by rw [abs_mul]
          _ ≤ fp.u + fp.u + fp.u * fp.u := by
            gcongr
            exact fp.u_nonneg
          _ = 2 * fp.u + fp.u ^ 2 := by ring
      have hold := p29_gamma_step_old fp.u (n + 1) fp.u_nonneg hvalid
      have hnew := p29_gamma_step_new fp.u (n + 1) fp.u_nonneg
        (Nat.succ_le_succ (Nat.zero_le n)) hvalid
      have hgammaS : 0 ≤ p29Gamma fp.u (n + 1) * S :=
        mul_nonneg
          (p29_gamma_nonneg fp.u (n + 1) fp.u_nonneg hvalid_prev) hS
      rw [p29_rounded_dot_succ_succ]
      rw [Fin.sum_univ_castSucc
        (f := fun k : Fin (n + 2) => x k * y k)]
      rw [Fin.sum_univ_castSucc
        (f := fun k : Fin (n + 2) => |x k| * |y k|)]
      change
        |fp.fl_add R (fp.fl_mul
            (x (Fin.last (n + 1))) (y (Fin.last (n + 1)))) -
          (a + q)| ≤ p29Gamma fp.u (n + 2) * (S + T)
      rw [hadd, hmul]
      calc
        |(R + q * (1 + δm)) * (1 + δa) - (a + q)| =
            |(R - a) * (1 + δa) + a * δa +
              q * (δm + δa + δm * δa)| := by
          congr 1
          ring
        _ ≤ |R - a| * |1 + δa| + |a| * |δa| +
              |q| * |δm + δa + δm * δa| := by
          calc
            _ ≤ |(R - a) * (1 + δa)| + |a * δa| +
                |q * (δm + δa + δm * δa)| := abs_add_three _ _ _
            _ = _ := by rw [abs_mul, abs_mul, abs_mul]
        _ ≤ (p29Gamma fp.u (n + 1) * S) * (1 + fp.u) +
              S * fp.u + T * (2 * fp.u + fp.u ^ 2) := by
          rw [show |q| = T by simp [q, T, abs_mul]]
          gcongr
        _ = ((1 + fp.u) * p29Gamma fp.u (n + 1) + fp.u) * S +
              (2 * fp.u + fp.u ^ 2) * T := by ring
        _ ≤ p29Gamma fp.u (n + 2) * S +
              p29Gamma fp.u (n + 2) * T := by
          gcongr
        _ = p29Gamma fp.u (n + 2) * (S + T) := by ring

/-- P29-T1: the first-step Schur-complement error calculation in Appendix B. -/
theorem p29_t1_first_schur_error
    (fp : P29FPModel) (m r : ℕ)
    (A22 : P29Matrix m m) (L11 : P29Matrix m r)
    (A12 : P29Matrix r m)
    (hvalid : P29GammaValid fp.u r) :
    ∀ i j,
      |p29RoundedSchur fp A22 L11 A12 i j -
          p29ExactSchur A22 L11 A12 i j| ≤
        p29SchurErrorMajorant fp A22 L11 A12 i j := by
  -- PROOF_START P29-T1-H001
  intro i j
  let R : ℝ := p29RoundedMatMul fp L11 A12 i j
  let E : ℝ := p29MatMul L11 A12 i j
  let a : ℝ := A22 i j
  let S : ℝ := ∑ k : Fin r, |L11 i k| * |A12 k j|
  have hdot : |R - E| ≤ p29Gamma fp.u r * S := by
    simpa [R, E, S, p29RoundedMatMul, p29MatMul] using
      (p29_rounded_dot_error fp r hvalid (L11 i) (fun k => A12 k j))
  obtain ⟨δ, hδ, hsub⟩ := fp.model_sub a R
  change |fp.fl_sub a R - (a - E)| ≤
    fp.u * |a - R| + p29Gamma fp.u r * S
  rw [hsub]
  calc
    |(a - R) * (1 + δ) - (a - E)| =
        |(a - R) * δ + (E - R)| := by
      congr 1
      ring
    _ ≤ |a - R| * |δ| + |E - R| := by
      calc
        _ ≤ |(a - R) * δ| + |E - R| := abs_add_le _ _
        _ = _ := by rw [abs_mul]
    _ ≤ |a - R| * fp.u + p29Gamma fp.u r * S := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
      · simpa [abs_sub_comm] using hdot
    _ = fp.u * |a - R| + p29Gamma fp.u r * S := by ring

end HighamBench
