import HighamBench.P29Definitions

namespace HighamBench

private lemma p29RoundedDotProduct_succ_succ
    (fp : P29FPModel) (n : ℕ) (x y : Fin (n + 2) → ℝ) :
    p29RoundedDotProduct fp (n + 2) x y =
      fp.fl_add
        (p29RoundedDotProduct fp (n + 1)
          (fun i => x i.castSucc) (fun i => y i.castSucc))
        (fp.fl_mul (x (Fin.last (n + 1))) (y (Fin.last (n + 1)))) := by
  simp [p29RoundedDotProduct, Fin.foldl_succ_last]

private lemma p29_one_add_pow_le_inv_gamma_denom
    (u : ℝ) (n : ℕ) (hu : 0 ≤ u) (hvalid : (n : ℝ) * u < 1) :
    (1 + u) ^ n ≤ 1 / (1 - (n : ℝ) * u) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hnvalid : (n : ℝ) * u < 1 := by
        rw [Nat.cast_succ] at hvalid
        nlinarith
      have hdn : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hnvalid
      have hds : 0 < 1 - (n + 1 : ℕ) * u := sub_pos.mpr hvalid
      have hone : 0 ≤ 1 + u := by linarith
      calc
        (1 + u) ^ (n + 1) = (1 + u) ^ n * (1 + u) := by rw [pow_succ]
        _ ≤ (1 / (1 - (n : ℝ) * u)) * (1 + u) :=
          mul_le_mul_of_nonneg_right (ih hnvalid) hone
        _ ≤ 1 / (1 - (n + 1 : ℕ) * u) := by
          rw [show 1 / (1 - (n : ℝ) * u) * (1 + u) =
              (1 + u) / (1 - (n : ℝ) * u) by
                simp [div_eq_mul_inv, mul_comm]]
          apply (div_le_div_iff₀ hdn hds).2
          push_cast
          nlinarith [sq_nonneg u]

private lemma p29_pow_sub_one_le_gamma
    (u : ℝ) (n : ℕ) (hu : 0 ≤ u) (hvalid : P29GammaValid u n) :
    (1 + u) ^ n - 1 ≤ p29Gamma u n := by
  have hd : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hvalid
  rw [p29Gamma]
  apply (le_div_iff₀ hd).2
  have hp := (le_div_iff₀ hd).1
    (p29_one_add_pow_le_inv_gamma_denom u n hu hvalid)
  nlinarith

private lemma p29_rounded_dot_error_pow
    (fp : P29FPModel) (n : ℕ) (x y : Fin n → ℝ) :
    |p29RoundedDotProduct fp n x y - ∑ k : Fin n, x k * y k| ≤
      ((1 + fp.u) ^ n - 1) * ∑ k : Fin n, |x k| * |y k| := by
  induction n with
  | zero => simp [p29RoundedDotProduct]
  | succ n ih =>
      cases n with
      | zero =>
          obtain ⟨δ, hδ, hmul⟩ := fp.model_mul (x 0) (y 0)
          rw [show p29RoundedDotProduct fp 1 x y = fp.fl_mul (x 0) (y 0) by
            simp [p29RoundedDotProduct], hmul]
          rw [Fin.sum_univ_one, Fin.sum_univ_one]
          norm_num [pow_one]
          change |x 0 * y 0 * (1 + δ) - x 0 * y 0| ≤
            fp.u * (|x 0| * |y 0|)
          rw [show x 0 * y 0 * (1 + δ) - x 0 * y 0 =
              (x 0 * y 0) * δ by ring, abs_mul, abs_mul]
          calc
            |x 0| * |y 0| * |δ| ≤ |x 0| * |y 0| * fp.u :=
              mul_le_mul_of_nonneg_left hδ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
            _ = fp.u * (|x 0| * |y 0|) := by ring
      | succ n =>
          let xo : Fin (n + 1) → ℝ := fun i => x i.castSucc
          let yo : Fin (n + 1) → ℝ := fun i => y i.castSucc
          let q := p29RoundedDotProduct fp (n + 1) xo yo
          let s := ∑ k : Fin (n + 1), xo k * yo k
          let S := ∑ k : Fin (n + 1), |xo k| * |yo k|
          let t := x (Fin.last (n + 1)) * y (Fin.last (n + 1))
          let c := (1 + fp.u) ^ (n + 1) - 1
          let C := (1 + fp.u) ^ (n + 2) - 1
          have hi : |q - s| ≤ c * S := by
            exact ih xo yo
          obtain ⟨δm, hδm, hmul⟩ :=
            fp.model_mul (x (Fin.last (n + 1))) (y (Fin.last (n + 1)))
          obtain ⟨δa, hδa, hadd⟩ :=
            fp.model_add q (fp.fl_mul
              (x (Fin.last (n + 1))) (y (Fin.last (n + 1))))
          have hu := fp.u_nonneg
          have hone : 1 ≤ 1 + fp.u := by linarith
          have hc : 0 ≤ c := by
            dsimp [c]
            linarith [one_le_pow₀ hone (n := n + 1)]
          have hC : 0 ≤ C := by
            dsimp [C]
            linarith [one_le_pow₀ hone (n := n + 2)]
          have hS : 0 ≤ S := by
            dsimp [S]
            positivity
          have hs : |s| ≤ S := by
            dsimp [s, S]
            simpa [abs_mul] using
              (Finset.abs_sum_le_sum_abs
                (f := fun k : Fin (n + 1) => xo k * yo k) Finset.univ)
          have hδa1 : |1 + δa| ≤ 1 + fp.u := by
            calc
              |1 + δa| ≤ |(1 : ℝ)| + |δa| := abs_add_le _ _
              _ ≤ 1 + fp.u := by norm_num; linarith
          have hθ : |δm + δa + δm * δa| ≤
              2 * fp.u + fp.u ^ 2 := by
            calc
              |δm + δa + δm * δa| ≤
                  |δm| + |δa| + |δm * δa| := by
                    calc
                      _ ≤ |δm + δa| + |δm * δa| := abs_add_le _ _
                      _ ≤ (|δm| + |δa|) + |δm * δa| := by
                        gcongr
                        exact abs_add_le _ _
              _ ≤ 2 * fp.u + fp.u ^ 2 := by
                rw [abs_mul]
                have hp := mul_le_mul hδm hδa (abs_nonneg δa) hu
                nlinarith
          have htwo : 2 * fp.u + fp.u ^ 2 ≤ C := by
            have hp : (1 + fp.u) ^ 2 ≤ (1 + fp.u) ^ (n + 2) :=
              pow_le_pow_right₀ hone (by omega)
            dsimp [C]
            norm_num [pow_two] at hp ⊢
            nlinarith
          have hold : |(q - s) * (1 + δa)| ≤ c * S * (1 + fp.u) := by
            rw [abs_mul]
            exact mul_le_mul hi hδa1 (abs_nonneg _) (mul_nonneg hc hS)
          have hsextra : |s * δa| ≤ S * fp.u := by
            rw [abs_mul]
            exact mul_le_mul hs hδa (abs_nonneg _) hS
          have hlast : |t * (δm + δa + δm * δa)| ≤ |t| * C := by
            rw [abs_mul]
            exact mul_le_mul (le_refl _) (hθ.trans htwo) (by positivity) (abs_nonneg _)
          have hsum : (∑ k : Fin (n + 2), x k * y k) = s + t := by
            rw [Fin.sum_univ_castSucc]
          have habsum : (∑ k : Fin (n + 2), |x k| * |y k|) =
              S + |x (Fin.last (n + 1))| * |y (Fin.last (n + 1))| := by
            rw [Fin.sum_univ_castSucc]
          rw [p29RoundedDotProduct_succ_succ fp n x y, hadd, hmul, hsum, habsum]
          change |(q + t * (1 + δm)) * (1 + δa) - (s + t)| ≤
            C * (S + |x (Fin.last (n + 1))| * |y (Fin.last (n + 1))|)
          rw [show (q + t * (1 + δm)) * (1 + δa) - (s + t) =
              (q - s) * (1 + δa) + s * δa +
                t * (δm + δa + δm * δa) by ring]
          calc
            |(q - s) * (1 + δa) + s * δa +
                t * (δm + δa + δm * δa)| ≤
                |(q - s) * (1 + δa)| + |s * δa| +
                  |t * (δm + δa + δm * δa)| := by
                    calc
                      _ ≤ |(q - s) * (1 + δa) + s * δa| +
                          |t * (δm + δa + δm * δa)| := abs_add_le _ _
                      _ ≤ (|(q - s) * (1 + δa)| + |s * δa|) +
                          |t * (δm + δa + δm * δa)| := by
                            gcongr
                            exact abs_add_le _ _
            _ ≤ c * S * (1 + fp.u) + S * fp.u + |t| * C := by
              gcongr
            _ = C * (S + |x (Fin.last (n + 1))| *
                |y (Fin.last (n + 1))|) := by
              dsimp [c, C, t]
              rw [abs_mul, pow_succ]
              ring

private lemma p29_rounded_dot_error
    (fp : P29FPModel) (n : ℕ) (x y : Fin n → ℝ)
    (hvalid : P29GammaValid fp.u n) :
    |p29RoundedDotProduct fp n x y - ∑ k : Fin n, x k * y k| ≤
      p29Gamma fp.u n * ∑ k : Fin n, |x k| * |y k| := by
  calc
    |p29RoundedDotProduct fp n x y - ∑ k : Fin n, x k * y k| ≤
        ((1 + fp.u) ^ n - 1) * ∑ k : Fin n, |x k| * |y k| :=
      p29_rounded_dot_error_pow fp n x y
    _ ≤ p29Gamma fp.u n * ∑ k : Fin n, |x k| * |y k| := by
      apply mul_le_mul_of_nonneg_right
      · exact p29_pow_sub_one_le_gamma fp.u n fp.u_nonneg hvalid
      · positivity

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
  let a := A22 i j
  let q := p29RoundedDotProduct fp r (L11 i) (fun k => A12 k j)
  let s := ∑ k : Fin r, L11 i k * A12 k j
  let S := ∑ k : Fin r, |L11 i k| * |A12 k j|
  have hdot : |q - s| ≤ p29Gamma fp.u r * S := by
    exact p29_rounded_dot_error fp r (L11 i) (fun k => A12 k j) hvalid
  obtain ⟨δ, hδ, hsub⟩ := fp.model_sub a q
  have hround : |(a - q) * δ| ≤ fp.u * |a - q| := by
    rw [abs_mul]
    calc
      |a - q| * |δ| ≤ |a - q| * fp.u :=
        mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
      _ = fp.u * |a - q| := by ring
  change |fp.fl_sub a q - (a - s)| ≤ fp.u * |a - q| + p29Gamma fp.u r * S
  rw [hsub]
  rw [show (a - q) * (1 + δ) - (a - s) =
      (a - q) * δ + (s - q) by ring]
  calc
    |(a - q) * δ + (s - q)| ≤ |(a - q) * δ| + |s - q| :=
      abs_add_le _ _
    _ ≤ fp.u * |a - q| + p29Gamma fp.u r * S := by
      exact add_le_add hround (by simpa [abs_sub_comm] using hdot)

end HighamBench
