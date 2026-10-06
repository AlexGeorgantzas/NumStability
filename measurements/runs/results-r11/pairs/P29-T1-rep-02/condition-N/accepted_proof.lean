import HighamBench.P29Definitions

namespace HighamBench

open scoped BigOperators

private lemma p29RoundedDotProduct_succ_last
    (fp : P29FPModel) (n : ℕ) (x y : Fin (n + 1) → ℝ) :
    p29RoundedDotProduct fp (n + 1) x y =
      fp.fl_add
        (p29RoundedDotProduct fp n
          (fun k => x k.castSucc) (fun k => y k.castSucc))
        (fp.fl_mul (x (Fin.last n)) (y (Fin.last n))) := by
  cases n with
  | zero => simp [p29RoundedDotProduct, fp.fl_add_zero]
  | succ n =>
      rw [p29RoundedDotProduct, Fin.foldl_succ_last]
      rfl

private lemma p29Gamma_nonneg_of_valid (u : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (h : P29GammaValid u n) :
    0 ≤ p29Gamma u n := by
  unfold p29Gamma P29GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu)
    (sub_nonneg.mpr (le_of_lt h))

private lemma p29Gamma_old_coeff (u : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (h : P29GammaValid u (n + 1)) :
    (1 + u) * p29Gamma u n + u ≤ p29Gamma u (n + 1) := by
  unfold p29Gamma P29GammaValid at *
  push_cast at h ⊢
  have hd : 0 < 1 - (n : ℝ) * u := by
    have : (n : ℝ) * u ≤ ((n : ℝ) + 1) * u := by nlinarith
    linarith
  have hd' : 0 < 1 - ((n : ℝ) + 1) * u := by linarith
  have heq :
      (1 + u) * ((n : ℝ) * u / (1 - (n : ℝ) * u)) + u =
        (((n : ℝ) + 1) * u) / (1 - (n : ℝ) * u) := by
    let d : ℝ := 1 - (n : ℝ) * u
    have hd0 : d ≠ 0 := ne_of_gt hd
    calc
      (1 + u) * ((n : ℝ) * u / d) + u =
          ((1 + u) * ((n : ℝ) * u)) / d + (u * d) / d := by
            rw [mul_div_cancel_right₀ u hd0]
            field_simp [hd0]
      _ = ((1 + u) * ((n : ℝ) * u) + u * d) / d := by
            rw [add_div]
      _ = (((n : ℝ) + 1) * u) / d := by
            congr 1
            dsimp [d]
            ring
  rw [heq]
  exact div_le_div_of_nonneg_left (by positivity) hd'
    (by nlinarith)

private lemma p29Gamma_new_coeff (u : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (hn : 1 ≤ n) (h : P29GammaValid u (n + 1)) :
    u * (2 + u) ≤ p29Gamma u (n + 1) := by
  unfold p29Gamma P29GammaValid at *
  push_cast at h ⊢
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd : 0 < 1 - ((n : ℝ) + 1) * u := by linarith
  apply (le_div_iff₀ hd).2
  have hp₁ : 0 ≤ ((n : ℝ) - 1) * u :=
    mul_nonneg (sub_nonneg.mpr hn') hu
  have hp₂ : 0 ≤ (2 * (n : ℝ) + 1) * u ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg u)
  have hp₃ : 0 ≤ ((n : ℝ) + 1) * u ^ 3 :=
    mul_nonneg (by positivity) (pow_nonneg hu 3)
  nlinarith

private lemma p29_one_step_error
    (u g G T z S t δ ε : ℝ)
    (hu : 0 ≤ u) (hg : 0 ≤ g) (hG : 0 ≤ G) (hT : 0 ≤ T)
    (hz : |z - S| ≤ g * T) (hS : |S| ≤ T)
    (hδ : |δ| ≤ u) (hε : |ε| ≤ u)
    (hold : (1 + u) * g + u ≤ G)
    (hnew : u * (2 + u) ≤ G) :
    |(z + t * (1 + δ)) * (1 + ε) - (S + t)| ≤
      G * (T + |t|) := by
  have h1ε : |1 + ε| ≤ 1 + u := by
    calc
      |1 + ε| ≤ |(1 : ℝ)| + |ε| := abs_add_le _ _
      _ ≤ 1 + u := by norm_num; linarith
  have hprod : |(1 + δ) * (1 + ε) - 1| ≤ u * (2 + u) := by
    have hid : (1 + δ) * (1 + ε) - 1 = δ + ε + δ * ε := by ring
    rw [hid]
    calc
      |δ + ε + δ * ε| ≤ |δ| + |ε| + |δ * ε| := by
        linarith [abs_add_le δ ε, abs_add_le (δ + ε) (δ * ε)]
      _ = |δ| + |ε| + |δ| * |ε| := by rw [abs_mul]
      _ ≤ u + u + u * u := by
        gcongr
      _ = u * (2 + u) := by ring
  have hid :
      (z + t * (1 + δ)) * (1 + ε) - (S + t) =
        (z - S) * (1 + ε) + S * ε +
          t * ((1 + δ) * (1 + ε) - 1) := by ring
  rw [hid]
  calc
    |(z - S) * (1 + ε) + S * ε +
        t * ((1 + δ) * (1 + ε) - 1)| ≤
        |(z - S) * (1 + ε)| + |S * ε| +
          |t * ((1 + δ) * (1 + ε) - 1)| := by
      linarith [abs_add_le ((z - S) * (1 + ε)) (S * ε),
        abs_add_le ((z - S) * (1 + ε) + S * ε)
          (t * ((1 + δ) * (1 + ε) - 1))]
    _ = |z - S| * |1 + ε| + |S| * |ε| +
        |t| * |(1 + δ) * (1 + ε) - 1| := by simp only [abs_mul]
    _ ≤ (g * T) * (1 + u) + T * u + |t| * (u * (2 + u)) := by
      gcongr
    _ ≤ G * T + G * |t| := by
      have ho := mul_le_mul_of_nonneg_right hold hT
      have hn := mul_le_mul_of_nonneg_left hnew (abs_nonneg t)
      nlinarith
    _ = G * (T + |t|) := by ring

private lemma p29RoundedDotProduct_error
    (fp : P29FPModel) (n : ℕ) (hvalid : P29GammaValid fp.u n)
    (x y : Fin n → ℝ) :
    |p29RoundedDotProduct fp n x y - ∑ k, x k * y k| ≤
      p29Gamma fp.u n * ∑ k, |x k| * |y k| := by
  induction n with
  | zero => simp [p29RoundedDotProduct, p29Gamma]
  | succ n ih =>
      cases n with
      | zero =>
          obtain ⟨δ, hδ, hmul⟩ := fp.model_mul (x (Fin.last 0)) (y (Fin.last 0))
          rw [p29RoundedDotProduct_succ_last]
          simp only [p29RoundedDotProduct, fp.fl_add_zero]
          rw [hmul]
          rw [Fin.sum_univ_one, Fin.sum_univ_one]
          have huγ : fp.u ≤ p29Gamma fp.u 1 := by
            simpa [p29Gamma] using p29Gamma_old_coeff fp.u 0 fp.u_nonneg hvalid
          calc
            |x (Fin.last 0) * y (Fin.last 0) * (1 + δ) -
                x (Fin.last 0) * y (Fin.last 0)| =
                |x (Fin.last 0) * y (Fin.last 0)| * |δ| := by
                  rw [show x (Fin.last 0) * y (Fin.last 0) * (1 + δ) -
                    x (Fin.last 0) * y (Fin.last 0) =
                      (x (Fin.last 0) * y (Fin.last 0)) * δ by ring, abs_mul]
            _ ≤ |x (Fin.last 0) * y (Fin.last 0)| * fp.u := by gcongr
            _ ≤ |x (Fin.last 0) * y (Fin.last 0)| * p29Gamma fp.u 1 := by
              gcongr
            _ = p29Gamma fp.u 1 *
                (|x (Fin.last 0)| * |y (Fin.last 0)|) := by rw [abs_mul]; ring
      | succ n =>
          let x₀ : Fin (n + 1) → ℝ := fun k => x k.castSucc
          let y₀ : Fin (n + 1) → ℝ := fun k => y k.castSucc
          have hvalid₀ : P29GammaValid fp.u (n + 1) := by
            unfold P29GammaValid at hvalid ⊢
            push_cast at hvalid ⊢
            have hc : ((n : ℝ) + 1) * fp.u ≤ ((n : ℝ) + 2) * fp.u := by
              nlinarith [fp.u_nonneg]
            linarith
          have hi := ih hvalid₀ x₀ y₀
          let z := p29RoundedDotProduct fp (n + 1) x₀ y₀
          let S := ∑ k, x₀ k * y₀ k
          let T := ∑ k, |x₀ k| * |y₀ k|
          let t := x (Fin.last (n + 1)) * y (Fin.last (n + 1))
          obtain ⟨δ, hδ, hmul⟩ :=
            fp.model_mul (x (Fin.last (n + 1))) (y (Fin.last (n + 1)))
          obtain ⟨ε, hε, hadd⟩ := fp.model_add z (fp.fl_mul
            (x (Fin.last (n + 1))) (y (Fin.last (n + 1))))
          have hT : 0 ≤ T := by
            dsimp [T]
            exact Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
          have hS : |S| ≤ T := by
            dsimp [S, T]
            calc
              |∑ k, x₀ k * y₀ k| ≤ ∑ k, |x₀ k * y₀ k| :=
                Finset.abs_sum_le_sum_abs _ _
              _ = ∑ k, |x₀ k| * |y₀ k| := by simp_rw [abs_mul]
          have hstep := p29_one_step_error fp.u
            (p29Gamma fp.u (n + 1)) (p29Gamma fp.u (n + 2)) T z S t δ ε
            fp.u_nonneg
            (p29Gamma_nonneg_of_valid fp.u (n + 1) fp.u_nonneg hvalid₀)
            (p29Gamma_nonneg_of_valid fp.u (n + 2) fp.u_nonneg hvalid)
            hT hi hS hδ hε
            (p29Gamma_old_coeff fp.u (n + 1) fp.u_nonneg hvalid)
            (p29Gamma_new_coeff fp.u (n + 1) fp.u_nonneg (by omega) hvalid)
          rw [p29RoundedDotProduct_succ_last, hadd, hmul,
            Fin.sum_univ_castSucc (fun k => x k * y k),
            Fin.sum_univ_castSucc (fun k => |x k| * |y k|)]
          simpa [x₀, y₀, z, S, T, t, abs_mul, Nat.add_assoc] using hstep

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
  unfold p29RoundedSchur p29ExactSchur p29SchurErrorMajorant
  unfold p29RoundedMatMul p29MatMul
  obtain ⟨δ, hδ, hsub⟩ := fp.model_sub (A22 i j)
    (p29RoundedDotProduct fp r (L11 i) (fun k => A12 k j))
  rw [hsub]
  have hdot := p29RoundedDotProduct_error fp r hvalid
    (L11 i) (fun k => A12 k j)
  calc
    |(A22 i j - p29RoundedDotProduct fp r (L11 i) (fun k => A12 k j)) *
          (1 + δ) - (A22 i j - ∑ k, L11 i k * A12 k j)| =
        |(A22 i j - p29RoundedDotProduct fp r (L11 i) (fun k => A12 k j)) * δ +
          ((∑ k, L11 i k * A12 k j) -
            p29RoundedDotProduct fp r (L11 i) (fun k => A12 k j))| := by
      congr 1
      ring
    _ ≤ |A22 i j - p29RoundedDotProduct fp r (L11 i) (fun k => A12 k j)| *
          |δ| +
        |(∑ k, L11 i k * A12 k j) -
          p29RoundedDotProduct fp r (L11 i) (fun k => A12 k j)| := by
      simpa only [abs_mul] using abs_add_le
        ((A22 i j - p29RoundedDotProduct fp r (L11 i) (fun k => A12 k j)) * δ)
        ((∑ k, L11 i k * A12 k j) -
          p29RoundedDotProduct fp r (L11 i) (fun k => A12 k j))
    _ ≤ |A22 i j - p29RoundedDotProduct fp r (L11 i) (fun k => A12 k j)| *
          fp.u +
        p29Gamma fp.u r * ∑ k, |L11 i k| * |A12 k j| := by
      gcongr
      simpa only [abs_sub_comm] using hdot
    _ = fp.u *
          |A22 i j - p29RoundedDotProduct fp r (L11 i) (fun k => A12 k j)| +
        p29Gamma fp.u r * ∑ k, |L11 i k| * |A12 k j| := by ring

end HighamBench
