import HighamBench.P29Definitions

namespace HighamBench

open scoped BigOperators

private lemma p29_gamma_nonneg (u : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (hvalid : P29GammaValid u n) :
    0 ≤ p29Gamma u n := by
  unfold p29Gamma P29GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) hu) (by linarith)

private lemma p29_u_le_gamma (u : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (hn : 1 ≤ n) (hvalid : P29GammaValid u n) :
    u ≤ p29Gamma u n := by
  unfold p29Gamma P29GammaValid at *
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : 0 < 1 - (n : ℝ) * u := by linarith
  apply (le_div_iff₀ hden).2
  have h₁ : 0 ≤ u * ((n : ℝ) - 1) :=
    mul_nonneg hu (sub_nonneg.mpr hn')
  have h₂ : 0 ≤ (n : ℝ) * u ^ 2 :=
    mul_nonneg (Nat.cast_nonneg n) (sq_nonneg u)
  nlinarith

private lemma p29_gamma_step (u : ℝ) (q : ℕ)
    (hu : 0 ≤ u) (hvalid : P29GammaValid u (q + 1)) :
    p29Gamma u q + u * (1 + p29Gamma u q) ≤
      p29Gamma u (q + 1) := by
  unfold p29Gamma P29GammaValid at *
  have hq : (q : ℝ) * u ≤ ((q + 1 : ℕ) : ℝ) * u := by
    norm_num
    nlinarith
  have hdq : 0 < 1 - (q : ℝ) * u := by linarith
  have hdq1 : 0 < 1 - ((q + 1 : ℕ) : ℝ) * u := by linarith
  have heq :
      (q : ℝ) * u / (1 - (q : ℝ) * u) +
          u * (1 + (q : ℝ) * u / (1 - (q : ℝ) * u)) =
        ((q + 1 : ℕ) : ℝ) * u / (1 - (q : ℝ) * u) := by
    rw [show ((q + 1 : ℕ) : ℝ) = (q : ℝ) + 1 by norm_num]
    field_simp [ne_of_gt hdq]
    ring
  rw [heq]
  apply div_le_div_of_nonneg_left
  · exact mul_nonneg (Nat.cast_nonneg _) hu
  · exact hdq1
  · linarith

private lemma p29_mul_add_step
    (fp : P29FPModel) (q : ℕ) (hq : 1 ≤ q)
    (hvalid : P29GammaValid fp.u (q + 1))
    (z s B x y : ℝ)
    (hs : |s| ≤ B)
    (hz : |z - s| ≤ p29Gamma fp.u q * B) :
    |fp.fl_add z (fp.fl_mul x y) - (s + x * y)| ≤
      p29Gamma fp.u (q + 1) * (B + |x| * |y|) := by
  obtain ⟨δm, hδm, hm⟩ := fp.model_mul x y
  obtain ⟨δa, hδa, ha⟩ := fp.model_add z (fp.fl_mul x y)
  have hu := fp.u_nonneg
  have hqvalid : P29GammaValid fp.u q := by
    unfold P29GammaValid at *
    have hcast : (q : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by norm_num
    nlinarith
  have hgamma0 : 0 ≤ p29Gamma fp.u q :=
    p29_gamma_nonneg fp.u q hu hqvalid
  have hB : 0 ≤ B := le_trans (abs_nonneg s) hs
  have hxy : 0 ≤ |x| * |y| := mul_nonneg (abs_nonneg x) (abs_nonneg y)
  have hzm : |z| ≤ (1 + p29Gamma fp.u q) * B := by
    calc
      |z| = |(z - s) + s| := by ring_nf
      _ ≤ |z - s| + |s| := abs_add_le _ _
      _ ≤ p29Gamma fp.u q * B + B := add_le_add hz hs
      _ = (1 + p29Gamma fp.u q) * B := by ring
  have honeδm : |1 + δm| ≤ 1 + fp.u := by
    calc
      |1 + δm| ≤ |(1 : ℝ)| + |δm| := abs_add_le _ _
      _ ≤ 1 + fp.u := by simpa using add_le_add_left hδm 1
  have hmabs : |fp.fl_mul x y| ≤ (1 + fp.u) * (|x| * |y|) := by
    rw [hm, abs_mul, abs_mul]
    nlinarith [abs_nonneg x, abs_nonneg y]
  have hraw :
      |fp.fl_add z (fp.fl_mul x y) - (s + x * y)| ≤
        (p29Gamma fp.u q + fp.u * (1 + p29Gamma fp.u q)) * B +
          (2 * fp.u + fp.u ^ 2) * (|x| * |y|) := by
    rw [ha, hm]
    calc
      |(z + x * y * (1 + δm)) * (1 + δa) - (s + x * y)| =
          |(z - s) + (x * y * δm) +
            δa * (z + x * y * (1 + δm))| := by ring_nf
      _ ≤ |z - s| + |x * y * δm| +
            |δa * (z + x * y * (1 + δm))| := by
          calc
            |(z - s) + (x * y * δm) +
                δa * (z + x * y * (1 + δm))| ≤
                |(z - s) + (x * y * δm)| +
                  |δa * (z + x * y * (1 + δm))| := abs_add_le _ _
            _ ≤ (|z - s| + |x * y * δm|) +
                  |δa * (z + x * y * (1 + δm))| := by
                    gcongr
                    exact abs_add_le _ _
      _ ≤ p29Gamma fp.u q * B + fp.u * (|x| * |y|) +
            fp.u * ((1 + p29Gamma fp.u q) * B +
              (1 + fp.u) * (|x| * |y|)) := by
          have hza : |z + x * y * (1 + δm)| ≤
              (1 + p29Gamma fp.u q) * B +
                (1 + fp.u) * (|x| * |y|) := by
            calc
              |z + x * y * (1 + δm)| ≤ |z| + |x * y * (1 + δm)| :=
                abs_add_le _ _
              _ ≤ (1 + p29Gamma fp.u q) * B +
                    (1 + fp.u) * (|x| * |y|) := by
                  gcongr
                  rw [abs_mul, abs_mul]
                  nlinarith [abs_nonneg x, abs_nonneg y]
          have hmerr : |x * y * δm| ≤ fp.u * (|x| * |y|) := by
            rw [abs_mul, abs_mul]
            nlinarith [abs_nonneg x, abs_nonneg y]
          have haerr : |δa * (z + x * y * (1 + δm))| ≤
              fp.u * ((1 + p29Gamma fp.u q) * B +
                (1 + fp.u) * (|x| * |y|)) := by
            rw [abs_mul]
            exact mul_le_mul hδa hza (abs_nonneg _) hu
          exact add_le_add (add_le_add hz hmerr) haerr
      _ = (p29Gamma fp.u q + fp.u * (1 + p29Gamma fp.u q)) * B +
            (2 * fp.u + fp.u ^ 2) * (|x| * |y|) := by ring
  have hstep := p29_gamma_step fp.u q hu hvalid
  have huGamma := p29_u_le_gamma fp.u q hu hq hqvalid
  have hterm : 2 * fp.u + fp.u ^ 2 ≤
      p29Gamma fp.u q + fp.u * (1 + p29Gamma fp.u q) := by
    nlinarith
  calc
    |fp.fl_add z (fp.fl_mul x y) - (s + x * y)| ≤
        (p29Gamma fp.u q + fp.u * (1 + p29Gamma fp.u q)) * B +
          (2 * fp.u + fp.u ^ 2) * (|x| * |y|) := hraw
    _ ≤ p29Gamma fp.u (q + 1) * B +
          p29Gamma fp.u (q + 1) * (|x| * |y|) := by
        gcongr
        exact le_trans hterm hstep
    _ = p29Gamma fp.u (q + 1) * (B + |x| * |y|) := by ring

private lemma p29_foldl_mul_add_error
    (fp : P29FPModel) (q n : ℕ) (hq : 1 ≤ q)
    (hvalid : P29GammaValid fp.u (q + n))
    (z s B : ℝ) (x y : Fin n → ℝ)
    (hs : |s| ≤ B)
    (hz : |z - s| ≤ p29Gamma fp.u q * B) :
    |Fin.foldl n
          (fun acc i => fp.fl_add acc (fp.fl_mul (x i) (y i))) z -
        (s + ∑ i : Fin n, x i * y i)| ≤
      p29Gamma fp.u (q + n) *
        (B + ∑ i : Fin n, |x i| * |y i|) := by
  induction n generalizing q z s B with
  | zero => simpa using hz
  | succ n ih =>
      have hvalidStep : P29GammaValid fp.u (q + 1) := by
        unfold P29GammaValid at *
        have hu := fp.u_nonneg
        have hle : ((q + 1 : ℕ) : ℝ) ≤ ((q + (n + 1) : ℕ) : ℝ) := by
          norm_num
        nlinarith
      have hstep := p29_mul_add_step fp q hq hvalidStep z s B (x 0) (y 0) hs hz
      have hs' : |s + x 0 * y 0| ≤ B + |x 0| * |y 0| := by
        calc
          |s + x 0 * y 0| ≤ |s| + |x 0 * y 0| := abs_add_le _ _
          _ ≤ B + |x 0| * |y 0| := by simpa [abs_mul] using add_le_add_right hs (|x 0 * y 0|)
      have hrec := ih (q := q + 1) (by omega)
        (hvalid := by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hvalid)
        (z := fp.fl_add z (fp.fl_mul (x 0) (y 0)))
        (s := s + x 0 * y 0) (B := B + |x 0| * |y 0|)
        (x := fun i => x i.succ) (y := fun i => y i.succ) hs' hstep
      simpa [Fin.foldl_succ, Fin.sum_univ_succ, Nat.add_assoc,
        add_assoc, add_left_comm, add_comm] using hrec

private lemma p29_rounded_dot_error
    (fp : P29FPModel) (n : ℕ) (x y : Fin n → ℝ)
    (hvalid : P29GammaValid fp.u n) :
    |p29RoundedDotProduct fp n x y - ∑ i : Fin n, x i * y i| ≤
      p29Gamma fp.u n * ∑ i : Fin n, |x i| * |y i| := by
  cases n with
  | zero => simp [p29RoundedDotProduct]
  | succ n =>
      obtain ⟨δ, hδ, hm⟩ := fp.model_mul (x 0) (y 0)
      have hvalid1 : P29GammaValid fp.u 1 := by
        unfold P29GammaValid at *
        push_cast at hvalid
        have hle : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
        norm_num at ⊢
        have := mul_le_mul_of_nonneg_right hle fp.u_nonneg
        norm_num at this
        exact lt_of_le_of_lt this hvalid
      have huGamma := p29_u_le_gamma fp.u 1 fp.u_nonneg (by omega) hvalid1
      have hmul : |fp.fl_mul (x 0) (y 0) - x 0 * y 0| ≤
          p29Gamma fp.u 1 * (|x 0| * |y 0|) := by
        rw [hm]
        have hnonneg : 0 ≤ |x 0| * |y 0| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
        rw [show x 0 * y 0 * (1 + δ) - x 0 * y 0 = (x 0 * y 0) * δ by ring,
          abs_mul, abs_mul]
        nlinarith
      have hs : |x 0 * y 0| ≤ |x 0| * |y 0| := by rw [abs_mul]
      have hfold := p29_foldl_mul_add_error fp 1 n (by omega)
        (by simpa [Nat.add_comm] using hvalid)
        (fp.fl_mul (x 0) (y 0)) (x 0 * y 0) (|x 0| * |y 0|)
        (fun i => x i.succ) (fun i => y i.succ) hs hmul
      simpa [p29RoundedDotProduct, Fin.sum_univ_succ, Nat.add_comm,
        add_assoc, abs_mul] using hfold

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
  have hdot := p29_rounded_dot_error fp r (L11 i) (fun k => A12 k j) hvalid
  obtain ⟨δ, hδ, hsub⟩ :=
    fp.model_sub (A22 i j) (p29RoundedMatMul fp L11 A12 i j)
  rw [p29RoundedSchur, p29ExactSchur, p29SchurErrorMajorant, hsub]
  calc
    |(A22 i j - p29RoundedMatMul fp L11 A12 i j) * (1 + δ) -
        (A22 i j - p29MatMul L11 A12 i j)| =
        |δ * (A22 i j - p29RoundedMatMul fp L11 A12 i j) +
          (p29MatMul L11 A12 i j - p29RoundedMatMul fp L11 A12 i j)| := by
            apply congrArg abs
            rw [mul_add, mul_one,
              mul_comm (A22 i j - p29RoundedMatMul fp L11 A12 i j) δ]
            abel
    _ ≤ |δ * (A22 i j - p29RoundedMatMul fp L11 A12 i j)| +
          |p29MatMul L11 A12 i j - p29RoundedMatMul fp L11 A12 i j| :=
        abs_add_le _ _
    _ ≤ fp.u * |A22 i j - p29RoundedMatMul fp L11 A12 i j| +
          p29Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j| := by
        rw [abs_mul]
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
        · rw [abs_sub_comm]
          simpa [p29RoundedMatMul, p29MatMul] using hdot

end HighamBench
