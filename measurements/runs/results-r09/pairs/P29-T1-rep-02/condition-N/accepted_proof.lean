import HighamBench.P29Definitions

namespace HighamBench

private lemma p29_gamma_nonneg (u : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (h : P29GammaValid u n) :
    0 ≤ p29Gamma u n := by
  unfold p29Gamma P29GammaValid at *
  have hd : 0 < 1 - (n : ℝ) * u := sub_pos.mpr h
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) hu) hd.le

private lemma p29_gamma_step (u : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (h : P29GammaValid u (n + 1)) :
    p29Gamma u n + u * (1 + p29Gamma u n) ≤
      p29Gamma u (n + 1) := by
  have hn : (n : ℝ) * u < 1 := by
    unfold P29GammaValid at h
    norm_num at h ⊢
    nlinarith [mul_nonneg (Nat.cast_nonneg n) hu]
  have hd₁ : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hn
  have hd₂ : 0 < 1 - ((n + 1 : ℕ) : ℝ) * u := by
    exact sub_pos.mpr h
  unfold p29Gamma
  have heq :
      (n : ℝ) * u / (1 - (n : ℝ) * u) +
          u * (1 + (n : ℝ) * u / (1 - (n : ℝ) * u)) =
        ((n + 1 : ℕ) : ℝ) * u / (1 - (n : ℝ) * u) := by
    field_simp
    <;> norm_num [Nat.cast_add, Nat.cast_one]
    <;> ring
  rw [heq]
  apply div_le_div_of_nonneg_left
  · exact mul_nonneg (Nat.cast_nonneg _) hu
  · exact hd₂
  · norm_num
    nlinarith

private lemma p29_two_rounds_le_gamma (u : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (h : P29GammaValid u (n + 2)) :
    u + u * (1 + u) ≤ p29Gamma u (n + 2) := by
  have hN : ((n + 2 : ℕ) : ℝ) * u < 1 := h
  have htwo_le : 2 * u ≤ ((n + 2 : ℕ) : ℝ) * u := by
    norm_num
    nlinarith [mul_nonneg (Nat.cast_nonneg n) hu]
  have htwo : 2 * u < 1 := lt_of_le_of_lt htwo_le hN
  have hd₂ : 0 < 1 - 2 * u := sub_pos.mpr htwo
  have hdN : 0 < 1 - ((n + 2 : ℕ) : ℝ) * u := sub_pos.mpr hN
  have hcoeff : u + u * (1 + u) ≤ 2 * u / (1 - 2 * u) := by
    apply (le_div_iff₀ hd₂).2
    nlinarith [mul_nonneg hu hu,
      mul_nonneg (mul_nonneg hu hu) hu]
  calc
    u + u * (1 + u) ≤ 2 * u / (1 - 2 * u) := hcoeff
    _ ≤ ((n + 2 : ℕ) : ℝ) * u /
        (1 - ((n + 2 : ℕ) : ℝ) * u) := by
      apply div_le_div₀
      · exact mul_nonneg (Nat.cast_nonneg _) hu
      · exact htwo_le
      · exact hdN
      · nlinarith
    _ = p29Gamma u (n + 2) := by rfl

private lemma p29RoundedDotProduct_succ_succ
    (fp : P29FPModel) (n : ℕ)
    (x y : Fin (n + 2) → ℝ) :
    p29RoundedDotProduct fp (n + 2) x y =
      fp.fl_add
        (p29RoundedDotProduct fp (n + 1)
          (fun i => x i.castSucc) (fun i => y i.castSucc))
        (fp.fl_mul (x (Fin.last (n + 1))) (y (Fin.last (n + 1)))) := by
  simp [p29RoundedDotProduct, Fin.foldl_succ_last, Fin.succ_last]

private lemma p29GammaValid_of_le (u : ℝ) {a b : ℕ}
    (hu : 0 ≤ u) (hab : a ≤ b) (h : P29GammaValid u b) :
    P29GammaValid u a := by
  unfold P29GammaValid at *
  have hc : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) hu]

private lemma p29_rounded_dot_error
    (fp : P29FPModel) (n : ℕ) (x y : Fin n → ℝ)
    (hvalid : P29GammaValid fp.u n) :
    |p29RoundedDotProduct fp n x y - ∑ k : Fin n, x k * y k| ≤
      p29Gamma fp.u n * ∑ k : Fin n, |x k| * |y k| := by
  revert x y
  induction n using Nat.twoStepInduction with
  | zero =>
      intro x y
      norm_num [p29RoundedDotProduct, p29Gamma]
  | one =>
      intro x y
      obtain ⟨δ, hδ, hmul⟩ := fp.model_mul (x 0) (y 0)
      have huγ : fp.u ≤ p29Gamma fp.u 1 := by
        simpa [p29Gamma] using
          (p29_gamma_step fp.u 0 fp.u_nonneg hvalid)
      calc
        |p29RoundedDotProduct fp 1 x y - ∑ k : Fin 1, x k * y k| =
            |x 0 * y 0| * |δ| := by
              simp [p29RoundedDotProduct, hmul]
              rw [show x 0 * y 0 * (1 + δ) - x 0 * y 0 =
                (x 0 * y 0) * δ by ring]
              simp only [abs_mul]
        _ ≤ |x 0 * y 0| * fp.u :=
          mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
        _ ≤ |x 0 * y 0| * p29Gamma fp.u 1 :=
          mul_le_mul_of_nonneg_left huγ (abs_nonneg _)
        _ = p29Gamma fp.u 1 * ∑ k : Fin 1, |x k| * |y k| := by
          simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, abs_mul]
          ring
  | more n _ ih =>
      intro x y
      let xr : Fin (n + 1) → ℝ := fun i => x i.castSucc
      let yr : Fin (n + 1) → ℝ := fun i => y i.castSucc
      let q : ℝ := p29RoundedDotProduct fp (n + 1) xr yr
      let s : ℝ := ∑ i : Fin (n + 1), xr i * yr i
      let S : ℝ := ∑ i : Fin (n + 1), |xr i| * |yr i|
      let a : ℝ := x (Fin.last (n + 1))
      let b : ℝ := y (Fin.last (n + 1))
      let z : ℝ := a * b
      let Z : ℝ := |a| * |b|
      let t : ℝ := fp.fl_mul a b
      let g : ℝ := p29Gamma fp.u (n + 1)
      let g' : ℝ := p29Gamma fp.u (n + 2)
      have hsmall : P29GammaValid fp.u (n + 1) :=
        p29GammaValid_of_le fp.u fp.u_nonneg (by omega) hvalid
      have hold : |q - s| ≤ g * S := by
        exact ih hsmall xr yr
      have hS : 0 ≤ S := by
        dsimp [S]
        positivity
      have hZ : 0 ≤ Z := by
        dsimp [Z]
        positivity
      have hg : 0 ≤ g := p29_gamma_nonneg fp.u (n + 1) fp.u_nonneg hsmall
      have hs : |s| ≤ S := by
        dsimp [s, S]
        calc
          |∑ i : Fin (n + 1), xr i * yr i| ≤
              ∑ i : Fin (n + 1), |xr i * yr i| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = ∑ i : Fin (n + 1), |xr i| * |yr i| := by
            congr 1
            funext i
            exact abs_mul _ _
      have hq : |q| ≤ (1 + g) * S := by
        calc
          |q| = |(q - s) + s| := by ring_nf
          _ ≤ |q - s| + |s| := abs_add_le _ _
          _ ≤ g * S + S := add_le_add hold hs
          _ = (1 + g) * S := by ring
      obtain ⟨δm, hδm, hmul⟩ := fp.model_mul a b
      have honeδm : |1 + δm| ≤ 1 + fp.u := by
        calc
          |1 + δm| ≤ |(1 : ℝ)| + |δm| := abs_add_le _ _
          _ ≤ 1 + fp.u := by simpa using add_le_add_left hδm 1
      have ht : |t| ≤ (1 + fp.u) * Z := by
        rw [show t = z * (1 + δm) by simpa [t, z] using hmul]
        rw [abs_mul]
        have hzabs : |z| = Z := by simp [z, Z, abs_mul]
        rw [hzabs]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left honeδm hZ
      have hqt : |q + t| ≤ (1 + g) * S + (1 + fp.u) * Z := by
        calc
          |q + t| ≤ |q| + |t| := abs_add_le _ _
          _ ≤ (1 + g) * S + (1 + fp.u) * Z := add_le_add hq ht
      obtain ⟨δa, hδa, hadd⟩ := fp.model_add q t
      have hraw :
          |fp.fl_add q t - (s + z)| ≤
            |q - s| + |z| * |δm| + |q + t| * |δa| := by
        rw [hadd]
        have heq : (q + t) * (1 + δa) - (s + z) =
            (q - s) + z * δm + (q + t) * δa := by
          rw [show t = z * (1 + δm) by simpa [t, z] using hmul]
          ring
        rw [heq]
        calc
          |(q - s) + z * δm + (q + t) * δa| ≤
              |(q - s) + z * δm| + |(q + t) * δa| := abs_add_le _ _
          _ ≤ (|q - s| + |z * δm|) + |(q + t) * δa| := by
            gcongr
            exact abs_add_le _ _
          _ = |q - s| + |z| * |δm| + |q + t| * |δa| := by
            simp only [abs_mul]
      have hzabs : |z| = Z := by simp [z, Z, abs_mul]
      have hR : 0 ≤ (1 + g) * S + (1 + fp.u) * Z := by
        exact add_nonneg
          (mul_nonneg (by linarith) hS)
          (mul_nonneg (by linarith [fp.u_nonneg]) hZ)
      have hmulerr : Z * |δm| ≤ Z * fp.u :=
        mul_le_mul_of_nonneg_left hδm hZ
      have haddErr :
          |q + t| * |δa| ≤
            ((1 + g) * S + (1 + fp.u) * Z) * fp.u := by
        calc
          |q + t| * |δa| ≤
              ((1 + g) * S + (1 + fp.u) * Z) * |δa| :=
            mul_le_mul_of_nonneg_right hqt (abs_nonneg _)
          _ ≤ ((1 + g) * S + (1 + fp.u) * Z) * fp.u :=
            mul_le_mul_of_nonneg_left hδa hR
      have hbound :
          |fp.fl_add q t - (s + z)| ≤
            (g + fp.u * (1 + g)) * S +
              (fp.u + fp.u * (1 + fp.u)) * Z := by
        calc
          |fp.fl_add q t - (s + z)| ≤
              |q - s| + |z| * |δm| + |q + t| * |δa| := hraw
          _ ≤ g * S + Z * fp.u +
              ((1 + g) * S + (1 + fp.u) * Z) * fp.u := by
            rw [hzabs]
            exact add_le_add (add_le_add hold hmulerr) haddErr
          _ = (g + fp.u * (1 + g)) * S +
              (fp.u + fp.u * (1 + fp.u)) * Z := by ring
      have hstep : g + fp.u * (1 + g) ≤ g' := by
        simpa [g, g', Nat.add_assoc] using
          (p29_gamma_step fp.u (n + 1) fp.u_nonneg hvalid)
      have htwo : fp.u + fp.u * (1 + fp.u) ≤ g' := by
        exact p29_two_rounds_le_gamma fp.u n fp.u_nonneg hvalid
      have hfinal : |fp.fl_add q t - (s + z)| ≤ g' * (S + Z) := by
        calc
          |fp.fl_add q t - (s + z)| ≤
              (g + fp.u * (1 + g)) * S +
                (fp.u + fp.u * (1 + fp.u)) * Z := hbound
          _ ≤ g' * S + g' * Z := by
            exact add_le_add
              (mul_le_mul_of_nonneg_right hstep hS)
              (mul_le_mul_of_nonneg_right htwo hZ)
          _ = g' * (S + Z) := by ring
      have hrounded : p29RoundedDotProduct fp (n + 2) x y = fp.fl_add q t := by
        simpa [q, t, xr, yr, a, b] using
          (p29RoundedDotProduct_succ_succ fp n x y)
      have hsum : (∑ i : Fin (n + 2), x i * y i) = s + z := by
        simpa [s, z, xr, yr, a, b] using
          (Fin.sum_univ_castSucc (fun i : Fin (n + 2) => x i * y i))
      have habssum : (∑ i : Fin (n + 2), |x i| * |y i|) = S + Z := by
        simpa [S, Z, xr, yr, a, b] using
          (Fin.sum_univ_castSucc (fun i : Fin (n + 2) => |x i| * |y i|))
      simpa [hrounded, hsum, habssum, g'] using hfinal

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
  have hdot :
      |p29RoundedMatMul fp L11 A12 i j - p29MatMul L11 A12 i j| ≤
        p29Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j| := by
    simpa [p29RoundedMatMul, p29MatMul] using
      (p29_rounded_dot_error fp r (L11 i) (fun k => A12 k j) hvalid)
  obtain ⟨δ, hδ, hsub⟩ :=
    fp.model_sub (A22 i j) (p29RoundedMatMul fp L11 A12 i j)
  unfold p29RoundedSchur p29ExactSchur p29SchurErrorMajorant
  rw [hsub]
  calc
    |(A22 i j - p29RoundedMatMul fp L11 A12 i j) * (1 + δ) -
        (A22 i j - p29MatMul L11 A12 i j)| =
        |(A22 i j - p29RoundedMatMul fp L11 A12 i j) * δ +
          (p29MatMul L11 A12 i j - p29RoundedMatMul fp L11 A12 i j)| := by
      congr 1
      ring
    _ ≤ |(A22 i j - p29RoundedMatMul fp L11 A12 i j) * δ| +
        |p29MatMul L11 A12 i j - p29RoundedMatMul fp L11 A12 i j| :=
      abs_add_le _ _
    _ = |A22 i j - p29RoundedMatMul fp L11 A12 i j| * |δ| +
        |p29RoundedMatMul fp L11 A12 i j - p29MatMul L11 A12 i j| := by
      rw [abs_mul, abs_sub_comm (p29MatMul L11 A12 i j)]
    _ ≤ |A22 i j - p29RoundedMatMul fp L11 A12 i j| * fp.u +
        p29Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j| :=
      add_le_add
        (mul_le_mul_of_nonneg_left hδ (abs_nonneg _)) hdot
    _ = fp.u * |A22 i j - p29RoundedMatMul fp L11 A12 i j| +
        p29Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j| := by
      ring

end HighamBench
