import HighamBench.P29Definitions

namespace HighamBench

lemma p29_gamma_step_old (u : ℝ) (q : ℕ)
    (hu : 0 ≤ u) (hv : ((q + 1 : ℕ) : ℝ) * u < 1) :
    (1 + u) * p29Gamma u q + u ≤ p29Gamma u (q + 1) := by
  have hdq : 0 < 1 - (q : ℝ) * u := by
    push_cast at hv
    nlinarith [show (0 : ℝ) ≤ (q : ℝ) by positivity]
  have hdqs : 0 < 1 - ((q + 1 : ℕ) : ℝ) * u := by
    linarith
  have hn : 0 ≤ ((q : ℝ) + 1) * u := mul_nonneg (by positivity) hu
  have hdn : 1 - u * (q : ℝ) ≠ 0 := by nlinarith [hdq]
  rw [p29Gamma, p29Gamma]
  push_cast
  rw [show (1 + u) * ((q : ℝ) * u / (1 - (q : ℝ) * u)) + u =
      (((q : ℝ) + 1) * u) / (1 - (q : ℝ) * u) by
        field_simp [hdn]
        ring]
  apply div_le_div_of_nonneg_left hn
  · simpa only [Nat.cast_add, Nat.cast_one] using hdqs
  · nlinarith

lemma p29_gamma_step_new (u : ℝ) (q : ℕ)
    (hu : 0 ≤ u) (hq : 1 ≤ q)
    (hv : ((q + 1 : ℕ) : ℝ) * u < 1) :
    2 * u + u ^ 2 ≤ p29Gamma u (q + 1) := by
  have hd : 0 < 1 - ((q + 1 : ℕ) : ℝ) * u := by linarith
  rw [p29Gamma]
  apply (le_div_iff₀ hd).2
  have hq' : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  push_cast
  have h₁ : 0 ≤ ((q : ℝ) - 1) * u :=
    mul_nonneg (sub_nonneg.mpr hq') hu
  have h₂ : 0 ≤ (2 * (q : ℝ) + 1) * u ^ 2 := mul_nonneg (by positivity) (sq_nonneg u)
  have h₃ : 0 ≤ ((q : ℝ) + 1) * u ^ 3 := mul_nonneg (by positivity) (by positivity)
  nlinarith

lemma p29_rounded_accum_step (fp : P29FPModel) (q : ℕ)
    (hq : 1 ≤ q) (x y a s B : ℝ)
    (hB : |s| ≤ B)
    (ha : |a - s| ≤ p29Gamma fp.u q * B)
    (hv : ((q + 1 : ℕ) : ℝ) * fp.u < 1) :
    |fp.fl_add a (fp.fl_mul x y) - (s + x * y)| ≤
      p29Gamma fp.u (q + 1) * (B + |x * y|) := by
  rcases fp.model_mul x y with ⟨δm, hδm, hm⟩
  rcases fp.model_add a (fp.fl_mul x y) with ⟨δa, hδa, hadd⟩
  let z : ℝ := x * y
  have hmerr : |fp.fl_mul x y - z| ≤ fp.u * |z| := by
    rw [hm]
    change |z * (1 + δm) - z| ≤ fp.u * |z|
    rw [show z * (1 + δm) - z = z * δm by ring, abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left hδm (abs_nonneg z)]
  have hadderr :
      |fp.fl_add a (fp.fl_mul x y) - (a + fp.fl_mul x y)| ≤
        fp.u * |a + fp.fl_mul x y| := by
    rw [hadd]
    rw [show (a + fp.fl_mul x y) * (1 + δa) -
        (a + fp.fl_mul x y) = (a + fp.fl_mul x y) * δa by ring,
      abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left hδa
      (abs_nonneg (a + fp.fl_mul x y))]
  have habase :
      |(a + fp.fl_mul x y) - (s + z)| ≤
        |a - s| + |fp.fl_mul x y - z| := by
    rw [show (a + fp.fl_mul x y) - (s + z) =
        (a - s) + (fp.fl_mul x y - z) by ring]
    exact abs_add_le _ _
  have haabs : |a| ≤ p29Gamma fp.u q * B + B := by
    calc
      |a| = |(a - s) + s| := by ring_nf
      _ ≤ |a - s| + |s| := abs_add_le _ _
      _ ≤ p29Gamma fp.u q * B + B := add_le_add ha hB
  have hmabs : |fp.fl_mul x y| ≤ fp.u * |z| + |z| := by
    calc
      |fp.fl_mul x y| = |(fp.fl_mul x y - z) + z| := by ring_nf
      _ ≤ |fp.fl_mul x y - z| + |z| := abs_add_le _ _
      _ ≤ fp.u * |z| + |z| := add_le_add hmerr (le_refl _)
  have hafm : |a + fp.fl_mul x y| ≤
      B + p29Gamma fp.u q * B + |z| + fp.u * |z| := by
    calc
      |a + fp.fl_mul x y| ≤ |a| + |fp.fl_mul x y| := abs_add_le _ _
      _ ≤ (p29Gamma fp.u q * B + B) + (fp.u * |z| + |z|) :=
        add_le_add haabs hmabs
      _ = B + p29Gamma fp.u q * B + |z| + fp.u * |z| := by ring
  have hB0 : 0 ≤ B := le_trans (abs_nonneg s) hB
  have hmain :
      |fp.fl_add a (fp.fl_mul x y) - (s + z)| ≤
        ((1 + fp.u) * p29Gamma fp.u q + fp.u) * B +
          (2 * fp.u + fp.u ^ 2) * |z| := by
    calc
      |fp.fl_add a (fp.fl_mul x y) - (s + z)| ≤
          |fp.fl_add a (fp.fl_mul x y) - (a + fp.fl_mul x y)| +
            |(a + fp.fl_mul x y) - (s + z)| :=
        abs_sub_le _ _ _
      _ ≤ fp.u * |a + fp.fl_mul x y| +
          (|a - s| + |fp.fl_mul x y - z|) :=
        add_le_add hadderr habase
      _ ≤ fp.u * (B + p29Gamma fp.u q * B + |z| + fp.u * |z|) +
          (p29Gamma fp.u q * B + fp.u * |z|) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hafm fp.u_nonneg)
          (add_le_add ha hmerr)
      _ = ((1 + fp.u) * p29Gamma fp.u q + fp.u) * B +
          (2 * fp.u + fp.u ^ 2) * |z| := by ring
  have hold := p29_gamma_step_old fp.u q fp.u_nonneg hv
  have hnew := p29_gamma_step_new fp.u q fp.u_nonneg hq hv
  have holdB := mul_le_mul_of_nonneg_right hold hB0
  have hnewz := mul_le_mul_of_nonneg_right hnew (abs_nonneg z)
  change |fp.fl_add a (fp.fl_mul x y) - (s + z)| ≤
    p29Gamma fp.u (q + 1) * (B + |z|)
  calc
    |fp.fl_add a (fp.fl_mul x y) - (s + z)| ≤
        ((1 + fp.u) * p29Gamma fp.u q + fp.u) * B +
          (2 * fp.u + fp.u ^ 2) * |z| := hmain
    _ ≤ p29Gamma fp.u (q + 1) * B +
          p29Gamma fp.u (q + 1) * |z| := add_le_add holdB hnewz
    _ = p29Gamma fp.u (q + 1) * (B + |z|) := by ring

lemma p29_rounded_fold_bound (fp : P29FPModel) :
    ∀ (n q : ℕ), 1 ≤ q →
      ∀ (x y : Fin n → ℝ) (a s B : ℝ),
        (((q + n : ℕ) : ℝ) * fp.u < 1) →
        |s| ≤ B →
        |a - s| ≤ p29Gamma fp.u q * B →
        |Fin.foldl n
              (fun acc i => fp.fl_add acc (fp.fl_mul (x i) (y i))) a -
            (s + ∑ i : Fin n, x i * y i)| ≤
          p29Gamma fp.u (q + n) *
            (B + ∑ i : Fin n, |x i * y i|) := by
  intro n
  induction n with
  | zero =>
      intro q hq x y a s B hv hB ha
      simpa using ha
  | succ n ih =>
      intro q hq x y a s B hv hB ha
      let z : ℝ := x 0 * y 0
      have hvstep : (((q + 1 : ℕ) : ℝ) * fp.u < 1) := by
        have hn : 0 ≤ (n : ℝ) * fp.u := mul_nonneg (by positivity) fp.u_nonneg
        push_cast at hv ⊢
        nlinarith
      have hfirst :
          |fp.fl_add a (fp.fl_mul (x 0) (y 0)) - (s + z)| ≤
            p29Gamma fp.u (q + 1) * (B + |z|) :=
        p29_rounded_accum_step fp q hq (x 0) (y 0) a s B hB ha hvstep
      have hBfirst : |s + z| ≤ B + |z| := by
        calc
          |s + z| ≤ |s| + |z| := abs_add_le _ _
          _ ≤ B + |z| := add_le_add hB (le_refl _)
      have hvrest : ((((q + 1) + n : ℕ) : ℝ) * fp.u < 1) := by
        push_cast at hv ⊢
        nlinarith
      have hrest := ih (q + 1) (by omega)
        (fun i : Fin n => x i.succ) (fun i : Fin n => y i.succ)
        (fp.fl_add a (fp.fl_mul (x 0) (y 0))) (s + z) (B + |z|)
        hvrest hBfirst hfirst
      simpa only [Fin.foldl_succ, Fin.sum_univ_succ, z, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm, add_assoc] using hrest

lemma p29_u_le_gamma_one (u : ℝ) (hu : 0 ≤ u) (hlt : u < 1) :
    u ≤ p29Gamma u 1 := by
  rw [p29Gamma]
  norm_num
  apply (le_div_iff₀ (sub_pos.mpr hlt)).2
  nlinarith [sq_nonneg u, hu]

lemma p29_rounded_dot_product_error (fp : P29FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hvalid : P29GammaValid fp.u n) :
    |p29RoundedDotProduct fp n x y - ∑ i : Fin n, x i * y i| ≤
      p29Gamma fp.u n * ∑ i : Fin n, |x i * y i| := by
  cases n with
  | zero =>
      simp [p29RoundedDotProduct, p29Gamma]
  | succ n =>
      let z : ℝ := x 0 * y 0
      have hv : (((n + 1 : ℕ) : ℝ) * fp.u < 1) := hvalid
      have hu1 : fp.u < 1 := by
        have hn : 0 ≤ (n : ℝ) * fp.u := mul_nonneg (by positivity) fp.u_nonneg
        push_cast at hv
        nlinarith
      rcases fp.model_mul (x 0) (y 0) with ⟨δ, hδ, hmul⟩
      have hmulerr : |fp.fl_mul (x 0) (y 0) - z| ≤ fp.u * |z| := by
        rw [hmul]
        change |z * (1 + δ) - z| ≤ fp.u * |z|
        rw [show z * (1 + δ) - z = z * δ by ring, abs_mul]
        simpa [mul_comm] using
          (mul_le_mul_of_nonneg_left hδ (abs_nonneg z))
      have hinit : |fp.fl_mul (x 0) (y 0) - z| ≤
          p29Gamma fp.u 1 * |z| := by
        exact le_trans hmulerr (mul_le_mul_of_nonneg_right
          (p29_u_le_gamma_one fp.u fp.u_nonneg hu1) (abs_nonneg z))
      have hfold := p29_rounded_fold_bound fp n 1 (by omega)
        (fun i : Fin n => x i.succ) (fun i : Fin n => y i.succ)
        (fp.fl_mul (x 0) (y 0)) z |z|
        (by simpa [Nat.add_comm] using hv) (le_refl _) hinit
      simpa only [p29RoundedDotProduct, Fin.sum_univ_succ, z,
        Nat.add_comm, add_assoc] using hfold

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
  simp only [p29RoundedSchur, p29ExactSchur, p29SchurErrorMajorant,
    p29RoundedMatMul, p29MatMul]
  let rp := p29RoundedDotProduct fp r (L11 i) (fun k => A12 k j)
  let ep := ∑ k : Fin r, L11 i k * A12 k j
  have hdot : |rp - ep| ≤
      p29Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j| := by
    have h := p29_rounded_dot_product_error fp r (L11 i)
      (fun k => A12 k j) hvalid
    simpa only [rp, ep, abs_mul] using h
  rcases fp.model_sub (A22 i j) rp with ⟨δ, hδ, hsub⟩
  have hsuberr :
      |fp.fl_sub (A22 i j) rp - (A22 i j - rp)| ≤
        fp.u * |A22 i j - rp| := by
    rw [hsub]
    rw [show (A22 i j - rp) * (1 + δ) - (A22 i j - rp) =
        (A22 i j - rp) * δ by ring, abs_mul]
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left hδ (abs_nonneg (A22 i j - rp)))
  have hexact :
      |(A22 i j - rp) - (A22 i j - ep)| ≤
        p29Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j| := by
    rw [show (A22 i j - rp) - (A22 i j - ep) = ep - rp by ring,
      abs_sub_comm]
    exact hdot
  change |fp.fl_sub (A22 i j) rp - (A22 i j - ep)| ≤
    fp.u * |A22 i j - rp| +
      p29Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j|
  calc
    |fp.fl_sub (A22 i j) rp - (A22 i j - ep)| ≤
        |fp.fl_sub (A22 i j) rp - (A22 i j - rp)| +
          |(A22 i j - rp) - (A22 i j - ep)| := abs_sub_le _ _ _
    _ ≤ fp.u * |A22 i j - rp| +
        p29Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j| :=
      add_le_add hsuberr hexact

end HighamBench
