import HighamBench.P15Definitions

namespace HighamBench

lemma p15_gamma_nonneg {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (h : GammaValid u n) : 0 ≤ gamma u n := by
  unfold GammaValid at h
  rw [gamma]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (sub_nonneg.mpr h.le)

lemma p15_gamma_valid_mono {u : ℝ} {m n : ℕ} (hu : 0 ≤ u)
    (hmn : m ≤ n) (h : GammaValid u n) : GammaValid u m := by
  unfold GammaValid at h ⊢
  have hc : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  nlinarith

lemma p15_error_comp_gamma_succ {u a d : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hv : GammaValid u (n + 1))
    (ha : |a| ≤ gamma u n) (hd : |d| ≤ u) :
    |(1 + a) * (1 + d) - 1| ≤ gamma u (n + 1) := by
  have hvn : GammaValid u n :=
    p15_gamma_valid_mono hu (Nat.le_succ n) hv
  have hgn : 0 ≤ gamma u n := p15_gamma_nonneg hu hvn
  have h1 : |a + d + a * d| ≤ |a| + |d| + |a| * |d| := by
    calc
      |a + d + a * d| ≤ |a + d| + |a * d| := abs_add_le _ _
      _ ≤ (|a| + |d|) + |a| * |d| := by
        rw [abs_mul]
        gcongr
        exact abs_add_le _ _
  have h2 : |a| + |d| + |a| * |d| ≤
      gamma u n + u + gamma u n * u := by
    gcongr
  have hdenn : 0 < 1 - (n : ℝ) * u := by
    simpa [GammaValid] using hvn
  have hdens : 0 < 1 - ((n + 1 : ℕ) : ℝ) * u := by
    simpa [GammaValid] using hv
  have h3 : gamma u n + u + gamma u n * u ≤ gamma u (n + 1) := by
    have heq : gamma u n + u + gamma u n * u =
        (((n + 1 : ℕ) : ℝ) * u) / (1 - (n : ℝ) * u) := by
      rw [gamma]
      field_simp [ne_of_gt hdenn]
      push_cast
      ring
    rw [heq, gamma]
    apply div_le_div_of_nonneg_left
    · positivity
    · exact hdens
    · push_cast
      nlinarith
  rw [show (1 + a) * (1 + d) - 1 = a + d + a * d by ring]
  exact h1.trans (h2.trans h3)

lemma p15_u_le_gamma {u : ℝ} {n : ℕ} (hu : 0 ≤ u) (hn : 1 ≤ n)
    (hv : GammaValid u n) : u ≤ gamma u n := by
  have hden : 0 < 1 - (n : ℝ) * u := by
    simpa [GammaValid] using hv
  rw [gamma, le_div_iff₀ hden]
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h₁ : 0 ≤ ((n : ℝ) - 1) * u := mul_nonneg (sub_nonneg.mpr hn') hu
  have h₂ : 0 ≤ (n : ℝ) * u * u :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) hu
  nlinarith

lemma p15_roundedDotProduct_succ_succ (fp : StandardFPModel) (n : ℕ)
    (x y : Fin (n + 2) → ℝ) :
    roundedDotProduct fp (n + 2) x y =
      fp.fl_add
        (roundedDotProduct fp (n + 1)
          (fun i ↦ x i.castSucc) (fun i ↦ y i.castSucc))
        (fp.fl_mul (x (Fin.last (n + 1))) (y (Fin.last (n + 1)))) := by
  simp only [roundedDotProduct, Fin.foldl_succ_last]
  congr 2

lemma p15_roundedDotProduct_backward (fp : StandardFPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hv : GammaValid fp.u n) :
    ∃ e : Fin n → ℝ,
      (∀ i, |e i| ≤ gamma fp.u n) ∧
      roundedDotProduct fp n x y = ∑ i, x i * y i * (1 + e i) := by
  induction n using Nat.twoStepInduction with
  | zero =>
      refine ⟨fun i ↦ Fin.elim0 i, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · simp [roundedDotProduct]
  | one =>
      obtain ⟨d, hd, hmul⟩ := fp.model_mul (x 0) (y 0)
      refine ⟨fun _ ↦ d, ?_, ?_⟩
      · intro i
        exact hd.trans (p15_u_le_gamma fp.u_nonneg (by omega) hv)
      · simpa [roundedDotProduct, hmul] using hmul
  | more n _ ih =>
      have hvp : GammaValid fp.u (n + 1) :=
        p15_gamma_valid_mono fp.u_nonneg (by omega) hv
      obtain ⟨e, he, hprefix⟩ := ih
        (fun i ↦ x i.castSucc) (fun i ↦ y i.castSucc) hvp
      obtain ⟨dm, hdm, hmul⟩ :=
        fp.model_mul (x (Fin.last (n + 1))) (y (Fin.last (n + 1)))
      obtain ⟨da, hda, hadd⟩ := fp.model_add
        (roundedDotProduct fp (n + 1)
          (fun i ↦ x i.castSucc) (fun i ↦ y i.castSucc))
        (fp.fl_mul (x (Fin.last (n + 1))) (y (Fin.last (n + 1))))
      let e' : Fin (n + 2) → ℝ := Fin.lastCases
        ((1 + dm) * (1 + da) - 1)
        (fun i ↦ (1 + e i) * (1 + da) - 1)
      refine ⟨e', ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simpa [e', Nat.add_assoc] using
            (p15_error_comp_gamma_succ (n := n + 1) fp.u_nonneg hv
              (hdm.trans (p15_u_le_gamma fp.u_nonneg (by omega) hvp)) hda)
        · simpa [e', Nat.add_assoc] using
            (p15_error_comp_gamma_succ (n := n + 1) fp.u_nonneg hv (he j) hda)
      · rw [p15_roundedDotProduct_succ_succ, hadd, hprefix, hmul]
        conv_rhs => rw [Fin.sum_univ_castSucc]
        simp only [e', Fin.lastCases_castSucc, Fin.lastCases_last]
        rw [add_mul, Finset.sum_mul]
        apply congrArg₂ (.+.)
        · apply Finset.sum_congr rfl
          intro i _
          ring
        · ring

lemma p15_roundedRectMatVec_backward (fp : StandardFPModel) {m n : ℕ}
    (A : P15RectMatrix m n) (x : Fin n → ℝ)
    (hv : GammaValid fp.u n) :
    ∃ Δ : P15RectMatrix m n,
      p15RectFrobNorm Δ ≤ gamma fp.u n * p15RectFrobNorm A ∧
      p15RoundedRectMatVec fp A x =
        p15RectMatVec (p15RectAdd A Δ) x := by
  classical
  have hrows : ∀ i : Fin m, ∃ e : Fin n → ℝ,
      (∀ j, |e j| ≤ gamma fp.u n) ∧
      roundedDotProduct fp n (A i) x = ∑ j, A i j * x j * (1 + e j) := by
    intro i
    exact p15_roundedDotProduct_backward fp n (A i) x hv
  choose e he hdot using hrows
  let Δ : P15RectMatrix m n := fun i j ↦ A i j * e i j
  refine ⟨Δ, ?_, ?_⟩
  · have hg : 0 ≤ gamma fp.u n := p15_gamma_nonneg fp.u_nonneg hv
    have hentry : ∀ i j, Δ i j ^ 2 ≤
        gamma fp.u n ^ 2 * A i j ^ 2 := by
      intro i j
      have he_sq : e i j ^ 2 ≤ gamma fp.u n ^ 2 := by
        rw [sq_le_sq]
        simpa [abs_of_nonneg hg] using he i j
      dsimp [Δ]
      calc
        (A i j * e i j) ^ 2 = A i j ^ 2 * e i j ^ 2 := by ring
        _ ≤ A i j ^ 2 * gamma fp.u n ^ 2 :=
          mul_le_mul_of_nonneg_left he_sq (sq_nonneg _)
        _ = gamma fp.u n ^ 2 * A i j ^ 2 := by ring
    have hsum : (∑ i : Fin m, ∑ j : Fin n, Δ i j ^ 2) ≤
        gamma fp.u n ^ 2 * (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
      calc
        (∑ i : Fin m, ∑ j : Fin n, Δ i j ^ 2) ≤
            ∑ i : Fin m, ∑ j : Fin n,
              gamma fp.u n ^ 2 * A i j ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          exact hentry i j
        _ = gamma fp.u n ^ 2 *
            (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
          simp_rw [Finset.mul_sum]
    unfold p15RectFrobNorm
    calc
      Real.sqrt (∑ i : Fin m, ∑ j : Fin n, Δ i j ^ 2) ≤
          Real.sqrt (gamma fp.u n ^ 2 *
            (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2)) :=
        Real.sqrt_le_sqrt hsum
      _ = Real.sqrt (gamma fp.u n ^ 2) *
          Real.sqrt (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg (gamma fp.u n))]
      _ = gamma fp.u n *
          Real.sqrt (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
        rw [Real.sqrt_sq hg]
  · funext i
    change roundedDotProduct fp n (A i) x =
      ∑ j : Fin n, (A i j + Δ i j) * x j
    rw [hdot i]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [Δ]
    ring

lemma p15_rectMatVec_rectMatMul {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p) (x : Fin p → ℝ) :
    p15RectMatVec A (p15RectMatVec B x) =
      p15RectMatVec (p15RectMatMul A B) x := by
  change A.mulVec (B.mulVec x) = (A * B).mulVec x
  exact Matrix.mulVec_mulVec x A B

/-- P15-T1: equations (3.3) and (3.4) in the proof of Lemma 3.1, including
their Frobenius-norm bounds and the composition used immediately afterward. -/
theorem p15_t1_low_rank_matvec_backward_representation
    {b r : ℕ} (fp : StandardFPModel)
    (X Y : P15RectMatrix b r) (v : P15Vector b)
    (hb : GammaValid fp.u b) (hr : GammaValid fp.u r) :
    let wHat := p15RoundedRectMatVec fp (p15RectTranspose Y) v
    let zHat := p15RoundedRectMatVec fp X wHat
    ∃ ΔYT : P15RectMatrix r b, ∃ ΔX : P15RectMatrix b r,
      p15RectFrobNorm ΔYT ≤
          gamma fp.u b * p15RectFrobNorm (p15RectTranspose Y) ∧
      p15RectFrobNorm ΔX ≤ gamma fp.u r * p15RectFrobNorm X ∧
      wHat = p15RectMatVec (p15RectAdd (p15RectTranspose Y) ΔYT) v ∧
      zHat = p15RectMatVec (p15RectAdd X ΔX) wHat ∧
      zHat = p15RectMatVec
        (p15RectMatMul (p15RectAdd X ΔX)
          (p15RectAdd (p15RectTranspose Y) ΔYT)) v := by
  -- PROOF_START P15-T1-H001
  dsimp only
  obtain ⟨ΔYT, hΔYT, hw⟩ :=
    p15_roundedRectMatVec_backward fp (p15RectTranspose Y) v hb
  obtain ⟨ΔX, hΔX, hz⟩ := p15_roundedRectMatVec_backward fp X
    (p15RoundedRectMatVec fp (p15RectTranspose Y) v) hr
  refine ⟨ΔYT, ΔX, hΔYT, hΔX, hw, hz, ?_⟩
  calc
    p15RoundedRectMatVec fp X
        (p15RoundedRectMatVec fp (p15RectTranspose Y) v) =
        p15RectMatVec (p15RectAdd X ΔX)
          (p15RoundedRectMatVec fp (p15RectTranspose Y) v) := hz
    _ = p15RectMatVec (p15RectAdd X ΔX)
          (p15RectMatVec (p15RectAdd (p15RectTranspose Y) ΔYT) v) := by
        rw [hw]
    _ = p15RectMatVec
          (p15RectMatMul (p15RectAdd X ΔX)
            (p15RectAdd (p15RectTranspose Y) ΔYT)) v :=
        p15_rectMatVec_rectMatMul _ _ _

end HighamBench
