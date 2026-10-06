import HighamBench.P15Definitions

namespace HighamBench

private lemma p15_gamma_nonneg {u : ℝ} (hu : 0 ≤ u) {n : ℕ}
    (h : GammaValid u n) : 0 ≤ gamma u n := by
  unfold gamma GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu)
    (le_of_lt (sub_pos.mpr h))

private lemma p15_gamma_step {u : ℝ} (hu : 0 ≤ u) (n : ℕ)
    (h : GammaValid u (n + 1)) :
    gamma u n + u + gamma u n * u ≤ gamma u (n + 1) := by
  have hn : (n : ℝ) * u ≤ ((n + 1 : ℕ) : ℝ) * u := by
    apply mul_le_mul_of_nonneg_right _ hu
    norm_num
  have hd1 : 0 < 1 - ((n + 1 : ℕ) : ℝ) * u := by
    exact sub_pos.mpr h
  have hd0 : 0 < 1 - (n : ℝ) * u := lt_of_lt_of_le hd1 (sub_le_sub_left hn 1)
  have hnum : 0 ≤ (n : ℝ) * u + u := add_nonneg
    (mul_nonneg (Nat.cast_nonneg _) hu) hu
  have hid : gamma u n + u + gamma u n * u =
      ((n : ℝ) * u + u) / (1 - (n : ℝ) * u) := by
    rw [gamma]
    field_simp
    ring
  rw [hid, gamma]
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hden : 1 - ((n : ℝ) + 1) * u ≤ 1 - (n : ℝ) * u := by
    nlinarith
  have hden' : 1 - ((n + 1 : ℕ) : ℝ) * u ≤
      1 - (n : ℝ) * u := by
    simpa only [Nat.cast_add, Nat.cast_one] using hden
  simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
    (div_le_div_of_nonneg_left hnum hd1 hden')

private lemma p15_gammaValid_of_succ {u : ℝ} (hu : 0 ≤ u) (n : ℕ)
    (h : GammaValid u (n + 1)) : GammaValid u n := by
  unfold GammaValid at *
  have hn : (n : ℝ) * u ≤ ((n + 1 : ℕ) : ℝ) * u := by
    apply mul_le_mul_of_nonneg_right _ hu
    norm_num
  exact lt_of_le_of_lt hn h

private lemma p15_u_le_gamma_succ {u : ℝ} (hu : 0 ≤ u) (n : ℕ)
    (h : GammaValid u (n + 1)) : u ≤ gamma u (n + 1) := by
  have hp := p15_gammaValid_of_succ hu n h
  have hg := p15_gamma_nonneg hu hp
  have hgu : 0 ≤ gamma u n * u := mul_nonneg hg hu
  have hs := p15_gamma_step hu n h
  nlinarith

private lemma p15_error_step {u θ δ : ℝ} (hu : 0 ≤ u) (n : ℕ)
    (h : GammaValid u (n + 1)) (hθ : |θ| ≤ gamma u n) (hδ : |δ| ≤ u) :
    |θ + δ + θ * δ| ≤ gamma u (n + 1) := by
  have hg : 0 ≤ gamma u n :=
    p15_gamma_nonneg hu (p15_gammaValid_of_succ hu n h)
  calc
    |θ + δ + θ * δ| ≤ |θ| + |δ| + |θ * δ| := abs_add_three _ _ _
    _ = |θ| + |δ| + |θ| * |δ| := by rw [abs_mul]
    _ ≤ gamma u n + u + gamma u n * u := by
      gcongr
    _ ≤ gamma u (n + 1) := p15_gamma_step hu n h

private lemma p15_roundedDotProduct_succ (fp : StandardFPModel) (n : ℕ)
    (x y : Fin (n + 1) → ℝ) :
    roundedDotProduct fp (n + 1) x y =
      fp.fl_add
        (roundedDotProduct fp n (fun i ↦ x i.castSucc) (fun i ↦ y i.castSucc))
        (fp.fl_mul (x (Fin.last n)) (y (Fin.last n))) := by
  cases n with
  | zero =>
      simp [roundedDotProduct, fp.fl_add_zero]
  | succ n =>
      simp only [roundedDotProduct]
      rw [Fin.foldl_succ_last]
      congr 4 <;> apply Fin.ext <;> rfl

private lemma p15_roundedDotProduct_backward (fp : StandardFPModel) (n : ℕ)
    (h : GammaValid fp.u n) (x y : Fin n → ℝ) :
    ∃ θ : Fin n → ℝ,
      (∀ j, |θ j| ≤ gamma fp.u n) ∧
      roundedDotProduct fp n x y = ∑ j : Fin n, x j * y j * (1 + θ j) := by
  induction n with
  | zero =>
      refine ⟨fun j ↦ Fin.elim0 j, ?_, ?_⟩
      · intro j
        exact Fin.elim0 j
      · simp [roundedDotProduct]
  | succ n ih =>
      cases n with
      | zero =>
          obtain ⟨δm, hδm, hm⟩ := fp.model_mul (x 0) (y 0)
          refine ⟨fun _ ↦ δm, ?_, ?_⟩
          · intro j
            exact hδm.trans (p15_u_le_gamma_succ fp.u_nonneg 0 h)
          · simpa [roundedDotProduct] using hm
      | succ k =>
          have hprev : GammaValid fp.u (k + 1) := by
            exact p15_gammaValid_of_succ fp.u_nonneg (k + 1) h
          obtain ⟨θ, hθ, hdot⟩ := ih hprev
            (fun i ↦ x i.castSucc) (fun i ↦ y i.castSucc)
          obtain ⟨δm, hδm, hm⟩ :=
            fp.model_mul (x (Fin.last (k + 1))) (y (Fin.last (k + 1)))
          obtain ⟨δa, hδa, ha⟩ := fp.model_add
            (roundedDotProduct fp (k + 1) (fun i ↦ x i.castSucc)
              (fun i ↦ y i.castSucc))
            (fp.fl_mul (x (Fin.last (k + 1))) (y (Fin.last (k + 1))))
          let θlast := δm + δa + δm * δa
          let θcast : Fin (k + 1) → ℝ :=
            fun i ↦ θ i + δa + θ i * δa
          let θ' : Fin (k + 1 + 1) → ℝ := Fin.lastCases θlast θcast
          refine ⟨θ', ?_, ?_⟩
          · intro j
            refine Fin.lastCases ?_ (fun i ↦ ?_) j
            · simp only [θ', θlast, Fin.lastCases_last]
              apply p15_error_step fp.u_nonneg (k + 1) h
              · exact hδm.trans (p15_u_le_gamma_succ fp.u_nonneg k hprev)
              · exact hδa
            · simp only [θ', θcast, Fin.lastCases_castSucc]
              exact p15_error_step fp.u_nonneg (k + 1) h (hθ i) hδa
          · rw [p15_roundedDotProduct_succ, ha, hm, hdot]
            nth_rewrite 2 [Fin.sum_univ_castSucc]
            simp only [θ', θcast, θlast, Fin.lastCases_castSucc,
              Fin.lastCases_last]
            have hp :
                (∑ i : Fin (k + 1),
                    x i.castSucc * y i.castSucc * (1 + (θ i + δa + θ i * δa))) =
                  (∑ i : Fin (k + 1), x i.castSucc * y i.castSucc * (1 + θ i)) *
                    (1 + δa) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i hi
              ring
            rw [hp]
            ring

private lemma p15_roundedRectMatVec_backward (fp : StandardFPModel) {m n : ℕ}
    (h : GammaValid fp.u n) (A : P15RectMatrix m n) (x : Fin n → ℝ) :
    ∃ Δ : P15RectMatrix m n,
      p15RectFrobNorm Δ ≤ gamma fp.u n * p15RectFrobNorm A ∧
      p15RoundedRectMatVec fp A x = p15RectMatVec (p15RectAdd A Δ) x := by
  classical
  let hex (i : Fin m) := p15_roundedDotProduct_backward fp n h (A i) x
  let θ : Fin m → Fin n → ℝ := fun i ↦ Classical.choose (hex i)
  have hθ (i : Fin m) (j : Fin n) : |θ i j| ≤ gamma fp.u n :=
    (Classical.choose_spec (hex i)).1 j
  have hdot (i : Fin m) :
      roundedDotProduct fp n (A i) x =
        ∑ j : Fin n, A i j * x j * (1 + θ i j) :=
    (Classical.choose_spec (hex i)).2
  let Δ : P15RectMatrix m n := fun i j ↦ A i j * θ i j
  refine ⟨Δ, ?_, ?_⟩
  · have hg : 0 ≤ gamma fp.u n := p15_gamma_nonneg fp.u_nonneg h
    have hpoint (i : Fin m) (j : Fin n) :
        (Δ i j) ^ 2 ≤ (gamma fp.u n) ^ 2 * (A i j) ^ 2 := by
      have hθsq : (θ i j) ^ 2 ≤ (gamma fp.u n) ^ 2 := by
        rw [sq_le_sq]
        simpa [abs_of_nonneg hg] using hθ i j
      change (A i j * θ i j) ^ 2 ≤ (gamma fp.u n) ^ 2 * (A i j) ^ 2
      calc
        (A i j * θ i j) ^ 2 = (θ i j) ^ 2 * (A i j) ^ 2 := by ring
        _ ≤ (gamma fp.u n) ^ 2 * (A i j) ^ 2 :=
          mul_le_mul_of_nonneg_right hθsq (sq_nonneg (A i j))
    have hsum :
        (∑ i : Fin m, ∑ j : Fin n, (Δ i j) ^ 2) ≤
          (gamma fp.u n) ^ 2 * (∑ i : Fin m, ∑ j : Fin n, (A i j) ^ 2) := by
      calc
        (∑ i : Fin m, ∑ j : Fin n, (Δ i j) ^ 2) ≤
            ∑ i : Fin m, ∑ j : Fin n,
              (gamma fp.u n) ^ 2 * (A i j) ^ 2 := by
          exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hpoint i j
        _ = (gamma fp.u n) ^ 2 *
              (∑ i : Fin m, ∑ j : Fin n, (A i j) ^ 2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
    have hΔsum : 0 ≤ ∑ i : Fin m, ∑ j : Fin n, (Δ i j) ^ 2 := by
      positivity
    have hAsum : 0 ≤ ∑ i : Fin m, ∑ j : Fin n, (A i j) ^ 2 := by
      positivity
    unfold p15RectFrobNorm
    apply (sq_le_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg hg (Real.sqrt_nonneg _))).mp
    rw [Real.sq_sqrt hΔsum, mul_pow, Real.sq_sqrt hAsum]
    exact hsum
  · funext i
    change roundedDotProduct fp n (A i) x =
      ∑ j : Fin n, (A i j + Δ i j) * x j
    rw [hdot i]
    apply Finset.sum_congr rfl
    intro j hj
    change A i j * x j * (1 + θ i j) =
      (A i j + A i j * θ i j) * x j
    ring

private lemma p15_rectMatVec_matMul {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p) (x : Fin p → ℝ) :
    p15RectMatVec (p15RectMatMul A B) x =
      p15RectMatVec A (p15RectMatVec B x) := by
  funext i
  simp only [p15RectMatVec, p15RectMatMul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

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
    p15_roundedRectMatVec_backward fp hb (p15RectTranspose Y) v
  obtain ⟨ΔX, hΔX, hz⟩ :=
    p15_roundedRectMatVec_backward fp hr X
      (p15RoundedRectMatVec fp (p15RectTranspose Y) v)
  refine ⟨ΔYT, ΔX, hΔYT, hΔX, hw, hz, ?_⟩
  rw [p15_rectMatVec_matMul, ← hw]
  exact hz

end HighamBench
