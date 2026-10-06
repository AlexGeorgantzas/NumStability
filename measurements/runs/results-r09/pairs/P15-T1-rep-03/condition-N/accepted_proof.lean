import HighamBench.P15Definitions

namespace HighamBench

private lemma p15_t1_gamma_nonneg {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (h : GammaValid u n) : 0 ≤ gamma u n := by
  rw [gamma]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu)
    (le_of_lt (sub_pos.mpr h))

private lemma p15_t1_gamma_step {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (h : GammaValid u (n + 1)) :
    gamma u n + u + gamma u n * u ≤ gamma u (n + 1) := by
  have hn : (n : ℝ) * u < 1 := by
    dsimp [GammaValid] at h ⊢
    push_cast at h
    nlinarith
  have hdenn : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hn
  have hdens : 0 < 1 - ((n + 1 : ℕ) : ℝ) * u := sub_pos.mpr h
  have hnum : 0 ≤ ((n + 1 : ℕ) : ℝ) * u :=
    mul_nonneg (Nat.cast_nonneg _) hu
  rw [gamma, gamma]
  have heq :
      (n : ℝ) * u / (1 - (n : ℝ) * u) + u +
          ((n : ℝ) * u / (1 - (n : ℝ) * u)) * u =
        ((n + 1 : ℕ) : ℝ) * u / (1 - (n : ℝ) * u) := by
    field_simp
    push_cast
    ring
  rw [heq]
  apply div_le_div_of_nonneg_left hnum hdens
  push_cast
  nlinarith

private lemma p15_t1_roundedDot_succ_last (fp : StandardFPModel) (n : ℕ)
    (x y : Fin (n + 2) → ℝ) :
    roundedDotProduct fp (n + 2) x y =
      fp.fl_add
        (roundedDotProduct fp (n + 1)
          (fun i => x i.castSucc) (fun i => y i.castSucc))
        (fp.fl_mul (x (Fin.last (n + 1))) (y (Fin.last (n + 1)))) := by
  simp [roundedDotProduct, Fin.foldl_succ_last]

private lemma p15_t1_gamma_valid_of_le {u : ℝ} {m n : ℕ}
    (h : GammaValid u n) (hmn : m ≤ n) (hu : 0 ≤ u) :
    GammaValid u m := by
  dsimp [GammaValid] at h ⊢
  have hc : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  nlinarith

private lemma p15_t1_theta_step {u θ δ : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hv : GammaValid u (n + 1))
    (hθ : |θ| ≤ gamma u n) (hδ : |δ| ≤ u) :
    |(1 + θ) * (1 + δ) - 1| ≤ gamma u (n + 1) := by
  have hvn : GammaValid u n :=
    p15_t1_gamma_valid_of_le hv (Nat.le_succ n) hu
  have hγ : 0 ≤ gamma u n := p15_t1_gamma_nonneg hu hvn
  have hprod : |θ| * |δ| ≤ gamma u n * u :=
    mul_le_mul hθ hδ (abs_nonneg δ) hγ
  calc
    |(1 + θ) * (1 + δ) - 1| = |θ + δ + θ * δ| := by ring_nf
    _ ≤ |θ| + |δ| + |θ * δ| := by
      exact (abs_add_le (θ + δ) (θ * δ)).trans
        (add_le_add (abs_add_le θ δ) le_rfl)
    _ = |θ| + |δ| + |θ| * |δ| := by rw [abs_mul]
    _ ≤ gamma u n + u + gamma u n * u := by linarith
    _ ≤ gamma u (n + 1) := p15_t1_gamma_step hu hv

private lemma p15_t1_u_le_gamma {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hn : 1 ≤ n) (hv : GammaValid u n) : u ≤ gamma u n := by
  have hden : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hv
  rw [gamma]
  apply (le_div_iff₀ hden).2
  have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [mul_nonneg (Nat.cast_nonneg n) (sq_nonneg u)]

private lemma p15_t1_roundedDot_backward (fp : StandardFPModel) :
    ∀ (n : ℕ), GammaValid fp.u n → ∀ (x y : Fin n → ℝ),
      ∃ θ : Fin n → ℝ,
        (∀ i, |θ i| ≤ gamma fp.u n) ∧
        roundedDotProduct fp n x y =
          ∑ i : Fin n, (x i * (1 + θ i)) * y i := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      intro h x y
      refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · simp [roundedDotProduct]
  | one =>
      intro h x y
      obtain ⟨δ, hδ, hmul⟩ := fp.model_mul (x 0) (y 0)
      refine ⟨fun _ => δ, ?_, ?_⟩
      · intro i
        have hs := p15_t1_gamma_step (n := 0) fp.u_nonneg h
        have huγ : fp.u ≤ gamma fp.u 1 := by simpa [gamma] using hs
        exact hδ.trans huγ
      · simp [roundedDotProduct, hmul]
        ring
  | more n ih ih' =>
      intro h x y
      have hprev : GammaValid fp.u (n + 1) :=
        p15_t1_gamma_valid_of_le h (by omega) fp.u_nonneg
      obtain ⟨θ, hθ, hdot⟩ := ih' hprev
        (fun i => x i.castSucc) (fun i => y i.castSucc)
      obtain ⟨ε, hε, hmul⟩ :=
        fp.model_mul (x (Fin.last (n + 1))) (y (Fin.last (n + 1)))
      obtain ⟨δ, hδ, hadd⟩ := fp.model_add
        (roundedDotProduct fp (n + 1)
          (fun i => x i.castSucc) (fun i => y i.castSucc))
        (fp.fl_mul (x (Fin.last (n + 1))) (y (Fin.last (n + 1))))
      let θ' : Fin (n + 2) → ℝ := Fin.lastCases
        ((1 + ε) * (1 + δ) - 1)
        (fun i => (1 + θ i) * (1 + δ) - 1)
      refine ⟨θ', ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [show θ' (Fin.last (n + 1)) = (1 + ε) * (1 + δ) - 1 by
            simp [θ']]
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (p15_t1_theta_step fp.u_nonneg (n := n + 1) h
              (hε.trans (p15_t1_u_le_gamma fp.u_nonneg (by omega) hprev)) hδ)
        · rw [show θ' j.castSucc = (1 + θ j) * (1 + δ) - 1 by
            simp [θ']]
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (p15_t1_theta_step fp.u_nonneg (n := n + 1) h (hθ j) hδ)
      · rw [p15_t1_roundedDot_succ_last, hadd, hmul, hdot]
        conv_rhs => rw [Fin.sum_univ_castSucc]
        simp only [θ', Fin.lastCases_castSucc, Fin.lastCases_last]
        rw [add_mul, Finset.sum_mul]
        congr 1
        · apply Finset.sum_congr rfl
          intro i hi
          ring
        · ring

private lemma p15_t1_roundedRectMatVec_backward (fp : StandardFPModel)
    {m n : ℕ} (A : P15RectMatrix m n) (x : Fin n → ℝ)
    (h : GammaValid fp.u n) :
    ∃ Δ : P15RectMatrix m n,
      p15RectFrobNorm Δ ≤ gamma fp.u n * p15RectFrobNorm A ∧
      p15RoundedRectMatVec fp A x =
        p15RectMatVec (p15RectAdd A Δ) x := by
  have hex : ∀ i : Fin m, ∃ θ : Fin n → ℝ,
      (∀ j, |θ j| ≤ gamma fp.u n) ∧
      roundedDotProduct fp n (A i) x =
        ∑ j : Fin n, (A i j * (1 + θ j)) * x j :=
    fun i => p15_t1_roundedDot_backward fp n h (A i) x
  choose θ hθ hdot using hex
  let Δ : P15RectMatrix m n := fun i j => A i j * θ i j
  refine ⟨Δ, ?_, ?_⟩
  · have hγ : 0 ≤ gamma fp.u n := p15_t1_gamma_nonneg fp.u_nonneg h
    have hterm : ∀ i : Fin m, ∀ j : Fin n,
        Δ i j ^ 2 ≤ (gamma fp.u n) ^ 2 * A i j ^ 2 := by
      intro i j
      have hsquare : |θ i j| ^ 2 ≤ (gamma fp.u n) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) hγ).2 (hθ i j)
      dsimp [Δ]
      rw [mul_pow]
      calc
        A i j ^ 2 * θ i j ^ 2 = A i j ^ 2 * |θ i j| ^ 2 := by
          rw [sq_abs]
        _ ≤ A i j ^ 2 * gamma fp.u n ^ 2 :=
          mul_le_mul_of_nonneg_left hsquare (sq_nonneg _)
        _ = gamma fp.u n ^ 2 * A i j ^ 2 := by ring
    have hsum : (∑ i : Fin m, ∑ j : Fin n, Δ i j ^ 2) ≤
        (gamma fp.u n) ^ 2 * (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
      calc
        (∑ i : Fin m, ∑ j : Fin n, Δ i j ^ 2) ≤
            ∑ i : Fin m, ∑ j : Fin n,
              (gamma fp.u n) ^ 2 * A i j ^ 2 := by
          exact Finset.sum_le_sum fun i _ =>
            Finset.sum_le_sum fun j _ => hterm i j
        _ = (gamma fp.u n) ^ 2 *
            (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
          simp_rw [Finset.mul_sum]
    have hsA : 0 ≤ ∑ i : Fin m, ∑ j : Fin n, A i j ^ 2 := by positivity
    have hsΔ : 0 ≤ ∑ i : Fin m, ∑ j : Fin n, Δ i j ^ 2 := by positivity
    have hnA : 0 ≤ p15RectFrobNorm A := by
      simp [p15RectFrobNorm]
    have hnΔ : 0 ≤ p15RectFrobNorm Δ := by
      simp [p15RectFrobNorm]
    have hsqA : p15RectFrobNorm A ^ 2 =
        ∑ i : Fin m, ∑ j : Fin n, A i j ^ 2 := by
      exact Real.sq_sqrt hsA
    have hsqΔ : p15RectFrobNorm Δ ^ 2 =
        ∑ i : Fin m, ∑ j : Fin n, Δ i j ^ 2 := by
      exact Real.sq_sqrt hsΔ
    have hsquares : p15RectFrobNorm Δ ^ 2 ≤
        (gamma fp.u n * p15RectFrobNorm A) ^ 2 := by
      rw [hsqΔ, mul_pow, hsqA]
      exact hsum
    exact (sq_le_sq₀ hnΔ (mul_nonneg hγ hnA)).1 hsquares
  · funext i
    change roundedDotProduct fp n (A i) x =
      ∑ j : Fin n, (A i j + Δ i j) * x j
    rw [hdot i]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [Δ]
    ring

private lemma p15_t1_rectMatVec_mul {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p)
    (x : Fin p → ℝ) :
    p15RectMatVec A (p15RectMatVec B x) =
      p15RectMatVec (p15RectMatMul A B) x := by
  funext i
  simp only [p15RectMatVec, p15RectMatMul]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
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
    p15_t1_roundedRectMatVec_backward fp (p15RectTranspose Y) v hb
  obtain ⟨ΔX, hΔX, hz⟩ :=
    p15_t1_roundedRectMatVec_backward fp X
      (p15RoundedRectMatVec fp (p15RectTranspose Y) v) hr
  refine ⟨ΔYT, ΔX, hΔYT, hΔX, hw, hz, ?_⟩
  rw [hz, hw]
  exact p15_t1_rectMatVec_mul _ _ _

end HighamBench
