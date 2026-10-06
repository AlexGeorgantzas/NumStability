import HighamBench.P15Definitions

namespace HighamBench

private lemma p15_gammaValid_mono {u : ℝ} {m n : ℕ}
    (hu : 0 ≤ u) (hmn : m ≤ n) (hn : GammaValid u n) :
    GammaValid u m := by
  unfold GammaValid at *
  have hc : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  nlinarith

private lemma p15_gamma_nonneg {u : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hn : GammaValid u n) : 0 ≤ gamma u n := by
  unfold GammaValid at hn
  rw [gamma]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (le_of_lt (sub_pos.mpr hn))

private lemma p15_gamma_mono {u : ℝ} {m n : ℕ}
    (hu : 0 ≤ u) (hmn : m ≤ n) (hn : GammaValid u n) :
    gamma u m ≤ gamma u n := by
  have hc : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hmul : (m : ℝ) * u ≤ (n : ℝ) * u :=
    mul_le_mul_of_nonneg_right hc hu
  have hden : 0 < 1 - (n : ℝ) * u := by
    exact sub_pos.mpr hn
  rw [gamma, gamma]
  exact div_le_div₀ (mul_nonneg (Nat.cast_nonneg _) hu) hmul hden (by linarith)

private lemma p15_gamma_update {u : ℝ} {k : ℕ} {a d : ℝ}
    (hu : 0 ≤ u) (hv : GammaValid u (k + 1))
    (ha : |a| ≤ gamma u k) (hd : |d| ≤ u) :
    |a + d + a * d| ≤ gamma u (k + 1) := by
  have hvk : GammaValid u k :=
    p15_gammaValid_mono hu (Nat.le_succ k) hv
  have hgk : 0 ≤ gamma u k := p15_gamma_nonneg hu hvk
  have htri : |a + d + a * d| ≤ |a| + |d| + |a| * |d| := by
    calc
      |a + d + a * d| ≤ |a + d| + |a * d| := abs_add_le _ _
      _ ≤ |a| + |d| + |a| * |d| := by
        rw [abs_mul]
        linarith [abs_add_le a d]
  have hest : |a| + |d| + |a| * |d| ≤
      gamma u k + u + gamma u k * u := by
    have hm : |a| * |d| ≤ gamma u k * u :=
      mul_le_mul ha hd (abs_nonneg _) hgk
    linarith
  have hkden : 0 < 1 - (k : ℝ) * u := by
    exact sub_pos.mpr hvk
  have hnextden : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := by
    exact sub_pos.mpr hv
  have hnum : 0 ≤ ((k : ℝ) + 1) * u :=
    mul_nonneg (by positivity) hu
  have halg : gamma u k + u + gamma u k * u =
      (((k : ℝ) + 1) * u) / (1 - (k : ℝ) * u) := by
    rw [gamma]
    field_simp
    ring
  have hfrac : (((k : ℝ) + 1) * u) / (1 - (k : ℝ) * u) ≤
      (((k : ℝ) + 1) * u) / (1 - ((k : ℝ) + 1) * u) := by
    apply div_le_div_of_nonneg_left hnum
    · convert hnextden using 1 <;> norm_num
    · nlinarith
  calc
    |a + d + a * d| ≤ gamma u k + u + gamma u k * u := htri.trans hest
    _ = (((k : ℝ) + 1) * u) / (1 - (k : ℝ) * u) := halg
    _ ≤ (((k : ℝ) + 1) * u) / (1 - ((k : ℝ) + 1) * u) := hfrac
    _ = gamma u (k + 1) := by rw [gamma]; norm_num

private lemma p15_rounded_sum_backward (fp : StandardFPModel) {n : ℕ}
    (a q mu : Fin (n + 1) → ℝ)
    (hq : ∀ i, q i = a i * (1 + mu i))
    (hmu : ∀ i, |mu i| ≤ fp.u)
    (hv : GammaValid fp.u (n + 1)) :
    ∃ theta : Fin (n + 1) → ℝ,
      Fin.foldl n (fun s i ↦ fp.fl_add s (q i.succ)) (q 0) =
        ∑ i, a i * (1 + theta i) ∧
      ∀ i, |theta i| ≤ gamma fp.u (n + 1) := by
  induction n with
  | zero =>
      refine ⟨mu, ?_, ?_⟩
      · simp [hq]
      · intro i
        have h := p15_gamma_update fp.u_nonneg hv
          (a := 0) (d := mu i) (by simp [gamma]) (hmu i)
        simpa using h
  | succ n ih =>
      have hv' : GammaValid fp.u (n + 1) :=
        p15_gammaValid_mono fp.u_nonneg (by omega) hv
      obtain ⟨theta, hfold, htheta⟩ := ih
        (a := fun i ↦ a i.castSucc)
        (q := fun i ↦ q i.castSucc)
        (mu := fun i ↦ mu i.castSucc)
        (fun i ↦ hq i.castSucc) (fun i ↦ hmu i.castSucc) hv'
      let s := Fin.foldl n
        (fun s i ↦ fp.fl_add s (q i.succ.castSucc)) (q (Fin.castSucc 0))
      obtain ⟨d, hd, hadd⟩ := fp.model_add s (q (Fin.last (n + 1)))
      let theta' : Fin (n + 2) → ℝ :=
        Fin.lastCases (mu (Fin.last (n + 1)) + d + mu (Fin.last (n + 1)) * d)
          (fun i ↦ theta i + d + theta i * d)
      refine ⟨theta', ?_, ?_⟩
      · rw [Fin.foldl_succ_last]
        simp only [Fin.succ_castSucc, Fin.castSucc_zero, Fin.succ_last]
        change fp.fl_add s (q (Fin.last (n + 1))) = _
        rw [hadd]
        change (s + q (Fin.last (n + 1))) * (1 + d) = _
        have hs : s = ∑ i, a i.castSucc * (1 + theta i) := hfold
        rw [hs, hq]
        conv_rhs => rw [Fin.sum_univ_castSucc]
        rw [add_mul, Finset.sum_mul]
        apply congrArg₂ (fun x y : ℝ ↦ x + y)
        · apply Finset.sum_congr rfl
          intro i hi
          simp [theta']
          ring
        · simp [theta']
          ring
      · intro i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simp only [theta', Fin.lastCases_last]
          have hv1 : GammaValid fp.u 1 :=
            p15_gammaValid_mono fp.u_nonneg (by omega) hv
          have hv2 : GammaValid fp.u 2 :=
            p15_gammaValid_mono fp.u_nonneg (by omega) hv
          have hmu1 := p15_gamma_update fp.u_nonneg hv1
            (a := 0) (d := mu (Fin.last (n + 1)))
            (by simp [gamma]) (hmu _)
          have hmu1' : |mu (Fin.last (n + 1))| ≤ gamma fp.u 1 := by
            simpa using hmu1
          have htwo := p15_gamma_update fp.u_nonneg hv2 hmu1' hd
          exact htwo.trans (p15_gamma_mono fp.u_nonneg (by omega) hv)
        · simp only [theta', Fin.lastCases_castSucc]
          exact p15_gamma_update fp.u_nonneg hv (htheta j) hd

private lemma p15_roundedDotProduct_backward (fp : StandardFPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hv : GammaValid fp.u n) :
    ∃ e : Fin n → ℝ,
      (∀ i, |e i| ≤ gamma fp.u n * |x i|) ∧
      roundedDotProduct fp n x y = ∑ i, (x i + e i) * y i := by
  cases n with
  | zero =>
      refine ⟨fun i ↦ Fin.elim0 i, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · simp [roundedDotProduct]
  | succ n =>
      let mu : Fin (n + 1) → ℝ := fun i ↦
        Classical.choose (fp.model_mul (x i) (y i))
      have hmu : ∀ i, |mu i| ≤ fp.u := fun i ↦
        (Classical.choose_spec (fp.model_mul (x i) (y i))).1
      have hmul : ∀ i, fp.fl_mul (x i) (y i) =
          (x i * y i) * (1 + mu i) := fun i ↦
        (Classical.choose_spec (fp.model_mul (x i) (y i))).2
      obtain ⟨theta, hsum, htheta⟩ := p15_rounded_sum_backward fp
        (a := fun i ↦ x i * y i)
        (q := fun i ↦ fp.fl_mul (x i) (y i))
        (mu := mu) hmul hmu hv
      refine ⟨fun i ↦ x i * theta i, ?_, ?_⟩
      · intro i
        rw [abs_mul, mul_comm (gamma fp.u (n + 1))]
        exact mul_le_mul_of_nonneg_left (htheta i) (abs_nonneg _)
      · rw [roundedDotProduct, hsum]
        apply Finset.sum_congr rfl
        intro i hi
        ring

private lemma p15_roundedRectMatVec_backward (fp : StandardFPModel)
    {m n : ℕ} (A : P15RectMatrix m n) (x : Fin n → ℝ)
    (hv : GammaValid fp.u n) :
    ∃ E : P15RectMatrix m n,
      p15RectFrobNorm E ≤ gamma fp.u n * p15RectFrobNorm A ∧
      p15RoundedRectMatVec fp A x = p15RectMatVec (p15RectAdd A E) x := by
  have hrow : ∀ i : Fin m, ∃ e : Fin n → ℝ,
      (∀ j, |e j| ≤ gamma fp.u n * |A i j|) ∧
      roundedDotProduct fp n (A i) x = ∑ j, (A i j + e j) * x j :=
    fun i ↦ p15_roundedDotProduct_backward fp n (A i) x hv
  choose e he hdot using hrow
  let E : P15RectMatrix m n := fun i j ↦ e i j
  refine ⟨E, ?_, ?_⟩
  · have hg : 0 ≤ gamma fp.u n := p15_gamma_nonneg fp.u_nonneg hv
    have hpoint : ∀ i j, E i j ^ 2 ≤
        (gamma fp.u n) ^ 2 * (A i j) ^ 2 := by
      intro i j
      have habs := he i j
      have hs : |E i j| ^ 2 ≤ (gamma fp.u n * |A i j|) ^ 2 := by
        exact pow_le_pow_left₀ (abs_nonneg _) habs 2
      simpa [sq_abs, mul_pow] using hs
    have hsum : (∑ i : Fin m, ∑ j : Fin n, E i j ^ 2) ≤
        (gamma fp.u n) ^ 2 * (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
      calc
        (∑ i : Fin m, ∑ j : Fin n, E i j ^ 2) ≤
            ∑ i : Fin m, ∑ j : Fin n,
              (gamma fp.u n) ^ 2 * A i j ^ 2 := by
                exact Finset.sum_le_sum fun i _ ↦
                  Finset.sum_le_sum fun j _ ↦ hpoint i j
        _ = (gamma fp.u n) ^ 2 *
            (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
              simp_rw [Finset.mul_sum]
    have hE_nonneg : 0 ≤ ∑ i : Fin m, ∑ j : Fin n, E i j ^ 2 := by positivity
    have hA_nonneg : 0 ≤ ∑ i : Fin m, ∑ j : Fin n, A i j ^ 2 := by positivity
    rw [p15RectFrobNorm, p15RectFrobNorm]
    calc
      Real.sqrt (∑ i : Fin m, ∑ j : Fin n, E i j ^ 2) ≤
          Real.sqrt ((gamma fp.u n) ^ 2 *
            (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2)) :=
        Real.sqrt_le_sqrt hsum
      _ = Real.sqrt ((gamma fp.u n) ^ 2) *
          Real.sqrt (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg (gamma fp.u n))]
      _ = gamma fp.u n *
          Real.sqrt (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hg]
  · funext i
    exact hdot i

private lemma p15_rectMatVec_mul {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p) (x : Fin p → ℝ) :
    p15RectMatVec (p15RectMatMul A B) x =
      p15RectMatVec A (p15RectMatVec B x) := by
  funext i
  simp only [p15RectMatVec, p15RectMatMul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
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
  dsimp
  obtain ⟨ΔYT, hΔYT, hw⟩ :=
    p15_roundedRectMatVec_backward fp (p15RectTranspose Y) v hb
  obtain ⟨ΔX, hΔX, hz⟩ :=
    p15_roundedRectMatVec_backward fp X
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
      (p15_rectMatVec_mul _ _ _).symm

end HighamBench
