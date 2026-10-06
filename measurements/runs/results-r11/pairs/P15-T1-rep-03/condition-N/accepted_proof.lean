import HighamBench.P15Definitions

namespace HighamBench

private lemma p15_gamma_nonneg {u : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hvalid : GammaValid u n) : 0 ≤ gamma u n := by
  unfold gamma
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) hu)
    (le_of_lt (sub_pos.mpr hvalid))

private lemma p15_gamma_mono_valid {u : ℝ} {m n : ℕ}
    (hu : 0 ≤ u) (hmn : m ≤ n) (hvalid : GammaValid u n) :
    GammaValid u m := by
  unfold GammaValid at *
  have hcast : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hmul : (m : ℝ) * u ≤ (n : ℝ) * u :=
    mul_le_mul_of_nonneg_right hcast hu
  exact lt_of_le_of_lt hmul hvalid

private lemma p15_u_le_gamma {u : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hn : 1 ≤ n) (hvalid : GammaValid u n) :
    u ≤ gamma u n := by
  have hden : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hvalid
  rw [gamma, le_div_iff₀ hden]
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h₁ : 0 ≤ ((n : ℝ) - 1) * u :=
    mul_nonneg (sub_nonneg.mpr hn') hu
  have h₂ : 0 ≤ ((n : ℝ) * u) * u :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hu) hu
  nlinarith

private lemma p15_gamma_step {u : ℝ} {k : ℕ}
    (hu : 0 ≤ u) (hvalid : GammaValid u (k + 1)) :
    gamma u k * (1 + u) + u ≤ gamma u (k + 1) := by
  have hkvalid : GammaValid u k :=
    p15_gamma_mono_valid hu (Nat.le_succ k) hvalid
  have hkden : 0 < 1 - (k : ℝ) * u := sub_pos.mpr hkvalid
  have hsden : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := sub_pos.mpr hvalid
  have heq :
      gamma u k * (1 + u) + u =
        (((k + 1 : ℕ) : ℝ) * u) / (1 - (k : ℝ) * u) := by
    rw [gamma]
    field_simp
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  rw [heq, gamma]
  apply div_le_div_of_nonneg_left
  · exact mul_nonneg (Nat.cast_nonneg (k + 1)) hu
  · exact hsden
  · norm_num
    nlinarith

private lemma p15_rounded_accum_step
    (fp : StandardFPModel) {k : ℕ} {q s S t rt : ℝ}
    (hk : 1 ≤ k) (hvalid : GammaValid fp.u (k + 1))
    (hqs : |q - s| ≤ gamma fp.u k * S) (hs : |s| ≤ S)
    (hS : 0 ≤ S)
    (hrt : ∃ δ : ℝ, |δ| ≤ fp.u ∧ rt = t * (1 + δ)) :
    |fp.fl_add q rt - (s + t)| ≤
      gamma fp.u (k + 1) * (S + |t|) := by
  rcases hrt with ⟨δm, hδm, rfl⟩
  rcases fp.model_add q (t * (1 + δm)) with ⟨δa, hδa, hadd⟩
  rw [hadd]
  have hu := fp.u_nonneg
  have hkvalid : GammaValid fp.u k :=
    p15_gamma_mono_valid hu (Nat.le_succ k) hvalid
  have hgk : 0 ≤ gamma fp.u k := p15_gamma_nonneg hu hkvalid
  have hug : fp.u ≤ gamma fp.u k := p15_u_le_gamma hu hk hkvalid
  have hstep := p15_gamma_step hu hvalid
  have h₁a : |1 + δa| ≤ 1 + fp.u := by
    calc
      |1 + δa| ≤ |(1 : ℝ)| + |δa| := abs_add_le _ _
      _ ≤ 1 + fp.u := by simpa using add_le_add_left hδa 1
  have h₁m : |1 + δm| ≤ 1 + fp.u := by
    calc
      |1 + δm| ≤ |(1 : ℝ)| + |δm| := abs_add_le _ _
      _ ≤ 1 + fp.u := by simpa using add_le_add_left hδm 1
  have hsp : |s + t| ≤ S + |t| := by
    nlinarith [abs_add_le s t]
  have hid :
      (q + t * (1 + δm)) * (1 + δa) - (s + t) =
        (q - s) * (1 + δa) + (s + t) * δa +
          (t * δm) * (1 + δa) := by
    ring
  rw [hid]
  calc
    |(q - s) * (1 + δa) + (s + t) * δa +
        (t * δm) * (1 + δa)|
        ≤ |(q - s) * (1 + δa)| + |(s + t) * δa| +
            |(t * δm) * (1 + δa)| := abs_add_three _ _ _
    _ = |q - s| * |1 + δa| + |s + t| * |δa| +
          (|t| * |δm|) * |1 + δa| := by simp only [abs_mul]
    _ ≤ (gamma fp.u k * S) * (1 + fp.u) +
          (S + |t|) * fp.u + (|t| * fp.u) * (1 + fp.u) := by
      gcongr
    _ ≤ gamma fp.u (k + 1) * (S + |t|) := by
      have hnon : 0 ≤ 1 + fp.u := by positivity
      have hcoef : fp.u + fp.u * (1 + fp.u) ≤
          gamma fp.u k * (1 + fp.u) + fp.u := by
        nlinarith [mul_le_mul_of_nonneg_right hug hnon]
      have ht : 0 ≤ |t| := abs_nonneg t
      nlinarith [mul_nonneg hS
        (sub_nonneg.mpr hstep),
        mul_nonneg ht (sub_nonneg.mpr (hcoef.trans hstep))]

private lemma p15_rounded_fold_bound
    (fp : StandardFPModel) (n : ℕ) :
    ∀ (k : ℕ) (q s S : ℝ) (t rt : Fin n → ℝ),
      1 ≤ k → GammaValid fp.u (k + n) →
      |q - s| ≤ gamma fp.u k * S → |s| ≤ S → 0 ≤ S →
      (∀ i, ∃ δ : ℝ, |δ| ≤ fp.u ∧ rt i = t i * (1 + δ)) →
      |Fin.foldl n (fun acc i ↦ fp.fl_add acc (rt i)) q -
          (s + ∑ i, t i)| ≤
        gamma fp.u (k + n) * (S + ∑ i, |t i|) := by
  intro k q s S t rt hk hvalid hqs hs hS hrt
  induction n generalizing k q s S with
  | zero =>
      simpa using hqs
  | succ n ih =>
      rw [Fin.foldl_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
      have hsmall : GammaValid fp.u (k + 1) := by
        apply p15_gamma_mono_valid fp.u_nonneg (n := k + (n + 1))
        · omega
        · simpa [Nat.add_assoc] using hvalid
      have hnext := p15_rounded_accum_step fp hk hsmall hqs hs hS (hrt 0)
      have hsnext : |s + t 0| ≤ S + |t 0| := by
        nlinarith [abs_add_le s (t 0)]
      have hrec := ih (k + 1) (fp.fl_add q (rt 0)) (s + t 0)
        (S + |t 0|) (fun i ↦ t i.succ) (fun i ↦ rt i.succ)
        (by omega) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hvalid)
        hnext hsnext (add_nonneg hS (abs_nonneg _)) (fun i ↦ hrt i.succ)
      simpa [add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec

private lemma p15_rounded_dot_forward_bound
    (fp : StandardFPModel) {n : ℕ} (a x : Fin n → ℝ)
    (hvalid : GammaValid fp.u n) :
    |roundedDotProduct fp n a x - ∑ i, a i * x i| ≤
      gamma fp.u n * ∑ i, |a i * x i| := by
  cases n with
  | zero => simp [roundedDotProduct]
  | succ n =>
      let t0 : ℝ := a 0 * x 0
      rcases fp.model_mul (a 0) (x 0) with ⟨δ0, hδ0, hmul0⟩
      have hvalid1 : GammaValid fp.u 1 :=
        p15_gamma_mono_valid fp.u_nonneg (Nat.succ_le_succ (Nat.zero_le n)) hvalid
      have hinit : |fp.fl_mul (a 0) (x 0) - t0| ≤
          gamma fp.u 1 * |t0| := by
        rw [hmul0]
        have hid : t0 * (1 + δ0) - t0 = t0 * δ0 := by ring
        rw [hid, abs_mul]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left
          (hδ0.trans (p15_u_le_gamma fp.u_nonneg (by omega) hvalid1))
          (abs_nonneg t0)
      have hfold := p15_rounded_fold_bound fp n 1
        (fp.fl_mul (a 0) (x 0)) t0 |t0|
        (fun i ↦ a i.succ * x i.succ)
        (fun i ↦ fp.fl_mul (a i.succ) (x i.succ))
        (by omega) (by simpa [Nat.add_comm] using hvalid) hinit (le_refl _)
        (abs_nonneg _) (fun i ↦ fp.model_mul (a i.succ) (x i.succ))
      simpa [roundedDotProduct, t0, Fin.sum_univ_succ, add_assoc,
        Nat.add_comm] using hfold

private lemma p15_rounded_dot_backward_entries
    (fp : StandardFPModel) {n : ℕ} (a x : Fin n → ℝ)
    (hvalid : GammaValid fp.u n) :
    ∃ d : Fin n → ℝ,
      (∀ j, |d j| ≤ gamma fp.u n * |a j|) ∧
      roundedDotProduct fp n a x = ∑ j, (a j + d j) * x j := by
  classical
  let e : ℝ := roundedDotProduct fp n a x - ∑ j, a j * x j
  let S : ℝ := ∑ j, |a j * x j|
  let θ : Fin n → ℝ := fun j ↦
    if S = 0 then 0
    else if 0 ≤ a j * x j then e / S else -(e / S)
  let d : Fin n → ℝ := fun j ↦ a j * θ j
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  have he : |e| ≤ gamma fp.u n * S := by
    simpa [e, S] using p15_rounded_dot_forward_bound fp a x hvalid
  have hg : 0 ≤ gamma fp.u n := p15_gamma_nonneg fp.u_nonneg hvalid
  have hθ : ∀ j, |θ j| ≤ gamma fp.u n := by
    intro j
    by_cases hSz : S = 0
    · simp [θ, hSz, hg]
    · have hSp : 0 < S := lt_of_le_of_ne hS (Ne.symm hSz)
      have hdiv : |e / S| ≤ gamma fp.u n := by
        rw [abs_div, abs_of_pos hSp]
        exact (div_le_iff₀ hSp).2 he
      simp only [θ, hSz, if_false]
      split_ifs <;> simpa using hdiv
  refine ⟨d, ?_, ?_⟩
  · intro j
    simpa [d, abs_mul, mul_comm] using
      mul_le_mul_of_nonneg_left (hθ j) (abs_nonneg (a j))
  · have hsum : ∑ j, d j * x j = e := by
      by_cases hSz : S = 0
      · have hez : e = 0 := by
          have : |e| ≤ 0 := by simpa [hSz] using he
          exact abs_eq_zero.mp (le_antisymm this (abs_nonneg e))
        simp [d, θ, hSz, hez]
      · have hterm : ∀ j, d j * x j = (e / S) * |a j * x j| := by
          intro j
          simp only [d, θ, hSz, if_false]
          split_ifs with hj
          · rw [abs_of_nonneg hj]
            ring
          · rw [abs_of_neg (lt_of_not_ge hj)]
            ring
        calc
          ∑ j, d j * x j = ∑ j, (e / S) * |a j * x j| :=
            Finset.sum_congr rfl (fun j _ ↦ hterm j)
          _ = (e / S) * S := by simp [S, Finset.mul_sum]
          _ = e := div_mul_cancel₀ e hSz
    calc
      roundedDotProduct fp n a x = (∑ j, a j * x j) + e := by simp [e]
      _ = ∑ j, (a j + d j) * x j := by
        rw [show (∑ j, (a j + d j) * x j) =
            (∑ j, a j * x j) + ∑ j, d j * x j by
          simp only [add_mul, Finset.sum_add_distrib]]
        rw [hsum]

private lemma p15_rect_frob_bound_of_entries {m n : ℕ}
    (D A : P15RectMatrix m n) {g : ℝ} (hg : 0 ≤ g)
    (hentry : ∀ i j, |D i j| ≤ g * |A i j|) :
    p15RectFrobNorm D ≤ g * p15RectFrobNorm A := by
  have hA : 0 ≤ ∑ i : Fin m, ∑ j : Fin n, A i j ^ 2 :=
    Finset.sum_nonneg (fun _ _ ↦
      Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
  have hsum :
      (∑ i : Fin m, ∑ j : Fin n, D i j ^ 2) ≤
        g ^ 2 * (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
    calc
      (∑ i : Fin m, ∑ j : Fin n, D i j ^ 2)
          ≤ ∑ i : Fin m, ∑ j : Fin n, (g * |A i j|) ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            apply Finset.sum_le_sum
            intro j _
            simpa [sq_abs] using
              ((sq_le_sq₀ (abs_nonneg (D i j))
                (mul_nonneg hg (abs_nonneg (A i j)))).2 (hentry i j))
      _ = g ^ 2 * (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
        simp [mul_pow, sq_abs, Finset.mul_sum]
  unfold p15RectFrobNorm
  apply (Real.sqrt_le_iff).2
  refine ⟨mul_nonneg hg (Real.sqrt_nonneg _), ?_⟩
  calc
    (∑ i : Fin m, ∑ j : Fin n, D i j ^ 2)
        ≤ g ^ 2 * (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := hsum
    _ = (g * Real.sqrt (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hA]

private lemma p15_rounded_rect_matvec_backward
    (fp : StandardFPModel) {m n : ℕ}
    (A : P15RectMatrix m n) (x : Fin n → ℝ)
    (hvalid : GammaValid fp.u n) :
    ∃ D : P15RectMatrix m n,
      p15RectFrobNorm D ≤ gamma fp.u n * p15RectFrobNorm A ∧
      p15RoundedRectMatVec fp A x =
        p15RectMatVec (p15RectAdd A D) x := by
  classical
  choose d hd hrep using fun i ↦
    p15_rounded_dot_backward_entries fp (A i) x hvalid
  let D : P15RectMatrix m n := fun i j ↦ d i j
  refine ⟨D, p15_rect_frob_bound_of_entries D A
    (p15_gamma_nonneg fp.u_nonneg hvalid) (fun i j ↦ hd i j), ?_⟩
  funext i
  simpa [p15RoundedRectMatVec, roundedMatVec, p15RectMatVec,
    p15RectAdd, D] using hrep i

private lemma p15_rect_matvec_mul_assoc {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p)
    (x : Fin p → ℝ) :
    p15RectMatVec A (p15RectMatVec B x) =
      p15RectMatVec (p15RectMatMul A B) x := by
  funext i
  simp only [p15RectMatVec, p15RectMatMul, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
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
  rcases p15_rounded_rect_matvec_backward fp (p15RectTranspose Y) v hb with
    ⟨ΔYT, hΔYT, hw⟩
  rcases p15_rounded_rect_matvec_backward fp X
      (p15RoundedRectMatVec fp (p15RectTranspose Y) v) hr with
    ⟨ΔX, hΔX, hz⟩
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
      p15_rect_matvec_mul_assoc _ _ _

end HighamBench
