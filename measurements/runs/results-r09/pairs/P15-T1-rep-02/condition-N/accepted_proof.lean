import HighamBench.P15Definitions
import Batteries.Data.Fin.Fold

namespace HighamBench

private lemma p15_gamma_nonneg {u : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hvalid : GammaValid u n) :
    0 ≤ gamma u n := by
  unfold gamma GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) hu)
    (le_of_lt (sub_pos.mpr hvalid))

private lemma p15_gamma_ge_u {u : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hn : 1 ≤ n) (hvalid : GammaValid u n) :
    u ≤ gamma u n := by
  unfold gamma GammaValid at *
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hvalid
  apply (le_div_iff₀ hden).2
  have hnu : u ≤ (n : ℝ) * u := by nlinarith
  have hnonneg : 0 ≤ (n : ℝ) * u * u :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hu) hu
  nlinarith

private lemma p15_gamma_step_old {u : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hvalid : GammaValid u (n + 1)) :
    u + (1 + u) * gamma u n ≤ gamma u (n + 1) := by
  have hnu : (n : ℝ) * u ≤ ((n + 1 : ℕ) : ℝ) * u := by
    gcongr
    exact_mod_cast Nat.le_succ n
  have hdenN : 0 < 1 - (n : ℝ) * u := by
    unfold GammaValid at hvalid
    nlinarith
  have hdenN' : 1 - u * (n : ℝ) ≠ 0 := by nlinarith
  have hdenS : 0 < 1 - ((n + 1 : ℕ) : ℝ) * u := by
    exact sub_pos.mpr hvalid
  have hrewrite :
      u + (1 + u) * gamma u n =
        (((n + 1 : ℕ) : ℝ) * u) / (1 - (n : ℝ) * u) := by
    unfold gamma
    apply (eq_div_iff (ne_of_gt hdenN)).2
    field_simp [ne_of_gt hdenN, hdenN']
    push_cast
    ring
  rw [hrewrite, gamma]
  apply (div_le_div_iff₀ hdenN hdenS).2
  have hnum : 0 ≤ ((n + 1 : ℕ) : ℝ) * u :=
    mul_nonneg (Nat.cast_nonneg _) hu
  nlinarith

private lemma p15_gamma_step_new {u : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hn : 1 ≤ n) (hvalid : GammaValid u (n + 1)) :
    2 * u + u ^ 2 ≤ gamma u (n + 1) := by
  have hvalidN : GammaValid u n := by
    unfold GammaValid at *
    have hnu : (n : ℝ) * u ≤ ((n + 1 : ℕ) : ℝ) * u := by
      gcongr
      exact_mod_cast Nat.le_succ n
    linarith
  have hgu : u ≤ gamma u n := p15_gamma_ge_u hu hn hvalidN
  have hfactor : 0 ≤ (1 + u) * (gamma u n - u) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr hgu)
  calc
    2 * u + u ^ 2 ≤ u + (1 + u) * gamma u n := by nlinarith
    _ ≤ gamma u (n + 1) := p15_gamma_step_old hu hvalid

private lemma p15_rounded_dot_step
    (fp : StandardFPModel) {k : ℕ} (hk : 1 ≤ k)
    (hvalid : GammaValid fp.u (k + 1))
    (a x acc S T : ℝ) (hT : 0 ≤ T) (hS : |S| ≤ T)
    (herr : |acc - S| ≤ gamma fp.u k * T) :
    |fp.fl_add acc (fp.fl_mul a x) - (S + a * x)| ≤
      gamma fp.u (k + 1) * (T + |a * x|) := by
  obtain ⟨dm, hdm, hmul⟩ := fp.model_mul a x
  obtain ⟨da, hda, hadd⟩ := fp.model_add acc (fp.fl_mul a x)
  have hvalidK : GammaValid fp.u k := by
    unfold GammaValid at *
    have hku : (k : ℝ) * fp.u ≤ ((k + 1 : ℕ) : ℝ) * fp.u := by
      apply mul_le_mul_of_nonneg_right
      · norm_num
      · exact fp.u_nonneg
    linarith
  have hgamma : 0 ≤ gamma fp.u k :=
    p15_gamma_nonneg fp.u_nonneg hvalidK
  have hone : |1 + da| ≤ 1 + fp.u := by
    calc
      |1 + da| ≤ |(1 : ℝ)| + |da| := abs_add_le _ _
      _ ≤ 1 + fp.u := by simpa using add_le_add_left hda 1
  have htwo : |dm + da + dm * da| ≤ 2 * fp.u + fp.u ^ 2 := by
    calc
      |dm + da + dm * da| ≤ |dm + da| + |dm * da| := abs_add_le _ _
      _ ≤ (|dm| + |da|) + |dm| * |da| := by
        rw [abs_mul]
        exact add_le_add (abs_add_le dm da) (le_refl _)
      _ ≤ (fp.u + fp.u) + fp.u * fp.u := by
        exact add_le_add
          (add_le_add hdm hda)
          (mul_le_mul hdm hda (abs_nonneg _) fp.u_nonneg)
      _ = 2 * fp.u + fp.u ^ 2 := by ring
  have hid :
      (acc + (a * x) * (1 + dm)) * (1 + da) - (S + a * x) =
        (acc - S) * (1 + da) + S * da +
          (a * x) * (dm + da + dm * da) := by ring
  rw [hadd, hmul, hid]
  have hraw :
      |(acc - S) * (1 + da) + S * da +
          (a * x) * (dm + da + dm * da)| ≤
        (gamma fp.u k * T) * (1 + fp.u) + T * fp.u +
          |a * x| * (2 * fp.u + fp.u ^ 2) := by
    calc
      |(acc - S) * (1 + da) + S * da +
          (a * x) * (dm + da + dm * da)| ≤
          |(acc - S) * (1 + da) + S * da| +
            |(a * x) * (dm + da + dm * da)| := abs_add_le _ _
      _ ≤ (|(acc - S) * (1 + da)| + |S * da|) +
            |(a * x) * (dm + da + dm * da)| := by
          exact add_le_add (abs_add_le _ _) (le_refl _)
      _ = (|acc - S| * |1 + da| + |S| * |da|) +
            |a * x| * |dm + da + dm * da| := by
          simp only [abs_mul]
      _ ≤ ((gamma fp.u k * T) * (1 + fp.u) + T * fp.u) +
            |a * x| * (2 * fp.u + fp.u ^ 2) := by
          apply add_le_add
          · apply add_le_add
            · exact (mul_le_mul_of_nonneg_right herr (abs_nonneg _)).trans
                (mul_le_mul_of_nonneg_left hone (mul_nonneg hgamma hT))
            · exact (mul_le_mul_of_nonneg_right hS (abs_nonneg _)).trans
                (mul_le_mul_of_nonneg_left hda hT)
          · exact mul_le_mul_of_nonneg_left htwo (abs_nonneg _)
      _ = (gamma fp.u k * T) * (1 + fp.u) + T * fp.u +
            |a * x| * (2 * fp.u + fp.u ^ 2) := by ring
  calc
    |(acc - S) * (1 + da) + S * da +
        (a * x) * (dm + da + dm * da)| ≤ _ := hraw
    _ = (fp.u + (1 + fp.u) * gamma fp.u k) * T +
          (2 * fp.u + fp.u ^ 2) * |a * x| := by ring
    _ ≤ gamma fp.u (k + 1) * T +
          gamma fp.u (k + 1) * |a * x| := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right
            (p15_gamma_step_old fp.u_nonneg hvalid) hT)
          (mul_le_mul_of_nonneg_right
            (p15_gamma_step_new fp.u_nonneg hk hvalid) (abs_nonneg _))
    _ = gamma fp.u (k + 1) * (T + |a * x|) := by ring

private lemma p15_gamma_valid_mono {u : ℝ} {m n : ℕ}
    (hu : 0 ≤ u) (hmn : m ≤ n) (hvalid : GammaValid u n) :
    GammaValid u m := by
  unfold GammaValid at *
  have hcast : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hmul : (m : ℝ) * u ≤ (n : ℝ) * u :=
    mul_le_mul_of_nonneg_right hcast hu
  linarith

private lemma p15_rounded_dot_fold
    {ι : Type} (fp : StandardFPModel) (a x : ι → ℝ)
    (l : List ι) (k : ℕ) (hk : 1 ≤ k)
    (hvalid : GammaValid fp.u (k + l.length))
    (acc S T : ℝ) (hT : 0 ≤ T) (hS : |S| ≤ T)
    (herr : |acc - S| ≤ gamma fp.u k * T) :
    |l.foldl (fun q i => fp.fl_add q (fp.fl_mul (a i) (x i))) acc -
        (S + (l.map (fun i => a i * x i)).sum)| ≤
      gamma fp.u (k + l.length) *
        (T + (l.map (fun i => |a i * x i|)).sum) := by
  induction l generalizing k acc S T with
  | nil => simpa using herr
  | cons i l ih =>
      have hstepValid : GammaValid fp.u (k + 1) := by
        apply p15_gamma_valid_mono fp.u_nonneg (n := k + (i :: l).length)
          (m := k + 1) ?_ hvalid
        simp only [List.length_cons]
        omega
      have hnextValid : GammaValid fp.u ((k + 1) + l.length) := by
        convert hvalid using 1 <;> simp only [List.length_cons] <;> omega
      have hnextT : 0 ≤ T + |a i * x i| :=
        add_nonneg hT (abs_nonneg _)
      have hnextS : |S + a i * x i| ≤ T + |a i * x i| :=
        (abs_add_le _ _).trans (add_le_add hS (le_refl _))
      have hnextErr := p15_rounded_dot_step fp hk hstepValid
        (a i) (x i) acc S T hT hS herr
      have hresult := ih (k + 1) (by omega) hnextValid
        (fp.fl_add acc (fp.fl_mul (a i) (x i)))
        (S + a i * x i) (T + |a i * x i|)
        hnextT hnextS hnextErr
      simpa [List.foldl, add_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hresult

private lemma p15_rounded_dot_forward_error
    (fp : StandardFPModel) {n : ℕ} (a x : Fin n → ℝ)
    (hvalid : GammaValid fp.u n) :
    |roundedDotProduct fp n a x - ∑ i : Fin n, a i * x i| ≤
      gamma fp.u n * ∑ i : Fin n, |a i * x i| := by
  cases n with
  | zero => simp [roundedDotProduct]
  | succ n =>
      let p : ℝ := a 0 * x 0
      obtain ⟨d, hd, hmul⟩ := fp.model_mul (a 0) (x 0)
      have hvalidOne : GammaValid fp.u 1 := by
        apply p15_gamma_valid_mono fp.u_nonneg (n := n + 1) (m := 1) ?_ hvalid
        omega
      have hinit :
          |fp.fl_mul (a 0) (x 0) - p| ≤ gamma fp.u 1 * |p| := by
        rw [hmul]
        have heq : a 0 * x 0 * (1 + d) - p = p * d := by
          dsimp [p]
          ring
        rw [heq, abs_mul]
        calc
          |p| * |d| ≤ |p| * gamma fp.u 1 :=
            mul_le_mul_of_nonneg_left
              (hd.trans (p15_gamma_ge_u fp.u_nonneg (by omega) hvalidOne))
              (abs_nonneg _)
          _ = gamma fp.u 1 * |p| := by ring
      have hfold := p15_rounded_dot_fold fp
        (fun i : Fin n => a i.succ) (fun i : Fin n => x i.succ)
        (List.finRange n) 1 (by omega)
        (by simpa [Nat.add_comm] using hvalid)
        (fp.fl_mul (a 0) (x 0)) p |p|
        (abs_nonneg _) (le_refl _) hinit
      rw [← Fin.sum_univ_def, ← Fin.sum_univ_def] at hfold
      rw [roundedDotProduct, Fin.foldl_eq_foldl_finRange]
      simpa [p, Fin.sum_univ_succ, add_assoc, Nat.add_comm] using hfold

private noncomputable def p15UnitSign (x : ℝ) : ℝ :=
  if 0 ≤ x then 1 else -1

private lemma p15_unitSign_mul (x : ℝ) : p15UnitSign x * x = |x| := by
  by_cases hx : 0 ≤ x
  · simp [p15UnitSign, hx, abs_of_nonneg hx]
  · have hx' : x < 0 := lt_of_not_ge hx
    simp [p15UnitSign, hx, abs_of_neg hx']

private lemma p15_abs_unitSign (x : ℝ) : |p15UnitSign x| = 1 := by
  by_cases hx : 0 ≤ x <;> simp [p15UnitSign, hx]

private lemma p15_rounded_dot_backward
    (fp : StandardFPModel) {n : ℕ} (a x : Fin n → ℝ)
    (hvalid : GammaValid fp.u n) :
    ∃ d : Fin n → ℝ,
      (∀ i, |d i| ≤ gamma fp.u n * |a i|) ∧
      roundedDotProduct fp n a x = ∑ i : Fin n, (a i + d i) * x i := by
  let exact : ℝ := ∑ i : Fin n, a i * x i
  let err : ℝ := roundedDotProduct fp n a x - exact
  let weight : ℝ := ∑ i : Fin n, |a i * x i|
  have hweight : 0 ≤ weight := by
    dsimp [weight]
    positivity
  have herr : |err| ≤ gamma fp.u n * weight := by
    simpa [err, exact, weight] using
      p15_rounded_dot_forward_error fp a x hvalid
  by_cases hw : weight = 0
  · refine ⟨fun _ => 0, ?_, ?_⟩
    · intro i
      simp only [abs_zero]
      exact mul_nonneg (p15_gamma_nonneg fp.u_nonneg hvalid) (abs_nonneg _)
    · have he : err = 0 := by
        have : |err| = 0 := le_antisymm (by simpa [hw] using herr) (abs_nonneg _)
        exact abs_eq_zero.mp this
      dsimp [err, exact] at he
      simp only [add_zero]
      linarith
  · have hwpos : 0 < weight := lt_of_le_of_ne hweight (Ne.symm hw)
    let d : Fin n → ℝ := fun i =>
      (err / weight) * |a i| * p15UnitSign (x i)
    have hquot : |err| / weight ≤ gamma fp.u n := by
      apply (div_le_iff₀ hwpos).2
      simpa [mul_comm] using herr
    have hd : ∀ i, |d i| ≤ gamma fp.u n * |a i| := by
      intro i
      have hqnonneg : 0 ≤ |err| / weight :=
        div_nonneg (abs_nonneg _) hweight
      calc
        |d i| = (|err| / weight) * |a i| := by
          simp [d, abs_mul, abs_div, abs_of_pos hwpos, p15_abs_unitSign]
        _ ≤ gamma fp.u n * |a i| :=
          mul_le_mul_of_nonneg_right hquot (abs_nonneg _)
    refine ⟨d, hd, ?_⟩
    have hsum : (∑ i : Fin n, d i * x i) = err := by
      calc
        (∑ i : Fin n, d i * x i) =
            ∑ i : Fin n, (err / weight) * |a i * x i| := by
              apply Finset.sum_congr rfl
              intro i _
              simp only [d]
              rw [mul_assoc, mul_assoc, p15_unitSign_mul, abs_mul]
        _ = (err / weight) * weight := by
              rw [Finset.mul_sum]
        _ = err := div_mul_cancel₀ err hw
    dsimp [err, exact] at hsum ⊢
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    linarith

private lemma p15_rounded_rect_matvec_backward
    (fp : StandardFPModel) {m n : ℕ}
    (A : P15RectMatrix m n) (x : Fin n → ℝ)
    (hvalid : GammaValid fp.u n) :
    ∃ D : P15RectMatrix m n,
      p15RectFrobNorm D ≤ gamma fp.u n * p15RectFrobNorm A ∧
      p15RoundedRectMatVec fp A x =
        p15RectMatVec (p15RectAdd A D) x := by
  classical
  let rowProof (i : Fin m) := p15_rounded_dot_backward fp (A i) x hvalid
  let D : P15RectMatrix m n := fun i => Classical.choose (rowProof i)
  have hD (i : Fin m) :
      (∀ j, |D i j| ≤ gamma fp.u n * |A i j|) ∧
      roundedDotProduct fp n (A i) x =
        ∑ j : Fin n, (A i j + D i j) * x j :=
    Classical.choose_spec (rowProof i)
  have hgamma : 0 ≤ gamma fp.u n :=
    p15_gamma_nonneg fp.u_nonneg hvalid
  have hsq (i : Fin m) (j : Fin n) :
      (D i j) ^ 2 ≤ (gamma fp.u n * |A i j|) ^ 2 := by
    apply sq_le_sq.mpr
    simpa [abs_mul, abs_of_nonneg hgamma] using (hD i).1 j
  have hsumsq :
      (∑ i : Fin m, ∑ j : Fin n, (D i j) ^ 2) ≤
        (gamma fp.u n) ^ 2 *
          (∑ i : Fin m, ∑ j : Fin n, (A i j) ^ 2) := by
    calc
      (∑ i : Fin m, ∑ j : Fin n, (D i j) ^ 2) ≤
          ∑ i : Fin m, ∑ j : Fin n,
            (gamma fp.u n * |A i j|) ^ 2 := by
              apply Finset.sum_le_sum
              intro i _
              apply Finset.sum_le_sum
              intro j _
              exact hsq i j
      _ = (gamma fp.u n) ^ 2 *
          (∑ i : Fin m, ∑ j : Fin n, (A i j) ^ 2) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              rw [mul_pow, sq_abs]
  refine ⟨D, ?_, ?_⟩
  · unfold p15RectFrobNorm
    calc
      Real.sqrt (∑ i : Fin m, ∑ j : Fin n, (D i j) ^ 2) ≤
          Real.sqrt ((gamma fp.u n) ^ 2 *
            (∑ i : Fin m, ∑ j : Fin n, (A i j) ^ 2)) :=
              Real.sqrt_le_sqrt hsumsq
      _ = Real.sqrt ((gamma fp.u n) ^ 2) *
          Real.sqrt (∑ i : Fin m, ∑ j : Fin n, (A i j) ^ 2) := by
              rw [Real.sqrt_mul (sq_nonneg (gamma fp.u n))]
      _ = gamma fp.u n *
          Real.sqrt (∑ i : Fin m, ∑ j : Fin n, (A i j) ^ 2) := by
              rw [Real.sqrt_sq hgamma]
  · funext i
    exact (hD i).2

private lemma p15_rect_matmul_matvec
    {m n p : ℕ} (A : P15RectMatrix m n)
    (B : P15RectMatrix n p) (x : Fin p → ℝ) :
    p15RectMatVec (p15RectMatMul A B) x =
      p15RectMatVec A (p15RectMatVec B x) := by
  funext i
  unfold p15RectMatVec p15RectMatMul
  simp_rw [Finset.sum_mul, Finset.mul_sum]
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
  obtain ⟨ΔYT, hΔYT, hw⟩ :=
    p15_rounded_rect_matvec_backward fp (p15RectTranspose Y) v hb
  obtain ⟨ΔX, hΔX, hz⟩ :=
    p15_rounded_rect_matvec_backward fp X
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
              (p15_rect_matmul_matvec _ _ _).symm

end HighamBench
