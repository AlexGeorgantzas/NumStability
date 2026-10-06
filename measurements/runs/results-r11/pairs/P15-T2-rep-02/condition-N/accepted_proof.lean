import HighamBench.P15Definitions

namespace HighamBench

private lemma p15_gamma_nonneg {u : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hv : GammaValid u n) : 0 ≤ gamma u n := by
  unfold GammaValid at hv
  unfold gamma
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu)
    (le_of_lt (sub_pos.mpr hv))

private lemma p15_gamma_step {u : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hv : GammaValid u (n + 1)) :
    gamma u n + u + gamma u n * u ≤ gamma u (n + 1) := by
  have hn : (n : ℝ) * u < 1 := by
    unfold GammaValid at hv
    have hcast : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcast hu) hv
  have hd : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hn
  have hd' : 0 < 1 - ((n + 1 : ℕ) : ℝ) * u := by
    exact sub_pos.mpr hv
  have heq : gamma u n + u + gamma u n * u =
      (((n + 1 : ℕ) : ℝ) * u) / (1 - (n : ℝ) * u) := by
    unfold gamma
    field_simp [hd.ne']
    push_cast
    ring
  rw [heq]
  unfold gamma
  have hdenle : 1 - ((n + 1 : ℕ) : ℝ) * u ≤ 1 - (n : ℝ) * u := by
    push_cast
    nlinarith
  exact div_le_div_of_nonneg_left
    (mul_nonneg (Nat.cast_nonneg _) hu) hd' hdenle

private lemma p15_gammaValid_pred {u : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hv : GammaValid u (n + 1)) : GammaValid u n := by
  unfold GammaValid at *
  push_cast at hv ⊢
  nlinarith

private lemma p15_gamma_mono_step {u : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hv : GammaValid u (n + 1)) :
    gamma u n ≤ gamma u (n + 1) := by
  have hvn := p15_gammaValid_pred hu hv
  have hgn := p15_gamma_nonneg hu hvn
  calc
    gamma u n ≤ gamma u n + u + gamma u n * u := by
      nlinarith [mul_nonneg hgn hu]
    _ ≤ gamma u (n + 1) := p15_gamma_step hu hv

private lemma p15_abs_factor_step {u d t : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hv : GammaValid u (n + 1))
    (hd : |d| ≤ u) (ht : |t| ≤ gamma u n) :
    |(1 + d) * (1 + t) - 1| ≤ gamma u (n + 1) := by
  have hvn := p15_gammaValid_pred hu hv
  have hgn := p15_gamma_nonneg hu hvn
  calc
    |(1 + d) * (1 + t) - 1| = |d + t + d * t| := by ring
    _ ≤ |d| + |t| + |d| * |t| := by
      calc
        |d + t + d * t| ≤ |d + t| + |d * t| := abs_add_le _ _
        _ ≤ (|d| + |t|) + |d| * |t| := by
          gcongr
          · exact abs_add_le d t
          · exact le_of_eq (abs_mul d t)
        _ = |d| + |t| + |d| * |t| := by ring
    _ ≤ u + gamma u n + u * gamma u n := by gcongr
    _ = gamma u n + u + gamma u n * u := by ring
    _ ≤ gamma u (n + 1) := p15_gamma_step hu hv

private lemma p15_foldl_add_backward (fp : StandardFPModel) :
    ∀ (n : ℕ) (z : Fin n → ℝ) (init : ℝ), GammaValid fp.u n →
      ∃ θ₀ : ℝ, ∃ θ : Fin n → ℝ,
        Fin.foldl n (fun acc i ↦ fp.fl_add acc (z i)) init =
            init * (1 + θ₀) + ∑ i, z i * (1 + θ i) ∧
        |θ₀| ≤ gamma fp.u n ∧ ∀ i, |θ i| ≤ gamma fp.u n
  | 0, z, init, hv => by
      refine ⟨0, fun i ↦ Fin.elim0 i, ?_, ?_, ?_⟩
      · simp
      · simp [gamma]
      · intro i
        exact Fin.elim0 i
  | n + 1, z, init, hv => by
      obtain ⟨d, hd, hadd⟩ := fp.model_add init (z 0)
      have hvn : GammaValid fp.u n := p15_gammaValid_pred fp.u_nonneg hv
      obtain ⟨t₀, t, hfold, ht₀, ht⟩ :=
        p15_foldl_add_backward fp n (fun i ↦ z i.succ)
          (fp.fl_add init (z 0)) hvn
      let q : ℝ := (1 + d) * (1 + t₀) - 1
      refine ⟨q, Fin.cases q t, ?_, ?_, ?_⟩
      · rw [Fin.foldl_succ, hfold, hadd, Fin.sum_univ_succ]
        simp only [Fin.cases_zero, Fin.cases_succ]
        dsimp [q]
        ring
      · exact p15_abs_factor_step fp.u_nonneg hv hd ht₀
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact p15_abs_factor_step fp.u_nonneg hv hd ht₀
        · exact le_trans (ht j) (p15_gamma_mono_step fp.u_nonneg hv)

private lemma p15_roundedDot_backward (fp : StandardFPModel) :
    ∀ (n : ℕ) (a x : Fin n → ℝ), GammaValid fp.u n →
      ∃ Δ : Fin n → ℝ,
        roundedDotProduct fp n a x = ∑ i, (a i + Δ i) * x i ∧
        ∀ i, |Δ i| ≤ gamma fp.u n * |a i|
  | 0, a, x, hv => by
      refine ⟨fun i ↦ Fin.elim0 i, ?_, ?_⟩
      · simp [roundedDotProduct]
      · intro i
        exact Fin.elim0 i
  | n + 1, a, x, hv => by
      choose d hd hmul using fun i ↦ fp.model_mul (a i) (x i)
      have hvn : GammaValid fp.u n := p15_gammaValid_pred fp.u_nonneg hv
      obtain ⟨t₀, t, hfold, ht₀, ht⟩ :=
        p15_foldl_add_backward fp n
          (fun i ↦ fp.fl_mul (a i.succ) (x i.succ))
          (fp.fl_mul (a 0) (x 0)) hvn
      let q : Fin (n + 1) → ℝ := fun i ↦
        a i * ((1 + d i) * (1 + Fin.cases t₀ t i) - 1)
      refine ⟨q, ?_, ?_⟩
      · rw [show roundedDotProduct fp (n + 1) a x =
          Fin.foldl n
            (fun acc i ↦ fp.fl_add acc
              (fp.fl_mul (a i.succ) (x i.succ)))
            (fp.fl_mul (a 0) (x 0)) by rfl]
        rw [hfold, hmul 0, Fin.sum_univ_succ]
        congr 1
        · dsimp [q]
          ring
        · apply Finset.sum_congr rfl
          intro i hi
          rw [hmul i.succ]
          dsimp [q]
          ring
      · intro i
        dsimp [q]
        rw [abs_mul]
        have hf : |(1 + d i) * (1 + Fin.cases t₀ t i) - 1| ≤
            gamma fp.u (n + 1) := by
          refine Fin.cases ?_ (fun j ↦ ?_) i
          · exact p15_abs_factor_step fp.u_nonneg hv (hd 0) ht₀
          · exact p15_abs_factor_step fp.u_nonneg hv (hd j.succ) (ht j)
        simpa [mul_comm] using
          (mul_le_mul_of_nonneg_left hf (abs_nonneg (a i)))

private lemma p15_frob_of_componentwise {m n : ℕ}
    {E A : P15RectMatrix m n} {g : ℝ} (hg : 0 ≤ g)
    (h : ∀ i j, |E i j| ≤ g * |A i j|) :
    p15RectFrobNorm E ≤ g * p15RectFrobNorm A := by
  let sE : ℝ := ∑ i : Fin m, ∑ j : Fin n, E i j ^ 2
  let sA : ℝ := ∑ i : Fin m, ∑ j : Fin n, A i j ^ 2
  have hsE : 0 ≤ sE := by
    dsimp [sE]
    positivity
  have hsA : 0 ≤ sA := by
    dsimp [sA]
    positivity
  have hs : sE ≤ g ^ 2 * sA := by
    dsimp [sE, sA]
    calc
      (∑ i : Fin m, ∑ j : Fin n, E i j ^ 2) ≤
          ∑ i : Fin m, ∑ j : Fin n, g ^ 2 * A i j ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        have hij := h i j
        have hp : 0 ≤ g * |A i j| := mul_nonneg hg (abs_nonneg _)
        have hij2 := (sq_le_sq₀ (abs_nonneg (E i j)) hp).2 hij
        simpa [sq_abs, mul_pow] using hij2
      _ = g ^ 2 * ∑ i : Fin m, ∑ j : Fin n, A i j ^ 2 := by
        simp_rw [Finset.mul_sum]
  unfold p15RectFrobNorm
  dsimp [sE, sA] at hsE hsA hs ⊢
  have heq := Real.sq_sqrt hsE
  have haq := Real.sq_sqrt hsA
  have he := Real.sqrt_nonneg (∑ i : Fin m, ∑ j : Fin n, E i j ^ 2)
  have ha := Real.sqrt_nonneg (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2)
  have hsq :
      Real.sqrt (∑ i : Fin m, ∑ j : Fin n, E i j ^ 2) ^ 2 ≤
        (g * Real.sqrt (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2)) ^ 2 := by
    rw [heq, mul_pow, haq]
    exact hs
  exact (sq_le_sq₀ he (mul_nonneg hg ha)).1 hsq

private lemma p15_roundedRectMatVec_backward (fp : StandardFPModel)
    {m n : ℕ} (A : P15RectMatrix m n) (x : Fin n → ℝ)
    (hv : GammaValid fp.u n) :
    ∃ Δ : P15RectMatrix m n,
      p15RectFrobNorm Δ ≤ gamma fp.u n * p15RectFrobNorm A ∧
      p15RoundedRectMatVec fp A x =
        p15RectMatVec (p15RectAdd A Δ) x := by
  choose Δ hdot hΔ using fun i ↦ p15_roundedDot_backward fp n (A i) x hv
  refine ⟨Δ, p15_frob_of_componentwise (p15_gamma_nonneg fp.u_nonneg hv) hΔ, ?_⟩
  funext i
  exact hdot i

private lemma p15_u_le_gamma_succ {u : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hv : GammaValid u (n + 1)) : u ≤ gamma u (n + 1) := by
  have hvn := p15_gammaValid_pred hu hv
  have hgn := p15_gamma_nonneg hu hvn
  have hprod := mul_nonneg hgn hu
  nlinarith [p15_gamma_step hu hv]

private lemma p15_gamma_inv_numeric {u : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hv : GammaValid u (n + 1)) :
    (gamma u n + u) / (1 - u) ≤ gamma u (n + 1) := by
  have hvn := p15_gammaValid_pred hu hv
  have hnu : (n : ℝ) * u < 1 := hvn
  have hnext : ((n + 1 : ℕ) : ℝ) * u < 1 := hv
  have hu1 : u < 1 := by
    have hone : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
    exact lt_of_le_of_lt (by simpa using mul_le_mul_of_nonneg_right hone hu) hnext
  have hd₁ : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hnu
  have hd₂ : 0 < 1 - u := sub_pos.mpr hu1
  have hd₃ : 0 < 1 - ((n + 1 : ℕ) : ℝ) * u := sub_pos.mpr hnext
  unfold gamma
  apply (div_le_div_iff₀ hd₂ hd₃).2
  field_simp [hd₁.ne']
  push_cast
  nlinarith [mul_nonneg (Nat.cast_nonneg n) hu]

private lemma p15_abs_inv_factor_step {u d t : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hv : GammaValid u (n + 1))
    (hd : |d| ≤ u) (ht : |t| ≤ gamma u n) :
    |(1 + t) / (1 + d) - 1| ≤ gamma u (n + 1) := by
  have hnext : ((n + 1 : ℕ) : ℝ) * u < 1 := hv
  have hu1 : u < 1 := by
    have hone : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
    exact lt_of_le_of_lt (by simpa using mul_le_mul_of_nonneg_right hone hu) hnext
  have hden : 0 < 1 + d := by
    have hlow : -u ≤ d := (abs_le.mp hd).1
    nlinarith
  have heq : (1 + t) / (1 + d) - 1 = (t - d) / (1 + d) := by
    field_simp [hden.ne']
    ring
  rw [heq, abs_div, abs_of_pos hden]
  apply le_trans (div_le_div_of_nonneg_right (abs_sub t d) hden.le)
  apply le_trans (div_le_div_of_nonneg_right (add_le_add ht hd) hden.le)
  have hden_lower : 1 - u ≤ 1 + d := by
    have := (abs_le.mp hd).1
    linarith
  have hnum : 0 ≤ gamma u n + u := by
    exact add_nonneg (p15_gamma_nonneg hu (p15_gammaValid_pred hu hv)) hu
  apply le_trans (div_le_div_of_nonneg_left hnum (sub_pos.mpr hu1) hden_lower)
  exact p15_gamma_inv_numeric hu hv

private lemma p15_foldl_sub_normalized (fp : StandardFPModel) :
    ∀ (n : ℕ) (a x : Fin n → ℝ) (rhs : ℝ), GammaValid fp.u n →
      ∃ P : ℝ, ∃ ρ : Fin n → ℝ,
        P ≠ 0 ∧ |P⁻¹ - 1| ≤ gamma fp.u n ∧
        Fin.foldl n
            (fun acc i ↦ fp.fl_sub acc (fp.fl_mul (a i) (x i))) rhs =
          P * (rhs - ∑ i, (a i * (1 + ρ i)) * x i) ∧
        ∀ i, |ρ i| ≤ gamma fp.u n
  | 0, a, x, rhs, hv => by
      refine ⟨1, fun i ↦ Fin.elim0 i, one_ne_zero, ?_, ?_, ?_⟩
      · simp [gamma]
      · simp
      · intro i
        exact Fin.elim0 i
  | n + 1, a, x, rhs, hv => by
      obtain ⟨d, hd, hsub⟩ :=
        fp.model_sub rhs (fp.fl_mul (a 0) (x 0))
      obtain ⟨e, he, hmul⟩ := fp.model_mul (a 0) (x 0)
      have hvn := p15_gammaValid_pred fp.u_nonneg hv
      obtain ⟨P, ρ, hP, hPinv, hfold, hρ⟩ :=
        p15_foldl_sub_normalized fp n (fun i ↦ a i.succ)
          (fun i ↦ x i.succ)
          (fp.fl_sub rhs (fp.fl_mul (a 0) (x 0))) hvn
      have hnext : ((n + 1 : ℕ) : ℝ) * fp.u < 1 := hv
      have hu1 : fp.u < 1 := by
        have hone : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
        exact lt_of_le_of_lt
          (by simpa using mul_le_mul_of_nonneg_right hone fp.u_nonneg) hnext
      have h1d : 1 + d ≠ 0 := by
        have := (abs_le.mp hd).1
        nlinarith
      let ρ' : Fin (n + 1) → ℝ := Fin.cases e
        (fun i ↦ (1 + ρ i) / (1 + d) - 1)
      refine ⟨P * (1 + d), ρ', mul_ne_zero hP h1d, ?_, ?_, ?_⟩
      · have heq : (P * (1 + d))⁻¹ - 1 =
            (1 + (P⁻¹ - 1)) / (1 + d) - 1 := by
          field_simp [hP, h1d]
          ring
        rw [heq]
        exact p15_abs_inv_factor_step fp.u_nonneg hv hd hPinv
      · have hsum :
            (∑ i : Fin n,
              (a i.succ *
                (1 + ((1 + ρ i) / (1 + d) - 1))) * x i.succ) =
              (∑ i : Fin n, (a i.succ * (1 + ρ i)) * x i.succ) /
                (1 + d) := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro i hi
            field_simp [h1d]
            ring
        rw [Fin.foldl_succ, hfold, hsub, hmul, Fin.sum_univ_succ]
        simp only [ρ', Fin.cases_zero, Fin.cases_succ]
        rw [hsum]
        field_simp [h1d]
        ring
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact le_trans he (p15_u_le_gamma_succ fp.u_nonneg hv)
        · exact p15_abs_inv_factor_step fp.u_nonneg hv hd (hρ j)

private lemma p15_gammaValid_mono {u : ℝ} {m n : ℕ}
    (hu : 0 ≤ u) (hmn : m ≤ n) (hv : GammaValid u n) :
    GammaValid u m := by
  unfold GammaValid at *
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) hu) hv

private lemma p15_gamma_mono {u : ℝ} {m n : ℕ}
    (hu : 0 ≤ u) (hmn : m ≤ n) (hv : GammaValid u n) :
    gamma u m ≤ gamma u n := by
  have hvm := p15_gammaValid_mono hu hmn hv
  have hma : (m : ℝ) * u ≤ (n : ℝ) * u :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) hu
  have hdm : 0 < 1 - (m : ℝ) * u := sub_pos.mpr hvm
  have hdn : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hv
  unfold gamma
  apply (div_le_div_iff₀ hdm hdn).2
  nlinarith

private lemma p15_sum_eq_lower_add_diag {n : ℕ} (q : Fin n)
    (f : Fin n → ℝ) (hupper : ∀ j, q.val < j.val → f j = 0) :
    (∑ j : Fin n, f j) =
      (∑ t : Fin q.val, f ⟨t.val, lt_trans t.isLt q.isLt⟩) + f q := by
  classical
  let g : ℕ → ℝ := fun k ↦ if hk : k < n then f ⟨k, hk⟩ else 0
  have hall : (∑ j : Fin n, f j) = ∑ k ∈ Finset.range n, g k := by
    rw [← Fin.sum_univ_eq_sum_range g n]
    apply Finset.sum_congr rfl
    intro j hj
    simp [g]
  have hlow :
      (∑ t : Fin q.val, f ⟨t.val, lt_trans t.isLt q.isLt⟩) =
        ∑ k ∈ Finset.range q.val, g k := by
    rw [← Fin.sum_univ_eq_sum_range g q.val]
    apply Finset.sum_congr rfl
    intro t ht
    simp only [g, dif_pos (lt_trans t.isLt q.isLt)]
  have htail : ∑ k ∈ Finset.Ico (q.val + 1) n, g k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkn : k < n := (Finset.mem_Ico.mp hk).2
    have hqk : q.val < k := by
      have := (Finset.mem_Ico.mp hk).1
      omega
    simp only [g, dif_pos hkn]
    exact hupper ⟨k, hkn⟩ hqk
  rw [hall, hlow]
  rw [← Finset.sum_range_add_sum_Ico g (Nat.succ_le_iff.mpr q.isLt)]
  rw [Finset.sum_range_succ, htail, add_zero]
  simp [g, q.isLt]

private lemma p15_forward_row_backward (fp : StandardFPModel) {n : ℕ}
    (L : P15Matrix n) (rhs : P15Vector n)
    (hdiag : ∀ i, L i i ≠ 0) (hlower : p15LowerTriangular L)
    (hv : GammaValid fp.u n) (q : Fin n) (x : P15Vector n) :
    let s := Fin.foldl q.val
      (fun acc (t : Fin q.val) ↦
        fp.fl_sub acc
          (fp.fl_mul (L q ⟨t.val, lt_trans t.isLt q.isLt⟩)
            (x ⟨t.val, lt_trans t.isLt q.isLt⟩)))
      (rhs q)
    let z := fp.fl_div s (L q q)
    ∀ y : P15Vector n,
      (∀ j, j.val ≤ q.val → y j = Function.update x q z j) →
      ∃ e : Fin n → ℝ,
        (∀ j, |e j| ≤ gamma fp.u n * |L q j|) ∧
        (∑ j, (L q j + e j) * y j) = rhs q := by
  dsimp only
  intro y hy
  let castQ : Fin q.val → Fin n :=
    fun t ↦ ⟨t.val, lt_trans t.isLt q.isLt⟩
  have hvq : GammaValid fp.u q.val :=
    p15_gammaValid_mono fp.u_nonneg (Nat.le_of_lt q.isLt) hv
  obtain ⟨P, ρ, hP, hPinv, hs, hρ⟩ :=
    p15_foldl_sub_normalized fp q.val
      (fun t ↦ L q (castQ t)) (fun t ↦ x (castQ t)) (rhs q) hvq
  let s := Fin.foldl q.val
      (fun acc (t : Fin q.val) ↦
        fp.fl_sub acc (fp.fl_mul (L q (castQ t)) (x (castQ t)))) (rhs q)
  obtain ⟨d, hd, hz⟩ := fp.model_div s (L q q) (hdiag q)
  have hvqs : GammaValid fp.u (q.val + 1) :=
    p15_gammaValid_mono fp.u_nonneg (by omega) hv
  have hnext : ((q.val + 1 : ℕ) : ℝ) * fp.u < 1 := hvqs
  have hu1 : fp.u < 1 := by
    have hone : (1 : ℝ) ≤ ((q.val + 1 : ℕ) : ℝ) := by norm_num
    exact lt_of_le_of_lt
      (by simpa using mul_le_mul_of_nonneg_right hone fp.u_nonneg) hnext
  have h1d : 1 + d ≠ 0 := by
    have := (abs_le.mp hd).1
    nlinarith
  have hQ : |(P * (1 + d))⁻¹ - 1| ≤ gamma fp.u (q.val + 1) := by
    have heq : (P * (1 + d))⁻¹ - 1 =
        (1 + (P⁻¹ - 1)) / (1 + d) - 1 := by
      field_simp [hP, h1d]
      ring
    rw [heq]
    exact p15_abs_inv_factor_step fp.u_nonneg hvqs hd hPinv
  let e : Fin n → ℝ := fun j ↦
    if hj : j.val < q.val then L q j * ρ ⟨j.val, hj⟩
    else if j = q then L q q * ((P * (1 + d))⁻¹ - 1)
    else 0
  refine ⟨e, ?_, ?_⟩
  · intro j
    dsimp [e]
    split_ifs with hj hjq
    · rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (le_trans (hρ ⟨j.val, hj⟩)
          (p15_gamma_mono fp.u_nonneg (Nat.le_of_lt q.isLt) hv))
        (abs_nonneg (L q j))
    · subst j
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (le_trans hQ (p15_gamma_mono fp.u_nonneg (by omega) hv))
        (abs_nonneg (L q q))
    · have hqj : q.val < j.val := by omega
      rw [hlower q j hqj]
      simp
  · let f : Fin n → ℝ := fun j ↦ (L q j + e j) * y j
    rw [p15_sum_eq_lower_add_diag q f]
    · have hlow :
          (∑ t : Fin q.val, f (castQ t)) =
            ∑ t : Fin q.val,
              (L q (castQ t) * (1 + ρ t)) * x (castQ t) := by
          apply Finset.sum_congr rfl
          intro t ht
          have hle : (castQ t).val ≤ q.val := by
            dsimp [castQ]
            omega
          have hne : castQ t ≠ q := by
            intro h
            have hh := congrArg Fin.val h
            dsimp [castQ] at hh
            omega
          dsimp [f]
          rw [hy (castQ t) hle]
          rw [Function.update_apply, if_neg hne]
          dsimp [e, castQ]
          rw [if_pos t.isLt]
          ring
      have hdiagY : y q = fp.fl_div s (L q q) := by
        rw [hy q (le_refl _)]
        simp
        rfl
      have hs' : s = P *
          (rhs q - ∑ t : Fin q.val,
            (L q (castQ t) * (1 + ρ t)) * x (castQ t)) := by
        exact hs
      rw [hlow]
      dsimp [f, e]
      simp only [lt_self_iff_false, ↓reduceDIte, if_pos]
      rw [hdiagY]
      have hL := hdiag q
      field_simp [hP, h1d, hL] at hz ⊢
      rw [hz, hs']
      ring
    · intro j hqj
      dsimp [f, e]
      rw [hlower q j hqj]
      simp [show ¬j.val < q.val by omega, show j ≠ q by
        intro h
        subst j
        omega]

private lemma p15_forward_steps_backward (fp : StandardFPModel) {n : ℕ}
    (L : P15Matrix n) (rhs : P15Vector n)
    (hdiag : ∀ i, L i i ≠ 0) (hlower : p15LowerTriangular L)
    (hv : GammaValid fp.u n) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : P15Vector n),
      let y := roundedForwardSubSteps fp n L rhs k hk x
      (∀ j, j.val < n - k → y j = x j) ∧
      ∀ i, n - k ≤ i.val →
        ∃ e : Fin n → ℝ,
          (∀ j, |e j| ≤ gamma fp.u n * |L i j|) ∧
          (∑ j, (L i j + e j) * y j) = rhs i := by
  intro k
  induction k with
  | zero =>
      intro hk x
      constructor
      · intro j hj
        rfl
      · intro i hi
        omega
  | succ k ih =>
      intro hk x
      have hk' : k ≤ n := Nat.le_of_succ_le hk
      have hq : n - k - 1 < n := by omega
      let q : Fin n := ⟨n - k - 1, hq⟩
      let s := Fin.foldl (n - k - 1)
        (fun acc (t : Fin (n - k - 1)) ↦
          fp.fl_sub acc
            (fp.fl_mul (L q ⟨t.val, by omega⟩) (x ⟨t.val, by omega⟩)))
        (rhs q)
      let x' := Function.update x q (fp.fl_div s (L q q))
      have hstep : roundedForwardSubSteps fp n L rhs (k + 1) hk x =
          roundedForwardSubSteps fp n L rhs k hk' x' := by
        simp only [roundedForwardSubSteps]
        rfl
      obtain ⟨hunch, hrows⟩ := ih hk' x'
      constructor
      · intro j hj
        rw [hstep, hunch j (by omega)]
        dsimp [x']
        rw [Function.update_apply, if_neg]
        intro heq
        have := congrArg Fin.val heq
        dsimp [q] at this
        omega
      · intro i hi
        rw [hstep]
        by_cases hiq : i = q
        · subst i
          apply p15_forward_row_backward fp L rhs hdiag hlower hv q x
          intro j hj
          have hu := hunch j (by dsimp [q] at hj ⊢; omega)
          exact hu
        · have hneval : i.val ≠ q.val := by
            intro h
            apply hiq
            exact Fin.ext h
          have hqi : q.val < i.val := by
            have hbase : n - (k + 1) = n - k - 1 := by omega
            rw [hbase] at hi
            have hqval : q.val = n - k - 1 := rfl
            omega
          exact hrows i (by dsimp [q] at hqi ⊢; omega)

private lemma p15_roundedForwardSub_backward (fp : StandardFPModel) {n : ℕ}
    (L : P15Matrix n) (rhs : P15Vector n)
    (hdiag : ∀ i, L i i ≠ 0) (hlower : p15LowerTriangular L)
    (hv : GammaValid fp.u n) :
    ∃ Δ : P15Matrix n,
      p15RectFrobNorm Δ ≤ gamma fp.u n * p15RectFrobNorm L ∧
      p15RectMatVec (p15RectAdd L Δ)
        (roundedForwardSub fp n L rhs) = rhs := by
  let xhat := roundedForwardSub fp n L rhs
  have hsteps := p15_forward_steps_backward fp L rhs hdiag hlower hv n (le_refl n)
    (fun _ ↦ 0)
  choose Δ hΔ hrow using fun i ↦ hsteps.2 i (by omega)
  refine ⟨Δ,
    p15_frob_of_componentwise (p15_gamma_nonneg fp.u_nonneg hv) hΔ, ?_⟩
  funext i
  exact hrow i

private lemma p15_rectMatMul_matVec {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p)
    (x : Fin p → ℝ) :
    p15RectMatVec (p15RectMatMul A B) x =
      p15RectMatVec A (p15RectMatVec B x) := by
  funext i
  unfold p15RectMatVec p15RectMatMul
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- P15-T2: the two-block instance of equation (4.22) in the proof of
Theorem 4.4, with the source's low-rank and triangular-solve perturbations. -/
theorem p15_t2_two_block_equation_4_22
    {b r : ℕ} (fp : StandardFPModel)
    (T₀ T₁ : P15Matrix b) (X Y : P15RectMatrix b r)
    (v₀ v₁ : P15Vector b)
    (hT₀diag : ∀ i, T₀ i i ≠ 0)
    (hT₁diag : ∀ i, T₁ i i ≠ 0)
    (hT₀lower : p15LowerTriangular T₀)
    (hT₁lower : p15LowerTriangular T₁)
    (hb : GammaValid fp.u b) (hr : GammaValid fp.u r) :
    let x₀ := roundedForwardSub fp b T₀ v₀
    let wInner := p15RoundedRectMatVec fp (p15RectTranspose Y) x₀
    let wHat := p15RoundedRectMatVec fp X wInner
    let rhsHat := fun i ↦ fp.fl_sub (v₁ i) (wHat i)
    let x₁ := roundedForwardSub fp b T₁ rhsHat
    ∃ ΔT₀ : P15Matrix b, ∃ ΔYT : P15RectMatrix r b,
      ∃ ΔX : P15RectMatrix b r, ∃ θ : P15Vector b,
      ∃ ΔT₁ : P15Matrix b, ∃ ΔT₁₀ : P15Matrix b,
        p15RectFrobNorm ΔT₀ ≤ gamma fp.u b * p15RectFrobNorm T₀ ∧
        p15RectFrobNorm ΔYT ≤
          gamma fp.u b * p15RectFrobNorm (p15RectTranspose Y) ∧
        p15RectFrobNorm ΔX ≤ gamma fp.u r * p15RectFrobNorm X ∧
        (∀ i, |θ i| ≤ fp.u) ∧
        p15RectFrobNorm ΔT₁ ≤ gamma fp.u b * p15RectFrobNorm T₁ ∧
        p15RectMatVec (p15RectAdd T₀ ΔT₀) x₀ = v₀ ∧
        wInner = p15RectMatVec
          (p15RectAdd (p15RectTranspose Y) ΔYT) x₀ ∧
        wHat = p15RectMatVec (p15RectAdd X ΔX) wInner ∧
        (∀ i, rhsHat i = (v₁ i - wHat i) * (1 + θ i)) ∧
        p15RectMatVec (p15RectAdd T₁ ΔT₁) x₁ = rhsHat ∧
        (∀ i j,
          p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀ i j =
            (1 + θ i) *
              p15RectMatMul (p15RectAdd X ΔX)
                (p15RectAdd (p15RectTranspose Y) ΔYT) i j) ∧
        ∀ i,
          p15RectMatVec
                (p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀) x₀ i +
              p15RectMatVec (p15RectAdd T₁ ΔT₁) x₁ i =
            v₁ i * (1 + θ i) := by
  -- PROOF_START P15-T2-H001
  dsimp only
  obtain ⟨ΔT₀, hΔT₀, hsolve₀⟩ :=
    p15_roundedForwardSub_backward fp T₀ v₀ hT₀diag hT₀lower hb
  obtain ⟨ΔYT, hΔYT, hinner⟩ :=
    p15_roundedRectMatVec_backward fp (p15RectTranspose Y)
      (roundedForwardSub fp b T₀ v₀) hb
  obtain ⟨ΔX, hΔX, houter⟩ :=
    p15_roundedRectMatVec_backward fp X
      (p15RoundedRectMatVec fp (p15RectTranspose Y)
        (roundedForwardSub fp b T₀ v₀)) hr
  choose θ hθ hrhs using fun i ↦ fp.model_sub (v₁ i)
    (p15RoundedRectMatVec fp X
      (p15RoundedRectMatVec fp (p15RectTranspose Y)
        (roundedForwardSub fp b T₀ v₀)) i)
  obtain ⟨ΔT₁, hΔT₁, hsolve₁⟩ :=
    p15_roundedForwardSub_backward fp T₁
      (fun i ↦ fp.fl_sub (v₁ i)
        (p15RoundedRectMatVec fp X
          (p15RoundedRectMatVec fp (p15RectTranspose Y)
            (roundedForwardSub fp b T₀ v₀)) i))
      hT₁diag hT₁lower hb
  let A : P15RectMatrix b r := p15RectAdd X ΔX
  let B : P15RectMatrix r b :=
    p15RectAdd (p15RectTranspose Y) ΔYT
  let ΔT₁₀ : P15Matrix b := fun i j ↦
    (1 + θ i) * p15RectMatMul A B i j - p15LowRankMatrix X Y i j
  refine ⟨ΔT₀, ΔYT, ΔX, θ, ΔT₁, ΔT₁₀,
    hΔT₀, hΔYT, hΔX, hθ, hΔT₁, hsolve₀,
    hinner, houter, hrhs, hsolve₁, ?_, ?_⟩
  · intro i j
    dsimp [ΔT₁₀, p15RectAdd]
    ring
  · intro i
    have hproduct :
        p15RectMatVec (p15RectMatMul A B)
            (roundedForwardSub fp b T₀ v₀) =
          p15RoundedRectMatVec fp X
            (p15RoundedRectMatVec fp (p15RectTranspose Y)
              (roundedForwardSub fp b T₀ v₀)) := by
      calc
        p15RectMatVec (p15RectMatMul A B)
            (roundedForwardSub fp b T₀ v₀) =
            p15RectMatVec A
              (p15RectMatVec B (roundedForwardSub fp b T₀ v₀)) :=
          p15_rectMatMul_matVec A B _
        _ = p15RectMatVec A
              (p15RoundedRectMatVec fp (p15RectTranspose Y)
                (roundedForwardSub fp b T₀ v₀)) := by rw [hinner]
        _ = p15RoundedRectMatVec fp X
              (p15RoundedRectMatVec fp (p15RectTranspose Y)
                (roundedForwardSub fp b T₀ v₀)) := by rw [houter]
    have hblock :
        p15RectMatVec
            (p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀)
            (roundedForwardSub fp b T₀ v₀) i =
          (1 + θ i) *
            p15RoundedRectMatVec fp X
              (p15RoundedRectMatVec fp (p15RectTranspose Y)
                (roundedForwardSub fp b T₀ v₀)) i := by
      unfold p15RectMatVec
      simp_rw [show ∀ j,
          p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀ i j =
            (1 + θ i) * p15RectMatMul A B i j by
        intro j
        dsimp [ΔT₁₀, p15RectAdd]
        ring]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      exact congrArg (fun z ↦ (1 + θ i) * z) (congrFun hproduct i)
    rw [hblock, congrFun hsolve₁ i, hrhs i]
    ring

end HighamBench
