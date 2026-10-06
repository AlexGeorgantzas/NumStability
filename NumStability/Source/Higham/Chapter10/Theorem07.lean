import NumStability.Algorithms.HighamChapter10

namespace NumStability

open scoped BigOperators

/-!
# Higham Chapter 10, Theorem 10.7

The source-strength proof of Higham, Theorem 10.7.  The decisive scalar
estimate keeps the two stage-local rounding constants separate.  This avoids
the additive pivot-rounding loss in the older, split perturbation proof.
-/

/-- Scalar signed-border endgame used at the first nonpositive Cholesky
    pivot.  Here `x² = t` and `y² = C W`; the two coefficient alternatives
    are the boundary and interior minima of the same quadratic on `x ≤ y`.
    The formulation contains no division and is convenient for the exact
    `γ_k` bookkeeping downstream. -/
theorem signedBorder_source_endgame
    (a W t E I P Q B C x y : ℝ)
    (hW : 0 ≤ W) (ht : 0 ≤ t) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x ≤ y) (hx2 : x ^ 2 = t) (hy2 : y ^ 2 = C * W)
    (hQdef : Q = E - I)
    (hshift : P * t ≤ (E - 1) * a + t)
    (hboundary : P ≤ B → Q ≥ C * (2 * B - P))
    (hinterior : B < P → B ^ 2 * C ≤ P * Q) :
    a - t + I * W + 2 * B * x * y ≤ E * (a + W) := by
  have hcore : 2 * B * x * y ≤ P * t + Q * W := by
    by_cases hPB : P ≤ B
    · have hcoef : 0 ≤ 2 * B - P := by linarith
      have hQW : (2 * B - P) * y ^ 2 ≤ Q * W := by
        rw [hy2]
        have := mul_le_mul_of_nonneg_right (hboundary hPB) hW
        nlinarith
      have hfac1 : 0 ≤ y - x := by linarith
      have hfac2 : 0 ≤ (2 * B - P) * y - P * x := by
        have hBP : 0 ≤ B - P := by linarith
        have h1 : 0 ≤ 2 * (B - P) * y := by positivity
        have h2 : 0 ≤ P * (y - x) := mul_nonneg hP hfac1
        nlinarith
      have hprod : 0 ≤ (y - x) * ((2 * B - P) * y - P * x) :=
        mul_nonneg hfac1 hfac2
      rw [← hx2]
      nlinarith [hQW, hprod]
    · have hBP : B < P := lt_of_not_ge hPB
      have hprod := hinterior hBP
      have htW : 0 ≤ t * W := mul_nonneg ht hW
      have hscaled := mul_le_mul_of_nonneg_right hprod htW
      have hsq : (2 * B * x * y) ^ 2 ≤ (P * t + Q * W) ^ 2 := by
        rw [show (2 * B * x * y) ^ 2 =
            4 * B ^ 2 * (x ^ 2 * y ^ 2) by ring,
          hx2, hy2]
        nlinarith [hscaled, sq_nonneg (P * t - Q * W)]
      have hleft : 0 ≤ 2 * B * x * y := by positivity
      have hright : 0 ≤ P * t + Q * W := by positivity
      nlinarith
  rw [hQdef] at hcore
  nlinarith

/-- Closed form for the second denominator which occurs in Theorem 10.7. -/
lemma gamma_div_one_sub_gamma_eq (fp : FPModel) (k : ℕ)
    (hk : gammaValid fp k) (hγ : gamma fp k < 1) :
    gamma fp k / (1 - gamma fp k) =
      (k : ℝ) * fp.u / (1 - 2 * (k : ℝ) * fp.u) := by
  have hku : (k : ℝ) * fp.u < 1 := by
    simpa [gammaValid] using hk
  have hd : 0 < 1 - (k : ℝ) * fp.u := by linarith
  have h2 : 2 * (k : ℝ) * fp.u < 1 := by
    have := hγ
    unfold gamma at this
    rw [div_lt_one hd] at this
    linarith
  unfold gamma
  push_cast
  field_simp [hd.ne', (by linarith : 1 - 2 * (k : ℝ) * fp.u ≠ 0)]
  ring

/-- The signed-pivot ratio simplifies exactly; this is why the raw pivot
    information must not be weakened to a global `γ` constant. -/
lemma one_sub_gamma_div_one_add_gamma_eq (fp : FPModel) (k : ℕ)
    (hk : gammaValid fp k) :
    (1 - gamma fp k) / (1 + gamma fp k) =
      1 - 2 * (k : ℝ) * fp.u := by
  have hku : (k : ℝ) * fp.u < 1 := by
    simpa [gammaValid] using hk
  have hd : 0 < 1 - (k : ℝ) * fp.u := by linarith
  unfold gamma
  push_cast
  field_simp [hd.ne']
  ring

/-- The reciprocal column-norm factor in closed form. -/
lemma one_div_one_sub_gamma_eq (fp : FPModel) (k : ℕ)
    (hk : gammaValid fp k) (hγ : gamma fp k < 1) :
    1 / (1 - gamma fp k) =
      (1 - (k : ℝ) * fp.u) / (1 - 2 * (k : ℝ) * fp.u) := by
  have hku : (k : ℝ) * fp.u < 1 := by
    simpa [gammaValid] using hk
  have hd : 0 < 1 - (k : ℝ) * fp.u := by linarith
  have h2 : 2 * (k : ℝ) * fp.u < 1 := by
    have := hγ
    unfold gamma at this
    rw [div_lt_one hd] at this
    linarith
  unfold gamma
  push_cast
  field_simp [hd.ne', (by linarith : 1 - 2 * (k : ℝ) * fp.u ≠ 0)]
  ring

/-- Native (unweakened) interior mass at stage `j`.  Unlike the display
    (10.21) wrapper, this retains `j γ_{j+1}/(1-γ_{j+1})`. -/
theorem higham10_7_stage_interior_mass_native (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i l : Fin n, A i l = A l i)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1)
    (j : Fin n)
    (IH : ∀ l : Fin n, l.val < j.val → 0 < fl_cholPivot fp n A l)
    (y : Fin j.val → ℝ) :
    |∑ i : Fin j.val, ∑ l : Fin j.val, y i *
      ((∑ p : Fin j.val,
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨l.val, by omega⟩) -
        A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) * y l| ≤
      (gamma fp (j.val + 1) / (1 - gamma fp (j.val + 1)) *
        (j.val : ℝ)) *
      ∑ i : Fin j.val,
        A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2 := by
  have hm1valid : gammaValid fp (j.val + 1) :=
    gammaValid_mono fp (by omega) hn1
  have hγm0 : 0 ≤ gamma fp (j.val + 1) := gamma_nonneg fp hm1valid
  have hγm1 : gamma fp (j.val + 1) < 1 :=
    lt_of_le_of_lt (gamma_mono fp (by omega) hn1) hγ1
  have h1γm : (0 : ℝ) < 1 - gamma fp (j.val + 1) := by linarith
  have hu : fp.u < 1 := by
    have h := hn1
    unfold gammaValid at h
    push_cast at h
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))
      fp.u_nonneg]
  set Am : Fin j.val → Fin j.val → ℝ :=
    fun i' l' => A ⟨i'.val, by omega⟩ ⟨l'.val, by omega⟩ with hAm
  have hcert : CholeskyBackwardError j.val Am
      (fl_cholesky fp j.val Am) (gamma fp (j.val + 1)) :=
    fl_cholesky_block_certificate fp j.isLt.le A hsym hu hm1valid IH
  have hloc : ∀ p q : Fin j.val,
      fl_cholesky fp j.val Am p q =
      fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨q.val, by omega⟩ :=
    fun p q => fl_cholesky_leading_principal fp j.isLt.le A p q
  have hentry : ∀ i l : Fin j.val,
      |(∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨l.val, by omega⟩) -
        A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩| ≤
      gamma fp (j.val + 1) / (1 - gamma fp (j.val + 1)) *
        (Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) *
         Real.sqrt (A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩)) := by
    intro i l
    have h := chol_cert_scaled_entrywise_le j.val Am
      (fl_cholesky fp j.val Am) (gamma fp (j.val + 1)) hγm0 hγm1 hcert
      (fun l' => (hAdiag _).le) i l
    simp only [hloc] at h
    exact h
  have hc0 : 0 ≤ gamma fp (j.val + 1) /
      (1 - gamma fp (j.val + 1)) := div_nonneg hγm0 h1γm.le
  have hE : ∀ i l : Fin j.val,
      |((∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨l.val, by omega⟩) -
          A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) /
        (Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) *
         Real.sqrt (A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩))| ≤
      gamma fp (j.val + 1) / (1 - gamma fp (j.val + 1)) := by
    intro i l
    have hsi := Real.sqrt_pos.mpr (hAdiag (⟨i.val, by omega⟩ : Fin n))
    have hsl := Real.sqrt_pos.mpr (hAdiag (⟨l.val, by omega⟩ : Fin n))
    rw [abs_div, abs_of_pos (mul_pos hsi hsl),
      div_le_iff₀ (mul_pos hsi hsl)]
    exact hentry i l
  have hquad := quadForm_cert_of_entrywise
    (fun i l : Fin j.val =>
      ((∑ p : Fin j.val,
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨l.val, by omega⟩) -
        A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) /
      (Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) *
       Real.sqrt (A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩)))
    (gamma fp (j.val + 1) / (1 - gamma fp (j.val + 1))) hc0 hE
  exact scaled_interior_mass_normwise_quad
    (fun i l : Fin j.val =>
      (∑ p : Fin j.val,
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨l.val, by omega⟩) -
        A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩)
    (fun i : Fin j.val => A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩)
    (fun i => (hAdiag _).le)
    (gamma fp (j.val + 1) / (1 - gamma fp (j.val + 1)) *
      (j.val : ℝ)) hquad y
    (fun i l h => h.elim
      (fun h0 => absurd h0 (hAdiag _).ne')
      (fun h0 => absurd h0 (hAdiag _).ne'))

/-- Cauchy--Schwarz part of `scaled_border_mass_normwise`, before its
    AM--GM weakening.  Retaining the geometric mean is essential at the
    exact Theorem 10.7 threshold. -/
lemma scaled_border_mass_sqrt {m : ℕ}
    (δ : Fin m → ℝ) (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i)
    (ε t : ℝ) (hε0 : 0 ≤ ε) (ht0 : 0 ≤ t)
    (hnz : ∀ i : Fin m, a i = 0 → δ i = 0)
    (hcert : ∑ i : Fin m,
      (if a i = 0 then 0 else δ i ^ 2 / a i) ≤ ε ^ 2 * t)
    (y : Fin m → ℝ) :
    |2 * ∑ i : Fin m, y i * δ i| ≤
      2 * ε * Real.sqrt t *
        Real.sqrt (∑ i : Fin m, a i * y i ^ 2) := by
  set W : ℝ := ∑ i : Fin m, a i * y i ^ 2 with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i _ =>
    mul_nonneg (ha i) (sq_nonneg _)
  have hcs : (∑ i : Fin m, y i * δ i) ^ 2 ≤ W * (ε ^ 2 * t) := by
    have hsplit : ∑ i : Fin m, y i * δ i =
        ∑ i : Fin m, (y i * Real.sqrt (a i)) *
          (if a i = 0 then 0 else δ i / Real.sqrt (a i)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : a i = 0
      · rw [if_pos hi, hnz i hi]
        simp
      · rw [if_neg hi]
        have hi' := lt_of_le_of_ne (ha i) (Ne.symm hi)
        have hsi := Real.sqrt_pos.mpr hi'
        field_simp
    rw [hsplit]
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => y i * Real.sqrt (a i))
      (fun i => if a i = 0 then 0 else δ i / Real.sqrt (a i))
    have hL : ∑ i : Fin m, (y i * Real.sqrt (a i)) ^ 2 = W := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_pow, Real.sq_sqrt (ha i)]
      ring
    have hR : ∑ i : Fin m,
        (if a i = 0 then 0 else δ i / Real.sqrt (a i)) ^ 2 =
        ∑ i : Fin m, (if a i = 0 then 0 else δ i ^ 2 / a i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : a i = 0
      · rw [if_pos hi, if_pos hi]
        norm_num
      · rw [if_neg hi, if_neg hi, div_pow, Real.sq_sqrt (ha i)]
    rw [hL, hR] at h
    exact h.trans (mul_le_mul_of_nonneg_left hcert hW0)
  have hsum : |∑ i : Fin m, y i * δ i| ≤
      ε * Real.sqrt t * Real.sqrt W := by
    have h1 : |∑ i : Fin m, y i * δ i| ^ 2 ≤
        (ε * Real.sqrt t * Real.sqrt W) ^ 2 := by
      rw [sq_abs]
      calc (∑ i : Fin m, y i * δ i) ^ 2
          ≤ W * (ε ^ 2 * t) := hcs
        _ = (ε * Real.sqrt t * Real.sqrt W) ^ 2 := by
            rw [mul_pow, mul_pow, Real.sq_sqrt ht0,
              Real.sq_sqrt hW0]
            ring
    have h2 : (0 : ℝ) ≤ ε * Real.sqrt t * Real.sqrt W := by positivity
    nlinarith [abs_nonneg (∑ i : Fin m, y i * δ i), h1, h2]
  calc |2 * ∑ i : Fin m, y i * δ i|
      = 2 * |∑ i : Fin m, y i * δ i| := by
        rw [abs_mul]
        norm_num
    _ ≤ 2 * (ε * Real.sqrt t * Real.sqrt W) := by linarith
    _ = 2 * ε * Real.sqrt t * Real.sqrt W := by ring

/-- Native scaled column certificate for the border computed before stage
    `j`'s square root. -/
theorem higham10_7_stage_border_certificate_native (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i l : Fin n, A i l = A l i)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1)
    (j : Fin n)
    (IH : ∀ l : Fin n, l.val < j.val → 0 < fl_cholPivot fp n A l) :
    ∑ i : Fin j.val,
      (((∑ p : Fin j.val,
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
        fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
        A ⟨i.val, by omega⟩ j) ^ 2 /
        A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) ≤
      (j.val : ℝ) * (gamma fp (j.val + 2) ^ 2 *
        (∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2) /
        (1 - gamma fp (j.val + 1))) := by
  have hm1valid : gammaValid fp (j.val + 1) :=
    gammaValid_mono fp (by omega) hn1
  have hγmG : gamma fp (j.val + 1) ≤ gamma fp (n + 1) :=
    gamma_mono fp (by omega) hn1
  have hγm1 : gamma fp (j.val + 1) < 1 :=
    lt_of_le_of_lt hγmG hγ1
  have h1γm : (0 : ℝ) < 1 - gamma fp (j.val + 1) := by linarith
  have hγ2valid : gammaValid fp (j.val + 2) :=
    gammaValid_mono fp (by omega) hn1
  have hdiag_ne : ∀ i : Fin j.val,
      fl_cholesky fp n A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ ≠ 0 := by
    intro i
    rw [fl_cholesky_diag_eq fp n A ⟨i.val, by omega⟩]
    have hu : fp.u < 1 := by
      have h := hn1
      unfold gammaValid at h
      push_cast at h
      nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))
        fp.u_nonneg]
    exact (fl_sqrt_pos fp hu _ (IH ⟨i.val, by omega⟩ i.isLt)).ne'
  set Am1 : Fin (j.val + 1) → Fin (j.val + 1) → ℝ :=
    fun i' l' => A ⟨i'.val, by omega⟩ ⟨l'.val, by omega⟩ with hAm1
  have hloc1 : ∀ p q : Fin (j.val + 1),
      fl_cholesky fp (j.val + 1) Am1 p q =
      fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨q.val, by omega⟩ :=
    fun p q => fl_cholesky_leading_principal fp
      (by omega : j.val + 1 ≤ n) A p q
  have hbord : ∀ i : Fin j.val,
      |(∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
          fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
        A ⟨i.val, by omega⟩ j| ≤
      gamma fp (j.val + 2) *
        (Real.sqrt (∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ ^ 2) *
         Real.sqrt (∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2)) := by
    intro i
    have hdz : fl_cholesky fp (j.val + 1) Am1
        ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ ≠ 0 := by
      rw [hloc1 ⟨i.val, by omega⟩ ⟨i.val, by omega⟩]
      exact hdiag_ne i
    have hb := fl_cholesky_border_bound fp (n := j.val + 1) Am1
      hγ2valid (Fin.last j.val) i hdz
    simp only [hloc1] at hb
    exact hb
  have hu : fp.u < 1 := by
    have h := hn1
    unfold gammaValid at h
    push_cast at h
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))
      fp.u_nonneg]
  set Am : Fin j.val → Fin j.val → ℝ :=
    fun i' l' => A ⟨i'.val, by omega⟩ ⟨l'.val, by omega⟩ with hAm
  have hcert : CholeskyBackwardError j.val Am
      (fl_cholesky fp j.val Am) (gamma fp (j.val + 1)) :=
    fl_cholesky_block_certificate fp j.isLt.le A hsym hu hm1valid IH
  have hloc : ∀ p q : Fin j.val,
      fl_cholesky fp j.val Am p q =
      fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨q.val, by omega⟩ :=
    fun p q => fl_cholesky_leading_principal fp j.isLt.le A p q
  have hcol : ∀ i : Fin j.val,
      (1 - gamma fp (j.val + 1)) *
        ∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ ^ 2 ≤
      A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ := by
    intro i
    have h := chol_cert_colNormSq_le j.val Am (fl_cholesky fp j.val Am)
      (gamma fp (j.val + 1)) hcert i
    simp only [hloc] at h
    exact h
  have hT0 : 0 ≤ ∑ p : Fin j.val,
      fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2 :=
    Finset.sum_nonneg fun p _ => sq_nonneg _
  have hstep : ∀ i : Fin j.val,
      (((∑ p : Fin j.val,
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
        fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
        A ⟨i.val, by omega⟩ j) ^ 2 /
        A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) ≤
      gamma fp (j.val + 2) ^ 2 *
        (∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2) /
        (1 - gamma fp (j.val + 1)) := by
    intro i
    have hDsq0 : (0 : ℝ) ≤ ∑ p : Fin j.val,
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ ^ 2 :=
      Finset.sum_nonneg fun p _ => sq_nonneg _
    have hδsq : ((∑ p : Fin j.val,
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
        fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
        A ⟨i.val, by omega⟩ j) ^ 2 ≤
        gamma fp (j.val + 2) ^ 2 *
        (∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ ^ 2) *
        ∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2 := by
      have h := mul_self_le_mul_self (abs_nonneg _) (hbord i)
      rw [abs_mul_abs_self] at h
      have hexp : (gamma fp (j.val + 2) *
          (Real.sqrt (∑ p : Fin j.val,
            fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ ^ 2) *
           Real.sqrt (∑ p : Fin j.val,
            fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2))) *
          (gamma fp (j.val + 2) *
          (Real.sqrt (∑ p : Fin j.val,
            fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ ^ 2) *
           Real.sqrt (∑ p : Fin j.val,
            fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2))) =
          gamma fp (j.val + 2) ^ 2 *
          (∑ p : Fin j.val,
            fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ ^ 2) *
          ∑ p : Fin j.val,
            fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2 := by
        rw [show ∀ g a b : ℝ, g * (a * b) * (g * (a * b)) =
            g ^ 2 * (a * a) * (b * b) from fun g a b => by ring,
          Real.mul_self_sqrt hDsq0, Real.mul_self_sqrt hT0]
      rw [hexp] at h
      rw [pow_two]
      exact h
    rw [div_le_div_iff₀ (hAdiag _) h1γm]
    have h1 := mul_le_mul_of_nonneg_right hδsq h1γm.le
    have h2 := mul_le_mul_of_nonneg_left (hcol i)
      (mul_nonneg (sq_nonneg (gamma fp (j.val + 2))) hT0)
    nlinarith [h1, h2]
  calc
    ∑ i : Fin j.val,
      (((∑ p : Fin j.val,
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
        fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
        A ⟨i.val, by omega⟩ j) ^ 2 /
        A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩)
      ≤ ∑ _i : Fin j.val,
        gamma fp (j.val + 2) ^ 2 *
        (∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2) /
        (1 - gamma fp (j.val + 1)) := Finset.sum_le_sum fun i _ => hstep i
    _ = (j.val : ℝ) * (gamma fp (j.val + 2) ^ 2 *
        (∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2) /
        (1 - gamma fp (j.val + 1))) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]

/-- Coarse common-denominator form of the native border certificate.  This
    weakening is deliberately postponed until after the stage-local proof;
    it keeps the exact raw-pivot ratio available in the endgame. -/
theorem higham10_7_stage_border_mass_commonDenom (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i l : Fin n, A i l = A l i)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1)
    (j : Fin n)
    (IH : ∀ l : Fin n, l.val < j.val → 0 < fl_cholPivot fp n A l)
    (y : Fin j.val → ℝ) :
    |2 * ∑ i : Fin j.val, y i *
      ((∑ p : Fin j.val,
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
        fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
        A ⟨i.val, by omega⟩ j)| ≤
      2 * (((j.val : ℝ) + 2) * fp.u /
        (1 - 2 * ((n : ℝ) + 1) * fp.u)) *
      Real.sqrt (∑ p : Fin j.val,
        fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2) *
      (Real.sqrt ((j.val : ℝ) /
          (1 - 2 * ((n : ℝ) + 1) * fp.u)) *
       Real.sqrt (∑ i : Fin j.val,
          A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2)) := by
  set d : ℝ := 1 - 2 * ((n : ℝ) + 1) * fp.u with hddef
  set B : ℝ := ((j.val : ℝ) + 2) * fp.u / d with hBdef
  set C : ℝ := (j.val : ℝ) / d with hCdef
  set t : ℝ := ∑ p : Fin j.val,
    fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2 with htdef
  set W : ℝ := ∑ i : Fin j.val,
    A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2 with hWdef
  have hnu : ((n : ℝ) + 1) * fp.u < 1 := by
    have h := hn1
    unfold gammaValid at h
    push_cast at h
    nlinarith
  have hbase : 0 < 1 - ((n : ℝ) + 1) * fp.u := by linarith
  have hd : 0 < d := by
    have h := hγ1
    unfold gamma at h
    push_cast at h
    rw [div_lt_one hbase] at h
    dsimp [d]
    nlinarith
  have hB : 0 ≤ B := div_nonneg
    (mul_nonneg (by positivity) fp.u_nonneg) hd.le
  have hC : 0 ≤ C := div_nonneg (Nat.cast_nonneg _) hd.le
  have ht : 0 ≤ t := Finset.sum_nonneg fun p _ => sq_nonneg _
  have hW : 0 ≤ W := Finset.sum_nonneg fun i _ =>
    mul_nonneg (hAdiag _).le (sq_nonneg _)
  have hmvalid : gammaValid fp (j.val + 1) :=
    gammaValid_mono fp (by omega) hn1
  have hmγ1 : gamma fp (j.val + 1) < 1 :=
    lt_of_le_of_lt (gamma_mono fp (by omega) hn1) hγ1
  have h2valid : gammaValid fp (j.val + 2) :=
    gammaValid_mono fp (by omega) hn1
  have h2den : 0 < 1 - ((j.val : ℝ) + 2) * fp.u := by
    have h := h2valid
    unfold gammaValid at h
    push_cast at h
    nlinarith
  have hd_le_h2 : d ≤ 1 - ((j.val : ℝ) + 2) * fp.u := by
    dsimp [d]
    have hj : (j.val : ℝ) + 2 ≤ 2 * ((n : ℝ) + 1) := by
      norm_num
      exact_mod_cast (show j.val + 2 ≤ 2 * (n + 1) by omega)
    nlinarith [mul_le_mul_of_nonneg_right hj fp.u_nonneg]
  have hγ2B : gamma fp (j.val + 2) ≤ B := by
    unfold gamma
    push_cast
    dsimp [B]
    exact div_le_div₀ (mul_nonneg (by positivity) fp.u_nonneg) le_rfl
      hd hd_le_h2
  have hrecip : 1 / (1 - gamma fp (j.val + 1)) ≤ 1 / d := by
    rw [one_div_one_sub_gamma_eq fp (j.val + 1) hmvalid hmγ1]
    simp only [Nat.cast_add, Nat.cast_one]
    have hdm : 0 < 1 - 2 * ((j.val : ℝ) + 1) * fp.u := by
      have h := hmγ1
      have hv : 0 < 1 - ((j.val : ℝ) + 1) * fp.u := by
        have h' := hmvalid
        unfold gammaValid at h'
        push_cast at h'
        linarith
      unfold gamma at h
      push_cast at h
      rw [div_lt_one hv] at h
      linarith
    have hd_le_hdm : d ≤ 1 - 2 * ((j.val : ℝ) + 1) * fp.u := by
      dsimp [d]
      have hj : (j.val : ℝ) + 1 ≤ (n : ℝ) + 1 := by
        exact_mod_cast (show j.val + 1 ≤ n + 1 by omega)
      nlinarith [mul_le_mul_of_nonneg_right hj fp.u_nonneg]
    change (1 - ((j.val : ℝ) + 1) * fp.u) /
          (1 - 2 * ((j.val : ℝ) + 1) * fp.u) ≤ 1 / d
    calc (1 - ((j.val : ℝ) + 1) * fp.u) /
          (1 - 2 * ((j.val : ℝ) + 1) * fp.u)
        ≤ 1 / (1 - 2 * ((j.val : ℝ) + 1) * fp.u) := by
          exact div_le_div_of_nonneg_right (by nlinarith [fp.u_nonneg]) hdm.le
      _ ≤ 1 / d := one_div_le_one_div_of_le hd hd_le_hdm
  have hγsq : gamma fp (j.val + 2) ^ 2 ≤ B ^ 2 := by
    have hγ0 := gamma_nonneg fp h2valid
    nlinarith [sq_nonneg (B - gamma fp (j.val + 2))]
  have hcoef : (j.val : ℝ) *
      (gamma fp (j.val + 2) ^ 2 * t /
        (1 - gamma fp (j.val + 1))) ≤
      (B * Real.sqrt C) ^ 2 * t := by
    have hrecip0 : 0 ≤ 1 / (1 - gamma fp (j.val + 1)) := by
      have : 0 < 1 - gamma fp (j.val + 1) := by linarith
      positivity
    have h1 : gamma fp (j.val + 2) ^ 2 *
        (1 / (1 - gamma fp (j.val + 1))) ≤ B ^ 2 * (1 / d) :=
      mul_le_mul hγsq hrecip (by positivity) (sq_nonneg B)
    have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg j.val)
    have h3 := mul_le_mul_of_nonneg_right h2 ht
    calc
      (j.val : ℝ) *
          (gamma fp (j.val + 2) ^ 2 * t /
            (1 - gamma fp (j.val + 1)))
          = (j.val : ℝ) *
            (gamma fp (j.val + 2) ^ 2 *
              (1 / (1 - gamma fp (j.val + 1)))) * t := by ring
      _ ≤ (j.val : ℝ) * (B ^ 2 * (1 / d)) * t := h3
      _ = (B * Real.sqrt C) ^ 2 * t := by
        rw [mul_pow, Real.sq_sqrt hC]
        dsimp [C]
        field_simp [hd.ne']
  have hnative := higham10_7_stage_border_certificate_native fp A hsym
    hAdiag hn1 hγ1 j IH
  have hcert0 : ∑ i : Fin j.val,
      (((∑ p : Fin j.val,
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
        fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
        A ⟨i.val, by omega⟩ j) ^ 2 /
        A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) ≤
      (B * Real.sqrt C) ^ 2 * t := hnative.trans hcoef
  have hcert : ∑ i : Fin j.val,
      (if A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ = 0 then 0 else
        ((∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
          fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
          A ⟨i.val, by omega⟩ j) ^ 2 /
          A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) ≤
      (B * Real.sqrt C) ^ 2 * t := by
    simpa only [if_neg (hAdiag _).ne'] using hcert0
  have hsqrt := scaled_border_mass_sqrt
    (fun i : Fin j.val =>
      (∑ p : Fin j.val,
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
        fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
        A ⟨i.val, by omega⟩ j)
    (fun i : Fin j.val => A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩)
    (fun i => (hAdiag _).le) (B * Real.sqrt C) t (by positivity) ht
    (fun i h0 => absurd h0 (hAdiag _).ne') hcert y
  dsimp [B, C, t, W, d] at hsqrt ⊢
  convert hsqrt using 1 <;> ring

private noncomputable def sourceD (u : ℝ) (n : ℕ) : ℝ :=
  1 - 2 * ((n : ℝ) + 1) * u

private noncomputable def sourceE (u : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * ((n : ℝ) + 1) * u / sourceD u n

private noncomputable def sourceI (u : ℝ) (j n : ℕ) : ℝ :=
  (j : ℝ) * ((j : ℝ) + 1) * u / sourceD u n

private noncomputable def sourceB (u : ℝ) (j n : ℕ) : ℝ :=
  ((j : ℝ) + 2) * u / sourceD u n

private noncomputable def sourceC (u : ℝ) (j n : ℕ) : ℝ :=
  (j : ℝ) / sourceD u n

private noncomputable def sourceR (u : ℝ) (j : ℕ) : ℝ :=
  1 - 2 * ((j : ℝ) + 1) * u

private noncomputable def sourceP (u : ℝ) (j n : ℕ) : ℝ :=
  1 - (1 - sourceE u n) / sourceR u j

private noncomputable def sourceQ (u : ℝ) (j n : ℕ) : ℝ :=
  sourceE u n - sourceI u j n

set_option maxHeartbeats 1000000 in
/-- Integer-polynomial core of the common-denominator coefficient bound.
    The proof separates the three small adjacent cases; all remaining cases
    follow from elementary monotone lower bounds. -/
private lemma source_common_product_core (u : ℝ) (n j : ℕ)
    (hu : 0 ≤ u) (hn3 : 3 ≤ n) (hj1 : 1 ≤ j) (hjn : j < n)
    (hd : 0 < sourceD u n) (hE1 : sourceE u n < 1) :
    let N : ℝ := n
    let J : ℝ := j
    let d := sourceD u n
    let r := sourceR u j
    let M := N * (N + 1)
    let K := J + 1
    let L := M - J * K
    (M - 2 * K * d) * L * d ≥ J * (J + 2) ^ 2 * r := by
  dsimp only
  set N : ℝ := (n : ℝ) with hN
  set J : ℝ := (j : ℝ) with hJ
  set d : ℝ := sourceD u n with hd'
  set r : ℝ := sourceR u j with hr'
  set M : ℝ := N * (N + 1) with hM
  set K : ℝ := J + 1 with hK
  set L : ℝ := M - J * K with hL
  have hN3 : (3 : ℝ) ≤ N := by
    simpa [N] using (show (3 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn3)
  have hJ1 : (1 : ℝ) ≤ J := by
    simpa [J] using (show (1 : ℝ) ≤ (j : ℝ) by exact_mod_cast hj1)
  have hJN : J < N := by
    simpa [J, N] using (show (j : ℝ) < (n : ℝ) by exact_mod_cast hjn)
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN3
  have hNp2 : 0 < N + 2 := by linarith
  have hdle1 : d ≤ 1 := by
    dsimp [d, sourceD]
    nlinarith
  have hrle1 : r ≤ 1 := by
    dsimp [r, sourceR]
    nlinarith
  have hr0 : 0 < r := by
    dsimp [r, sourceR, d, sourceD] at *
    have hjcast : J + 1 ≤ N + 1 := by linarith
    have hmul := mul_le_mul_of_nonneg_right hjcast hu
    nlinarith
  have hsmall : (N + 1) * (N + 2) * u < 1 := by
    have h := hE1
    dsimp [sourceE] at h
    rw [div_lt_one hd] at h
    rw [hd', sourceD] at h
    rw [show (n : ℝ) = N from hN.symm] at h
    nlinarith
  have hdlo : N / (N + 2) < d := by
    rw [div_lt_iff₀ hNp2]
    dsimp [d, sourceD, N] at *
    have hm := mul_lt_mul_of_pos_left hsmall (by positivity : (0 : ℝ) < 2 / (N + 1))
    field_simp [show N + 1 ≠ 0 by linarith] at hm
    nlinarith
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hL0 : 0 ≤ L := by
    dsimp [L, M, K]
    have hfac1 : 0 ≤ N - J := by linarith
    have hfac2 : 0 ≤ N + J + 1 := by positivity
    nlinarith [mul_nonneg hfac1 hfac2]
  by_cases hjone : j = 1
  · subst j
    norm_num [J, K] at *
    have hM12 : 12 ≤ M := by
      dsimp [M]
      nlinarith [mul_nonneg (by linarith : 0 ≤ N - 3)
        (by linarith : 0 ≤ N + 4)]
    have hA8 : 8 ≤ M - 4 * d := by nlinarith
    have hL10 : 10 ≤ M - 2 := by linarith
    have hd35 : (3 / 5 : ℝ) ≤ d := by
      have hfrac : (3 / 5 : ℝ) ≤ N / (N + 2) := by
        rw [le_div_iff₀ hNp2]
        nlinarith
      linarith
    have hA0 : 0 ≤ M - 4 * d := by linarith
    have hL' : 0 ≤ M - 2 := by linarith
    have h1 := mul_le_mul hA8 hL10 (by norm_num) hA0
    have h2 := mul_le_mul_of_nonneg_right h1 hd.le
    have h48 : (48 : ℝ) ≤ 80 * d := by nlinarith
    have hrhs : 9 * r ≤ 9 := by nlinarith
    nlinarith [h2, h48, hrhs]
  · have hj2 : 2 ≤ j := by omega
    have hJ2 : (2 : ℝ) ≤ J := by
      simpa [J] using (show (2 : ℝ) ≤ (j : ℝ) by exact_mod_cast hj2)
    by_cases hgap : j + 2 ≤ n
    · have hgapR : J + 2 ≤ N := by
        simpa [J, N] using
          (show (j : ℝ) + 2 ≤ (n : ℝ) by exact_mod_cast hgap)
      have hMlower : (J + 2) * (J + 3) ≤ M := by
        dsimp [M]
        have h1 : 0 ≤ N - (J + 2) := by linarith
        have h2 : 0 ≤ N + J + 3 := by positivity
        nlinarith [mul_nonneg h1 h2]
      have hA : J ^ 2 + 3 * J + 4 ≤ M - 2 * K * d := by
        dsimp [K]
        have hKd : 2 * (J + 1) * d ≤ 2 * (J + 1) :=
          calc
            2 * (J + 1) * d ≤ 2 * (J + 1) * 1 :=
              mul_le_mul_of_nonneg_left hdle1
                (by positivity : 0 ≤ 2 * (J + 1))
            _ = 2 * (J + 1) := by ring
        nlinarith
      have hLl : 4 * J + 6 ≤ L := by
        dsimp [L, K]
        nlinarith
      have hdfrac : (J + 2) / (J + 4) ≤ d := by
        have hmono : (J + 2) / (J + 4) ≤ N / (N + 2) := by
          have hJ4 : 0 < J + 4 := by linarith
          rw [div_le_div_iff₀ hJ4 hNp2]
          nlinarith
        linarith
      have hpoly : J * (J + 2) ^ 2 ≤
          (J ^ 2 + 3 * J + 4) * (4 * J + 6) *
            ((J + 2) / (J + 4)) := by
        have hJ4 : 0 < J + 4 := by linarith
        rw [show (J ^ 2 + 3 * J + 4) * (4 * J + 6) *
            ((J + 2) / (J + 4)) =
            ((J ^ 2 + 3 * J + 4) * (4 * J + 6) * (J + 2)) /
              (J + 4) by ring,
          le_div_iff₀ hJ4]
        have hp : 0 ≤ 3 * J ^ 3 + 12 * J ^ 2 + 26 * J + 24 := by
          positivity
        nlinarith
      have hA0 : 0 ≤ M - 2 * K * d :=
        le_trans (by positivity : 0 ≤ J ^ 2 + 3 * J + 4) hA
      have hmul1 := mul_le_mul hA hLl (by positivity) hA0
      have hmul2 := mul_le_mul_of_nonneg_right hmul1 hd.le
      have hmul3 := mul_le_mul_of_nonneg_left hdfrac
        (mul_nonneg hA0 hL0)
      have hR : J * (J + 2) ^ 2 * r ≤ J * (J + 2) ^ 2 :=
        mul_le_of_le_one_right (by positivity) hrle1
      nlinarith [hmul2, hmul3, hpoly, hR]
    · have hnEq : n = j + 1 := by omega
      subst n
      have hNeq : N = J + 1 := by simp [N, J]
      by_cases hj5 : 5 ≤ j
      · have hJ5 : (5 : ℝ) ≤ J := by
          simpa [J] using (show (5 : ℝ) ≤ (j : ℝ) by exact_mod_cast hj5)
        have hA : J * (J + 1) ≤ M - 2 * K * d := by
          dsimp [M, K]
          rw [hNeq]
          have hKd : 2 * (J + 1) * d ≤ 2 * (J + 1) :=
            calc
              2 * (J + 1) * d ≤ 2 * (J + 1) * 1 :=
                mul_le_mul_of_nonneg_left hdle1
                  (by positivity : 0 ≤ 2 * (J + 1))
              _ = 2 * (J + 1) := by ring
          nlinarith
        have hLeq : L = 2 * (J + 1) := by
          dsimp [L, M, K]
          rw [hNeq]
          ring
        have hdfrac : (J + 1) / (J + 3) ≤ d := by
          have := hdlo
          rw [hNeq] at this
          have hden : J + 1 + 2 = J + 3 := by ring
          rw [hden] at this
          exact this.le
        have hpoly : J * (J + 2) ^ 2 ≤
            (J * (J + 1)) * (2 * (J + 1)) * ((J + 1) / (J + 3)) := by
          have hJ3 : 0 < J + 3 := by linarith
          rw [show (J * (J + 1)) * (2 * (J + 1)) * ((J + 1) / (J + 3)) =
              ((J * (J + 1)) * (2 * (J + 1)) * (J + 1)) / (J + 3) by ring,
            le_div_iff₀ hJ3]
          have ha0 : 0 ≤ J - 5 := by linarith
          have hpos : 0 ≤ (J - 5) ^ 3 + 14 * (J - 5) ^ 2 +
              55 * (J - 5) + 40 := by positivity
          have hJ0 : 0 ≤ J := by linarith
          have hprod := mul_nonneg hJ0 hpos
          nlinarith [hprod]
        rw [hLeq]
        have hA0 : 0 ≤ M - 2 * K * d :=
          le_trans (mul_nonneg (by positivity) (by positivity)) hA
        have hfrac0 : 0 ≤ (J + 1) / (J + 3) := by positivity
        have hmulA : (J * (J + 1)) * (2 * (J + 1)) * ((J + 1) / (J + 3)) ≤
            (M - 2 * K * d) * (2 * (J + 1)) * ((J + 1) / (J + 3)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hA (by positivity)) hfrac0
        have hmul3 := mul_le_mul_of_nonneg_left hdfrac
          (mul_nonneg hA0 (by positivity : 0 ≤ 2 * (J + 1)))
        have hR : J * (J + 2) ^ 2 * r ≤ J * (J + 2) ^ 2 :=
          mul_le_of_le_one_right (by positivity) hrle1
        calc
          J * (J + 2) ^ 2 * r ≤ J * (J + 2) ^ 2 := hR
          _ ≤ (J * (J + 1)) * (2 * (J + 1)) * ((J + 1) / (J + 3)) := hpoly
          _ ≤ (M - 2 * K * d) * (2 * (J + 1)) * ((J + 1) / (J + 3)) := hmulA
          _ ≤ (M - 2 * K * d) * (2 * (J + 1)) * d := hmul3
      · have hjcases : j = 2 ∨ j = 3 ∨ j = 4 := by omega
        rcases hjcases with rfl | rfl | rfl
        · norm_num [J, N, M, K, L, d, r, sourceD, sourceR] at *
          have hs : 0 ≤ u * (1 - 12 * u) :=
            mul_nonneg hu (by nlinarith)
          change 32 * (1 - 6 * u) ≤
            (12 - 6 * (1 - 8 * u)) * 6 * (1 - 8 * u)
          ring_nf
          nlinarith [hs]
        · norm_num [J, N, M, K, L, d, r, sourceD, sourceR] at *
          have hu2 : u ^ 2 ≤ u / 30 := by
            have hm := mul_le_mul_of_nonneg_left hsmall.le hu
            nlinarith
          have hdiff : 0 ≤ 21 + 280 * u - 6400 * u ^ 2 := by
            nlinarith [hu2]
          change 75 * (1 - 8 * u) ≤
            (20 - 8 * (1 - 10 * u)) * 8 * (1 - 10 * u)
          ring_nf
          nlinarith [hdiff]
        · norm_num [J, N, M, K, L, d, r, sourceD, sourceR] at *
          have hu2 : u ^ 2 ≤ u / 42 := by
            have hm := mul_le_mul_of_nonneg_left hsmall.le hu
            nlinarith
          have hdiff : 0 ≤ 56 + 240 * u - 14400 * u ^ 2 := by
            nlinarith [hu2]
          change 144 * (1 - 10 * u) ≤
            (30 - 10 * (1 - 12 * u)) * 10 * (1 - 12 * u)
          ring_nf
          nlinarith [hdiff]

/-- Exact numerator form of the signed-pivot coefficient. -/
private lemma sourceP_formula (u : ℝ) (n j : ℕ)
    (hd : sourceD u n ≠ 0) (hr : sourceR u j ≠ 0) :
    sourceP u j n =
      u * ((n : ℝ) * ((n : ℝ) + 1) -
        2 * ((j : ℝ) + 1) * sourceD u n) /
          (sourceD u n * sourceR u j) := by
  set d : ℝ := sourceD u n with hddef
  set r : ℝ := sourceR u j with hrdef
  have hd0 : d ≠ 0 := by simpa [d] using hd
  have hr0 : r ≠ 0 := by simpa [r] using hr
  change 1 - (1 - (n : ℝ) * ((n : ℝ) + 1) * u / d) / r =
    u * ((n : ℝ) * ((n : ℝ) + 1) -
      2 * ((j : ℝ) + 1) * d) / (d * r)
  field_simp [hd0, hr0]
  rw [hddef, hrdef]
  simp [sourceD, sourceR, Nat.rawCast]
  ring

/-- Exact numerator form of the remaining interior coefficient. -/
private lemma sourceQ_formula (u : ℝ) (n j : ℕ)
    (hd : sourceD u n ≠ 0) :
    sourceQ u j n =
      u * ((n : ℝ) * ((n : ℝ) + 1) -
        (j : ℝ) * ((j : ℝ) + 1)) / sourceD u n := by
  set d : ℝ := sourceD u n with hddef
  have hd0 : d ≠ 0 := by simpa [d] using hd
  change (n : ℝ) * ((n : ℝ) + 1) * u / d -
      (j : ℝ) * ((j : ℝ) + 1) * u / d =
    u * ((n : ℝ) * ((n : ℝ) + 1) -
      (j : ℝ) * ((j : ℝ) + 1)) / d
  field_simp [hd0]

/-- The boundary alternative in the unique `n = 2`, `j = 1` stage. -/
private lemma source_boundary_two_formula (u : ℝ)
    (hd : sourceD u 2 ≠ 0) (hr : sourceR u 1 ≠ 0) :
    sourceQ u 1 2 - sourceC u 1 2 *
        (2 * sourceB u 1 2 - sourceP u 1 2) =
      8 * u ^ 2 * (1 + 12 * u) /
        (sourceD u 2 ^ 2 * sourceR u 1) := by
  set d : ℝ := sourceD u 2 with hddef
  set r : ℝ := sourceR u 1 with hrdef
  have hd0 : d ≠ 0 := by simpa [d] using hd
  have hr0 : r ≠ 0 := by simpa [r] using hr
  rw [sourceQ_formula u 2 1 hd, sourceP_formula u 2 1 hd hr]
  dsimp [sourceB, sourceC]
  norm_num [Nat.rawCast]
  rw [← hddef, ← hrdef]
  field_simp [hd0, hr0]
  rw [hddef, hrdef]
  simp only [sourceD, sourceR, Nat.rawCast]
  norm_num [Nat.rawCast]
  ring_nf
  norm_num [Nat.rawCast]
  change -(u * 4) + u * 4 + (u ^ 2 * 48 - u ^ 2 * 4 * 10) +
      u ^ 3 * 4 * 24 = u ^ 2 * 8 + u ^ 3 * 96
  ring

/-- In the two-dimensional stage, `B < P` is exactly the lower bound
    `1 < 36u` once `u > 0`. -/
private lemma sourceP_sub_B_two_formula (u : ℝ)
    (hd : sourceD u 2 ≠ 0) (hr : sourceR u 1 ≠ 0) :
    sourceP u 1 2 - sourceB u 1 2 =
      u * (36 * u - 1) / (sourceD u 2 * sourceR u 1) := by
  set d : ℝ := sourceD u 2 with hddef
  set r : ℝ := sourceR u 1 with hrdef
  have hd0 : d ≠ 0 := by simpa [d] using hd
  have hr0 : r ≠ 0 := by simpa [r] using hr
  rw [sourceP_formula u 2 1 hd hr]
  dsimp [sourceB]
  norm_num [Nat.rawCast]
  change u * (6 - 4 * d) / (d * r) - 3 * u / d =
    u * (36 * u - 1) / (d * r)
  field_simp [hd0, hr0]
  rw [hddef, hrdef]
  simp only [sourceD, sourceR, Nat.rawCast]
  norm_num [Nat.rawCast]
  ring_nf
  norm_num [Nat.rawCast]
  exact Or.inl rfl

/-- Exact product remainder in the two-dimensional stage. -/
private lemma source_product_two_formula (u : ℝ)
    (hd : sourceD u 2 ≠ 0) (hr : sourceR u 1 ≠ 0) :
    sourceP u 1 2 * sourceQ u 1 2 -
        sourceB u 1 2 ^ 2 * sourceC u 1 2 =
      -(u ^ 2 * (576 * u ^ 2 - 84 * u + 1)) /
        (sourceD u 2 ^ 3 * sourceR u 1) := by
  set d : ℝ := sourceD u 2 with hddef
  set r : ℝ := sourceR u 1 with hrdef
  have hd0 : d ≠ 0 := by simpa [d] using hd
  have hr0 : r ≠ 0 := by simpa [r] using hr
  rw [sourceP_formula u 2 1 hd hr, sourceQ_formula u 2 1 hd]
  dsimp [sourceB, sourceC]
  norm_num [Nat.rawCast]
  rw [← hddef, ← hrdef]
  field_simp [hd0, hr0]
  rw [hddef, hrdef]
  simp only [sourceD, sourceR, Nat.rawCast]
  norm_num [Nat.rawCast]
  ring_nf
  norm_num [Nat.rawCast]
  change -(u ^ 2 * 9) + u ^ 2 * 4 * 2 + u ^ 3 * 36 +
      (u ^ 3 * 4 * 12 - u ^ 4 * 4 * 144) =
    -u ^ 2 + (u ^ 3 * 84 - u ^ 4 * 576)
  ring

/-- General difference between the signed-pivot and border coefficients. -/
private lemma sourceP_sub_B_formula (u : ℝ) (n j : ℕ)
    (hd : sourceD u n ≠ 0) (hr : sourceR u j ≠ 0) :
    sourceP u j n - sourceB u j n =
      u * (((n : ℝ) * ((n : ℝ) + 1) -
          2 * ((j : ℝ) + 1) * sourceD u n) -
        ((j : ℝ) + 2) * sourceR u j) /
          (sourceD u n * sourceR u j) := by
  rw [sourceP_formula u n j hd hr]
  set d : ℝ := sourceD u n with hddef
  set r : ℝ := sourceR u j with hrdef
  have hd0 : d ≠ 0 := by simpa [d] using hd
  have hr0 : r ≠ 0 := by simpa [r] using hr
  dsimp [sourceB]
  rw [← hddef]
  field_simp [hd0, hr0] <;> ring

/-- A single exact rational identity turns the integer-polynomial core into
    the product alternative required by `signedBorder_source_endgame`. -/
private lemma source_product_diff_formula (u : ℝ) (n j : ℕ)
    (hd : sourceD u n ≠ 0) (hr : sourceR u j ≠ 0) :
    sourceP u j n * sourceQ u j n -
        sourceB u j n ^ 2 * sourceC u j n =
      u ^ 2 *
        ((((n : ℝ) * ((n : ℝ) + 1) -
              2 * ((j : ℝ) + 1) * sourceD u n) *
            ((n : ℝ) * ((n : ℝ) + 1) -
              (j : ℝ) * ((j : ℝ) + 1)) * sourceD u n) -
          (j : ℝ) * ((j : ℝ) + 2) ^ 2 * sourceR u j) /
        (sourceD u n ^ 3 * sourceR u j) := by
  rw [sourceP_formula u n j hd hr, sourceQ_formula u n j hd]
  set d : ℝ := sourceD u n with hddef
  set r : ℝ := sourceR u j with hrdef
  have hd0 : d ≠ 0 := by simpa [d] using hd
  have hr0 : r ≠ 0 := by simpa [r] using hr
  dsimp [sourceB, sourceC]
  rw [← hddef]
  field_simp [hd0, hr0] <;> ring

/-- All scalar side conditions needed by the exact source-threshold stage
    argument.  The two alternatives are exhaustive: dimensions at least
    three satisfy the product inequality (unless `u = 0`, when both do),
    while the sole two-dimensional stage has the explicit boundary formula. -/
private theorem source_common_coefficients (u : ℝ) (n j : ℕ)
    (hu : 0 ≤ u) (hn2 : 2 ≤ n) (hj1 : 1 ≤ j) (hjn : j < n)
    (hd : 0 < sourceD u n) (hE1 : sourceE u n < 1) :
    0 ≤ sourceE u n ∧
    0 ≤ sourceI u j n ∧
    0 ≤ sourceB u j n ∧
    0 ≤ sourceC u j n ∧
    0 < sourceR u j ∧
    0 ≤ sourceP u j n ∧
    0 ≤ sourceQ u j n ∧
    sourceQ u j n = sourceE u n - sourceI u j n ∧
    (sourceP u j n ≤ sourceB u j n →
      sourceQ u j n ≥ sourceC u j n *
        (2 * sourceB u j n - sourceP u j n)) ∧
    (sourceB u j n < sourceP u j n →
      sourceB u j n ^ 2 * sourceC u j n ≤
        sourceP u j n * sourceQ u j n) := by
  let N : ℝ := n
  let J : ℝ := j
  let d : ℝ := sourceD u n
  let r : ℝ := sourceR u j
  let M : ℝ := N * (N + 1)
  let K : ℝ := J + 1
  let L : ℝ := M - J * K
  have hN2 : (2 : ℝ) ≤ N := by
    simpa [N] using (show (2 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn2)
  have hJ1 : (1 : ℝ) ≤ J := by
    simpa [J] using (show (1 : ℝ) ≤ (j : ℝ) by exact_mod_cast hj1)
  have hJN : J < N := by
    simpa [J, N] using (show (j : ℝ) < (n : ℝ) by exact_mod_cast hjn)
  have hN0 : 0 < N := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hK0 : 0 ≤ K := by dsimp [K]; linarith
  have hd' : 0 < d := by simpa [d] using hd
  have hdle1 : d ≤ 1 := by
    dsimp [d, sourceD]
    nlinarith
  have hdr : d ≤ r := by
    dsimp [d, r, sourceD, sourceR]
    have hjcast : (j : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast (show j + 1 ≤ n + 1 by omega)
    nlinarith [mul_le_mul_of_nonneg_right hjcast hu]
  have hr' : 0 < r := lt_of_lt_of_le hd' hdr
  have hrle1 : r ≤ 1 := by
    dsimp [r, sourceR]
    nlinarith
  have hKle : K ≤ N := by
    simpa [K, J, N] using
      (show ((j + 1 : ℕ) : ℝ) ≤ (n : ℝ) by exact_mod_cast (show j + 1 ≤ n by omega))
  have hM2K : 0 ≤ M - 2 * K := by
    have hprod : 0 ≤ N * (N - 1) := mul_nonneg hN0.le (by linarith)
    dsimp [M]
    nlinarith
  have hKd : 2 * K * d ≤ 2 * K := by
    calc
      2 * K * d ≤ 2 * K * 1 :=
        mul_le_mul_of_nonneg_left hdle1 (by positivity)
      _ = 2 * K := by ring
  have hA0 : 0 ≤ M - 2 * K * d := by linarith
  have hJK : J * K ≤ (N - 1) * N := by
    have h1 : J * K ≤ J * N := mul_le_mul_of_nonneg_left hKle hJ0
    have h2 : J * N ≤ (N - 1) * N :=
      mul_le_mul_of_nonneg_right (by linarith) hN0.le
    exact h1.trans h2
  have hL0 : 0 ≤ L := by
    dsimp [L, M]
    nlinarith
  have hE0 : 0 ≤ sourceE u n := by
    dsimp [sourceE]
    exact div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) hu) hd.le
  have hI0 : 0 ≤ sourceI u j n := by
    dsimp [sourceI]
    exact div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) hu) hd.le
  have hB0 : 0 ≤ sourceB u j n := by
    dsimp [sourceB]
    positivity
  have hC0 : 0 ≤ sourceC u j n := by
    dsimp [sourceC]
    positivity
  have hP0 : 0 ≤ sourceP u j n := by
    rw [sourceP_formula u n j hd.ne' hr'.ne']
    exact div_nonneg (mul_nonneg hu hA0) (mul_nonneg hd.le hr'.le)
  have hQ0 : 0 ≤ sourceQ u j n := by
    rw [sourceQ_formula u n j hd.ne']
    exact div_nonneg (mul_nonneg hu hL0) hd.le
  refine ⟨hE0, hI0, hB0, hC0, hr', hP0, hQ0, rfl, ?_, ?_⟩
  · intro hPB
    by_cases hn3 : 3 ≤ n
    · by_cases hu0 : u = 0
      · subst u
        simp [sourceQ, sourceC, sourceB, sourceP, sourceE, sourceI,
          sourceD, sourceR]
      · have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
        have hN3 : (3 : ℝ) ≤ N := by
          simpa [N] using (show (3 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn3)
        have hpoly : 0 < M - 3 * J - 4 := by
          have hfac : 0 ≤ (N - 3) * (N + 1) :=
            mul_nonneg (by linarith) (by linarith)
          dsimp [M]
          nlinarith
        have hrterm : (J + 2) * r ≤ J + 2 := by
          calc
            (J + 2) * r ≤ (J + 2) * 1 :=
              mul_le_mul_of_nonneg_left hrle1 (by positivity)
            _ = J + 2 := by ring
        have hnum : 0 < (M - 2 * K * d) - (J + 2) * r := by
          dsimp [K] at hKd
          nlinarith
        have hdiff := sourceP_sub_B_formula u n j hd.ne' hr'.ne'
        have hden : 0 < sourceD u n * sourceR u j := mul_pos hd (by simpa [r] using hr')
        have hpositive : 0 < sourceP u j n - sourceB u j n := by
          rw [hdiff]
          exact div_pos (mul_pos hu' (by simpa [M, K, d, r, N, J] using hnum)) hden
        linarith
    · have hnEq : n = 2 := by omega
      have hjEq : j = 1 := by omega
      subst n
      subst j
      have hrem := source_boundary_two_formula u hd.ne' (by simpa [r] using hr'.ne')
      have hden : 0 < sourceD u 2 ^ 2 * sourceR u 1 := by positivity
      have hrem0 : 0 ≤ 8 * u ^ 2 * (1 + 12 * u) /
          (sourceD u 2 ^ 2 * sourceR u 1) := by positivity
      nlinarith
  · intro hBP
    by_cases hn3 : 3 ≤ n
    · have hcore := source_common_product_core u n j hu hn3 hj1 hjn hd hE1
      have hformula := source_product_diff_formula u n j hd.ne' hr'.ne'
      have hnum0 : 0 ≤
          (((N * (N + 1) - 2 * (J + 1) * d) *
              (N * (N + 1) - J * (J + 1)) * d) -
            J * (J + 2) ^ 2 * r) := by
        simpa [N, J, d, r] using sub_nonneg.mpr hcore
      have hden : 0 < sourceD u n ^ 3 * sourceR u j := by positivity
      have hfrac0 : 0 ≤ u ^ 2 *
          ((((n : ℝ) * ((n : ℝ) + 1) -
                2 * ((j : ℝ) + 1) * sourceD u n) *
              ((n : ℝ) * ((n : ℝ) + 1) -
                (j : ℝ) * ((j : ℝ) + 1)) * sourceD u n) -
            (j : ℝ) * ((j : ℝ) + 2) ^ 2 * sourceR u j) /
          (sourceD u n ^ 3 * sourceR u j) := by
        apply div_nonneg
        · exact mul_nonneg (sq_nonneg u) (by simpa [N, J, d, r] using hnum0)
        · exact hden.le
      exact sub_nonneg.mp (by rw [hformula]; exact hfrac0)
    · have hnEq : n = 2 := by omega
      have hjEq : j = 1 := by omega
      subst n
      subst j
      have hru : 0 < sourceR u 1 := by simpa [r] using hr'
      have hdiff := sourceP_sub_B_two_formula u hd.ne' hru.ne'
      have hden : 0 < sourceD u 2 * sourceR u 1 := mul_pos hd hru
      have hnumpos : 0 < u * (36 * u - 1) := by
        have hpos : 0 < sourceP u 1 2 - sourceB u 1 2 := by linarith
        rw [hdiff] at hpos
        rcases div_pos_iff.mp hpos with hgood | hbad
        · exact hgood.1
        · exfalso
          linarith [hbad.2, hden]
      have hu36 : 1 < 36 * u := by
        rcases (mul_pos_iff.mp hnumpos) with h | h
        · linarith
        · linarith
      have hu12 : 12 * u < 1 := by
        have h := hE1
        dsimp [sourceE] at h
        rw [div_lt_one hd] at h
        dsimp [sourceD] at h
        norm_num [Nat.rawCast] at h
        nlinarith
      have hpoly : 576 * u ^ 2 - 84 * u + 1 ≤ 0 := by
        have hprod : 0 ≤ u * (1 - 12 * u) :=
          mul_nonneg hu (by linarith)
        nlinarith
      have hformula := source_product_two_formula u hd.ne' hru.ne'
      have hden2 : 0 < sourceD u 2 ^ 3 * sourceR u 1 := by positivity
      have hfrac0 : 0 ≤
          -(u ^ 2 * (576 * u ^ 2 - 84 * u + 1)) /
            (sourceD u 2 ^ 3 * sourceR u 1) := by
        apply div_nonneg
        · nlinarith [sq_nonneg u]
        · exact hden2.le
      exact sub_nonneg.mp (by rw [hformula]; exact hfrac0)

/-- Exact bordered perturbation decomposition with a geometric-mean border
    term.  This is the non-AM--GM form needed at the source constant. -/
private lemma bordered_perturbation_floor_sqrt (m : ℕ)
    (Gint : Fin m → Fin m → ℝ) (gb : Fin m → ℝ)
    (Bint : Fin m → Fin m → ℝ) (bb a : Fin m → ℝ)
    (ajj t : ℝ) (y : Fin m → ℝ) (I B C lam : ℝ)
    (hgram : (∑ i : Fin m, ∑ l : Fin m, y i * Gint i l * y l) +
      2 * (∑ i : Fin m, y i * gb i) + t = 0)
    (hint : |∑ i : Fin m, ∑ l : Fin m,
      y i * (Gint i l - Bint i l) * y l| ≤
      I * (∑ i : Fin m, a i * y i ^ 2))
    (hbord : |2 * ∑ i : Fin m, y i * (gb i - bb i)| ≤
      2 * B * Real.sqrt t *
        (Real.sqrt C * Real.sqrt (∑ i : Fin m, a i * y i ^ 2)))
    (hfloor : lam * ((∑ i : Fin m, a i * y i ^ 2) + ajj) ≤
      (∑ i : Fin m, ∑ l : Fin m, y i * Bint i l * y l) +
      2 * (∑ i : Fin m, y i * bb i) + ajj) :
    lam * ((∑ i : Fin m, a i * y i ^ 2) + ajj) ≤
      ajj - t + I * (∑ i : Fin m, a i * y i ^ 2) +
        2 * B * Real.sqrt t *
          (Real.sqrt C * Real.sqrt (∑ i : Fin m, a i * y i ^ 2)) := by
  have hdecomp : (∑ i : Fin m, ∑ l : Fin m, y i * Bint i l * y l) +
      2 * (∑ i : Fin m, y i * bb i) + ajj =
      -(∑ i : Fin m, ∑ l : Fin m,
        y i * (Gint i l - Bint i l) * y l) -
      2 * (∑ i : Fin m, y i * (gb i - bb i)) + (ajj - t) := by
    have hsplitI : ∑ i : Fin m, ∑ l : Fin m,
        y i * (Gint i l - Bint i l) * y l =
        (∑ i : Fin m, ∑ l : Fin m, y i * Gint i l * y l) -
          ∑ i : Fin m, ∑ l : Fin m, y i * Bint i l * y l := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    have hsplitB : ∑ i : Fin m, y i * (gb i - bb i) =
        (∑ i : Fin m, y i * gb i) - ∑ i : Fin m, y i * bb i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplitI, hsplitB]
    linarith [hgram]
  have hf := hfloor
  rw [hdecomp] at hf
  have hi := abs_le.mp hint
  have hb := abs_le.mp hbord
  linarith [hi.1, hi.2, hb.1, hb.2]

/-- If `Uy = -c` and every column of `U` has weighted square norm bounded
    by `a_i/d`, then the solved border has mass at most `(m/d) W`. -/
private lemma solved_border_mass_le (m : ℕ)
    (U : Fin m → Fin m → ℝ) (c y a : Fin m → ℝ) (d : ℝ)
    (hd : 0 < d)
    (hy : ∀ p : Fin m, ∑ i : Fin m, U p i * y i = -(c p))
    (hcol : ∀ i : Fin m,
      d * ∑ p : Fin m, U p i ^ 2 ≤ a i) :
    ∑ p : Fin m, c p ^ 2 ≤
      (m : ℝ) / d * ∑ i : Fin m, a i * y i ^ 2 := by
  have hrow : ∀ p : Fin m,
      c p ^ 2 ≤ (m : ℝ) * ∑ i : Fin m, (U p i * y i) ^ 2 := by
    intro p
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Fin m)) (fun _ => (1 : ℝ))
      (fun i => U p i * y i)
    have hsum : ∑ i : Fin m, (1 : ℝ) * (U p i * y i) = -(c p) := by
      simpa only [one_mul] using hy p
    have hones : ∑ _i : Fin m, ((1 : ℝ)) ^ 2 = (m : ℝ) := by simp
    rw [hsum, hones] at hcs
    simpa only [neg_sq] using hcs
  have hsumrow : ∑ p : Fin m, c p ^ 2 ≤
      ∑ p : Fin m, (m : ℝ) * ∑ i : Fin m, (U p i * y i) ^ 2 :=
    Finset.sum_le_sum fun p _ => hrow p
  have hreorder : ∑ p : Fin m, (m : ℝ) *
        ∑ i : Fin m, (U p i * y i) ^ 2 =
      (m : ℝ) * ∑ i : Fin m,
        (∑ p : Fin m, U p i ^ 2) * y i ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hcols : ∀ i : Fin m, ∑ p : Fin m, U p i ^ 2 ≤ a i / d :=
    fun i => (le_div_iff₀ hd).2 (by simpa [mul_comm] using hcol i)
  calc
    ∑ p : Fin m, c p ^ 2
        ≤ ∑ p : Fin m, (m : ℝ) *
            ∑ i : Fin m, (U p i * y i) ^ 2 := hsumrow
    _ = (m : ℝ) * ∑ i : Fin m,
          (∑ p : Fin m, U p i ^ 2) * y i ^ 2 := hreorder
    _ ≤ (m : ℝ) * ∑ i : Fin m, (a i / d) * y i ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (hcols i) (sq_nonneg _)
    _ = (m : ℝ) / d * ∑ i : Fin m, a i * y i ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      field_simp [hd.ne'] <;> ring

/-- The source common denominator is positive exactly under the usual
    `γ_{n+1} < 1` hypothesis. -/
private lemma sourceD_pos_of_gamma_lt_one (fp : FPModel) (n : ℕ)
    (hn1 : gammaValid fp (n + 1)) (hγ1 : gamma fp (n + 1) < 1) :
    0 < sourceD fp.u n := by
  have hbase : 0 < 1 - ((n : ℝ) + 1) * fp.u := by
    have h := hn1
    unfold gammaValid at h
    push_cast at h
    nlinarith
  have h := hγ1
  unfold gamma at h
  push_cast at h
  rw [div_lt_one hbase] at h
  dsimp [sourceD]
  nlinarith

/-- Every earlier stage reciprocal is bounded by the final source common
    denominator. -/
private lemma source_stage_recip_le (fp : FPModel) {n : ℕ}
    (j : Fin n) (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1) :
    1 / (1 - gamma fp (j.val + 1)) ≤ 1 / sourceD fp.u n := by
  have hmvalid : gammaValid fp (j.val + 1) :=
    gammaValid_mono fp (by omega) hn1
  have hmγ1 : gamma fp (j.val + 1) < 1 :=
    lt_of_le_of_lt (gamma_mono fp (by omega) hn1) hγ1
  rw [one_div_one_sub_gamma_eq fp (j.val + 1) hmvalid hmγ1]
  simp only [Nat.cast_add, Nat.cast_one]
  let dm : ℝ := 1 - 2 * ((j.val : ℝ) + 1) * fp.u
  let d : ℝ := sourceD fp.u n
  have hd : 0 < d := by simpa [d] using sourceD_pos_of_gamma_lt_one fp n hn1 hγ1
  have hdm : 0 < dm := by
    have h := hmγ1
    have hv : 0 < 1 - ((j.val : ℝ) + 1) * fp.u := by
      have h' := hmvalid
      unfold gammaValid at h'
      push_cast at h'
      nlinarith
    unfold gamma at h
    push_cast at h
    rw [div_lt_one hv] at h
    dsimp [dm]
    nlinarith
  have hdle : d ≤ dm := by
    dsimp [d, dm, sourceD]
    have hj : (j.val : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      exact_mod_cast (show j.val + 1 ≤ n + 1 by omega)
    nlinarith [mul_le_mul_of_nonneg_right hj fp.u_nonneg]
  change (1 - ((j.val : ℝ) + 1) * fp.u) / dm ≤ 1 / d
  calc
    (1 - ((j.val : ℝ) + 1) * fp.u) / dm ≤ 1 / dm := by
      exact div_le_div_of_nonneg_right (by
        nlinarith [mul_nonneg (by positivity : 0 ≤ (j.val : ℝ) + 1)
          fp.u_nonneg]) hdm.le
    _ ≤ 1 / d := one_div_le_one_div_of_le hd hdle

/-- Native stage interior mass is no larger than its common-denominator
    coefficient `sourceI`. -/
private lemma source_stage_interior_coeff_le (fp : FPModel) {n : ℕ}
    (j : Fin n) (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1) :
    gamma fp (j.val + 1) / (1 - gamma fp (j.val + 1)) * (j.val : ℝ) ≤
      sourceI fp.u j.val n := by
  have hmvalid : gammaValid fp (j.val + 1) :=
    gammaValid_mono fp (by omega) hn1
  have hmγ1 : gamma fp (j.val + 1) < 1 :=
    lt_of_le_of_lt (gamma_mono fp (by omega) hn1) hγ1
  rw [gamma_div_one_sub_gamma_eq fp (j.val + 1) hmvalid hmγ1]
  simp only [Nat.cast_add, Nat.cast_one]
  let dm : ℝ := 1 - 2 * ((j.val : ℝ) + 1) * fp.u
  let d : ℝ := sourceD fp.u n
  have hd : 0 < d := by simpa [d] using sourceD_pos_of_gamma_lt_one fp n hn1 hγ1
  have hdm : 0 < dm := by
    have h := hmγ1
    have hv : 0 < 1 - ((j.val : ℝ) + 1) * fp.u := by
      have h' := hmvalid
      unfold gammaValid at h'
      push_cast at h'
      nlinarith
    unfold gamma at h
    push_cast at h
    rw [div_lt_one hv] at h
    dsimp [dm]
    nlinarith
  have hdle : d ≤ dm := by
    dsimp [d, dm, sourceD]
    have hj : (j.val : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      exact_mod_cast (show j.val + 1 ≤ n + 1 by omega)
    nlinarith [mul_le_mul_of_nonneg_right hj fp.u_nonneg]
  have hnum : 0 ≤ (j.val : ℝ) * ((j.val : ℝ) + 1) * fp.u :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) fp.u_nonneg
  have hdiv : (j.val : ℝ) * ((j.val : ℝ) + 1) * fp.u / dm ≤
      (j.val : ℝ) * ((j.val : ℝ) + 1) * fp.u / d :=
    div_le_div₀ hnum le_rfl hd hdle
  dsimp [sourceI, d, dm] at *
  convert hdiv using 1 <;> ring

set_option maxHeartbeats 1800000 in
/-- Source-strength stage step for the concrete Algorithm 10.2 run.  Unlike
    the older sharp wrapper, this retains the stage-local raw-pivot ratio and
    the geometric-mean border defect through the scalar endgame. -/
theorem higham10_7_fl_cholesky_pivot_pos_source_step (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i l : Fin n, A i l = A l i)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1)
    (hn2 : 2 ≤ n) (j : Fin n) (hj1 : 1 ≤ j.val)
    (IH : ∀ l : Fin n, l.val < j.val → 0 < fl_cholPivot fp n A l)
    (lam : ℝ)
    (hfloor : ∀ y : Fin j.val → ℝ,
      lam * ((∑ i : Fin j.val,
          A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) + A j j) ≤
        (∑ i : Fin j.val, ∑ l : Fin j.val,
          y i * A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l) +
        2 * (∑ i : Fin j.val, y i * A ⟨i.val, by omega⟩ j) + A j j)
    (hthresh : sourceE fp.u n < lam) :
    0 < fl_cholPivot fp n A j := by
  by_contra hs
  push_neg at hs
  have hlam1 : lam ≤ 1 := by
    have h0 := hfloor (fun _ => (0 : ℝ))
    norm_num at h0
    exact le_of_mul_le_mul_right
      (by linarith : lam * A j j ≤ 1 * A j j) (hAdiag j)
  have hE1 : sourceE fp.u n < 1 := lt_of_lt_of_le hthresh hlam1
  have hd : 0 < sourceD fp.u n := sourceD_pos_of_gamma_lt_one fp n hn1 hγ1
  obtain ⟨hE0, hI0, hB0, hC0, hr0, hP0, hQ0, hQdef,
      hboundary, hinterior⟩ :=
    source_common_coefficients fp.u n j.val fp.u_nonneg hn2 hj1 j.isLt hd hE1
  have hu : fp.u < 1 := by
    have h := hn1
    unfold gammaValid at h
    push_cast at h
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))
      fp.u_nonneg]
  have hdiag_pos : ∀ i : Fin j.val,
      0 < fl_cholesky fp n A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ := by
    intro i
    rw [fl_cholesky_diag_eq fp n A ⟨i.val, by omega⟩]
    exact fl_sqrt_pos fp hu _ (IH ⟨i.val, by omega⟩ i.isLt)
  set U : Fin j.val → Fin j.val → ℝ := fun p i =>
    fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ with hUdef
  set c : Fin j.val → ℝ := fun p =>
    fl_cholesky fp n A ⟨p.val, by omega⟩ j with hcdef
  obtain ⟨y, hy⟩ := upperTriangular_solve_exists j.val U
    (fun p i hpi => fl_cholesky_strict_lower fp n A _ _ hpi)
    (fun i => (hdiag_pos i).ne') (fun p => -(c p))
  have hgram0 := bordered_gram_zero j.val U c y hy
  set t : ℝ := ∑ p : Fin j.val, c p ^ 2 with htdef
  set W : ℝ := ∑ i : Fin j.val,
    A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2 with hWdef
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun p _ => sq_nonneg _
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i _ =>
    mul_nonneg (hAdiag _).le (sq_nonneg _)
  have hgram : (∑ i : Fin j.val, ∑ l : Fin j.val,
      y i * (∑ p : Fin j.val, U p i * U p l) * y l) +
      2 * (∑ i : Fin j.val, y i * ∑ p : Fin j.val, U p i * c p) + t = 0 := by
    simpa [t] using hgram0
  have hint0 := higham10_7_stage_interior_mass_native fp A hsym hAdiag
    hn1 hγ1 j IH y
  have hIcoeff := source_stage_interior_coeff_le fp j hn1 hγ1
  have hint : |∑ i : Fin j.val, ∑ l : Fin j.val, y i *
      ((∑ p : Fin j.val, U p i * U p l) -
        A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) * y l| ≤
      sourceI fp.u j.val n * W := by
    have hmass := hint0.trans (mul_le_mul_of_nonneg_right hIcoeff hW0)
    simpa [U, W] using hmass
  have hbord0 := higham10_7_stage_border_mass_commonDenom fp A hsym
    hAdiag hn1 hγ1 j IH y
  have hbord : |2 * ∑ i : Fin j.val, y i *
      ((∑ p : Fin j.val, U p i * c p) - A ⟨i.val, by omega⟩ j)| ≤
      2 * sourceB fp.u j.val n * Real.sqrt t *
        (Real.sqrt (sourceC fp.u j.val n) * Real.sqrt W) := by
    simpa [U, c, t, W, sourceB, sourceC, sourceD] using hbord0
  have hfloorG := bordered_perturbation_floor_sqrt j.val
    (fun i l => ∑ p : Fin j.val, U p i * U p l)
    (fun i => ∑ p : Fin j.val, U p i * c p)
    (fun i l => A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩)
    (fun i => A ⟨i.val, by omega⟩ j)
    (fun i => A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩)
    (A j j) t y (sourceI fp.u j.val n) (sourceB fp.u j.val n)
    (sourceC fp.u j.val n) lam hgram hint hbord (hfloor y)
  have hmvalid : gammaValid fp (j.val + 1) :=
    gammaValid_mono fp (by omega) hn1
  have hmγ1 : gamma fp (j.val + 1) < 1 :=
    lt_of_le_of_lt (gamma_mono fp (by omega) hn1) hγ1
  set Am : Fin j.val → Fin j.val → ℝ :=
    fun i l => A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ with hAm
  have hcert : CholeskyBackwardError j.val Am
      (fl_cholesky fp j.val Am) (gamma fp (j.val + 1)) :=
    fl_cholesky_block_certificate fp j.isLt.le A hsym hu hmvalid IH
  have hloc : ∀ p q : Fin j.val,
      fl_cholesky fp j.val Am p q =
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨q.val, by omega⟩ :=
    fun p q => fl_cholesky_leading_principal fp j.isLt.le A p q
  have hcol : ∀ i : Fin j.val,
      (1 - gamma fp (j.val + 1)) * ∑ p : Fin j.val, U p i ^ 2 ≤
        A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ := by
    intro i
    have h := chol_cert_colNormSq_le j.val Am (fl_cholesky fp j.val Am)
      (gamma fp (j.val + 1)) hcert i
    simp only [hloc] at h
    simpa [U] using h
  have htWnative := solved_border_mass_le j.val U c y
    (fun i => A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩)
    (1 - gamma fp (j.val + 1)) (by linarith) hy hcol
  have hrecip := source_stage_recip_le fp j hn1 hγ1
  have hcoefC : (j.val : ℝ) / (1 - gamma fp (j.val + 1)) ≤
      sourceC fp.u j.val n := by
    have hm := mul_le_mul_of_nonneg_left hrecip (Nat.cast_nonneg j.val)
    simpa [sourceC, div_eq_mul_inv] using hm
  have htCW : t ≤ sourceC fp.u j.val n * W := by
    calc
      t ≤ (j.val : ℝ) / (1 - gamma fp (j.val + 1)) * W :=
        by simpa [t, W] using htWnative
      _ ≤ sourceC fp.u j.val n * W :=
        mul_le_mul_of_nonneg_right hcoefC hW0
  set x : ℝ := Real.sqrt t with hxdef
  set z : ℝ := Real.sqrt (sourceC fp.u j.val n) * Real.sqrt W with hzdef
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hx2 : x ^ 2 = t := by dsimp [x]; exact Real.sq_sqrt ht0
  have hz2 : z ^ 2 = sourceC fp.u j.val n * W := by
    dsimp [z]
    rw [mul_pow, Real.sq_sqrt hC0, Real.sq_sqrt hW0]
  have hxz : x ≤ z := by nlinarith
  have hlow := fl_cholSubFold_pivot_lower fp j.val c (A j j) hmvalid
  have hpiv_eq : fl_cholPivot fp n A j =
      fl_cholSubFold fp j.val c c (A j j) := rfl
  have hAj := hAdiag j
  have habsAj : |A j j| = A j j := abs_of_pos hAj
  have hlow2 : A j j - t - gamma fp (j.val + 1) * (A j j + t) ≤
      fl_cholPivot fp n A j := by
    rw [hpiv_eq, htdef]
    simpa [habsAj] using hlow
  have hgm0 : 0 ≤ gamma fp (j.val + 1) := gamma_nonneg fp hmvalid
  have hkey : (1 - gamma fp (j.val + 1)) * A j j ≤
      (1 + gamma fp (j.val + 1)) * t := by nlinarith
  have hdenp : 0 < 1 + gamma fp (j.val + 1) := by linarith
  have hratio : (1 - gamma fp (j.val + 1)) /
      (1 + gamma fp (j.val + 1)) = sourceR fp.u j.val := by
    simpa [sourceR] using one_sub_gamma_div_one_add_gamma_eq fp
      (j.val + 1) hmvalid
  have hrat : ((1 - gamma fp (j.val + 1)) /
      (1 + gamma fp (j.val + 1))) * A j j ≤ t := by
    calc
      ((1 - gamma fp (j.val + 1)) /
          (1 + gamma fp (j.val + 1))) * A j j =
        ((1 - gamma fp (j.val + 1)) * A j j) /
          (1 + gamma fp (j.val + 1)) := by ring
      _ ≤ t := (div_le_iff₀ hdenp).2 (by nlinarith)
  have hrt : sourceR fp.u j.val * A j j ≤ t := by
    rw [← hratio]
    exact hrat
  have hfac0 : 0 ≤ (1 - sourceE fp.u n) / sourceR fp.u j.val :=
    div_nonneg (by linarith) hr0.le
  have hmul := mul_le_mul_of_nonneg_left hrt hfac0
  have hcancel : ((1 - sourceE fp.u n) / sourceR fp.u j.val) *
      (sourceR fp.u j.val * A j j) = (1 - sourceE fp.u n) * A j j := by
    field_simp [hr0.ne']
  rw [hcancel] at hmul
  have hshift : sourceP fp.u j.val n * t ≤
      (sourceE fp.u n - 1) * A j j + t := by
    dsimp [sourceP]
    nlinarith
  have hscalar := signedBorder_source_endgame (A j j) W t
    (sourceE fp.u n) (sourceI fp.u j.val n) (sourceP fp.u j.val n)
    (sourceQ fp.u j.val n) (sourceB fp.u j.val n)
    (sourceC fp.u j.val n) x z hW0 ht0 hP0 hQ0 hB0 hC0 hx0 hz0 hxz
    hx2 hz2 hQdef hshift hboundary hinterior
  have hfloorG' : lam * (W + A j j) ≤
      A j j - t + sourceI fp.u j.val n * W +
        2 * sourceB fp.u j.val n * x * z := by
    simpa [W, x, z, mul_assoc] using hfloorG
  have hmasspos : 0 < A j j + W := by linarith
  nlinarith [hfloorG', hscalar]

/-- **Theorem 10.7 (Demmel), exact source threshold for the concrete
    Algorithm 10.2 run** (Higham, p. 200).  If
    `λ_min(D⁻¹AD⁻¹) > n γ_{n+1}/(1-γ_{n+1})`, every raw rounded
    Cholesky pivot is positive.  No run-level or stage-level certificate is
    assumed: all defect bounds are constructed from the preceding pivots. -/
theorem higham10_7_fl_cholesky_success_source (fp : FPModel) (n : ℕ)
    (hn0 : 0 < n) (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i l : Fin n, A i l = A l i)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1)
    (hH_sym : IsSymmetricFiniteMatrix (fun i l : Fin n =>
      A i l / (Real.sqrt (A i i) * Real.sqrt (A l l))))
    (hthresh : (n : ℝ) *
      (gamma fp (n + 1) / (1 - gamma fp (n + 1))) <
      finiteMinEigenvalue hn0 (fun i l : Fin n =>
        A i l / (Real.sqrt (A i i) * Real.sqrt (A l l))) hH_sym) :
    ∀ j : Fin n, 0 < fl_cholPivot fp n A j := by
  let lam : ℝ := finiteMinEigenvalue hn0 (fun i l : Fin n =>
    A i l / (Real.sqrt (A i i) * Real.sqrt (A l l))) hH_sym
  have hEeq : sourceE fp.u n = (n : ℝ) *
      (gamma fp (n + 1) / (1 - gamma fp (n + 1))) := by
    rw [gamma_div_one_sub_gamma_eq fp (n + 1) hn1 hγ1]
    simp only [Nat.cast_add, Nat.cast_one]
    dsimp [sourceE, sourceD]
    ring
  have hElam : sourceE fp.u n < lam := by
    rw [hEeq]
    exact hthresh
  have H : ∀ k : ℕ, ∀ j : Fin n, j.val = k →
      0 < fl_cholPivot fp n A j := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k IHk =>
      intro j hj
      by_cases hj0 : j.val = 0
      · have hjeq : j = ⟨0, hn0⟩ := Fin.ext hj0
        subst j
        simpa [fl_cholPivot, fl_cholSubFold] using hAdiag ⟨0, hn0⟩
      · have hj1 : 1 ≤ j.val := by omega
        have hn2 : 2 ≤ n := by omega
        have IH : ∀ l : Fin n, l.val < j.val →
            0 < fl_cholPivot fp n A l :=
          fun l hl => IHk l.val (hj ▸ hl) l rfl
        refine higham10_7_fl_cholesky_pivot_pos_source_step fp A hsym
          hAdiag hn1 hγ1 hn2 j hj1 IH lam ?_ hElam
        intro y
        exact min_eig_scaled_bordered_floor n hn0 A hsym hAdiag hH_sym j y
  exact fun j => H j.val j rfl

/-- Terminal source-facing closure of Theorem 10.7: Algorithm 10.2 succeeds
    at Demmel's printed threshold and its computed upper-triangular factor is
    nonsingular (expressed by a unit determinant). -/
theorem higham10_7_actual_algorithm_source_closed (fp : FPModel) (n : ℕ)
    (hn0 : 0 < n) (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i l : Fin n, A i l = A l i)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1)
    (hH_sym : IsSymmetricFiniteMatrix (fun i l : Fin n =>
      A i l / (Real.sqrt (A i i) * Real.sqrt (A l l))))
    (hthresh : (n : ℝ) *
      (gamma fp (n + 1) / (1 - gamma fp (n + 1))) <
      finiteMinEigenvalue hn0 (fun i l : Fin n =>
        A i l / (Real.sqrt (A i i) * Real.sqrt (A l l))) hH_sym) :
    (∀ j : Fin n, 0 < fl_cholPivot fp n A j) ∧
      IsUnit (Matrix.det (Matrix.of (fl_cholesky fp n A))) := by
  have hpiv := higham10_7_fl_cholesky_success_source fp n hn0 A hsym
    hAdiag hn1 hγ1 hH_sym hthresh
  refine ⟨hpiv, ?_⟩
  have hu : fp.u < 1 := by
    have h := hn1
    unfold gammaValid at h
    push_cast at h
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))
      fp.u_nonneg]
  have hdiag : ∀ i : Fin n, fl_cholesky fp n A i i ≠ 0 := by
    intro i
    rw [fl_cholesky_diag_eq fp n A i]
    exact (fl_sqrt_pos fp hu _ (hpiv i)).ne'
  let R : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fl_cholesky fp n A)
  have hBT : R.BlockTriangular id := fun i j hij =>
    fl_cholesky_strict_lower fp n A i j hij
  change IsUnit R.det
  rw [Matrix.det_of_upperTriangular hBT]
  exact isUnit_iff_ne_zero.mpr
    (Finset.prod_ne_zero_iff.mpr fun i _ => hdiag i)

end NumStability
