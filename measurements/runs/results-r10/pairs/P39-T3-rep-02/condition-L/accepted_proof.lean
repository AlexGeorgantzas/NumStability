import HighamBench.P39Definitions

namespace HighamBench

open Filter

/-- P39-T3: the R-quadratic residual-ratio core of Theorem 2.3. -/
theorem p39_t3_choice_two_r_quadratic_core
    (residual : ℕ → ℝ) (B : ℝ)
    (hpos : ∀ k, 0 < residual k) (hB : 0 < B)
    (hstep : ∀ k,
      residual (k + 2) ≤
        ((p39ResidualRatio residual k) ^ 2 + B * residual (k + 1)) *
          residual (k + 1))
    (hsmall :
      2 * p39ResidualRatio residual 0 + 2 * B * residual 0 ≤ 1) :
    let D := 1 / (2 * p39ResidualRatio residual 0)
    1 < D ∧
      p39ScaledResidualRatio residual D 0 = 1 / 2 ∧
      (∀ k,
        0 < p39ScaledResidualRatio residual D k ∧
        p39ScaledResidualRatio residual D k ≤ (1 / 2 : ℝ) ^ (2 ^ k)) ∧
      Tendsto (p39ScaledResidualRatio residual D) atTop (nhds 0) := by
  -- PROOF_START P39-T3-H001
  let D : ℝ := 1 / (2 * p39ResidualRatio residual 0)
  let beta : ℕ → ℝ := p39ScaledResidualRatio residual D
  let Q : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ (2 ^ k)
  change 1 < D ∧ beta 0 = 1 / 2 ∧
    (∀ k, 0 < beta k ∧ beta k ≤ Q k) ∧ Tendsto beta atTop (nhds 0)

  have hratio_pos (k : ℕ) : 0 < p39ResidualRatio residual k := by
    exact div_pos (hpos (k + 1)) (hpos k)
  have hden_pos : 0 < 2 * p39ResidualRatio residual 0 := by
    exact mul_pos (by norm_num) (hratio_pos 0)
  have hden_lt : 2 * p39ResidualRatio residual 0 < 1 := by
    have hstrict :
        2 * p39ResidualRatio residual 0 <
          2 * p39ResidualRatio residual 0 + 2 * B * residual 0 := by
      have : 0 < 2 * B * residual 0 :=
        mul_pos (mul_pos (by norm_num) hB) (hpos 0)
      linarith
    exact hstrict.trans_le hsmall
  have hD : 1 < D := by
    dsimp [D]
    exact (one_lt_div hden_pos).2 hden_lt
  have hD_pos : 0 < D := lt_trans (by norm_num) hD
  have hD_ne : D ≠ 0 := ne_of_gt hD_pos
  have hD_inv : 1 / D = 2 * p39ResidualRatio residual 0 := by
    dsimp [D]
    field_simp
  have hcoefficient : 1 / D + 2 * B * residual 0 ≤ 1 := by
    rw [hD_inv]
    exact hsmall

  have hbeta_pos (k : ℕ) : 0 < beta k := by
    exact mul_pos hD_pos (hratio_pos k)
  have hQ_nonneg (k : ℕ) : 0 ≤ Q k := by
    positivity
  have hQ_succ (k : ℕ) : Q (k + 1) = (Q k) ^ 2 := by
    simp [Q, pow_succ, pow_mul]

  have hbeta_zero : beta 0 = 1 / 2 := by
    dsimp [beta, p39ScaledResidualRatio, D]
    field_simp [ne_of_gt (hratio_pos 0)]
  have hratio_step (k : ℕ) :
      p39ResidualRatio residual (k + 1) ≤
        (p39ResidualRatio residual k) ^ 2 + B * residual (k + 1) := by
    apply (div_le_iff₀ (hpos (k + 1))).2
    simpa [p39ResidualRatio, Nat.add_assoc] using hstep k
  have hresidual_ratio (k : ℕ) :
      residual (k + 1) = p39ResidualRatio residual k * residual k := by
    rw [p39ResidualRatio]
    field_simp [ne_of_gt (hpos k)]

  have hbounds : ∀ k : ℕ,
      beta k ≤ Q k ∧
        residual (k + 1) ≤ 2 * residual 0 * Q (k + 1) / D := by
    intro k
    induction k with
    | zero =>
        constructor
        · simpa [Q] using le_of_eq hbeta_zero
        · rw [hresidual_ratio 0]
          dsimp [Q, beta, p39ScaledResidualRatio, D] at hbeta_zero ⊢
          field_simp [ne_of_gt (hratio_pos 0)] at hbeta_zero ⊢
          nlinarith
    | succ k ih =>
        have hbeta_rec :
            beta (k + 1) ≤
              (beta k) ^ 2 / D + D * B * residual (k + 1) := by
          calc
            beta (k + 1) = D * p39ResidualRatio residual (k + 1) := rfl
            _ ≤ D * ((p39ResidualRatio residual k) ^ 2 +
                B * residual (k + 1)) :=
              mul_le_mul_of_nonneg_left (hratio_step k) (le_of_lt hD_pos)
            _ = (beta k) ^ 2 / D + D * B * residual (k + 1) := by
              dsimp [beta, p39ScaledResidualRatio]
              field_simp [hD_ne]
        have hsquare : (beta k) ^ 2 ≤ (Q k) ^ 2 := by
          nlinarith [hbeta_pos k, hQ_nonneg k]
        have hsquare_div : (beta k) ^ 2 / D ≤ Q (k + 1) / D := by
          rw [hQ_succ]
          exact div_le_div_of_nonneg_right hsquare (le_of_lt hD_pos)
        have hresidual_term :
            D * B * residual (k + 1) ≤
              2 * B * residual 0 * Q (k + 1) := by
          calc
            D * B * residual (k + 1) ≤
                D * B * (2 * residual 0 * Q (k + 1) / D) := by
              exact mul_le_mul_of_nonneg_left ih.2 (by positivity)
            _ = 2 * B * residual 0 * Q (k + 1) := by
              field_simp [hD_ne]
        have hbeta_next : beta (k + 1) ≤ Q (k + 1) := by
          calc
            beta (k + 1) ≤
                (beta k) ^ 2 / D + D * B * residual (k + 1) := hbeta_rec
            _ ≤ Q (k + 1) / D +
                2 * B * residual 0 * Q (k + 1) :=
              add_le_add hsquare_div hresidual_term
            _ = (1 / D + 2 * B * residual 0) * Q (k + 1) := by ring
            _ ≤ 1 * Q (k + 1) :=
              mul_le_mul_of_nonneg_right hcoefficient (hQ_nonneg (k + 1))
            _ = Q (k + 1) := one_mul _
        constructor
        · exact hbeta_next
        · rw [hresidual_ratio (k + 1)]
          have hratio_upper :
              p39ResidualRatio residual (k + 1) ≤ Q (k + 1) := by
            have hratio_le_beta :
                p39ResidualRatio residual (k + 1) ≤ beta (k + 1) := by
              dsimp [beta, p39ScaledResidualRatio]
              nlinarith [hratio_pos (k + 1)]
            exact hratio_le_beta.trans hbeta_next
          calc
            p39ResidualRatio residual (k + 1) * residual (k + 1) ≤
                Q (k + 1) * (2 * residual 0 * Q (k + 1) / D) := by
              exact mul_le_mul hratio_upper ih.2 (le_of_lt (hpos (k + 1)))
                (hQ_nonneg (k + 1))
            _ = 2 * residual 0 * Q (k + 2) / D := by
              rw [hQ_succ (k + 1)]
              ring

  refine ⟨hD, hbeta_zero, ?_, ?_⟩
  · intro k
    exact ⟨hbeta_pos k, (hbounds k).1⟩
  · have hgeom : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds 0) := by
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hexponent : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop := by
      exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have hQ_tendsto : Tendsto Q atTop (nhds 0) := by
      exact hgeom.comp hexponent
    exact squeeze_zero (fun k => le_of_lt (hbeta_pos k))
      (fun k => (hbounds k).1) hQ_tendsto

end HighamBench
