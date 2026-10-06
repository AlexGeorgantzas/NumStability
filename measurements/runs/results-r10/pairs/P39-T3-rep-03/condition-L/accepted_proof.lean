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
  dsimp only
  let r : ℕ → ℝ := p39ResidualRatio residual
  let D : ℝ := 1 / (2 * r 0)
  let q : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ (2 ^ k)
  have hrpos : ∀ k, 0 < r k := by
    intro k
    exact div_pos (hpos (k + 1)) (hpos k)
  have hr0 : 0 < r 0 := hrpos 0
  have hcpos : 0 < B * residual 0 := mul_pos hB (hpos 0)
  have htwo_r0_lt : 2 * r 0 < 1 := by
    linarith
  have hD : 1 < D := by
    dsimp [D]
    exact (lt_div_iff₀ (by positivity : 0 < 2 * r 0)).2 (by simpa using htwo_r0_lt)
  have hDr0 : D * r 0 = 1 / 2 := by
    dsimp [D]
    field_simp
  have hqpos : ∀ k, 0 < q k := by
    intro k
    exact pow_pos (by norm_num) _
  have hqsq : ∀ k, q k ^ 2 = q (k + 1) := by
    intro k
    dsimp [q]
    rw [← pow_mul]
    congr 1
  have hratio_step : ∀ k, r (k + 1) ≤ r k ^ 2 + B * residual (k + 1) := by
    intro k
    have hk := hstep k
    dsimp [r, p39ResidualRatio] at ⊢ hk
    apply (div_le_iff₀ (hpos (k + 1))).2
    simpa [add_assoc] using hk
  have hbounds : ∀ k,
      D * r k ≤ q k ∧
      D * residual (k + 1) ≤ 2 * residual 0 * q (k + 1) := by
    intro k
    induction k with
    | zero =>
        constructor
        · simpa [q] using hDr0.le
        · have hres : r 0 * residual 0 = residual 1 := by
            dsimp [r, p39ResidualRatio]
            exact div_mul_cancel₀ _ (ne_of_gt (hpos 0))
          rw [← hres, ← mul_assoc, hDr0]
          norm_num [q]
          nlinarith
    | succ k ih =>
        have hDpos : 0 < D := lt_trans zero_lt_one hD
        have hDone : 0 < 1 / D := one_div_pos.mpr hDpos
        have hbeta_nonneg : 0 ≤ D * r k := (mul_pos hDpos (hrpos k)).le
        have hbeta_sq : (D * r k) ^ 2 ≤ q k ^ 2 := by
          nlinarith [ih.1, hbeta_nonneg, (hqpos k).le]
        have hfirst : D * r (k + 1) ≤ q (k + 1) := by
          calc
            D * r (k + 1)
                ≤ D * (r k ^ 2 + B * residual (k + 1)) :=
                  mul_le_mul_of_nonneg_left (hratio_step k) hDpos.le
            _ = (1 / D) * (D * r k) ^ 2 + B * (D * residual (k + 1)) := by
                  field_simp
                  <;> ring
            _ ≤ (1 / D) * q k ^ 2 + B * (2 * residual 0 * q (k + 1)) := by
                  exact add_le_add
                    (mul_le_mul_of_nonneg_left hbeta_sq hDone.le)
                    (mul_le_mul_of_nonneg_left ih.2 hB.le)
            _ = q (k + 1) * (2 * r 0 + 2 * B * residual 0) := by
                  rw [hqsq k]
                  have hDinv : 1 / D = 2 * r 0 := by
                    dsimp [D]
                    field_simp
                  rw [hDinv]
                  ring
            _ ≤ q (k + 1) := by
                  nlinarith [hqpos (k + 1)]
        constructor
        · simpa [Nat.succ_eq_add_one] using hfirst
        · have hres : r (k + 1) * residual (k + 1) = residual (k + 2) := by
            dsimp [r, p39ResidualRatio]
            simpa [Nat.add_assoc] using
              (div_mul_cancel₀ (residual (k + 2)) (ne_of_gt (hpos (k + 1))))
          calc
            D * residual (k + 2)
                = D * (r (k + 1) * residual (k + 1)) := by rw [hres]
            _ = (D * r (k + 1)) * residual (k + 1) := by ring
            _ ≤ q (k + 1) * residual (k + 1) :=
                  mul_le_mul_of_nonneg_right hfirst (hpos (k + 1)).le
            _ ≤ q (k + 1) * (D * residual (k + 1)) := by
                  apply mul_le_mul_of_nonneg_left _ (hqpos (k + 1)).le
                  nlinarith [hpos (k + 1)]
            _ ≤ q (k + 1) * (2 * residual 0 * q (k + 1)) := by
                  exact mul_le_mul_of_nonneg_left ih.2 (hqpos (k + 1)).le
            _ = 2 * residual 0 * q (k + 2) := by
                  rw [← hqsq (k + 1)]
                  ring
  refine ⟨hD, ?_, ?_, ?_⟩
  · simpa [p39ScaledResidualRatio, D, r] using hDr0
  · intro k
    constructor
    · exact mul_pos (lt_trans zero_lt_one hD) (hrpos k)
    · simpa [p39ScaledResidualRatio, D, r, q] using (hbounds k).1
  · have hq_tendsto : Tendsto q atTop (nhds 0) := by
      have hexponents : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        hexponents
    refine squeeze_zero (g := q) ?_ ?_ hq_tendsto
    · intro k
      exact (mul_pos (lt_trans zero_lt_one hD) (hrpos k)).le
    · intro k
      simpa [p39ScaledResidualRatio, D, r, q] using (hbounds k).1

end HighamBench
