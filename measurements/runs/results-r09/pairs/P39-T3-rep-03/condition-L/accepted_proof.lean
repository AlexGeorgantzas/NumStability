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
  let q : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ (2 ^ k)
  have hratio_pos (k : ℕ) : 0 < p39ResidualRatio residual k := by
    rw [p39ResidualRatio]
    exact div_pos (hpos (k + 1)) (hpos k)
  have htwo_ratio_pos : 0 < 2 * p39ResidualRatio residual 0 := by
    exact mul_pos (by norm_num) (hratio_pos 0)
  have htwo_ratio_lt_one : 2 * p39ResidualRatio residual 0 < 1 := by
    have hBr_pos : 0 < 2 * B * residual 0 := by
      exact mul_pos (mul_pos (by norm_num) hB) (hpos 0)
    linarith
  have hD_pos : 0 < D := by
    dsimp [D]
    positivity
  have hD : 1 < D := by
    dsimp [D]
    exact one_lt_one_div htwo_ratio_pos htwo_ratio_lt_one
  have hD_ne : D ≠ 0 := ne_of_gt hD_pos
  have hD_nonneg : 0 ≤ D := le_of_lt hD_pos
  have hD_inv_le_one : 1 / D ≤ 1 := by
    exact (div_le_one hD_pos).2 (le_of_lt hD)
  have hinvD : 1 / D = 2 * p39ResidualRatio residual 0 := by
    dsimp [D]
    field_simp
  have hcoef : 1 / D + 2 * B * residual 0 ≤ 1 := by
    rw [hinvD]
    exact hsmall
  have hratio_mul (k : ℕ) :
      p39ResidualRatio residual k * residual k = residual (k + 1) := by
    rw [p39ResidualRatio]
    field_simp [ne_of_gt (hpos k)]
  have hratio_step (k : ℕ) :
      p39ResidualRatio residual (k + 1) ≤
        (p39ResidualRatio residual k) ^ 2 + B * residual (k + 1) := by
    rw [p39ResidualRatio]
    apply (div_le_iff₀ (hpos (k + 1))).2
    simpa [p39ResidualRatio, Nat.add_assoc] using hstep k
  have hscaled_step (k : ℕ) :
      p39ScaledResidualRatio residual D (k + 1) ≤
        (p39ScaledResidualRatio residual D k) ^ 2 / D +
          D * B * residual (k + 1) := by
    calc
      p39ScaledResidualRatio residual D (k + 1) =
          D * p39ResidualRatio residual (k + 1) := rfl
      _ ≤ D * ((p39ResidualRatio residual k) ^ 2 +
          B * residual (k + 1)) :=
        mul_le_mul_of_nonneg_left (hratio_step k) hD_nonneg
      _ = (p39ScaledResidualRatio residual D k) ^ 2 / D +
          D * B * residual (k + 1) := by
        rw [p39ScaledResidualRatio]
        field_simp
        <;> ring
  have hscaled_pos (k : ℕ) :
      0 < p39ScaledResidualRatio residual D k := by
    rw [p39ScaledResidualRatio]
    exact mul_pos hD_pos (hratio_pos k)
  have hq_pos (k : ℕ) : 0 < q k := by
    dsimp [q]
    positivity
  have hq_succ (k : ℕ) : q (k + 1) = (q k) ^ 2 := by
    dsimp [q]
    rw [pow_succ, pow_mul]
  have hscaled_zero : p39ScaledResidualRatio residual D 0 = 1 / 2 := by
    rw [p39ScaledResidualRatio]
    dsimp [D]
    field_simp [ne_of_gt (hratio_pos 0)]
  have hmain : ∀ k : ℕ,
      p39ScaledResidualRatio residual D k ≤ q k ∧
        residual (k + 1) ≤ 2 * residual 0 * q (k + 1) / D := by
    intro k
    induction k with
    | zero =>
        constructor
        · rw [hscaled_zero]
          norm_num [q]
        · rw [← hratio_mul 0]
          apply (le_div_iff₀ hD_pos).2
          rw [show p39ResidualRatio residual 0 * residual 0 * D =
              residual 0 * (D * p39ResidualRatio residual 0) by ring]
          rw [← p39ScaledResidualRatio]
          rw [hscaled_zero]
          norm_num [q]
          ring_nf
          exact le_rfl
    | succ k ih =>
        have hsq :
            (p39ScaledResidualRatio residual D k) ^ 2 ≤ (q k) ^ 2 := by
          nlinarith [hscaled_pos k, hq_pos k]
        have hfirst :
            (p39ScaledResidualRatio residual D k) ^ 2 / D ≤
              (q k) ^ 2 / D := by
          exact div_le_div_of_nonneg_right hsq hD_nonneg
        have hsecond :
            D * B * residual (k + 1) ≤
              D * B * (2 * residual 0 * q (k + 1) / D) := by
          exact mul_le_mul_of_nonneg_left ih.2 (mul_nonneg hD_nonneg (le_of_lt hB))
        have hnext : p39ScaledResidualRatio residual D (k + 1) ≤ q (k + 1) := by
          calc
            p39ScaledResidualRatio residual D (k + 1) ≤
                (p39ScaledResidualRatio residual D k) ^ 2 / D +
                  D * B * residual (k + 1) := hscaled_step k
            _ ≤ (q k) ^ 2 / D +
                  D * B * (2 * residual 0 * q (k + 1) / D) :=
              add_le_add hfirst hsecond
            _ = q (k + 1) * (1 / D + 2 * B * residual 0) := by
              rw [hq_succ k]
              field_simp
              <;> ring
            _ ≤ q (k + 1) * 1 :=
              mul_le_mul_of_nonneg_left hcoef (le_of_lt (hq_pos (k + 1)))
            _ = q (k + 1) := by ring
        constructor
        · exact hnext
        · have hratio_scaled (j : ℕ) :
              p39ResidualRatio residual j =
                p39ScaledResidualRatio residual D j / D := by
              rw [p39ScaledResidualRatio]
              field_simp
          have hratio_le :
              p39ResidualRatio residual (k + 1) ≤ q (k + 1) := by
            calc
              p39ResidualRatio residual (k + 1) =
                  p39ScaledResidualRatio residual D (k + 1) / D :=
                hratio_scaled (k + 1)
              _ ≤ q (k + 1) / D :=
                div_le_div_of_nonneg_right hnext hD_nonneg
              _ = q (k + 1) * (1 / D) := by ring
              _ ≤ q (k + 1) * 1 :=
                mul_le_mul_of_nonneg_left hD_inv_le_one
                  (le_of_lt (hq_pos (k + 1)))
              _ = q (k + 1) := by ring
          calc
            residual (k + 1 + 1) =
                p39ResidualRatio residual (k + 1) * residual (k + 1) := by
              rw [hratio_mul]
            _ ≤ q (k + 1) * (2 * residual 0 * q (k + 1) / D) := by
              exact mul_le_mul hratio_le ih.2 (le_of_lt (hpos (k + 1)))
                (le_of_lt (hq_pos (k + 1)))
            _ = 2 * residual 0 * q (k + 1 + 1) / D := by
              rw [hq_succ]
              ring
  refine ⟨hD, hscaled_zero, ?_, ?_⟩
  · intro k
    exact ⟨hscaled_pos k, (hmain k).1⟩
  · have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds 0) := by
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have htwo_pow : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop := by
      exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have hq_tendsto : Tendsto q atTop (nhds 0) := by
      exact hpow.comp htwo_pow
    exact squeeze_zero'
      (Filter.Eventually.of_forall (fun k => le_of_lt (hscaled_pos k)))
      (Filter.Eventually.of_forall (fun k => (hmain k).1)) hq_tendsto

end HighamBench
