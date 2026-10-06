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
  change
    1 < D ∧
      p39ScaledResidualRatio residual D 0 = 1 / 2 ∧
      (∀ k,
        0 < p39ScaledResidualRatio residual D k ∧
        p39ScaledResidualRatio residual D k ≤ (1 / 2 : ℝ) ^ (2 ^ k)) ∧
      Tendsto (p39ScaledResidualRatio residual D) atTop (nhds 0)

  have hratio_pos (k : ℕ) : 0 < p39ResidualRatio residual k := by
    exact div_pos (hpos (k + 1)) (hpos k)

  have hden_pos : 0 < 2 * p39ResidualRatio residual 0 := by
    exact mul_pos (by norm_num) (hratio_pos 0)
  have hden_lt : 2 * p39ResidualRatio residual 0 < 1 := by
    have hextra : 0 < 2 * B * residual 0 := by
      exact mul_pos (mul_pos (by norm_num) hB) (hpos 0)
    linarith
  have hD : 1 < D := by
    dsimp [D]
    rw [lt_div_iff₀ hden_pos]
    simpa using hden_lt
  have hD_pos : 0 < D := lt_trans zero_lt_one hD
  have hD_ne : D ≠ 0 := ne_of_gt hD_pos
  have hD_inv : 1 / D = 2 * p39ResidualRatio residual 0 := by
    dsimp [D]
    field_simp
  have hcoef : 1 / D + 2 * B * residual 0 ≤ 1 := by
    rw [hD_inv]
    exact hsmall

  have hbeta_pos (k : ℕ) : 0 < p39ScaledResidualRatio residual D k := by
    exact mul_pos hD_pos (hratio_pos k)
  have hbeta_zero : p39ScaledResidualRatio residual D 0 = 1 / 2 := by
    rw [p39ScaledResidualRatio]
    dsimp [D]
    field_simp [ne_of_gt (hratio_pos 0)]

  have hresidual_identity (k : ℕ) :
      D * residual (k + 1) =
        p39ScaledResidualRatio residual D k * residual k := by
    rw [p39ScaledResidualRatio, p39ResidualRatio]
    field_simp [ne_of_gt (hpos k)]

  have hbeta_step (k : ℕ) :
      p39ScaledResidualRatio residual D (k + 1) ≤
        (p39ScaledResidualRatio residual D k) ^ 2 / D +
          D * B * residual (k + 1) := by
    have hratio_step :
        p39ResidualRatio residual (k + 1) ≤
          (p39ResidualRatio residual k) ^ 2 + B * residual (k + 1) := by
      rw [p39ResidualRatio]
      apply (div_le_iff₀ (hpos (k + 1))).2
      simpa [p39ResidualRatio, Nat.add_assoc] using hstep k
    calc
      p39ScaledResidualRatio residual D (k + 1) =
          D * p39ResidualRatio residual (k + 1) := rfl
      _ ≤ D * ((p39ResidualRatio residual k) ^ 2 +
          B * residual (k + 1)) :=
        mul_le_mul_of_nonneg_left hratio_step (le_of_lt hD_pos)
      _ = (p39ScaledResidualRatio residual D k) ^ 2 / D +
          D * B * residual (k + 1) := by
        rw [p39ScaledResidualRatio]
        field_simp [hD_ne]
        <;> ring

  have hpow_succ (k : ℕ) :
      (((1 / 2 : ℝ) ^ (2 ^ k)) ^ 2) =
        (1 / 2 : ℝ) ^ (2 ^ (k + 1)) := by
    rw [← pow_mul, pow_succ]

  have hjoint (k : ℕ) :
      p39ScaledResidualRatio residual D k ≤ (1 / 2 : ℝ) ^ (2 ^ k) ∧
      D * residual (k + 1) ≤
        2 * residual 0 * (1 / 2 : ℝ) ^ (2 ^ (k + 1)) := by
    induction k with
    | zero =>
        constructor
        · simpa using hbeta_zero.le
        · rw [hresidual_identity 0, hbeta_zero]
          norm_num
          nlinarith
    | succ k ih =>
        have hsq :
            (p39ScaledResidualRatio residual D k) ^ 2 ≤
              (((1 / 2 : ℝ) ^ (2 ^ k)) ^ 2) :=
          pow_le_pow_left₀ (le_of_lt (hbeta_pos k)) ih.1 2
        have hfirst :
            (p39ScaledResidualRatio residual D k) ^ 2 / D ≤
              (1 / 2 : ℝ) ^ (2 ^ (k + 1)) / D := by
          rw [← hpow_succ k]
          exact div_le_div_of_nonneg_right hsq (le_of_lt hD_pos)
        have hsecond :
            D * B * residual (k + 1) ≤
              2 * B * residual 0 * (1 / 2 : ℝ) ^ (2 ^ (k + 1)) := by
          calc
            D * B * residual (k + 1) = B * (D * residual (k + 1)) := by ring
            _ ≤ B * (2 * residual 0 *
                (1 / 2 : ℝ) ^ (2 ^ (k + 1))) :=
              mul_le_mul_of_nonneg_left ih.2 (le_of_lt hB)
            _ = 2 * B * residual 0 *
                (1 / 2 : ℝ) ^ (2 ^ (k + 1)) := by ring
        have hbeta_next :
            p39ScaledResidualRatio residual D (k + 1) ≤
              (1 / 2 : ℝ) ^ (2 ^ (k + 1)) := by
          calc
            p39ScaledResidualRatio residual D (k + 1) ≤
                (p39ScaledResidualRatio residual D k) ^ 2 / D +
                  D * B * residual (k + 1) := hbeta_step k
            _ ≤ (1 / 2 : ℝ) ^ (2 ^ (k + 1)) / D +
                  2 * B * residual 0 *
                    (1 / 2 : ℝ) ^ (2 ^ (k + 1)) :=
              add_le_add hfirst hsecond
            _ = (1 / D + 2 * B * residual 0) *
                  (1 / 2 : ℝ) ^ (2 ^ (k + 1)) := by ring
            _ ≤ 1 * (1 / 2 : ℝ) ^ (2 ^ (k + 1)) :=
              mul_le_mul_of_nonneg_right hcoef (by positivity)
            _ = (1 / 2 : ℝ) ^ (2 ^ (k + 1)) := one_mul _
        constructor
        · exact hbeta_next
        · have hr_le : residual (k + 1) ≤
              2 * residual 0 * (1 / 2 : ℝ) ^ (2 ^ (k + 1)) := by
            calc
              residual (k + 1) ≤ D * residual (k + 1) := by
                nlinarith [hpos (k + 1)]
              _ ≤ 2 * residual 0 *
                  (1 / 2 : ℝ) ^ (2 ^ (k + 1)) := ih.2
          rw [hresidual_identity (k + 1)]
          calc
            p39ScaledResidualRatio residual D (k + 1) * residual (k + 1) ≤
                (1 / 2 : ℝ) ^ (2 ^ (k + 1)) *
                  (2 * residual 0 * (1 / 2 : ℝ) ^ (2 ^ (k + 1))) :=
              mul_le_mul hbeta_next hr_le (le_of_lt (hpos (k + 1))) (by positivity)
            _ = 2 * residual 0 *
                (1 / 2 : ℝ) ^ (2 ^ ((k + 1) + 1)) := by
              rw [← hpow_succ (k + 1)]
              ring

  have hbound (k : ℕ) :
      0 < p39ScaledResidualRatio residual D k ∧
      p39ScaledResidualRatio residual D k ≤ (1 / 2 : ℝ) ^ (2 ^ k) :=
    ⟨hbeta_pos k, (hjoint k).1⟩
  have hmajorant :
      Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ (2 ^ k)) atTop (nhds 0) := by
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
  refine ⟨hD, hbeta_zero, hbound, ?_⟩
  exact squeeze_zero (fun k => (hbeta_pos k).le) (fun k => (hjoint k).1) hmajorant

end HighamBench
