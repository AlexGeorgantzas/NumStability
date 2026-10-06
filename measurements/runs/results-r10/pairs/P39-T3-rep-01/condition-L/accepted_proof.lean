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
    exact div_pos (hpos (k + 1)) (hpos k)
  have hden_pos : 0 < 2 * p39ResidualRatio residual 0 := by
    exact mul_pos (by norm_num) (hratio_pos 0)
  have hD_pos : 0 < D := by
    dsimp [D]
    positivity
  have hD_mul : D * (2 * p39ResidualRatio residual 0) = 1 := by
    dsimp [D]
    exact one_div_mul_cancel (ne_of_gt hden_pos)
  have htworatio_lt : 2 * p39ResidualRatio residual 0 < 1 := by
    have hforcing : 0 < 2 * B * residual 0 := by
      exact mul_pos (mul_pos (by norm_num) hB) (hpos 0)
    linarith
  have hD : 1 < D := by
    nlinarith
  have hbeta_zero : p39ScaledResidualRatio residual D 0 = 1 / 2 := by
    rw [p39ScaledResidualRatio]
    nlinarith [hD_mul]
  have hratio_residual (k : ℕ) :
      residual (k + 1) = p39ResidualRatio residual k * residual k := by
    rw [p39ResidualRatio]
    field_simp [ne_of_gt (hpos k)]
  have hratio_step (k : ℕ) :
      p39ResidualRatio residual (k + 1) ≤
        (p39ResidualRatio residual k) ^ 2 + B * residual (k + 1) := by
    rw [p39ResidualRatio]
    apply (div_le_iff₀ (hpos (k + 1))).2
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstep k
  have hscaled_pos (k : ℕ) : 0 < p39ScaledResidualRatio residual D k := by
    exact mul_pos hD_pos (hratio_pos k)
  have hq_pos (k : ℕ) : 0 < q k := by
    dsimp [q]
    positivity
  have hq_succ (k : ℕ) : q (k + 1) = (q k) ^ 2 := by
    dsimp [q]
    rw [show 2 ^ (k + 1) = 2 ^ k * 2 by omega, pow_mul]
  have hscaled_step (k : ℕ) :
      p39ScaledResidualRatio residual D (k + 1) ≤
        (p39ScaledResidualRatio residual D k) ^ 2 / D +
          B * (D * residual (k + 1)) := by
    rw [p39ScaledResidualRatio]
    calc
      D * p39ResidualRatio residual (k + 1) ≤
          D * ((p39ResidualRatio residual k) ^ 2 + B * residual (k + 1)) :=
        mul_le_mul_of_nonneg_left (hratio_step k) hD_pos.le
      _ = (D * p39ResidualRatio residual k) ^ 2 / D +
          B * (D * residual (k + 1)) := by
        field_simp [ne_of_gt hD_pos] <;> ring
  have hmain (k : ℕ) :
      p39ScaledResidualRatio residual D k ≤ q k ∧
        D * residual (k + 1) ≤ 2 * residual 0 * q (k + 1) := by
    induction k with
    | zero =>
        constructor
        · simpa [q] using hbeta_zero.le
        · have heq : D * residual (0 + 1) = 2 * residual 0 * q (0 + 1) := by
            calc
              D * residual (0 + 1) =
                  p39ScaledResidualRatio residual D 0 * residual 0 := by
                rw [hratio_residual 0, p39ScaledResidualRatio]
                ring
              _ = (1 / 2 : ℝ) * residual 0 := by rw [hbeta_zero]
              _ = 2 * residual 0 * q (0 + 1) := by
                norm_num [q]
                ring
          exact heq.le
    | succ k ih =>
        have hsquare :
            (p39ScaledResidualRatio residual D k) ^ 2 ≤ (q k) ^ 2 := by
          nlinarith [ih.1, hscaled_pos k, hq_pos k]
        have hfirst :
            p39ScaledResidualRatio residual D (k + 1) ≤ q (k + 1) := by
          calc
            p39ScaledResidualRatio residual D (k + 1) ≤
                (p39ScaledResidualRatio residual D k) ^ 2 / D +
                  B * (D * residual (k + 1)) := hscaled_step k
            _ ≤ (q k) ^ 2 / D +
                  B * (2 * residual 0 * q (k + 1)) := by
              exact add_le_add
                (div_le_div_of_nonneg_right hsquare hD_pos.le)
                (mul_le_mul_of_nonneg_left ih.2 hB.le)
            _ = (2 * p39ResidualRatio residual 0 + 2 * B * residual 0) *
                  q (k + 1) := by
              rw [hq_succ k]
              field_simp [ne_of_gt hD_pos]
              nlinarith [hD_mul]
            _ ≤ q (k + 1) := by
              have := mul_le_mul_of_nonneg_right hsmall (hq_pos (k + 1)).le
              norm_num at this ⊢
              exact this
        constructor
        · simpa only [Nat.succ_eq_add_one] using hfirst
        · have hresidual_bound :
              residual (k + 1) ≤ 2 * residual 0 * q (k + 1) := by
            calc
              residual (k + 1) ≤ D * residual (k + 1) := by
                simpa only [one_mul] using
                  mul_le_mul_of_nonneg_right hD.le (hpos (k + 1)).le
              _ ≤ 2 * residual 0 * q (k + 1) := ih.2
          calc
            D * residual (Nat.succ k + 1) =
                p39ScaledResidualRatio residual D (k + 1) *
                  residual (k + 1) := by
              rw [show Nat.succ k + 1 = (k + 1) + 1 by omega,
                hratio_residual (k + 1), p39ScaledResidualRatio]
              ring
            _ ≤ q (k + 1) * residual (k + 1) :=
              mul_le_mul_of_nonneg_right hfirst (hpos (k + 1)).le
            _ ≤ q (k + 1) * (2 * residual 0 * q (k + 1)) :=
              mul_le_mul_of_nonneg_left hresidual_bound (hq_pos (k + 1)).le
            _ = 2 * residual 0 * q (Nat.succ k + 1) := by
              rw [show Nat.succ k + 1 = (k + 1) + 1 by omega, hq_succ]
              ring
  have hq_tendsto : Tendsto q atTop (nhds 0) := by
    have hbase : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hexponent : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    exact hbase.comp hexponent
  have hscaled_tendsto :
      Tendsto (p39ScaledResidualRatio residual D) atTop (nhds 0) := by
    exact squeeze_zero (fun k => (hscaled_pos k).le) (fun k => (hmain k).1) hq_tendsto
  change 1 < D ∧
    p39ScaledResidualRatio residual D 0 = 1 / 2 ∧
    (∀ k, 0 < p39ScaledResidualRatio residual D k ∧
      p39ScaledResidualRatio residual D k ≤ (1 / 2 : ℝ) ^ (2 ^ k)) ∧
    Tendsto (p39ScaledResidualRatio residual D) atTop (nhds 0)
  refine ⟨hD, hbeta_zero, ?_, hscaled_tendsto⟩
  intro k
  exact ⟨hscaled_pos k, (hmain k).1⟩

end HighamBench
