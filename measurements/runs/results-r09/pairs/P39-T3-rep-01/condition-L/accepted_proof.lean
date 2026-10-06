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
  let τ : ℕ → ℝ := fun k => p39ResidualRatio residual k
  let a : ℝ := 2 * τ 0
  let D : ℝ := 1 / a
  let q : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ (2 ^ k)
  have hτpos (k : ℕ) : 0 < τ k := by
    exact div_pos (hpos (k + 1)) (hpos k)
  have hapos : 0 < a := by
    exact mul_pos (by norm_num) (hτpos 0)
  have ha_ne : a ≠ 0 := ne_of_gt hapos
  have hsmall' : a + 2 * B * residual 0 ≤ 1 := by
    simpa [a, τ] using hsmall
  have hBrpos : 0 < 2 * B * residual 0 := by
    exact mul_pos (mul_pos (by norm_num) hB) (hpos 0)
  have halt : a < 1 := by linarith
  have hale : a ≤ 1 := halt.le
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  have hDgt : 1 < D := by
    dsimp [D]
    rw [lt_div_iff₀ hapos]
    linarith
  have haD : a * D = 1 := by
    simp [D, ha_ne]
  have hτ_mul (k : ℕ) : τ k * residual k = residual (k + 1) := by
    simp [τ, p39ResidualRatio, ne_of_gt (hpos k)]
  have hqpos (k : ℕ) : 0 < q k := by
    dsimp [q]
    positivity
  have hq_succ (k : ℕ) : q (k + 1) = (q k) ^ 2 := by
    change (1 / 2 : ℝ) ^ (2 ^ (k + 1)) =
      ((1 / 2 : ℝ) ^ (2 ^ k)) ^ 2
    rw [show 2 ^ (k + 1) = 2 ^ k * 2 by exact pow_succ 2 k]
    exact pow_mul _ _ _
  have hτstep (k : ℕ) :
      τ (k + 1) ≤ (τ k) ^ 2 + B * residual (k + 1) := by
    change residual (k + 2) / residual (k + 1) ≤
      (p39ResidualRatio residual k) ^ 2 + B * residual (k + 1)
    exact (div_le_iff₀ (hpos (k + 1))).2 (hstep k)
  have hmain : ∀ k : ℕ,
      D * τ k ≤ q k ∧
        residual (k + 1) ≤
          2 * residual 0 * a ^ (k + 1) * q (k + 1) := by
    intro k
    induction k with
    | zero =>
        constructor
        · dsimp [D, a, q]
          field_simp [ne_of_gt (hτpos 0)]
          norm_num
        · rw [← hτ_mul 0]
          apply le_of_eq
          norm_num [a, q]
          ring
    | succ k ih =>
        have hpow : a ^ k ≤ 1 := pow_le_one₀ hapos.le hale
        have hτle : τ k ≤ a * q k := by
          calc
            τ k = a * (D * τ k) := by rw [← mul_assoc, haD, one_mul]
            _ ≤ a * q k := mul_le_mul_of_nonneg_left ih.1 hapos.le
        have hsq : (τ k) ^ 2 ≤ (a * q k) ^ 2 := by
          rw [pow_two, pow_two]
          exact mul_le_mul hτle hτle (hτpos k).le
            (mul_nonneg hapos.le (hqpos k).le)
        have hinside :
            (τ k) ^ 2 + B * residual (k + 1) ≤
              (a * q k) ^ 2 +
                B * (2 * residual 0 * a ^ (k + 1) * q (k + 1)) := by
          exact add_le_add hsq (mul_le_mul_of_nonneg_left ih.2 hB.le)
        have hcoef : a + 2 * B * residual 0 * a ^ k ≤ 1 := by
          have hm : 2 * B * residual 0 * a ^ k ≤ 2 * B * residual 0 := by
            exact mul_le_of_le_one_right hBrpos.le hpow
          linarith
        have halgebra :
            D * ((a * q k) ^ 2 +
              B * (2 * residual 0 * a ^ (k + 1) * q (k + 1))) ≤
                q (k + 1) := by
          rw [hq_succ]
          have hq0 : 0 ≤ (q k) ^ 2 := sq_nonneg _
          calc
            D * ((a * q k) ^ 2 +
                B * (2 * residual 0 * a ^ (k + 1) * (q k) ^ 2)) =
                (a + 2 * B * residual 0 * a ^ k) * (q k) ^ 2 := by
                  dsimp [D]
                  rw [pow_succ]
                  field_simp [ha_ne]
                  <;> ring
            _ ≤ 1 * (q k) ^ 2 := mul_le_mul_of_nonneg_right hcoef hq0
            _ = (q k) ^ 2 := one_mul _
        have hscaled_next : D * τ (k + 1) ≤ q (k + 1) := by
          calc
            D * τ (k + 1) ≤
                D * ((τ k) ^ 2 + B * residual (k + 1)) :=
              mul_le_mul_of_nonneg_left (hτstep k) hDpos.le
            _ ≤ D * ((a * q k) ^ 2 +
                B * (2 * residual 0 * a ^ (k + 1) * q (k + 1))) :=
              mul_le_mul_of_nonneg_left hinside hDpos.le
            _ ≤ q (k + 1) := halgebra
        constructor
        · exact hscaled_next
        · have hτnext_le : τ (k + 1) ≤ a * q (k + 1) := by
            calc
              τ (k + 1) = a * (D * τ (k + 1)) := by
                rw [← mul_assoc, haD, one_mul]
              _ ≤ a * q (k + 1) :=
                mul_le_mul_of_nonneg_left hscaled_next hapos.le
          calc
            residual (k + 1 + 1) = τ (k + 1) * residual (k + 1) := by
              rw [hτ_mul (k + 1)]
            _ ≤ (a * q (k + 1)) *
                (2 * residual 0 * a ^ (k + 1) * q (k + 1)) := by
              exact mul_le_mul hτnext_le ih.2 (hpos (k + 1)).le
                (mul_nonneg hapos.le (hqpos (k + 1)).le)
            _ = 2 * residual 0 * a ^ (k + 1 + 1) * q (k + 1 + 1) := by
              rw [hq_succ, pow_succ]
              ring
  have hscaled_zero : p39ScaledResidualRatio residual D 0 = 1 / 2 := by
    change D * τ 0 = 1 / 2
    dsimp [D, a]
    field_simp [ne_of_gt (hτpos 0)]
  have hscaled : ∀ k : ℕ,
      0 < p39ScaledResidualRatio residual D k ∧
        p39ScaledResidualRatio residual D k ≤ (1 / 2 : ℝ) ^ (2 ^ k) := by
    intro k
    change 0 < D * τ k ∧ D * τ k ≤ q k
    exact ⟨mul_pos hDpos (hτpos k), (hmain k).1⟩
  have hq_tendsto : Tendsto q atTop (nhds 0) := by
    have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have he : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    exact hp.comp he
  have hscaled_tendsto :
      Tendsto (p39ScaledResidualRatio residual D) atTop (nhds 0) := by
    exact squeeze_zero (fun k => (hscaled k).1.le) (fun k => (hscaled k).2)
      hq_tendsto
  change 1 < D ∧
    p39ScaledResidualRatio residual D 0 = 1 / 2 ∧
      (∀ k, 0 < p39ScaledResidualRatio residual D k ∧
        p39ScaledResidualRatio residual D k ≤ (1 / 2 : ℝ) ^ (2 ^ k)) ∧
      Tendsto (p39ScaledResidualRatio residual D) atTop (nhds 0)
  exact ⟨hDgt, hscaled_zero, hscaled, hscaled_tendsto⟩

end HighamBench
