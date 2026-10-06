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
  let τ : ℕ → ℝ := p39ResidualRatio residual
  let D : ℝ := 1 / (2 * τ 0)
  let β : ℕ → ℝ := p39ScaledResidualRatio residual D
  let q : ℕ → ℝ := fun k ↦ (1 / 2 : ℝ) ^ (2 ^ k)
  change 1 < D ∧ β 0 = 1 / 2 ∧
    (∀ k, 0 < β k ∧ β k ≤ q k) ∧ Tendsto β atTop (nhds 0)

  have hτpos (k : ℕ) : 0 < τ k := by
    dsimp [τ, p39ResidualRatio]
    exact div_pos (hpos (k + 1)) (hpos k)
  change 2 * τ 0 + 2 * B * residual 0 ≤ 1 at hsmall
  have hdenpos : 0 < 2 * τ 0 := mul_pos (by norm_num) (hτpos 0)
  have hdenlt : 2 * τ 0 < 1 := by
    nlinarith [mul_pos hB (hpos 0)]
  have hDgt : 1 < D := by
    dsimp [D]
    exact one_lt_one_div hdenpos hdenlt
  have hDpos : 0 < D := lt_trans zero_lt_one hDgt
  have hDinv : 1 / D = 2 * τ 0 := by
    dsimp [D]
    field_simp [ne_of_gt hdenpos]
  have hcoef : 1 / D + 2 * B * residual 0 ≤ 1 := by
    rw [hDinv]
    exact hsmall

  have hβdef (k : ℕ) : β k = D * τ k := by
    rfl
  have hβpos (k : ℕ) : 0 < β k := by
    rw [hβdef]
    exact mul_pos hDpos (hτpos k)
  have hβ0 : β 0 = 1 / 2 := by
    rw [hβdef]
    dsimp [D]
    field_simp [ne_of_gt (hτpos 0)]

  have hres_succ (k : ℕ) : residual (k + 1) = τ k * residual k := by
    dsimp [τ, p39ResidualRatio]
    exact (div_mul_cancel₀ _ (ne_of_gt (hpos k))).symm
  have hτstep (k : ℕ) :
      τ (k + 1) ≤ τ k ^ 2 + B * residual (k + 1) := by
    dsimp [τ, p39ResidualRatio]
    rw [div_le_iff₀ (hpos (k + 1))]
    simpa [Nat.add_assoc] using hstep k

  have hqpos (k : ℕ) : 0 < q k := by
    dsimp [q]
    positivity
  have hqzero : q 0 = 1 / 2 := by
    norm_num [q]
  have hqsucc (k : ℕ) : q (k + 1) = q k ^ 2 := by
    dsimp [q]
    simp [pow_succ, pow_mul]

  have hbounds : ∀ k : ℕ,
      β k ≤ q k ∧ residual k ≤ 2 * residual 0 * q k := by
    intro k
    induction k with
    | zero =>
        constructor
        · simpa [hqzero] using hβ0.le
        · rw [hqzero]
          nlinarith
    | succ k ih =>
        rcases ih with ⟨hβk, hrk⟩
        have hτleβ : τ k ≤ β k := by
          calc
            τ k = 1 * τ k := by ring
            _ ≤ D * τ k := mul_le_mul_of_nonneg_right hDgt.le (hτpos k).le
            _ = β k := (hβdef k).symm
        have hprod : β k * residual k ≤ q k * (2 * residual 0 * q k) :=
          mul_le_mul hβk hrk (hpos k).le (hqpos k).le
        have hforce : B * (β k * residual k) ≤
            B * (q k * (2 * residual 0 * q k)) :=
          mul_le_mul_of_nonneg_left hprod hB.le
        have hβsq : β k ^ 2 ≤ q k ^ 2 := by
          nlinarith [(hβpos k).le, (hqpos k).le]
        have hdiv : β k ^ 2 / D ≤ q k ^ 2 / D :=
          div_le_div_of_nonneg_right hβsq hDpos.le
        have hβstep : β (k + 1) ≤
            β k ^ 2 / D + B * β k * residual k := by
          calc
            β (k + 1) = D * τ (k + 1) := hβdef (k + 1)
            _ ≤ D * (τ k ^ 2 + B * residual (k + 1)) :=
              mul_le_mul_of_nonneg_left (hτstep k) hDpos.le
            _ = β k ^ 2 / D + B * β k * residual k := by
              rw [hres_succ]
              rw [hβdef]
              field_simp [ne_of_gt hDpos]
              <;> ring
        constructor
        · calc
            β (k + 1) ≤ β k ^ 2 / D + B * β k * residual k := hβstep
            _ ≤ q k ^ 2 / D + 2 * B * residual 0 * q k ^ 2 := by
              apply add_le_add hdiv
              nlinarith [hforce]
            _ = q k ^ 2 * (1 / D + 2 * B * residual 0) := by ring
            _ ≤ q k ^ 2 * 1 := mul_le_mul_of_nonneg_left hcoef (sq_nonneg (q k))
            _ = q (k + 1) := by rw [hqsucc]; ring
        · calc
            residual (k + 1) = τ k * residual k := hres_succ k
            _ ≤ β k * residual k :=
              mul_le_mul_of_nonneg_right hτleβ (hpos k).le
            _ ≤ q k * (2 * residual 0 * q k) := hprod
            _ = 2 * residual 0 * q (k + 1) := by rw [hqsucc]; ring

  refine ⟨hDgt, hβ0, ?_, ?_⟩
  · intro k
    exact ⟨hβpos k, (hbounds k).1⟩
  · apply squeeze_zero (fun k ↦ (hβpos k).le) (fun k ↦ (hbounds k).1)
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))

end HighamBench
