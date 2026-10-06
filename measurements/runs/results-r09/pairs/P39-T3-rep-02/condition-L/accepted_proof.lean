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
  let e : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ (2 ^ k)
  change 1 < D ∧ β 0 = 1 / 2 ∧
    (∀ k, 0 < β k ∧ β k ≤ e k) ∧ Tendsto β atTop (nhds 0)

  have hτpos : ∀ k, 0 < τ k := by
    intro k
    exact div_pos (hpos (k + 1)) (hpos k)
  have hbudget : 2 * τ 0 + 2 * B * residual 0 ≤ 1 := by
    simpa [τ] using hsmall
  have htwoτpos : 0 < 2 * τ 0 := mul_pos (by norm_num) (hτpos 0)
  have htwoτlt : 2 * τ 0 < 1 := by
    have hBrpos : 0 < 2 * B * residual 0 :=
      mul_pos (mul_pos (by norm_num) hB) (hpos 0)
    linarith
  have hD : 1 < D := by
    exact one_lt_one_div htwoτpos htwoτlt
  have hDpos : 0 < D := lt_trans (by norm_num) hD

  have hβdef (k : ℕ) : β k = D * τ k := by
    rfl
  have hβpos : ∀ k, 0 < β k := by
    intro k
    rw [hβdef]
    exact mul_pos hDpos (hτpos k)
  have hDtwoτ : D * (2 * τ 0) = 1 := by
    dsimp [D]
    field_simp [ne_of_gt (hτpos 0)]
  have hβzero : β 0 = 1 / 2 := by
    rw [hβdef]
    nlinarith [hDtwoτ]

  have hτmul (k : ℕ) : τ k * residual k = residual (k + 1) := by
    dsimp [τ, p39ResidualRatio]
    field_simp [ne_of_gt (hpos k)]
  have hscaledRes (k : ℕ) :
      D * residual (k + 1) = β k * residual k := by
    rw [hβdef]
    rw [← hτmul k]
    ring
  have hτstep (k : ℕ) :
      τ (k + 1) ≤ τ k ^ 2 + B * residual (k + 1) := by
    apply (div_le_iff₀ (hpos (k + 1))).2
    simpa [τ, p39ResidualRatio, Nat.add_assoc] using hstep k
  have hquad (k : ℕ) : D * τ k ^ 2 = (2 * τ 0) * β k ^ 2 := by
    rw [hβdef]
    nlinarith [hDtwoτ]
  have hβstep (k : ℕ) :
      β (k + 1) ≤ (2 * τ 0) * β k ^ 2 + B * (D * residual (k + 1)) := by
    have hm := mul_le_mul_of_nonneg_left (hτstep k) hDpos.le
    rw [hβdef]
    calc
      D * τ (k + 1) ≤ D * (τ k ^ 2 + B * residual (k + 1)) := hm
      _ = (2 * τ 0) * β k ^ 2 + B * (D * residual (k + 1)) := by
        rw [mul_add, hquad]
        ring

  have hepos : ∀ k, 0 < e k := by
    intro k
    exact pow_pos (by norm_num) _
  have hesucc (k : ℕ) : e (k + 1) = (e k) ^ 2 := by
    dsimp [e]
    rw [pow_succ, pow_mul]

  have hinv : ∀ k,
      β k ≤ e k ∧
        D * residual (k + 1) ≤ 2 * residual 0 * e (k + 1) := by
    intro k
    induction k with
    | zero =>
        constructor
        · simpa [e] using hβzero.le
        · rw [hscaledRes 0, hβzero]
          norm_num [e]
          ring_nf
          exact le_rfl
    | succ k ih =>
        have hsq : β k ^ 2 ≤ e (k + 1) := by
          rw [hesucc]
          exact (sq_le_sq₀ (hβpos k).le (hepos k).le).2 ih.1
        have ht₁ :
            (2 * τ 0) * β k ^ 2 ≤ (2 * τ 0) * e (k + 1) :=
          mul_le_mul_of_nonneg_left hsq htwoτpos.le
        have ht₂ :
            B * (D * residual (k + 1)) ≤
              B * (2 * residual 0 * e (k + 1)) :=
          mul_le_mul_of_nonneg_left ih.2 hB.le
        have hcoef :
            (2 * τ 0 + 2 * B * residual 0) * e (k + 1) ≤ e (k + 1) := by
          have := mul_le_mul_of_nonneg_right hbudget (hepos (k + 1)).le
          simpa using this
        have hnext : β (k + 1) ≤ e (k + 1) := by
          nlinarith [hβstep k, ht₁, ht₂, hcoef]
        constructor
        · exact hnext
        · have hr_le_D : residual (k + 1) ≤ D * residual (k + 1) := by
            nlinarith [mul_pos (sub_pos.mpr hD) (hpos (k + 1))]
          have hr : residual (k + 1) ≤ 2 * residual 0 * e (k + 1) :=
            hr_le_D.trans ih.2
          calc
            D * residual (k + 1 + 1) = β (k + 1) * residual (k + 1) :=
              hscaledRes (k + 1)
            _ ≤ e (k + 1) * (2 * residual 0 * e (k + 1)) :=
              mul_le_mul hnext hr (hpos (k + 1)).le (hepos (k + 1)).le
            _ = 2 * residual 0 * e (k + 1 + 1) := by
              rw [hesucc]
              ring

  refine ⟨hD, hβzero, ?_, ?_⟩
  · intro k
    exact ⟨hβpos k, (hinv k).1⟩
  · apply squeeze_zero (fun k => (hβpos k).le) (fun k => (hinv k).1)
    have hgeom : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hexp : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    exact hgeom.comp hexp

end HighamBench
