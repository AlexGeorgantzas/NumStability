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
    simp only [τ, p39ResidualRatio]
    exact div_pos (hpos (k + 1)) (hpos k)
  have hsum : 2 * τ 0 + 2 * B * residual 0 ≤ 1 := by
    simpa only [τ] using hsmall
  have htwoτpos : 0 < 2 * τ 0 := mul_pos (by norm_num) (hτpos 0)
  have htwoτlt : 2 * τ 0 < 1 := by
    have hBrpos : 0 < 2 * B * residual 0 :=
      mul_pos (mul_pos (by norm_num) hB) (hpos 0)
    linarith
  have hDpos : 0 < D := by
    dsimp only [D]
    exact one_div_pos.mpr htwoτpos
  have hDden : D * (2 * τ 0) = 1 := by
    dsimp only [D]
    exact one_div_mul_cancel (ne_of_gt htwoτpos)
  have hD : 1 < D := by
    dsimp only [D]
    simpa only [one_div] using (one_lt_inv₀ htwoτpos).2 htwoτlt

  have hβτ (k : ℕ) : β k = D * τ k := by
    rfl
  have hβpos (k : ℕ) : 0 < β k := by
    rw [hβτ]
    exact mul_pos hDpos (hτpos k)
  have hqpos (k : ℕ) : 0 < q k := by
    dsimp only [q]
    positivity
  have hq_succ (k : ℕ) : q (k + 1) = (q k) ^ 2 := by
    simp only [q, pow_succ, pow_mul]

  have hβ0 : β 0 = 1 / 2 := by
    rw [hβτ]
    dsimp only [D]
    field_simp [ne_of_gt (hτpos 0)]

  have hτstep (k : ℕ) :
      τ (k + 1) ≤ (τ k) ^ 2 + B * residual (k + 1) := by
    simp only [τ, p39ResidualRatio]
    rw [div_le_iff₀ (hpos (k + 1))]
    simpa only [Nat.add_assoc] using hstep k

  have hscale_sq (k : ℕ) :
      D * (τ k) ^ 2 = (2 * τ 0) * (β k) ^ 2 := by
    rw [hβτ]
    calc
      D * (τ k) ^ 2 = (D * (2 * τ 0)) * (D * (τ k) ^ 2) := by
        rw [hDden]
        ring
      _ = (2 * τ 0) * (D * τ k) ^ 2 := by ring

  have hind : ∀ k : ℕ,
      β k ≤ q k ∧
        D * residual (k + 1) ≤ 2 * residual 0 * q (k + 1) := by
    intro k
    induction k with
    | zero =>
        constructor
        · simpa only [q, pow_zero, pow_one] using le_of_eq hβ0
        · have hid : D * residual (0 + 1) = β 0 * residual 0 := by
            rw [hβτ]
            simp only [τ, p39ResidualRatio]
            field_simp [ne_of_gt (hpos 0)]
          rw [hid, hβ0]
          norm_num [q]
          ring_nf
          exact le_rfl
    | succ k ih =>
        have hβsq : (β k) ^ 2 ≤ (q k) ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr ih.1)
            (add_nonneg (le_of_lt (hqpos k)) (le_of_lt (hβpos k)))]
        have hfirst : D * (τ k) ^ 2 ≤ (2 * τ 0) * (q k) ^ 2 := by
          rw [hscale_sq]
          exact mul_le_mul_of_nonneg_left hβsq (le_of_lt htwoτpos)
        have hsecond :
            B * (D * residual (k + 1)) ≤
              (2 * B * residual 0) * (q k) ^ 2 := by
          calc
            B * (D * residual (k + 1))
                ≤ B * (2 * residual 0 * q (k + 1)) :=
              mul_le_mul_of_nonneg_left ih.2 (le_of_lt hB)
            _ = (2 * B * residual 0) * (q k) ^ 2 := by
              rw [hq_succ]
              ring
        have hβnext : β (k + 1) ≤ q (k + 1) := by
          calc
            β (k + 1) = D * τ (k + 1) := hβτ (k + 1)
            _ ≤ D * ((τ k) ^ 2 + B * residual (k + 1)) :=
              mul_le_mul_of_nonneg_left (hτstep k) (le_of_lt hDpos)
            _ = D * (τ k) ^ 2 + B * (D * residual (k + 1)) := by ring
            _ ≤ (2 * τ 0) * (q k) ^ 2 +
                (2 * B * residual 0) * (q k) ^ 2 := add_le_add hfirst hsecond
            _ = (2 * τ 0 + 2 * B * residual 0) * (q k) ^ 2 := by ring
            _ ≤ 1 * (q k) ^ 2 :=
              mul_le_mul_of_nonneg_right hsum (sq_nonneg (q k))
            _ = q (k + 1) := by rw [hq_succ, one_mul]
        constructor
        · exact hβnext
        · have hr_le : residual (k + 1) ≤ 2 * residual 0 * q (k + 1) := by
            calc
              residual (k + 1) ≤ D * residual (k + 1) := by
                have := mul_lt_mul_of_pos_right hD (hpos (k + 1))
                linarith
              _ ≤ 2 * residual 0 * q (k + 1) := ih.2
          have hid : D * residual (k + 1 + 1) =
              β (k + 1) * residual (k + 1) := by
            rw [hβτ]
            simp only [τ, p39ResidualRatio]
            field_simp [ne_of_gt (hpos (k + 1))]
          calc
            D * residual (k + 1 + 1) =
                β (k + 1) * residual (k + 1) := hid
            _ ≤ q (k + 1) * residual (k + 1) :=
              mul_le_mul_of_nonneg_right hβnext (le_of_lt (hpos (k + 1)))
            _ ≤ q (k + 1) * (2 * residual 0 * q (k + 1)) :=
              mul_le_mul_of_nonneg_left hr_le (le_of_lt (hqpos (k + 1)))
            _ = 2 * residual 0 * q (k + 1 + 1) := by
              rw [hq_succ]
              ring

  refine ⟨hD, hβ0, ?_, ?_⟩
  · intro k
    exact ⟨hβpos k, (hind k).1⟩
  · apply squeeze_zero (fun k ↦ (hβpos k).le) (fun k ↦ (hind k).1)
    have hbase : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hexp : Tendsto (fun k : ℕ ↦ 2 ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    simpa only [q] using hbase.comp hexp

end HighamBench
