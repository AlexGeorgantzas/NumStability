import HighamBench.P32Definitions

namespace HighamBench

/-- P32-T3: the sharp structured first-order condition formula in (3.3)--(3.4). -/
theorem p32_t3_sharp_structured_condition_formula
    {n t : ℕ}
    (K : P32CoefficientMap n t) (H : P32CoefficientMap n n)
    (g : P32Vector t) (f : P32Vector n) (xNorm : ℝ)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i) (hx : 0 < xNorm) :
    p32LinearizedCondition K H g f xNorm =
      p32ConditionFormula K H g f xNorm := by
  -- PROOF_START P32-T3-H001
  let R : P32Vector n := p32ConditionRadius K H g f
  let S : Set ℝ := p32LinearizedValues K H g f xNorm
  change sSup S = ‖R‖ / xNorm

  have hR_nonneg (i : Fin n) : 0 ≤ R i := by
    apply add_nonneg <;> apply Finset.sum_nonneg
    · intro j hj
      exact mul_nonneg (abs_nonneg _) (hg j)
    · intro j hj
      exact mul_nonneg (abs_nonneg _) (hf j)

  have hresponse_le (dp : P32Vector t) (db : P32Vector n)
      (hadm : P32Admissible g f dp db) :
      ‖p32LinearResponse K H dp db‖ ≤ ‖R‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg R)).2
    intro i
    rw [Real.norm_eq_abs]
    calc
      |p32LinearResponse K H dp db i| =
          |∑ j, H i j * db j - ∑ j, K i j * dp j| := rfl
      _ ≤ |∑ j, H i j * db j| + |∑ j, K i j * dp j| := abs_sub _ _
      _ ≤ (∑ j, |H i j * db j|) + ∑ j, |K i j * dp j| :=
        add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
      _ = (∑ j, |H i j| * |db j|) + ∑ j, |K i j| * |dp j| := by
        simp only [abs_mul]
      _ ≤ (∑ j, |H i j| * f j) + ∑ j, |K i j| * g j := by
        apply add_le_add <;> apply Finset.sum_le_sum
        · intro j hj
          exact mul_le_mul_of_nonneg_left (hadm.2 j) (abs_nonneg _)
        · intro j hj
          exact mul_le_mul_of_nonneg_left (hadm.1 j) (abs_nonneg _)
      _ = R i := by
        simp only [R, p32ConditionRadius]
        ac_rfl
      _ ≤ ‖R‖ := by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hR_nonneg i)] using
          (norm_le_pi_norm R i)

  have hzero : (0 : ℝ) ∈ S := by
    refine ⟨(0 : P32Vector t), (0 : P32Vector n), ?_, ?_⟩
    · constructor
      · intro j
        simpa using hg j
      · intro i
        simpa using hf i
    · have hz : p32LinearResponse K H (0 : P32Vector t) (0 : P32Vector n) = 0 := by
        funext i
        simp [p32LinearResponse]
      rw [hz, norm_zero, zero_div]

  have hupper : ∀ q ∈ S, q ≤ ‖R‖ / xNorm := by
    intro q hq
    rcases hq with ⟨dp, db, hadm, rfl⟩
    exact (div_le_div_iff_of_pos_right hx).2 (hresponse_le dp db hadm)

  have hS_bdd : BddAbove S := ⟨‖R‖ / xNorm, hupper⟩
  have hsup_nonneg : 0 ≤ sSup S := le_csSup hS_bdd hzero

  apply le_antisymm
  · exact csSup_le ⟨0, hzero⟩ hupper
  · apply (div_le_iff₀ hx).2
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hsup_nonneg hx.le)).2
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (hR_nonneg i)]

    let dp : P32Vector t := fun j ↦ if 0 ≤ K i j then -g j else g j
    let db : P32Vector n := fun j ↦ if 0 ≤ H i j then f j else -f j

    have hadm : P32Admissible g f dp db := by
      constructor
      · intro j
        dsimp [dp]
        split <;> simp only [abs_neg, abs_of_nonneg (hg j), le_refl]
      · intro j
        dsimp [db]
        split <;> simp only [abs_neg, abs_of_nonneg (hf j), le_refl]

    have hK (j : Fin t) : K i j * dp j = -(|K i j| * g j) := by
      dsimp [dp]
      split
      · rename_i h
        rw [abs_of_nonneg h]
        ring
      · rename_i h
        rw [abs_of_neg (lt_of_not_ge h)]
        ring

    have hH (j : Fin n) : H i j * db j = |H i j| * f j := by
      dsimp [db]
      split
      · rename_i h
        rw [abs_of_nonneg h]
      · rename_i h
        rw [abs_of_neg (lt_of_not_ge h)]
        ring

    have hresponse_i : p32LinearResponse K H dp db i = R i := by
      simp only [p32LinearResponse]
      rw [Finset.sum_congr rfl (fun j hj ↦ hH j)]
      rw [Finset.sum_congr rfl (fun j hj ↦ hK j)]
      simp only [Finset.sum_neg_distrib, sub_neg_eq_add]
      simp only [R, p32ConditionRadius]
      ac_rfl

    have hcoord : R i ≤ ‖p32LinearResponse K H dp db‖ := by
      have hi := norm_le_pi_norm (p32LinearResponse K H dp db) i
      rw [hresponse_i, Real.norm_eq_abs, abs_of_nonneg (hR_nonneg i)] at hi
      exact hi

    have hmem : ‖p32LinearResponse K H dp db‖ / xNorm ∈ S := by
      exact ⟨dp, db, hadm, rfl⟩
    have hdiv : R i / xNorm ≤ sSup S :=
      ((div_le_div_iff_of_pos_right hx).2 hcoord).trans (le_csSup hS_bdd hmem)
    exact (div_le_iff₀ hx).1 hdiv

end HighamBench
