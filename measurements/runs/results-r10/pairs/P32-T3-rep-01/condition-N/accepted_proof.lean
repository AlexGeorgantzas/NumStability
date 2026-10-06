import HighamBench.P32Definitions

namespace HighamBench

private lemma p32ConditionRadius_apply_nonneg
    {n t : ℕ}
    (K : P32CoefficientMap n t) (H : P32CoefficientMap n n)
    (g : P32Vector t) (f : P32Vector n)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i) (i : Fin n) :
    0 ≤ p32ConditionRadius K H g f i := by
  simp only [p32ConditionRadius]
  exact add_nonneg
    (Finset.sum_nonneg fun j _ ↦ mul_nonneg (abs_nonneg _) (hg j))
    (Finset.sum_nonneg fun j _ ↦ mul_nonneg (abs_nonneg _) (hf j))

private lemma p32LinearResponse_norm_le_radius_norm
    {n t : ℕ}
    (K : P32CoefficientMap n t) (H : P32CoefficientMap n n)
    (g : P32Vector t) (f : P32Vector n)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i)
    (dp : P32Vector t) (db : P32Vector n)
    (hadm : P32Admissible g f dp db) :
    ‖p32LinearResponse K H dp db‖ ≤ ‖p32ConditionRadius K H g f‖ := by
  rcases hadm with ⟨hdp, hdb⟩
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  rw [Real.norm_eq_abs]
  calc
    |p32LinearResponse K H dp db i|
        = |(∑ j, H i j * db j) - ∑ j, K i j * dp j| := by
            rfl
    _ ≤ |∑ j, H i j * db j| + |∑ j, K i j * dp j| := abs_sub _ _
    _ ≤ (∑ j, |H i j * db j|) + ∑ j, |K i j * dp j| :=
      add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
    _ = (∑ j, |H i j| * |db j|) + ∑ j, |K i j| * |dp j| := by
      simp only [abs_mul]
    _ ≤ (∑ j, |H i j| * f j) + ∑ j, |K i j| * g j :=
      add_le_add
        (Finset.sum_le_sum fun j _ ↦
          mul_le_mul_of_nonneg_left (hdb j) (abs_nonneg _))
        (Finset.sum_le_sum fun j _ ↦
          mul_le_mul_of_nonneg_left (hdp j) (abs_nonneg _))
    _ = p32ConditionRadius K H g f i := by
      simp only [p32ConditionRadius]
      ac_rfl
    _ = ‖p32ConditionRadius K H g f i‖ := by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (p32ConditionRadius_apply_nonneg K H g f hg hf i)]
    _ ≤ ‖p32ConditionRadius K H g f‖ :=
      norm_le_pi_norm (p32ConditionRadius K H g f) i

private lemma p32_zero_mem_linearizedValues
    {n t : ℕ}
    (K : P32CoefficientMap n t) (H : P32CoefficientMap n n)
    (g : P32Vector t) (f : P32Vector n) (xNorm : ℝ)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i) :
    0 ∈ p32LinearizedValues K H g f xNorm := by
  refine ⟨0, 0, ?_, ?_⟩
  · constructor
    · intro j
      simpa using hg j
    · intro i
      simpa using hf i
  · have hresponse : p32LinearResponse K H 0 0 = 0 := by
      funext i
      simp [p32LinearResponse]
    rw [hresponse, norm_zero, zero_div]

private lemma p32_radius_div_le_attainable_value
    {n t : ℕ}
    (K : P32CoefficientMap n t) (H : P32CoefficientMap n n)
    (g : P32Vector t) (f : P32Vector n) (xNorm : ℝ)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i) (hx : 0 < xNorm)
    (i : Fin n) :
    ∃ q ∈ p32LinearizedValues K H g f xNorm,
      p32ConditionRadius K H g f i / xNorm ≤ q := by
  let dp : P32Vector t := fun j ↦ if 0 ≤ K i j then -g j else g j
  let db : P32Vector n := fun j ↦ if 0 ≤ H i j then f j else -f j
  have hadm : P32Admissible g f dp db := by
    constructor
    · intro j
      dsimp [dp]
      split_ifs <;> simp [abs_of_nonneg (hg j)]
    · intro j
      dsimp [db]
      split_ifs <;> simp [abs_of_nonneg (hf j)]
  have hH (j : Fin n) : H i j * db j = |H i j| * f j := by
    dsimp [db]
    split_ifs with h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h)]
      ring
  have hK (j : Fin t) : K i j * dp j = -(|K i j| * g j) := by
    dsimp [dp]
    split_ifs with h
    · rw [abs_of_nonneg h]
      ring
    · rw [abs_of_neg (lt_of_not_ge h)]
      ring
  have hresponse :
      p32LinearResponse K H dp db i = p32ConditionRadius K H g f i := by
    simp only [p32LinearResponse, p32ConditionRadius]
    calc
      (∑ j, H i j * db j) - ∑ j, K i j * dp j
          = (∑ j, |H i j| * f j) - ∑ j, -(|K i j| * g j) := by
              congr 1
              · exact Finset.sum_congr rfl fun j _ ↦ hH j
              · exact Finset.sum_congr rfl fun j _ ↦ hK j
      _ = (∑ j, |K i j| * g j) + ∑ j, |H i j| * f j := by
        rw [Finset.sum_neg_distrib]
        ring
  refine ⟨‖p32LinearResponse K H dp db‖ / xNorm, ?_, ?_⟩
  · exact ⟨dp, db, hadm, rfl⟩
  · apply (div_le_div_iff_of_pos_right hx).2
    calc
      p32ConditionRadius K H g f i
          = ‖p32LinearResponse K H dp db i‖ := by
              rw [Real.norm_eq_abs, hresponse,
                abs_of_nonneg (p32ConditionRadius_apply_nonneg K H g f hg hf i)]
      _ ≤ ‖p32LinearResponse K H dp db‖ :=
        norm_le_pi_norm (p32LinearResponse K H dp db) i

/-- P32-T3: the sharp structured first-order condition formula in (3.3)--(3.4). -/
theorem p32_t3_sharp_structured_condition_formula
    {n t : ℕ}
    (K : P32CoefficientMap n t) (H : P32CoefficientMap n n)
    (g : P32Vector t) (f : P32Vector n) (xNorm : ℝ)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i) (hx : 0 < xNorm) :
    p32LinearizedCondition K H g f xNorm =
      p32ConditionFormula K H g f xNorm := by
  -- PROOF_START P32-T3-H001
  unfold p32LinearizedCondition p32ConditionFormula
  have hzero : 0 ∈ p32LinearizedValues K H g f xNorm :=
    p32_zero_mem_linearizedValues K H g f xNorm hg hf
  have hupper : ∀ q ∈ p32LinearizedValues K H g f xNorm,
      q ≤ ‖p32ConditionRadius K H g f‖ / xNorm := by
    intro q hq
    rcases hq with ⟨dp, db, hadm, rfl⟩
    exact (div_le_div_iff_of_pos_right hx).2
      (p32LinearResponse_norm_le_radius_norm K H g f hg hf dp db hadm)
  have hbdd : BddAbove (p32LinearizedValues K H g f xNorm) :=
    ⟨‖p32ConditionRadius K H g f‖ / xNorm, hupper⟩
  apply le_antisymm
  · exact csSup_le ⟨0, hzero⟩ hupper
  · have hsup_nonneg :
        0 ≤ sSup (p32LinearizedValues K H g f xNorm) :=
      le_csSup hbdd hzero
    apply (div_le_iff₀ hx).2
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hsup_nonneg hx.le)).2
    intro i
    rw [Real.norm_eq_abs,
      abs_of_nonneg (p32ConditionRadius_apply_nonneg K H g f hg hf i)]
    rcases p32_radius_div_le_attainable_value K H g f xNorm hg hf hx i with
      ⟨q, hq, hiq⟩
    exact (div_le_iff₀ hx).1 (hiq.trans (le_csSup hbdd hq))

end HighamBench
