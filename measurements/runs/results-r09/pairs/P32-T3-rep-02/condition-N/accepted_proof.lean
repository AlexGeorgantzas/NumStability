import HighamBench.P32Definitions

namespace HighamBench

open scoped BigOperators

private lemma p32_conditionRadius_nonneg
    {n t : ℕ}
    (K : P32CoefficientMap n t) (H : P32CoefficientMap n n)
    (g : P32Vector t) (f : P32Vector n)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i) :
    ∀ i, 0 ≤ p32ConditionRadius K H g f i := by
  intro i
  apply add_nonneg
  · exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (abs_nonneg _) (hg j)
  · exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (abs_nonneg _) (hf j)

private lemma p32_linearResponse_abs_le_radius
    {n t : ℕ}
    (K : P32CoefficientMap n t) (H : P32CoefficientMap n n)
    (g : P32Vector t) (f : P32Vector n)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i)
    (dp : P32Vector t) (db : P32Vector n)
    (hadm : P32Admissible g f dp db) :
    ∀ i, |p32LinearResponse K H dp db i| ≤
      p32ConditionRadius K H g f i := by
  intro i
  have hHsum :
      |∑ j, H i j * db j| ≤ ∑ j, |H i j * db j| := by
    simpa using
      (Finset.abs_sum_le_sum_abs (fun j ↦ H i j * db j) Finset.univ)
  have hKsum :
      |∑ j, K i j * dp j| ≤ ∑ j, |K i j * dp j| := by
    simpa using
      (Finset.abs_sum_le_sum_abs (fun j ↦ K i j * dp j) Finset.univ)
  have hHbox :
      (∑ j, |H i j * db j|) ≤ ∑ j, |H i j| * f j := by
    apply Finset.sum_le_sum
    intro j _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hadm.2 j) (abs_nonneg _)
  have hKbox :
      (∑ j, |K i j * dp j|) ≤ ∑ j, |K i j| * g j := by
    apply Finset.sum_le_sum
    intro j _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hadm.1 j) (abs_nonneg _)
  change |∑ j, H i j * db j - ∑ j, K i j * dp j| ≤ _
  calc
    |∑ j, H i j * db j - ∑ j, K i j * dp j| ≤
        |∑ j, H i j * db j| + |∑ j, K i j * dp j| := abs_sub _ _
    _ ≤ (∑ j, |H i j * db j|) + ∑ j, |K i j * dp j| :=
      add_le_add hHsum hKsum
    _ ≤ (∑ j, |H i j| * f j) + ∑ j, |K i j| * g j :=
      add_le_add hHbox hKbox
    _ = p32ConditionRadius K H g f i := by
      simp only [p32ConditionRadius]
      ac_rfl

private lemma p32_linearResponse_norm_le_radius
    {n t : ℕ}
    (K : P32CoefficientMap n t) (H : P32CoefficientMap n n)
    (g : P32Vector t) (f : P32Vector n)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i)
    (dp : P32Vector t) (db : P32Vector n)
    (hadm : P32Admissible g f dp db) :
    ‖p32LinearResponse K H dp db‖ ≤ ‖p32ConditionRadius K H g f‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
  intro i
  rw [Real.norm_eq_abs]
  calc
    |p32LinearResponse K H dp db i| ≤ p32ConditionRadius K H g f i :=
      p32_linearResponse_abs_le_radius K H g f hg hf dp db hadm i
    _ = |p32ConditionRadius K H g f i| :=
      (abs_of_nonneg (p32_conditionRadius_nonneg K H g f hg hf i)).symm
    _ = ‖p32ConditionRadius K H g f i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖p32ConditionRadius K H g f‖ := norm_le_pi_norm _ i

private lemma p32_pi_norm_attained
    {n : ℕ} [Nonempty (Fin n)] (v : P32Vector n) :
    ∃ i, ‖v‖ = ‖v i‖ := by
  obtain ⟨i, _, hi⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin n))
      Finset.univ_nonempty (fun i ↦ ‖v i‖₊)
  refine ⟨i, ?_⟩
  rw [Pi.norm_def]
  calc
    (↑(Finset.univ.sup fun j ↦ ‖v j‖₊) : ℝ) = ↑‖v i‖₊ :=
      congrArg (fun z : NNReal ↦ (z : ℝ)) hi
    _ = ‖v i‖ := rfl

/-- P32-T3: the sharp structured first-order condition formula in (3.3)--(3.4). -/
theorem p32_t3_sharp_structured_condition_formula
    {n t : ℕ}
    (K : P32CoefficientMap n t) (H : P32CoefficientMap n n)
    (g : P32Vector t) (f : P32Vector n) (xNorm : ℝ)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i) (hx : 0 < xNorm) :
    p32LinearizedCondition K H g f xNorm =
      p32ConditionFormula K H g f xNorm := by
  -- PROOF_START P32-T3-H001
  classical
  have hupper : ∀ q ∈ p32LinearizedValues K H g f xNorm,
      q ≤ p32ConditionFormula K H g f xNorm := by
    intro q hq
    rcases hq with ⟨dp, db, hadm, rfl⟩
    unfold p32ConditionFormula
    exact div_le_div_of_nonneg_right
      (p32_linearResponse_norm_le_radius K H g f hg hf dp db hadm) hx.le
  have hnonempty : (p32LinearizedValues K H g f xNorm).Nonempty := by
    let dp : P32Vector t := 0
    let db : P32Vector n := 0
    have hadm : P32Admissible g f dp db := by
      constructor
      · intro j
        simpa [dp] using hg j
      · intro i
        simpa [db] using hf i
    exact ⟨‖p32LinearResponse K H dp db‖ / xNorm, dp, db, hadm, rfl⟩
  have hattain : p32ConditionFormula K H g f xNorm ∈
      p32LinearizedValues K H g f xNorm := by
    cases isEmpty_or_nonempty (Fin n) with
    | inl hempty =>
        letI := hempty
        let dp : P32Vector t := 0
        let db : P32Vector n := 0
        have hadm : P32Admissible g f dp db := by
          constructor
          · intro j
            simpa [dp] using hg j
          · intro i
            exact isEmptyElim i
        refine ⟨dp, db, hadm, ?_⟩
        unfold p32ConditionFormula
        have hresponse0 : p32LinearResponse K H dp db = (0 : P32Vector n) :=
          Subsingleton.elim _ _
        rw [hresponse0, norm_zero, zero_div]
        rw [Pi.norm_def]
        simp
    | inr hnonemptyFin =>
        letI := hnonemptyFin
        obtain ⟨i, hi⟩ :=
          p32_pi_norm_attained (p32ConditionRadius K H g f)
        have hri : ‖p32ConditionRadius K H g f‖ =
            p32ConditionRadius K H g f i := by
          calc
            ‖p32ConditionRadius K H g f‖ =
                ‖p32ConditionRadius K H g f i‖ := hi
            _ = |p32ConditionRadius K H g f i| := Real.norm_eq_abs _
            _ = p32ConditionRadius K H g f i :=
              abs_of_nonneg (p32_conditionRadius_nonneg K H g f hg hf i)
        let dp : P32Vector t := fun j ↦
          if 0 ≤ K i j then -g j else g j
        let db : P32Vector n := fun j ↦
          if 0 ≤ H i j then f j else -f j
        have hadm : P32Admissible g f dp db := by
          constructor
          · intro j
            dsimp [dp]
            split_ifs <;> simp [abs_of_nonneg (hg j)]
          · intro j
            dsimp [db]
            split_ifs <;> simp [abs_of_nonneg (hf j)]
        have hH : (∑ j, H i j * db j) = ∑ j, |H i j| * f j := by
          apply Finset.sum_congr rfl
          intro j _
          dsimp [db]
          split_ifs with hj
          · rw [abs_of_nonneg hj]
          · rw [abs_of_neg (lt_of_not_ge hj)]
            ring
        have hK : (∑ j, K i j * dp j) = -(∑ j, |K i j| * g j) := by
          calc
            (∑ j, K i j * dp j) = ∑ j, -(|K i j| * g j) := by
              apply Finset.sum_congr rfl
              intro j _
              dsimp [dp]
              split_ifs with hj
              · rw [abs_of_nonneg hj]
                ring
              · rw [abs_of_neg (lt_of_not_ge hj)]
                ring
            _ = -(∑ j, |K i j| * g j) := by
              rw [Finset.sum_neg_distrib]
        have hcoord : p32LinearResponse K H dp db i =
            p32ConditionRadius K H g f i := by
          change (∑ j, H i j * db j) - ∑ j, K i j * dp j = _
          rw [hH, hK]
          simp only [p32ConditionRadius]
          ring
        have hnorm : ‖p32LinearResponse K H dp db‖ =
            ‖p32ConditionRadius K H g f‖ := by
          apply le_antisymm
          · exact p32_linearResponse_norm_le_radius K H g f hg hf dp db hadm
          · calc
              ‖p32ConditionRadius K H g f‖ =
                  p32ConditionRadius K H g f i := hri
              _ = |p32LinearResponse K H dp db i| := by
                rw [hcoord, abs_of_nonneg
                  (p32_conditionRadius_nonneg K H g f hg hf i)]
              _ = ‖p32LinearResponse K H dp db i‖ := (Real.norm_eq_abs _).symm
              _ ≤ ‖p32LinearResponse K H dp db‖ := norm_le_pi_norm _ i
        refine ⟨dp, db, hadm, ?_⟩
        unfold p32ConditionFormula
        rw [hnorm]
  unfold p32LinearizedCondition
  apply le_antisymm
  · exact csSup_le hnonempty hupper
  · exact le_csSup ⟨p32ConditionFormula K H g f xNorm, hupper⟩ hattain

end HighamBench
