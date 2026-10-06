import HighamBench.P32Definitions

namespace HighamBench

private lemma p32ConditionRadius_nonneg
    {n t : ℕ}
    (K : P32CoefficientMap n t) (H : P32CoefficientMap n n)
    (g : P32Vector t) (f : P32Vector n)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i) :
    ∀ i, 0 ≤ p32ConditionRadius K H g f i := by
  intro i
  apply add_nonneg
  · exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (abs_nonneg _) (hg j)
  · exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (abs_nonneg _) (hf j)

private lemma p32LinearResponse_norm_le_radius
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
    |∑ j, H i j * db j - ∑ j, K i j * dp j| ≤
        |∑ j, H i j * db j| + |∑ j, K i j * dp j| := abs_sub _ _
    _ ≤ (∑ j, |H i j * db j|) + ∑ j, |K i j * dp j| :=
      add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
    _ = (∑ j, |H i j| * |db j|) + ∑ j, |K i j| * |dp j| := by
      simp_rw [abs_mul]
    _ ≤ (∑ j, |H i j| * f j) + ∑ j, |K i j| * g j := by
      apply add_le_add
      · exact Finset.sum_le_sum fun j _ ↦
          mul_le_mul_of_nonneg_left (hadm.2 j) (abs_nonneg _)
      · exact Finset.sum_le_sum fun j _ ↦
          mul_le_mul_of_nonneg_left (hadm.1 j) (abs_nonneg _)
    _ = p32ConditionRadius K H g f i := by
      simp only [p32ConditionRadius]
      ring
    _ = ‖p32ConditionRadius K H g f i‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (p32ConditionRadius_nonneg K H g f hg hf i)]
    _ ≤ ‖p32ConditionRadius K H g f‖ :=
      norm_le_pi_norm (p32ConditionRadius K H g f) i

private lemma p32ConditionRadius_norm_attained
    {n t : ℕ}
    (K : P32CoefficientMap n t) (H : P32CoefficientMap n n)
    (g : P32Vector t) (f : P32Vector n)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i) :
    ∃ dp db, P32Admissible g f dp db ∧
      ‖p32LinearResponse K H dp db‖ = ‖p32ConditionRadius K H g f‖ := by
  classical
  cases n with
  | zero =>
      refine ⟨fun _ ↦ 0, fun i ↦ Fin.elim0 i, ?_, ?_⟩
      · constructor
        · intro j
          simpa using hg j
        · intro i
          exact Fin.elim0 i
      · simp [p32LinearResponse, p32ConditionRadius, Pi.norm_def]
  | succ n =>
      let R := p32ConditionRadius K H g f
      have hR : ∀ i, 0 ≤ R i := p32ConditionRadius_nonneg K H g f hg hf
      obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ
        Finset.univ_nonempty (fun i ↦ ‖R i‖₊)
      have hnormR : ‖R‖ = R i := by
        calc
          ‖R‖ = ↑(Finset.univ.sup fun k ↦ ‖R k‖₊) := Pi.norm_def R
          _ = (‖R i‖₊ : ℝ) := congrArg (fun x : NNReal ↦ (x : ℝ)) hi
          _ = ‖R i‖ := rfl
          _ = |R i| := Real.norm_eq_abs _
          _ = R i := abs_of_nonneg (hR i)
      let dp : P32Vector t := fun j ↦ if 0 ≤ K i j then -g j else g j
      let db : P32Vector (Nat.succ n) := fun j ↦ if 0 ≤ H i j then f j else -f j
      have hdp : ∀ j, |dp j| ≤ g j := by
        intro j
        dsimp [dp]
        split_ifs <;> simp [abs_of_nonneg (hg j)]
      have hdb : ∀ j, |db j| ≤ f j := by
        intro j
        dsimp [db]
        split_ifs <;> simp [abs_of_nonneg (hf j)]
      have hadm : P32Admissible g f dp db := ⟨hdp, hdb⟩
      have hH : ∀ j, H i j * db j = |H i j| * f j := by
        intro j
        by_cases h : 0 ≤ H i j
        · simp [db, h, abs_of_nonneg h]
        · have h' : H i j ≤ 0 := le_of_not_ge h
          rw [show db j = -f j by simp [db, h], abs_of_nonpos h']
          ring
      have hK : ∀ j, K i j * dp j = -(|K i j| * g j) := by
        intro j
        by_cases h : 0 ≤ K i j
        · rw [show dp j = -g j by simp [dp, h], abs_of_nonneg h]
          ring
        · have h' : K i j ≤ 0 := le_of_not_ge h
          rw [show dp j = g j by simp [dp, h], abs_of_nonpos h']
          ring
      have hsumH : (∑ j, H i j * db j) = ∑ j, |H i j| * f j :=
        Finset.sum_congr rfl fun j _ ↦ hH j
      have hsumK : (∑ j, K i j * dp j) = -(∑ j, |K i j| * g j) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ ↦ hK j
      have hresp : p32LinearResponse K H dp db i = R i := by
        simp only [p32LinearResponse]
        rw [hsumH, hsumK]
        dsimp [R, p32ConditionRadius]
        ring
      have hupper : ‖p32LinearResponse K H dp db‖ ≤ ‖R‖ :=
        p32LinearResponse_norm_le_radius K H g f hg hf dp db hadm
      have hlower : ‖R‖ ≤ ‖p32LinearResponse K H dp db‖ := by
        calc
          ‖R‖ = R i := hnormR
          _ = ‖p32LinearResponse K H dp db i‖ := by
            rw [Real.norm_eq_abs, hresp, abs_of_nonneg (hR i)]
          _ ≤ ‖p32LinearResponse K H dp db‖ :=
            norm_le_pi_norm (p32LinearResponse K H dp db) i
      exact ⟨dp, db, hadm, le_antisymm hupper hlower⟩

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
  obtain ⟨dp, db, hadm, hnorm⟩ :=
    p32ConditionRadius_norm_attained K H g f hg hf
  have hformula_mem : p32ConditionFormula K H g f xNorm ∈
      p32LinearizedValues K H g f xNorm := by
    refine ⟨dp, db, hadm, ?_⟩
    unfold p32ConditionFormula
    exact congrArg (fun z : ℝ ↦ z / xNorm) hnorm.symm
  have hvalues_le : ∀ q ∈ p32LinearizedValues K H g f xNorm,
      q ≤ p32ConditionFormula K H g f xNorm := by
    intro q hq
    obtain ⟨dp', db', hadm', rfl⟩ := hq
    unfold p32ConditionFormula
    exact div_le_div_of_nonneg_right
      (p32LinearResponse_norm_le_radius K H g f hg hf dp' db' hadm') hx.le
  have hbdd : BddAbove (p32LinearizedValues K H g f xNorm) :=
    ⟨p32ConditionFormula K H g f xNorm, hvalues_le⟩
  apply le_antisymm
  · exact csSup_le ⟨_, hformula_mem⟩ hvalues_le
  · exact le_csSup hbdd hformula_mem

end HighamBench
