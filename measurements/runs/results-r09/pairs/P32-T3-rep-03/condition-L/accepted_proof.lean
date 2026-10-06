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
  have hR_nonneg (i : Fin n) : 0 ≤ R i := by
    dsimp [R, p32ConditionRadius]
    exact add_nonneg
      (Finset.sum_nonneg fun j _ ↦ mul_nonneg (abs_nonneg _) (hg j))
      (Finset.sum_nonneg fun j _ ↦ mul_nonneg (abs_nonneg _) (hf j))
  have hcomponent
      (dp : P32Vector t) (db : P32Vector n)
      (ha : P32Admissible g f dp db) (i : Fin n) :
      |p32LinearResponse K H dp db i| ≤ R i := by
    have hH :
        |∑ j, H i j * db j| ≤ ∑ j, |H i j| * f j := by
      calc
        |∑ j, H i j * db j| ≤ ∑ j, |H i j * db j| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j, |H i j| * |db j| := by
          apply Finset.sum_congr rfl
          intro j _
          rw [abs_mul]
        _ ≤ ∑ j, |H i j| * f j := by
          exact Finset.sum_le_sum fun j _ ↦
            mul_le_mul_of_nonneg_left (ha.2 j) (abs_nonneg _)
    have hK :
        |∑ j, K i j * dp j| ≤ ∑ j, |K i j| * g j := by
      calc
        |∑ j, K i j * dp j| ≤ ∑ j, |K i j * dp j| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j, |K i j| * |dp j| := by
          apply Finset.sum_congr rfl
          intro j _
          rw [abs_mul]
        _ ≤ ∑ j, |K i j| * g j := by
          exact Finset.sum_le_sum fun j _ ↦
            mul_le_mul_of_nonneg_left (ha.1 j) (abs_nonneg _)
    change |∑ j, H i j * db j - ∑ j, K i j * dp j| ≤ R i
    calc
      |∑ j, H i j * db j - ∑ j, K i j * dp j| ≤
          |∑ j, H i j * db j| + |∑ j, K i j * dp j| := abs_sub _ _
      _ ≤ (∑ j, |H i j| * f j) + ∑ j, |K i j| * g j :=
        add_le_add hH hK
      _ = R i := by
        dsimp [R, p32ConditionRadius]
        ac_rfl
  have hnorm
      (dp : P32Vector t) (db : P32Vector n)
      (ha : P32Admissible g f dp db) :
      ‖p32LinearResponse K H dp db‖ ≤ ‖R‖ := by
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg R)]
    intro i
    calc
      ‖p32LinearResponse K H dp db i‖ =
          |p32LinearResponse K H dp db i| := Real.norm_eq_abs _
      _ ≤ R i := hcomponent dp db ha i
      _ = ‖R i‖ := by rw [Real.norm_eq_abs, abs_of_nonneg (hR_nonneg i)]
      _ ≤ ‖R‖ := norm_le_pi_norm R i
  have hbound : ∀ q ∈ p32LinearizedValues K H g f xNorm,
      q ≤ p32ConditionFormula K H g f xNorm := by
    intro q hq
    rcases hq with ⟨dp, db, ha, rfl⟩
    dsimp [p32ConditionFormula]
    change ‖p32LinearResponse K H dp db‖ / xNorm ≤ ‖R‖ / xNorm
    exact div_le_div_of_nonneg_right (hnorm dp db ha) hx.le
  have hzero_mem : 0 ∈ p32LinearizedValues K H g f xNorm := by
    refine ⟨(fun _ ↦ 0), (fun _ ↦ 0), ?_, ?_⟩
    · constructor
      · intro j
        simpa using hg j
      · intro i
        simpa using hf i
    · have hz : p32LinearResponse K H (fun _ ↦ 0) (fun _ ↦ 0) = 0 := by
        ext i
        simp [p32LinearResponse]
      rw [hz]
      simp
  have hformula_mem :
      p32ConditionFormula K H g f xNorm ∈
        p32LinearizedValues K H g f xNorm := by
    cases isEmpty_or_nonempty (Fin n) with
    | inl hn =>
        have hR_zero : R = 0 := Subsingleton.elim _ _
        change ‖R‖ / xNorm ∈ p32LinearizedValues K H g f xNorm
        rw [hR_zero]
        simpa using hzero_mem
    | inr hn =>
        obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup
          (Finset.univ : Finset (Fin n)) Finset.univ_nonempty
          (fun i ↦ ‖R i‖₊)
        have hi_norm : ‖R‖ = ‖R i‖ := by
          rw [Pi.norm_def]
          exact congrArg ((↑) : NNReal → ℝ) hi
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
        have hHterm (j : Fin n) : H i j * db j = |H i j| * f j := by
          dsimp [db]
          split_ifs with hj
          · rw [abs_of_nonneg hj]
          · rw [abs_of_nonpos (le_of_not_ge hj)]
            ring
        have hKterm (j : Fin t) : K i j * dp j = -(|K i j| * g j) := by
          dsimp [dp]
          split_ifs with hj
          · rw [abs_of_nonneg hj]
            ring
          · rw [abs_of_nonpos (le_of_not_ge hj)]
            ring
        have hat_i : p32LinearResponse K H dp db i = R i := by
          dsimp [p32LinearResponse, R, p32ConditionRadius]
          simp_rw [hHterm, hKterm, Finset.sum_neg_distrib]
          ring
        have hnorm_eq : ‖p32LinearResponse K H dp db‖ = ‖R‖ := by
          apply le_antisymm (hnorm dp db hadm)
          calc
            ‖R‖ = ‖R i‖ := hi_norm
            _ = ‖p32LinearResponse K H dp db i‖ := by rw [hat_i]
            _ ≤ ‖p32LinearResponse K H dp db‖ :=
              norm_le_pi_norm (p32LinearResponse K H dp db) i
        refine ⟨dp, db, hadm, ?_⟩
        dsimp [p32ConditionFormula]
        exact congrArg (fun z : ℝ ↦ z / xNorm) hnorm_eq.symm
  unfold p32LinearizedCondition
  apply le_antisymm
  · exact csSup_le ⟨0, hzero_mem⟩ hbound
  · exact le_csSup ⟨p32ConditionFormula K H g f xNorm, hbound⟩ hformula_mem

end HighamBench
