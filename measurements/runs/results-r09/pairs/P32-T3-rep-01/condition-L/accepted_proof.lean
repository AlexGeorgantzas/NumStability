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
  cases n with
  | zero =>
      have hvalues : p32LinearizedValues K H g f xNorm = {0} := by
        ext q
        constructor
        · rintro ⟨dp, db, hadm, rfl⟩
          have hz : p32LinearResponse K H dp db = 0 := Subsingleton.elim _ _
          rw [hz, norm_zero, zero_div]
          exact Set.mem_singleton 0
        · intro hq
          have hq0 : q = 0 := by simpa using hq
          subst q
          refine ⟨(fun _ ↦ 0), (fun i ↦ Fin.elim0 i), ?_, ?_⟩
          · constructor
            · intro j
              simpa using hg j
            · intro i
              exact Fin.elim0 i
          · have hz : p32LinearResponse K H (fun _ ↦ 0)
                (fun i ↦ Fin.elim0 i) = 0 := Subsingleton.elim _ _
            rw [hz, norm_zero, zero_div]
      rw [p32LinearizedCondition, p32ConditionFormula, hvalues,
        csSup_singleton]
      have hz : p32ConditionRadius K H g f = 0 := Subsingleton.elim _ _
      rw [hz, norm_zero, zero_div]
  | succ n =>
      let R : P32Vector (n + 1) := p32ConditionRadius K H g f
      have hR_nonneg : ∀ i, 0 ≤ R i := by
        intro i
        exact add_nonneg
          (Finset.sum_nonneg fun j _ ↦ mul_nonneg (abs_nonneg _) (hg j))
          (Finset.sum_nonneg fun j _ ↦ mul_nonneg (abs_nonneg _) (hf j))
      have hresponse_le : ∀ dp db, P32Admissible g f dp db →
          ‖p32LinearResponse K H dp db‖ ≤ ‖R‖ := by
        intro dp db hadm
        apply (pi_norm_le_iff_of_nonneg (norm_nonneg R)).2
        intro i
        change |∑ j, H i j * db j - ∑ j, K i j * dp j| ≤ ‖R‖
        calc
          |∑ j, H i j * db j - ∑ j, K i j * dp j| ≤
              |∑ j, H i j * db j| + |∑ j, K i j * dp j| :=
            abs_sub _ _
          _ ≤ (∑ j, |H i j| * |db j|) +
                ∑ j, |K i j| * |dp j| := by
            apply add_le_add
            · simpa only [abs_mul] using
                (Finset.abs_sum_le_sum_abs (fun j ↦ H i j * db j) Finset.univ)
            · simpa only [abs_mul] using
                (Finset.abs_sum_le_sum_abs (fun j ↦ K i j * dp j) Finset.univ)
          _ ≤ (∑ j, |H i j| * f j) +
                ∑ j, |K i j| * g j := by
            apply add_le_add
            · exact Finset.sum_le_sum fun j _ ↦
                mul_le_mul_of_nonneg_left (hadm.2 j) (abs_nonneg _)
            · exact Finset.sum_le_sum fun j _ ↦
                mul_le_mul_of_nonneg_left (hadm.1 j) (abs_nonneg _)
          _ = R i := by
            simp only [R, p32ConditionRadius]
            ac_rfl
          _ ≤ ‖R‖ := by
            simpa only [Real.norm_eq_abs, abs_of_nonneg (hR_nonneg i)] using
              (norm_le_pi_norm R i)
      obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ
        Finset.univ_nonempty (fun i : Fin (n + 1) ↦ ‖R i‖₊)
      have hiR : ‖R‖ = R i := by
        calc
          ‖R‖ = (↑(‖R i‖₊) : ℝ) := by
            rw [Pi.norm_def]
            exact congrArg Subtype.val hi
          _ = R i := by
            rw [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg (hR_nonneg i)]
      let dp : P32Vector t := fun j ↦ if 0 ≤ K i j then -g j else g j
      let db : P32Vector (n + 1) :=
        fun j ↦ if 0 ≤ H i j then f j else -f j
      have hadm : P32Admissible g f dp db := by
        constructor
        · intro j
          by_cases hj : 0 ≤ K i j
          · simp [dp, hj, abs_of_nonneg (hg j)]
          · simp [dp, hj, abs_of_nonneg (hg j)]
        · intro j
          by_cases hj : 0 ≤ H i j
          · simp [db, hj, abs_of_nonneg (hf j)]
          · simp [db, hj, abs_of_nonneg (hf j)]
      have hH : ∀ j, H i j * db j = |H i j| * f j := by
        intro j
        by_cases hj : 0 ≤ H i j
        · simp only [db, if_pos hj, abs_of_nonneg hj]
        · have hj' : H i j < 0 := lt_of_not_ge hj
          simp only [db, if_neg hj, abs_of_neg hj']
          ring
      have hK : ∀ j, K i j * dp j = -(|K i j| * g j) := by
        intro j
        by_cases hj : 0 ≤ K i j
        · simp only [dp, if_pos hj, abs_of_nonneg hj]
          ring
        · have hj' : K i j < 0 := lt_of_not_ge hj
          simp only [dp, if_neg hj, abs_of_neg hj']
          ring
      have hcoord : p32LinearResponse K H dp db i = R i := by
        simp only [p32LinearResponse]
        rw [Finset.sum_congr rfl (fun j _ ↦ hH j),
          Finset.sum_congr rfl (fun j _ ↦ hK j), Finset.sum_neg_distrib]
        simp only [sub_neg_eq_add, R, p32ConditionRadius]
        ac_rfl
      have hresponse_eq : ‖p32LinearResponse K H dp db‖ = ‖R‖ := by
        apply le_antisymm (hresponse_le dp db hadm)
        rw [hiR]
        calc
          R i = ‖p32LinearResponse K H dp db i‖ := by
            rw [hcoord, Real.norm_eq_abs, abs_of_nonneg (hR_nonneg i)]
          _ ≤ ‖p32LinearResponse K H dp db‖ :=
            norm_le_pi_norm (p32LinearResponse K H dp db) i
      let S := p32LinearizedValues K H g f xNorm
      let kappa := ‖R‖ / xNorm
      have hkappa_mem : kappa ∈ S := by
        refine ⟨dp, db, hadm, ?_⟩
        simp only [kappa, hresponse_eq]
      have hupper : ∀ q, q ∈ S → q ≤ kappa := by
        intro q hq
        rcases hq with ⟨dp', db', hadm', rfl⟩
        exact (div_le_div_iff_of_pos_right hx).2 (hresponse_le dp' db' hadm')
      change sSup S = kappa
      exact le_antisymm (csSup_le ⟨kappa, hkappa_mem⟩ hupper)
        (le_csSup ⟨kappa, hupper⟩ hkappa_mem)

end HighamBench
