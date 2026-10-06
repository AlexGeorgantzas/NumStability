import HighamBench.P32Definitions

namespace HighamBench

open scoped BigOperators

private lemma p32_norm_attained {m : ℕ} [Nonempty (Fin m)]
    (v : Fin m → ℝ) : ∃ i, ‖v‖ = ‖v i‖ := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ
    Finset.univ_nonempty (fun i => ‖v i‖₊)
  refine ⟨i, ?_⟩
  rw [Pi.norm_def]
  change (↑(Finset.univ.sup fun b => ‖v b‖₊) : ℝ) = (↑‖v i‖₊ : ℝ)
  exact congrArg (fun x : NNReal => (x : ℝ)) hi

private lemma p32_linearResponse_norm_le_radius_norm
    {n t : ℕ}
    (K : P32CoefficientMap n t) (H : P32CoefficientMap n n)
    (g : P32Vector t) (f : P32Vector n)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i)
    (dp : P32Vector t) (db : P32Vector n)
    (hadm : P32Admissible g f dp db) :
    ‖p32LinearResponse K H dp db‖ ≤ ‖p32ConditionRadius K H g f‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  rw [Real.norm_eq_abs]
  have hH :
      |∑ j, H i j * db j| ≤ ∑ j, |H i j| * f j := by
    calc
      |∑ j, H i j * db j| ≤ ∑ j, |H i j * db j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |H i j| * |db j| := by simp only [abs_mul]
      _ ≤ ∑ j, |H i j| * f j := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hadm.2 j) (abs_nonneg _)
  have hK :
      |∑ j, K i j * dp j| ≤ ∑ j, |K i j| * g j := by
    calc
      |∑ j, K i j * dp j| ≤ ∑ j, |K i j * dp j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |K i j| * |dp j| := by simp only [abs_mul]
      _ ≤ ∑ j, |K i j| * g j := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hadm.1 j) (abs_nonneg _)
  have hradius : 0 ≤ p32ConditionRadius K H g f i := by
    apply add_nonneg <;> apply Finset.sum_nonneg
    · intro j _
      exact mul_nonneg (abs_nonneg _) (hg j)
    · intro j _
      exact mul_nonneg (abs_nonneg _) (hf j)
  calc
    |p32LinearResponse K H dp db i| =
        |(∑ j, H i j * db j) - ∑ j, K i j * dp j| := rfl
    _ ≤ |∑ j, H i j * db j| + |∑ j, K i j * dp j| := by
      simpa [sub_eq_add_neg] using
        (abs_add_le (∑ j, H i j * db j) (-∑ j, K i j * dp j))
    _ ≤ (∑ j, |H i j| * f j) + ∑ j, |K i j| * g j :=
      add_le_add hH hK
    _ = p32ConditionRadius K H g f i := by
      simp only [p32ConditionRadius]
      ring
    _ = ‖p32ConditionRadius K H g f i‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hradius]
    _ ≤ ‖p32ConditionRadius K H g f‖ :=
      norm_le_pi_norm _ i

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
      simp only [p32LinearizedCondition, p32LinearizedValues,
        p32ConditionFormula, p32ConditionRadius, p32LinearResponse,
        P32Admissible, Pi.norm_def, Finset.univ_eq_empty, Finset.sup_empty,
        Finset.sum_empty]
      rw [show (⊥ : NNReal) = 0 from rfl]
      simp only [NNReal.coe_zero, zero_div]
      change sSup {q : ℝ | ∃ (dp : Fin t → ℝ) (db : Fin 0 → ℝ),
        ((∀ j, |dp j| ≤ g j) ∧ ∀ i, |db i| ≤ f i) ∧ q = 0} = 0
      have hset :
          {q : ℝ | ∃ (dp : Fin t → ℝ) (db : Fin 0 → ℝ),
            ((∀ j, |dp j| ≤ g j) ∧ ∀ i, |db i| ≤ f i) ∧ q = 0} = {0} := by
        ext q
        constructor
        · rintro ⟨_, _, _, rfl⟩
          simp
        · intro hq
          have hq0 : q = 0 := by simpa using hq
          subst q
          refine ⟨0, 0, ⟨fun j => by simpa using hg j, ?_⟩, rfl⟩
          intro i
          exact Fin.elim0 i
      rw [hset]
      exact csSup_singleton 0
  | succ n =>
      let R : P32Vector (n + 1) := p32ConditionRadius K H g f
      obtain ⟨i, hi⟩ := p32_norm_attained R
      let db : P32Vector (n + 1) :=
        fun j => if 0 ≤ H i j then f j else -f j
      let dp : P32Vector t :=
        fun j => if 0 ≤ K i j then -g j else g j
      have hdb : ∀ j, |db j| ≤ f j := by
        intro j
        dsimp [db]
        split_ifs <;> simp only [abs_neg, abs_of_nonneg (hf j), le_refl]
      have hdp : ∀ j, |dp j| ≤ g j := by
        intro j
        dsimp [dp]
        split_ifs <;> simp only [abs_neg, abs_of_nonneg (hg j), le_refl]
      have hadm : P32Admissible g f dp db := ⟨hdp, hdb⟩
      have hHterm : ∀ j, H i j * db j = |H i j| * f j := by
        intro j
        dsimp [db]
        split_ifs with h
        · rw [abs_of_nonneg h]
        · have hlt : H i j < 0 := lt_of_not_ge h
          rw [abs_of_neg hlt]
          ring
      have hKterm : ∀ j, K i j * dp j = -(|K i j| * g j) := by
        intro j
        dsimp [dp]
        split_ifs with h
        · rw [abs_of_nonneg h]
          ring
        · have hlt : K i j < 0 := lt_of_not_ge h
          rw [abs_of_neg hlt]
          ring
      have hresponse_i : p32LinearResponse K H dp db i = R i := by
        change (∑ j, H i j * db j) - (∑ j, K i j * dp j) =
          (∑ j, |K i j| * g j) + ∑ j, |H i j| * f j
        simp_rw [hHterm, hKterm]
        rw [Finset.sum_neg_distrib]
        ring
      have hnorm_upper :
          ‖p32LinearResponse K H dp db‖ ≤ ‖R‖ := by
        exact p32_linearResponse_norm_le_radius_norm K H g f hg hf dp db hadm
      have hnorm_lower :
          ‖R‖ ≤ ‖p32LinearResponse K H dp db‖ := by
        calc
          ‖R‖ = ‖R i‖ := hi
          _ = ‖p32LinearResponse K H dp db i‖ :=
            congrArg (fun z : ℝ => ‖z‖) hresponse_i.symm
          _ ≤ ‖p32LinearResponse K H dp db‖ :=
            norm_le_pi_norm _ i
      have hnorm : ‖p32LinearResponse K H dp db‖ = ‖R‖ :=
        le_antisymm hnorm_upper hnorm_lower
      have hformula_mem :
          ‖R‖ / xNorm ∈ p32LinearizedValues K H g f xNorm := by
        refine ⟨dp, db, hadm, ?_⟩
        exact congrArg (fun z : ℝ => z / xNorm) hnorm.symm
      have hupper : ∀ q : ℝ,
          q ∈ p32LinearizedValues K H g f xNorm → q ≤ ‖R‖ / xNorm := by
        intro q hq
        rcases hq with ⟨dp', db', hadm', rfl⟩
        apply (div_le_div_iff_of_pos_right hx).2
        exact p32_linearResponse_norm_le_radius_norm
          K H g f hg hf dp' db' hadm'
      have hbdd : BddAbove (p32LinearizedValues K H g f xNorm) :=
        ⟨‖R‖ / xNorm, hupper⟩
      change sSup (p32LinearizedValues K H g f xNorm) = ‖R‖ / xNorm
      exact le_antisymm
        (csSup_le ⟨‖R‖ / xNorm, hformula_mem⟩ hupper)
        (le_csSup hbdd hformula_mem)

end HighamBench
