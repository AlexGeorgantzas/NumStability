import HighamBench.P32Definitions

namespace HighamBench

open scoped BigOperators

private lemma p32_radius_nonneg
    {n t : ℕ}
    (K : P32CoefficientMap n t) (H : P32CoefficientMap n n)
    (g : P32Vector t) (f : P32Vector n)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i) :
    ∀ i, 0 ≤ p32ConditionRadius K H g f i := by
  intro i
  rw [p32ConditionRadius]
  exact add_nonneg
    (Finset.sum_nonneg fun j _ ↦ mul_nonneg (abs_nonneg _) (hg j))
    (Finset.sum_nonneg fun j _ ↦ mul_nonneg (abs_nonneg _) (hf j))

private lemma p32_abs_apply_le_norm
    {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    |v i| ≤ ‖v‖ := by
  rw [Pi.norm_def]
  change ‖v i‖ ≤ ↑(Finset.univ.sup fun j ↦ ‖v j‖₊)
  exact_mod_cast
    Finset.le_sup (f := fun j ↦ ‖v j‖₊) (Finset.mem_univ i)

private lemma p32_response_norm_le_radius_norm
    {n t : ℕ}
    (K : P32CoefficientMap n t) (H : P32CoefficientMap n n)
    (g : P32Vector t) (f : P32Vector n)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i)
    (dp : P32Vector t) (db : P32Vector n)
    (hadm : P32Admissible g f dp db) :
    ‖p32LinearResponse K H dp db‖ ≤
      ‖p32ConditionRadius K H g f‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
  intro i
  rw [Real.norm_eq_abs]
  have hH :
      |∑ j, H i j * db j| ≤ ∑ j, |H i j| * f j := by
    calc
      |∑ j, H i j * db j| ≤ ∑ j, |H i j * db j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |H i j| * f j := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hadm.2 j) (abs_nonneg _)
  have hK :
      |∑ j, K i j * dp j| ≤ ∑ j, |K i j| * g j := by
    calc
      |∑ j, K i j * dp j| ≤ ∑ j, |K i j * dp j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |K i j| * g j := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hadm.1 j) (abs_nonneg _)
  have hpoint :
      |p32LinearResponse K H dp db i| ≤
        p32ConditionRadius K H g f i := by
    rw [p32LinearResponse, p32ConditionRadius]
    calc
      |(∑ j, H i j * db j) - ∑ j, K i j * dp j| ≤
          |∑ j, H i j * db j| + |∑ j, K i j * dp j| := abs_sub _ _
      _ ≤ (∑ j, |H i j| * f j) + ∑ j, |K i j| * g j :=
        add_le_add hH hK
      _ = (∑ j, |K i j| * g j) + ∑ j, |H i j| * f j := add_comm _ _
  exact hpoint.trans (by
    rw [← abs_of_nonneg (p32_radius_nonneg K H g f hg hf i)]
    exact p32_abs_apply_le_norm (p32ConditionRadius K H g f) i)

private lemma p32_exists_attaining_perturbation
    {n t : ℕ}
    (K : P32CoefficientMap n t) (H : P32CoefficientMap n n)
    (g : P32Vector t) (f : P32Vector n)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i) :
    ∃ dp db, P32Admissible g f dp db ∧
      ‖p32LinearResponse K H dp db‖ =
        ‖p32ConditionRadius K H g f‖ := by
  classical
  by_cases hn : Nonempty (Fin n)
  · letI := hn
    let r := p32ConditionRadius K H g f
    rcases Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
        (fun i ↦ ‖r i‖₊) with ⟨i, -, hi⟩
    have hri : 0 ≤ r i := p32_radius_nonneg K H g f hg hf i
    have hnormr : ‖r‖ = r i := by
      calc
        ‖r‖ = ↑(Finset.univ.sup fun j ↦ ‖r j‖₊) := Pi.norm_def r
        _ = ↑‖r i‖₊ := congrArg ((↑·) : NNReal → ℝ) hi
        _ = |r i| := Real.norm_eq_abs (r i)
        _ = r i := abs_of_nonneg hri
    let sgn : ℝ → ℝ := fun a ↦ if 0 ≤ a then 1 else -1
    have habs_sgn (a : ℝ) : |sgn a| = 1 := by
      by_cases ha : 0 ≤ a <;> simp [sgn, ha]
    have hmul_sgn (a : ℝ) : a * sgn a = |a| := by
      by_cases ha : 0 ≤ a
      · simp [sgn, ha, abs_of_nonneg ha]
      · have ha' : a ≤ 0 := le_of_not_ge ha
        simp [sgn, ha, abs_of_nonpos ha']
    let dp : P32Vector t := fun j ↦ -(sgn (K i j) * g j)
    let db : P32Vector n := fun j ↦ sgn (H i j) * f j
    have hadm : P32Admissible g f dp db := by
      constructor
      · intro j
        rw [show dp j = -(sgn (K i j) * g j) from rfl,
          abs_neg, abs_mul, habs_sgn, one_mul, abs_of_nonneg (hg j)]
      · intro j
        rw [show db j = sgn (H i j) * f j from rfl,
          abs_mul, habs_sgn, one_mul, abs_of_nonneg (hf j)]
    have hHsum :
        (∑ j, H i j * db j) = ∑ j, |H i j| * f j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show db j = sgn (H i j) * f j from rfl, ← mul_assoc,
        hmul_sgn]
    have hKsum :
        (∑ j, K i j * dp j) = -(∑ j, |K i j| * g j) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [show dp j = -(sgn (K i j) * g j) from rfl, mul_neg,
        ← mul_assoc, hmul_sgn]
    have hresp : p32LinearResponse K H dp db i = r i := by
      rw [p32LinearResponse, hHsum, hKsum]
      simp only [sub_neg_eq_add]
      rw [show r i =
          (∑ j, |K i j| * g j) + ∑ j, |H i j| * f j by
            rfl]
      exact add_comm _ _
    have hlower : ‖r‖ ≤ ‖p32LinearResponse K H dp db‖ := by
      rw [hnormr]
      have hc := p32_abs_apply_le_norm (p32LinearResponse K H dp db) i
      rw [hresp, abs_of_nonneg hri] at hc
      exact hc
    refine ⟨dp, db, hadm, le_antisymm ?_ hlower⟩
    exact p32_response_norm_le_radius_norm K H g f hg hf dp db hadm
  · have hfin : IsEmpty (Fin n) := not_nonempty_iff.mp hn
    letI := hfin
    refine ⟨0, 0, ?_, ?_⟩
    · constructor
      · intro j
        simpa using hg j
      · intro i
        exact isEmptyElim i
    · have hresponse : p32LinearResponse K H (0 : P32Vector t)
          (0 : P32Vector n) = 0 := Subsingleton.elim _ _
      have hradius : p32ConditionRadius K H g f = 0 := Subsingleton.elim _ _
      rw [hresponse, hradius]

/-- P32-T3: the sharp structured first-order condition formula in (3.3)--(3.4). -/
theorem p32_t3_sharp_structured_condition_formula
    {n t : ℕ}
    (K : P32CoefficientMap n t) (H : P32CoefficientMap n n)
    (g : P32Vector t) (f : P32Vector n) (xNorm : ℝ)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i) (hx : 0 < xNorm) :
    p32LinearizedCondition K H g f xNorm =
      p32ConditionFormula K H g f xNorm := by
  -- PROOF_START P32-T3-H001
  let S := p32LinearizedValues K H g f xNorm
  let C := p32ConditionFormula K H g f xNorm
  rcases p32_exists_attaining_perturbation K H g f hg hf with
    ⟨dp, db, hadm, hattain⟩
  have hCmem : C ∈ S := by
    refine ⟨dp, db, hadm, ?_⟩
    rw [show C = ‖p32ConditionRadius K H g f‖ / xNorm by rfl,
      hattain]
  have hupper : ∀ q : ℝ, q ∈ S → q ≤ C := by
    intro q hq
    rcases hq with ⟨dp', db', hadm', rfl⟩
    change ‖p32LinearResponse K H dp' db'‖ / xNorm ≤
      ‖p32ConditionRadius K H g f‖ / xNorm
    exact (div_le_div_iff_of_pos_right hx).2
      (p32_response_norm_le_radius_norm K H g f hg hf dp' db' hadm')
  have hbdd : BddAbove S := ⟨C, hupper⟩
  change sSup S = C
  exact le_antisymm (csSup_le ⟨C, hCmem⟩ hupper) (le_csSup hbdd hCmem)

end HighamBench
