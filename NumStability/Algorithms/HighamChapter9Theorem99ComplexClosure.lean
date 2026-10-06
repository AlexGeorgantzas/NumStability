import NumStability.Algorithms.HighamChapter9ComplexClosure

namespace NumStability

open scoped BigOperators

/-!
# Higham Theorem 9.9 over the complex source domain

This module closes the literal source statement of Theorem 9.9 over `ℂ`.
It constructs exact no-pivot LU factors from nonsingularity and row or column
diagonal dominance, and controls the complete equation-(9.5) reduced-matrix
history rather than only the final upper factor.  Every size hypothesis and
comparison uses the complex modulus `‖z‖`; no real-specialization assumption
is present.
-/

/-! ## Literal complex equation-(9.5) history -/

/-- The prefix product through the first `steps` pivots. -/
noncomputable def higham9_9_complexPrefixDot {n : ℕ}
    (L U : Fin n → Fin n → ℂ) (steps : ℕ) (i j : Fin n) : ℂ :=
  ∑ q : Fin n, if q.val < steps then L i q * U q j else 0

/-- **Equation (9.5), over `ℂ`.**  The entry remaining after `steps` exact
no-pivot elimination stages. -/
noncomputable def higham9_9_complexGEReducedEntry {n : ℕ}
    (A L U : Fin n → Fin n → ℂ) (steps : ℕ) (i j : Fin n) : ℂ :=
  A i j - higham9_9_complexPrefixDot L U steps i j

/-- The largest complex modulus in the complete equation-(9.5) history.
Stages are indexed by `Fin n`, so `n = 1` contains its initial stage. -/
noncomputable def higham9_9_complexNoPivotReducedEntryMax {n : ℕ}
    (hn : 0 < n) (A L U : Fin n → Fin n → ℂ) : ℝ :=
  Finset.sup' (Finset.univ : Finset (Fin n))
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
    (fun step : Fin n => higham9_13_complexMaxEntryNorm hn
      (fun i j => higham9_9_complexGEReducedEntry A L U step.val i j))

/-- The source growth factor formed from the full exact equation-(9.5)
reduced history. -/
noncomputable def higham9_9_complexNoPivotReducedGrowthFactor {n : ℕ}
    (hn : 0 < n) (A L U : Fin n → Fin n → ℂ) : ℝ :=
  higham9_9_complexNoPivotReducedEntryMax hn A L U /
    higham9_13_complexMaxEntryNorm hn A

/-! ## Row-dominant complex no-pivot LU construction -/

namespace Higham9Theorem99ComplexDirect

private theorem rowDiagDominant_zero_diag_row_zero {n : ℕ}
    {A : Fin n → Fin n → ℂ} (hDD : higham9_ComplexRowDiagDominant A)
    {i : Fin n} (hdiag : A i i = 0) :
    ∀ j : Fin n, A i j = 0 := by
  classical
  have hsum_le_zero :
      (∑ j : Fin n, if i = j then 0 else ‖A i j‖) ≤ 0 := by
    simpa [hdiag] using hDD i
  have hterm_nonneg :
      ∀ j ∈ (Finset.univ : Finset (Fin n)),
        0 ≤ (if i = j then 0 else ‖A i j‖) := by
    intro j _
    by_cases hij : i = j <;> simp [hij, norm_nonneg]
  have hsum_eq_zero :
      (∑ j : Fin n, if i = j then 0 else ‖A i j‖) = 0 :=
    le_antisymm hsum_le_zero (Finset.sum_nonneg hterm_nonneg)
  have hterms :=
    (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hsum_eq_zero
  intro j
  by_cases hij : i = j
  · subst j
    exact hdiag
  · have hterm : (if i = j then 0 else ‖A i j‖) = 0 :=
      hterms j (Finset.mem_univ j)
    exact norm_eq_zero.mp (by simpa [hij] using hterm)

/-- Nonsingularity makes every diagonal entry of a complex row-dominant
matrix nonzero. -/
theorem diag_ne_zero_of_rowDiagDominant_det_ne_zero {n : ℕ}
    {A : Fin n → Fin n → ℂ}
    (hDD : higham9_ComplexRowDiagDominant A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℂ) ≠ 0) :
    ∀ i : Fin n, A i i ≠ 0 := by
  intro i hdiag
  have hrow := rowDiagDominant_zero_diag_row_zero hDD hdiag
  exact hdet (Matrix.det_eq_zero_of_row_eq_zero i
    (fun j => by simpa [Matrix.of_apply] using hrow j))

/-- A first exact complex no-pivot Schur-complement step preserves row
diagonal dominance. -/
theorem rowDiagDominant_firstSchurComplement {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℂ}
    (hDD : higham9_ComplexRowDiagDominant A)
    (hpivot : A 0 0 ≠ 0) :
    higham9_ComplexRowDiagDominant
      (higham9_8_complexFirstSchurComplement A) := by
  classical
  intro i
  let S : Fin m → Fin m → ℂ := higham9_8_complexFirstSchurComplement A
  let offS : ℝ := ∑ j : Fin m, if i = j then 0 else ‖S i j‖
  let offA : ℝ := ∑ j : Fin m, if i = j then 0 else ‖A i.succ j.succ‖
  let pivotTail : ℝ := ∑ j : Fin m, ‖A 0 j.succ‖
  let ratio : ℝ := ‖A i.succ 0 / A 0 0‖
  let diagCorrection : ℝ := ratio * ‖A 0 i.succ‖
  have hsourceRow : ‖A i.succ 0‖ + offA ≤ ‖A i.succ i.succ‖ := by
    have h := hDD i.succ
    rw [Fin.sum_univ_succ] at h
    simpa [offA, Fin.succ_inj] using h
  have hpivotRow : pivotTail ≤ ‖A 0 0‖ := by
    have h := hDD (0 : Fin (m + 1))
    rw [Fin.sum_univ_succ] at h
    simpa [pivotTail] using h
  have hratioTail : ratio * pivotTail ≤ ‖A i.succ 0‖ := by
    calc
      ratio * pivotTail ≤ ratio * ‖A 0 0‖ :=
        mul_le_mul_of_nonneg_left hpivotRow (norm_nonneg _)
      _ = ‖A i.succ 0‖ := by
        dsimp [ratio]
        rw [norm_div]
        field_simp [norm_ne_zero_iff.mpr hpivot]
  have hentry : ∀ j : Fin m, i ≠ j →
      ‖S i j‖ ≤ ‖A i.succ j.succ‖ + ratio * ‖A 0 j.succ‖ := by
    intro j _hij
    have hfactor :
        A i.succ 0 * A 0 j.succ / A 0 0 =
          (A i.succ 0 / A 0 0) * A 0 j.succ := by ring
    calc
      ‖S i j‖ =
          ‖A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0‖ := rfl
      _ ≤ ‖A i.succ j.succ‖ +
          ‖A i.succ 0 * A 0 j.succ / A 0 0‖ := by
        simpa [sub_eq_add_neg, norm_neg] using
          norm_add_le (A i.succ j.succ)
            (-(A i.succ 0 * A 0 j.succ / A 0 0))
      _ = ‖A i.succ j.succ‖ + ratio * ‖A 0 j.succ‖ := by
        rw [hfactor, norm_mul]
  have hoffWithCorrection :
      offS + diagCorrection ≤ offA + ratio * pivotTail := by
    calc
      offS + diagCorrection =
          ∑ j : Fin m,
            ((if i = j then 0 else ‖S i j‖) +
              if i = j then diagCorrection else 0) := by
        rw [Finset.sum_add_distrib]
        simp [offS]
      _ ≤ ∑ j : Fin m,
            ((if i = j then 0 else ‖A i.succ j.succ‖) +
              ratio * ‖A 0 j.succ‖) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hij : i = j
        · subst j
          simp [diagCorrection]
        · simpa [hij] using hentry j hij
      _ = offA + ratio * pivotTail := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hoffToOldDiag : offS + diagCorrection ≤ ‖A i.succ i.succ‖ := by
    calc
      offS + diagCorrection ≤ offA + ratio * pivotTail := hoffWithCorrection
      _ ≤ offA + ‖A i.succ 0‖ := by linarith
      _ = ‖A i.succ 0‖ + offA := by ring
      _ ≤ ‖A i.succ i.succ‖ := hsourceRow
  have holdDiagToNew :
      ‖A i.succ i.succ‖ ≤ ‖S i i‖ + diagCorrection := by
    have heq :
        A i.succ i.succ =
          S i i + (A i.succ 0 / A 0 0) * A 0 i.succ := by
      dsimp [S]
      simp only [higham9_8_complexFirstSchurComplement]
      ring
    calc
      ‖A i.succ i.succ‖ =
          ‖S i i + (A i.succ 0 / A 0 0) * A 0 i.succ‖ := by rw [heq]
      _ ≤ ‖S i i‖ + ‖(A i.succ 0 / A 0 0) * A 0 i.succ‖ :=
        norm_add_le _ _
      _ = ‖S i i‖ + diagCorrection := by rw [norm_mul]
  change offS ≤ ‖S i i‖
  linarith

/-- Assembling the first pivot row over a row-dominant trailing upper factor
preserves complex row diagonal dominance. -/
theorem complexLUFirstStepU_rowDiagDominant {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℂ}
    {U₁ : Fin m → Fin m → ℂ}
    (hA : higham9_ComplexRowDiagDominant A)
    (hU₁ : higham9_ComplexRowDiagDominant U₁) :
    higham9_ComplexRowDiagDominant
      (higham9_8_complexLUFirstStepU A U₁) := by
  intro i
  refine Fin.cases ?_ (fun q => ?_) i
  · simpa [higham9_8_complexLUFirstStepU] using hA (0 : Fin (m + 1))
  · have h := hU₁ q
    rw [Fin.sum_univ_succ]
    simpa [higham9_8_complexLUFirstStepU, Fin.succ_inj] using h

/-- Direct exact complex no-pivot LU construction.  Besides the LU
certificate it retains row dominance of `U` and nonzero pivots, the two
invariants needed for the literal growth history and the transpose bridge. -/
theorem rowDiagDominant_exists_exactNoPivotLU_rowUpper :
    ∀ n : ℕ, ∀ A : Fin n → Fin n → ℂ,
      higham9_ComplexRowDiagDominant A →
      Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℂ) ≠ 0 →
      ∃ L U : Fin n → Fin n → ℂ,
        higham9_8_ComplexLUFactSpec n A L U ∧
        higham9_ComplexRowDiagDominant U ∧
        (∀ i : Fin n, U i i ≠ 0) := by
  intro n
  induction n with
  | zero =>
      intro A _hDD _hdet
      refine ⟨A, A, ?_, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> intro i
        all_goals exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ m ih =>
      intro A hDD hdet
      have hpivot : A 0 0 ≠ 0 :=
        (diag_ne_zero_of_rowDiagDominant_det_ne_zero hDD hdet) 0
      let S : Fin m → Fin m → ℂ := higham9_8_complexFirstSchurComplement A
      have hSDD : higham9_ComplexRowDiagDominant S := by
        simpa [S] using rowDiagDominant_firstSchurComplement hDD hpivot
      have hSdet :
          Matrix.det (Matrix.of S : Matrix (Fin m) (Fin m) ℂ) ≠ 0 := by
        simpa [S] using
          higham9_8_complexFirstSchurComplement_det_ne_zero A hpivot hdet
      obtain ⟨L₁, U₁, hLU₁, hU₁Row, hU₁diag⟩ := ih S hSDD hSdet
      let L := higham9_8_complexLUFirstStepL A L₁
      let U := higham9_8_complexLUFirstStepU A U₁
      refine ⟨L, U, ?_, ?_, ?_⟩
      · simpa [L, U, S] using
          higham9_8_complexLUFactSpec_of_firstSchurComplement_explicit
            hpivot hLU₁
      · simpa [U] using complexLUFirstStepU_rowDiagDominant hDD hU₁Row
      · intro i
        refine Fin.cases ?_ (fun q => ?_) i
        · simpa [U, higham9_8_complexLUFirstStepU] using hpivot
        · simpa [U, higham9_8_complexLUFirstStepU] using hU₁diag q

/-! ## Direct reduced-history estimate -/

noncomputable def upperTailMass {n : ℕ}
    (U : Fin n → Fin n → ℂ) (q : Fin n) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => k ≤ j.val), ‖U q j‖

noncomputable def eliminatedTailBudget {n : ℕ}
    (L U : Fin n → Fin n → ℂ) (i : Fin n) (k : ℕ) : ℝ :=
  ∑ q ∈ Finset.univ.filter (fun q : Fin n => q.val < k),
    ‖L i q‖ * upperTailMass U q k

noncomputable def sourcePrefixMass {n : ℕ}
    (A : Fin n → Fin n → ℂ) (i : Fin n) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k), ‖A i j‖

lemma upperTailMass_succ {n : ℕ}
    (U : Fin n → Fin n → ℂ) (q : Fin n) (k : ℕ) (hk : k < n) :
    upperTailMass U q k = ‖U q ⟨k, hk⟩‖ + upperTailMass U q (k + 1) := by
  classical
  let p : Fin n := ⟨k, hk⟩
  have hset :
      Finset.univ.filter (fun j : Fin n => k ≤ j.val) =
        insert p (Finset.univ.filter (fun j : Fin n => k + 1 ≤ j.val)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hkj
      by_cases hj : j = p
      · exact Or.inl hj
      · right
        have hne : j.val ≠ k := by
          intro h
          exact hj (Fin.ext (by simpa [p] using h))
        omega
    · rintro (rfl | h)
      · simp [p]
      · omega
  have hpnot : p ∉ Finset.univ.filter (fun j : Fin n => k + 1 ≤ j.val) := by
    simp [p]
  unfold upperTailMass
  rw [hset, Finset.sum_insert hpnot]

lemma sourcePrefixMass_succ {n : ℕ}
    (A : Fin n → Fin n → ℂ) (i : Fin n) (k : ℕ) (hk : k < n) :
    sourcePrefixMass A i (k + 1) =
      sourcePrefixMass A i k + ‖A i ⟨k, hk⟩‖ := by
  classical
  let p : Fin n := ⟨k, hk⟩
  have hset :
      Finset.univ.filter (fun j : Fin n => j.val < k + 1) =
        insert p (Finset.univ.filter (fun j : Fin n => j.val < k)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hj
      by_cases hjp : j = p
      · exact Or.inl hjp
      · right
        have hne : j.val ≠ k := by
          intro h
          exact hjp (Fin.ext (by simpa [p] using h))
        omega
    · rintro (rfl | h)
      · simp [p]
      · omega
  have hpnot : p ∉ Finset.univ.filter (fun j : Fin n => j.val < k) := by
    simp [p]
  unfold sourcePrefixMass
  rw [hset, Finset.sum_insert hpnot, add_comm]

lemma eliminatedTailBudget_succ {n : ℕ}
    (L U : Fin n → Fin n → ℂ) (i : Fin n) (k : ℕ) (hk : k < n) :
    eliminatedTailBudget L U i (k + 1) =
      (∑ q ∈ Finset.univ.filter (fun q : Fin n => q.val < k),
        ‖L i q‖ * upperTailMass U q (k + 1)) +
      ‖L i ⟨k, hk⟩‖ * upperTailMass U ⟨k, hk⟩ (k + 1) := by
  classical
  let p : Fin n := ⟨k, hk⟩
  have hset :
      Finset.univ.filter (fun q : Fin n => q.val < k + 1) =
        insert p (Finset.univ.filter (fun q : Fin n => q.val < k)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hq
      by_cases hqp : q = p
      · exact Or.inl hqp
      · right
        have hne : q.val ≠ k := by
          intro h
          exact hqp (Fin.ext (by simpa [p] using h))
        omega
    · rintro (rfl | h)
      · simp [p]
      · omega
  have hpnot : p ∉ Finset.univ.filter (fun q : Fin n => q.val < k) := by
    simp [p]
  unfold eliminatedTailBudget
  rw [hset, Finset.sum_insert hpnot, add_comm]

lemma upper_offdiag_sum_eq_strictUpper {n : ℕ}
    (U : Fin n → Fin n → ℂ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (i : Fin n) :
    (∑ j : Fin n, if i = j then 0 else ‖U i j‖) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), ‖U i j‖ := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j.val < i.val
  · have hij : i ≠ j := Fin.ne_of_val_ne (by omega)
    simp [hij, hUT i j hji]
  · by_cases hij : i = j
    · subst j
      simp
    · have hijv : i.val < j.val := by
        have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
        omega
      simp [hij, hijv]

lemma upperTailMass_le_diag {n : ℕ}
    {U : Fin n → Fin n → ℂ}
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hRow : higham9_ComplexRowDiagDominant U)
    (q : Fin n) (k : ℕ) (hqk : q.val < k) :
    upperTailMass U q k ≤ ‖U q q‖ := by
  classical
  have hsubset :
      Finset.univ.filter (fun j : Fin n => k ≤ j.val) ⊆
        Finset.univ.filter (fun j : Fin n => q.val < j.val) := by
    intro j hj
    have hjk := (Finset.mem_filter.mp hj).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_lt_of_le hqk hjk⟩
  have htail_le :
      upperTailMass U q k ≤
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => q.val < j.val), ‖U q j‖ := by
    unfold upperTailMass
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (by intro j _hj _hjnot; exact norm_nonneg (U q j))
  calc
    upperTailMass U q k
        ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin n => q.val < j.val),
            ‖U q j‖ := htail_le
    _ = ∑ j : Fin n, (if q = j then 0 else ‖U q j‖) :=
      (upper_offdiag_sum_eq_strictUpper U hUT q).symm
    _ ≤ ‖U q q‖ := hRow q

lemma complexPrefixDot_norm_le_prefixProductNorm {n : ℕ}
    (L U : Fin n → Fin n → ℂ) (i j : Fin n) (steps : ℕ) :
    ‖higham9_9_complexPrefixDot L U steps i j‖ ≤
      ∑ q ∈ Finset.univ.filter (fun q : Fin n => q.val < steps),
        ‖L i q‖ * ‖U q j‖ := by
  classical
  unfold higham9_9_complexPrefixDot
  have hsum :
      ‖∑ q : Fin n, if q.val < steps then L i q * U q j else 0‖ ≤
        ∑ q : Fin n, ‖if q.val < steps then L i q * U q j else 0‖ := by
    simpa using
      (norm_sum_le (s := (Finset.univ : Finset (Fin n)))
        (f := fun q : Fin n => if q.val < steps then L i q * U q j else 0))
  calc
    ‖∑ q : Fin n, if q.val < steps then L i q * U q j else 0‖
        ≤ ∑ q : Fin n, ‖if q.val < steps then L i q * U q j else 0‖ := hsum
    _ = ∑ q : Fin n,
          if q.val < steps then ‖L i q‖ * ‖U q j‖ else 0 := by
      apply Finset.sum_congr rfl
      intro q _hq
      by_cases hqk : q.val < steps <;> simp [hqk]
    _ = ∑ q ∈ Finset.univ.filter (fun q : Fin n => q.val < steps),
          ‖L i q‖ * ‖U q j‖ := by
      simp [Finset.sum_filter]

lemma source_eq_prefix_add_lowerPivot {n : ℕ}
    {A L U : Fin n → Fin n → ℂ}
    (hLU : higham9_8_ComplexLUFactSpec n A L U)
    (i k : Fin n) :
    A i k = higham9_9_complexPrefixDot L U k.val i k + L i k * U k k := by
  rw [← hLU.product_eq i k]
  unfold higham9_9_complexPrefixDot
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun q : Fin n => q.val < k.val)
    (fun q : Fin n => L i q * U q k)]
  congr 1
  · simp [Finset.sum_filter]
  · rw [Finset.sum_eq_single k]
    · intro q hq hqk
      have hnotlt : ¬ q.val < k.val := (Finset.mem_filter.mp hq).2
      have hle : k.val ≤ q.val := Nat.le_of_not_gt hnotlt
      have hne_val : k.val ≠ q.val := by
        intro hval
        exact hqk (Fin.ext hval.symm)
      have hkq : k.val < q.val := lt_of_le_of_ne hle hne_val
      rw [hLU.U_lower_zero q k hkq, mul_zero]
    · intro hk_not_mem
      exact (hk_not_mem (by simp)).elim

lemma complexPrefixDot_eq_source_of_row_or_col_eliminated {n : ℕ}
    {A L U : Fin n → Fin n → ℂ}
    (hLU : higham9_8_ComplexLUFactSpec n A L U)
    (i j : Fin n) (steps : ℕ)
    (helim : i.val < steps ∨ j.val < steps) :
    higham9_9_complexPrefixDot L U steps i j = A i j := by
  classical
  rw [← hLU.product_eq i j]
  unfold higham9_9_complexPrefixDot
  apply Finset.sum_congr rfl
  intro q _hq
  by_cases hqk : q.val < steps
  · simp [hqk]
  · have hkq : steps ≤ q.val := Nat.le_of_not_gt hqk
    rcases helim with hik | hjk
    · have hiq : i.val < q.val := lt_of_lt_of_le hik hkq
      simp [hqk, hLU.L_upper_zero i q hiq]
    · have hjq : j.val < q.val := lt_of_lt_of_le hjk hkq
      simp [hqk, hLU.U_lower_zero q j hjq]

/-- The eliminated-row contribution to the still-active tail is paid for by
source entries already left behind in the same row. -/
theorem eliminatedTailBudget_le_sourcePrefixMass {n : ℕ}
    {A L U : Fin n → Fin n → ℂ}
    (hLU : higham9_8_ComplexLUFactSpec n A L U)
    (hURow : higham9_ComplexRowDiagDominant U)
    (i : Fin n) :
    ∀ k : ℕ, k ≤ n →
      eliminatedTailBudget L U i k ≤ sourcePrefixMass A i k := by
  intro k hk
  induction k with
  | zero =>
      simp [eliminatedTailBudget, sourcePrefixMass]
  | succ k ih =>
      have hklt : k < n := Nat.lt_of_succ_le hk
      let p : Fin n := ⟨k, hklt⟩
      let oldTail : ℝ :=
        ∑ q ∈ Finset.univ.filter (fun q : Fin n => q.val < k),
          ‖L i q‖ * upperTailMass U q (k + 1)
      let pivotColumnMass : ℝ :=
        ∑ q ∈ Finset.univ.filter (fun q : Fin n => q.val < k),
          ‖L i q‖ * ‖U q p‖
      have hdecompose :
          oldTail + pivotColumnMass = eliminatedTailBudget L U i k := by
        dsimp [oldTail, pivotColumnMass]
        rw [← Finset.sum_add_distrib]
        unfold eliminatedTailBudget
        apply Finset.sum_congr rfl
        intro q _hq
        have htail := upperTailMass_succ U q k hklt
        have hp : (⟨k, hklt⟩ : Fin n) = p := rfl
        rw [hp] at htail
        rw [htail]
        ring
      have htailPivot : upperTailMass U p (k + 1) ≤ ‖U p p‖ := by
        apply upperTailMass_le_diag hLU.U_lower_zero hURow
        simp [p]
      have hprefixNorm :
          ‖higham9_9_complexPrefixDot L U p.val i p‖ ≤ pivotColumnMass := by
        simpa [pivotColumnMass, p] using
          complexPrefixDot_norm_le_prefixProductNorm L U i p p.val
      have hsource := source_eq_prefix_add_lowerPivot hLU i p
      have hpivotEq :
          L i p * U p p = A i p - higham9_9_complexPrefixDot L U p.val i p := by
        rw [hsource]
        ring
      have hpivotProduct :
          ‖L i p‖ * ‖U p p‖ ≤ ‖A i p‖ + pivotColumnMass := by
        calc
          ‖L i p‖ * ‖U p p‖ = ‖L i p * U p p‖ := (norm_mul _ _).symm
          _ = ‖A i p - higham9_9_complexPrefixDot L U p.val i p‖ := by
            rw [hpivotEq]
          _ ≤ ‖A i p‖ + ‖higham9_9_complexPrefixDot L U p.val i p‖ := by
            simpa [sub_eq_add_neg, norm_neg] using
              norm_add_le (A i p) (-(higham9_9_complexPrefixDot L U p.val i p))
          _ ≤ ‖A i p‖ + pivotColumnMass :=
            add_le_add (le_refl _) hprefixNorm
      have hnewTerm :
          ‖L i p‖ * upperTailMass U p (k + 1) ≤
            ‖A i p‖ + pivotColumnMass :=
        le_trans
          (mul_le_mul_of_nonneg_left htailPivot (norm_nonneg (L i p)))
          hpivotProduct
      rw [eliminatedTailBudget_succ L U i k hklt]
      calc
        oldTail + ‖L i p‖ * upperTailMass U p (k + 1)
            ≤ oldTail + (‖A i p‖ + pivotColumnMass) :=
              add_le_add (le_refl oldTail) hnewTerm
        _ = (oldTail + pivotColumnMass) + ‖A i p‖ := by ring
        _ = eliminatedTailBudget L U i k + ‖A i p‖ := by rw [hdecompose]
        _ ≤ sourcePrefixMass A i k + ‖A i p‖ :=
          add_le_add (ih (Nat.le_of_lt hklt)) (le_refl _)
        _ = sourcePrefixMass A i (k + 1) := by
          simpa [p] using (sourcePrefixMass_succ A i k hklt).symm

lemma complexPrefixDot_norm_le_eliminatedTailBudget {n : ℕ}
    (L U : Fin n → Fin n → ℂ) (i j : Fin n) (steps : ℕ)
    (hsj : steps ≤ j.val) :
    ‖higham9_9_complexPrefixDot L U steps i j‖ ≤
      eliminatedTailBudget L U i steps := by
  classical
  refine le_trans
    (complexPrefixDot_norm_le_prefixProductNorm L U i j steps) ?_
  unfold eliminatedTailBudget
  apply Finset.sum_le_sum
  intro q hq
  have hjmem :
      j ∈ Finset.univ.filter (fun x : Fin n => steps ≤ x.val) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsj⟩
  have hentry : ‖U q j‖ ≤ upperTailMass U q steps := by
    unfold upperTailMass
    exact Finset.single_le_sum
      (fun x _hx => norm_nonneg (U q x)) hjmem
  exact mul_le_mul_of_nonneg_left hentry (norm_nonneg (L i q))

lemma sourcePrefixMass_le_complexMaxEntryNorm {n : ℕ}
    (hn : 0 < n) {A : Fin n → Fin n → ℂ}
    (hRow : higham9_ComplexRowDiagDominant A)
    (i : Fin n) (k : ℕ) (hki : k ≤ i.val) :
    sourcePrefixMass A i k ≤ higham9_13_complexMaxEntryNorm hn A := by
  classical
  let S := Finset.univ.filter (fun j : Fin n => j.val < k)
  have heq :
      sourcePrefixMass A i k =
        ∑ j ∈ S, (if i = j then 0 else ‖A i j‖) := by
    unfold sourcePrefixMass
    apply Finset.sum_congr rfl
    intro j hj
    have hjk : j.val < k := (Finset.mem_filter.mp hj).2
    have hji : j ≠ i := by
      intro h
      subst j
      omega
    have hij : i ≠ j := Ne.symm hji
    simp [hij]
  have hprefix_le_offdiag :
      (∑ j ∈ S, (if i = j then 0 else ‖A i j‖)) ≤
        ∑ j : Fin n, (if i = j then 0 else ‖A i j‖) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro j _hj; exact Finset.mem_univ j)
      (by
        intro j _hjuniv _hjnot
        by_cases hij : i = j <;> simp [hij, norm_nonneg])
  calc
    sourcePrefixMass A i k
        = ∑ j ∈ S, (if i = j then 0 else ‖A i j‖) := heq
    _ ≤ ∑ j : Fin n, (if i = j then 0 else ‖A i j‖) :=
      hprefix_le_offdiag
    _ ≤ ‖A i i‖ := hRow i
    _ ≤ higham9_13_complexMaxEntryNorm hn A :=
      higham9_13_entry_norm_le_complexMaxEntryNorm hn A i i

/-- Every exact equation-(9.5) reduced entry associated with a row-dominant
complex LU certificate is at most twice the source maximum. -/
theorem reducedEntry_norm_le_two_complexMaxEntryNorm {n : ℕ} (hn : 0 < n)
    {A L U : Fin n → Fin n → ℂ}
    (hRow : higham9_ComplexRowDiagDominant A)
    (hLU : higham9_8_ComplexLUFactSpec n A L U)
    (hURow : higham9_ComplexRowDiagDominant U)
    (step i j : Fin n) :
    ‖higham9_9_complexGEReducedEntry A L U step.val i j‖ ≤
      2 * higham9_13_complexMaxEntryNorm hn A := by
  by_cases hi : step.val ≤ i.val
  · by_cases hj : step.val ≤ j.val
    · have hprefixBudget :
          ‖higham9_9_complexPrefixDot L U step.val i j‖ ≤
            eliminatedTailBudget L U i step.val :=
        complexPrefixDot_norm_le_eliminatedTailBudget L U i j step.val hj
      have hbudgetSource :
          eliminatedTailBudget L U i step.val ≤ sourcePrefixMass A i step.val :=
        eliminatedTailBudget_le_sourcePrefixMass
          hLU hURow i step.val (Nat.le_of_lt step.isLt)
      have hsourceMax :
          sourcePrefixMass A i step.val ≤ higham9_13_complexMaxEntryNorm hn A :=
        sourcePrefixMass_le_complexMaxEntryNorm hn hRow i step.val hi
      unfold higham9_9_complexGEReducedEntry
      calc
        ‖A i j - higham9_9_complexPrefixDot L U step.val i j‖
            ≤ ‖A i j‖ + ‖higham9_9_complexPrefixDot L U step.val i j‖ := by
              simpa [sub_eq_add_neg, norm_neg] using
                norm_add_le (A i j)
                  (-(higham9_9_complexPrefixDot L U step.val i j))
        _ ≤ higham9_13_complexMaxEntryNorm hn A +
              eliminatedTailBudget L U i step.val :=
          add_le_add
            (higham9_13_entry_norm_le_complexMaxEntryNorm hn A i j)
            hprefixBudget
        _ ≤ higham9_13_complexMaxEntryNorm hn A + sourcePrefixMass A i step.val :=
          add_le_add (le_refl _) hbudgetSource
        _ ≤ higham9_13_complexMaxEntryNorm hn A +
              higham9_13_complexMaxEntryNorm hn A :=
          add_le_add (le_refl _) hsourceMax
        _ = 2 * higham9_13_complexMaxEntryNorm hn A := by ring
    · have hjlt : j.val < step.val := Nat.lt_of_not_ge hj
      have hpref := complexPrefixDot_eq_source_of_row_or_col_eliminated
        hLU i j step.val (Or.inr hjlt)
      simp [higham9_9_complexGEReducedEntry, hpref,
        mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
          (higham9_13_complexMaxEntryNorm_nonneg hn A)]
  · have hilt : i.val < step.val := Nat.lt_of_not_ge hi
    have hpref := complexPrefixDot_eq_source_of_row_or_col_eliminated
      hLU i j step.val (Or.inl hilt)
    simp [higham9_9_complexGEReducedEntry, hpref,
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (higham9_13_complexMaxEntryNorm_nonneg hn A)]

/-- Direct scalar proof of the source full reduced-history growth bound. -/
theorem noPivotReducedGrowthFactor_le_two {n : ℕ} (hn : 0 < n)
    {A L U : Fin n → Fin n → ℂ}
    (hRow : higham9_ComplexRowDiagDominant A)
    (hLU : higham9_8_ComplexLUFactSpec n A L U)
    (hURow : higham9_ComplexRowDiagDominant U)
    (hAmax : 0 < higham9_13_complexMaxEntryNorm hn A) :
    higham9_9_complexNoPivotReducedGrowthFactor hn A L U ≤ 2 := by
  have hentryMax :
      higham9_9_complexNoPivotReducedEntryMax hn A L U ≤
        2 * higham9_13_complexMaxEntryNorm hn A := by
    unfold higham9_9_complexNoPivotReducedEntryMax
    apply Finset.sup'_le
    intro step _hstep
    apply higham9_13_complexMaxEntryNorm_le_of_entry_le_bound
    intro i j
    exact reducedEntry_norm_le_two_complexMaxEntryNorm
      hn hRow hLU hURow step i j
  unfold higham9_9_complexNoPivotReducedGrowthFactor
  rw [div_le_iff₀ hAmax]
  simpa [mul_comm] using hentryMax

end Higham9Theorem99ComplexDirect

/-! ## Transpose/rescaling bridge and final-factor consequences -/

/-- Complex max-entry modulus is invariant under the function-shaped
transpose. -/
theorem higham9_9_complex_maxEntryNorm_transpose {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℂ) :
    higham9_13_complexMaxEntryNorm hn (higham9_complexTranspose A) =
      higham9_13_complexMaxEntryNorm hn A := by
  apply le_antisymm
  · apply higham9_13_complexMaxEntryNorm_le_of_entry_le_bound
    intro i j
    exact higham9_13_entry_norm_le_complexMaxEntryNorm hn A j i
  · apply higham9_13_complexMaxEntryNorm_le_of_entry_le_bound
    intro i j
    simpa [higham9_complexTranspose] using
      higham9_13_entry_norm_le_complexMaxEntryNorm hn
        (higham9_complexTranspose A) j i

/-- Transpose preserves nonsingularity over `ℂ`. -/
theorem higham9_9_complex_transpose_det_ne_zero {n : ℕ}
    (A : Fin n → Fin n → ℂ)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℂ) ≠ 0) :
    Matrix.det
      (Matrix.of (higham9_complexTranspose A) : Matrix (Fin n) (Fin n) ℂ) ≠ 0 := by
  have hmat :
      (Matrix.of (higham9_complexTranspose A) : Matrix (Fin n) (Fin n) ℂ) =
        (Matrix.of A : Matrix (Fin n) (Fin n) ℂ).transpose := by
    ext i j
    rfl
  intro hzero
  apply hdet
  rw [← Matrix.det_transpose (Matrix.of A : Matrix (Fin n) (Fin n) ℂ)]
  rw [← hmat]
  exact hzero

/-- Transposing an exact complex LU factorization and absorbing the upper
pivots into the new upper factor produces a unit-lower no-pivot LU
factorization of the original matrix. -/
theorem higham9_9_complex_LUFactSpec_of_transpose_rescaled {n : ℕ}
    (A L_T U_T : Fin n → Fin n → ℂ)
    (hLUt : higham9_8_ComplexLUFactSpec n
      (higham9_complexTranspose A) L_T U_T)
    (hUdiag : ∀ i : Fin n, U_T i i ≠ 0) :
    higham9_8_ComplexLUFactSpec n A
      (fun i j => U_T j i / U_T j j)
      (fun i j => U_T i i * L_T j i) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact div_self (hUdiag i)
  · intro i j hij
    have hz : U_T j i = 0 := hLUt.U_lower_zero j i hij
    simp [hz]
  · intro i j hji
    have hz : L_T j i = 0 := hLUt.L_upper_zero j i hji
    simp [hz]
  · intro i j
    calc
      (∑ k : Fin n, (U_T k i / U_T k k) * (U_T k k * L_T j k)) =
          ∑ k : Fin n, L_T j k * U_T k i := by
        apply Finset.sum_congr rfl
        intro k _hk
        have hk := hUdiag k
        field_simp [hk]
      _ = higham9_complexTranspose A j i := hLUt.product_eq j i
      _ = A i j := rfl

/-- Row diagonal dominance bounds every off-diagonal row ratio over `ℂ`. -/
theorem higham9_9_complex_rowDiagDominant_entry_ratio_norm_le_one {n : ℕ}
    {A : Fin n → Fin n → ℂ}
    (hDD : higham9_ComplexRowDiagDominant A)
    {i j : Fin n} (hij : j ≠ i) (hdiag : A i i ≠ 0) :
    ‖A i j / A i i‖ ≤ 1 := by
  have hterm :
      ‖A i j‖ ≤ ∑ k : Fin n, if i = k then 0 else ‖A i k‖ := by
    have hj :
        (fun k : Fin n => if i = k then (0 : ℝ) else ‖A i k‖) j =
          ‖A i j‖ := by
      simp [Ne.symm hij]
    rw [← hj]
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun k : Fin n => if i = k then (0 : ℝ) else ‖A i k‖)
      (by intro k _; by_cases hik : i = k <;> simp [hik, norm_nonneg])
      (Finset.mem_univ j)
  have hle : ‖A i j‖ ≤ ‖A i i‖ := le_trans hterm (hDD i)
  have hden : 0 < ‖A i i‖ := norm_pos_iff.mpr hdiag
  rw [norm_div, div_le_iff₀ hden]
  simpa using hle

/-- The transpose/rescaling construction preserves every literal
equation-(9.5) reduced entry, up to transpose. -/
theorem higham9_9_complex_transpose_rescaled_reducedEntry_eq {n : ℕ}
    (A L_T U_T : Fin n → Fin n → ℂ)
    (hUdiag : ∀ i : Fin n, U_T i i ≠ 0)
    (steps : ℕ) (i j : Fin n) :
    higham9_9_complexGEReducedEntry A
        (fun p q => U_T q p / U_T q q)
        (fun p q => U_T p p * L_T q p) steps i j =
      higham9_9_complexGEReducedEntry
        (higham9_complexTranspose A) L_T U_T steps j i := by
  unfold higham9_9_complexGEReducedEntry higham9_9_complexPrefixDot
  simp only [higham9_complexTranspose]
  congr 1
  apply Finset.sum_congr rfl
  intro q _hq
  by_cases hq : q.val < steps
  · simp only [hq, if_true]
    have hdiag := hUdiag q
    field_simp [hdiag]
  · simp [hq]

/-- Product splitting at an upper entry for the complex LU certificate. -/
lemma higham9_9_complex_source_eq_prefix_add_upper {n : ℕ}
    {A L U : Fin n → Fin n → ℂ}
    (hLU : higham9_8_ComplexLUFactSpec n A L U)
    (i j : Fin n) :
    A i j = higham9_9_complexPrefixDot L U i.val i j + U i j := by
  rw [← hLU.product_eq i j]
  unfold higham9_9_complexPrefixDot
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun q : Fin n => q.val < i.val)
    (fun q : Fin n => L i q * U q j)]
  congr 1
  · simp [Finset.sum_filter]
  · rw [Finset.sum_eq_single i]
    · simp [hLU.L_diag i]
    · intro q hq hqi
      have hnotlt : ¬ q.val < i.val := (Finset.mem_filter.mp hq).2
      have hle : i.val ≤ q.val := Nat.le_of_not_gt hnotlt
      have hne_val : i.val ≠ q.val := by
        intro hval
        exact hqi (Fin.ext hval.symm)
      have hiq : i.val < q.val := lt_of_le_of_ne hle hne_val
      rw [hLU.L_upper_zero i q hiq, zero_mul]
    · intro hi_not_mem
      exact (hi_not_mem (by simp)).elim

/-- Every stored upper entry is its pivot-row equation-(9.5) reduced entry. -/
theorem higham9_9_complex_reducedEntry_eq_upper {n : ℕ}
    {A L U : Fin n → Fin n → ℂ}
    (hLU : higham9_8_ComplexLUFactSpec n A L U)
    (i j : Fin n) :
    higham9_9_complexGEReducedEntry A L U i.val i j = U i j := by
  unfold higham9_9_complexGEReducedEntry
  rw [higham9_9_complex_source_eq_prefix_add_upper hLU i j]
  ring

/-- Every pivot-column reduced entry equals its lower multiplier times the
pivot. -/
theorem higham9_9_complex_reducedEntry_eq_lower_mul_pivot {n : ℕ}
    {A L U : Fin n → Fin n → ℂ}
    (hLU : higham9_8_ComplexLUFactSpec n A L U)
    (i k : Fin n) :
    higham9_9_complexGEReducedEntry A L U k.val i k = L i k * U k k := by
  unfold higham9_9_complexGEReducedEntry
  rw [Higham9Theorem99ComplexDirect.source_eq_prefix_add_lowerPivot hLU i k]
  ring

/-- Exact no-row-interchange condition for GEPP: at every stage the current
diagonal pivot is maximal in modulus in its active column (ties are allowed). -/
def higham9_9_complexNoRowInterchangesRequired {n : ℕ}
    (A L U : Fin n → Fin n → ℂ) : Prop :=
  ∀ k i : Fin n, k.val ≤ i.val →
    ‖higham9_9_complexGEReducedEntry A L U k.val i k‖ ≤
      ‖higham9_9_complexGEReducedEntry A L U k.val k k‖

/-- Unit-bounded lower multipliers certify that GEPP can keep every current
pivot row, hence requires no row interchanges. -/
theorem higham9_9_complex_noRowInterchangesRequired_of_multiplier_bound {n : ℕ}
    {A L U : Fin n → Fin n → ℂ}
    (hLU : higham9_8_ComplexLUFactSpec n A L U)
    (hLbound : ∀ i j : Fin n, ‖L i j‖ ≤ 1) :
    higham9_9_complexNoRowInterchangesRequired A L U := by
  intro k i _hki
  rw [higham9_9_complex_reducedEntry_eq_lower_mul_pivot hLU i k,
    higham9_9_complex_reducedEntry_eq_upper hLU k k, norm_mul]
  simpa using
    mul_le_mul_of_nonneg_right (hLbound i k) (norm_nonneg (U k k))

/-- A full reduced-history bound controls the final exact upper factor. -/
theorem higham9_9_complex_growthFactor_le_noPivotReducedGrowthFactor {n : ℕ}
    (hn : 0 < n) {A L U : Fin n → Fin n → ℂ}
    (hLU : higham9_8_ComplexLUFactSpec n A L U)
    (hAmax : 0 < higham9_13_complexMaxEntryNorm hn A) :
    higham9_complexGrowthFactor hn A U ≤
      higham9_9_complexNoPivotReducedGrowthFactor hn A L U := by
  have hUmax :
      higham9_13_complexMaxEntryNorm hn U ≤
        higham9_9_complexNoPivotReducedEntryMax hn A L U := by
    apply higham9_13_complexMaxEntryNorm_le_of_entry_le_bound
    intro i j
    rw [← higham9_9_complex_reducedEntry_eq_upper hLU i j]
    have hentry := higham9_13_entry_norm_le_complexMaxEntryNorm hn
      (fun p q : Fin n =>
        higham9_9_complexGEReducedEntry A L U i.val p q) i j
    have hstage :
        higham9_13_complexMaxEntryNorm hn
            (fun p q : Fin n =>
              higham9_9_complexGEReducedEntry A L U i.val p q) ≤
          higham9_9_complexNoPivotReducedEntryMax hn A L U := by
      unfold higham9_9_complexNoPivotReducedEntryMax
      exact Finset.le_sup'
        (fun step : Fin n => higham9_13_complexMaxEntryNorm hn
          (fun p q => higham9_9_complexGEReducedEntry A L U step.val p q))
        (Finset.mem_univ i)
    exact le_trans hentry hstage
  unfold higham9_complexGrowthFactor
    higham9_9_complexNoPivotReducedGrowthFactor
  exact div_le_div_of_nonneg_right hUmax (le_of_lt hAmax)

/-- Uniform pointwise control of every equation-(9.5) stage implies the full
history growth-factor bound. -/
theorem higham9_9_complex_noPivotReducedGrowthFactor_le_two_of_entry_bound
    {n : ℕ} (hn : 0 < n) {A L U : Fin n → Fin n → ℂ}
    (hAmax : 0 < higham9_13_complexMaxEntryNorm hn A)
    (hentry : ∀ step i j : Fin n,
      ‖higham9_9_complexGEReducedEntry A L U step.val i j‖ ≤
        2 * higham9_13_complexMaxEntryNorm hn A) :
    higham9_9_complexNoPivotReducedGrowthFactor hn A L U ≤ 2 := by
  have hmax :
      higham9_9_complexNoPivotReducedEntryMax hn A L U ≤
        2 * higham9_13_complexMaxEntryNorm hn A := by
    unfold higham9_9_complexNoPivotReducedEntryMax
    apply Finset.sup'_le
    intro step _hstep
    apply higham9_13_complexMaxEntryNorm_le_of_entry_le_bound
    exact hentry step
  unfold higham9_9_complexNoPivotReducedGrowthFactor
  rw [div_le_iff₀ hAmax]
  simpa [mul_comm] using hmax

/-! ## Source-facing Theorem 9.9 endpoints -/

/-- **Higham Theorem 9.9 (Wilkinson), complex row-dominance case.**  A
nonsingular complex row-diagonally-dominant matrix has an exact LU
factorization without pivoting.  Every equation-(9.5) reduced entry and the
full reduced-history growth factor are bounded by two times the source
maximum, and the final upper factor has growth at most two. -/
theorem higham9_9_complex_rowDiagDominant_exists_noPivotLU_growth_le_two
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℂ)
    (hRow : higham9_ComplexRowDiagDominant A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℂ) ≠ 0) :
    ∃ L U : Fin n → Fin n → ℂ,
      higham9_8_ComplexLUFactSpec n A L U ∧
      (∀ i : Fin n, U i i ≠ 0) ∧
      (∀ step i j : Fin n,
        ‖higham9_9_complexGEReducedEntry A L U step.val i j‖ ≤
          2 * higham9_13_complexMaxEntryNorm hn A) ∧
      0 < higham9_13_complexMaxEntryNorm hn A ∧
        higham9_9_complexNoPivotReducedGrowthFactor hn A L U ≤ 2 ∧
        higham9_complexGrowthFactor hn A U ≤ 2 := by
  obtain ⟨L, U, hLU, hURow, hUdiag⟩ :=
    Higham9Theorem99ComplexDirect.rowDiagDominant_exists_exactNoPivotLU_rowUpper
      n A hRow hdet
  have hentry : ∀ step i j : Fin n,
      ‖higham9_9_complexGEReducedEntry A L U step.val i j‖ ≤
        2 * higham9_13_complexMaxEntryNorm hn A :=
    Higham9Theorem99ComplexDirect.reducedEntry_norm_le_two_complexMaxEntryNorm
      hn hRow hLU hURow
  let hAmax : 0 < higham9_13_complexMaxEntryNorm hn A :=
    higham9_complexMaxEntryNorm_pos_of_det_ne_zero hn A hdet
  have hhistory :
      higham9_9_complexNoPivotReducedGrowthFactor hn A L U ≤ 2 :=
    Higham9Theorem99ComplexDirect.noPivotReducedGrowthFactor_le_two
      hn hRow hLU hURow hAmax
  refine ⟨L, U, hLU, hUdiag, hentry, hAmax, hhistory, ?_⟩
  exact le_trans
    (higham9_9_complex_growthFactor_le_noPivotReducedGrowthFactor
      hn hLU hAmax)
    hhistory

/-- **Higham Theorem 9.9 (Wilkinson), complex column-dominance case.**  The
constructed exact no-pivot LU factorization has every lower-factor entry of
modulus at most one.  Consequently its literal GEPP active columns can retain
the current diagonal pivot without a row interchange.  Its complete
equation-(9.5) history and final upper factor both have growth at most two. -/
theorem higham9_9_complex_colDiagDominant_exists_noPivotLU_growth_le_two
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℂ)
    (hCol : higham9_ComplexColDiagDominant A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℂ) ≠ 0) :
    ∃ L U : Fin n → Fin n → ℂ,
      higham9_8_ComplexLUFactSpec n A L U ∧
      (∀ i : Fin n, U i i ≠ 0) ∧
      (∀ i j : Fin n, ‖L i j‖ ≤ 1) ∧
      higham9_9_complexNoRowInterchangesRequired A L U ∧
      (∀ step i j : Fin n,
        ‖higham9_9_complexGEReducedEntry A L U step.val i j‖ ≤
          2 * higham9_13_complexMaxEntryNorm hn A) ∧
      0 < higham9_13_complexMaxEntryNorm hn A ∧
        higham9_9_complexNoPivotReducedGrowthFactor hn A L U ≤ 2 ∧
        higham9_complexGrowthFactor hn A U ≤ 2 := by
  let A_T : Fin n → Fin n → ℂ := higham9_complexTranspose A
  have hRowT : higham9_ComplexRowDiagDominant A_T := by
    exact (higham9_complexRowDiagDominant_transpose_iff_colDiagDominant A).2 hCol
  have hdetT :
      Matrix.det (Matrix.of A_T : Matrix (Fin n) (Fin n) ℂ) ≠ 0 := by
    simpa [A_T] using higham9_9_complex_transpose_det_ne_zero A hdet
  obtain ⟨L_T, U_T, hLUt, hUTRow, hUdiag⟩ :=
    Higham9Theorem99ComplexDirect.rowDiagDominant_exists_exactNoPivotLU_rowUpper
      n A_T hRowT hdetT
  let L : Fin n → Fin n → ℂ := fun i j => U_T j i / U_T j j
  let U : Fin n → Fin n → ℂ := fun i j => U_T i i * L_T j i
  have hLU : higham9_8_ComplexLUFactSpec n A L U := by
    simpa [L, U, A_T] using
      higham9_9_complex_LUFactSpec_of_transpose_rescaled
        A L_T U_T hLUt hUdiag
  have hUdiagNew : ∀ i : Fin n, U i i ≠ 0 := by
    intro i
    simpa [U, hLUt.L_diag i] using hUdiag i
  have hLbound : ∀ i j : Fin n, ‖L i j‖ ≤ 1 := by
    intro i j
    by_cases hij : i = j
    · subst i
      simp [L, hUdiag j]
    · simpa [L] using
        higham9_9_complex_rowDiagDominant_entry_ratio_norm_le_one
          hUTRow hij (hUdiag j)
  have hnoSwap : higham9_9_complexNoRowInterchangesRequired A L U :=
    higham9_9_complex_noRowInterchangesRequired_of_multiplier_bound
      hLU hLbound
  have hentry : ∀ step i j : Fin n,
      ‖higham9_9_complexGEReducedEntry A L U step.val i j‖ ≤
        2 * higham9_13_complexMaxEntryNorm hn A := by
    intro step i j
    have hT :=
      Higham9Theorem99ComplexDirect.reducedEntry_norm_le_two_complexMaxEntryNorm
        hn hRowT hLUt hUTRow step j i
    have heq := higham9_9_complex_transpose_rescaled_reducedEntry_eq
      A L_T U_T hUdiag step.val i j
    rw [← heq] at hT
    simpa [L, U, A_T, higham9_9_complex_maxEntryNorm_transpose hn A] using hT
  let hAmax : 0 < higham9_13_complexMaxEntryNorm hn A :=
    higham9_complexMaxEntryNorm_pos_of_det_ne_zero hn A hdet
  have hhistory :
      higham9_9_complexNoPivotReducedGrowthFactor hn A L U ≤ 2 :=
    higham9_9_complex_noPivotReducedGrowthFactor_le_two_of_entry_bound
      hn hAmax hentry
  refine ⟨L, U, hLU, hUdiagNew, hLbound, hnoSwap, hentry,
    hAmax, hhistory, ?_⟩
  exact le_trans
    (higham9_9_complex_growthFactor_le_noPivotReducedGrowthFactor
      hn hLU hAmax)
    hhistory

/-- **Higham Theorem 9.9, literal complex row-or-column wrapper.**  No LU,
trace, or growth conclusion is supplied by the caller. -/
theorem higham9_9_complex_diagDominant_exists_noPivotLU_growth_le_two
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℂ)
    (hDom : higham9_ComplexRowDiagDominant A ∨
      higham9_ComplexColDiagDominant A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℂ) ≠ 0) :
    ∃ L U : Fin n → Fin n → ℂ,
      higham9_8_ComplexLUFactSpec n A L U ∧
      (∀ i : Fin n, U i i ≠ 0) ∧
      (∀ step i j : Fin n,
        ‖higham9_9_complexGEReducedEntry A L U step.val i j‖ ≤
          2 * higham9_13_complexMaxEntryNorm hn A) ∧
      0 < higham9_13_complexMaxEntryNorm hn A ∧
        higham9_9_complexNoPivotReducedGrowthFactor hn A L U ≤ 2 ∧
        higham9_complexGrowthFactor hn A U ≤ 2 := by
  rcases hDom with hRow | hCol
  · exact higham9_9_complex_rowDiagDominant_exists_noPivotLU_growth_le_two
      hn A hRow hdet
  · obtain ⟨L, U, hLU, hUdiag, _hLbound, _hnoSwap, hentry,
      hAmax, hhistory, hfinal⟩ :=
      higham9_9_complex_colDiagDominant_exists_noPivotLU_growth_le_two
        hn A hCol hdet
    exact ⟨L, U, hLU, hUdiag, hentry, hAmax, hhistory, hfinal⟩

end NumStability
