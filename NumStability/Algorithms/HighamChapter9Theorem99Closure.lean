import NumStability.Algorithms.HighamChapter9

namespace NumStability

open scoped BigOperators

/-!
# Higham Theorem 9.9: general diagonal-dominance closure

The source proves this result later through block diagonal dominance.  To keep
the chapter dependency graph acyclic, this module instead gives the elementary
scalar proof directly.  In the column case it also makes the transpose and
pivot-rescaling bridge explicit at every equation-(9.5) reduced stage.
-/

namespace Higham9Theorem99Direct

/-! ## Direct scalar row-dominance foundation -/

/-- A first exact no-pivot Schur-complement step preserves row diagonal
dominance. -/
theorem rowDiagDominant_firstSchurComplement {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hDD : IsRowDiagDominant (m + 1) A)
    (hpivot : A 0 0 ≠ 0) :
    IsRowDiagDominant m (luFirstSchurComplement A) := by
  classical
  intro i
  let S : Fin m → Fin m → ℝ := luFirstSchurComplement A
  let offS : ℝ := ∑ j : Fin m, if i = j then 0 else |S i j|
  let offA : ℝ := ∑ j : Fin m, if i = j then 0 else |A i.succ j.succ|
  let pivotTail : ℝ := ∑ j : Fin m, |A 0 j.succ|
  let ratio : ℝ := |A i.succ 0 / A 0 0|
  let diagCorrection : ℝ := ratio * |A 0 i.succ|
  have hsourceRow : |A i.succ 0| + offA ≤ |A i.succ i.succ| := by
    have h := hDD i.succ
    rw [Fin.sum_univ_succ] at h
    simpa [offA, Fin.succ_inj] using h
  have hpivotRow : pivotTail ≤ |A 0 0| := by
    have h := hDD (0 : Fin (m + 1))
    rw [Fin.sum_univ_succ] at h
    simpa [pivotTail] using h
  have hratioTail : ratio * pivotTail ≤ |A i.succ 0| := by
    calc
      ratio * pivotTail ≤ ratio * |A 0 0| :=
        mul_le_mul_of_nonneg_left hpivotRow (abs_nonneg _)
      _ = |A i.succ 0| := by
        dsimp [ratio]
        rw [abs_div]
        field_simp [abs_ne_zero.mpr hpivot]
  have hentry : ∀ j : Fin m, i ≠ j →
      |S i j| ≤ |A i.succ j.succ| + ratio * |A 0 j.succ| := by
    intro j _hij
    have hfactor :
        A i.succ 0 * A 0 j.succ / A 0 0 =
          (A i.succ 0 / A 0 0) * A 0 j.succ := by ring
    calc
      |S i j| =
          |A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0| := rfl
      _ ≤ |A i.succ j.succ| +
          |A i.succ 0 * A 0 j.succ / A 0 0| := by
        simpa [abs_neg] using
          (abs_sub_le (A i.succ j.succ) 0
            (A i.succ 0 * A 0 j.succ / A 0 0))
      _ = |A i.succ j.succ| + ratio * |A 0 j.succ| := by
        rw [hfactor, abs_mul]
  have hoffWithCorrection :
      offS + diagCorrection ≤ offA + ratio * pivotTail := by
    calc
      offS + diagCorrection =
          ∑ j : Fin m,
            ((if i = j then 0 else |S i j|) +
              if i = j then diagCorrection else 0) := by
        rw [Finset.sum_add_distrib]
        simp [offS]
      _ ≤ ∑ j : Fin m,
            ((if i = j then 0 else |A i.succ j.succ|) +
              ratio * |A 0 j.succ|) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hij : i = j
        · subst j
          simp [diagCorrection]
        · simpa [hij] using hentry j hij
      _ = offA + ratio * pivotTail := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hoffToOldDiag : offS + diagCorrection ≤ |A i.succ i.succ| := by
    calc
      offS + diagCorrection ≤ offA + ratio * pivotTail := hoffWithCorrection
      _ ≤ offA + |A i.succ 0| := by linarith
      _ = |A i.succ 0| + offA := by ring
      _ ≤ |A i.succ i.succ| := hsourceRow
  have holdDiagToNew :
      |A i.succ i.succ| ≤ |S i i| + diagCorrection := by
    have heq :
        A i.succ i.succ =
          S i i + (A i.succ 0 / A 0 0) * A 0 i.succ := by
      dsimp [S]
      simp only [luFirstSchurComplement]
      ring
    calc
      |A i.succ i.succ| =
          |S i i + (A i.succ 0 / A 0 0) * A 0 i.succ| := by rw [heq]
      _ ≤ |S i i| + |(A i.succ 0 / A 0 0) * A 0 i.succ| :=
        abs_add_le _ _
      _ = |S i i| + diagCorrection := by rw [abs_mul]
  change offS ≤ |S i i|
  linarith

/-- Assembling the source pivot row over a row-dominant trailing upper factor
preserves row diagonal dominance of the complete upper factor. -/
theorem luFirstStepU_rowDiagDominant {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    {U₁ : Fin m → Fin m → ℝ}
    (hA : IsRowDiagDominant (m + 1) A)
    (hU₁ : IsRowDiagDominant m U₁) :
    IsRowDiagDominant (m + 1) (luFirstStepU A U₁) := by
  intro i
  refine Fin.cases ?_ (fun q => ?_) i
  · simpa [luFirstStepU] using hA (0 : Fin (m + 1))
  · have h := hU₁ q
    rw [Fin.sum_univ_succ]
    simpa [luFirstStepU, Fin.succ_inj] using h

/-- Direct scalar no-pivot LU construction for a nonsingular row diagonally
dominant matrix; the resulting upper factor is row diagonally dominant. -/
theorem rowDiagDominant_exists_exactNoPivotLU_rowUpper :
    ∀ n : ℕ, ∀ A : Fin n → Fin n → ℝ,
      IsRowDiagDominant n A →
      Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 →
      ∃ L U : Fin n → Fin n → ℝ,
        LUFactSpec n A L U ∧ IsRowDiagDominant n U := by
  intro n
  induction n with
  | zero =>
      intro A _hDD _hdet
      refine ⟨A, A, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_⟩
        · intro i
          exact Fin.elim0 i
        · intro i _j
          exact Fin.elim0 i
        · intro i _j
          exact Fin.elim0 i
        · intro i _j
          exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ m ih =>
      intro A hDD hdet
      have hpivot : A 0 0 ≠ 0 :=
        (higham9_9_rowDiagDominant_diag_ne_zero_of_det_ne_zero hDD hdet) 0
      let S : Fin m → Fin m → ℝ := luFirstSchurComplement A
      have hSDD : IsRowDiagDominant m S := by
        simpa [S] using rowDiagDominant_firstSchurComplement hDD hpivot
      have hSdet :
          Matrix.det (Matrix.of S : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
        simpa [S, higham9_1_firstSchurComplement] using
          higham9_9_colDiagDominant_firstSchurComplement_det_ne_zero hpivot hdet
      obtain ⟨L₁, U₁, hLU₁, hU₁Row⟩ := ih S hSDD hSdet
      refine ⟨luFirstStepL A L₁, luFirstStepU A U₁, ?_, ?_⟩
      · exact LUFactSpec.of_firstSchurComplement_explicit hpivot hLU₁
      · exact luFirstStepU_rowDiagDominant hDD hU₁Row

/-- For an upper-triangular matrix, the full off-diagonal row sum is its
strict-upper row sum. -/
theorem upper_offdiag_sum_eq_strictUpper {n : ℕ}
    (U : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (i : Fin n) :
    (∑ j : Fin n, if i = j then 0 else |U i j|) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), |U i j| := by
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

/-! ## Direct equation-(9.5) reduced-history estimate -/

noncomputable def upperTailMass {n : ℕ}
    (U : Fin n → Fin n → ℝ) (q : Fin n) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => k ≤ j.val), |U q j|

noncomputable def eliminatedTailBudget {n : ℕ}
    (L U : Fin n → Fin n → ℝ) (i : Fin n) (k : ℕ) : ℝ :=
  ∑ q ∈ Finset.univ.filter (fun q : Fin n => q.val < k),
    |L i q| * upperTailMass U q k

noncomputable def sourcePrefixMass {n : ℕ}
    (A : Fin n → Fin n → ℝ) (i : Fin n) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k), |A i j|

lemma upperTailMass_succ {n : ℕ}
    (U : Fin n → Fin n → ℝ) (q : Fin n) (k : ℕ) (hk : k < n) :
    upperTailMass U q k = |U q ⟨k, hk⟩| + upperTailMass U q (k + 1) := by
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
    (A : Fin n → Fin n → ℝ) (i : Fin n) (k : ℕ) (hk : k < n) :
    sourcePrefixMass A i (k + 1) =
      sourcePrefixMass A i k + |A i ⟨k, hk⟩| := by
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
    (L U : Fin n → Fin n → ℝ) (i : Fin n) (k : ℕ) (hk : k < n) :
    eliminatedTailBudget L U i (k + 1) =
      (∑ q ∈ Finset.univ.filter (fun q : Fin n => q.val < k),
        |L i q| * upperTailMass U q (k + 1)) +
      |L i ⟨k, hk⟩| * upperTailMass U ⟨k, hk⟩ (k + 1) := by
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

lemma upperTailMass_le_diag {n : ℕ}
    {U : Fin n → Fin n → ℝ}
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hRow : IsRowDiagDominant n U)
    (q : Fin n) (k : ℕ) (hqk : q.val < k) :
    upperTailMass U q k ≤ |U q q| := by
  classical
  have hsubset :
      Finset.univ.filter (fun j : Fin n => k ≤ j.val) ⊆
        Finset.univ.filter (fun j : Fin n => q.val < j.val) := by
    intro j hj
    have hjk := (Finset.mem_filter.mp hj).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_lt_of_le hqk hjk⟩
  have htail_le :
      upperTailMass U q k ≤
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => q.val < j.val), |U q j| := by
    unfold upperTailMass
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (by intro j _hj _hjnot; exact abs_nonneg (U q j))
  calc
    upperTailMass U q k
        ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin n => q.val < j.val),
            |U q j| := htail_le
    _ = ∑ j : Fin n, (if q = j then 0 else |U q j|) :=
      (upper_offdiag_sum_eq_strictUpper U hUT q).symm
    _ ≤ |U q q| := hRow q

lemma rectPrefixDot_abs_le_prefixProductAbs {n : ℕ}
    (L U : Fin n → Fin n → ℝ) (i j k : Fin n) :
    |higham9_2_rectPrefixDot L U i j k| ≤
      ∑ q ∈ Finset.univ.filter (fun q : Fin n => q.val < k.val),
        |L i q| * |U q j| := by
  classical
  unfold higham9_2_rectPrefixDot
  rw [Finset.sum_filter]
  calc
    |∑ q : Fin n, if q.val < k.val then L i q * U q j else 0|
        ≤ ∑ q : Fin n, |if q.val < k.val then L i q * U q j else 0| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ q : Fin n,
          if q.val < k.val then |L i q| * |U q j| else 0 := by
      apply Finset.sum_congr rfl
      intro q _hq
      by_cases hqk : q.val < k.val <;> simp [hqk, abs_mul]

lemma source_eq_prefix_add_lowerPivot {n : ℕ}
    {A L U : Fin n → Fin n → ℝ} (hLU : LUFactSpec n A L U)
    (i k : Fin n) :
    A i k = higham9_2_rectPrefixDot L U i k k + L i k * U k k := by
  calc
    A i k = ∑ q : Fin n, L i q * U q k := (hLU.product_eq i k).symm
    _ = rectMatMul L U i k := by rfl
    _ = higham9_2_rectPrefixDot L U i k k + L i k * U k k :=
      higham9_2_rectMatMul_eq_prefix_add_lower hLU.U_lower_zero i k

lemma rectPrefixDot_eq_source_of_row_or_col_eliminated {n : ℕ}
    {A L U : Fin n → Fin n → ℝ} (hLU : LUFactSpec n A L U)
    (i j k : Fin n) (helim : i.val < k.val ∨ j.val < k.val) :
    higham9_2_rectPrefixDot L U i j k = A i j := by
  classical
  rw [← hLU.product_eq i j]
  unfold higham9_2_rectPrefixDot
  apply Finset.sum_congr rfl
  intro q _hq
  by_cases hqk : q.val < k.val
  · simp [hqk]
  · have hkq : k.val ≤ q.val := Nat.le_of_not_gt hqk
    rcases helim with hik | hjk
    · have hiq : i.val < q.val := lt_of_lt_of_le hik hkq
      simp [hqk, hLU.L_upper_zero i q hiq]
    · have hjq : j.val < q.val := lt_of_lt_of_le hjk hkq
      simp [hqk, hLU.U_lower_zero q j hjq]

/-- The contribution from eliminated rows to still-active columns is paid for
by source entries already left behind in the same row. -/
theorem eliminatedTailBudget_le_sourcePrefixMass {n : ℕ}
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U)
    (hURow : IsRowDiagDominant n U)
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
          |L i q| * upperTailMass U q (k + 1)
      let pivotColumnMass : ℝ :=
        ∑ q ∈ Finset.univ.filter (fun q : Fin n => q.val < k),
          |L i q| * |U q p|
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
      have htailPivot : upperTailMass U p (k + 1) ≤ |U p p| := by
        apply upperTailMass_le_diag hLU.U_lower_zero hURow
        simp [p]
      have hprefixAbs :
          |higham9_2_rectPrefixDot L U i p p| ≤ pivotColumnMass := by
        simpa [pivotColumnMass, p] using
          rectPrefixDot_abs_le_prefixProductAbs L U i p p
      have hsource := source_eq_prefix_add_lowerPivot hLU i p
      have hpivotProduct :
          |L i p| * |U p p| ≤ |A i p| + pivotColumnMass := by
        calc
          |L i p| * |U p p| = |L i p * U p p| := (abs_mul _ _).symm
          _ = |A i p - higham9_2_rectPrefixDot L U i p p| := by
            congr 1
            linarith
          _ ≤ |A i p| + |higham9_2_rectPrefixDot L U i p p| := by
            simpa [sub_eq_add_neg, abs_neg] using
              abs_add_le (A i p) (-(higham9_2_rectPrefixDot L U i p p))
          _ ≤ |A i p| + pivotColumnMass :=
            add_le_add (le_refl _) hprefixAbs
      have hnewTerm :
          |L i p| * upperTailMass U p (k + 1) ≤
            |A i p| + pivotColumnMass :=
        le_trans
          (mul_le_mul_of_nonneg_left htailPivot (abs_nonneg (L i p)))
          hpivotProduct
      rw [eliminatedTailBudget_succ L U i k hklt]
      calc
        oldTail + |L i p| * upperTailMass U p (k + 1)
            ≤ oldTail + (|A i p| + pivotColumnMass) :=
              add_le_add (le_refl oldTail) hnewTerm
        _ = (oldTail + pivotColumnMass) + |A i p| := by ring
        _ = eliminatedTailBudget L U i k + |A i p| := by rw [hdecompose]
        _ ≤ sourcePrefixMass A i k + |A i p| :=
          add_le_add (ih (Nat.le_of_lt hklt)) (le_refl _)
        _ = sourcePrefixMass A i (k + 1) := by
          simpa [p] using (sourcePrefixMass_succ A i k hklt).symm

lemma rectPrefixDot_abs_le_eliminatedTailBudget {n : ℕ}
    (L U : Fin n → Fin n → ℝ) (i j k : Fin n) (hkj : k.val ≤ j.val) :
    |higham9_2_rectPrefixDot L U i j k| ≤
      eliminatedTailBudget L U i k.val := by
  classical
  refine le_trans (rectPrefixDot_abs_le_prefixProductAbs L U i j k) ?_
  unfold eliminatedTailBudget
  apply Finset.sum_le_sum
  intro q hq
  have hjmem :
      j ∈ Finset.univ.filter (fun x : Fin n => k.val ≤ x.val) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkj⟩
  have hentry : |U q j| ≤ upperTailMass U q k.val := by
    unfold upperTailMass
    exact Finset.single_le_sum
      (fun x _hx => abs_nonneg (U q x)) hjmem
  exact mul_le_mul_of_nonneg_left hentry (abs_nonneg (L i q))

lemma sourcePrefixMass_le_maxEntryNorm {n : ℕ}
    (hn : 0 < n) {A : Fin n → Fin n → ℝ}
    (hRow : IsRowDiagDominant n A)
    (i : Fin n) (k : ℕ) (hki : k ≤ i.val) :
    sourcePrefixMass A i k ≤ maxEntryNorm hn A := by
  classical
  let S := Finset.univ.filter (fun j : Fin n => j.val < k)
  have heq :
      sourcePrefixMass A i k =
        ∑ j ∈ S, (if i = j then 0 else |A i j|) := by
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
      (∑ j ∈ S, (if i = j then 0 else |A i j|)) ≤
        ∑ j : Fin n, (if i = j then 0 else |A i j|) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro j _hj; exact Finset.mem_univ j)
      (by
        intro j _hjuniv _hjnot
        by_cases hij : i = j <;> simp [hij, abs_nonneg])
  calc
    sourcePrefixMass A i k
        = ∑ j ∈ S, (if i = j then 0 else |A i j|) := heq
    _ ≤ ∑ j : Fin n, (if i = j then 0 else |A i j|) :=
      hprefix_le_offdiag
    _ ≤ |A i i| := hRow i
    _ ≤ maxEntryNorm hn A := entry_le_maxEntryNorm hn A i i

/-- Every exact equation-(9.5) reduced entry of a nonsingular row diagonally
dominant matrix is at most twice the source max entry. -/
theorem reducedEntry_abs_le_two_maxEntryNorm {n : ℕ} (hn : 0 < n)
    {A L U : Fin n → Fin n → ℝ}
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hLU : LUFactSpec n A L U)
    (step i j : Fin n) :
    |higham9_5_rectGEReducedEntry A L U step.val i j| ≤
      2 * maxEntryNorm hn A := by
  have hURow : IsRowDiagDominant n U := by
    obtain ⟨L₀, U₀, hLU₀, hU₀Row⟩ :=
      rowDiagDominant_exists_exactNoPivotLU_rowUpper n A hRow hdet
    have huniq := higham9_1_lu_unique_of_pivots_ne_zero hLU hLU₀
      ((higham9_1_det_ne_zero_iff_pivots_ne_zero hLU).mp hdet)
    rw [huniq.2]
    exact hU₀Row
  by_cases hi : step.val ≤ i.val
  · by_cases hj : step.val ≤ j.val
    · have hprefixBudget :
          |higham9_2_rectPrefixDot L U i j step| ≤
            eliminatedTailBudget L U i step.val :=
        rectPrefixDot_abs_le_eliminatedTailBudget L U i j step hj
      have hbudgetSource :
          eliminatedTailBudget L U i step.val ≤ sourcePrefixMass A i step.val :=
        eliminatedTailBudget_le_sourcePrefixMass
          hLU hURow i step.val (Nat.le_of_lt step.isLt)
      have hsourceMax :
          sourcePrefixMass A i step.val ≤ maxEntryNorm hn A :=
        sourcePrefixMass_le_maxEntryNorm hn hRow i step.val hi
      rw [higham9_5_rectGEReducedEntry_eq_rectPrefixDot A L U i j step]
      calc
        |A i j - higham9_2_rectPrefixDot L U i j step|
            ≤ |A i j| + |higham9_2_rectPrefixDot L U i j step| := by
              simpa [sub_eq_add_neg, abs_neg] using
                abs_add_le (A i j) (-(higham9_2_rectPrefixDot L U i j step))
        _ ≤ maxEntryNorm hn A + eliminatedTailBudget L U i step.val :=
          add_le_add (entry_le_maxEntryNorm hn A i j) hprefixBudget
        _ ≤ maxEntryNorm hn A + sourcePrefixMass A i step.val :=
          add_le_add (le_refl _) hbudgetSource
        _ ≤ maxEntryNorm hn A + maxEntryNorm hn A :=
          add_le_add (le_refl _) hsourceMax
        _ = 2 * maxEntryNorm hn A := by ring
    · have hjlt : j.val < step.val := Nat.lt_of_not_ge hj
      have hpref := rectPrefixDot_eq_source_of_row_or_col_eliminated
        hLU i j step (Or.inr hjlt)
      rw [higham9_5_rectGEReducedEntry_eq_rectPrefixDot A L U i j step, hpref]
      simp [mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (maxEntryNorm_nonneg hn A)]
  · have hilt : i.val < step.val := Nat.lt_of_not_ge hi
    have hpref := rectPrefixDot_eq_source_of_row_or_col_eliminated
      hLU i j step (Or.inl hilt)
    rw [higham9_5_rectGEReducedEntry_eq_rectPrefixDot A L U i j step, hpref]
    simp [mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (maxEntryNorm_nonneg hn A)]

/-- Direct scalar row-dominance proof of the source no-pivot reduced growth
factor bound. -/
theorem noPivotReducedGrowthFactor_le_two {n : ℕ} (hn : 0 < n)
    {A L U : Fin n → Fin n → ℝ}
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hLU : LUFactSpec n A L U)
    (hAmax : 0 < maxEntryNorm hn A) :
    higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax ≤ 2 := by
  have hentryMax :
      higham_problem9_9_noPivotReducedEntryMax hn A L U ≤
        2 * maxEntryNorm hn A := by
    unfold higham_problem9_9_noPivotReducedEntryMax
    apply Finset.sup'_le
    intro step _hstep
    unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _hi
    apply Finset.sup'_le
    intro j _hj
    exact reducedEntry_abs_le_two_maxEntryNorm hn hRow hdet hLU step i j
  unfold higham_problem9_9_noPivotReducedGrowthFactor
  rw [div_le_iff₀ hAmax]
  simpa [mul_comm] using hentryMax

end Higham9Theorem99Direct

/-- Transposing an exact LU factorization and absorbing the upper pivots into
the new upper factor preserves every equation-(9.5) reduced entry, up to
transpose. -/
theorem higham9_9_transpose_rescaled_reducedEntry_eq {n : ℕ}
    (A L_T U_T : Fin n → Fin n → ℝ)
    (hUdiag : ∀ i : Fin n, U_T i i ≠ 0)
    (steps : ℕ) (i j : Fin n) :
    higham9_5_rectGEReducedEntry A
        (fun p q => U_T q p / U_T q q)
        (fun p q => U_T p p * L_T q p) steps i j =
      higham9_5_rectGEReducedEntry (matTranspose A) L_T U_T steps j i := by
  unfold higham9_5_rectGEReducedEntry higham9_5_rectPrefixRange
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hrn : r < n
  · simp only [hrn, dite_true]
    have hdiag := hUdiag ⟨r, hrn⟩
    field_simp [hdiag]
  · simp [hrn]

/-- The transpose/rescaling construction preserves the source maximum over
all equation-(9.5) reduced matrices. -/
theorem higham9_9_transpose_rescaled_noPivotReducedEntryMax_eq {n : ℕ}
    (hn : 0 < n) (A L_T U_T : Fin n → Fin n → ℝ)
    (hUdiag : ∀ i : Fin n, U_T i i ≠ 0) :
    higham_problem9_9_noPivotReducedEntryMax hn A
        (fun p q => U_T q p / U_T q q)
        (fun p q => U_T p p * L_T q p) =
      higham_problem9_9_noPivotReducedEntryMax hn
        (matTranspose A) L_T U_T := by
  unfold higham_problem9_9_noPivotReducedEntryMax
  congr 1
  funext step
  have hstage :
      (fun i j : Fin n =>
          higham9_5_rectGEReducedEntry A
            (fun p q => U_T q p / U_T q q)
            (fun p q => U_T p p * L_T q p) step.val i j) =
        matTranspose (fun i j : Fin n =>
          higham9_5_rectGEReducedEntry (matTranspose A) L_T U_T
            step.val i j) := by
    funext i j
    exact higham9_9_transpose_rescaled_reducedEntry_eq
      A L_T U_T hUdiag step.val i j
  rw [hstage, maxEntryNorm_matTranspose]

/-- The transpose/rescaling construction preserves the source no-pivot
growth factor, including the common source denominator. -/
theorem higham9_9_transpose_rescaled_noPivotReducedGrowthFactor_eq {n : ℕ}
    (hn : 0 < n) (A L_T U_T : Fin n → Fin n → ℝ)
    (hUdiag : ∀ i : Fin n, U_T i i ≠ 0)
    (hAmax : 0 < maxEntryNorm hn A) :
    higham_problem9_9_noPivotReducedGrowthFactor hn A
        (fun p q => U_T q p / U_T q q)
        (fun p q => U_T p p * L_T q p) hAmax =
      higham_problem9_9_noPivotReducedGrowthFactor hn
        (matTranspose A) L_T U_T
        (by simpa [maxEntryNorm_matTranspose hn A] using hAmax) := by
  unfold higham_problem9_9_noPivotReducedGrowthFactor
  rw [higham9_9_transpose_rescaled_noPivotReducedEntryMax_eq
    hn A L_T U_T hUdiag, maxEntryNorm_matTranspose]

/-- A source no-pivot reduced-history bound controls the final exact upper
factor, since every upper entry occurs on its pivot-row reduced stage. -/
theorem higham9_9_growthFactorEntry_le_noPivotReducedGrowthFactor {n : ℕ}
    (hn : 0 < n) {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U)
    (hAmax : 0 < maxEntryNorm hn A) :
    growthFactorEntry hn A U hAmax ≤
      higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax := by
  have hUmax :
      maxEntryNorm hn U ≤
        higham_problem9_9_noPivotReducedEntryMax hn A L U := by
    unfold maxEntryNorm
    apply Finset.sup'_le
    intro i _hi
    apply Finset.sup'_le
    intro j _hj
    have hredUpdate :=
      higham9_5_rectGEReducedEntry_eq_DoolittleUUpdate
        (Nat.le_refl n) A L U i j
    have hupdate := higham9_2_rectDoolittleUUpdate_eq_of_LUFactSpec hLU i j
    have hred : higham9_5_rectGEReducedEntry A L U i.val i j = U i j := by
      have hredUpdate' :
          higham9_5_rectGEReducedEntry A L U i.val i j =
            higham9_2_rectDoolittleUUpdate (Nat.le_refl n) A L U i j := by
        simpa [higham9_2_rectRow] using hredUpdate
      rw [hredUpdate', ← hupdate]
    rw [← hred]
    have hstage :
        maxEntryNorm hn
            (fun p q : Fin n => higham9_5_rectGEReducedEntry A L U i.val p q) ≤
          higham_problem9_9_noPivotReducedEntryMax hn A L U := by
      unfold higham_problem9_9_noPivotReducedEntryMax
      exact Finset.le_sup'
        (fun K : Fin n => maxEntryNorm hn
          (fun p q : Fin n => higham9_5_rectGEReducedEntry A L U K.val p q))
        (Finset.mem_univ i)
    exact le_trans
      (entry_le_maxEntryNorm hn
        (fun p q : Fin n => higham9_5_rectGEReducedEntry A L U i.val p q) i j)
      hstage
  unfold growthFactorEntry higham_problem9_9_noPivotReducedGrowthFactor
  exact div_le_div_of_nonneg_right hUmax (le_of_lt hAmax)

/-- **Theorem 9.9 (Wilkinson), row-diagonal-dominance case, all
dimensions.**  A nonsingular row diagonally dominant real matrix has an exact
no-pivot LU factorization, every exact equation-(9.5) reduced matrix has
max-entry growth at most two, and consequently the final upper factor has
growth at most two. -/
theorem higham9_9_rowDiagDominant_exists_LUFactSpec_noPivotGrowthFactor_le_two
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n A L U ∧
        ∃ hAmax : 0 < maxEntryNorm hn A,
          higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax ≤ 2 ∧
          growthFactorEntry hn A U hAmax ≤ 2 := by
  obtain ⟨L, U, hLU, _hURow⟩ :=
    Higham9Theorem99Direct.rowDiagDominant_exists_exactNoPivotLU_rowUpper
      n A hRow hdet
  let hAmax : 0 < maxEntryNorm hn A :=
    maxEntryNorm_pos_of_det_ne_zero hn A hdet
  have hsource :
      higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax ≤ 2 :=
    Higham9Theorem99Direct.noPivotReducedGrowthFactor_le_two
      hn hRow hdet hLU hAmax
  refine ⟨L, U, hLU, hAmax, hsource, ?_⟩
  exact le_trans
    (higham9_9_growthFactorEntry_le_noPivotReducedGrowthFactor hn hLU hAmax)
    hsource

/-- **Theorem 9.9 (Wilkinson), column-diagonal-dominance case, all
dimensions.**  A nonsingular column diagonally dominant real matrix has an
exact no-pivot LU factorization with every lower-factor entry bounded by one.
Its complete equation-(9.5) reduced history, and hence its final upper factor,
has max-entry growth at most two. -/
theorem higham9_9_colDiagDominant_exists_LUFactSpec_noPivotGrowthFactor_le_two
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hCol : IsDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n A L U ∧
      (∀ i j : Fin n, |L i j| ≤ 1) ∧
        ∃ hAmax : 0 < maxEntryNorm hn A,
          higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax ≤ 2 ∧
          growthFactorEntry hn A U hAmax ≤ 2 := by
  have hdetT :
      Matrix.det
        (Matrix.of (matTranspose A) : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
    have hmat :
        (Matrix.of (matTranspose A) : Matrix (Fin n) (Fin n) ℝ) =
          (Matrix.of A : Matrix (Fin n) (Fin n) ℝ).transpose := by
      ext i j
      rfl
    intro hzero
    apply hdet
    rw [← Matrix.det_transpose (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)]
    rw [← hmat]
    exact hzero
  have hRowT : IsRowDiagDominant n (matTranspose A) :=
    (higham9_9_rowDiagDominant_transpose_iff_colDiagDominant A).2 hCol
  obtain ⟨L_T, U_T, hLUt, hUTRow⟩ :=
    Higham9Theorem99Direct.rowDiagDominant_exists_exactNoPivotLU_rowUpper
      n (matTranspose A) hRowT hdetT
  have hUdiag : ∀ i : Fin n, U_T i i ≠ 0 :=
    hLUt.det_ne_zero_iff_U_diag_ne_zero.mp hdetT
  let L : Fin n → Fin n → ℝ := fun i j => U_T j i / U_T j j
  let U : Fin n → Fin n → ℝ := fun i j => U_T i i * L_T j i
  have hLU : LUFactSpec n A L U := by
    simpa [L, U] using
      higham9_13_LUFactSpec_of_transpose_LUFactSpec_nonzero_pivots
        A L_T U_T hLUt hUdiag
  have hLbound : ∀ i j : Fin n, |L i j| ≤ 1 := by
    intro i j
    by_cases hij : i = j
    · subst i
      simp [L, hUdiag j]
    · simpa [L] using
        higham9_9_rowDiagDominant_entry_ratio_abs_le_one
          hUTRow hij (hUdiag j)
  let hAmax : 0 < maxEntryNorm hn A :=
    maxEntryNorm_pos_of_det_ne_zero hn A hdet
  let hAmaxT : 0 < maxEntryNorm hn (matTranspose A) := by
    simpa [maxEntryNorm_matTranspose hn A] using hAmax
  have hsourceT :
      higham_problem9_9_noPivotReducedGrowthFactor
          hn (matTranspose A) L_T U_T hAmaxT ≤ 2 :=
    Higham9Theorem99Direct.noPivotReducedGrowthFactor_le_two
      hn hRowT hdetT hLUt hAmaxT
  have hsource :
      higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax ≤ 2 := by
    have heq := higham9_9_transpose_rescaled_noPivotReducedGrowthFactor_eq
      hn A L_T U_T hUdiag hAmax
    simpa [L, U, hAmaxT] using heq.trans_le hsourceT
  refine ⟨L, U, hLU, hLbound, hAmax, hsource, ?_⟩
  exact le_trans
    (higham9_9_growthFactorEntry_le_noPivotReducedGrowthFactor hn hLU hAmax)
    hsource

/-- **Theorem 9.9**, source disjunction wrapper.  This is the literal
row-or-column diagonal-dominance statement, with the column-only multiplier
conclusion retained in its corresponding branch. -/
theorem higham9_9_diagDominant_exists_LUFactSpec_noPivotGrowthFactor_le_two
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hDom : IsRowDiagDominant n A ∨ IsDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n A L U ∧
        ∃ hAmax : 0 < maxEntryNorm hn A,
          higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax ≤ 2 ∧
          growthFactorEntry hn A U hAmax ≤ 2 := by
  rcases hDom with hRow | hCol
  · exact higham9_9_rowDiagDominant_exists_LUFactSpec_noPivotGrowthFactor_le_two
      hn A hRow hdet
  · obtain ⟨L, U, hLU, _hLbound, hAmax, hsource, hfinal⟩ :=
      higham9_9_colDiagDominant_exists_LUFactSpec_noPivotGrowthFactor_le_two
        hn A hCol hdet
    exact ⟨L, U, hLU, hAmax, hsource, hfinal⟩

end NumStability
