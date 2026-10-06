import NumStability.Algorithms.Ch14Corollary147Closure
import NumStability.Algorithms.LU.BlockLU

namespace NumStability

open scoped BigOperators
open Ch14Ext

/-! # Chapter 13 point-row diagonal-dominance growth closure

This file is deliberately downstream of the Chapter 14 exact-LU existence
closure.  Chapter 14 proves that the upper factor of an exact no-pivot LU
factorization of a nonsingular row diagonally dominant matrix is itself row
diagonally dominant.  The lemmas below use that fact to prove the source
general-dimension bound `rho_n <= 2` for every exact reduced matrix, and then
connect that scalar-GE bound to the Algorithm 13.3 block-stage history.
-/

/-- The part of row `q` of `U` whose column indices have not yet been
eliminated at natural-number stage `k`. -/
noncomputable def higham13_pointRowUpperTailMass {n : ℕ}
    (U : Fin n → Fin n → ℝ) (q : Fin n) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => k ≤ j.val), |U q j|

/-- The triangular-tail budget from already eliminated rows in source row
`i` at natural-number stage `k`. -/
noncomputable def higham13_pointRowEliminatedTailBudget {n : ℕ}
    (L U : Fin n → Fin n → ℝ) (i : Fin n) (k : ℕ) : ℝ :=
  ∑ q ∈ Finset.univ.filter (fun q : Fin n => q.val < k),
    |L i q| * higham13_pointRowUpperTailMass U q k

/-- Absolute mass of the source entries in row `i` whose column indices have
already been eliminated at stage `k`. -/
noncomputable def higham13_pointRowSourcePrefixMass {n : ℕ}
    (A : Fin n → Fin n → ℝ) (i : Fin n) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k), |A i j|

lemma higham13_pointRowUpperTailMass_succ {n : ℕ}
    (U : Fin n → Fin n → ℝ) (q : Fin n) (k : ℕ) (hk : k < n) :
    higham13_pointRowUpperTailMass U q k =
      |U q ⟨k, hk⟩| + higham13_pointRowUpperTailMass U q (k + 1) := by
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
  unfold higham13_pointRowUpperTailMass
  rw [hset, Finset.sum_insert hpnot]

lemma higham13_pointRowSourcePrefixMass_succ {n : ℕ}
    (A : Fin n → Fin n → ℝ) (i : Fin n) (k : ℕ) (hk : k < n) :
    higham13_pointRowSourcePrefixMass A i (k + 1) =
      higham13_pointRowSourcePrefixMass A i k + |A i ⟨k, hk⟩| := by
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
  unfold higham13_pointRowSourcePrefixMass
  rw [hset, Finset.sum_insert hpnot, add_comm]

lemma higham13_pointRowEliminatedTailBudget_succ {n : ℕ}
    (L U : Fin n → Fin n → ℝ) (i : Fin n) (k : ℕ) (hk : k < n) :
    higham13_pointRowEliminatedTailBudget L U i (k + 1) =
      (∑ q ∈ Finset.univ.filter (fun q : Fin n => q.val < k),
        |L i q| * higham13_pointRowUpperTailMass U q (k + 1)) +
      |L i ⟨k, hk⟩| * higham13_pointRowUpperTailMass U ⟨k, hk⟩ (k + 1) := by
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
  unfold higham13_pointRowEliminatedTailBudget
  rw [hset, Finset.sum_insert hpnot, add_comm]

/-- A tail starting strictly to the right of row `q` is controlled by the
diagonal of a row diagonally dominant upper-triangular matrix. -/
lemma higham13_pointRowUpperTailMass_le_diag {n : ℕ}
    {U : Fin n → Fin n → ℝ}
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hRow : IsRowDiagDominant n U)
    (q : Fin n) (k : ℕ) (hqk : q.val < k) :
    higham13_pointRowUpperTailMass U q k ≤ |U q q| := by
  classical
  have hsubset :
      Finset.univ.filter (fun j : Fin n => k ≤ j.val) ⊆
        Finset.univ.filter (fun j : Fin n => q.val < j.val) := by
    intro j hj
    have hjk := (Finset.mem_filter.mp hj).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_lt_of_le hqk hjk⟩
  have htail_le :
      higham13_pointRowUpperTailMass U q k ≤
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => q.val < j.val), |U q j| := by
    unfold higham13_pointRowUpperTailMass
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (by intro j _hj _hjnot; exact abs_nonneg (U q j))
  calc
    higham13_pointRowUpperTailMass U q k
        ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin n => q.val < j.val),
            |U q j| := htail_le
    _ = ∑ j : Fin n, if q = j then 0 else |U q j| :=
      (ch14ext_upper_offdiag_sum_eq_strictUpper U hUT q).symm
    _ ≤ |U q q| := hRow q

/-- Absolute value of the exact prefix dot product is bounded by its
termwise-absolute prefix. -/
lemma higham13_rectPrefixDot_abs_le_prefixProductAbs {n : ℕ}
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

/-- Exact LU multiplication splits at the pivot column into the already
eliminated prefix plus the current lower-times-pivot term. -/
lemma higham13_source_eq_prefix_add_lowerPivot {n : ℕ}
    {A L U : Fin n → Fin n → ℝ} (hLU : LUFactSpec n A L U)
    (i k : Fin n) :
    A i k = higham9_2_rectPrefixDot L U i k k + L i k * U k k := by
  calc
    A i k = ∑ q : Fin n, L i q * U q k := (hLU.product_eq i k).symm
    _ = rectMatMul L U i k := by rfl
    _ = higham9_2_rectPrefixDot L U i k k + L i k * U k k :=
      higham9_2_rectMatMul_eq_prefix_add_lower hLU.U_lower_zero i k

/-- Once either the row or column has already been eliminated, the exact LU
prefix equals the full source entry. -/
lemma higham13_rectPrefixDot_eq_source_of_row_or_col_eliminated {n : ℕ}
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

/-- The source triangular-tail invariant.  At every stage, the contribution
from eliminated rows to the still-active columns is paid for by source entries
that have already left the active row. -/
theorem higham13_pointRowEliminatedTailBudget_le_sourcePrefixMass {n : ℕ}
    {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U)
    (hURow : IsRowDiagDominant n U)
    (i : Fin n) :
    ∀ k : ℕ, k ≤ n →
      higham13_pointRowEliminatedTailBudget L U i k ≤
        higham13_pointRowSourcePrefixMass A i k := by
  intro k hk
  induction k with
  | zero =>
      simp [higham13_pointRowEliminatedTailBudget,
        higham13_pointRowSourcePrefixMass]
  | succ k ih =>
      have hklt : k < n := Nat.lt_of_succ_le hk
      let p : Fin n := ⟨k, hklt⟩
      let oldTail : ℝ :=
        ∑ q ∈ Finset.univ.filter (fun q : Fin n => q.val < k),
          |L i q| * higham13_pointRowUpperTailMass U q (k + 1)
      let pivotColumnMass : ℝ :=
        ∑ q ∈ Finset.univ.filter (fun q : Fin n => q.val < k),
          |L i q| * |U q p|
      have hdecompose :
          oldTail + pivotColumnMass =
            higham13_pointRowEliminatedTailBudget L U i k := by
        dsimp [oldTail, pivotColumnMass]
        rw [← Finset.sum_add_distrib]
        unfold higham13_pointRowEliminatedTailBudget
        apply Finset.sum_congr rfl
        intro q _hq
        have htail := higham13_pointRowUpperTailMass_succ U q k hklt
        have hp : (⟨k, hklt⟩ : Fin n) = p := rfl
        rw [hp] at htail
        rw [htail]
        ring
      have htailPivot :
          higham13_pointRowUpperTailMass U p (k + 1) ≤ |U p p| := by
        apply higham13_pointRowUpperTailMass_le_diag hLU.U_lower_zero hURow
        simp [p]
      have hprefixAbs :
          |higham9_2_rectPrefixDot L U i p p| ≤ pivotColumnMass := by
        simpa [pivotColumnMass, p] using
          higham13_rectPrefixDot_abs_le_prefixProductAbs L U i p p
      have hsource := higham13_source_eq_prefix_add_lowerPivot hLU i p
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
          |L i p| * higham13_pointRowUpperTailMass U p (k + 1) ≤
            |A i p| + pivotColumnMass :=
        le_trans
          (mul_le_mul_of_nonneg_left htailPivot (abs_nonneg (L i p)))
          hpivotProduct
      rw [higham13_pointRowEliminatedTailBudget_succ L U i k hklt]
      calc
        oldTail +
              |L i p| * higham13_pointRowUpperTailMass U p (k + 1)
            ≤ oldTail + (|A i p| + pivotColumnMass) :=
              add_le_add (le_refl oldTail) hnewTerm
        _ = (oldTail + pivotColumnMass) + |A i p| := by ring
        _ = higham13_pointRowEliminatedTailBudget L U i k + |A i p| := by
          rw [hdecompose]
        _ ≤ higham13_pointRowSourcePrefixMass A i k + |A i p| :=
          add_le_add (ih (Nat.le_of_lt hklt)) (le_refl _)
        _ = higham13_pointRowSourcePrefixMass A i (k + 1) := by
          simpa [p] using
            (higham13_pointRowSourcePrefixMass_succ A i k hklt).symm

/-- For an active column, the absolute LU prefix contributing to its reduced
entry is one component of the eliminated triangular-tail budget. -/
lemma higham13_rectPrefixDot_abs_le_eliminatedTailBudget {n : ℕ}
    (L U : Fin n → Fin n → ℝ) (i j k : Fin n) (hkj : k.val ≤ j.val) :
    |higham9_2_rectPrefixDot L U i j k| ≤
      higham13_pointRowEliminatedTailBudget L U i k.val := by
  classical
  refine le_trans
    (higham13_rectPrefixDot_abs_le_prefixProductAbs L U i j k) ?_
  unfold higham13_pointRowEliminatedTailBudget
  apply Finset.sum_le_sum
  intro q hq
  have hjmem :
      j ∈ Finset.univ.filter (fun x : Fin n => k.val ≤ x.val) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkj⟩
  have hentry :
      |U q j| ≤ higham13_pointRowUpperTailMass U q k.val := by
    unfold higham13_pointRowUpperTailMass
    exact Finset.single_le_sum
      (fun x _hx => abs_nonneg (U q x)) hjmem
  exact mul_le_mul_of_nonneg_left hentry (abs_nonneg (L i q))

/-- In an active source row, the already-eliminated source prefix has mass at
most the source max entry, by point-row diagonal dominance. -/
lemma higham13_pointRowSourcePrefixMass_le_maxEntryNorm {n : ℕ}
    (hn : 0 < n) {A : Fin n → Fin n → ℝ}
    (hRow : IsRowDiagDominant n A)
    (i : Fin n) (k : ℕ) (hki : k ≤ i.val) :
    higham13_pointRowSourcePrefixMass A i k ≤ maxEntryNorm hn A := by
  classical
  let S := Finset.univ.filter (fun j : Fin n => j.val < k)
  have heq :
      higham13_pointRowSourcePrefixMass A i k =
        ∑ j ∈ S, (if i = j then 0 else |A i j|) := by
    unfold higham13_pointRowSourcePrefixMass
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
    higham13_pointRowSourcePrefixMass A i k
        = ∑ j ∈ S, (if i = j then 0 else |A i j|) := heq
    _ ≤ ∑ j : Fin n, (if i = j then 0 else |A i j|) :=
      hprefix_le_offdiag
    _ ≤ |A i i| := hRow i
    _ ≤ maxEntryNorm hn A := entry_le_maxEntryNorm hn A i i

/-- Source equation (13.23), general dimension: every exact no-pivot reduced
entry of a nonsingular point-row diagonally dominant matrix is at most twice
the source max entry. -/
theorem higham13_eq13_23_pointRow_reducedEntry_abs_le_two_maxEntryNorm
    {n : ℕ} (hn : 0 < n)
    {A L U : Fin n → Fin n → ℝ}
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hLU : LUFactSpec n A L U)
    (step i j : Fin n) :
    |higham9_5_rectGEReducedEntry A L U step.val i j| ≤
      2 * maxEntryNorm hn A := by
  have hURow : IsRowDiagDominant n U :=
    ch14ext_exactNoPivotLU_upper_rowDiagDominant A L U hRow hdet hLU
  by_cases hi : step.val ≤ i.val
  · by_cases hj : step.val ≤ j.val
    · have hprefixBudget :
          |higham9_2_rectPrefixDot L U i j step| ≤
            higham13_pointRowEliminatedTailBudget L U i step.val :=
        higham13_rectPrefixDot_abs_le_eliminatedTailBudget L U i j step hj
      have hbudgetSource :
          higham13_pointRowEliminatedTailBudget L U i step.val ≤
            higham13_pointRowSourcePrefixMass A i step.val :=
        higham13_pointRowEliminatedTailBudget_le_sourcePrefixMass
          hLU hURow i step.val (Nat.le_of_lt step.isLt)
      have hsourceMax :
          higham13_pointRowSourcePrefixMass A i step.val ≤
            maxEntryNorm hn A :=
        higham13_pointRowSourcePrefixMass_le_maxEntryNorm hn hRow i step.val hi
      rw [higham9_5_rectGEReducedEntry_eq_rectPrefixDot A L U i j step]
      calc
        |A i j - higham9_2_rectPrefixDot L U i j step|
            ≤ |A i j| + |higham9_2_rectPrefixDot L U i j step| := by
              simpa [sub_eq_add_neg, abs_neg] using
                abs_add_le (A i j) (-(higham9_2_rectPrefixDot L U i j step))
        _ ≤ maxEntryNorm hn A +
              higham13_pointRowEliminatedTailBudget L U i step.val :=
          add_le_add (entry_le_maxEntryNorm hn A i j) hprefixBudget
        _ ≤ maxEntryNorm hn A +
              higham13_pointRowSourcePrefixMass A i step.val :=
          add_le_add (le_refl _) hbudgetSource
        _ ≤ maxEntryNorm hn A + maxEntryNorm hn A :=
          add_le_add (le_refl _) hsourceMax
        _ = 2 * maxEntryNorm hn A := by ring
    · have hjlt : j.val < step.val := Nat.lt_of_not_ge hj
      have hpref :=
        higham13_rectPrefixDot_eq_source_of_row_or_col_eliminated
          hLU i j step (Or.inr hjlt)
      rw [higham9_5_rectGEReducedEntry_eq_rectPrefixDot A L U i j step,
        hpref]
      simp [mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (maxEntryNorm_nonneg hn A)]
  · have hilt : i.val < step.val := Nat.lt_of_not_ge hi
    have hpref :=
      higham13_rectPrefixDot_eq_source_of_row_or_col_eliminated
        hLU i j step (Or.inl hilt)
    rw [higham9_5_rectGEReducedEntry_eq_rectPrefixDot A L U i j step,
      hpref]
    simp [mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (maxEntryNorm_nonneg hn A)]

/-- Equation (13.23) in the source scalar-GE `rho_n` form. -/
theorem higham13_eq13_23_pointRow_noPivotReducedGrowthFactor_le_two
    {n : ℕ} (hn : 0 < n)
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
    exact higham13_eq13_23_pointRow_reducedEntry_abs_le_two_maxEntryNorm
      hn hRow hdet hLU step i j
  unfold higham_problem9_9_noPivotReducedGrowthFactor
  rw [div_le_iff₀ hAmax]
  simpa [mul_comm] using hentryMax

/-- Source-facing equation (13.23) wrapper deriving the positive growth-factor
denominator from nonsingularity. -/
theorem higham13_eq13_23_pointRow_noPivotReducedGrowthFactor_le_two_exists_hAmax
    {n : ℕ} (hn : 0 < n)
    {A L U : Fin n → Fin n → ℝ}
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hLU : LUFactSpec n A L U) :
    ∃ hAmax : 0 < maxEntryNorm hn A,
      higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax ≤ 2 := by
  let hAmax : 0 < maxEntryNorm hn A :=
    maxEntryNorm_pos_of_det_ne_zero hn A hdet
  exact ⟨hAmax,
    higham13_eq13_23_pointRow_noPivotReducedGrowthFactor_le_two
      hn hRow hdet hLU hAmax⟩

/-- Full point-row source closure: nonsingularity and row diagonal dominance
construct exact no-pivot factors and prove their equation (9.5) growth factor
is at most two.  No factorization certificate is required from the caller. -/
theorem higham13_eq13_23_pointRow_exists_exactNoPivotLU_growthFactor_le_two
    {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ)
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ L U : Fin n → Fin n → ℝ,
      LUFactSpec n A L U ∧
        ∃ hAmax : 0 < maxEntryNorm hn A,
          higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax ≤ 2 := by
  obtain ⟨L, U, hLU, _hURow⟩ :=
    ch14ext_rowDiagDominant_exists_exactNoPivotLU_rowUpper n A hRow hdet
  exact ⟨L, U, hLU,
    higham13_eq13_23_pointRow_noPivotReducedGrowthFactor_le_two_exists_hAmax
      hn hRow hdet hLU⟩

/-! ## Bridge to the Chapter 13 common growth-object API -/

/-- A matrix-valued representative of the source equation (9.5) reduced
history.  Every entry is the maximum entry magnitude across the actual reduced
matrices, so its max-entry norm is exactly that history maximum. -/
noncomputable def higham13_noPivotReducedHistoryGrowthMatrix {n : ℕ}
    (hn : 0 < n) (A L U : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun _ _ => higham_problem9_9_noPivotReducedEntryMax hn A L U

lemma higham13_noPivotReducedEntryMax_nonneg {n : ℕ}
    (hn : 0 < n) (A L U : Fin n → Fin n → ℝ) :
    0 ≤ higham_problem9_9_noPivotReducedEntryMax hn A L U := by
  have hstage :
      maxEntryNorm hn
          (fun i j : Fin n => higham9_5_rectGEReducedEntry A L U 0 i j) ≤
        higham_problem9_9_noPivotReducedEntryMax hn A L U := by
    unfold higham_problem9_9_noPivotReducedEntryMax
    exact Finset.le_sup'
      (fun step : Fin n =>
        maxEntryNorm hn
          (fun i j : Fin n =>
            higham9_5_rectGEReducedEntry A L U step.val i j))
      (Finset.mem_univ (⟨0, hn⟩ : Fin n))
  exact le_trans
    (maxEntryNorm_nonneg hn
      (fun i j : Fin n => higham9_5_rectGEReducedEntry A L U 0 i j))
    hstage

theorem higham13_noPivotReducedHistoryGrowthMatrix_maxEntryNorm {n : ℕ}
    (hn : 0 < n) (A L U : Fin n → Fin n → ℝ) :
    maxEntryNorm hn (higham13_noPivotReducedHistoryGrowthMatrix hn A L U) =
      higham_problem9_9_noPivotReducedEntryMax hn A L U := by
  let C := higham_problem9_9_noPivotReducedEntryMax hn A L U
  have hC : 0 ≤ C := by
    simpa [C] using higham13_noPivotReducedEntryMax_nonneg hn A L U
  apply le_antisymm
  · apply maxEntryNorm_le_of_entry_le_bound
    intro i j
    simp [higham13_noPivotReducedHistoryGrowthMatrix, C, abs_of_nonneg hC]
  · have hentry := entry_le_maxEntryNorm hn
      (higham13_noPivotReducedHistoryGrowthMatrix hn A L U)
      (⟨0, hn⟩ : Fin n) (⟨0, hn⟩ : Fin n)
    simpa [higham13_noPivotReducedHistoryGrowthMatrix, C, abs_of_nonneg hC]
      using hentry

/-- The generic `growthFactorEntry` of the history representative is
definitionally the source no-pivot reduced growth factor. -/
theorem higham13_noPivotReducedHistory_growthFactorEntry_eq {n : ℕ}
    (hn : 0 < n) (A L U : Fin n → Fin n → ℝ)
    (hAmax : 0 < maxEntryNorm hn A) :
    growthFactorEntry hn A
        (higham13_noPivotReducedHistoryGrowthMatrix hn A L U) hAmax =
      higham_problem9_9_noPivotReducedGrowthFactor hn A L U hAmax := by
  unfold growthFactorEntry higham_problem9_9_noPivotReducedGrowthFactor
  rw [higham13_noPivotReducedHistoryGrowthMatrix_maxEntryNorm]

/-- The history representative contains every actual equation (9.5) reduced
stage in max-entry norm. -/
theorem higham13_noPivotReducedHistoryGrowthMatrix_contains_stage {n : ℕ}
    (hn : 0 < n) (A L U : Fin n → Fin n → ℝ) (step : Fin n) :
    maxEntryNorm hn
        (fun i j : Fin n =>
          higham9_5_rectGEReducedEntry A L U step.val i j) ≤
      maxEntryNorm hn
        (higham13_noPivotReducedHistoryGrowthMatrix hn A L U) := by
  rw [higham13_noPivotReducedHistoryGrowthMatrix_maxEntryNorm]
  unfold higham_problem9_9_noPivotReducedEntryMax
  exact Finset.le_sup'
    (fun K : Fin n =>
      maxEntryNorm hn
        (fun i j : Fin n => higham9_5_rectGEReducedEntry A L U K.val i j))
    (Finset.mem_univ step)

/-- In particular, the common growth object contains the source matrix at
stage zero. -/
theorem higham13_noPivotReducedHistoryGrowthMatrix_contains_initial {n : ℕ}
    (hn : 0 < n) (A L U : Fin n → Fin n → ℝ) :
    maxEntryNorm hn A ≤
      maxEntryNorm hn
        (higham13_noPivotReducedHistoryGrowthMatrix hn A L U) := by
  simpa [higham9_5_rectGEReducedEntry_zero] using
    higham13_noPivotReducedHistoryGrowthMatrix_contains_stage
      hn A L U (⟨0, hn⟩ : Fin n)

/-- The final exact upper factor is also contained in the equation (9.5)
history: row `i` of `U` is the reduced pivot row at stage `i`. -/
theorem higham13_noPivotReducedHistoryGrowthMatrix_contains_upper {n : ℕ}
    (hn : 0 < n) {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U) :
    maxEntryNorm hn U ≤
      maxEntryNorm hn
        (higham13_noPivotReducedHistoryGrowthMatrix hn A L U) := by
  apply maxEntryNorm_le_of_entry_le_bound
  intro i j
  have hredUpdate :=
    higham9_5_rectGEReducedEntry_eq_DoolittleUUpdate
      (Nat.le_refl n) A L U i j
  have hupdate := higham9_2_rectDoolittleUUpdate_eq_of_LUFactSpec hLU i j
  have hredUpdate' :
      higham9_5_rectGEReducedEntry A L U i.val i j =
        higham9_2_rectDoolittleUUpdate (Nat.le_refl n) A L U i j := by
    simpa [higham9_2_rectRow] using hredUpdate
  have hred : higham9_5_rectGEReducedEntry A L U i.val i j = U i j := by
    rw [hredUpdate', ← hupdate]
  rw [← hred]
  exact le_trans
    (entry_le_maxEntryNorm hn
      (fun p q : Fin n =>
        higham9_5_rectGEReducedEntry A L U i.val p q) i j)
    (higham13_noPivotReducedHistoryGrowthMatrix_contains_stage hn A L U i)

/-- Equation (13.23) on the same matrix-valued growth object used by the
Chapter 13 Problem 13.4 and Table 13.1 adapters. -/
theorem higham13_eq13_23_pointRow_historyGrowthFactorEntry_le_two
    {n : ℕ} (hn : 0 < n)
    {A L U : Fin n → Fin n → ℝ}
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hLU : LUFactSpec n A L U)
    (hAmax : 0 < maxEntryNorm hn A) :
    growthFactorEntry hn A
        (higham13_noPivotReducedHistoryGrowthMatrix hn A L U) hAmax ≤ 2 := by
  rw [higham13_noPivotReducedHistory_growthFactorEntry_eq]
  exact higham13_eq13_23_pointRow_noPivotReducedGrowthFactor_le_two
    hn hRow hdet hLU hAmax

end NumStability
