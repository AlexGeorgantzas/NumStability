import NumStability.Algorithms.LinearSystems.LU.BlockLU.ArbitraryNorm
import NumStability.Source.Higham.Chapter13.Section03.RowDominanceClosure

/-!
  Source/Higham/Chapter13/Section03/ArbitraryNormDominance.lean

  Arbitrary-subordinate-norm source correspondence for Higham Theorems 13.7
  and 13.8. Reusable continuous-linear-map foundations live in
  `NumStability.Algorithms.LinearSystems.LU.BlockLU.ArbitraryNorm`.
-/

namespace NumStability

open scoped BigOperators

/-- One Schur step preserves column block diagonal dominance in the operator
norm induced by the ambient (arbitrary) vector norm. -/
theorem higham13_clmBlockSchur_blockDiagDomCol
    {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (A : Fin (m + 1) → Fin (m + 1) → E →L[ℝ] E)
    (P : E →L[ℝ] E)
    (hLeft : ∀ x : E, P (A 0 0 x) = x)
    (hRight : ∀ x : E, A 0 0 (P x) = x)
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j => ‖A i j‖)
      (fun j => continuousLinearMapLowerNorm (A j j) hunit)) :
    IsBlockDiagDomCol m
      (fun i j => ‖higham13_clmBlockSchur A P i j‖)
      (fun j => continuousLinearMapLowerNorm
        (higham13_clmBlockSchur A P j j) hunit) := by
  have hPpos : 0 < ‖P‖ :=
    continuousLinearMap_opNorm_pos_of_right_inverse (A 0 0) P hunit hRight
  have hRecip :
      continuousLinearMapLowerNorm (A 0 0) hunit = (‖P‖)⁻¹ :=
    continuousLinearMapLowerNorm_eq_inv_opNorm_of_inverse
      (A 0 0) P hunit hLeft hRight
  apply block_diag_dom_schur_inherit
      (blockNorm := fun i j => ‖A i j‖)
      (hNorm := fun i j => norm_nonneg (A i j))
      (invDiagBound := fun j => continuousLinearMapLowerNorm (A j j) hunit)
      (normInv := ‖P‖)
      (hNormInv := norm_nonneg P)
      (hDom := hDom)
      (hNormInvBound := ?_)
      (schurNorm := fun i j => ‖higham13_clmBlockSchur A P i j‖)
      (hSchurBound := ?_)
      (schurInvDiag := fun j => continuousLinearMapLowerNorm
        (higham13_clmBlockSchur A P j j) hunit)
      (hSchurDiag := ?_)
  · change ‖P‖ * continuousLinearMapLowerNorm (A 0 0) hunit ≤ 1
    rw [hRecip]
    exact le_of_eq (mul_inv_cancel₀ (ne_of_gt hPpos))
  · intro i j
    calc
      ‖higham13_clmBlockSchur A P i j‖
          ≤ ‖A i.succ j.succ‖ + ‖A i.succ 0 * P * A 0 j.succ‖ := by
        simpa [higham13_clmBlockSchur] using
          norm_sub_le (A i.succ j.succ) (A i.succ 0 * P * A 0 j.succ)
      _ ≤ ‖A i.succ j.succ‖ +
          ‖A i.succ 0‖ * ‖P‖ * ‖A 0 j.succ‖ := by
        apply add_le_add le_rfl
        calc
          ‖A i.succ 0 * P * A 0 j.succ‖
              ≤ ‖A i.succ 0 * P‖ * ‖A 0 j.succ‖ := norm_mul_le _ _
          _ ≤ (‖A i.succ 0‖ * ‖P‖) * ‖A 0 j.succ‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
  · intro j
    apply higham13_eq13_18_min_lower_bound
      (fun x => A j.succ j.succ x)
      (fun x => A j.succ 0 (P (A 0 j.succ x)))
      (fun x => higham13_clmBlockSchur A P j j x)
      (continuousLinearMapLowerNorm (A j.succ j.succ) hunit)
      (continuousLinearMapLowerNorm (higham13_clmBlockSchur A P j j) hunit)
      (‖A j.succ 0‖ * ‖P‖ * ‖A 0 j.succ‖)
    · intro x hx
      exact continuousLinearMapLowerNorm_le (A j.succ j.succ) hunit x hx
    · exact continuousLinearMapLowerNorm_attained
        (higham13_clmBlockSchur A P j j) hunit
    · intro x hx
      exact continuousLinearMap_triple_norm_le_of_unit
        (A j.succ 0) P (A 0 j.succ) hx
    · intro x
      simp [higham13_clmBlockSchur]

/-- One Schur step preserves row block diagonal dominance in the operator
norm induced by an arbitrary ambient vector norm. -/
theorem higham13_clmBlockSchur_blockDiagDomRow
    {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (A : Fin (m + 1) → Fin (m + 1) → E →L[ℝ] E)
    (P : E →L[ℝ] E)
    (hLeft : ∀ x : E, P (A 0 0 x) = x)
    (hRight : ∀ x : E, A 0 0 (P x) = x)
    (hDom : IsBlockDiagDomRow (m + 1)
      (fun i j => ‖A i j‖)
      (fun i => continuousLinearMapLowerNorm (A i i) hunit)) :
    IsBlockDiagDomRow m
      (fun i j => ‖higham13_clmBlockSchur A P i j‖)
      (fun i => continuousLinearMapLowerNorm
        (higham13_clmBlockSchur A P i i) hunit) := by
  have hPpos : 0 < ‖P‖ :=
    continuousLinearMap_opNorm_pos_of_right_inverse (A 0 0) P hunit hRight
  have hRecip :
      continuousLinearMapLowerNorm (A 0 0) hunit = (‖P‖)⁻¹ :=
    continuousLinearMapLowerNorm_eq_inv_opNorm_of_inverse
      (A 0 0) P hunit hLeft hRight
  apply block_diag_dom_schur_inherit_row
      (blockNorm := fun i j => ‖A i j‖)
      (hNorm := fun i j => norm_nonneg (A i j))
      (invDiagBound := fun i => continuousLinearMapLowerNorm (A i i) hunit)
      (normInv := ‖P‖)
      (hNormInv := norm_nonneg P)
      (hDom := hDom)
      (hNormInvBound := ?_)
      (schurNorm := fun i j => ‖higham13_clmBlockSchur A P i j‖)
      (hSchurBound := ?_)
      (schurInvDiag := fun i => continuousLinearMapLowerNorm
        (higham13_clmBlockSchur A P i i) hunit)
      (hSchurDiag := ?_)
  · change ‖P‖ * continuousLinearMapLowerNorm (A 0 0) hunit ≤ 1
    rw [hRecip]
    exact le_of_eq (mul_inv_cancel₀ (ne_of_gt hPpos))
  · intro i j
    calc
      ‖higham13_clmBlockSchur A P i j‖
          ≤ ‖A i.succ j.succ‖ + ‖A i.succ 0 * P * A 0 j.succ‖ := by
        simpa [higham13_clmBlockSchur] using
          norm_sub_le (A i.succ j.succ) (A i.succ 0 * P * A 0 j.succ)
      _ ≤ ‖A i.succ j.succ‖ +
          ‖A i.succ 0‖ * ‖P‖ * ‖A 0 j.succ‖ := by
        apply add_le_add le_rfl
        calc
          ‖A i.succ 0 * P * A 0 j.succ‖
              ≤ ‖A i.succ 0 * P‖ * ‖A 0 j.succ‖ := norm_mul_le _ _
          _ ≤ (‖A i.succ 0‖ * ‖P‖) * ‖A 0 j.succ‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
  · intro i
    apply higham13_eq13_18_min_lower_bound
      (fun x => A i.succ i.succ x)
      (fun x => A i.succ 0 (P (A 0 i.succ x)))
      (fun x => higham13_clmBlockSchur A P i i x)
      (continuousLinearMapLowerNorm (A i.succ i.succ) hunit)
      (continuousLinearMapLowerNorm (higham13_clmBlockSchur A P i i) hunit)
      (‖A i.succ 0‖ * ‖P‖ * ‖A 0 i.succ‖)
    · intro x hx
      exact continuousLinearMapLowerNorm_le (A i.succ i.succ) hunit x hx
    · exact continuousLinearMapLowerNorm_attained
        (higham13_clmBlockSchur A P i i) hunit
    · intro x hx
      exact continuousLinearMap_triple_norm_le_of_unit
        (A i.succ 0) P (A 0 i.succ) hx
    · intro x
      simp [higham13_clmBlockSchur]

/-- The recursively generated Schur-stage table on the first tail is the
tail of the original table.  This is the block-type-generic form of the
matrix-only tail-shift theorem in `BlockLU`; in particular it applies to
continuous linear maps for every induced operator norm. -/
theorem higham13_algorithm13_3_schurStageBlock_tail_shift_generic
    {m : ℕ} {α : Type*} [Sub α] [Mul α]
    (A : Fin (m + 1) → Fin (m + 1) → α)
    (pivotInv : ℕ → α) :
    ∀ k : ℕ, ∀ i j : Fin m,
      higham13_algorithm13_3_schurStageBlock
          (fun q r =>
            A q.succ r.succ - A q.succ 0 * pivotInv 0 * A 0 r.succ)
          (fun q => pivotInv (q + 1)) k i j =
        higham13_algorithm13_3_schurStageBlock A pivotInv (k + 1)
          i.succ j.succ := by
  intro k
  induction k with
  | zero =>
      intro i j
      simp [higham13_algorithm13_3_schurStageBlock]
  | succ k ih =>
      intro i j
      by_cases hk : k < m
      · have hkFull : k + 1 < m + 1 := Nat.succ_lt_succ hk
        by_cases hactive : k + 1 ≤ i.val ∧ k + 1 ≤ j.val
        · have hactiveFull :
              k + 1 + 1 ≤ i.succ.val ∧ k + 1 + 1 ≤ j.succ.val := by
            simpa [Fin.val_succ] using
              And.intro (Nat.succ_le_succ hactive.1)
                (Nat.succ_le_succ hactive.2)
          simp [higham13_algorithm13_3_schurStageBlock, hk, hkFull,
            hactive, ih, Fin.val_succ]
        · have hactiveFull :
              ¬ (k + 1 + 1 ≤ i.succ.val ∧ k + 1 + 1 ≤ j.succ.val) := by
            simpa [Fin.val_succ] using hactive
          simp [higham13_algorithm13_3_schurStageBlock, hk, hkFull,
            ih, Fin.val_succ]
      · have hkFull : ¬ k + 1 < m + 1 := by
          simpa using hk
        simp [higham13_algorithm13_3_schurStageBlock, hk, hkFull, ih]

/-- Full block nonsingularity and column block diagonal dominance construct
the complete Algorithm 13.3 pivot table.  Every selected pivot is a genuine
two-sided inverse of the actual recursively generated diagonal block.  Thus
the source hypotheses, rather than an externally supplied execution
certificate, produce the elimination data. -/
theorem higham13_clm_exists_pivotInv_two_sided_of_blockNonsingular_blockDiagDomCol
    {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [FiniteDimensional ℝ E]
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (A : Fin m → Fin m → E →L[ℝ] E)
    (hA : Higham13CLMBlockNonsingular A)
    (hDom : IsBlockDiagDomCol m
      (fun i j => ‖A i j‖)
      (fun j => continuousLinearMapLowerNorm (A j j) hunit)) :
    ∃ pivotInv : ℕ → E →L[ℝ] E,
      (∀ k : ℕ, ∀ hk : k < m, ∀ x : E,
        pivotInv k
            (higham13_algorithm13_3_schurStageBlock A pivotInv k
              ⟨k, hk⟩ ⟨k, hk⟩ x) = x) ∧
      (∀ k : ℕ, ∀ hk : k < m, ∀ x : E,
        higham13_algorithm13_3_schurStageBlock A pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩ (pivotInv k x) = x) := by
  induction m with
  | zero =>
      refine ⟨fun _ => 0, ?_, ?_⟩
      · intro k hk
        omega
      · intro k hk
        omega
  | succ m ih =>
      have hA00 : Function.Injective (A 0 0) :=
        higham13_clm_diag_injective_of_blockNonsingular_blockDiagDomCol
          hunit A hA hDom 0
      let P : E →L[ℝ] E := higham13_clmInverseOfInjective (A 0 0) hA00
      have hLeft : ∀ x : E, P (A 0 0 x) = x := by
        intro x
        exact higham13_clmInverseOfInjective_left (A 0 0) hA00 x
      have hRight : ∀ x : E, A 0 0 (P x) = x := by
        intro x
        exact higham13_clmInverseOfInjective_right (A 0 0) hA00 x
      let S : Fin m → Fin m → E →L[ℝ] E := higham13_clmBlockSchur A P
      have hS : Higham13CLMBlockNonsingular S := by
        exact higham13_clmBlockSchur_nonsingular A P hRight hA
      have hSDom : IsBlockDiagDomCol m
          (fun i j => ‖S i j‖)
          (fun j => continuousLinearMapLowerNorm (S j j) hunit) := by
        exact higham13_clmBlockSchur_blockDiagDomCol
          hunit A P hLeft hRight hDom
      rcases ih S hS hSDom with ⟨tailInv, hTailLeft, hTailRight⟩
      let pivotInv : ℕ → E →L[ℝ] E
        | 0 => P
        | k + 1 => tailInv k
      refine ⟨pivotInv, ?_, ?_⟩
      · intro k hk x
        cases k with
        | zero =>
            simpa [pivotInv, higham13_algorithm13_3_schurStageBlock] using
              hLeft x
        | succ k =>
            have hkTail : k < m := Nat.lt_of_succ_lt_succ hk
            have hStage :
                higham13_algorithm13_3_schurStageBlock S tailInv k
                    ⟨k, hkTail⟩ ⟨k, hkTail⟩ =
                  higham13_algorithm13_3_schurStageBlock A pivotInv (k + 1)
                    ⟨k + 1, hk⟩ ⟨k + 1, hk⟩ := by
              simpa [S, higham13_clmBlockSchur, pivotInv] using
                (higham13_algorithm13_3_schurStageBlock_tail_shift_generic
                  A pivotInv k ⟨k, hkTail⟩ ⟨k, hkTail⟩)
            rw [← hStage]
            simpa [pivotInv] using hTailLeft k hkTail x
      · intro k hk x
        cases k with
        | zero =>
            simpa [pivotInv, higham13_algorithm13_3_schurStageBlock] using
              hRight x
        | succ k =>
            have hkTail : k < m := Nat.lt_of_succ_lt_succ hk
            have hStage :
                higham13_algorithm13_3_schurStageBlock S tailInv k
                    ⟨k, hkTail⟩ ⟨k, hkTail⟩ =
                  higham13_algorithm13_3_schurStageBlock A pivotInv (k + 1)
                    ⟨k + 1, hk⟩ ⟨k + 1, hk⟩ := by
              simpa [S, higham13_clmBlockSchur, pivotInv] using
                (higham13_algorithm13_3_schurStageBlock_tail_shift_generic
                  A pivotInv k ⟨k, hkTail⟩ ⟨k, hkTail⟩)
            rw [← hStage]
            simpa [pivotInv] using hTailRight k hkTail x

/-- Row-BDD companion to the constructed-pivot theorem. -/
theorem higham13_clm_exists_pivotInv_two_sided_of_blockNonsingular_blockDiagDomRow
    {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [FiniteDimensional ℝ E]
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (A : Fin m → Fin m → E →L[ℝ] E)
    (hA : Higham13CLMBlockNonsingular A)
    (hDom : IsBlockDiagDomRow m
      (fun i j => ‖A i j‖)
      (fun i => continuousLinearMapLowerNorm (A i i) hunit)) :
    ∃ pivotInv : ℕ → E →L[ℝ] E,
      (∀ k : ℕ, ∀ hk : k < m, ∀ x : E,
        pivotInv k
            (higham13_algorithm13_3_schurStageBlock A pivotInv k
              ⟨k, hk⟩ ⟨k, hk⟩ x) = x) ∧
      (∀ k : ℕ, ∀ hk : k < m, ∀ x : E,
        higham13_algorithm13_3_schurStageBlock A pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩ (pivotInv k x) = x) := by
  induction m with
  | zero =>
      refine ⟨fun _ => 0, ?_, ?_⟩
      · intro k hk
        omega
      · intro k hk
        omega
  | succ m ih =>
      have hA00 : Function.Injective (A 0 0) :=
        higham13_clm_diag_injective_of_blockNonsingular_blockDiagDomRow
          hunit A hA hDom 0
      let P : E →L[ℝ] E := higham13_clmInverseOfInjective (A 0 0) hA00
      have hLeft : ∀ x : E, P (A 0 0 x) = x := by
        intro x
        exact higham13_clmInverseOfInjective_left (A 0 0) hA00 x
      have hRight : ∀ x : E, A 0 0 (P x) = x := by
        intro x
        exact higham13_clmInverseOfInjective_right (A 0 0) hA00 x
      let S : Fin m → Fin m → E →L[ℝ] E := higham13_clmBlockSchur A P
      have hS : Higham13CLMBlockNonsingular S := by
        exact higham13_clmBlockSchur_nonsingular A P hRight hA
      have hSDom : IsBlockDiagDomRow m
          (fun i j => ‖S i j‖)
          (fun i => continuousLinearMapLowerNorm (S i i) hunit) := by
        exact higham13_clmBlockSchur_blockDiagDomRow
          hunit A P hLeft hRight hDom
      rcases ih S hS hSDom with ⟨tailInv, hTailLeft, hTailRight⟩
      let pivotInv : ℕ → E →L[ℝ] E
        | 0 => P
        | k + 1 => tailInv k
      refine ⟨pivotInv, ?_, ?_⟩
      · intro k hk x
        cases k with
        | zero =>
            simpa [pivotInv, higham13_algorithm13_3_schurStageBlock] using
              hLeft x
        | succ k =>
            have hkTail : k < m := Nat.lt_of_succ_lt_succ hk
            have hStage :
                higham13_algorithm13_3_schurStageBlock S tailInv k
                    ⟨k, hkTail⟩ ⟨k, hkTail⟩ =
                  higham13_algorithm13_3_schurStageBlock A pivotInv (k + 1)
                    ⟨k + 1, hk⟩ ⟨k + 1, hk⟩ := by
              simpa [S, higham13_clmBlockSchur, pivotInv] using
                (higham13_algorithm13_3_schurStageBlock_tail_shift_generic
                  A pivotInv k ⟨k, hkTail⟩ ⟨k, hkTail⟩)
            rw [← hStage]
            simpa [pivotInv] using hTailLeft k hkTail x
      · intro k hk x
        cases k with
        | zero =>
            simpa [pivotInv, higham13_algorithm13_3_schurStageBlock] using
              hRight x
        | succ k =>
            have hkTail : k < m := Nat.lt_of_succ_lt_succ hk
            have hStage :
                higham13_algorithm13_3_schurStageBlock S tailInv k
                    ⟨k, hkTail⟩ ⟨k, hkTail⟩ =
                  higham13_algorithm13_3_schurStageBlock A pivotInv (k + 1)
                    ⟨k + 1, hk⟩ ⟨k + 1, hk⟩ := by
              simpa [S, higham13_clmBlockSchur, pivotInv] using
                (higham13_algorithm13_3_schurStageBlock_tail_shift_generic
                  A pivotInv k ⟨k, hkTail⟩ ⟨k, hkTail⟩)
            rw [← hStage]
            simpa [pivotInv] using hTailRight k hkTail x

/-- Source-complete column-BDD form of Higham Theorems 13.7 and 13.8 for an
arbitrary subordinate norm.  The chosen norm on `E` is completely generic;
the block norm below is its induced continuous-linear operator norm.

From only full block nonsingularity and the source column-BDD hypothesis, this
theorem constructs Algorithm 13.3's active inverses, proves preservation of
column BDD for the *actual* lower-norm table, and proves the active Schur-block
growth estimate `‖Aᵢⱼ⁽ᵏ⁾‖ ≤ 2 maxᵢⱼ ‖Aᵢⱼ‖`.  No Euclidean norm,
prebuilt execution, or pivot certificate occurs in its hypotheses. -/
theorem higham13_theorem13_7_and_13_8_clm_column_source_closure
    {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [FiniteDimensional ℝ E]
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (A : Fin m → Fin m → E →L[ℝ] E)
    (hA : Higham13CLMBlockNonsingular A)
    (hDom : IsBlockDiagDomCol m
      (fun i j => ‖A i j‖)
      (fun j => continuousLinearMapLowerNorm (A j j) hunit))
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, ‖A i j‖ ≤ normMax) :
    ∃ pivotInv : ℕ → E →L[ℝ] E,
      SchurStageActiveColumnDom13_7
        (higham13_algorithm13_3_schurStageNorm A pivotInv)
        (fun k j =>
          continuousLinearMapLowerNorm
            (higham13_algorithm13_3_schurStageBlock A pivotInv k j j)
            hunit) ∧
      ∀ k : ℕ, ∀ i j : Fin m,
        k ≤ i.val → k ≤ j.val →
          ‖higham13_algorithm13_3_schurStageBlock A pivotInv k i j‖ ≤
            2 * normMax := by
  rcases
      higham13_clm_exists_pivotInv_two_sided_of_blockNonsingular_blockDiagDomCol
        hunit A hA hDom with
    ⟨pivotInv, hLeft, hRight⟩
  have hSource :=
    higham13_algorithm13_3_source_lowerNorm_table_of_active_schur_pivots
      hunit A pivotInv hLeft hRight
  have hActiveDom : SchurStageActiveColumnDom13_7
      (higham13_algorithm13_3_schurStageNorm A pivotInv)
      (fun k j =>
        continuousLinearMapLowerNorm
          (higham13_algorithm13_3_schurStageBlock A pivotInv k j j)
          hunit) := by
    exact
      higham13_theorem13_7_active_column_dominance_of_exact_update_reciprocal
        (fun i j => ‖A i j‖)
        (fun j => continuousLinearMapLowerNorm (A j j) hunit)
        hDom
        (higham13_algorithm13_3_schurStageBlock A pivotInv)
        pivotInv
        (higham13_algorithm13_3_schurStageNorm A pivotInv)
        (fun k j =>
          continuousLinearMapLowerNorm
            (higham13_algorithm13_3_schurStageBlock A pivotInv k j j)
            hunit)
        (fun k => ‖pivotInv k‖)
        (by intro i j; rfl)
        (by intro j; rfl)
        (by intro k i j; rfl)
        (by intro k; rfl)
        hSource.2
        (higham13_algorithm13_3_schurStageBlock_exact_update A pivotInv)
        hSource.1
  have hDiagBound : ∀ j : Fin m,
      continuousLinearMapLowerNorm (A j j) hunit ≤ ‖A j j‖ := by
    intro j
    have hunitCopy := hunit
    obtain ⟨x, hx⟩ := hunitCopy
    calc
      continuousLinearMapLowerNorm (A j j) hunit ≤ ‖A j j x‖ :=
        continuousLinearMapLowerNorm_le (A j j) hunit x hx
      _ ≤ ‖A j j‖ * ‖x‖ := ContinuousLinearMap.le_opNorm (A j j) x
      _ = ‖A j j‖ := by rw [hx, mul_one]
  refine ⟨pivotInv, hActiveDom, ?_⟩
  intro k i j hik hjk
  exact
    higham13_algorithm13_3_clm_active_stage_bound_of_continuousLinearMap_source_table
      hunit
      (fun q => continuousLinearMapLowerNorm (A q q) hunit)
      A pivotInv hDom hDiagBound
      (by intro q; rfl)
      hLeft hRight normMax hMax k i j hik hjk

/-- Source-complete row-BDD companion to
`higham13_theorem13_7_and_13_8_clm_column_source_closure`.  It proves the
row form claimed alongside the column form in the source, again for the
operator norm subordinate to an arbitrary chosen vector norm. -/
theorem higham13_theorem13_7_and_13_8_clm_row_source_closure
    {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [FiniteDimensional ℝ E]
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (A : Fin m → Fin m → E →L[ℝ] E)
    (hA : Higham13CLMBlockNonsingular A)
    (hDom : IsBlockDiagDomRow m
      (fun i j => ‖A i j‖)
      (fun i => continuousLinearMapLowerNorm (A i i) hunit))
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, ‖A i j‖ ≤ normMax) :
    ∃ pivotInv : ℕ → E →L[ℝ] E,
      SchurStageActiveRowDom13_7
        (higham13_algorithm13_3_schurStageNorm A pivotInv)
        (fun k i =>
          continuousLinearMapLowerNorm
            (higham13_algorithm13_3_schurStageBlock A pivotInv k i i)
            hunit) ∧
      ∀ k : ℕ, ∀ i j : Fin m,
        k ≤ i.val → k ≤ j.val →
          ‖higham13_algorithm13_3_schurStageBlock A pivotInv k i j‖ ≤
            2 * normMax := by
  rcases
      higham13_clm_exists_pivotInv_two_sided_of_blockNonsingular_blockDiagDomRow
        hunit A hA hDom with
    ⟨pivotInv, hLeft, hRight⟩
  let stageNorm : ℕ → Fin m → Fin m → ℝ :=
    higham13_algorithm13_3_schurStageNorm A pivotInv
  let stageLower : ℕ → Fin m → ℝ :=
    fun k i => continuousLinearMapLowerNorm
      (higham13_algorithm13_3_schurStageBlock A pivotInv k i i) hunit
  let pivotNorm : ℕ → ℝ := fun k => ‖pivotInv k‖
  have hSource :
      SchurStageActiveDiagLowerUpdate13_7 stageNorm stageLower pivotNorm ∧
        SchurStageActivePivotInvReciprocal13_7 stageLower pivotNorm := by
    simpa [stageNorm, stageLower, pivotNorm] using
      (higham13_algorithm13_3_source_lowerNorm_table_of_active_schur_pivots
        hunit A pivotInv hLeft hRight)
  have hPivotBound : ∀ k : ℕ, ∀ hk : k < m,
      pivotNorm k * stageLower k ⟨k, hk⟩ ≤ 1 :=
    higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
      stageLower pivotNorm hSource.2
  have hLocal : SchurStageActiveLocalSchurBound13_8 stageNorm pivotNorm := by
    simpa [stageNorm, pivotNorm] using
      (higham13_algorithm13_3_schurStage_local_schur_bound A pivotInv)
  have hActiveDom : SchurStageActiveRowDom13_7 stageNorm stageLower := by
    apply higham13_theorem13_7_active_row_dominance_of_steps
      (fun i j => ‖A i j‖)
      (fun i => continuousLinearMapLowerNorm (A i i) hunit)
      hDom stageNorm stageLower
    · intro i j
      rfl
    · intro i
      rfl
    · exact higham13_theorem13_7_active_row_dom_step_of_local_schur_bound
        stageNorm stageLower pivotNorm
        (fun k i j => by
          exact higham13_algorithm13_3_schurStageNorm_nonneg
            A pivotInv k i j)
        (fun k => by simp [pivotNorm])
        hPivotBound hLocal hSource.1
  have hDiagBound : ∀ i : Fin m,
      continuousLinearMapLowerNorm (A i i) hunit ≤ ‖A i i‖ := by
    intro i
    have hunitCopy := hunit
    obtain ⟨x, hx⟩ := hunitCopy
    calc
      continuousLinearMapLowerNorm (A i i) hunit ≤ ‖A i i x‖ :=
        continuousLinearMapLowerNorm_le (A i i) hunit x hx
      _ ≤ ‖A i i‖ * ‖x‖ := ContinuousLinearMap.le_opNorm (A i i) x
      _ = ‖A i i‖ := by rw [hx, mul_one]
  refine ⟨pivotInv, ?_, ?_⟩
  · simpa [stageNorm, stageLower] using hActiveDom
  · intro k i j hik hjk
    simpa [stageNorm] using
      (higham13_theorem13_8_active_stage_block_bound_of_local_schur_bound_row
        (fun p q => ‖A p q‖)
        (fun p => continuousLinearMapLowerNorm (A p p) hunit)
        hDom hDiagBound stageNorm stageLower pivotNorm
        (by intro p q; rfl)
        (fun n p q => by
          exact higham13_algorithm13_3_schurStageNorm_nonneg
            A pivotInv n p q)
        (fun n => by simp [pivotNorm])
        hActiveDom hPivotBound hLocal normMax hMax k i j hik hjk)

end NumStability
