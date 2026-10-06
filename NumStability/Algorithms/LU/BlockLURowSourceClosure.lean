/-
  Algorithms/LU/BlockLURowSourceClosure.lean

  Row-block-diagonal-dominance closure for Higham, Chapter 13, Theorems
  13.7 and 13.8.  This complements `BlockLUSourceClosure`'s column route.
-/

import NumStability.Algorithms.LU.BlockLUSourceClosure

namespace NumStability

/-- A zero off-diagonal block row and a singular diagonal block make the
    flattened block matrix singular. -/
theorem
    higham13_blockMatrixFlat_det_eq_zero_of_offdiag_row_zero_of_diag_det_eq_zero
    {m r : ℕ}
    (A : Fin m → Fin m → Fin r → Fin r → ℝ)
    (j : Fin m)
    (hdiagdet : Matrix.det (A j j) = 0)
    (hoff : ∀ q : Fin m, q ≠ j → ∀ s t : Fin r, A j q s t = 0) :
    Matrix.det (blockMatrixFlat A) = 0 := by
  classical
  obtain ⟨x, hxne, hxker⟩ :=
    (Matrix.exists_vecMul_eq_zero_iff (M := Matrix.of (A j j))).mpr hdiagdet
  obtain ⟨s0, hs0⟩ := higham13_exists_nonzero_coord_of_vec_ne_zero hxne
  let v : Fin m × Fin r → ℝ := fun p => if p.1 = j then x p.2 else 0
  have hvne : v ≠ 0 := by
    intro hv
    have hcoord := congr_fun hv (j, s0)
    simp [v] at hcoord
    exact hs0 hcoord
  have hmul : Matrix.vecMul v (blockMatrixFlat A) = 0 := by
    ext q
    rcases q with ⟨q, t⟩
    rw [Matrix.vecMul, dotProduct]
    change (∑ p : Fin m × Fin r, v p * A p.1 q p.2 t) = 0
    rw [Fintype.sum_prod_type]
    simp only [v, ite_mul, zero_mul]
    simp
    by_cases hq : q = j
    · subst q
      have ht := congr_fun hxker t
      simpa [Matrix.vecMul, dotProduct] using ht
    · simp [hoff q hq]
  exact (Matrix.exists_vecMul_eq_zero_iff).mp ⟨v, hvne, hmul⟩

/-- Nonsingularity contradiction form of the zero-row lemma. -/
theorem
    higham13_not_blockMatrixNonsingular_of_offdiag_row_zero_of_diag_det_eq_zero
    {m r : ℕ}
    (A : Fin m → Fin m → Fin r → Fin r → ℝ)
    (j : Fin m)
    (hdiagdet : Matrix.det (A j j) = 0)
    (hoff : ∀ q : Fin m, q ≠ j → ∀ s t : Fin r, A j q s t = 0) :
    ¬ BlockMatrixNonsingular A := by
  intro hA
  exact (blockMatrixFlat_det_ne_zero_of_blockMatrixNonsingular A hA)
    (higham13_blockMatrixFlat_det_eq_zero_of_offdiag_row_zero_of_diag_det_eq_zero
      A j hdiagdet hoff)

/-- Row-BDD diagonal-block nonsingularity from the source full-matrix
    nonsingularity hypothesis. -/
theorem
    higham13_diag_det_ne_zero_of_blockMatrixNonsingular_blockDiagDomRow_opNorm2_lowerNorm2
    {m r : ℕ} (hr : 0 < r)
    (A : Fin m → Fin m → Fin r → Fin r → ℝ)
    (hA : BlockMatrixNonsingular A)
    (hDom : IsBlockDiagDomRow m
      (fun i j => opNorm2 (A i j))
      (fun i => matMulVecLowerNorm2 hr (A i i))) :
    ∀ i : Fin m, Matrix.det (A i i) ≠ 0 := by
  intro i hdet
  have hlower := matMulVecLowerNorm2_eq_zero_of_det_eq_zero hr (A i i) hdet
  have hoffNorm : ∀ j : Fin m, i ≠ j → opNorm2 (A i j) = 0 :=
    higham13_blockDiagDomRow_offdiag_zero_of_diagBound_nonpos
      (fun i j => opNorm2 (A i j))
      (fun i => matMulVecLowerNorm2 hr (A i i))
      (fun i j => opNorm2_nonneg (A i j)) hDom i
      (by simpa using (le_of_eq hlower))
  have hoff : ∀ j : Fin m, j ≠ i → ∀ s t : Fin r, A i j s t = 0 := by
    intro j hji
    exact higham13_block_entries_zero_of_opNorm2_eq_zero
      (A i j) (hoffNorm j hji.symm)
  exact
    (higham13_not_blockMatrixNonsingular_of_offdiag_row_zero_of_diag_det_eq_zero
      A i hdet hoff) hA

/-- Exact Euclidean/operator-2 Schur inheritance for row BDD. -/
theorem higham13_blockSchur_blockDiagDomRow_opNorm2_lowerNorm2
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (A11_inv : Matrix (Fin r) (Fin r) ℝ)
    (hRight : IsRightInverse r (A 0 0) A11_inv)
    (hDom : IsBlockDiagDomRow (m + 1)
      (fun i j => opNorm2 (A i j))
      (fun i => matMulVecLowerNorm2 hr (A i i))) :
    IsBlockDiagDomRow m
      (fun i j => opNorm2 (blockSchur A A11_inv i j))
      (fun i => matMulVecLowerNorm2 hr (blockSchur A A11_inv i i)) := by
  classical
  letI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hEq : ∀ i j : Fin m,
      (blockSchur A A11_inv i j : Matrix (Fin r) (Fin r) ℝ) =
        A i.succ j.succ - A i.succ 0 * A11_inv * A 0 j.succ := by
    intro i j
    ext s t
    simp [blockSchur, Matrix.mul_apply, mul_assoc]
    simp_rw [Finset.mul_sum]
  have hpos : 0 < opNorm2 A11_inv :=
    opNorm2_pos_of_right_inverse (A 0 0) A11_inv hRight
  have hrecip := matMulVecLowerNorm2_eq_inv_opNorm2_of_isRightInverse
    hr (A 0 0) A11_inv hRight
  apply block_diag_dom_schur_inherit_row
      (blockNorm := fun i j => opNorm2 (A i j))
      (hNorm := fun i j => opNorm2_nonneg (A i j))
      (invDiagBound := fun i => matMulVecLowerNorm2 hr (A i i))
      (normInv := opNorm2 A11_inv)
      (hNormInv := opNorm2_nonneg A11_inv)
      (hDom := hDom)
      (hNormInvBound := ?_)
      (schurNorm := fun i j => opNorm2 (blockSchur A A11_inv i j))
      (hSchurBound := ?_)
      (schurInvDiag := fun i =>
        matMulVecLowerNorm2 hr (blockSchur A A11_inv i i))
      (hSchurDiag := ?_)
  · change opNorm2 A11_inv * matMulVecLowerNorm2 hr (A 0 0) ≤ 1
    rw [hrecip]
    exact le_of_eq (mul_inv_cancel₀ (ne_of_gt hpos))
  · intro i j
    change opNorm2 (blockSchur A A11_inv i j) ≤
      opNorm2 (A i.succ j.succ) +
        opNorm2 (A i.succ 0) * opNorm2 A11_inv * opNorm2 (A 0 j.succ)
    rw [hEq i j]
    calc
      opNorm2 (A i.succ j.succ - A i.succ 0 * A11_inv * A 0 j.succ) ≤
          opNorm2 (A i.succ j.succ) +
            opNorm2 (A i.succ 0 * A11_inv * A 0 j.succ) :=
        opNorm2_sub_le _ _
      _ ≤ opNorm2 (A i.succ j.succ) +
          opNorm2 (A i.succ 0) * opNorm2 A11_inv * opNorm2 (A 0 j.succ) := by
        apply add_le_add_right
        simpa [matMul, Matrix.mul_apply] using
          opNorm2_matMul_triple_le (A i.succ 0) A11_inv (A 0 j.succ)
  · intro i
    let perturb := matMul r (matMul r (A i.succ 0) A11_inv) (A 0 i.succ)
    apply higham13_eq13_18_vecNorm2_min_lower_bound
      (fun x => matMulVec r (A i.succ i.succ) x)
      (fun x => matMulVec r perturb x)
      (fun x => matMulVec r (blockSchur A A11_inv i i) x)
      (matMulVecLowerNorm2 hr (A i.succ i.succ))
      (matMulVecLowerNorm2 hr (blockSchur A A11_inv i i))
      (opNorm2 (A i.succ 0) * opNorm2 A11_inv * opNorm2 (A 0 i.succ))
      (fun x hx => matMulVecLowerNorm2_le hr _ x hx)
      (matMulVecLowerNorm2_attained hr _)
      (by
        intro x hx
        simpa [perturb] using
          vecNorm2_matMulVec_triple_le_opNorm2_of_unit
            (A i.succ 0) A11_inv (A 0 i.succ) hx)
      (by
        intro x
        rw [hEq i i]
        simpa [perturb, matMulVec, matMul, Matrix.mul_apply, Pi.sub_apply] using
          Matrix.sub_mulVec (A i.succ i.succ)
            (A i.succ 0 * A11_inv * A 0 i.succ) x)

/-- Recursive active-pivot construction for source row BDD. -/
theorem
    higham13_algorithm13_3_exists_pivotInv_right_inverse_of_blockMatrixNonsingular_blockDiagDomRow_opNorm2_lowerNorm2
    {r : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ} (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ),
      BlockMatrixNonsingular A →
      IsBlockDiagDomRow m (fun i j => opNorm2 (A i j))
        (fun i => matMulVecLowerNorm2 hr (A i i)) →
      ∃ pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ,
        ∀ k : ℕ, ∀ hk : k < m,
          IsRightInverse r
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
              ⟨k, hk⟩ ⟨k, hk⟩) (pivotInv k) := by
  intro m
  induction m with
  | zero =>
      intro A _hA _hDom
      exact ⟨fun _ => 0, fun k hk => by omega⟩
  | succ m ih =>
      intro A hA hDom
      have hdet :=
        higham13_diag_det_ne_zero_of_blockMatrixNonsingular_blockDiagDomRow_opNorm2_lowerNorm2
          hr A hA hDom 0
      let Ainv := nonsingInv r (A 0 0)
      have hInv : IsInverse r (A 0 0) Ainv := by
        simpa [Ainv] using
          isInverse_nonsingInv_of_det_ne_zero r (A 0 0) hdet
      let S := blockSchur A Ainv
      have hS : BlockMatrixNonsingular S := by
        simpa [S] using
          blockSchur_nonsingular_of_nonsingular_of_first_block_inverse
            hInv.1 hInv.2 hA
      have hSDom : IsBlockDiagDomRow m (fun i j => opNorm2 (S i j))
          (fun i => matMulVecLowerNorm2 hr (S i i)) := by
        simpa [S] using
          higham13_blockSchur_blockDiagDomRow_opNorm2_lowerNorm2
            hr A Ainv hInv.2 hDom
      rcases ih S hS hSDom with ⟨tailInv, hTail⟩
      let pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ
        | 0 => Ainv
        | k + 1 => tailInv k
      refine ⟨pivotInv, ?_⟩
      apply
        higham13_algorithm13_3_pivot_right_inverse_of_initial_pivot_and_first_schur_tail_pivot_right_inverse
      · simpa [pivotInv, higham13_algorithm13_3_schurStageMatrixBlock,
          higham13_algorithm13_3_schurStageBlock] using hInv.2
      · intro k hk
        simpa [S, pivotInv] using hTail k hk

/-- The row version of the active one-step dominance rule follows from the
    column rule applied to transposed scalar norm tables. -/
theorem higham13_theorem13_7_active_row_dom_step_of_local_schur_bound
    {m : ℕ}
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (hStageNonneg : ∀ k : ℕ, ∀ i j : Fin m, 0 ≤ stageNorm k i j)
    (hPivotInvNonneg : ∀ k : ℕ, 0 ≤ pivotInvNorm k)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      pivotInvNorm k * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hLocal : SchurStageActiveLocalSchurBound13_8 stageNorm pivotInvNorm)
    (hDiagUpdate : SchurStageActiveDiagLowerUpdate13_7
      stageNorm stageInvDiagBound pivotInvNorm) :
    SchurStageActiveRowDomStep13_7 stageNorm stageInvDiagBound := by
  let stageT : ℕ → Fin m → Fin m → ℝ :=
    fun k i j => stageNorm k j i
  have hLocalT : SchurStageActiveLocalSchurBound13_8 stageT pivotInvNorm := by
    intro k hk i j hik hjk
    dsimp [stageT]
    calc
      stageNorm (k + 1) j i ≤
          stageNorm k j i +
            stageNorm k j ⟨k, hk⟩ * pivotInvNorm k *
              stageNorm k ⟨k, hk⟩ i := hLocal k hk j i hjk hik
      _ = stageNorm k j i +
            stageNorm k ⟨k, hk⟩ i * pivotInvNorm k *
              stageNorm k j ⟨k, hk⟩ := by ring
  have hDiagT : SchurStageActiveDiagLowerUpdate13_7
      stageT stageInvDiagBound pivotInvNorm := by
    intro k hk j hj
    convert hDiagUpdate k hk j hj using 1
    · simp [stageT]
      ring
  have hStepT : SchurStageActiveColumnDomStep13_7
      stageT stageInvDiagBound := by
    exact higham13_theorem13_7_active_column_dom_step_of_local_schur_bound
      stageT stageInvDiagBound pivotInvNorm
      (fun k i j => hStageNonneg k j i) hPivotInvNonneg hPivotInvBound
      hLocalT hDiagT
  intro k hRow i hi
  have hCol : ∀ j : Fin m, k ≤ j.val →
      ∑ q ∈ activeBlockIndices13_8 m k,
          (if q = j then 0 else stageT k q j) ≤
        stageInvDiagBound k j := by
    intro j hj
    simpa [stageT, eq_comm] using hRow j hj
  simpa [stageT, eq_comm] using hStepT k hCol i hi

/-- Concrete active row dominance for the Algorithm 13.3 matrix stages. -/
theorem
    higham13_algorithm13_3_matrix_opNorm2_active_row_dominance_of_vecNorm2_source_table
    {m r : ℕ} (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hDom : IsBlockDiagDomRow m (fun i j => opNorm2 (A i j))
      (fun i => matMulVecLowerNorm2 hr (A i i)))
    (hPivot : ∀ k : ℕ, ∀ hk : k < m,
      IsRightInverse r
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
          ⟨k, hk⟩ ⟨k, hk⟩) (pivotInv k)) :
    SchurStageActiveRowDom13_7
      (fun k i j => opNorm2
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
      (fun k i => matMulVecLowerNorm2 hr
        (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i i)) := by
  let stageNorm := fun k i j => opNorm2
    (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j)
  let stageLower := fun k i => matMulVecLowerNorm2 hr
    (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i i)
  let pivotNorm := fun k => opNorm2 (pivotInv k)
  have hDiag : SchurStageActiveDiagLowerUpdate13_7
      stageNorm stageLower pivotNorm := by
    simpa [stageNorm, stageLower, pivotNorm] using
      higham13_algorithm13_3_vecNorm2_diag_lower_update hr A pivotInv
  have hRecip : SchurStageActivePivotInvReciprocal13_7
      stageLower pivotNorm := by
    simpa [stageLower, pivotNorm] using
      higham13_algorithm13_3_vecNorm2_active_pivot_reciprocal_of_right_inverse
        hr A pivotInv hPivot
  have hBound : ∀ k : ℕ, ∀ hk : k < m,
      pivotNorm k * stageLower k ⟨k, hk⟩ ≤ 1 :=
    higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
      stageLower pivotNorm hRecip
  apply higham13_theorem13_7_active_row_dominance_of_steps
      (fun i j => opNorm2 (A i j))
      (fun i => matMulVecLowerNorm2 hr (A i i)) hDom
      stageNorm stageLower
      (by
        intro i j
        simp [stageNorm, higham13_algorithm13_3_schurStageMatrixBlock,
          higham13_algorithm13_3_schurStageBlock])
      (fun _ => rfl)
  exact higham13_theorem13_7_active_row_dom_step_of_local_schur_bound
    stageNorm stageLower pivotNorm
    (fun _k _i _j => opNorm2_nonneg _)
    (fun _k => opNorm2_nonneg _)
    hBound
    (by
      simpa [stageNorm, pivotNorm] using
        higham13_algorithm13_3_matrix_opNorm2_active_local_schur_bound
          A pivotInv)
    hDiag

/-- Row-BDD active-stage `2 * max` theorem, obtained by transposing the scalar
    norm tables in the column proof. -/
theorem higham13_theorem13_8_active_stage_block_bound_of_local_schur_bound_row
    {m : ℕ}
    (blockNorm : Fin m → Fin m → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomRow m blockNorm invDiagBound)
    (hDiagBound : ∀ i : Fin m, invDiagBound i ≤ blockNorm i i)
    (stageNorm : ℕ → Fin m → Fin m → ℝ)
    (stageInvDiagBound : ℕ → Fin m → ℝ)
    (pivotInvNorm : ℕ → ℝ)
    (hInit : ∀ i j : Fin m, stageNorm 0 i j = blockNorm i j)
    (hStageNonneg : ∀ k : ℕ, ∀ i j : Fin m, 0 ≤ stageNorm k i j)
    (hPivotInvNonneg : ∀ k : ℕ, 0 ≤ pivotInvNorm k)
    (hActiveDom : SchurStageActiveRowDom13_7 stageNorm stageInvDiagBound)
    (hPivotInvBound : ∀ k : ℕ, ∀ hk : k < m,
      pivotInvNorm k * stageInvDiagBound k ⟨k, hk⟩ ≤ 1)
    (hLocal : SchurStageActiveLocalSchurBound13_8 stageNorm pivotInvNorm)
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, blockNorm i j ≤ normMax) :
    ∀ k : ℕ, ∀ i j : Fin m, k ≤ i.val → k ≤ j.val →
      stageNorm k i j ≤ 2 * normMax := by
  let blockT : Fin m → Fin m → ℝ := fun i j => blockNorm j i
  let stageT : ℕ → Fin m → Fin m → ℝ :=
    fun k i j => stageNorm k j i
  have hDomT : IsBlockDiagDomCol m blockT invDiagBound := by
    simpa [blockT] using
      (isBlockDiagDomRow_iff_col_transpose m blockNorm invDiagBound).mp hDom
  have hActiveT : SchurStageActiveColumnDom13_7 stageT stageInvDiagBound := by
    intro k j hj
    simpa [stageT, eq_comm] using hActiveDom k j hj
  have hLocalT : SchurStageActiveLocalSchurBound13_8 stageT pivotInvNorm := by
    intro k hk i j hik hjk
    dsimp [stageT]
    calc
      stageNorm (k + 1) j i ≤
          stageNorm k j i + stageNorm k j ⟨k, hk⟩ * pivotInvNorm k *
            stageNorm k ⟨k, hk⟩ i := hLocal k hk j i hjk hik
      _ = stageNorm k j i + stageNorm k ⟨k, hk⟩ i * pivotInvNorm k *
            stageNorm k j ⟨k, hk⟩ := by ring
  intro k i j hik hjk
  simpa [stageT] using
    higham13_theorem13_8_active_stage_block_bound_of_local_schur_bound
      blockT invDiagBound hDomT
      (by intro q; simpa [blockT] using hDiagBound q)
      stageT stageInvDiagBound pivotInvNorm
      (by intro p q; simpa [stageT, blockT] using hInit q p)
      (fun n p q => hStageNonneg n q p) hPivotInvNonneg hActiveT
      hPivotInvBound hLocalT normMax
      (by intro p q; simpa [blockT] using hMax q p)
      k j i hjk hik

/-- Higham, Theorem 13.7, source-facing Euclidean row-BDD endpoint. -/
theorem higham13_theorem13_7_algorithm13_3_opNorm2_row
    {m r : ℕ} (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hA : BlockMatrixNonsingular A)
    (hDiagRight : ∀ i : Fin m, IsRightInverse r (A i i) (diagInv i))
    (hDom : IsBlockDiagDomRow m (fun i j => opNorm2 (A i j))
      (fun i => (opNorm2 (diagInv i))⁻¹)) :
    ∃ pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r A
        (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)
        (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ∧
      SchurStageActiveRowDom13_7
        (fun k i j => opNorm2
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
        (fun k i => matMulVecLowerNorm2 hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i i)) := by
  have hLower : ∀ i : Fin m,
      matMulVecLowerNorm2 hr (A i i) = (opNorm2 (diagInv i))⁻¹ := by
    intro i
    exact matMulVecLowerNorm2_eq_inv_opNorm2_of_isRightInverse
      hr (A i i) (diagInv i) (hDiagRight i)
  have hDomLower : IsBlockDiagDomRow m (fun i j => opNorm2 (A i j))
      (fun i => matMulVecLowerNorm2 hr (A i i)) := by
    intro i
    simpa [hLower i] using hDom i
  rcases
      higham13_algorithm13_3_exists_pivotInv_right_inverse_of_blockMatrixNonsingular_blockDiagDomRow_opNorm2_lowerNorm2
        hr A hA hDomLower with ⟨pivotInv, hPivot⟩
  refine ⟨pivotInv,
    higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivot_left_inverse
      A pivotInv
      (higham13_algorithm13_3_pivot_left_inverse_of_pivot_right_inverse
        A pivotInv hPivot), ?_⟩
  exact
    higham13_algorithm13_3_matrix_opNorm2_active_row_dominance_of_vecNorm2_source_table
      hr A pivotInv hDomLower hPivot

/-- Higham, Theorem 13.8, source-facing Euclidean row-BDD endpoint. -/
theorem higham13_theorem13_8_algorithm13_3_opNorm2_row
    {m r : ℕ} (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hA : BlockMatrixNonsingular A)
    (hDiagRight : ∀ i : Fin m, IsRightInverse r (A i i) (diagInv i))
    (hDom : IsBlockDiagDomRow m (fun i j => opNorm2 (A i j))
      (fun i => (opNorm2 (diagInv i))⁻¹))
    (normMax : ℝ) (hMax : ∀ i j : Fin m, opNorm2 (A i j) ≤ normMax) :
    ∃ pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r A
        (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)
        (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ∧
      ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
        opNorm2 (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
          2 * normMax := by
  have hLower : ∀ i : Fin m,
      matMulVecLowerNorm2 hr (A i i) = (opNorm2 (diagInv i))⁻¹ := by
    intro i
    exact matMulVecLowerNorm2_eq_inv_opNorm2_of_isRightInverse
      hr (A i i) (diagInv i) (hDiagRight i)
  have hDomLower : IsBlockDiagDomRow m (fun i j => opNorm2 (A i j))
      (fun i => matMulVecLowerNorm2 hr (A i i)) := by
    intro i
    simpa [hLower i] using hDom i
  rcases
      higham13_algorithm13_3_exists_pivotInv_right_inverse_of_blockMatrixNonsingular_blockDiagDomRow_opNorm2_lowerNorm2
        hr A hA hDomLower with ⟨pivotInv, hPivot⟩
  let stageNorm := fun k i j => opNorm2
    (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j)
  let stageLower := fun k i => matMulVecLowerNorm2 hr
    (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i i)
  let pivotNorm := fun k => opNorm2 (pivotInv k)
  have hRecip : SchurStageActivePivotInvReciprocal13_7 stageLower pivotNorm := by
    simpa [stageLower, pivotNorm] using
      higham13_algorithm13_3_vecNorm2_active_pivot_reciprocal_of_right_inverse
        hr A pivotInv hPivot
  have hBound : ∀ k : ℕ, ∀ hk : k < m,
      pivotNorm k * stageLower k ⟨k, hk⟩ ≤ 1 :=
    higham13_theorem13_7_pivot_inverse_bound_of_reciprocal
      stageLower pivotNorm hRecip
  refine ⟨pivotInv,
    higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivot_left_inverse
      A pivotInv
      (higham13_algorithm13_3_pivot_left_inverse_of_pivot_right_inverse
        A pivotInv hPivot), ?_⟩
  intro k i j _hk hik hjk
  exact higham13_theorem13_8_active_stage_block_bound_of_local_schur_bound_row
    (fun i j => opNorm2 (A i j))
    (fun i => matMulVecLowerNorm2 hr (A i i)) hDomLower
    (fun i => matMulVecLowerNorm2_le_opNorm2 hr (A i i))
    stageNorm stageLower pivotNorm
    (by
      intro p q
      simp [stageNorm, higham13_algorithm13_3_schurStageMatrixBlock,
        higham13_algorithm13_3_schurStageBlock])
    (fun _n _p _q => opNorm2_nonneg _)
    (fun _n => opNorm2_nonneg _)
    (by
      simpa [stageNorm, stageLower] using
        higham13_algorithm13_3_matrix_opNorm2_active_row_dominance_of_vecNorm2_source_table
          hr A pivotInv hDomLower hPivot)
    hBound
    (by
      simpa [stageNorm, pivotNorm] using
        higham13_algorithm13_3_matrix_opNorm2_active_local_schur_bound A pivotInv)
    normMax hMax k i j hik hjk

end NumStability
