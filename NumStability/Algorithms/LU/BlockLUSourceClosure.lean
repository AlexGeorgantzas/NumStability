/-
  Algorithms/LU/BlockLUSourceClosure.lean

  Source-level closure theorems for Higham, Chapter 13, Theorems 13.7 and
  13.8.  The main `BlockLU` module develops the one-step Schur estimates and
  the concrete Algorithm 13.3 stage machinery.  This module closes the
  missing recursive existence argument: full block nonsingularity and block
  diagonal dominance construct every active pivot inverse, the block LU
  factors, inherited Schur-complement dominance, and the `2 * max` growth
  bound, without an all-leading-prefix or prebuilt-pivot hypothesis.
-/

import NumStability.Algorithms.LU.BlockLU

namespace NumStability

/-- A singular square matrix has zero Euclidean lower norm. -/
theorem matMulVecLowerNorm2_eq_zero_of_det_eq_zero {r : ℕ}
    (hr : 0 < r) (B : Fin r → Fin r → ℝ)
    (hdet : Matrix.det B = 0) :
    matMulVecLowerNorm2 hr B = 0 := by
  classical
  letI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨x, s0, hx0, hBx⟩ :=
    higham13_exists_diag_kernel_coord_of_det_eq_zero B hdet
  have hx : x ≠ 0 := by
    intro hzero
    have := congr_fun hzero s0
    exact hx0 this
  have hxnorm_ne : vecNorm2 x ≠ 0 := by
    intro hnorm
    apply hx
    funext i
    exact (vecNorm2_eq_zero_iff x).mp hnorm i
  have hxpos : 0 < vecNorm2 x :=
    lt_of_le_of_ne (vecNorm2_nonneg x) (Ne.symm hxnorm_ne)
  let y : Fin r → ℝ := fun i => (vecNorm2 x)⁻¹ * x i
  have hy : vecNorm2 y = 1 := by
    simpa [y] using vecNorm2_inv_smul_self_of_pos x hxpos
  have hBx0 : matMulVec r B x = 0 := by
    ext s
    simpa [matMulVec] using hBx s
  have hBy0 : matMulVec r B y = 0 := by
    calc
      matMulVec r B y =
          fun i => (vecNorm2 x)⁻¹ * matMulVec r B x i := by
            simpa [y] using
              (matMulVec_const_mul_right r B (vecNorm2 x)⁻¹ x)
      _ = (fun _ : Fin r => 0) := by simp [hBx0]
      _ = 0 := rfl
  apply le_antisymm
  · calc
      matMulVecLowerNorm2 hr B ≤ vecNorm2 (matMulVec r B y) :=
        matMulVecLowerNorm2_le hr B y hy
      _ = 0 := by
        rw [hBy0]
        change vecNorm2 (fun _ : Fin r => 0) = 0
        exact vecNorm2_zero
  · unfold matMulVecLowerNorm2
    exact vecNorm2_nonneg _

/-- Every matrix entry is bounded by the exact Euclidean operator norm. -/
theorem higham13_abs_entry_le_opNorm2 {r : ℕ}
    (B : Fin r → Fin r → ℝ) (s t : Fin r) :
    |B s t| ≤ opNorm2 B := by
  have hcert := opNorm2Le_opNorm2 B
  have hcol := hcert (finiteBasisVec t)
  have hbasis : vecNorm2 (finiteBasisVec t : Fin r → ℝ) = 1 :=
    vecNorm2_finiteBasisVec t
  have hmatvec : matMulVec r B (finiteBasisVec t) = fun i => B i t := by
    simpa [matMulVec, finiteMatVec] using finiteMatVec_finiteBasisVec B t
  have hcolnorm : vecNorm2 (fun i => B i t) ≤ opNorm2 B := by
    simpa [hmatvec, hbasis] using hcol
  exact (abs_coord_le_vecNorm2 (fun i => B i t) s).trans hcolnorm

/-- Zero Euclidean operator norm forces every entry of a finite matrix to
    vanish. -/
theorem higham13_block_entries_zero_of_opNorm2_eq_zero {r : ℕ}
    (B : Fin r → Fin r → ℝ) (hB : opNorm2 B = 0) :
    ∀ s t : Fin r, B s t = 0 := by
  intro s t
  have habs : |B s t| = 0 :=
    le_antisymm
      (by simpa [hB] using higham13_abs_entry_le_opNorm2 B s t)
      (abs_nonneg _)
  exact abs_eq_zero.mp habs

/-- The diagonal-block nonsingularity step in Higham's Theorem 13.7.

    Writing the diagonal BDD entry as the attained minimum action removes the
    artificial nonpositive-bound premise used by earlier scalar wrappers.  If
    a diagonal block were singular, its lower norm would be zero, BDD would
    force its whole off-diagonal block column to vanish, and the full block
    matrix would be singular. -/
theorem
    higham13_diag_det_ne_zero_of_blockMatrixNonsingular_blockDiagDomCol_opNorm2_lowerNorm2
    {m r : ℕ} (hr : 0 < r)
    (A : Fin m → Fin m → Fin r → Fin r → ℝ)
    (hA : BlockMatrixNonsingular A)
    (hDom : IsBlockDiagDomCol m
      (fun i j => opNorm2 (A i j))
      (fun j => matMulVecLowerNorm2 hr (A j j))) :
    ∀ j : Fin m, Matrix.det (A j j) ≠ 0 := by
  intro j hdet
  have hlower : matMulVecLowerNorm2 hr (A j j) = 0 :=
    matMulVecLowerNorm2_eq_zero_of_det_eq_zero hr (A j j) hdet
  have hoffNorm : ∀ i : Fin m, i ≠ j → opNorm2 (A i j) = 0 :=
    higham13_blockDiagDomCol_offdiag_zero_of_diagBound_nonpos
      (fun i j => opNorm2 (A i j))
      (fun j => matMulVecLowerNorm2 hr (A j j))
      (fun i j => opNorm2_nonneg (A i j)) hDom j
      (by simpa using (le_of_eq hlower))
  have hoff : ∀ i : Fin m, i ≠ j → ∀ s t : Fin r, A i j s t = 0 := by
    intro i hij
    exact higham13_block_entries_zero_of_opNorm2_eq_zero
      (A i j) (hoffNorm i hij)
  exact
    (higham13_not_blockMatrixNonsingular_of_offdiag_col_zero_of_diag_det_eq_zero
      A j hdet hoff) hA

/-- The exact Euclidean/operator-2 one-step inheritance lemma used by the
    recursive proof of Theorem 13.7. -/
theorem higham13_blockSchur_blockDiagDomCol_opNorm2_lowerNorm2
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (A11_inv : Matrix (Fin r) (Fin r) ℝ)
    (hRight : IsRightInverse r (A 0 0) A11_inv)
    (hDom : IsBlockDiagDomCol (m + 1)
      (fun i j => opNorm2 (A i j))
      (fun j => matMulVecLowerNorm2 hr (A j j))) :
    IsBlockDiagDomCol m
      (fun i j => opNorm2 (blockSchur A A11_inv i j))
      (fun j => matMulVecLowerNorm2 hr (blockSchur A A11_inv j j)) := by
  classical
  letI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hSchurEq : ∀ i j : Fin m,
      (blockSchur A A11_inv i j : Matrix (Fin r) (Fin r) ℝ) =
        A i.succ j.succ - A i.succ 0 * A11_inv * A 0 j.succ := by
    intro i j
    ext s t
    simp [blockSchur, Matrix.mul_apply, mul_assoc]
    simp_rw [Finset.mul_sum]
  have hInvPos : 0 < opNorm2 A11_inv :=
    opNorm2_pos_of_right_inverse (A 0 0) A11_inv hRight
  have hRecip :
      matMulVecLowerNorm2 hr (A 0 0) = (opNorm2 A11_inv)⁻¹ :=
    matMulVecLowerNorm2_eq_inv_opNorm2_of_isRightInverse
      hr (A 0 0) A11_inv hRight
  apply block_diag_dom_schur_inherit
      (blockNorm := fun i j => opNorm2 (A i j))
      (hNorm := fun i j => opNorm2_nonneg (A i j))
      (invDiagBound := fun j => matMulVecLowerNorm2 hr (A j j))
      (normInv := opNorm2 A11_inv)
      (hNormInv := opNorm2_nonneg A11_inv)
      (hDom := hDom)
      (hNormInvBound := ?_)
      (schurNorm := fun i j => opNorm2 (blockSchur A A11_inv i j))
      (hSchurBound := ?_)
      (schurInvDiag := fun j =>
        matMulVecLowerNorm2 hr (blockSchur A A11_inv j j))
      (hSchurDiag := ?_)
  · change opNorm2 A11_inv * matMulVecLowerNorm2 hr (A 0 0) ≤ 1
    rw [hRecip]
    exact le_of_eq (mul_inv_cancel₀ (ne_of_gt hInvPos))
  · intro i j
    change opNorm2 (blockSchur A A11_inv i j) ≤
      opNorm2 (A i.succ j.succ) +
        opNorm2 (A i.succ 0) * opNorm2 A11_inv * opNorm2 (A 0 j.succ)
    rw [hSchurEq i j]
    calc
      opNorm2 (A i.succ j.succ - A i.succ 0 * A11_inv * A 0 j.succ)
          ≤ opNorm2 (A i.succ j.succ) +
              opNorm2 (A i.succ 0 * A11_inv * A 0 j.succ) :=
        opNorm2_sub_le (A i.succ j.succ)
          (A i.succ 0 * A11_inv * A 0 j.succ)
      _ ≤ opNorm2 (A i.succ j.succ) +
            opNorm2 (A i.succ 0) * opNorm2 A11_inv *
              opNorm2 (A 0 j.succ) := by
        apply add_le_add_right
        simpa [matMul, Matrix.mul_apply] using
          (opNorm2_matMul_triple_le
            (A i.succ 0) A11_inv (A 0 j.succ))
  · intro j
    let perturb : Fin r → Fin r → ℝ :=
      matMul r (matMul r (A j.succ 0) A11_inv) (A 0 j.succ)
    apply higham13_eq13_18_vecNorm2_min_lower_bound
      (fun x => matMulVec r (A j.succ j.succ) x)
      (fun x => matMulVec r perturb x)
      (fun x => matMulVec r (blockSchur A A11_inv j j) x)
      (matMulVecLowerNorm2 hr (A j.succ j.succ))
      (matMulVecLowerNorm2 hr (blockSchur A A11_inv j j))
      (opNorm2 (A j.succ 0) * opNorm2 A11_inv * opNorm2 (A 0 j.succ))
      (fun x hx => matMulVecLowerNorm2_le hr (A j.succ j.succ) x hx)
      (matMulVecLowerNorm2_attained hr (blockSchur A A11_inv j j))
      (by
        intro x hx
        simpa [perturb] using
          (vecNorm2_matMulVec_triple_le_opNorm2_of_unit
            (A j.succ 0) A11_inv (A 0 j.succ) hx))
      (by
        intro x
        rw [hSchurEq j j]
        simpa [perturb, matMulVec, matMul, Matrix.mul_apply, Pi.sub_apply] using
          (Matrix.sub_mulVec
            (A j.succ j.succ)
            (A j.succ 0 * A11_inv * A 0 j.succ) x))

/-- Higham, Theorem 13.7, recursive pivot-existence core in the Euclidean
    subordinate norm.

    This is the key missing dependency in the earlier theorem surfaces.  It
    derives the complete Algorithm 13.3 active-pivot table from the source
    hypotheses `A` nonsingular and `A` block diagonally dominant.  In
    particular, it assumes neither nonsingularity of every leading prefix nor
    any pivot inverse at an active Schur stage. -/
theorem
    higham13_algorithm13_3_exists_pivotInv_right_inverse_of_blockMatrixNonsingular_blockDiagDomCol_opNorm2_lowerNorm2
    {r : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ),
      BlockMatrixNonsingular A →
      IsBlockDiagDomCol m
        (fun i j => opNorm2 (A i j))
        (fun j => matMulVecLowerNorm2 hr (A j j)) →
      ∃ pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ,
        ∀ k : ℕ, ∀ hk : k < m,
          IsRightInverse r
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
              ⟨k, hk⟩ ⟨k, hk⟩)
            (pivotInv k) := by
  intro m
  induction m with
  | zero =>
      intro A _hA _hDom
      refine ⟨fun _ => 0, ?_⟩
      intro k hk
      omega
  | succ m ih =>
      intro A hA hDom
      have hdet : Matrix.det (A 0 0) ≠ 0 :=
        higham13_diag_det_ne_zero_of_blockMatrixNonsingular_blockDiagDomCol_opNorm2_lowerNorm2
          hr A hA hDom 0
      let A11_inv : Matrix (Fin r) (Fin r) ℝ := nonsingInv r (A 0 0)
      have hInv : IsInverse r (A 0 0) A11_inv := by
        simpa [A11_inv] using
          (isInverse_nonsingInv_of_det_ne_zero r (A 0 0) hdet)
      let S : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ :=
        blockSchur A A11_inv
      have hSnonsing : BlockMatrixNonsingular S := by
        simpa [S] using
          (blockSchur_nonsingular_of_nonsingular_of_first_block_inverse
            hInv.1 hInv.2 hA)
      have hSDom : IsBlockDiagDomCol m
          (fun i j => opNorm2 (S i j))
          (fun j => matMulVecLowerNorm2 hr (S j j)) := by
        simpa [S] using
          (higham13_blockSchur_blockDiagDomCol_opNorm2_lowerNorm2
            hr A A11_inv hInv.2 hDom)
      rcases ih S hSnonsing hSDom with ⟨tailInv, hTailInv⟩
      let pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ
        | 0 => A11_inv
        | k + 1 => tailInv k
      refine ⟨pivotInv, ?_⟩
      apply
        higham13_algorithm13_3_pivot_right_inverse_of_initial_pivot_and_first_schur_tail_pivot_right_inverse
      · simpa [pivotInv, higham13_algorithm13_3_schurStageMatrixBlock,
          higham13_algorithm13_3_schurStageBlock] using hInv.2
      · intro k hk
        simpa [S, pivotInv] using hTailInv k hk

/-- The attained Euclidean lower norm is bounded by the corresponding
    operator norm. -/
theorem matMulVecLowerNorm2_le_opNorm2 {r : ℕ} (hr : 0 < r)
    (B : Fin r → Fin r → ℝ) :
    matMulVecLowerNorm2 hr B ≤ opNorm2 B := by
  let e : Fin r → ℝ := finiteBasisVec ⟨0, hr⟩
  have he : vecNorm2 e = 1 := by
    simpa [e] using vecNorm2_finiteBasisVec (⟨0, hr⟩ : Fin r)
  calc
    matMulVecLowerNorm2 hr B ≤ vecNorm2 (matMulVec r B e) :=
      matMulVecLowerNorm2_le hr B e he
    _ ≤ opNorm2 B * vecNorm2 e := opNorm2Le_opNorm2 B e
    _ = opNorm2 B := by rw [he, mul_one]

/-- Higham, Theorem 13.7, source-facing Euclidean column-BDD endpoint.

    The initial `diagInv` table states the printed quantity
    `||A_jj^{-1}||_2^{-1}`.  From full nonsingularity and this BDD condition,
    the theorem constructs the complete Algorithm 13.3 pivot sequence, the
    concrete block LU factors, and block diagonal dominance of every active
    Schur complement. -/
theorem higham13_theorem13_7_algorithm13_3_opNorm2_column
    {m r : ℕ} (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hA : BlockMatrixNonsingular A)
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hDom : IsBlockDiagDomCol m
      (fun i j => opNorm2 (A i j))
      (fun j => (opNorm2 (diagInv j))⁻¹)) :
    ∃ pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ,
      (∀ k : ℕ, ∀ hk : k < m,
        IsRightInverse r
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩)
          (pivotInv k)) ∧
      BlockLUFactSpec m r A
        (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)
        (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ∧
      SchurStageActiveColumnDom13_7
        (fun k i j => opNorm2
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j))
        (fun k j => matMulVecLowerNorm2 hr
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k j j)) := by
  have hInit : ∀ j : Fin m,
      matMulVecLowerNorm2 hr (A j j) = (opNorm2 (diagInv j))⁻¹ := by
    intro j
    exact matMulVecLowerNorm2_eq_inv_opNorm2_of_isRightInverse
      hr (A j j) (diagInv j) (hDiagRight j)
  have hDomLower : IsBlockDiagDomCol m
      (fun i j => opNorm2 (A i j))
      (fun j => matMulVecLowerNorm2 hr (A j j)) := by
    intro j
    simpa [hInit j] using hDom j
  rcases
      higham13_algorithm13_3_exists_pivotInv_right_inverse_of_blockMatrixNonsingular_blockDiagDomCol_opNorm2_lowerNorm2
        hr A hA hDomLower with ⟨pivotInv, hPivot⟩
  have hPivotLeft :=
    higham13_algorithm13_3_pivot_left_inverse_of_pivot_right_inverse
      A pivotInv hPivot
  refine ⟨pivotInv, hPivot,
    higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivot_left_inverse
      A pivotInv hPivotLeft, ?_⟩
  exact
    higham13_algorithm13_3_matrix_opNorm2_active_column_dominance_of_vecNorm2_source_table
      hr A pivotInv (fun j => matMulVecLowerNorm2 hr (A j j))
      hDomLower (fun _ => rfl) hPivot

/-- Higham, Theorem 13.8, source-facing Euclidean column-BDD endpoint.

    Under exactly the nonsingularity and BDD data used by Theorem 13.7, this
    constructs the block LU factors and proves the printed active-stage growth
    estimate `||A_ij^(k)||_2 <= 2 * max_ij ||A_ij||_2`. -/
theorem higham13_theorem13_8_algorithm13_3_opNorm2_column
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (diagInv : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hA : BlockMatrixNonsingular A)
    (hDiagRight : ∀ j : Fin m, IsRightInverse r (A j j) (diagInv j))
    (hDom : IsBlockDiagDomCol m
      (fun i j => opNorm2 (A i j))
      (fun j => (opNorm2 (diagInv j))⁻¹))
    (normMax : ℝ)
    (hMax : ∀ i j : Fin m, opNorm2 (A i j) ≤ normMax) :
    ∃ pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ,
      BlockLUFactSpec m r A
        (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)
        (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ∧
      ∀ k : ℕ, ∀ i j : Fin m, k ≤ m → k ≤ i.val → k ≤ j.val →
        opNorm2
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k i j) ≤
            2 * normMax := by
  have hInit : ∀ j : Fin m,
      matMulVecLowerNorm2 hr (A j j) = (opNorm2 (diagInv j))⁻¹ := by
    intro j
    exact matMulVecLowerNorm2_eq_inv_opNorm2_of_isRightInverse
      hr (A j j) (diagInv j) (hDiagRight j)
  have hDomLower : IsBlockDiagDomCol m
      (fun i j => opNorm2 (A i j))
      (fun j => matMulVecLowerNorm2 hr (A j j)) := by
    intro j
    simpa [hInit j] using hDom j
  rcases
      higham13_algorithm13_3_exists_pivotInv_right_inverse_of_blockMatrixNonsingular_blockDiagDomCol_opNorm2_lowerNorm2
        hr A hA hDomLower with ⟨pivotInv, hPivot⟩
  have hPivotLeft :=
    higham13_algorithm13_3_pivot_left_inverse_of_pivot_right_inverse
      A pivotInv hPivot
  refine ⟨pivotInv,
    higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivot_left_inverse
      A pivotInv hPivotLeft, ?_⟩
  exact
    higham13_algorithm13_3_matrix_opNorm2_active_stage_bound_of_vecNorm2_source_table
      hm hr A pivotInv (fun j => matMulVecLowerNorm2 hr (A j j))
      hDomLower (fun j => matMulVecLowerNorm2_le_opNorm2 hr (A j j))
      (fun _ => rfl) hPivot normMax hMax

end NumStability
