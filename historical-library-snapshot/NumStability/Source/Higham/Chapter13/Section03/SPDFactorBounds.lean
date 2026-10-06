import NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefinite
import NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefiniteFactorBounds
import NumStability.Source.Higham.Chapter13.Equation24
import NumStability.Source.Higham.Chapter13.Lemma09
import NumStability.Source.Higham.Chapter13.Lemma10.SchurComplement
import NumStability.Source.Higham.Chapter13.Problem04.BlockInverseBounds
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStages
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis

/-!
# Higham Section 13.3 SPD factor bounds

Source-facing recursive SPD certificates and the concrete equation (13.24)
factor bounds for Algorithm 13.3.
-/

namespace NumStability

/-- One source SPD elimination step, with all data needed by the recursive
    Eq. (13.24) proof.  Lemma 13.9 bounds the whole multiplier block-column;
    the SPD Schur facts and Lemma 13.10's two operator halves propagate the
    common `A` and `A⁻¹` radii to the tail. -/
theorem higham13_spd_first_step_source_certificates
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (normA normAinv : ℝ) (hNormA : 0 ≤ normA) (hNormAinv : 0 ≤ normAinv)
    (hSPD : IsSymPosDef ((m + 1) * r) (blockMatrixFlatFin A))
    (hAop : finiteOpNorm2Le (blockMatrixFlatFin A) normA)
    (hAinvop : finiteOpNorm2Le
      (nonsingInv ((m + 1) * r) (blockMatrixFlatFin A)) normAinv) :
    IsInverse r (A 0 0) (nonsingInv r (A 0 0)) ∧
      IsSymPosDef (m * r)
        (blockMatrixFlatFin (blockSchur A (nonsingInv r (A 0 0)))) ∧
      rectOpNorm2Le
        (rectMatMul (blockMatrixFirstSplitA21 A) (nonsingInv r (A 0 0)))
        (Real.sqrt (normA * normAinv)) ∧
      finiteOpNorm2Le
        (blockMatrixFlatFin (blockSchur A (nonsingInv r (A 0 0)))) normA ∧
      finiteOpNorm2Le
        (nonsingInv (m * r)
          (blockMatrixFlatFin (blockSchur A (nonsingInv r (A 0 0)))))
        normAinv := by
  classical
  letI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  let F : Matrix (Fin (r + m * r)) (Fin (r + m * r)) ℝ :=
    blockMatrixFirstSplitFlat A
  let A11 : Matrix (Fin r) (Fin r) ℝ := blockMatrixFirstSplitA11 A
  let A12 : Matrix (Fin r) (Fin (m * r)) ℝ := blockMatrixFirstSplitA12 A
  let A21 : Matrix (Fin (m * r)) (Fin r) ℝ := blockMatrixFirstSplitA21 A
  let A22 : Matrix (Fin (m * r)) (Fin (m * r)) ℝ := blockMatrixFirstSplitA22 A
  let P : Matrix (Fin r) (Fin r) ℝ := nonsingInv r (A 0 0)
  let S : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ := blockSchur A P
  have hFullGeneral : (Matrix.fromBlocks A11 A12 A21 A22).PosDef := by
    simpa [A11, A12, A21, A22] using
      blockMatrixFirstSplit_fromBlocks_posDef_of_isSymPosDef_flatFin A hSPD
  have hA12 : A12 = A21.transpose := by
    simpa [A11, A12, A21, A22] using
      blockMatrixFirstSplitA12_eq_transpose_A21_of_posDef A
        (by simpa [A11, A12, A21, A22] using hFullGeneral)
  have hFull : (Matrix.fromBlocks A11 A21.transpose A21 A22).PosDef := by
    simpa [hA12] using hFullGeneral
  have hA11pos : A11.PosDef := by
    have hHerm :
        (Matrix.fromBlocks A11 A21.transpose
          (A21.transpose).conjTranspose A22).PosDef := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hFull
    exact higham13_spd_leadingBlock_posDef A11 A21.transpose A22 hHerm
  have hA11det : Matrix.det A11 ≠ 0 :=
    ne_of_gt (Matrix.PosDef.det_pos hA11pos)
  have hA00 : A11 = A 0 0 := rfl
  have hPInv : IsInverse r (A 0 0) P := by
    simpa [P, hA00] using isInverse_nonsingInv_of_det_ne_zero r A11 hA11det
  have hFpos : Matrix.PosDef (F : Matrix (Fin (r + m * r)) (Fin (r + m * r)) ℝ) := by
    have hUniform := isSymPosDef_to_matrix_posDef (blockMatrixFlatFin A) hSPD
    change Matrix.PosDef (blockMatrixFirstSplitFlat A)
    rw [blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin_reindex]
    exact matrix_posDef_submatrix_of_injective hUniform
      blockMatrixFirstSplitToFlatFinEquiv
      blockMatrixFirstSplitToFlatFinEquiv.injective
  have hFspd : IsSymPosDef (r + m * r) F :=
    matrix_posDef_to_isSymPosDef F hFpos
  have hPartition := blockMatrixFirstSplit_fromBlocks_eq A
  have hA11block : A11 = fun i j : Fin r =>
      F (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin (m * r)))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin (m * r))) := by
    ext i j
    have h := congr_fun (congr_fun hPartition (Sum.inl i)) (Sum.inl j)
    simpa [F, A11, A12, A21, A22, Matrix.fromBlocks] using h.symm
  have hA12block : A21.transpose = fun (i : Fin r) (j : Fin (m * r)) =>
      F (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin (m * r)))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin (m * r))) := by
    ext i j
    have h := congr_fun (congr_fun hPartition (Sum.inl i)) (Sum.inr j)
    simpa [F, A11, A12, A21, A22, Matrix.fromBlocks, hA12] using h.symm
  have hA21block : A21 = fun (i : Fin (m * r)) (j : Fin r) =>
      F (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin (m * r)))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin (m * r))) := by
    ext i j
    have h := congr_fun (congr_fun hPartition (Sum.inr i)) (Sum.inl j)
    simpa [F, A11, A12, A21, A22, Matrix.fromBlocks] using h.symm
  have hA22block : A22 = fun i j : Fin (m * r) =>
      F (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin (m * r)))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin (m * r))) := by
    ext i j
    have h := congr_fun (congr_fun hPartition (Sum.inr i)) (Sum.inr j)
    simpa [F, A11, A12, A21, A22, Matrix.fromBlocks] using h.symm
  have hFirstOp : finiteOpNorm2Le F normA := by
    simpa [F] using
      finiteOpNorm2Le_blockMatrixFirstSplitFlat_of_blockMatrixFlatFin A hAop
  letI : Invertible (F : Matrix (Fin (r + m * r)) (Fin (r + m * r)) ℝ) :=
    hFpos.isUnit.invertible
  have hFinvExact : finiteOpNorm2Le (nonsingInv (r + m * r) F)
      (opNorm2 (nonsingInv ((m + 1) * r) (blockMatrixFlatFin A))) := by
    have hInvOf := finiteOpNorm2Le_invOf_reindex_equiv_nonsingInv
      (e := blockMatrixFirstSplitToFlatFinEquiv)
      (blockMatrixFlatFin A) (F : Matrix (Fin (r + m * r)) (Fin (r + m * r)) ℝ)
      (by simpa [F] using blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin_reindex A)
    have hRight : IsRightInverse (r + m * r) F
        (⅟F : Matrix (Fin (r + m * r)) (Fin (r + m * r)) ℝ) :=
      isRightInverse_of_eq_invOf F (⅟F) rfl
    have heq := nonsingInv_eq_of_isRightInverse F _ hRight
    simpa [heq] using hInvOf
  have hInvRadius :
      opNorm2 (nonsingInv ((m + 1) * r) (blockMatrixFlatFin A)) ≤ normAinv :=
    opNorm2_le_of_finiteOpNorm2Le _ hNormAinv hAinvop
  have hFinvOp : finiteOpNorm2Le (nonsingInv (r + m * r) F) normAinv :=
    finiteOpNorm2Le_mono _ hInvRadius hFinvExact
  have hFRadius : opNorm2 F ≤ normA :=
    opNorm2_le_of_finiteOpNorm2Le F hNormA hFirstOp
  have hFinvRadius : opNorm2 (nonsingInv (r + m * r) F) ≤ normAinv :=
    opNorm2_le_of_finiteOpNorm2Le _ hNormAinv hFinvOp
  have hkappa : kappa2 F (nonsingInv (r + m * r) F) ≤ normA * normAinv := by
    change opNorm2 F * opNorm2 (nonsingInv (r + m * r) F) ≤ normA * normAinv
    exact mul_le_mul hFRadius hFinvRadius
      (opNorm2_nonneg _) hNormA
  have hmultExact : rectOpNorm2Le
      (rectMatMul A21 (nonsingInv r A11))
      (Real.sqrt (kappa2 F (nonsingInv (r + m * r) F))) :=
    by
      have h :=
        higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_spd_leading_nonsingInv_kappa2
          F A22 A21 hA22block hA21block hFspd
      rw [← hA11block] at h
      exact h
  have hmult : rectOpNorm2Le (rectMatMul A21 P)
      (Real.sqrt (normA * normAinv)) := by
    have hsqrt := Real.sqrt_le_sqrt hkappa
    exact rectOpNorm2Le_mono hsqrt
      (by simpa [P, A11, hA00] using hmultExact)
  have hPeq : P = A11⁻¹ := by rfl
  have hSeq : blockMatrixFlatFin S =
      A22 - A21 * A11⁻¹ * A21.transpose := by
    have hschur := blockMatrixFirstSplit_schur_eq_blockMatrixFlatFin_blockSchur A P
    simpa [S, A12, A21, A22, P, hA12, hPeq] using hschur.symm
  have hSpos : Matrix.PosDef (blockMatrixFlatFin S) := by
    rw [hSeq]
    exact higham13_spd_schurComplement_source_posDef A11 A21 A22 hFull
  have hSspd : IsSymPosDef (m * r) (blockMatrixFlatFin S) :=
    matrix_posDef_to_isSymPosDef _ hSpos
  have hSumOp : finiteOpNorm2Le
      (fun i j : Fin r ⊕ Fin (m * r) =>
        (Matrix.fromBlocks A11 A21.transpose A21 A22) i j) normA := by
    have hRe := finiteOpNorm2Le_reindex_equiv
      (finSumFinEquiv : (Fin r ⊕ Fin (m * r)) ≃ Fin (r + m * r)) F hFirstOp
    have heq : (fun i j : Fin r ⊕ Fin (m * r) =>
        F (finSumFinEquiv i) (finSumFinEquiv j)) =
        fun i j => (Matrix.fromBlocks A11 A21.transpose A21 A22) i j := by
      simpa [F, A11, A12, A21, A22, hA12] using hPartition
    simpa [heq] using hRe
  have hSop : finiteOpNorm2Le (blockMatrixFlatFin S) normA := by
    cases m with
    | zero =>
        apply finiteOpNorm2Le_of_finiteFrobNormSq_le_sq _ hNormA
        have hempty : (Finset.univ : Finset (Fin (0 * r))) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro i _hi
          exact (Nat.not_lt_zero i.val) (by simpa using i.isLt)
        unfold finiteFrobNormSq
        rw [hempty]
        positivity
    | succ m =>
        haveI : Nonempty (Fin ((m + 1) * r)) :=
          ⟨⟨0, Nat.mul_pos (Nat.succ_pos m) hr⟩⟩
        have h := higham13_lemma13_10_schur_opNorm2Le_of_full_operator_bound
          A11 A21 A22 hFull hSumOp
        simpa [hSeq] using h
  have hSinvExact : finiteOpNorm2Le
      (nonsingInv (m * r) (blockMatrixFlatFin S))
      (opNorm2 (nonsingInv (r + m * r) F)) := by
    have h := higham13_problem13_4_Sinv_finiteOpNorm2Le_from_source_posDef_block_inverse
      F A11 A21 A22 hFull hA11block hA12block hA21block hA22block
    rw [← hSeq] at h
    simpa [nonsingInv] using h
  have hSinv : finiteOpNorm2Le
      (nonsingInv (m * r) (blockMatrixFlatFin S)) normAinv :=
    finiteOpNorm2Le_mono _ hFinvRadius hSinvExact
  simpa [P, S, A21] using ⟨hPInv, hSspd, hmult, hSop, hSinv⟩

/-- Recursive source-facing SPD factor certificate for Algorithm 13.3.

    From SPD and operator certificates for the original matrix and its
    canonical inverse, this constructs every active pivot, the concrete block
    LU factors, and the two global bounds used in equation (13.24):
    `||L||₂ ≤ 1 + m sqrt(normA*normAinv)` and
    `||U||₂ ≤ sqrt(m) normA`. -/
theorem higham13_algorithm13_3_spd_factor_norm_certificates
    {r : ℕ} (hr : 0 < r) :
    ∀ {m : ℕ}
      (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
      (normA normAinv : ℝ),
      0 ≤ normA → 0 ≤ normAinv →
      IsSymPosDef (m * r) (blockMatrixFlatFin A) →
      finiteOpNorm2Le (blockMatrixFlatFin A) normA →
      finiteOpNorm2Le (nonsingInv (m * r) (blockMatrixFlatFin A)) normAinv →
      ∃ pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ,
        (∀ k : ℕ, ∀ hk : k < m,
          IsRightInverse r
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
              ⟨k, hk⟩ ⟨k, hk⟩)
            (pivotInv k)) ∧
        BlockLUFactSpec m r A
          (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)
          (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ∧
        finiteOpNorm2Le
          (blockMatrixFlatFin
            (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv))
          (1 + (m : ℝ) * Real.sqrt (normA * normAinv)) ∧
        finiteOpNorm2Le
          (blockMatrixFlatFin
            (higham13_algorithm13_3_upperFromMatrixStages A pivotInv))
          (Real.sqrt (m : ℝ) * normA) := by
  intro m
  induction m with
  | zero =>
      intro A normA normAinv hNormA hNormAinv _hSPD _hAop _hAinvop
      let pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ := fun _ => 0
      have hPivot : ∀ k : ℕ, ∀ hk : k < 0,
          IsRightInverse r
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
              ⟨k, hk⟩ ⟨k, hk⟩) (pivotInv k) := by
        intro k hk
        omega
      have hFact : BlockLUFactSpec 0 r A
          (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)
          (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) := by
        exact
          higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivot_left_inverse
            A pivotInv (by intro k hk; omega)
      refine ⟨pivotInv, hPivot, hFact, ?_, ?_⟩
      · apply finiteOpNorm2Le_blockMatrixFlatFin_zero
        norm_num
      · apply finiteOpNorm2Le_blockMatrixFlatFin_zero
        simp
  | succ m ih =>
      intro A normA normAinv hNormA hNormAinv hSPD hAop hAinvop
      obtain ⟨hPInv, hSspd, hMult, hSop, hSinvop⟩ :=
        higham13_spd_first_step_source_certificates
          hr A normA normAinv hNormA hNormAinv hSPD hAop hAinvop
      let P : Matrix (Fin r) (Fin r) ℝ := nonsingInv r (A 0 0)
      let S : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ := blockSchur A P
      rcases ih S normA normAinv hNormA hNormAinv
          (by simpa [S, P] using hSspd)
          (by simpa [S, P] using hSop)
          (by simpa [S, P] using hSinvop) with
        ⟨tailInv, hTailPivot, hTailFact, hTailL, hTailU⟩
      let pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ
        | 0 => P
        | k + 1 => tailInv k
      have hPivot : ∀ k : ℕ, ∀ hk : k < m + 1,
          IsRightInverse r
            (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
              ⟨k, hk⟩ ⟨k, hk⟩) (pivotInv k) := by
        apply
          higham13_algorithm13_3_pivot_right_inverse_of_initial_pivot_and_first_schur_tail_pivot_right_inverse
        · simpa [pivotInv, P, higham13_algorithm13_3_schurStageMatrixBlock,
            higham13_algorithm13_3_schurStageBlock] using hPInv.2
        · intro k hk
          simpa [S, P, pivotInv] using hTailPivot k hk
      have hFact : BlockLUFactSpec (m + 1) r A
          (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)
          (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) := by
        exact
          higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivot_left_inverse
            A pivotInv
            (higham13_algorithm13_3_pivot_left_inverse_of_pivot_right_inverse
              A pivotInv hPivot)
      have hLowerEq :
          higham13_algorithm13_3_lowerFromMatrixStages A pivotInv =
            blockLUOneStepL A P
              (higham13_algorithm13_3_lowerFromMatrixStages S tailInv) := by
        simpa [P, S, pivotInv] using
          higham13_algorithm13_3_lowerFromMatrixStages_succ_eq_blockLUOneStepL
            A pivotInv
      have hUpperEq :
          higham13_algorithm13_3_upperFromMatrixStages A pivotInv =
            blockLUOneStepU A
              (higham13_algorithm13_3_upperFromMatrixStages S tailInv) := by
        simpa [P, S, pivotInv] using
          higham13_algorithm13_3_upperFromMatrixStages_succ_eq_blockLUOneStepU
            A pivotInv
      let c : ℝ := Real.sqrt (normA * normAinv)
      have hc : 0 ≤ c := Real.sqrt_nonneg _
      have hLstep : finiteOpNorm2Le
          (blockMatrixFlatFin
            (blockLUOneStepL A P
              (higham13_algorithm13_3_lowerFromMatrixStages S tailInv)))
          ((1 + (m : ℝ) * c) + c) := by
        apply finiteOpNorm2Le_blockLUOneStepL
          A P (higham13_algorithm13_3_lowerFromMatrixStages S tailInv)
          hc
          (by nlinarith [mul_nonneg (Nat.cast_nonneg m) hc])
        · simpa [P, c, rectMatMul, Matrix.mul_apply] using hMult
        · simpa [S, P, c] using hTailL
      have hL : finiteOpNorm2Le
          (blockMatrixFlatFin
            (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv))
          (1 + ((m + 1 : ℕ) : ℝ) * c) := by
        rw [hLowerEq]
        convert hLstep using 1
        push_cast
        ring
      have hUstep : finiteOpNorm2Le
          (blockMatrixFlatFin
            (blockLUOneStepU A
              (higham13_algorithm13_3_upperFromMatrixStages S tailInv)))
          (Real.sqrt ((m + 1 : ℕ) : ℝ) * normA) :=
        finiteOpNorm2Le_blockLUOneStepU A
          (higham13_algorithm13_3_upperFromMatrixStages S tailInv)
          m hNormA hAop (by simpa [S, P] using hTailU)
      have hU : finiteOpNorm2Le
          (blockMatrixFlatFin
            (higham13_algorithm13_3_upperFromMatrixStages A pivotInv))
          (Real.sqrt ((m + 1 : ℕ) : ℝ) * normA) := by
        rw [hUpperEq]
        exact hUstep
      refine ⟨pivotInv, hPivot, hFact, ?_, ?_⟩
      · simpa [c] using hL
      · exact hU

/-- Higham, Chapter 13, equation (13.24), for the concrete Algorithm 13.3
    factors of an SPD block matrix.  No factor-norm premises are assumed: the
    two bounds and their printed product consequence are derived from SPD via
    Lemmas 13.9--13.10. -/
theorem higham13_eq13_24_algorithm13_3_spd
    {m r : ℕ} (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (hSPD : IsSymPosDef (m * r) (blockMatrixFlatFin A)) :
    ∃ pivotInv : ℕ → Matrix (Fin r) (Fin r) ℝ,
      (∀ k : ℕ, ∀ hk : k < m,
        IsRightInverse r
          (higham13_algorithm13_3_schurStageMatrixBlock A pivotInv k
            ⟨k, hk⟩ ⟨k, hk⟩)
          (pivotInv k)) ∧
      BlockLUFactSpec m r A
        (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)
        (higham13_algorithm13_3_upperFromMatrixStages A pivotInv) ∧
      opNorm2
          (blockMatrixFlatFin
            (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)) ≤
        1 + (m : ℝ) *
          Real.sqrt (kappa2 (blockMatrixFlatFin A)
            (nonsingInv (m * r) (blockMatrixFlatFin A))) ∧
      opNorm2
          (blockMatrixFlatFin
            (higham13_algorithm13_3_upperFromMatrixStages A pivotInv)) ≤
        Real.sqrt (m : ℝ) * opNorm2 (blockMatrixFlatFin A) ∧
      opNorm2
          (blockMatrixFlatFin
            (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)) *
        opNorm2
          (blockMatrixFlatFin
            (higham13_algorithm13_3_upperFromMatrixStages A pivotInv)) ≤
        Real.sqrt (m : ℝ) *
          (1 + (m : ℝ) *
            Real.sqrt (kappa2 (blockMatrixFlatFin A)
              (nonsingInv (m * r) (blockMatrixFlatFin A)))) *
          opNorm2 (blockMatrixFlatFin A) := by
  let normA : ℝ := opNorm2 (blockMatrixFlatFin A)
  let normAinv : ℝ := opNorm2 (nonsingInv (m * r) (blockMatrixFlatFin A))
  have hAop : finiteOpNorm2Le (blockMatrixFlatFin A) normA :=
    finiteOpNorm2Le_of_opNorm2Le _ (opNorm2Le_opNorm2 _)
  have hAinvop : finiteOpNorm2Le
      (nonsingInv (m * r) (blockMatrixFlatFin A)) normAinv :=
    finiteOpNorm2Le_of_opNorm2Le _ (opNorm2Le_opNorm2 _)
  rcases higham13_algorithm13_3_spd_factor_norm_certificates hr
      A normA normAinv (opNorm2_nonneg _) (opNorm2_nonneg _)
      hSPD hAop hAinvop with
    ⟨pivotInv, hPivot, hFact, hLcert, hUcert⟩
  let Lflat := blockMatrixFlatFin
    (higham13_algorithm13_3_lowerFromMatrixStages A pivotInv)
  let Uflat := blockMatrixFlatFin
    (higham13_algorithm13_3_upperFromMatrixStages A pivotInv)
  let kappaA : ℝ := kappa2 (blockMatrixFlatFin A)
    (nonsingInv (m * r) (blockMatrixFlatFin A))
  have hkappa : kappaA = normA * normAinv := by
    rfl
  have hLradius : 0 ≤ 1 + (m : ℝ) * Real.sqrt kappaA := by
    positivity
  have hUradius : 0 ≤ Real.sqrt (m : ℝ) * normA := by
    exact mul_nonneg (Real.sqrt_nonneg _) (opNorm2_nonneg _)
  have hL : opNorm2 Lflat ≤ 1 + (m : ℝ) * Real.sqrt kappaA := by
    apply opNorm2_le_of_finiteOpNorm2Le Lflat hLradius
    simpa [Lflat, kappaA, hkappa, normA, normAinv] using hLcert
  have hU : opNorm2 Uflat ≤ Real.sqrt (m : ℝ) * normA := by
    apply opNorm2_le_of_finiteOpNorm2Le Uflat hUradius
    simpa [Uflat, normA] using hUcert
  have hProd : opNorm2 Lflat * opNorm2 Uflat ≤
      Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappaA) * normA :=
    higham13_eq13_24_spd_scalar_bound
      (opNorm2 Lflat) (opNorm2 Uflat) normA kappaA m
      (opNorm2_nonneg Uflat) hL hU
  refine ⟨pivotInv, hPivot, hFact, ?_, ?_, ?_⟩
  · simpa [Lflat, kappaA] using hL
  · simpa [Uflat, normA] using hU
  · simpa [Lflat, Uflat, kappaA, normA] using hProd

end NumStability
