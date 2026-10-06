import NumStability.Algorithms.LeastSquares.Higham20Theorem20_7ActualRhs

namespace NumStability

open scoped BigOperators

namespace Theorem20_7

/-!
# Swap-aware assembly for the actually rounded source trace

The concrete source executor is naturally specified only on its `n` active
stages.  These totalized sequences agree with it on that horizon and use the
identity/zero continuation afterwards.  This makes the generic swap-aware
telescope applicable without introducing any numerical premise.
-/

noncomputable def sourceConstructedPivotedStoredQRPseqTotal
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) : Fin m → Fin m → ℝ :=
  if k < n then sourceConstructedPivotedStoredQRPseq fp hn hmn A k
  else idMatrix m

noncomputable def sourceConstructedPivotedStoredQRSwapSeqTotal
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) : Equiv.Perm (Fin n) :=
  if k < n then sourceConstructedPivotedStoredQRSwapSeq fp hn hmn A k
  else Equiv.refl (Fin n)

noncomputable def sourceConstructedPivotedStoredQREseqTotal
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) : Fin m → Fin n → ℝ :=
  if k < n then sourceConstructedPivotedStoredQREseq fp hn hmn A k
  else 0

theorem sourceConstructedPivotedStoredQRPseqTotal_orthogonal
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) :
    IsOrthogonal m
      (sourceConstructedPivotedStoredQRPseqTotal fp hn hmn A k) := by
  by_cases hk : k < n
  · simp only [sourceConstructedPivotedStoredQRPseqTotal, if_pos hk]
    exact sourceConstructedPivotedStoredQRPseq_orthogonal_unconditional
      fp hn hmn A k
  · simp only [sourceConstructedPivotedStoredQRPseqTotal, if_neg hk]
    exact idMatrix_orthogonal m

theorem sourceConstructedPivotedStoredQR_step_with_residual_total
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n)
    (i : Fin m) (j : Fin n) :
    fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A (k + 1) i j =
      matMulRect m m n
          (sourceConstructedPivotedStoredQRPseqTotal fp hn hmn A k)
          (Wave13.columnPermuteMatrix
            (fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A k)
            (sourceConstructedPivotedStoredQRSwapSeqTotal
              fp hn hmn A k)) i j +
        sourceConstructedPivotedStoredQREseqTotal fp hn hmn A k i j := by
  simp only [sourceConstructedPivotedStoredQRPseqTotal,
    sourceConstructedPivotedStoredQRSwapSeqTotal,
    sourceConstructedPivotedStoredQREseqTotal,
    if_pos hk]
  exact sourceConstructedPivotedStoredQR_step_with_residual
    fp hn hmn A k i j

noncomputable def sourceConstructedPivotedStoredQRQ
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) : Fin m → Fin m → ℝ :=
  Wave19.Qacc (sourceConstructedPivotedStoredQRPseqTotal fp hn hmn A) n

noncomputable def sourceConstructedPivotedStoredQRPi
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) : Equiv.Perm (Fin n) :=
  pivotPermAcc (sourceConstructedPivotedStoredQRSwapSeqTotal fp hn hmn A) n

noncomputable def sourceConstructedPivotedStoredQRdA
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  pivotDAacc
    (sourceConstructedPivotedStoredQRPseqTotal fp hn hmn A)
    (sourceConstructedPivotedStoredQRSwapSeqTotal fp hn hmn A)
    (sourceConstructedPivotedStoredQREseqTotal fp hn hmn A) n

/-- Premise-free Ch19.6 factorization endpoint for the literal, actually
rounded, actively pivoted source trace. -/
theorem fl_sourceConstructedPivotedStoredQR_actual_factorization
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) :
    let Q := sourceConstructedPivotedStoredQRQ fp hn hmn A
    let R := fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A n
    let pi := sourceConstructedPivotedStoredQRPi fp hn hmn A
    let dA := sourceConstructedPivotedStoredQRdA fp hn hmn A
    IsOrthogonal m Q ∧
      IsUpperTrapezoidal m n R ∧
      (∀ i j, R i j =
        matMulRect m m n (matTranspose Q)
          (fun a b => Wave13.columnPermuteMatrix A pi a b + dA a b) i j) ∧
      ∀ i j, Wave13.columnPermuteMatrix A pi i j + dA i j =
        matMulRect m m n Q R i j := by
  dsimp only
  let Pseq := sourceConstructedPivotedStoredQRPseqTotal fp hn hmn A
  let Sseq := sourceConstructedPivotedStoredQRSwapSeqTotal fp hn hmn A
  let Eseq := sourceConstructedPivotedStoredQREseqTotal fp hn hmn A
  let Q := Wave19.Qacc Pseq n
  let R := fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A n
  let pi := pivotPermAcc Sseq n
  let dA := pivotDAacc Pseq Sseq Eseq n
  let B : Fin m → Fin n → ℝ := fun i j =>
    Wave13.columnPermuteMatrix A pi i j + dA i j
  have hP : ∀ k, IsOrthogonal m (Pseq k) := by
    intro k
    exact sourceConstructedPivotedStoredQRPseqTotal_orthogonal
      fp hn hmn A k
  have hQ : IsOrthogonal m Q := Wave19.Qacc_orthogonal Pseq hP n
  have hR : IsUpperTrapezoidal m n R :=
    fl_sourceConstructedPivotedStoredQRMatrixSeq_upperTrapezoidal
      fp hn hmn A
  have hTel : ∀ i j, R i j =
      matMulRect m m n (matTranspose Q) B i j := by
    intro i j
    simpa [Pseq, Sseq, Eseq, Q, R, pi, dA, B,
      fl_sourceConstructedPivotedStoredQRMatrixSeq] using
      pivoted_entrywise_residual_telescope n
        (fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A)
        Pseq Sseq Eseq hP
        (fun k hk i j =>
          sourceConstructedPivotedStoredQR_step_with_residual_total
            fp hn hmn A k hk i j) i j
  have hTelEq : R = matMulRect m m n (matTranspose Q) B :=
    funext fun i => funext fun j => hTel i j
  have hQQT : matMul m Q (matTranspose Q) = idMatrix m :=
    funext fun i => funext fun j => hQ.right_inv i j
  have hReconstructEq : matMulRect m m n Q R = B := by
    rw [hTelEq, ← matMulRect_assoc_square_left, hQQT,
      matMulRect_id_left]
  refine ⟨hQ, hR, ?_, ?_⟩
  · intro i j
    simpa [Q, R, pi, dA, B, Pseq, Sseq, Eseq,
      sourceConstructedPivotedStoredQRQ,
      sourceConstructedPivotedStoredQRPi,
      sourceConstructedPivotedStoredQRdA] using hTel i j
  · intro i j
    simpa [Q, R, pi, dA, B, Pseq, Sseq, Eseq,
      sourceConstructedPivotedStoredQRQ,
      sourceConstructedPivotedStoredQRPi,
      sourceConstructedPivotedStoredQRdA] using
        (congrFun (congrFun hReconstructEq i) j).symm

/-- Totalized completed-column residuals remain zero after multiplication by
the accumulated exact reflectors. -/
theorem sourceConstructedPivotedStoredQR_QaccE_completed_column_zero
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (k : ℕ) (i : Fin m) (j : Fin n) (hj : j.val < k) :
    matMulRect m m n
        (Wave19.Qacc
          (sourceConstructedPivotedStoredQRPseqTotal fp hn hmn A) (k + 1))
        (sourceConstructedPivotedStoredQREseqTotal fp hn hmn A k) i j = 0 := by
  by_cases hk : k < n
  · simp only [sourceConstructedPivotedStoredQREseqTotal, if_pos hk]
    unfold matMulRect
    apply Finset.sum_eq_zero
    intro s _
    rw [sourceConstructedPivotedStoredQREseq_completed_column_zero
      fp hn hmn A k hk s j hj]
    ring
  · simp only [sourceConstructedPivotedStoredQREseqTotal, if_neg hk]
    simp [matMulRect]

/-! ## Local column norms and rounded-growth transport -/

noncomputable def sourceConstructedPivotedStoredQRResidualNormCoeff
    (fp : FPModel) (m : ℕ) : ℝ :=
  gamma fp (m + 1) + fp.u +
    2 * Real.sqrt 2 * gamma fp (11 * m + 23)

theorem sourceConstructedPivotedStoredQRResidualNormCoeff_nonneg
    (fp : FPModel) (m : ℕ)
    (hvalid : gammaValid fp (11 * m + 23)) :
    0 ≤ sourceConstructedPivotedStoredQRResidualNormCoeff fp m := by
  have hgsmall : 0 ≤ gamma fp (m + 1) :=
    gamma_nonneg fp (gammaValid_mono fp (by omega) hvalid)
  have hgbig : 0 ≤ gamma fp (11 * m + 23) := gamma_nonneg fp hvalid
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  unfold sourceConstructedPivotedStoredQRResidualNormCoeff
  exact add_nonneg (add_nonneg hgsmall fp.u_nonneg)
    (mul_nonneg (mul_nonneg (by norm_num) hsqrt) hgbig)

theorem sourceConstructedPivotedStoredQRExactRawVector_vecNorm2_le_two_sigma
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) :
    vecNorm2 (sourceConstructedPivotedStoredQRExactRawVector
      fp hn hmn A k) ≤
      2 * sourceConstructedPivotedStoredQRSigma fp hn hmn A k := by
  let hm : 0 < m := lt_of_lt_of_le hn hmn
  let x := sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k
  let S := sourceConstructedPivotedStoredQRRowSwap fp hn hmn A k
  have hperm : vecNorm2
      (sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A k) =
        vecNorm2 (householderVector hm x) := by
    rw [sourceConstructedPivotedStoredQRExactRawVector_eq_vecPermute]
    unfold vecNorm2
    rw [vecNorm2Sq_permute]
    rfl
  rw [hperm]
  simpa [x, sourceConstructedPivotedStoredQRSigma] using
    householderVector_vecNorm2_le_two hm x

/-- Exact shape of the local residual on the displayed pivot column: only the
rounded signed diagonal differs from the exact shadow. -/
theorem sourceConstructedPivotedStoredQREseq_pivotColumn_eq_smul_basis
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n) :
    (fun i => sourceConstructedPivotedStoredQREseq fp hn hmn A k i
      (pivotedQRActiveCol k hk)) =
      fun i =>
        (sourceConstructedPivotedStoredQRRoundedAlpha fp hn hmn A k -
          householderAlpha (lt_of_lt_of_le hn hmn)
            (sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k)) *
          finiteBasisVec (pivotedQRActiveRow hmn k hk) i := by
  funext i
  let row := pivotedQRActiveRow hmn k hk
  let col := pivotedQRActiveCol k hk
  by_cases hir : i = row
  · subst i
    rw [sourceConstructedPivotedStoredQREseq,
      fl_sourceConstructedPivotedStoredQRMatrixSeq_succ_pivot_eq_alpha
        fp hn hmn A k hk]
    change sourceConstructedPivotedStoredQRRoundedAlpha fp hn hmn A k -
      matMulVec m (sourceConstructedPivotedStoredQRPseq fp hn hmn A k)
        (fun r => sourceConstructedPivotedStoredQRSwappedPanel
          fp hn hmn A k r (pivotedQRActiveCol k hk))
        (pivotedQRActiveRow hmn k hk) = _
    rw [sourceConstructedPivotedStoredQRPseq_pivot_eq_exactAlpha
      fp hn hmn A k hk]
    simp [finiteBasisVec, row]
  · have hine : i.val ≠ k := by
      intro hik
      apply hir
      apply Fin.ext
      simpa [row, pivotedQRActiveRow] using hik
    rcases lt_or_gt_of_ne hine with hi | hi
    · rw [sourceConstructedPivotedStoredQREseq_completed_row_zero
        fp hn hmn A k hk i hi (pivotedQRActiveCol k hk)]
      simp [finiteBasisVec, hir, row]
    · rw [sourceConstructedPivotedStoredQREseq,
        congrFun (congrFun
          (fl_sourceConstructedPivotedStoredQRMatrixSeq_succ_of_lt
            fp hn hmn A k hk) i) (pivotedQRActiveCol k hk),
        fl_householderCoxHighamConstructedPanelStep_pivotTail_eq_zero
          fp (lt_of_lt_of_le hn hmn)
            (pivotedQRActiveRow hmn k hk) (pivotedQRActiveCol k hk)
            (sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k)
            hi (by simp [pivotedQRActiveCol])]
      change 0 - matMulVec m
        (sourceConstructedPivotedStoredQRPseq fp hn hmn A k)
        (fun r => sourceConstructedPivotedStoredQRSwappedPanel
          fp hn hmn A k r (pivotedQRActiveCol k hk)) i = _
      rw [sourceConstructedPivotedStoredQRPseq_pivot_tail_zero
        fp hn hmn A k hk i hi]
      simp [finiteBasisVec, hir, row]

theorem sourceConstructedPivotedStoredQREseq_pivotColumn_vecNorm2_le
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (k : ℕ) (hk : k < n) :
    vecNorm2 (fun i => sourceConstructedPivotedStoredQREseq
      fp hn hmn A k i (pivotedQRActiveCol k hk)) ≤
      gamma fp (m + 1) *
        sourceConstructedPivotedStoredQRSigma fp hn hmn A k := by
  let row := pivotedQRActiveRow hmn k hk
  let err := sourceConstructedPivotedStoredQRRoundedAlpha fp hn hmn A k -
    householderAlpha (lt_of_lt_of_le hn hmn)
      (sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k)
  rw [sourceConstructedPivotedStoredQREseq_pivotColumn_eq_smul_basis
    fp hn hmn A k hk]
  change vecNorm2 (fun i => err * finiteBasisVec row i) ≤ _
  rw [vecNorm2_smul, vecNorm2_finiteBasisVec]
  simp only [mul_one]
  have herr := sourceConstructedPivotedStoredQRRoundedAlpha_error
    fp hn hmn A k hk (gammaValid_mono fp (by omega) hvalid)
  simpa [err, row, sourceConstructedPivotedStoredQRSigma,
    abs_householderScale_eq_vecNorm2 (lt_of_lt_of_le hn hmn)
      (sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k)] using herr

/-- A genuinely updated trailing residual column has the concrete
constructor/application norm bound. -/
theorem sourceConstructedPivotedStoredQREseq_trailing_vecNorm2_le
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (k : ℕ) (hk : k < n) (j : Fin n) (hj : k < j.val) :
    vecNorm2 (fun i => sourceConstructedPivotedStoredQREseq
      fp hn hmn A k i j) ≤
      (fp.u + 2 * Real.sqrt 2 * gamma fp (11 * m + 23)) *
        sourceConstructedPivotedStoredQRSigma fp hn hmn A k := by
  let S := sourceConstructedPivotedStoredQRRowSwap fp hn hmn A k
  let b : Fin m → ℝ := fun q =>
    sourceConstructedPivotedStoredQRActivePanelPerm fp hn hmn A k q j
  let bp : Fin m → ℝ := vecPermute S b
  let v := sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A k
  let E : Fin m → ℝ := fun i =>
    sourceConstructedPivotedStoredQREseq fp hn hmn A k i j
  let d := gamma fp (11 * m + 23) * Real.sqrt 2
  have hS : ∀ q, S (S q) = q := by
    intro q
    simp [S, sourceConstructedPivotedStoredQRRowSwap,
      sourceConstructedRowSwap, hk]
  have hbp : ∀ i, bp i =
      if i.val < k then 0 else
        sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k i j := by
    intro i
    simp only [bp, b, vecPermute,
      sourceConstructedPivotedStoredQRActivePanelPerm,
      sourceConstructedActivePanelPerm]
    rw [hS i]
  have hentry : ∀ i, |E i| ≤ fp.u * |bp i| + d * |v i| := by
    intro i
    by_cases hi : i.val < k
    · have hE := sourceConstructedPivotedStoredQREseq_completed_row_zero
        fp hn hmn A k hk i hi j
      have hv := sourceConstructedPivotedStoredQRExactRawVector_zero_prefix
        fp hn hmn A k hk i hi
      rw [show E i = 0 by simpa [E] using hE,
        hbp i, if_pos hi,
        show v i = 0 by simpa [v] using hv]
      simp
    · have hraw :=
        sourceConstructedPivotedStoredQREseq_activeTrailing_abs_le_unconditional
          fp hn hmn A hvalid k hk i (Nat.le_of_not_gt hi) j hj
      rw [hbp i, if_neg hi]
      simpa [E, v, d, mul_assoc] using hraw
  have hbnorm : vecNorm2 bp ≤
      sourceConstructedPivotedStoredQRSigma fp hn hmn A k := by
    have hperm : vecNorm2 bp = vecNorm2 b := by
      unfold bp vecNorm2
      rw [vecNorm2Sq_permute]
    rw [hperm]
    exact sourceConstructedPivotedStoredQRActiveInput_pivot_max
      fp hn hmn A k hk j (Nat.le_of_lt hj)
  have hvnorm : vecNorm2 v ≤
      2 * sourceConstructedPivotedStoredQRSigma fp hn hmn A k := by
    exact sourceConstructedPivotedStoredQRExactRawVector_vecNorm2_le_two_sigma
      fp hn hmn A k
  have hd : 0 ≤ d := mul_nonneg (gamma_nonneg fp hvalid)
    (Real.sqrt_nonneg 2)
  have hnorm := vecNorm2_le_of_abs_le_two_term E bp v fp.u d
    fp.u_nonneg hd hentry
  calc
    vecNorm2 (fun i => sourceConstructedPivotedStoredQREseq
        fp hn hmn A k i j) = vecNorm2 E := by rfl
    _ ≤ fp.u * vecNorm2 bp + d * vecNorm2 v := hnorm
    _ ≤ fp.u * sourceConstructedPivotedStoredQRSigma fp hn hmn A k +
        d * (2 * sourceConstructedPivotedStoredQRSigma fp hn hmn A k) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hbnorm fp.u_nonneg)
        (mul_le_mul_of_nonneg_left hvnorm hd)
    _ = (fp.u + 2 * Real.sqrt 2 * gamma fp (11 * m + 23)) *
        sourceConstructedPivotedStoredQRSigma fp hn hmn A k := by
      simp only [d]
      ring

/-- Uniform norm bound for every local matrix residual column. -/
theorem sourceConstructedPivotedStoredQREseq_vecNorm2_le_sigma
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (k : ℕ) (hk : k < n) (j : Fin n) :
    vecNorm2 (fun i => sourceConstructedPivotedStoredQREseq
      fp hn hmn A k i j) ≤
      sourceConstructedPivotedStoredQRResidualNormCoeff fp m *
        sourceConstructedPivotedStoredQRSigma fp hn hmn A k := by
  have hsigma0 : 0 ≤ sourceConstructedPivotedStoredQRSigma
      fp hn hmn A k := vecNorm2_nonneg _
  have hgsmall : 0 ≤ gamma fp (m + 1) :=
    gamma_nonneg fp (gammaValid_mono fp (by omega) hvalid)
  have hdelta0 : 0 ≤ fp.u +
      2 * Real.sqrt 2 * gamma fp (11 * m + 23) := by
    have hgbig := gamma_nonneg fp hvalid
    have hsqrt := Real.sqrt_nonneg 2
    exact add_nonneg fp.u_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hsqrt) hgbig)
  by_cases hjPrev : j.val < k
  · have hzero : (fun i => sourceConstructedPivotedStoredQREseq
        fp hn hmn A k i j) = 0 := by
      funext i
      exact sourceConstructedPivotedStoredQREseq_completed_column_zero
        fp hn hmn A k hk i j hjPrev
    rw [hzero]
    change vecNorm2 (fun _ : Fin m => 0) ≤ _
    rw [vecNorm2_zero]
    exact mul_nonneg
      (sourceConstructedPivotedStoredQRResidualNormCoeff_nonneg
        fp m hvalid) hsigma0
  · by_cases hjPivot : j.val = k
    · have hjEq : j = pivotedQRActiveCol k hk := Fin.ext hjPivot
      subst j
      have hpivot :=
        sourceConstructedPivotedStoredQREseq_pivotColumn_vecNorm2_le
          fp hn hmn A hvalid k hk
      calc
        vecNorm2 (fun i => sourceConstructedPivotedStoredQREseq fp hn hmn A k i
            (pivotedQRActiveCol k hk)) ≤
            gamma fp (m + 1) *
              sourceConstructedPivotedStoredQRSigma fp hn hmn A k := hpivot
        _ ≤ sourceConstructedPivotedStoredQRResidualNormCoeff fp m *
              sourceConstructedPivotedStoredQRSigma fp hn hmn A k := by
          apply mul_le_mul_of_nonneg_right _ hsigma0
          unfold sourceConstructedPivotedStoredQRResidualNormCoeff
          linarith
    · have htrail :=
        sourceConstructedPivotedStoredQREseq_trailing_vecNorm2_le
          fp hn hmn A hvalid k hk j (by omega)
      calc
        vecNorm2 (fun i => sourceConstructedPivotedStoredQREseq
            fp hn hmn A k i j) ≤
            (fp.u + 2 * Real.sqrt 2 * gamma fp (11 * m + 23)) *
              sourceConstructedPivotedStoredQRSigma fp hn hmn A k := htrail
        _ ≤ sourceConstructedPivotedStoredQRResidualNormCoeff fp m *
              sourceConstructedPivotedStoredQRSigma fp hn hmn A k := by
          apply mul_le_mul_of_nonneg_right _ hsigma0
          unfold sourceConstructedPivotedStoredQRResidualNormCoeff
          linarith

noncomputable def sourceConstructedPivotedStoredQRGrowthFactor
    (fp : FPModel) (m : ℕ) : ℝ :=
  1 + (fp.u + 2 * Real.sqrt 2 * gamma fp (11 * m + 23))

theorem one_le_sourceConstructedPivotedStoredQRGrowthFactor
    (fp : FPModel) (m : ℕ)
    (hvalid : gammaValid fp (11 * m + 23)) :
    1 ≤ sourceConstructedPivotedStoredQRGrowthFactor fp m := by
  have hgbig : 0 ≤ gamma fp (11 * m + 23) := gamma_nonneg fp hvalid
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  unfold sourceConstructedPivotedStoredQRGrowthFactor
  have htail : 0 ≤ 2 * Real.sqrt 2 * gamma fp (11 * m + 23) :=
    mul_nonneg (mul_nonneg (by norm_num) hsqrt) hgbig
  linarith [fp.u_nonneg]

theorem sourceConstructedPivotedStoredQRSigma_le_pow_mul_of_le
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (q k : ℕ) (hqk : q ≤ k) (hk : k < n) :
    sourceConstructedPivotedStoredQRSigma fp hn hmn A k ≤
      sourceConstructedPivotedStoredQRGrowthFactor fp m ^ (k - q) *
        sourceConstructedPivotedStoredQRSigma fp hn hmn A q := by
  let sigma : ℕ → ℝ :=
    sourceConstructedPivotedStoredQRSigma fp hn hmn A
  let g := sourceConstructedPivotedStoredQRGrowthFactor fp m
  have hg : 0 ≤ g := le_trans (by norm_num)
    (one_le_sourceConstructedPivotedStoredQRGrowthFactor fp m hvalid)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hqk
  have hsub : q + d - q = d := by omega
  rw [hsub]
  induction d with
  | zero => simp
  | succ d ih =>
      have hprev : q + d + 1 < n := by omega
      have hstep := sourceConstructedPivotedStoredQRSigma_succ_le
        fp hn hmn A hvalid (q + d) hprev
      calc
        sigma (q + (d + 1)) = sigma ((q + d) + 1) := by congr 1
        _ ≤ g * sigma (q + d) := by
          simpa [sigma, g, sourceConstructedPivotedStoredQRGrowthFactor]
            using hstep
        _ ≤ g * (g ^ d * sigma q) :=
          mul_le_mul_of_nonneg_left
            (ih (by omega) (by omega) (by omega)) hg
        _ = g ^ (d + 1) * sigma q := by
          rw [pow_succ]
          ring

theorem sourceConstructedPivotedStoredQRSigma_le_rawVector_vecNorm2
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) :
    sourceConstructedPivotedStoredQRSigma fp hn hmn A k ≤
      vecNorm2 (sourceConstructedPivotedStoredQRExactRawVector
        fp hn hmn A k) := by
  let hm : 0 < m := lt_of_lt_of_le hn hmn
  let x := sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k
  have hperm : vecNorm2
      (sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A k) =
        vecNorm2 (householderVector hm x) := by
    rw [sourceConstructedPivotedStoredQRExactRawVector_eq_vecPermute]
    unfold vecNorm2
    rw [vecNorm2Sq_permute]
    rfl
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.one_le_sqrt]
    norm_num
  have hsigma0 : 0 ≤ vecNorm2 x := vecNorm2_nonneg x
  have hsign := householderVector_sign_norm_bound hm x
  rw [hperm]
  change vecNorm2 x ≤ vecNorm2 (householderVector hm x)
  calc
    vecNorm2 x = 1 * vecNorm2 x := by ring
    _ ≤ Real.sqrt 2 * vecNorm2 x :=
      mul_le_mul_of_nonneg_right hsqrt1 hsigma0
    _ ≤ vecNorm2 (householderVector hm x) := hsign

theorem sourceConstructedPivotedStoredQRExactBeta_mul_vecNorm2_sq
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ)
    (hsigma : 0 < sourceConstructedPivotedStoredQRSigma fp hn hmn A k) :
    sourceConstructedPivotedStoredQRExactBeta fp hn hmn A k *
        vecNorm2 (sourceConstructedPivotedStoredQRExactRawVector
          fp hn hmn A k) ^ 2 = 2 := by
  let hm : 0 < m := lt_of_lt_of_le hn hmn
  let x := sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k
  have hx : x ≠ 0 := by
    exact sourceConstructedPivotedStoredQRActiveInput_ne_of_sigma_pos
      fp hn hmn A k (by simpa [x] using hsigma)
  have hperm : vecNorm2
      (sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A k) =
        vecNorm2 (householderVector hm x) := by
    rw [sourceConstructedPivotedStoredQRExactRawVector_eq_vecPermute]
    unfold vecNorm2
    rw [vecNorm2Sq_permute]
    rfl
  rw [hperm, vecNorm2_sq]
  simpa [sourceConstructedPivotedStoredQRExactBeta, x, hm,
    vecNorm2Sq, pow_two] using
      householderBetaFromScale_mul_norm_sq hm x hx

theorem sourceConstructedPivotedStoredQRQaccTotal_eq_actual
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (r : ℕ) (hr : r ≤ n) :
    Wave19.Qacc (sourceConstructedPivotedStoredQRPseqTotal fp hn hmn A) r =
      Wave19.Qacc (sourceConstructedPivotedStoredQRPseq fp hn hmn A) r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [Wave19.Qacc, Wave19.Qacc, ih (by omega)]
      rw [show sourceConstructedPivotedStoredQRPseqTotal fp hn hmn A r =
          sourceConstructedPivotedStoredQRPseq fp hn hmn A r by
        simp [sourceConstructedPivotedStoredQRPseqTotal,
          show r < n by omega]]

noncomputable def sourceConstructedPivotedStoredQRTransportEta
    (fp : FPModel) (m n : ℕ) : ℝ :=
  sourceConstructedPivotedStoredQRResidualNormCoeff fp m *
    sourceConstructedPivotedStoredQRGrowthFactor fp m ^ n

noncomputable def sourceConstructedPivotedStoredQRStageCoeff
    (fp : FPModel) (m n k : ℕ) : ℝ :=
  sourceConstructedPivotedStoredQRLocalCoeff fp m +
    6 * ((k : ℝ) + 1) *
      sourceConstructedPivotedStoredQRTransportEta fp m n

theorem sourceConstructedPivotedStoredQRTransportEta_nonneg
    (fp : FPModel) (m n : ℕ)
    (hvalid : gammaValid fp (11 * m + 23)) :
    0 ≤ sourceConstructedPivotedStoredQRTransportEta fp m n := by
  unfold sourceConstructedPivotedStoredQRTransportEta
  exact mul_nonneg
    (sourceConstructedPivotedStoredQRResidualNormCoeff_nonneg fp m hvalid)
    (pow_nonneg
      (le_trans (by norm_num)
        (one_le_sourceConstructedPivotedStoredQRGrowthFactor fp m hvalid)) n)

theorem sourceConstructedPivotedStoredQRStageCoeff_nonneg
    (fp : FPModel) (m n k : ℕ)
    (hvalid : gammaValid fp (11 * m + 23)) :
    0 ≤ sourceConstructedPivotedStoredQRStageCoeff fp m n k := by
  unfold sourceConstructedPivotedStoredQRStageCoeff
  exact add_nonneg
    (sourceConstructedPivotedStoredQRLocalCoeff_nonneg fp m hvalid)
    (mul_nonneg
      (mul_nonneg (by norm_num) (by positivity))
      (sourceConstructedPivotedStoredQRTransportEta_nonneg
        fp m n hvalid))

theorem sourceConstructedPivotedStoredQREseqTotal_abs_le_printedAlphaScale
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (hgammaHalf : gamma fp (m + 1) ≤ (1 : ℝ) / 2)
    (k : ℕ) (i : Fin m) (j : Fin n) :
    |sourceConstructedPivotedStoredQREseqTotal fp hn hmn A k i j| ≤
      sourceConstructedPivotedStoredQRLocalCoeff fp m *
        sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A i := by
  by_cases hk : k < n
  · simp only [sourceConstructedPivotedStoredQREseqTotal, if_pos hk]
    exact sourceConstructedPivotedStoredQREseq_abs_le_printedAlphaScale
      fp hn hmn A hvalid hgammaHalf k hk i j
  · simp only [sourceConstructedPivotedStoredQREseqTotal, if_neg hk,
      Pi.zero_apply, abs_zero]
    exact mul_nonneg
      (sourceConstructedPivotedStoredQRLocalCoeff_nonneg fp m hvalid)
      (sourceConstructedPivotedStoredQRPrintedAlphaScale_nonneg
        fp hn hmn A i)

/-- The norm of one actual local residual, relative to any preceding raw
reflector, is controlled by the rounded pivot-growth envelope. -/
theorem sourceConstructedPivotedStoredQREseq_norm_div_rawVector_le_eta
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (k : ℕ) (hk : k < n)
    (hsigma : 0 < sourceConstructedPivotedStoredQRSigma fp hn hmn A k)
    (q : ℕ) (hq : q < k + 1) (j : Fin n) :
    vecNorm2 (fun i => sourceConstructedPivotedStoredQREseq
        fp hn hmn A k i j) /
        vecNorm2 (sourceConstructedPivotedStoredQRExactRawVector
          fp hn hmn A q) ≤
      sourceConstructedPivotedStoredQRTransportEta fp m n := by
  let sigma : ℕ → ℝ :=
    sourceConstructedPivotedStoredQRSigma fp hn hmn A
  let raw : ℕ → Fin m → ℝ :=
    sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A
  let D := sourceConstructedPivotedStoredQRResidualNormCoeff fp m
  let g := sourceConstructedPivotedStoredQRGrowthFactor fp m
  have hqk : q ≤ k := by omega
  have hqN : q < n := lt_of_le_of_lt hqk hk
  have hD0 : 0 ≤ D :=
    sourceConstructedPivotedStoredQRResidualNormCoeff_nonneg fp m hvalid
  have hg1 : 1 ≤ g :=
    one_le_sourceConstructedPivotedStoredQRGrowthFactor fp m hvalid
  have hg0 : 0 ≤ g := le_trans (by norm_num) hg1
  have hscale : sigma k ≤ g ^ (k - q) * sigma q := by
    exact sourceConstructedPivotedStoredQRSigma_le_pow_mul_of_le
      fp hn hmn A hvalid q k hqk hk
  have hsigmaq : 0 < sigma q := by
    have hq0 : 0 ≤ sigma q := vecNorm2_nonneg _
    by_contra hnot
    have hqz : sigma q = 0 := le_antisymm (le_of_not_gt hnot) hq0
    rw [hqz, mul_zero] at hscale
    linarith
  have hrawLower : sigma q ≤ vecNorm2 (raw q) := by
    exact sourceConstructedPivotedStoredQRSigma_le_rawVector_vecNorm2
      fp hn hmn A q
  have hrawPos : 0 < vecNorm2 (raw q) :=
    lt_of_lt_of_le hsigmaq hrawLower
  have hf := sourceConstructedPivotedStoredQREseq_vecNorm2_le_sigma
    fp hn hmn A hvalid k hk j
  have hpow : g ^ (k - q) ≤ g ^ n :=
    pow_le_pow_right₀ hg1 (by omega)
  have hsigq0 : 0 ≤ sigma q := vecNorm2_nonneg _
  have hgpow0 : 0 ≤ g ^ n := pow_nonneg hg0 n
  have hnorm : vecNorm2 (fun i => sourceConstructedPivotedStoredQREseq
        fp hn hmn A k i j) ≤ D * g ^ n * vecNorm2 (raw q) := by
    calc
      vecNorm2 (fun i => sourceConstructedPivotedStoredQREseq
          fp hn hmn A k i j) ≤ D * sigma k := by simpa [D] using hf
      _ ≤ D * (g ^ (k - q) * sigma q) :=
        mul_le_mul_of_nonneg_left hscale hD0
      _ ≤ D * (g ^ n * sigma q) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpow hsigq0) hD0
      _ ≤ D * g ^ n * vecNorm2 (raw q) := by
        calc
          D * (g ^ n * sigma q) = (D * g ^ n) * sigma q := by ring
          _ ≤ (D * g ^ n) * vecNorm2 (raw q) :=
            mul_le_mul_of_nonneg_left hrawLower (mul_nonneg hD0 hgpow0)
  apply (div_le_iff₀ hrawPos).2
  simpa [sourceConstructedPivotedStoredQRTransportEta, D, g, raw,
    mul_assoc] using hnorm

theorem sourceConstructedPivotedStoredQRSigma_pos_of_le_of_pos
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (k : ℕ) (hk : k < n)
    (hsigma : 0 < sourceConstructedPivotedStoredQRSigma fp hn hmn A k)
    (q : ℕ) (hqk : q ≤ k) :
    0 < sourceConstructedPivotedStoredQRSigma fp hn hmn A q := by
  have hscale := sourceConstructedPivotedStoredQRSigma_le_pow_mul_of_le
    fp hn hmn A hvalid q k hqk hk
  have hq0 : 0 ≤ sourceConstructedPivotedStoredQRSigma
      fp hn hmn A q := vecNorm2_nonneg _
  by_contra hnot
  have hqz : sourceConstructedPivotedStoredQRSigma fp hn hmn A q = 0 :=
    le_antisymm (le_of_not_gt hnot) hq0
  rw [hqz, mul_zero] at hscale
  linarith

/-- One matrix residual after transport through every reflector accumulated up
to its stage.  Zero pivots contribute exactly zero; nonzero pivots use the
rounded growth envelope rather than a false exact sigma ordering. -/
theorem sourceConstructedPivotedStoredQR_stageImage_entrywise_le
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (hgammaHalf : gamma fp (m + 1) ≤ (1 : ℝ) / 2)
    (k : ℕ) (i : Fin m) (j : Fin n) :
    |matMulRect m m n
        (Wave19.Qacc
          (sourceConstructedPivotedStoredQRPseqTotal fp hn hmn A) (k + 1))
        (sourceConstructedPivotedStoredQREseqTotal fp hn hmn A k) i j| ≤
      sourceConstructedPivotedStoredQRStageCoeff fp m n k *
        sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A i := by
  by_cases hk : k < n
  · let v : ℕ → Fin m → ℝ :=
      sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A
    let beta : ℕ → ℝ :=
      sourceConstructedPivotedStoredQRExactBeta fp hn hmn A
    let f : Fin m → ℝ := fun r =>
      sourceConstructedPivotedStoredQREseq fp hn hmn A k r j
    let alpha : Fin m → ℝ :=
      sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A
    let eta := sourceConstructedPivotedStoredQRTransportEta fp m n
    let C := sourceConstructedPivotedStoredQRLocalCoeff fp m
    let sigma := sourceConstructedPivotedStoredQRSigma fp hn hmn A k
    by_cases hsigma0 : sigma = 0
    · have hx : sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k = 0 := by
        funext q
        have hnorm : vecNorm2
            (sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k) = 0 := by
          simpa [sigma, sourceConstructedPivotedStoredQRSigma] using hsigma0
        exact (vecNorm2_eq_zero_iff
          (sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k)).mp
            hnorm q
      have hE := sourceConstructedPivotedStoredQREseq_eq_zero_of_input_eq_zero
        fp hn hmn A k hk hx
      rw [sourceConstructedPivotedStoredQREseqTotal, if_pos hk, hE]
      simp [matMulRect]
      exact mul_nonneg
        (sourceConstructedPivotedStoredQRStageCoeff_nonneg
          fp m n k hvalid)
        (sourceConstructedPivotedStoredQRPrintedAlphaScale_nonneg
          fp hn hmn A i)
    · have hsigma : 0 < sigma :=
        lt_of_le_of_ne (vecNorm2_nonneg _) (Ne.symm hsigma0)
      have hsymm : ∀ q, matTranspose
          (sourceConstructedPivotedStoredQRPseq fp hn hmn A q) =
            sourceConstructedPivotedStoredQRPseq fp hn hmn A q := by
        intro q
        exact householder_symmetric m (v q) (beta q)
      rw [sourceConstructedPivotedStoredQREseqTotal, if_pos hk,
        sourceConstructedPivotedStoredQRQaccTotal_eq_actual
          fp hn hmn A (k + 1) (by omega),
        qacc_matMulRect_eq_applyProd
          (sourceConstructedPivotedStoredQRPseq fp hn hmn A)
          hsymm (k + 1)
          (sourceConstructedPivotedStoredQREseq fp hn hmn A k) i j]
      change |Wave19.applyProd
          (fun t => householder m (v t) (beta t)) 0 (k + 1) f i| ≤
        sourceConstructedPivotedStoredQRStageCoeff fp m n k * alpha i
      have hbound := applyProd_rawHouseholder_entrywise_le_general
        v beta f alpha 3 eta C (k + 1) i
        (by norm_num)
        (sourceConstructedPivotedStoredQRPrintedAlphaScale_nonneg
          fp hn hmn A)
        (fun q => by
          simpa [v, beta, sourceConstructedPivotedStoredQRPseq] using
            sourceConstructedPivotedStoredQRPseq_orthogonal_unconditional
              fp hn hmn A q)
        (by
          intro q hq
          have hqk : q ≤ k := by omega
          have hsigq := sourceConstructedPivotedStoredQRSigma_pos_of_le_of_pos
            fp hn hmn A hvalid k hk (by simpa [sigma] using hsigma) q hqk
          exact lt_of_lt_of_le hsigq
            (sourceConstructedPivotedStoredQRSigma_le_rawVector_vecNorm2
              fp hn hmn A q))
        (by
          intro q hq
          have hqk : q ≤ k := by omega
          have hsigq := sourceConstructedPivotedStoredQRSigma_pos_of_le_of_pos
            fp hn hmn A hvalid k hk (by simpa [sigma] using hsigma) q hqk
          simpa [v, beta] using
            sourceConstructedPivotedStoredQRExactBeta_mul_vecNorm2_sq
              fp hn hmn A q hsigq)
        (by
          intro q hq r
          have hqn : q < n := by omega
          simpa [v, alpha] using
            sourceConstructedPivotedStoredQRExactRawVector_abs_le_three_printedAlphaScale
              fp hn hmn A q hqn
                (gammaValid_mono fp (by omega) hvalid) hgammaHalf r)
        (by
          intro q hq
          simpa [f, v, eta] using
            sourceConstructedPivotedStoredQREseq_norm_div_rawVector_le_eta
              fp hn hmn A hvalid k hk (by simpa [sigma] using hsigma)
                q hq j)
        (by
          simpa [f, C, alpha] using
            sourceConstructedPivotedStoredQREseq_abs_le_printedAlphaScale
              fp hn hmn A hvalid hgammaHalf k hk i j)
      change |Wave19.applyProd
          (fun t => householder m (v t) (beta t)) 0 (k + 1) f i| ≤
        (C + 6 * ((k : ℝ) + 1) * eta) * alpha i
      convert hbound using 1 <;> push_cast <;> ring
  · rw [sourceConstructedPivotedStoredQREseqTotal, if_neg hk]
    simp [matMulRect]
    exact mul_nonneg
      (sourceConstructedPivotedStoredQRStageCoeff_nonneg fp m n k hvalid)
      (sourceConstructedPivotedStoredQRPrintedAlphaScale_nonneg
        fp hn hmn A i)

noncomputable def sourceConstructedPivotedStoredQRAccumCoeff
    (fp : FPModel) (m n : ℕ) (j : Fin n) : ℝ :=
  ∑ k ∈ Finset.range (j.val + 1),
    sourceConstructedPivotedStoredQRStageCoeff fp m n k

theorem sourceConstructedPivotedStoredQRAccumCoeff_nonneg
    (fp : FPModel) (m n : ℕ)
    (hvalid : gammaValid fp (11 * m + 23)) (j : Fin n) :
    0 ≤ sourceConstructedPivotedStoredQRAccumCoeff fp m n j := by
  unfold sourceConstructedPivotedStoredQRAccumCoeff
  exact Finset.sum_nonneg fun k _ =>
    sourceConstructedPivotedStoredQRStageCoeff_nonneg fp m n k hvalid

/-- Fully accumulated rowwise perturbation bound for the premise-free actual
trace.  The coefficient is an explicit finite sum of the local rounded-storage
and growth-transport coefficients. -/
theorem sourceConstructedPivotedStoredQRdA_abs_le_printedAlphaScale
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (hgammaHalf : gamma fp (m + 1) ≤ (1 : ℝ) / 2)
    (i : Fin m) (j : Fin n) :
    |sourceConstructedPivotedStoredQRdA fp hn hmn A i j| ≤
      sourceConstructedPivotedStoredQRAccumCoeff fp m n j *
        sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A i := by
  let Pseq := sourceConstructedPivotedStoredQRPseqTotal fp hn hmn A
  let Sseq := sourceConstructedPivotedStoredQRSwapSeqTotal fp hn hmn A
  let Eseq := sourceConstructedPivotedStoredQREseqTotal fp hn hmn A
  let alpha := sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A
  have h := pivotDAacc_final_entrywise_bound Pseq Sseq Eseq
    (fun k r => sourceConstructedPivotedStoredQRStageCoeff fp m n k * alpha r)
    (by
      intro k col hcol
      by_cases hk : k < n
      · simp only [Sseq, sourceConstructedPivotedStoredQRSwapSeqTotal,
          if_pos hk]
        exact sourceConstructedPivotedStoredQRSwapSeq_fix_prefix
          fp hn hmn A k col hcol
      · simp [Sseq, sourceConstructedPivotedStoredQRSwapSeqTotal, hk])
    (by
      intro k col hcol
      by_cases hk : k < n
      · simp only [Sseq, sourceConstructedPivotedStoredQRSwapSeqTotal,
          if_pos hk]
        exact sourceConstructedPivotedStoredQRSwapSeq_maps_active
          fp hn hmn A k col hcol
      · simp [Sseq, sourceConstructedPivotedStoredQRSwapSeqTotal, hk]
        exact hcol)
    (by
      intro k r col hcol
      exact sourceConstructedPivotedStoredQR_QaccE_completed_column_zero
        fp hn hmn A k r col hcol)
    (by
      intro k r col
      exact sourceConstructedPivotedStoredQR_stageImage_entrywise_le
        fp hn hmn A hvalid hgammaHalf k r col)
    i j
  have hsum :
      (∑ k ∈ Finset.range (j.val + 1),
          sourceConstructedPivotedStoredQRStageCoeff fp m n k * alpha i) =
        sourceConstructedPivotedStoredQRAccumCoeff fp m n j * alpha i := by
    rw [← Finset.sum_mul]
    rfl
  simpa [sourceConstructedPivotedStoredQRdA, Pseq, Sseq, Eseq, alpha,
    hsum] using h

/-- Source-facing Ch19.6 closure for the literal actual trace: concrete
factorization plus a produced rowwise perturbation bound.  There is no
`StageDataReady`, row-policy, or target-bearing component-budget premise. -/
theorem fl_sourceConstructedPivotedStoredQR_actual_rowwise_backward_error
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (hgammaHalf : gamma fp (m + 1) ≤ (1 : ℝ) / 2) :
    let Q := sourceConstructedPivotedStoredQRQ fp hn hmn A
    let R := fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A n
    let pi := sourceConstructedPivotedStoredQRPi fp hn hmn A
    let dA := sourceConstructedPivotedStoredQRdA fp hn hmn A
    IsOrthogonal m Q ∧
      IsUpperTrapezoidal m n R ∧
      (∀ i j, R i j =
        matMulRect m m n (matTranspose Q)
          (fun a b => Wave13.columnPermuteMatrix A pi a b + dA a b) i j) ∧
      (∀ i j, Wave13.columnPermuteMatrix A pi i j + dA i j =
        matMulRect m m n Q R i j) ∧
      ∀ i j, |dA i j| ≤
        sourceConstructedPivotedStoredQRAccumCoeff fp m n j *
          sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A i := by
  dsimp only
  rcases fl_sourceConstructedPivotedStoredQR_actual_factorization
    fp hn hmn A with ⟨hQ, hR, hTel, hRec⟩
  exact ⟨hQ, hR, hTel, hRec,
    sourceConstructedPivotedStoredQRdA_abs_le_printedAlphaScale
      fp hn hmn A hvalid hgammaHalf⟩

/-! ## Printed Cox--Higham rate compression -/

/-- Uniform first-order coefficient used in the printed Ch19.6 polynomial
envelope.  The rounded pivot-growth factor is kept explicit rather than
replaced by a false exact ordering. -/
noncomputable def sourceConstructedPivotedStoredQRGammaTilde
    (fp : FPModel) (m : ℕ) : ℝ :=
  sourceConstructedPivotedStoredQRLocalCoeff fp m +
    2 * sourceConstructedPivotedStoredQRTransportEta fp m m

theorem sourceConstructedPivotedStoredQRGammaTilde_nonneg
    (fp : FPModel) (m : ℕ)
    (hvalid : gammaValid fp (11 * m + 23)) :
    0 ≤ sourceConstructedPivotedStoredQRGammaTilde fp m := by
  unfold sourceConstructedPivotedStoredQRGammaTilde
  exact add_nonneg
    (sourceConstructedPivotedStoredQRLocalCoeff_nonneg fp m hvalid)
    (mul_nonneg (by norm_num)
      (sourceConstructedPivotedStoredQRTransportEta_nonneg fp m m hvalid))

theorem sourceConstructedPivotedStoredQRTransportEta_le_m
    (fp : FPModel) (m n : ℕ) (hmn : n ≤ m)
    (hvalid : gammaValid fp (11 * m + 23)) :
    sourceConstructedPivotedStoredQRTransportEta fp m n ≤
      sourceConstructedPivotedStoredQRTransportEta fp m m := by
  have hg1 := one_le_sourceConstructedPivotedStoredQRGrowthFactor
    fp m hvalid
  have hpow : sourceConstructedPivotedStoredQRGrowthFactor fp m ^ n ≤
      sourceConstructedPivotedStoredQRGrowthFactor fp m ^ m :=
    pow_le_pow_right₀ hg1 hmn
  unfold sourceConstructedPivotedStoredQRTransportEta
  exact mul_le_mul_of_nonneg_left hpow
    (sourceConstructedPivotedStoredQRResidualNormCoeff_nonneg fp m hvalid)

theorem sourceConstructedPivotedStoredQRStageCoeff_le_coxHigham
    (fp : FPModel) (m n k : ℕ) (hmn : n ≤ m)
    (hvalid : gammaValid fp (11 * m + 23)) :
    sourceConstructedPivotedStoredQRStageCoeff fp m n k ≤
      (1 + 4 * ((k : ℝ) + 1)) *
        sourceConstructedPivotedStoredQRGammaTilde fp m := by
  let C := sourceConstructedPivotedStoredQRLocalCoeff fp m
  let etaN := sourceConstructedPivotedStoredQRTransportEta fp m n
  let etaM := sourceConstructedPivotedStoredQRTransportEta fp m m
  have hC : 0 ≤ C :=
    sourceConstructedPivotedStoredQRLocalCoeff_nonneg fp m hvalid
  have hetaN : 0 ≤ etaN :=
    sourceConstructedPivotedStoredQRTransportEta_nonneg fp m n hvalid
  have hetaM : 0 ≤ etaM :=
    sourceConstructedPivotedStoredQRTransportEta_nonneg fp m m hvalid
  have heta : etaN ≤ etaM :=
    sourceConstructedPivotedStoredQRTransportEta_le_m
      fp m n hmn hvalid
  have ht : 0 ≤ (k : ℝ) + 1 := by positivity
  change C + 6 * ((k : ℝ) + 1) * etaN ≤
    (1 + 4 * ((k : ℝ) + 1)) * (C + 2 * etaM)
  nlinarith

/-- Literal `(j+1)^2 5 gammaTilde` source-rate bound of Cox--Higham
Theorem 3.2 / Higham Theorem 19.6, instantiated by the actual rounded trace. -/
theorem sourceConstructedPivotedStoredQRdA_abs_le_coxHigham
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (hgammaHalf : gamma fp (m + 1) ≤ (1 : ℝ) / 2)
    (i : Fin m) (j : Fin n) :
    |sourceConstructedPivotedStoredQRdA fp hn hmn A i j| ≤
      ((j.val : ℝ) + 1) ^ 2 *
        (5 * sourceConstructedPivotedStoredQRGammaTilde fp m) *
          sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A i := by
  let Pseq := sourceConstructedPivotedStoredQRPseqTotal fp hn hmn A
  let Sseq := sourceConstructedPivotedStoredQRSwapSeqTotal fp hn hmn A
  let Eseq := sourceConstructedPivotedStoredQREseqTotal fp hn hmn A
  let alpha := sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A
  let gammaTilde := sourceConstructedPivotedStoredQRGammaTilde fp m
  apply pivotDAacc_coxHigham_rowwise_bound Pseq Sseq Eseq alpha gammaTilde
    (sourceConstructedPivotedStoredQRGammaTilde_nonneg fp m hvalid)
    (sourceConstructedPivotedStoredQRPrintedAlphaScale_nonneg fp hn hmn A)
  · intro k col hcol
    by_cases hk : k < n
    · simp only [Sseq, sourceConstructedPivotedStoredQRSwapSeqTotal,
        if_pos hk]
      exact sourceConstructedPivotedStoredQRSwapSeq_fix_prefix
        fp hn hmn A k col hcol
    · simp [Sseq, sourceConstructedPivotedStoredQRSwapSeqTotal, hk]
  · intro k col hcol
    by_cases hk : k < n
    · simp only [Sseq, sourceConstructedPivotedStoredQRSwapSeqTotal,
        if_pos hk]
      exact sourceConstructedPivotedStoredQRSwapSeq_maps_active
        fp hn hmn A k col hcol
    · simp [Sseq, sourceConstructedPivotedStoredQRSwapSeqTotal, hk]
      exact hcol
  · intro k r col hcol
    exact sourceConstructedPivotedStoredQR_QaccE_completed_column_zero
      fp hn hmn A k r col hcol
  · intro k r col
    have hstage := sourceConstructedPivotedStoredQR_stageImage_entrywise_le
      fp hn hmn A hvalid hgammaHalf k r col
    have hcoeff := sourceConstructedPivotedStoredQRStageCoeff_le_coxHigham
      fp m n k hmn hvalid
    have halpha := sourceConstructedPivotedStoredQRPrintedAlphaScale_nonneg
      fp hn hmn A r
    exact hstage.trans
      (mul_le_mul_of_nonneg_right hcoeff halpha)

/-- Named, source-facing Ch19.6 endpoint at the printed Cox--Higham rate. -/
theorem higham19_6_sourceConstructed_actual_closed
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (hgammaHalf : gamma fp (m + 1) ≤ (1 : ℝ) / 2) :
    let Q := sourceConstructedPivotedStoredQRQ fp hn hmn A
    let R := fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A n
    let pi := sourceConstructedPivotedStoredQRPi fp hn hmn A
    let dA := sourceConstructedPivotedStoredQRdA fp hn hmn A
    IsOrthogonal m Q ∧
      IsUpperTrapezoidal m n R ∧
      (∀ i j, R i j =
        matMulRect m m n (matTranspose Q)
          (fun a b => Wave13.columnPermuteMatrix A pi a b + dA a b) i j) ∧
      (∀ i j, Wave13.columnPermuteMatrix A pi i j + dA i j =
        matMulRect m m n Q R i j) ∧
      ∀ i j, |dA i j| ≤
        ((j.val : ℝ) + 1) ^ 2 *
          (5 * sourceConstructedPivotedStoredQRGammaTilde fp m) *
            sourceConstructedPivotedStoredQRPrintedAlphaScale
              fp hn hmn A i := by
  dsimp only
  rcases fl_sourceConstructedPivotedStoredQR_actual_factorization
    fp hn hmn A with ⟨hQ, hR, hTel, hRec⟩
  exact ⟨hQ, hR, hTel, hRec,
    sourceConstructedPivotedStoredQRdA_abs_le_coxHigham
      fp hn hmn A hvalid hgammaHalf⟩

/-! ## Linear-in-`m` source-rate closure

The unrestricted endpoint above retains the exact rounded pivot-growth power.
For the standard first-order regime, the usual smallness condition makes that
power at most two.  The transport coefficient then becomes a fixed multiple of
the local `gamma_{11m+23}` radius and compresses to a genuine `gamma_{c m}`
constant, rather than the `gamma_{O(m^2)}` bound obtained by blindly absorbing
the unrestricted power. -/

/-- Standard smallness condition ensuring that the cumulative rounded
    pivot-scale growth stays in the first-order regime. -/
def sourceConstructedPivotedStoredQRPivotGrowthSmall
    (fp : FPModel) (m : ℕ) : Prop :=
  (m : ℝ) *
      (fp.u + 2 * Real.sqrt 2 * gamma fp (11 * m + 23)) ≤ (1 : ℝ) / 2

/-- Linear-rate replacement for the unrestricted growth transport. -/
noncomputable def sourceConstructedPivotedStoredQRLinearTransportEta
    (fp : FPModel) (m : ℕ) : ℝ :=
  2 * sourceConstructedPivotedStoredQRResidualNormCoeff fp m

/-- Printed-rate `gammaTilde`: local error plus the fixed, linearly bounded
    transport contribution. -/
noncomputable def sourceConstructedPivotedStoredQRLinearGammaTilde
    (fp : FPModel) (m : ℕ) : ℝ :=
  sourceConstructedPivotedStoredQRLocalCoeff fp m +
    2 * sourceConstructedPivotedStoredQRLinearTransportEta fp m

theorem sourceConstructedPivotedStoredQRLinearTransportEta_nonneg
    (fp : FPModel) (m : ℕ)
    (hvalid : gammaValid fp (11 * m + 23)) :
    0 ≤ sourceConstructedPivotedStoredQRLinearTransportEta fp m := by
  unfold sourceConstructedPivotedStoredQRLinearTransportEta
  exact mul_nonneg (by norm_num)
    (sourceConstructedPivotedStoredQRResidualNormCoeff_nonneg fp m hvalid)

theorem sourceConstructedPivotedStoredQRLinearGammaTilde_nonneg
    (fp : FPModel) (m : ℕ)
    (hvalid : gammaValid fp (11 * m + 23)) :
    0 ≤ sourceConstructedPivotedStoredQRLinearGammaTilde fp m := by
  unfold sourceConstructedPivotedStoredQRLinearGammaTilde
  exact add_nonneg
    (sourceConstructedPivotedStoredQRLocalCoeff_nonneg fp m hvalid)
    (mul_nonneg (by norm_num)
      (sourceConstructedPivotedStoredQRLinearTransportEta_nonneg fp m hvalid))

/-- Under the explicit first-order smallness guard, all `n ≤ m` rounded
    pivot-growth factors together enlarge a pivot scale by at most two. -/
theorem sourceConstructedPivotedStoredQRGrowthFactor_pow_le_two
    (fp : FPModel) (m n : ℕ) (hmn : n ≤ m)
    (hvalid : gammaValid fp (11 * m + 23))
    (hsmall : sourceConstructedPivotedStoredQRPivotGrowthSmall fp m) :
    sourceConstructedPivotedStoredQRGrowthFactor fp m ^ n ≤ 2 := by
  let d : ℝ := fp.u + 2 * Real.sqrt 2 * gamma fp (11 * m + 23)
  have hg : 0 ≤ gamma fp (11 * m + 23) := gamma_nonneg fp hvalid
  have hd : 0 ≤ d := by
    dsimp [d]
    exact add_nonneg fp.u_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg 2)) hg)
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmn
  have hnsmall : (n : ℝ) * d ≤ (1 : ℝ) / 2 := by
    exact (mul_le_mul_of_nonneg_right hnmR hd).trans (by
      simpa [sourceConstructedPivotedStoredQRPivotGrowthSmall, d] using hsmall)
  have hpow := one_add_pow_sub_one_le_two_mul_nat_mul_of_nat_mul_le_half
    n hd hnsmall
  have htwice : 2 * ((n : ℝ) * d) ≤ 1 := by linarith
  change (1 + d) ^ n ≤ 2
  linarith

/-- The unrestricted transport eta collapses to the fixed linear eta under
    the first-order pivot-growth guard. -/
theorem sourceConstructedPivotedStoredQRTransportEta_le_linear
    (fp : FPModel) (m n : ℕ) (hmn : n ≤ m)
    (hvalid : gammaValid fp (11 * m + 23))
    (hsmall : sourceConstructedPivotedStoredQRPivotGrowthSmall fp m) :
    sourceConstructedPivotedStoredQRTransportEta fp m n ≤
      sourceConstructedPivotedStoredQRLinearTransportEta fp m := by
  have hD := sourceConstructedPivotedStoredQRResidualNormCoeff_nonneg fp m hvalid
  have hpow := sourceConstructedPivotedStoredQRGrowthFactor_pow_le_two
    fp m n hmn hvalid hsmall
  unfold sourceConstructedPivotedStoredQRTransportEta
  unfold sourceConstructedPivotedStoredQRLinearTransportEta
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hpow hD

/-- Each actual transported stage coefficient has the printed Cox--Higham
    shape with the linear-rate `gammaTilde`. -/
theorem sourceConstructedPivotedStoredQRStageCoeff_le_coxHigham_linear
    (fp : FPModel) (m n k : ℕ) (hmn : n ≤ m)
    (hvalid : gammaValid fp (11 * m + 23))
    (hsmall : sourceConstructedPivotedStoredQRPivotGrowthSmall fp m) :
    sourceConstructedPivotedStoredQRStageCoeff fp m n k ≤
      (1 + 4 * ((k : ℝ) + 1)) *
        sourceConstructedPivotedStoredQRLinearGammaTilde fp m := by
  let C := sourceConstructedPivotedStoredQRLocalCoeff fp m
  let etaN := sourceConstructedPivotedStoredQRTransportEta fp m n
  let etaL := sourceConstructedPivotedStoredQRLinearTransportEta fp m
  have hC : 0 ≤ C :=
    sourceConstructedPivotedStoredQRLocalCoeff_nonneg fp m hvalid
  have hetaN : 0 ≤ etaN :=
    sourceConstructedPivotedStoredQRTransportEta_nonneg fp m n hvalid
  have hetaL : 0 ≤ etaL :=
    sourceConstructedPivotedStoredQRLinearTransportEta_nonneg fp m hvalid
  have heta : etaN ≤ etaL :=
    sourceConstructedPivotedStoredQRTransportEta_le_linear
      fp m n hmn hvalid hsmall
  have ht : 0 ≤ (k : ℝ) + 1 := by positivity
  change C + 6 * ((k : ℝ) + 1) * etaN ≤
    (1 + 4 * ((k : ℝ) + 1)) * (C + 2 * etaL)
  nlinarith

/-- Literal `(j+1)^2 5 gammaTilde` Cox--Higham bound for the actual rounded
    trace, now with a genuinely linear-in-`m` gamma-tilde coefficient. -/
theorem sourceConstructedPivotedStoredQRdA_abs_le_coxHigham_linear
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (hgammaHalf : gamma fp (m + 1) ≤ (1 : ℝ) / 2)
    (hsmall : sourceConstructedPivotedStoredQRPivotGrowthSmall fp m)
    (i : Fin m) (j : Fin n) :
    |sourceConstructedPivotedStoredQRdA fp hn hmn A i j| ≤
      ((j.val : ℝ) + 1) ^ 2 *
        (5 * sourceConstructedPivotedStoredQRLinearGammaTilde fp m) *
          sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A i := by
  let Pseq := sourceConstructedPivotedStoredQRPseqTotal fp hn hmn A
  let Sseq := sourceConstructedPivotedStoredQRSwapSeqTotal fp hn hmn A
  let Eseq := sourceConstructedPivotedStoredQREseqTotal fp hn hmn A
  let alpha := sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A
  let gammaTilde := sourceConstructedPivotedStoredQRLinearGammaTilde fp m
  apply pivotDAacc_coxHigham_rowwise_bound Pseq Sseq Eseq alpha gammaTilde
    (sourceConstructedPivotedStoredQRLinearGammaTilde_nonneg fp m hvalid)
    (sourceConstructedPivotedStoredQRPrintedAlphaScale_nonneg fp hn hmn A)
  · intro k col hcol
    by_cases hk : k < n
    · simp only [Sseq, sourceConstructedPivotedStoredQRSwapSeqTotal,
        if_pos hk]
      exact sourceConstructedPivotedStoredQRSwapSeq_fix_prefix
        fp hn hmn A k col hcol
    · simp [Sseq, sourceConstructedPivotedStoredQRSwapSeqTotal, hk]
  · intro k col hcol
    by_cases hk : k < n
    · simp only [Sseq, sourceConstructedPivotedStoredQRSwapSeqTotal,
        if_pos hk]
      exact sourceConstructedPivotedStoredQRSwapSeq_maps_active
        fp hn hmn A k col hcol
    · simp [Sseq, sourceConstructedPivotedStoredQRSwapSeqTotal, hk]
      exact hcol
  · intro k r col hcol
    exact sourceConstructedPivotedStoredQR_QaccE_completed_column_zero
      fp hn hmn A k r col hcol
  · intro k r col
    have hstage := sourceConstructedPivotedStoredQR_stageImage_entrywise_le
      fp hn hmn A hvalid hgammaHalf k r col
    have hcoeff := sourceConstructedPivotedStoredQRStageCoeff_le_coxHigham_linear
      fp m n k hmn hvalid hsmall
    have halpha := sourceConstructedPivotedStoredQRPrintedAlphaScale_nonneg
      fp hn hmn A r
    exact hstage.trans
      (mul_le_mul_of_nonneg_right hcoeff halpha)

/-- **Higham Theorem 19.6, actual rounded full-swap executor, printed
    linear-rate endpoint.**  This removes `StageDataReady` and
    `StrongStageModel`: the concrete source-constructed pivoted stored-QR trace
    itself supplies the exact reflector, local rounded residual, pivot schedule,
    factorization, and the literal row-growth scale. -/
theorem higham19_6_sourceConstructed_actual_closed_linearRate
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (hgammaHalf : gamma fp (m + 1) ≤ (1 : ℝ) / 2)
    (hsmall : sourceConstructedPivotedStoredQRPivotGrowthSmall fp m) :
    let Q := sourceConstructedPivotedStoredQRQ fp hn hmn A
    let R := fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A n
    let pi := sourceConstructedPivotedStoredQRPi fp hn hmn A
    let dA := sourceConstructedPivotedStoredQRdA fp hn hmn A
    IsOrthogonal m Q ∧
      IsUpperTrapezoidal m n R ∧
      (∀ i j, R i j =
        matMulRect m m n (matTranspose Q)
          (fun a b => Wave13.columnPermuteMatrix A pi a b + dA a b) i j) ∧
      (∀ i j, Wave13.columnPermuteMatrix A pi i j + dA i j =
        matMulRect m m n Q R i j) ∧
      ∀ i j, |dA i j| ≤
        ((j.val : ℝ) + 1) ^ 2 *
          (5 * sourceConstructedPivotedStoredQRLinearGammaTilde fp m) *
            sourceConstructedPivotedStoredQRPrintedAlphaScale
              fp hn hmn A i := by
  dsimp only
  rcases fl_sourceConstructedPivotedStoredQR_actual_factorization
    fp hn hmn A with ⟨hQ, hR, hTel, hRec⟩
  exact ⟨hQ, hR, hTel, hRec,
    sourceConstructedPivotedStoredQRdA_abs_le_coxHigham_linear
      fp hn hmn A hvalid hgammaHalf hsmall⟩

/-- The new coefficient is literally a Higham `gamma_{c m}` radius: the fixed
    index `33 * (11m+23)` absorbs all local construction, application, and
    bounded transport terms. -/
theorem sourceConstructedPivotedStoredQRLinearGammaTilde_le_gamma
    (fp : FPModel) (m : ℕ)
    (hvalid : gammaValid fp (33 * (11 * m + 23))) :
    sourceConstructedPivotedStoredQRLinearGammaTilde fp m ≤
      gamma fp (33 * (11 * m + 23)) := by
  let K : ℕ := 11 * m + 23
  have hKpos : 0 < K := by dsimp [K]; omega
  have hKle : K ≤ 33 * K := by omega
  have hvalidK : gammaValid fp K :=
    gammaValid_mono fp hKle (by simpa [K] using hvalid)
  have hg : 0 ≤ gamma fp K := gamma_nonneg fp hvalidK
  have hu : fp.u ≤ gamma fp K := u_le_gamma fp hKpos hvalidK
  have hmK : m + 1 ≤ K := by dsimp [K]; omega
  have hgm : gamma fp (m + 1) ≤ gamma fp K :=
    gamma_mono fp hmK hvalidK
  have hsqrt : Real.sqrt 2 ≤ (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg 2]
  have hsqrtGamma : Real.sqrt 2 * gamma fp K ≤ 2 * gamma fp K :=
    mul_le_mul_of_nonneg_right hsqrt hg
  have hC : sourceConstructedPivotedStoredQRLocalCoeff fp m ≤
      9 * gamma fp K := by
    unfold sourceConstructedPivotedStoredQRLocalCoeff
    change 2 * gamma fp (m + 1) + fp.u +
        3 * Real.sqrt 2 * gamma fp K ≤ 9 * gamma fp K
    nlinarith
  have hD : sourceConstructedPivotedStoredQRResidualNormCoeff fp m ≤
      6 * gamma fp K := by
    unfold sourceConstructedPivotedStoredQRResidualNormCoeff
    change gamma fp (m + 1) + fp.u +
        2 * Real.sqrt 2 * gamma fp K ≤ 6 * gamma fp K
    nlinarith
  have hlinear : sourceConstructedPivotedStoredQRLinearGammaTilde fp m ≤
      33 * gamma fp K := by
    unfold sourceConstructedPivotedStoredQRLinearGammaTilde
    unfold sourceConstructedPivotedStoredQRLinearTransportEta
    nlinarith
  have h33 := gamma_nsmul_le fp 33 K (by norm_num)
    (by simpa [K] using hvalid)
  exact hlinear.trans (by simpa [K] using h33)

/-- Fully explicit source-rate version: the actual rounded full-swap trace has
    the printed `(j+1)^2 * 5 * gamma_{c m} * alpha_i` envelope. -/
theorem higham19_6_sourceConstructed_actual_closed_gammaRate
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (33 * (11 * m + 23)))
    (hgammaHalf : gamma fp (m + 1) ≤ (1 : ℝ) / 2)
    (hsmall : sourceConstructedPivotedStoredQRPivotGrowthSmall fp m) :
    let Q := sourceConstructedPivotedStoredQRQ fp hn hmn A
    let R := fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A n
    let pi := sourceConstructedPivotedStoredQRPi fp hn hmn A
    let dA := sourceConstructedPivotedStoredQRdA fp hn hmn A
    IsOrthogonal m Q ∧
      IsUpperTrapezoidal m n R ∧
      (∀ i j, R i j =
        matMulRect m m n (matTranspose Q)
          (fun a b => Wave13.columnPermuteMatrix A pi a b + dA a b) i j) ∧
      (∀ i j, Wave13.columnPermuteMatrix A pi i j + dA i j =
        matMulRect m m n Q R i j) ∧
      ∀ i j, |dA i j| ≤
        ((j.val : ℝ) + 1) ^ 2 *
          (5 * gamma fp (33 * (11 * m + 23))) *
            sourceConstructedPivotedStoredQRPrintedAlphaScale
              fp hn hmn A i := by
  dsimp only
  have hvalidLocal : gammaValid fp (11 * m + 23) :=
    gammaValid_mono fp (by omega) hvalid
  rcases higham19_6_sourceConstructed_actual_closed_linearRate
    fp hn hmn A hvalidLocal hgammaHalf hsmall with
      ⟨hQ, hR, hTel, hRec, hbound⟩
  refine ⟨hQ, hR, hTel, hRec, ?_⟩
  intro i j
  have hG := sourceConstructedPivotedStoredQRLinearGammaTilde_le_gamma
    fp m hvalid
  have hsq : 0 ≤ ((j.val : ℝ) + 1) ^ 2 := sq_nonneg _
  have ha := sourceConstructedPivotedStoredQRPrintedAlphaScale_nonneg
    fp hn hmn A i
  have h5 : 5 * sourceConstructedPivotedStoredQRLinearGammaTilde fp m ≤
      5 * gamma fp (33 * (11 * m + 23)) :=
    mul_le_mul_of_nonneg_left hG (by norm_num)
  have hpref : ((j.val : ℝ) + 1) ^ 2 *
        (5 * sourceConstructedPivotedStoredQRLinearGammaTilde fp m) ≤
      ((j.val : ℝ) + 1) ^ 2 *
        (5 * gamma fp (33 * (11 * m + 23))) :=
    mul_le_mul_of_nonneg_left h5 hsq
  exact (hbound i j).trans (mul_le_mul_of_nonneg_right hpref ha)

/-! ## Two-scale transport for the paired right-hand side -/

/-- Cox--Higham prefix transport with separate matrix-row and RHS-row scales.
The reflector row is bounded by `alpha`, while the residual row is bounded by
`rho`; the printed bridge `phi * alpha ≤ rho` converts the rank-one transport
term to the RHS scale. -/
theorem applyProd_rawHouseholder_entrywise_le_two_scales_phi {m : ℕ}
    (v : ℕ → Fin m → ℝ) (beta : ℕ → ℝ) (f : Fin m → ℝ)
    (alpha rho : Fin m → ℝ) (phi rawCoeff eta localCoeff : ℝ)
    (i : ℕ) (l : Fin m)
    (hphi : 0 ≤ phi) (hrawCoeff : 0 ≤ rawCoeff) (heta : 0 ≤ eta)
    (halpha : ∀ r, 0 ≤ alpha r) (hrho : ∀ r, 0 ≤ rho r)
    (hphiAlpha : ∀ r, phi * alpha r ≤ rho r)
    (horth : ∀ k, IsOrthogonal m (householder m (v k) (beta k)))
    (hvpos : ∀ k < i, 0 < vecNorm2 (v k))
    (hbeta : ∀ k < i, beta k * vecNorm2 (v k) ^ 2 = 2)
    (hvrow : ∀ k < i, ∀ r, |v k r| ≤ rawCoeff * alpha r)
    (hratio : ∀ k < i, vecNorm2 f / vecNorm2 (v k) ≤ phi * eta)
    (hfrow : |f l| ≤ localCoeff * rho l) :
    |Wave19.applyProd (fun t => householder m (v t) (beta t)) 0 i f l| ≤
      (localCoeff + 2 * rawCoeff * (i : ℝ) * eta) * rho l := by
  let P : ℕ → Fin m → Fin m → ℝ :=
    fun t => householder m (v t) (beta t)
  let zterm : ℕ → Fin m → ℝ := rawHouseholderZTerm v beta f i
  have hexpand := applyProd_rawHouseholder_coordinate_expansion v beta f i l
  have hz : ∀ k ∈ Finset.range i,
      |zterm k l| ≤ 2 * rawCoeff * eta * rho l := by
    intro k hk
    have hki : k < i := Finset.mem_range.mp hk
    let wk : Fin m → ℝ :=
      Wave19.applyProd P (k + 1) (i - (k + 1)) f
    have hwknorm : vecNorm2 wk = vecNorm2 f := by
      exact Wave19.vecNorm2_applyProd P horth (k + 1)
        (i - (k + 1)) f
    let alpha0 : ℝ := (rawCoeff / 2) * alpha l
    have halpha0 : 0 ≤ alpha0 :=
      mul_nonneg (div_nonneg hrawCoeff (by norm_num)) (halpha l)
    have hvrow0 : |v k l| ≤ 2 * alpha0 := by
      calc
        |v k l| ≤ rawCoeff * alpha l := hvrow k hki l
        _ = 2 * alpha0 := by simp [alpha0]; ring
    have hrank := Wave19.zk_rankOne_entrywise_le
      (v k) wk alpha0 l (hvpos k hki) halpha0 hvrow0
    have hratioW : vecNorm2 wk / vecNorm2 (v k) ≤ phi * eta := by
      rw [hwknorm]
      exact hratio k hki
    have hscale0 : 0 ≤ 4 * alpha0 :=
      mul_nonneg (by norm_num) halpha0
    have hbound :
        |(2 / vecNorm2 (v k) ^ 2) * v k l *
            (∑ s : Fin m, v k s * wk s)| ≤
          4 * alpha0 * (phi * eta) := by
      calc
        |(2 / vecNorm2 (v k) ^ 2) * v k l *
            (∑ s : Fin m, v k s * wk s)| ≤
            4 * alpha0 * (vecNorm2 wk / vecNorm2 (v k)) := hrank
        _ ≤ 4 * alpha0 * (phi * eta) :=
          mul_le_mul_of_nonneg_left hratioW hscale0
    have hvsq_ne : vecNorm2 (v k) ^ 2 ≠ 0 :=
      ne_of_gt (sq_pos_of_pos (hvpos k hki))
    have hcoef : beta k = 2 / vecNorm2 (v k) ^ 2 :=
      (eq_div_iff hvsq_ne).2 (hbeta k hki)
    have hzform : zterm k l =
        (2 / vecNorm2 (v k) ^ 2) * v k l *
          (∑ s : Fin m, v k s * wk s) := by
      simp [zterm, rawHouseholderZTerm, P, wk, hcoef]
    rw [hzform]
    have htransport :
        2 * rawCoeff * eta * (phi * alpha l) ≤
          2 * rawCoeff * eta * rho l :=
      mul_le_mul_of_nonneg_left (hphiAlpha l)
        (mul_nonneg (mul_nonneg (by norm_num) hrawCoeff) heta)
    calc
      |(2 / vecNorm2 (v k) ^ 2) * v k l *
          (∑ s : Fin m, v k s * wk s)| ≤
          4 * alpha0 * (phi * eta) := hbound
      _ = 2 * rawCoeff * eta * (phi * alpha l) := by
        simp [alpha0]
        ring
      _ ≤ 2 * rawCoeff * eta * rho l := htransport
  have hsumAbs :
      |∑ k ∈ Finset.range i, zterm k l| ≤
        (i : ℝ) * (2 * rawCoeff * eta * rho l) := by
    calc
      |∑ k ∈ Finset.range i, zterm k l| ≤
          ∑ k ∈ Finset.range i, |zterm k l| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range i,
          (2 * rawCoeff * eta * rho l) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hz k hk
      _ = (i : ℝ) * (2 * rawCoeff * eta * rho l) := by simp
  have hsub := abs_sub_le (f l) 0
    (∑ k ∈ Finset.range i, zterm k l)
  rw [hexpand]
  calc
    |f l - ∑ k ∈ Finset.range i, zterm k l| ≤
        |f l| + |∑ k ∈ Finset.range i, zterm k l| := by
      simpa using hsub
    _ ≤ localCoeff * rho l +
        (i : ℝ) * (2 * rawCoeff * eta * rho l) :=
      add_le_add hfrow hsumAbs
    _ = (localCoeff + 2 * rawCoeff * (i : ℝ) * eta) * rho l := by
      ring

/-! ## Exact paired-RHS telescope for the actual trace -/

noncomputable def sourceConstructedPivotedStoredQRRhsEseqTotal
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (k : ℕ) : Fin m → ℝ :=
  if k < n then sourceConstructedPivotedStoredQRRhsEseq fp hn hmn A b k
  else 0

noncomputable def sourceConstructedPivotedStoredQRRhsMatrixSeq
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (k : ℕ) : Fin m → Fin 1 → ℝ :=
  fun i _ => fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b k i

noncomputable def sourceConstructedPivotedStoredQRRhsEMatrixSeqTotal
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (k : ℕ) : Fin m → Fin 1 → ℝ :=
  fun i _ => sourceConstructedPivotedStoredQRRhsEseqTotal
    fp hn hmn A b k i

noncomputable def sourceConstructedPivotedStoredQRRhsDelta
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) : Fin m → ℝ :=
  fun i => Wave19.DAacc
    (sourceConstructedPivotedStoredQRPseqTotal fp hn hmn A)
    (sourceConstructedPivotedStoredQRRhsEMatrixSeqTotal
      fp hn hmn A b) n i 0

theorem sourceConstructedPivotedStoredQRRhs_step_with_residual_total
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (k : ℕ) (hk : k < n) (i : Fin m) :
    fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b (k + 1) i =
      matMulVec m
          (sourceConstructedPivotedStoredQRPseqTotal fp hn hmn A k)
          (fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b k) i +
        sourceConstructedPivotedStoredQRRhsEseqTotal
          fp hn hmn A b k i := by
  simp only [sourceConstructedPivotedStoredQRPseqTotal,
    sourceConstructedPivotedStoredQRRhsEseqTotal, if_pos hk]
  exact sourceConstructedPivotedStoredQRRhs_step_with_residual
    fp hn hmn A b k i

theorem sourceConstructedPivotedStoredQRRhs_telescope
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (i : Fin m) :
    fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b n i =
      matMulVec m
        (matTranspose (sourceConstructedPivotedStoredQRQ fp hn hmn A))
        (fun a => b a +
          sourceConstructedPivotedStoredQRRhsDelta fp hn hmn A b a) i := by
  have h := Wave19.entrywise_residual_telescope n
    (sourceConstructedPivotedStoredQRRhsMatrixSeq fp hn hmn A b)
    (sourceConstructedPivotedStoredQRPseqTotal fp hn hmn A)
    (sourceConstructedPivotedStoredQRRhsEMatrixSeqTotal fp hn hmn A b)
    (sourceConstructedPivotedStoredQRPseqTotal_orthogonal fp hn hmn A)
    (fun k hk r _j => by
      simpa [sourceConstructedPivotedStoredQRRhsMatrixSeq,
        sourceConstructedPivotedStoredQRRhsEMatrixSeqTotal,
        matMulRect, matMulVec] using
        sourceConstructedPivotedStoredQRRhs_step_with_residual_total
          fp hn hmn A b k hk r)
    i (0 : Fin 1)
  simpa [sourceConstructedPivotedStoredQRRhsMatrixSeq,
    sourceConstructedPivotedStoredQRRhsDelta,
    sourceConstructedPivotedStoredQRQ, matMulRect, matMulVec] using h

theorem sourceConstructedPivotedStoredQRRhs_reconstruct
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (i : Fin m) :
    b i + sourceConstructedPivotedStoredQRRhsDelta fp hn hmn A b i =
      matMulVec m (sourceConstructedPivotedStoredQRQ fp hn hmn A)
        (fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b n) i := by
  let Q := sourceConstructedPivotedStoredQRQ fp hn hmn A
  let c := fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b n
  let db := sourceConstructedPivotedStoredQRRhsDelta fp hn hmn A b
  have hQ : IsOrthogonal m Q := by
    exact Wave19.Qacc_orthogonal
      (sourceConstructedPivotedStoredQRPseqTotal fp hn hmn A)
      (sourceConstructedPivotedStoredQRPseqTotal_orthogonal fp hn hmn A) n
  have hTelEq : c = matMulVec m (matTranspose Q) (fun a => b a + db a) :=
    funext fun r => by
      simpa [Q, c, db] using
        sourceConstructedPivotedStoredQRRhs_telescope fp hn hmn A b r
  have hQQT : matMul m Q (matTranspose Q) = idMatrix m :=
    funext fun r => funext fun s => hQ.right_inv r s
  have hRec : matMulVec m Q c = fun a => b a + db a := by
    funext r
    rw [hTelEq, ← matMulVec_matMul m Q (matTranspose Q) _ r,
      hQQT, matMulVec_id]
  exact (congrFun hRec i).symm

/-! ## Produced paired-RHS norm and transport bounds -/

noncomputable def sourceConstructedPivotedStoredQRRhsLocalCoeff
    (fp : FPModel) (m : ℕ) : ℝ :=
  fp.u + 3 * Real.sqrt 2 * gamma fp (11 * m + 23)

noncomputable def sourceConstructedPivotedStoredQRRhsNormCoeff
    (fp : FPModel) (m : ℕ) : ℝ :=
  fp.u + 2 * Real.sqrt 2 * gamma fp (11 * m + 23)

theorem sourceConstructedPivotedStoredQRRhsLocalCoeff_nonneg
    (fp : FPModel) (m : ℕ)
    (hvalid : gammaValid fp (11 * m + 23)) :
    0 ≤ sourceConstructedPivotedStoredQRRhsLocalCoeff fp m := by
  have hg := gamma_nonneg fp hvalid
  have hs := Real.sqrt_nonneg 2
  unfold sourceConstructedPivotedStoredQRRhsLocalCoeff
  exact add_nonneg fp.u_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hs) hg)

theorem sourceConstructedPivotedStoredQRRhsNormCoeff_nonneg
    (fp : FPModel) (m : ℕ)
    (hvalid : gammaValid fp (11 * m + 23)) :
    0 ≤ sourceConstructedPivotedStoredQRRhsNormCoeff fp m := by
  have hg := gamma_nonneg fp hvalid
  have hs := Real.sqrt_nonneg 2
  unfold sourceConstructedPivotedStoredQRRhsNormCoeff
  exact add_nonneg fp.u_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hs) hg)

/-- Norm form of the actual local RHS residual.  The zero-pivot branch is
exact; otherwise the literal printed `phi` bounds the active RHS tail. -/
theorem sourceConstructedPivotedStoredQRRhsEseq_vecNorm2_le_phi_sigma
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (k : ℕ) (hk : k < n) :
    vecNorm2 (sourceConstructedPivotedStoredQRRhsEseq
      fp hn hmn A b k) ≤
      sourceConstructedPivotedStoredQRPrintedPhi fp hn hmn A b *
        sourceConstructedPivotedStoredQRRhsNormCoeff fp m *
          sourceConstructedPivotedStoredQRSigma fp hn hmn A k := by
  let x := sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k
  let phi := sourceConstructedPivotedStoredQRPrintedPhi fp hn hmn A b
  let c := fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b k
  let S := sourceConstructedPivotedStoredQRRowSwap fp hn hmn A k
  let work := sourceConstructedPivotedStoredQRRhsWork fp hn hmn A k c
  let cp : Fin m → ℝ := vecPermute S work
  let v := sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A k
  let E := sourceConstructedPivotedStoredQRRhsEseq fp hn hmn A b k
  let d := gamma fp (11 * m + 23) * Real.sqrt 2 * phi
  have hphi0 : 0 ≤ phi :=
    sourceConstructedPivotedStoredQRPrintedPhi_nonneg fp hn hmn A b
  have hsigma0 : 0 ≤ sourceConstructedPivotedStoredQRSigma
      fp hn hmn A k := vecNorm2_nonneg _
  have hnormCoeff0 : 0 ≤ sourceConstructedPivotedStoredQRRhsNormCoeff fp m :=
    sourceConstructedPivotedStoredQRRhsNormCoeff_nonneg fp m hvalid
  by_cases hx : x = 0
  · have hE := sourceConstructedPivotedStoredQRRhsEseq_eq_zero_of_input_eq_zero
      fp hn hmn A b k hk (by simpa [x] using hx)
    rw [hE]
    change vecNorm2 (fun _ : Fin m => 0) ≤ _
    rw [vecNorm2_zero]
    exact mul_nonneg (mul_nonneg hphi0 hnormCoeff0) hsigma0
  · have hsigma : 0 < sourceConstructedPivotedStoredQRSigma
        fp hn hmn A k := by
      change 0 < vecNorm2 x
      have hne : vecNorm2 x ≠ 0 := by
        intro hz
        apply hx
        funext q
        exact (vecNorm2_eq_zero_iff x).mp hz q
      exact lt_of_le_of_ne (vecNorm2_nonneg x) (Ne.symm hne)
    have hworkNorm : vecNorm2 work ≤ phi *
        sourceConstructedPivotedStoredQRSigma fp hn hmn A k := by
      simpa [work, c, phi,
        sourceConstructedPivotedStoredQRRhsActiveNorm] using
        sourceConstructedPivotedStoredQRRhsActiveNorm_le_phi_mul_sigma
          fp hn hmn A b k hk hsigma
    have hcpNorm : vecNorm2 cp = vecNorm2 work := by
      unfold cp vecNorm2
      rw [vecNorm2Sq_permute]
    have hSinv : ∀ q, S (S q) = q := by
      intro q
      simp [S, sourceConstructedPivotedStoredQRRowSwap,
        sourceConstructedRowSwap, hk]
    have hcp : ∀ i, cp i = if i.val < k then 0 else c i := by
      intro i
      simp only [cp, work, vecPermute,
        sourceConstructedPivotedStoredQRRhsWork]
      rw [hSinv i]
    have hd : 0 ≤ d :=
      mul_nonneg (mul_nonneg (gamma_nonneg fp hvalid)
        (Real.sqrt_nonneg 2)) hphi0
    have hentry : ∀ i, |E i| ≤ fp.u * |cp i| + d * |v i| := by
      intro i
      by_cases hi : i.val < k
      · have hEi := sourceConstructedPivotedStoredQRRhsEseq_prefix_zero
          fp hn hmn A b k hk i hi
        have hvi := sourceConstructedPivotedStoredQRExactRawVector_zero_prefix
          fp hn hmn A k hk i hi
        rw [show E i = 0 by simpa [E] using hEi,
          hcp i, if_pos hi, show v i = 0 by simpa [v] using hvi]
        simp
      · have hi' : k ≤ i.val := Nat.le_of_not_gt hi
        have hlocal :=
          sourceConstructedPivotedStoredQRRhsEseq_active_abs_le_scaled
            fp hn hmn A b hvalid k hk (by simpa [x] using hx)
              phi hphi0 (by simpa [work, x, phi] using hworkNorm) i hi'
        rw [hcp i, if_neg hi]
        simpa [E, v, c, d, mul_assoc] using hlocal
    have hnorm := vecNorm2_le_of_abs_le_two_term E cp v fp.u d
      fp.u_nonneg hd hentry
    have hvnorm :=
      sourceConstructedPivotedStoredQRExactRawVector_vecNorm2_le_two_sigma
        fp hn hmn A k
    calc
      vecNorm2 (sourceConstructedPivotedStoredQRRhsEseq
          fp hn hmn A b k) = vecNorm2 E := by rfl
      _ ≤ fp.u * vecNorm2 cp + d * vecNorm2 v := hnorm
      _ ≤ fp.u * (phi * sourceConstructedPivotedStoredQRSigma
            fp hn hmn A k) +
          d * (2 * sourceConstructedPivotedStoredQRSigma
            fp hn hmn A k) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (by simpa [hcpNorm] using hworkNorm)
            fp.u_nonneg)
          (mul_le_mul_of_nonneg_left hvnorm hd)
      _ = phi * sourceConstructedPivotedStoredQRRhsNormCoeff fp m *
          sourceConstructedPivotedStoredQRSigma fp hn hmn A k := by
        simp only [d, sourceConstructedPivotedStoredQRRhsNormCoeff]
        ring

noncomputable def sourceConstructedPivotedStoredQRRhsTransportEta
    (fp : FPModel) (m : ℕ) : ℝ :=
  sourceConstructedPivotedStoredQRRhsNormCoeff fp m *
    sourceConstructedPivotedStoredQRGrowthFactor fp m ^ m

noncomputable def sourceConstructedPivotedStoredQRRhsStageCoeff
    (fp : FPModel) (m k : ℕ) : ℝ :=
  sourceConstructedPivotedStoredQRRhsLocalCoeff fp m +
    6 * ((k : ℝ) + 1) *
      sourceConstructedPivotedStoredQRRhsTransportEta fp m

noncomputable def sourceConstructedPivotedStoredQRRhsGammaTilde
    (fp : FPModel) (m : ℕ) : ℝ :=
  sourceConstructedPivotedStoredQRRhsLocalCoeff fp m +
    2 * sourceConstructedPivotedStoredQRRhsTransportEta fp m

theorem sourceConstructedPivotedStoredQRRhsTransportEta_nonneg
    (fp : FPModel) (m : ℕ)
    (hvalid : gammaValid fp (11 * m + 23)) :
    0 ≤ sourceConstructedPivotedStoredQRRhsTransportEta fp m := by
  unfold sourceConstructedPivotedStoredQRRhsTransportEta
  exact mul_nonneg
    (sourceConstructedPivotedStoredQRRhsNormCoeff_nonneg fp m hvalid)
    (pow_nonneg
      (le_trans (by norm_num)
        (one_le_sourceConstructedPivotedStoredQRGrowthFactor fp m hvalid)) m)

theorem sourceConstructedPivotedStoredQRRhsStageCoeff_nonneg
    (fp : FPModel) (m k : ℕ)
    (hvalid : gammaValid fp (11 * m + 23)) :
    0 ≤ sourceConstructedPivotedStoredQRRhsStageCoeff fp m k := by
  unfold sourceConstructedPivotedStoredQRRhsStageCoeff
  exact add_nonneg
    (sourceConstructedPivotedStoredQRRhsLocalCoeff_nonneg fp m hvalid)
    (mul_nonneg (mul_nonneg (by norm_num) (by positivity))
      (sourceConstructedPivotedStoredQRRhsTransportEta_nonneg
        fp m hvalid))

theorem sourceConstructedPivotedStoredQRRhsGammaTilde_nonneg
    (fp : FPModel) (m : ℕ)
    (hvalid : gammaValid fp (11 * m + 23)) :
    0 ≤ sourceConstructedPivotedStoredQRRhsGammaTilde fp m := by
  unfold sourceConstructedPivotedStoredQRRhsGammaTilde
  exact add_nonneg
    (sourceConstructedPivotedStoredQRRhsLocalCoeff_nonneg fp m hvalid)
    (mul_nonneg (by norm_num)
      (sourceConstructedPivotedStoredQRRhsTransportEta_nonneg fp m hvalid))

theorem sourceConstructedPivotedStoredQR_phi_mul_alpha_le_betaScale
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (i : Fin m) :
    sourceConstructedPivotedStoredQRPrintedPhi fp hn hmn A b *
        sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A i ≤
      sourceConstructedPivotedStoredQRPrintedBetaScale fp hn hmn A b i := by
  exact le_max_left _ _

theorem sourceConstructedPivotedStoredQRRhsEseq_abs_le_betaScale
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (hgammaHalf : gamma fp (m + 1) ≤ (1 : ℝ) / 2)
    (k : ℕ) (hk : k < n) (i : Fin m) :
    |sourceConstructedPivotedStoredQRRhsEseq fp hn hmn A b k i| ≤
      sourceConstructedPivotedStoredQRRhsLocalCoeff fp m *
        sourceConstructedPivotedStoredQRPrintedBetaScale fp hn hmn A b i := by
  simpa [sourceConstructedPivotedStoredQRRhsLocalCoeff] using
    sourceConstructedPivotedStoredQRRhsEseq_abs_le_printedBetaScale
      fp hn hmn A b hvalid hgammaHalf k hk i

theorem sourceConstructedPivotedStoredQRRhsEseq_norm_div_rawVector_le
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (k : ℕ) (hk : k < n)
    (hsigma : 0 < sourceConstructedPivotedStoredQRSigma fp hn hmn A k)
    (q : ℕ) (hq : q < k + 1) :
    vecNorm2 (sourceConstructedPivotedStoredQRRhsEseq
        fp hn hmn A b k) /
        vecNorm2 (sourceConstructedPivotedStoredQRExactRawVector
          fp hn hmn A q) ≤
      sourceConstructedPivotedStoredQRPrintedPhi fp hn hmn A b *
        sourceConstructedPivotedStoredQRRhsTransportEta fp m := by
  let sigma : ℕ → ℝ :=
    sourceConstructedPivotedStoredQRSigma fp hn hmn A
  let raw : ℕ → Fin m → ℝ :=
    sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A
  let phi := sourceConstructedPivotedStoredQRPrintedPhi fp hn hmn A b
  let D := sourceConstructedPivotedStoredQRRhsNormCoeff fp m
  let g := sourceConstructedPivotedStoredQRGrowthFactor fp m
  have hqk : q ≤ k := by omega
  have hphi0 : 0 ≤ phi :=
    sourceConstructedPivotedStoredQRPrintedPhi_nonneg fp hn hmn A b
  have hD0 : 0 ≤ D :=
    sourceConstructedPivotedStoredQRRhsNormCoeff_nonneg fp m hvalid
  have hg1 : 1 ≤ g :=
    one_le_sourceConstructedPivotedStoredQRGrowthFactor fp m hvalid
  have hg0 : 0 ≤ g := le_trans (by norm_num) hg1
  have hscale : sigma k ≤ g ^ (k - q) * sigma q :=
    sourceConstructedPivotedStoredQRSigma_le_pow_mul_of_le
      fp hn hmn A hvalid q k hqk hk
  have hsigq := sourceConstructedPivotedStoredQRSigma_pos_of_le_of_pos
    fp hn hmn A hvalid k hk hsigma q hqk
  have hrawLower : sigma q ≤ vecNorm2 (raw q) :=
    sourceConstructedPivotedStoredQRSigma_le_rawVector_vecNorm2
      fp hn hmn A q
  have hrawPos : 0 < vecNorm2 (raw q) := lt_of_lt_of_le hsigq hrawLower
  have hf := sourceConstructedPivotedStoredQRRhsEseq_vecNorm2_le_phi_sigma
    fp hn hmn A b hvalid k hk
  have hpow : g ^ (k - q) ≤ g ^ m :=
    pow_le_pow_right₀ hg1 (by omega)
  have hsigq0 : 0 ≤ sigma q := vecNorm2_nonneg _
  have hgpow0 : 0 ≤ g ^ m := pow_nonneg hg0 m
  have hphiD0 : 0 ≤ phi * D := mul_nonneg hphi0 hD0
  have hnorm : vecNorm2 (sourceConstructedPivotedStoredQRRhsEseq
        fp hn hmn A b k) ≤ phi * D * g ^ m * vecNorm2 (raw q) := by
    calc
      vecNorm2 (sourceConstructedPivotedStoredQRRhsEseq
          fp hn hmn A b k) ≤ phi * D * sigma k := by
        simpa [phi, D, mul_assoc] using hf
      _ ≤ phi * D * (g ^ (k - q) * sigma q) :=
        mul_le_mul_of_nonneg_left hscale hphiD0
      _ ≤ phi * D * (g ^ m * sigma q) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpow hsigq0) hphiD0
      _ ≤ phi * D * g ^ m * vecNorm2 (raw q) := by
        calc
          phi * D * (g ^ m * sigma q) =
              (phi * D * g ^ m) * sigma q := by ring
          _ ≤ (phi * D * g ^ m) * vecNorm2 (raw q) :=
            mul_le_mul_of_nonneg_left hrawLower
              (mul_nonneg hphiD0 hgpow0)
  apply (div_le_iff₀ hrawPos).2
  simpa [sourceConstructedPivotedStoredQRRhsTransportEta,
    phi, D, g, raw, mul_assoc] using hnorm

theorem sourceConstructedPivotedStoredQRRhsStageCoeff_le_coxHigham
    (fp : FPModel) (m k : ℕ)
    (hvalid : gammaValid fp (11 * m + 23)) :
    sourceConstructedPivotedStoredQRRhsStageCoeff fp m k ≤
      (1 + 4 * ((k : ℝ) + 1)) *
        sourceConstructedPivotedStoredQRRhsGammaTilde fp m := by
  let C := sourceConstructedPivotedStoredQRRhsLocalCoeff fp m
  let eta := sourceConstructedPivotedStoredQRRhsTransportEta fp m
  have hC : 0 ≤ C :=
    sourceConstructedPivotedStoredQRRhsLocalCoeff_nonneg fp m hvalid
  have heta : 0 ≤ eta :=
    sourceConstructedPivotedStoredQRRhsTransportEta_nonneg fp m hvalid
  have ht : 0 ≤ (k : ℝ) + 1 := by positivity
  change C + 6 * ((k : ℝ) + 1) * eta ≤
    (1 + 4 * ((k : ℝ) + 1)) * (C + 2 * eta)
  nlinarith

theorem sourceConstructedPivotedStoredQRRhs_stageImage_entrywise_le
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (hgammaHalf : gamma fp (m + 1) ≤ (1 : ℝ) / 2)
    (k : ℕ) (i : Fin m) :
    |matMulVec m
        (Wave19.Qacc
          (sourceConstructedPivotedStoredQRPseqTotal fp hn hmn A) (k + 1))
        (sourceConstructedPivotedStoredQRRhsEseqTotal
          fp hn hmn A b k) i| ≤
      sourceConstructedPivotedStoredQRRhsStageCoeff fp m k *
        sourceConstructedPivotedStoredQRPrintedBetaScale
          fp hn hmn A b i := by
  by_cases hk : k < n
  · let v : ℕ → Fin m → ℝ :=
      sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A
    let beta : ℕ → ℝ :=
      sourceConstructedPivotedStoredQRExactBeta fp hn hmn A
    let f := sourceConstructedPivotedStoredQRRhsEseq fp hn hmn A b k
    let alpha := sourceConstructedPivotedStoredQRPrintedAlphaScale
      fp hn hmn A
    let rho := sourceConstructedPivotedStoredQRPrintedBetaScale
      fp hn hmn A b
    let phi := sourceConstructedPivotedStoredQRPrintedPhi fp hn hmn A b
    let eta := sourceConstructedPivotedStoredQRRhsTransportEta fp m
    let C := sourceConstructedPivotedStoredQRRhsLocalCoeff fp m
    let sigma := sourceConstructedPivotedStoredQRSigma fp hn hmn A k
    by_cases hsigma0 : sigma = 0
    · have hx : sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k = 0 := by
        funext q
        have hnorm : vecNorm2
            (sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k) = 0 := by
          simpa [sigma, sourceConstructedPivotedStoredQRSigma] using hsigma0
        exact (vecNorm2_eq_zero_iff
          (sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k)).mp
            hnorm q
      have hE := sourceConstructedPivotedStoredQRRhsEseq_eq_zero_of_input_eq_zero
        fp hn hmn A b k hk hx
      rw [sourceConstructedPivotedStoredQRRhsEseqTotal, if_pos hk, hE]
      simp [matMulVec]
      exact mul_nonneg
        (sourceConstructedPivotedStoredQRRhsStageCoeff_nonneg
          fp m k hvalid)
        (sourceConstructedPivotedStoredQRPrintedBetaScale_nonneg
          fp hn hmn A b i)
    · have hsigma : 0 < sigma :=
        lt_of_le_of_ne (vecNorm2_nonneg _) (Ne.symm hsigma0)
      have hsymm : ∀ q, matTranspose
          (sourceConstructedPivotedStoredQRPseq fp hn hmn A q) =
            sourceConstructedPivotedStoredQRPseq fp hn hmn A q := by
        intro q
        exact householder_symmetric m (v q) (beta q)
      rw [sourceConstructedPivotedStoredQRRhsEseqTotal, if_pos hk,
        sourceConstructedPivotedStoredQRQaccTotal_eq_actual
          fp hn hmn A (k + 1) (by omega),
        qacc_matMulVec_eq_applyProd
          (sourceConstructedPivotedStoredQRPseq fp hn hmn A)
          hsymm (k + 1)
          (sourceConstructedPivotedStoredQRRhsEseq fp hn hmn A b k)]
      change |Wave19.applyProd
          (fun t => householder m (v t) (beta t)) 0 (k + 1) f i| ≤
        sourceConstructedPivotedStoredQRRhsStageCoeff fp m k * rho i
      have hbound := applyProd_rawHouseholder_entrywise_le_two_scales_phi
        v beta f alpha rho phi 3 eta C (k + 1) i
        (sourceConstructedPivotedStoredQRPrintedPhi_nonneg fp hn hmn A b)
        (by norm_num)
        (sourceConstructedPivotedStoredQRRhsTransportEta_nonneg fp m hvalid)
        (sourceConstructedPivotedStoredQRPrintedAlphaScale_nonneg
          fp hn hmn A)
        (sourceConstructedPivotedStoredQRPrintedBetaScale_nonneg
          fp hn hmn A b)
        (sourceConstructedPivotedStoredQR_phi_mul_alpha_le_betaScale
          fp hn hmn A b)
        (fun q => by
          simpa [v, beta, sourceConstructedPivotedStoredQRPseq] using
            sourceConstructedPivotedStoredQRPseq_orthogonal_unconditional
              fp hn hmn A q)
        (by
          intro q hq
          have hqk : q ≤ k := by omega
          have hsigq := sourceConstructedPivotedStoredQRSigma_pos_of_le_of_pos
            fp hn hmn A hvalid k hk (by simpa [sigma] using hsigma) q hqk
          exact lt_of_lt_of_le hsigq
            (sourceConstructedPivotedStoredQRSigma_le_rawVector_vecNorm2
              fp hn hmn A q))
        (by
          intro q hq
          have hqk : q ≤ k := by omega
          have hsigq := sourceConstructedPivotedStoredQRSigma_pos_of_le_of_pos
            fp hn hmn A hvalid k hk (by simpa [sigma] using hsigma) q hqk
          simpa [v, beta] using
            sourceConstructedPivotedStoredQRExactBeta_mul_vecNorm2_sq
              fp hn hmn A q hsigq)
        (by
          intro q hq r
          have hqn : q < n := by omega
          simpa [v, alpha] using
            sourceConstructedPivotedStoredQRExactRawVector_abs_le_three_printedAlphaScale
              fp hn hmn A q hqn
                (gammaValid_mono fp (by omega) hvalid) hgammaHalf r)
        (by
          intro q hq
          simpa [f, v, phi, eta] using
            sourceConstructedPivotedStoredQRRhsEseq_norm_div_rawVector_le
              fp hn hmn A b hvalid k hk
                (by simpa [sigma] using hsigma) q hq)
        (by
          simpa [f, C, rho] using
            sourceConstructedPivotedStoredQRRhsEseq_abs_le_betaScale
              fp hn hmn A b hvalid hgammaHalf k hk i)
      change |Wave19.applyProd
          (fun t => householder m (v t) (beta t)) 0 (k + 1) f i| ≤
        (C + 6 * ((k : ℝ) + 1) * eta) * rho i
      convert hbound using 1 <;> push_cast <;> ring
  · rw [sourceConstructedPivotedStoredQRRhsEseqTotal, if_neg hk]
    simp [matMulVec]
    exact mul_nonneg
      (sourceConstructedPivotedStoredQRRhsStageCoeff_nonneg fp m k hvalid)
      (sourceConstructedPivotedStoredQRPrintedBetaScale_nonneg
        fp hn hmn A b i)

theorem sourceConstructedPivotedStoredQRRhsDelta_abs_le_coxHigham
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (hgammaHalf : gamma fp (m + 1) ≤ (1 : ℝ) / 2)
    (i : Fin m) :
    |sourceConstructedPivotedStoredQRRhsDelta fp hn hmn A b i| ≤
      (n : ℝ) ^ 2 *
        (5 * sourceConstructedPivotedStoredQRRhsGammaTilde fp m) *
          sourceConstructedPivotedStoredQRPrintedBetaScale
            fp hn hmn A b i := by
  let Pseq := sourceConstructedPivotedStoredQRPseqTotal fp hn hmn A
  let Eseq := sourceConstructedPivotedStoredQRRhsEMatrixSeqTotal
    fp hn hmn A b
  let rho := sourceConstructedPivotedStoredQRPrintedBetaScale
    fp hn hmn A b
  let gammaTilde := sourceConstructedPivotedStoredQRRhsGammaTilde fp m
  have h := Wave19.entrywise_residual_telescope_bound n Pseq Eseq
    (fun k r => (1 + 4 * ((k : ℝ) + 1)) * gammaTilde * rho r)
    (by
      intro k hk r _j
      have hstage :=
        sourceConstructedPivotedStoredQRRhs_stageImage_entrywise_le
          fp hn hmn A b hvalid hgammaHalf k r
      have hcoeff :=
        sourceConstructedPivotedStoredQRRhsStageCoeff_le_coxHigham
          fp m k hvalid
      have hrho := sourceConstructedPivotedStoredQRPrintedBetaScale_nonneg
        fp hn hmn A b r
      have hstage' := hstage.trans
        (mul_le_mul_of_nonneg_right hcoeff hrho)
      simpa [Pseq, Eseq,
        sourceConstructedPivotedStoredQRRhsEMatrixSeqTotal,
        gammaTilde, rho, matMulRect, matMulVec] using hstage')
    i (0 : Fin 1)
  have hfactor :
      (∑ k ∈ Finset.range n,
          (1 + 4 * ((k : ℝ) + 1)) * gammaTilde * rho i) =
        (∑ k ∈ Finset.range n, (1 + 4 * ((k : ℝ) + 1))) *
          gammaTilde * rho i := by
    rw [← Finset.sum_mul, ← Finset.sum_mul]
  rw [hfactor] at h
  have hsum := Wave19.stage_sum_le_five_j_sq n
  have hscale : 0 ≤ gammaTilde * rho i :=
    mul_nonneg
      (sourceConstructedPivotedStoredQRRhsGammaTilde_nonneg fp m hvalid)
      (sourceConstructedPivotedStoredQRPrintedBetaScale_nonneg
        fp hn hmn A b i)
  calc
    |sourceConstructedPivotedStoredQRRhsDelta fp hn hmn A b i| ≤
        (∑ k ∈ Finset.range n, (1 + 4 * ((k : ℝ) + 1))) *
          gammaTilde * rho i := by
      simpa [sourceConstructedPivotedStoredQRRhsDelta, Pseq, Eseq] using h
    _ = (∑ k ∈ Finset.range n, (1 + 4 * ((k : ℝ) + 1))) *
          (gammaTilde * rho i) := by ring
    _ ≤ (5 * (n : ℝ) ^ 2) * (gammaTilde * rho i) :=
      mul_le_mul_of_nonneg_right hsum hscale
    _ = (n : ℝ) ^ 2 * (5 * gammaTilde) * rho i := by ring

/-- Complete, produced common-reflector QR/RHS closure before the triangular
solve. -/
theorem higham20_7_sourceConstructed_actual_qr_rhs_closed
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (hgammaHalf : gamma fp (m + 1) ≤ (1 : ℝ) / 2) :
    let Q := sourceConstructedPivotedStoredQRQ fp hn hmn A
    let R := fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A n
    let pi := sourceConstructedPivotedStoredQRPi fp hn hmn A
    let dA := sourceConstructedPivotedStoredQRdA fp hn hmn A
    let c := fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b n
    let db := sourceConstructedPivotedStoredQRRhsDelta fp hn hmn A b
    IsOrthogonal m Q ∧
      IsUpperTrapezoidal m n R ∧
      (∀ i j, R i j = matMulRect m m n (matTranspose Q)
        (fun a d => Wave13.columnPermuteMatrix A pi a d + dA a d) i j) ∧
      (∀ i j, Wave13.columnPermuteMatrix A pi i j + dA i j =
        matMulRect m m n Q R i j) ∧
      (∀ i, c i = matMulVec m (matTranspose Q)
        (fun a => b a + db a) i) ∧
      (∀ i, b i + db i = matMulVec m Q c i) ∧
      (∀ i j, |dA i j| ≤ ((j.val : ℝ) + 1) ^ 2 *
        (5 * sourceConstructedPivotedStoredQRGammaTilde fp m) *
          sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A i) ∧
      ∀ i, |db i| ≤ (n : ℝ) ^ 2 *
        (5 * sourceConstructedPivotedStoredQRRhsGammaTilde fp m) *
          sourceConstructedPivotedStoredQRPrintedBetaScale
            fp hn hmn A b i := by
  dsimp only
  rcases higham19_6_sourceConstructed_actual_closed
    fp hn hmn A hvalid hgammaHalf with ⟨hQ, hR, hTel, hRec, hdA⟩
  exact ⟨hQ, hR, hTel, hRec,
    sourceConstructedPivotedStoredQRRhs_telescope fp hn hmn A b,
    sourceConstructedPivotedStoredQRRhs_reconstruct fp hn hmn A b,
    hdA,
    sourceConstructedPivotedStoredQRRhsDelta_abs_le_coxHigham
      fp hn hmn A b hvalid hgammaHalf⟩

end Theorem20_7

end NumStability
