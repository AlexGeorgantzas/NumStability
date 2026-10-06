import NumStability.Algorithms.LeastSquares.Higham20Theorem20_7ActualTrace

namespace NumStability

open scoped BigOperators

namespace Theorem20_7

/-!
# Source-scale closure lemmas for the actually rounded Theorem 20.7 trace

This file contains the downstream estimates that are independent of the
zero-active-column implementation branch in `Higham20Theorem20_7ActualTrace`.
The first bridge is needed for the paired right-hand side.  Unlike a matrix
column chosen by column pivoting, the RHS active tail has norm only
`rho * sigma`.  Keeping `rho` in the primitive multiplier estimate is
essential: in particular the error bound becomes zero when the RHS is zero.
-/

/-! ## Literal printed alpha scale for the actually rounded trace -/

/-- The numerator `max_{j,t} |aᵢⱼ^(t)|` from Theorem 20.7, taken over the
actual source-stored rounded states. -/
noncomputable def sourceConstructedPivotedStoredQRPrintedAlphaScale
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (i : Fin m) : ℝ :=
  Wave18D.rowInftyGrowthFactor
    (fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A) n i

theorem sourceConstructedPivotedStoredQRPrintedAlphaScale_nonneg
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (i : Fin m) :
    0 ≤ sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A i := by
  let j0 : Fin n := ⟨0, hn⟩
  exact Wave18D.rowInftyGrowthFactor_nonneg
    (fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A) n i j0

theorem sourceConstructedPivotedStoredQRSwappedPanel_abs_le_printedAlphaScale
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n)
    (i : Fin m) (j : Fin n) :
    |sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k i j| ≤
      sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A i := by
  simpa [sourceConstructedPivotedStoredQRSwappedPanel,
    sourceConstructedPivotedStoredQRPrintedAlphaScale,
    Wave13.columnPermuteMatrix] using
    (Wave18D.abs_entry_le_rowInftyGrowthFactor
      (fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A) n i k
      (Nat.le_of_lt hk) (sourceConstructedPivotedStoredQRSwapSeq
        fp hn hmn A k j))

theorem sourceConstructedPivotedStoredQRRoundedAlpha_abs_le_printedAlphaScale
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n) :
    |sourceConstructedPivotedStoredQRRoundedAlpha fp hn hmn A k| ≤
      sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A
        (pivotedQRActiveRow hmn k hk) := by
  have h := Wave18D.abs_entry_le_rowInftyGrowthFactor
    (fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A) n
    (pivotedQRActiveRow hmn k hk) (k + 1)
    (Nat.succ_le_iff.mpr hk) (pivotedQRActiveCol k hk)
  rw [fl_sourceConstructedPivotedStoredQRMatrixSeq_succ_pivot_eq_alpha
    fp hn hmn A k hk] at h
  simpa [sourceConstructedPivotedStoredQRPrintedAlphaScale] using h

/-- Constructor-scale rounding error for the signed value stored on the
pivot diagonal. -/
theorem sourceConstructedPivotedStoredQRRoundedAlpha_error
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n)
    (hvalid : gammaValid fp (2 * (m + 1))) :
    |sourceConstructedPivotedStoredQRRoundedAlpha fp hn hmn A k -
        householderAlpha (lt_of_lt_of_le hn hmn)
          (sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k)| ≤
      gamma fp (m + 1) *
        |householderScale (lt_of_lt_of_le hn hmn)
          (sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k)| := by
  let hm : 0 < m := lt_of_lt_of_le hn hmn
  let x := sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k
  obtain ⟨theta, htheta, hscale⟩ :=
    fl_householderScale_relative_error fp hm x hvalid
  have hflzero : x = 0 → fl_householderScale fp hm x = 0 := by
    intro hx
    rw [hx] at hscale ⊢
    simpa [householderScale] using hscale
  have halphaHat :
      sourceConstructedPivotedStoredQRRoundedAlpha fp hn hmn A k =
        -fl_householderScale fp hm x := by
    by_cases hx : x = 0
    · unfold sourceConstructedPivotedStoredQRRoundedAlpha
      rw [dif_pos hk]
      dsimp only
      rw [if_pos hx, hflzero hx]
      simp
    · unfold sourceConstructedPivotedStoredQRRoundedAlpha
      rw [dif_pos hk]
      dsimp only
      rw [if_neg hx]
      rfl
  rw [halphaHat]
  simp only [householderAlpha]
  rw [hscale]
  calc
    |- (householderScale hm x * (1 + theta)) -
        -householderScale hm x| =
        |householderScale hm x| * |theta| := by
      rw [show -(householderScale hm x * (1 + theta)) -
          -householderScale hm x = -(householderScale hm x * theta) by ring,
        abs_neg, abs_mul]
    _ ≤ |householderScale hm x| * gamma fp (m + 1) :=
      mul_le_mul_of_nonneg_left htheta (abs_nonneg _)
    _ = gamma fp (m + 1) * |householderScale hm x| := by ring

/-- If the constructor-scale relative error is at most one half, the exact
signed alpha shadow is at most twice the rounded diagonal magnitude recorded
by the source trace.  The zero-input branch is included. -/
theorem sourceConstructedPivotedStoredQRExactAlpha_abs_le_two_printedAlphaScale
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n)
    (hvalid : gammaValid fp (2 * (m + 1)))
    (hgammaHalf : gamma fp (m + 1) ≤ (1 : ℝ) / 2) :
    |householderAlpha (lt_of_lt_of_le hn hmn)
        (sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k)| ≤
      2 * sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A
        (pivotedQRActiveRow hmn k hk) := by
  let hm : 0 < m := lt_of_lt_of_le hn hmn
  let x := sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k
  let alpha := householderAlpha hm x
  let alphaHat := sourceConstructedPivotedStoredQRRoundedAlpha fp hn hmn A k
  let scale := sourceConstructedPivotedStoredQRPrintedAlphaScale
    fp hn hmn A (pivotedQRActiveRow hmn k hk)
  by_cases hx : x = 0
  · simp [x, hx, householderAlpha, householderScale]
    exact sourceConstructedPivotedStoredQRPrintedAlphaScale_nonneg
      fp hn hmn A _
  · have herr :=
      sourceConstructedPivotedStoredQRRoundedAlpha_error
        fp hn hmn A k hk hvalid
    have haHat : |alphaHat| ≤ scale := by
      simpa [alphaHat, scale] using
        sourceConstructedPivotedStoredQRRoundedAlpha_abs_le_printedAlphaScale
          fp hn hmn A k hk
    have hscaleAlpha :
        |householderScale hm x| = |alpha| := by
      simp [alpha, householderAlpha]
    have herr' : |alphaHat - alpha| ≤ gamma fp (m + 1) * |alpha| := by
      simpa [alphaHat, alpha, x, hm, hscaleAlpha] using herr
    have htri : |alpha| ≤ |alphaHat - alpha| + |alphaHat| := by
      have h := abs_sub_le alpha alphaHat 0
      simpa [abs_sub_comm] using h
    have hgamma0 : 0 ≤ gamma fp (m + 1) :=
      gamma_nonneg fp (gammaValid_mono fp (by omega) hvalid)
    have hscale0 : 0 ≤ scale := by
      exact sourceConstructedPivotedStoredQRPrintedAlphaScale_nonneg
        fp hn hmn A _
    have ha0 : 0 ≤ |alpha| := abs_nonneg _
    calc
      |householderAlpha hm x| = |alpha| := by rfl
      _ ≤ 2 * scale := by nlinarith

/-- Rounded-storage replacement for Cox--Higham (2.10).  The exact raw
shadow vector is bounded by three times the literal computed-state row
maximum: one unit for the current pivot-column entry and two for the exact
signed alpha recovered from its rounded stored diagonal. -/
theorem sourceConstructedPivotedStoredQRExactRawVector_abs_le_three_printedAlphaScale
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n)
    (hvalid : gammaValid fp (2 * (m + 1)))
    (hgammaHalf : gamma fp (m + 1) ≤ (1 : ℝ) / 2)
    (i : Fin m) :
    |sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A k i| ≤
      3 * sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A i := by
  let hm : 0 < m := lt_of_lt_of_le hn hmn
  let row := pivotedQRActiveRow hmn k hk
  let col := pivotedQRActiveCol k hk
  let first : Fin m := ⟨0, hm⟩
  let S := sourceConstructedPivotedStoredQRRowSwap fp hn hmn A k
  let As := sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k
  let x := sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k
  let scale : Fin m → ℝ :=
    sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A
  have hSinv : ∀ q, S (S q) = q := by
    intro q
    simp [S, sourceConstructedPivotedStoredQRRowSwap,
      sourceConstructedRowSwap, hk]
  have hxPull : ∀ q, x (S q) = if q.val < k then 0 else As q col := by
    intro q
    simp only [x, sourceConstructedPivotedStoredQRActiveInput, dif_pos hk,
      sourceConstructedActiveInput, sourceConstructedActivePanelPerm]
    change (if (S (S q)).val < k then 0 else As (S (S q)) col) =
      (if q.val < k then 0 else As q col)
    rw [hSinv q]
  have hv : sourceConstructedPivotedStoredQRExactRawVector
      fp hn hmn A k i = householderVector hm x (S i) := by
    rfl
  have hscale0 : ∀ q, 0 ≤ scale q := by
    intro q
    exact sourceConstructedPivotedStoredQRPrintedAlphaScale_nonneg
      fp hn hmn A q
  by_cases hfirst : S i = first
  · have hirow : i = row := by
      calc
        i = S (S i) := (hSinv i).symm
        _ = S first := by rw [hfirst]
        _ = row := by
          simp [S, first, row, sourceConstructedPivotedStoredQRRowSwap,
            sourceConstructedRowSwap, hk]
    subst i
    have hrowval : row.val = k := by simp [row, pivotedQRActiveRow]
    have hxFirst : x first = As row col := by
      have hpull := hxPull row
      rw [if_neg (by omega)] at hpull
      have hSrow : S row = first := by
        simp [S, first, row, sourceConstructedPivotedStoredQRRowSwap,
          sourceConstructedRowSwap, hk]
      simpa [hSrow] using hpull
    have hentry : |As row col| ≤ scale row := by
      exact sourceConstructedPivotedStoredQRSwappedPanel_abs_le_printedAlphaScale
        fp hn hmn A k hk row col
    have halpha :=
      sourceConstructedPivotedStoredQRExactAlpha_abs_le_two_printedAlphaScale
        fp hn hmn A k hk hvalid hgammaHalf
    have hscaleAbs : |householderScale hm x| ≤ 2 * scale row := by
      simpa [householderAlpha, hm, x, row, scale] using halpha
    rw [hv, hfirst, show first = (⟨0, hm⟩ : Fin m) by rfl,
      householderVector_zero, hxFirst]
    calc
      |As row col + householderScale hm x| ≤
          |As row col| + |householderScale hm x| := abs_add_le _ _
      _ ≤ scale row + 2 * scale row := add_le_add hentry hscaleAbs
      _ = 3 * scale row := by ring
  · rw [hv, householderVector_tail hm x (S i) hfirst, hxPull]
    by_cases hi : i.val < k
    · rw [if_pos hi, abs_zero]
      exact mul_nonneg (by norm_num) (hscale0 i)
    · rw [if_neg hi]
      have hentry : |As i col| ≤ scale i :=
        sourceConstructedPivotedStoredQRSwappedPanel_abs_le_printedAlphaScale
          fp hn hmn A k hk i col
      nlinarith [hscale0 i]

/-! ## Full local residual support -/

/-- Every exact-shadow stage preserves an already completed stored column. -/
theorem sourceConstructedPivotedStoredQRPseq_completed_column_preservation
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < n) (j : Fin n) (hj : j.val < k) :
    matMulVec m (sourceConstructedPivotedStoredQRPseq fp hn hmn A k)
        (fun r => sourceConstructedPivotedStoredQRSwappedPanel
          fp hn hmn A k r j) =
      fun r => fl_sourceConstructedPivotedStoredQRMatrixSeq
        fp hn hmn A k r j := by
  let v := sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A k
  let beta := sourceConstructedPivotedStoredQRExactBeta fp hn hmn A k
  let xcol : Fin m → ℝ :=
    fun r => sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k r j
  have hfix := sourceConstructedPivotedStoredQRSwapSeq_fix_prefix
    fp hn hmn A k j hj
  have hxcol : xcol = fun r =>
      fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A k r j := by
    funext r
    simp [xcol, sourceConstructedPivotedStoredQRSwappedPanel,
      Wave13.columnPermuteMatrix, hfix]
  have hvprefix : ∀ r : Fin m, r.val < k → v r = 0 := by
    intro r hr
    exact sourceConstructedPivotedStoredQRExactRawVector_zero_prefix
      fp hn hmn A k hk r hr
  have hsupport : ∀ r : Fin m, k ≤ r.val → xcol r = 0 := by
    intro r hr
    rw [hxcol]
    exact fl_sourceConstructedPivotedStoredQRMatrixSeq_prefix_lower_zero
      fp hn hmn A k (Nat.le_of_lt hk) r j hj (lt_of_lt_of_le hj hr)
  have hpres := matMulVec_householder_eq_self_of_zero_prefix_support
    m k v xcol beta hvprefix hsupport
  simpa [sourceConstructedPivotedStoredQRPseq, v, beta, xcol, hxcol] using hpres

/-- A completed source column carries exactly zero local residual. -/
theorem sourceConstructedPivotedStoredQREseq_completed_column_zero
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < n) (i : Fin m) (j : Fin n) (hj : j.val < k) :
    sourceConstructedPivotedStoredQREseq fp hn hmn A k i j = 0 := by
  have hnext := congrFun (congrFun
    (fl_sourceConstructedPivotedStoredQRMatrixSeq_succ_of_lt
      fp hn hmn A k hk) i) j
  have hcopy :
      fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A (k + 1) i j =
        sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k i j := by
    rw [hnext]
    exact fl_householderCoxHighamConstructedPanelStep_prevColumn_eq
      fp (lt_of_lt_of_le hn hmn)
        (pivotedQRActiveRow hmn k hk) (pivotedQRActiveCol k hk)
        (sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k) hj
  have hpres := congrFun
    (sourceConstructedPivotedStoredQRPseq_completed_column_preservation
      fp hn hmn A k hk j hj) i
  have hfix := sourceConstructedPivotedStoredQRSwapSeq_fix_prefix
    fp hn hmn A k j hj
  have hAs : sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k i j =
      fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A k i j := by
    simp [sourceConstructedPivotedStoredQRSwappedPanel,
      Wave13.columnPermuteMatrix, hfix]
  rw [sourceConstructedPivotedStoredQREseq, hcopy]
  change sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k i j -
    matMulVec m (sourceConstructedPivotedStoredQRPseq fp hn hmn A k)
      (fun r => sourceConstructedPivotedStoredQRSwappedPanel
        fp hn hmn A k r j) i = 0
  rw [hpres, ← hAs]
  ring

/-- Prefix rows are copied and the exact shadow reflector is the identity on
those coordinates, so their local residual is zero. -/
theorem sourceConstructedPivotedStoredQREseq_completed_row_zero
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < n) (i : Fin m) (hi : i.val < k) (j : Fin n) :
    sourceConstructedPivotedStoredQREseq fp hn hmn A k i j = 0 := by
  let v := sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A k
  let beta := sourceConstructedPivotedStoredQRExactBeta fp hn hmn A k
  let As := sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k
  have hvzero : v i = 0 :=
    sourceConstructedPivotedStoredQRExactRawVector_zero_prefix
      fp hn hmn A k hk i hi
  have hpres : matMulVec m (householder m v beta) (fun r => As r j) i =
      As i j := by
    rw [householder_matMulVec_eq]
    simp [hvzero]
  have hnext := congrFun (congrFun
    (fl_sourceConstructedPivotedStoredQRMatrixSeq_succ_of_lt
      fp hn hmn A k hk) i) j
  have hcopy :
      fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A (k + 1) i j =
        As i j := by
    rw [hnext]
    exact fl_householderCoxHighamConstructedPanelStep_prevRow_eq
      fp (lt_of_lt_of_le hn hmn)
        (pivotedQRActiveRow hmn k hk) (pivotedQRActiveCol k hk) As hi
  rw [sourceConstructedPivotedStoredQREseq, hcopy]
  change As i j - matMulVec m (householder m v beta)
    (fun r => As r j) i = 0
  rw [hpres]
  ring

/-- The exact shadow sends the displayed pivot column to the exact signed
alpha at the stored pivot row. -/
theorem sourceConstructedPivotedStoredQRPseq_pivot_eq_exactAlpha
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n) :
    matMulVec m (sourceConstructedPivotedStoredQRPseq fp hn hmn A k)
        (fun r => sourceConstructedPivotedStoredQRSwappedPanel
          fp hn hmn A k r (pivotedQRActiveCol k hk))
        (pivotedQRActiveRow hmn k hk) =
      householderAlpha (lt_of_lt_of_le hn hmn)
        (sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k) := by
  let hm : 0 < m := lt_of_lt_of_le hn hmn
  let row := pivotedQRActiveRow hmn k hk
  let col := pivotedQRActiveCol k hk
  let first : Fin m := ⟨0, hm⟩
  let S := sourceConstructedPivotedStoredQRRowSwap fp hn hmn A k
  let As := sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k
  let Ap := sourceConstructedPivotedStoredQRActivePanelPerm fp hn hmn A k
  let x := sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k
  let v := sourceConstructedPivotedStoredQRExactRawVectorPerm fp hn hmn A k
  let beta := sourceConstructedPivotedStoredQRExactBeta fp hn hmn A k
  by_cases hx : x = 0
  · have hP := sourceConstructedPivotedStoredQRPseq_eq_id_of_input_eq_zero
      fp hn hmn A k (by simpa [x] using hx)
    have hzero :=
      sourceConstructedPivotedStoredQRSwappedPanel_pivotColumn_eq_zero_of_input_eq_zero
        fp hn hmn A k hk (by simpa [x] using hx) row
          (by simp [row, pivotedQRActiveRow])
    rw [hP, congrFun (matMulVec_id m (fun r => As r col)) row]
    simpa [As, col, row, x, hx, householderAlpha, householderScale] using hzero
  · have hwork := sourceConstructedPivotedStoredQRPseq_matMulVec_eq_work
      fp hn hmn A k hk row (by simp [row, pivotedQRActiveRow]) col
    have hSrow : S row = first := by
      simp [S, row, first, sourceConstructedPivotedStoredQRRowSwap,
        sourceConstructedRowSwap, hk]
    have hApx : (fun q => Ap q col) = x := by
      funext q
      dsimp [Ap, x]
      rw [sourceConstructedPivotedStoredQRActiveInput, dif_pos hk]
      rfl
    have hbeta0 : 0 ≤ householderBetaFromScale hm x :=
      le_of_lt (householderBetaFromScale_pos_of_ne_zero hm x hx)
    have hnormEq :
        householder m
            (householderNormalizedVector m (householderVector hm x)
              (householderBetaFromScale hm x)) 1 =
          householder m (householderVector hm x)
            (householderBetaFromScale hm x) :=
      householder_normalizedVector_eq m (householderVector hm x)
        (householderBetaFromScale hm x) hbeta0
    rw [show row = pivotedQRActiveRow hmn k hk by rfl,
      show col = pivotedQRActiveCol k hk by rfl] at hwork
    rw [hwork, show S row = first from hSrow, hApx]
    change matMulVec m
      (householder m (householderVector hm x)
        (householderBetaFromScale hm x)) x first = householderAlpha hm x
    rw [← hnormEq]
    simpa [first, householderAlpha] using
      householder_constructed_matMulVec_first hm x hx

/-- The exact shadow annihilates the displayed pivot-column tail. -/
theorem sourceConstructedPivotedStoredQRPseq_pivot_tail_zero
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n)
    (i : Fin m) (hi : k < i.val) :
    matMulVec m (sourceConstructedPivotedStoredQRPseq fp hn hmn A k)
        (fun r => sourceConstructedPivotedStoredQRSwappedPanel
          fp hn hmn A k r (pivotedQRActiveCol k hk)) i = 0 := by
  let hm : 0 < m := lt_of_lt_of_le hn hmn
  let row := pivotedQRActiveRow hmn k hk
  let col := pivotedQRActiveCol k hk
  let first : Fin m := ⟨0, hm⟩
  let S := sourceConstructedPivotedStoredQRRowSwap fp hn hmn A k
  let As := sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k
  let Ap := sourceConstructedPivotedStoredQRActivePanelPerm fp hn hmn A k
  let x := sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k
  let v := sourceConstructedPivotedStoredQRExactRawVectorPerm fp hn hmn A k
  let beta := sourceConstructedPivotedStoredQRExactBeta fp hn hmn A k
  by_cases hx : x = 0
  · have hP := sourceConstructedPivotedStoredQRPseq_eq_id_of_input_eq_zero
      fp hn hmn A k (by simpa [x] using hx)
    have hzero :=
      sourceConstructedPivotedStoredQRSwappedPanel_pivotColumn_eq_zero_of_input_eq_zero
        fp hn hmn A k hk (by simpa [x] using hx) i (Nat.le_of_lt hi)
    rw [hP, congrFun (matMulVec_id m (fun r => As r col)) i]
    simpa [As, col] using hzero
  · have hwork := sourceConstructedPivotedStoredQRPseq_matMulVec_eq_work
      fp hn hmn A k hk i (Nat.le_of_lt hi) col
    have hSi : S i ≠ first := by
      intro h
      have hback := congrArg S h
      have hSinv : S (S i) = i := by
        simp [S, sourceConstructedPivotedStoredQRRowSwap,
          sourceConstructedRowSwap, hk]
      have hSfirst : S first = row := by
        simp [S, row, first, sourceConstructedPivotedStoredQRRowSwap,
          sourceConstructedRowSwap, hk]
      rw [hSinv, hSfirst] at hback
      have hiv := congrArg Fin.val hback
      simp [row, pivotedQRActiveRow] at hiv
      omega
    have hApx : (fun q => Ap q col) = x := by
      funext q
      dsimp [Ap, x]
      rw [sourceConstructedPivotedStoredQRActiveInput, dif_pos hk]
      rfl
    have hbeta0 : 0 ≤ householderBetaFromScale hm x :=
      le_of_lt (householderBetaFromScale_pos_of_ne_zero hm x hx)
    have hnormEq :
        householder m
            (householderNormalizedVector m (householderVector hm x)
              (householderBetaFromScale hm x)) 1 =
          householder m (householderVector hm x)
            (householderBetaFromScale hm x) :=
      householder_normalizedVector_eq m (householderVector hm x)
        (householderBetaFromScale hm x) hbeta0
    rw [show col = pivotedQRActiveCol k hk by rfl] at hwork
    rw [hwork, hApx]
    change matMulVec m
      (householder m (householderVector hm x)
        (householderBetaFromScale hm x)) x (S i) = 0
    rw [← hnormEq]
    exact householder_constructed_matMulVec_tail_zero hm x hx (S i) hSi

/-! ## Explicit local component budget for the actual source trace -/

/-- Piecewise local residual budget for one actually rounded pivoted QR
stage.  Completed columns and rows have zero residual.  On the stored pivot
column, only the rounded signed diagonal contributes; the pivot tail is
stored exactly as zero.  A genuinely updated trailing entry uses the
implementation-backed Cox--Higham Lemma 2.2 budget. -/
noncomputable def sourceConstructedPivotedStoredQRComponentBudget
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ)
    (i : Fin m) (j : Fin n) : ℝ :=
  if j.val < k then 0
  else if i.val < k then 0
  else if j.val = k then
    if i.val = k then
      gamma fp (m + 1) *
        |householderScale (lt_of_lt_of_le hn hmn)
          (sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k)|
    else 0
  else
    fp.u *
        |sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k i j| +
      gamma fp (11 * m + 23) * Real.sqrt 2 *
        |sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A k i|

theorem sourceConstructedPivotedStoredQRComponentBudget_nonneg
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (k : ℕ) (i : Fin m) (j : Fin n) :
    0 ≤ sourceConstructedPivotedStoredQRComponentBudget
      fp hn hmn A k i j := by
  unfold sourceConstructedPivotedStoredQRComponentBudget
  split_ifs
  · rfl
  · rfl
  · exact mul_nonneg
      (gamma_nonneg fp (gammaValid_mono fp (by omega) hvalid))
      (abs_nonneg _)
  · rfl
  · exact add_nonneg
      (mul_nonneg fp.u_nonneg (abs_nonneg _))
      (mul_nonneg
        (mul_nonneg (gamma_nonneg fp hvalid) (Real.sqrt_nonneg 2))
        (abs_nonneg _))

/-- The exact-shadow residual of every entry in an actually rounded source
stage is bounded by the explicit piecewise budget above.  This theorem has no
target-bearing residual hypothesis and includes the zero-active-column
branch. -/
theorem sourceConstructedPivotedStoredQREseq_abs_le_componentBudget
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (k : ℕ) (hk : k < n) (i : Fin m) (j : Fin n) :
    |sourceConstructedPivotedStoredQREseq fp hn hmn A k i j| ≤
      sourceConstructedPivotedStoredQRComponentBudget
        fp hn hmn A k i j := by
  by_cases hjPrev : j.val < k
  · rw [sourceConstructedPivotedStoredQREseq_completed_column_zero
      fp hn hmn A k hk i j hjPrev]
    simp [sourceConstructedPivotedStoredQRComponentBudget, hjPrev]
  by_cases hiPrev : i.val < k
  · rw [sourceConstructedPivotedStoredQREseq_completed_row_zero
      fp hn hmn A k hk i hiPrev j]
    simp [sourceConstructedPivotedStoredQRComponentBudget, hjPrev, hiPrev]
  by_cases hjPivot : j.val = k
  · have hjEq : j = pivotedQRActiveCol k hk := Fin.ext hjPivot
    subst j
    by_cases hiPivot : i.val = k
    · have hiEq : i = pivotedQRActiveRow hmn k hk := by
        apply Fin.ext
        simpa [pivotedQRActiveRow] using hiPivot
      subst i
      rw [sourceConstructedPivotedStoredQREseq,
        fl_sourceConstructedPivotedStoredQRMatrixSeq_succ_pivot_eq_alpha
          fp hn hmn A k hk]
      change
        |sourceConstructedPivotedStoredQRRoundedAlpha fp hn hmn A k -
          matMulVec m (sourceConstructedPivotedStoredQRPseq fp hn hmn A k)
            (fun r => sourceConstructedPivotedStoredQRSwappedPanel
              fp hn hmn A k r (pivotedQRActiveCol k hk))
            (pivotedQRActiveRow hmn k hk)| ≤ _
      rw [
        sourceConstructedPivotedStoredQRPseq_pivot_eq_exactAlpha
          fp hn hmn A k hk]
      simpa [sourceConstructedPivotedStoredQRComponentBudget,
        pivotedQRActiveRow, pivotedQRActiveCol] using
        sourceConstructedPivotedStoredQRRoundedAlpha_error
          fp hn hmn A k hk
            (gammaValid_mono fp (by omega) hvalid)
    · have hki : k < i.val := by omega
      have hnext := congrFun (congrFun
        (fl_sourceConstructedPivotedStoredQRMatrixSeq_succ_of_lt
          fp hn hmn A k hk) i) (pivotedQRActiveCol k hk)
      rw [sourceConstructedPivotedStoredQREseq, hnext,
        fl_householderCoxHighamConstructedPanelStep_pivotTail_eq_zero
          fp (lt_of_lt_of_le hn hmn)
            (pivotedQRActiveRow hmn k hk) (pivotedQRActiveCol k hk)
            (sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k)
            hki (by simp [pivotedQRActiveCol])]
      change
        |0 - matMulVec m
          (sourceConstructedPivotedStoredQRPseq fp hn hmn A k)
          (fun r => sourceConstructedPivotedStoredQRSwappedPanel
            fp hn hmn A k r (pivotedQRActiveCol k hk)) i| ≤ _
      rw [
        sourceConstructedPivotedStoredQRPseq_pivot_tail_zero
          fp hn hmn A k hk i hki]
      simp [sourceConstructedPivotedStoredQRComponentBudget,
        pivotedQRActiveCol, hjPrev, hiPrev, hiPivot]
  · have hkj : k < j.val := by omega
    simpa [sourceConstructedPivotedStoredQRComponentBudget,
      hjPrev, hiPrev, hjPivot] using
      sourceConstructedPivotedStoredQREseq_activeTrailing_abs_le_unconditional
        fp hn hmn A hvalid k hk i (Nat.le_of_not_gt hiPrev) j hkj

theorem sourceConstructedPivotedStoredQREseq_norm_le_componentBudget
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (k : ℕ) (hk : k < n) (j : Fin n) :
    vecNorm2 (fun i => sourceConstructedPivotedStoredQREseq
      fp hn hmn A k i j) ≤
      vecNorm2 (fun i => sourceConstructedPivotedStoredQRComponentBudget
        fp hn hmn A k i j) := by
  apply vecNorm2_le_of_abs_le
  intro i
  exact sourceConstructedPivotedStoredQREseq_abs_le_componentBudget
    fp hn hmn A hvalid k hk i j

/-- Uniform row coefficient obtained by compressing the literal piecewise
budget against the printed maximum of the actually stored states.  The first
term pays for rounded signed-pivot storage; the remaining terms are the
constructor/application budget on a trailing entry. -/
noncomputable def sourceConstructedPivotedStoredQRLocalCoeff
    (fp : FPModel) (m : ℕ) : ℝ :=
  2 * gamma fp (m + 1) + fp.u +
    3 * Real.sqrt 2 * gamma fp (11 * m + 23)

theorem sourceConstructedPivotedStoredQRLocalCoeff_nonneg
    (fp : FPModel) (m : ℕ)
    (hvalid : gammaValid fp (11 * m + 23)) :
    0 ≤ sourceConstructedPivotedStoredQRLocalCoeff fp m := by
  have hgsmall : 0 ≤ gamma fp (m + 1) :=
    gamma_nonneg fp (gammaValid_mono fp (by omega) hvalid)
  have hgbig : 0 ≤ gamma fp (11 * m + 23) := gamma_nonneg fp hvalid
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  unfold sourceConstructedPivotedStoredQRLocalCoeff
  exact add_nonneg
    (add_nonneg (mul_nonneg (by norm_num) hgsmall) fp.u_nonneg)
    (mul_nonneg (mul_nonneg (by norm_num) hsqrt) hgbig)

/-- The explicit local component budget is bounded rowwise by the literal
printed alpha scale of the actually rounded trace. -/
theorem sourceConstructedPivotedStoredQRComponentBudget_le_printedAlphaScale
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (hgammaHalf : gamma fp (m + 1) ≤ (1 : ℝ) / 2)
    (k : ℕ) (hk : k < n) (i : Fin m) (j : Fin n) :
    sourceConstructedPivotedStoredQRComponentBudget fp hn hmn A k i j ≤
      sourceConstructedPivotedStoredQRLocalCoeff fp m *
        sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A i := by
  let scale : Fin m → ℝ :=
    sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A
  have hscale0 : ∀ r, 0 ≤ scale r := by
    intro r
    exact sourceConstructedPivotedStoredQRPrintedAlphaScale_nonneg
      fp hn hmn A r
  have hgsmall : 0 ≤ gamma fp (m + 1) :=
    gamma_nonneg fp (gammaValid_mono fp (by omega) hvalid)
  have hgbig : 0 ≤ gamma fp (11 * m + 23) := gamma_nonneg fp hvalid
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hcoeff0 : 0 ≤ sourceConstructedPivotedStoredQRLocalCoeff fp m :=
    sourceConstructedPivotedStoredQRLocalCoeff_nonneg fp m hvalid
  by_cases hjPrev : j.val < k
  · rw [sourceConstructedPivotedStoredQRComponentBudget, if_pos hjPrev]
    exact mul_nonneg hcoeff0 (by simpa [scale] using hscale0 i)
  by_cases hiPrev : i.val < k
  · rw [sourceConstructedPivotedStoredQRComponentBudget,
      if_neg hjPrev, if_pos hiPrev]
    exact mul_nonneg hcoeff0 (by simpa [scale] using hscale0 i)
  by_cases hjPivot : j.val = k
  · by_cases hiPivot : i.val = k
    · have hiEq : i = pivotedQRActiveRow hmn k hk := by
        apply Fin.ext
        simpa [pivotedQRActiveRow] using hiPivot
      have halpha :=
        sourceConstructedPivotedStoredQRExactAlpha_abs_le_two_printedAlphaScale
          fp hn hmn A k hk
            (gammaValid_mono fp (by omega) hvalid) hgammaHalf
      have hscaleAbs :
          |householderScale (lt_of_lt_of_le hn hmn)
              (sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k)| ≤
            2 * scale i := by
        subst i
        simpa [householderAlpha, scale] using halpha
      rw [sourceConstructedPivotedStoredQRComponentBudget,
        if_neg hjPrev, if_neg hiPrev, if_pos hjPivot, if_pos hiPivot]
      calc
        gamma fp (m + 1) *
            |householderScale (lt_of_lt_of_le hn hmn)
              (sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k)| ≤
            gamma fp (m + 1) * (2 * scale i) :=
          mul_le_mul_of_nonneg_left hscaleAbs hgsmall
        _ ≤ sourceConstructedPivotedStoredQRLocalCoeff fp m * scale i := by
          have htail :
              0 ≤ 3 * Real.sqrt 2 * gamma fp (11 * m + 23) :=
            mul_nonneg (mul_nonneg (by norm_num) hsqrt) hgbig
          have hcoef : 2 * gamma fp (m + 1) ≤
              sourceConstructedPivotedStoredQRLocalCoeff fp m := by
            unfold sourceConstructedPivotedStoredQRLocalCoeff
            linarith [fp.u_nonneg]
          rw [show gamma fp (m + 1) * (2 * scale i) =
              (2 * gamma fp (m + 1)) * scale i by ring]
          exact mul_le_mul_of_nonneg_right hcoef (hscale0 i)
    · rw [sourceConstructedPivotedStoredQRComponentBudget,
        if_neg hjPrev, if_neg hiPrev, if_pos hjPivot, if_neg hiPivot]
      exact mul_nonneg hcoeff0 (hscale0 i)
  · have hAs :=
      sourceConstructedPivotedStoredQRSwappedPanel_abs_le_printedAlphaScale
        fp hn hmn A k hk i j
    have hv :=
      sourceConstructedPivotedStoredQRExactRawVector_abs_le_three_printedAlphaScale
        fp hn hmn A k hk (gammaValid_mono fp (by omega) hvalid)
          hgammaHalf i
    rw [sourceConstructedPivotedStoredQRComponentBudget,
      if_neg hjPrev, if_neg hiPrev, if_neg hjPivot]
    calc
      fp.u * |sourceConstructedPivotedStoredQRSwappedPanel
          fp hn hmn A k i j| +
          gamma fp (11 * m + 23) * Real.sqrt 2 *
            |sourceConstructedPivotedStoredQRExactRawVector
              fp hn hmn A k i| ≤
        fp.u * scale i +
          gamma fp (11 * m + 23) * Real.sqrt 2 * (3 * scale i) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (by simpa [scale] using hAs)
            fp.u_nonneg)
          (mul_le_mul_of_nonneg_left (by simpa [scale] using hv)
            (mul_nonneg hgbig hsqrt))
      _ ≤ sourceConstructedPivotedStoredQRLocalCoeff fp m * scale i := by
        have hsmall2 : 0 ≤ 2 * gamma fp (m + 1) :=
          mul_nonneg (by norm_num) hgsmall
        have hcoef :
            fp.u + 3 * Real.sqrt 2 * gamma fp (11 * m + 23) ≤
              sourceConstructedPivotedStoredQRLocalCoeff fp m := by
          unfold sourceConstructedPivotedStoredQRLocalCoeff
          linarith
        rw [show fp.u * scale i +
            gamma fp (11 * m + 23) * Real.sqrt 2 * (3 * scale i) =
              (fp.u + 3 * Real.sqrt 2 * gamma fp (11 * m + 23)) *
                scale i by ring]
        exact mul_le_mul_of_nonneg_right hcoef (hscale0 i)

/-- Direct rowwise local residual estimate, with no residual premise. -/
theorem sourceConstructedPivotedStoredQREseq_abs_le_printedAlphaScale
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (hgammaHalf : gamma fp (m + 1) ≤ (1 : ℝ) / 2)
    (k : ℕ) (hk : k < n) (i : Fin m) (j : Fin n) :
    |sourceConstructedPivotedStoredQREseq fp hn hmn A k i j| ≤
      sourceConstructedPivotedStoredQRLocalCoeff fp m *
        sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A i :=
  (sourceConstructedPivotedStoredQREseq_abs_le_componentBudget
      fp hn hmn A hvalid k hk i j).trans
    (sourceConstructedPivotedStoredQRComponentBudget_le_printedAlphaScale
      fp hn hmn A hvalid hgammaHalf k hk i j)

/-- Scaled form of the Cox--Higham absolute multiplier estimate. -/
theorem raw_abs_multiplier_le_sqrt_two_mul_scale {n : ℕ}
    (v b : Fin n → ℝ) (sigma beta rho : ℝ)
    (hrho : 0 ≤ rho)
    (hsigma : 0 < |sigma|)
    (hvnorm : Real.sqrt 2 * |sigma| ≤ vecNorm2 v)
    (hb : vecNorm2 b ≤ rho * |sigma|)
    (hbeta : beta * vecNorm2 v ^ 2 = 2) :
    beta * (∑ j : Fin n, |v j| * |b j|) ≤ Real.sqrt 2 * rho := by
  by_cases hrho0 : rho = 0
  · subst rho
    have hbnorm : vecNorm2 b = 0 := by
      apply le_antisymm
      · simpa using hb
      · exact vecNorm2_nonneg b
    have hbzero : b = 0 := by
      funext i
      exact (vecNorm2_eq_zero_iff b).mp hbnorm i
    simp [hbzero]
  · have hrhopos : 0 < rho := lt_of_le_of_ne hrho (Ne.symm hrho0)
    let bs : Fin n → ℝ := fun j => (rho⁻¹) * b j
    have hbsnorm : vecNorm2 bs = rho⁻¹ * vecNorm2 b := by
      rw [show bs = fun j => (rho⁻¹) * b j by rfl, vecNorm2_smul,
        abs_of_pos (inv_pos.mpr hrhopos)]
    have hbs : vecNorm2 bs ≤ |sigma| := by
      rw [hbsnorm]
      have hinvnonneg : 0 ≤ rho⁻¹ := le_of_lt (inv_pos.mpr hrhopos)
      calc
        rho⁻¹ * vecNorm2 b ≤ rho⁻¹ * (rho * |sigma|) :=
          mul_le_mul_of_nonneg_left hb hinvnonneg
        _ = |sigma| := by field_simp
    have hscaled := raw_abs_multiplier_le_sqrt_two
      v bs sigma beta hsigma hvnorm hbs hbeta
    have hsum :
        (∑ j : Fin n, |v j| * |bs j|) =
          rho⁻¹ * (∑ j : Fin n, |v j| * |b j|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [bs, abs_mul, abs_inv, abs_of_pos hrhopos]
      field_simp
    rw [hsum] at hscaled
    calc
      beta * (∑ j : Fin n, |v j| * |b j|) =
          rho * (beta * (rho⁻¹ *
            (∑ j : Fin n, |v j| * |b j|))) := by
            field_simp
      _ ≤ rho * Real.sqrt 2 :=
        mul_le_mul_of_nonneg_left hscaled hrho
      _ = Real.sqrt 2 * rho := by ring

/-- Primitive computed-reflector application error when the operand has norm
at most `rho` times the pivot scale. -/
theorem fl_householderApply_raw_entrywise_error_scaled
    (fp : FPModel) (a n : ℕ)
    (vraw vhat b : Fin n → ℝ) (beta sigma eps rho : ℝ)
    (hrho : 0 ≤ rho)
    (hbeta_nonneg : 0 ≤ beta)
    (hvec : HouseholderVectorError n
      (householderNormalizedVector n vraw beta) vhat eps)
    (heps_nonneg : 0 ≤ eps)
    (heps_bound : eps ≤ gamma fp a)
    (hsigma : 0 < |sigma|)
    (hvnorm : Real.sqrt 2 * |sigma| ≤ vecNorm2 vraw)
    (hb : vecNorm2 b ≤ rho * |sigma|)
    (hbeta : beta * vecNorm2 vraw ^ 2 = 2)
    (hvalid : gammaValid fp (2 * a + n + 3))
    (i : Fin n) :
    |fl_householderApply fp n vhat 1 b i -
        matMulVec n (householder n vraw beta) b i| ≤
      fp.u * |b i| +
        gamma fp (2 * a + n + 3) * Real.sqrt 2 * rho * |vraw i| := by
  let vnorm := householderNormalizedVector n vraw beta
  have happ :=
    fl_householderApply_normalized_entrywise_error fp a n vnorm vhat eps b
      hvec heps_nonneg heps_bound hvalid i
  rw [householder_normalizedVector_eq n vraw beta hbeta_nonneg] at happ
  have hscale := normalized_outer_row_eq_raw vraw b beta hbeta_nonneg i
  have hmult := raw_abs_multiplier_le_sqrt_two_mul_scale
    vraw b sigma beta rho hrho hsigma hvnorm hb hbeta
  have hrow :
      beta * |vraw i| * (∑ j : Fin n, |vraw j| * |b j|) ≤
        Real.sqrt 2 * rho * |vraw i| := by
    calc
      beta * |vraw i| * (∑ j : Fin n, |vraw j| * |b j|) =
          |vraw i| *
            (beta * (∑ j : Fin n, |vraw j| * |b j|)) := by ring
      _ ≤ |vraw i| * (Real.sqrt 2 * rho) :=
        mul_le_mul_of_nonneg_left hmult (abs_nonneg (vraw i))
      _ = Real.sqrt 2 * rho * |vraw i| := by ring
  have hgamma_nonneg : 0 ≤ gamma fp (2 * a + n + 3) :=
    gamma_nonneg fp hvalid
  calc
    |fl_householderApply fp n vhat 1 b i -
        matMulVec n (householder n vraw beta) b i| ≤
      fp.u * |b i| +
        gamma fp (2 * a + n + 3) * |vnorm i| *
          (∑ j : Fin n, |vnorm j| * |b j|) := happ
    _ = fp.u * |b i| + gamma fp (2 * a + n + 3) *
        (beta * |vraw i| *
          (∑ j : Fin n, |vraw j| * |b j|)) := by
      rw [← hscale]
      ring
    _ ≤ fp.u * |b i| + gamma fp (2 * a + n + 3) *
        (Real.sqrt 2 * rho * |vraw i|) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hrow hgamma_nonneg)
    _ = fp.u * |b i| +
        gamma fp (2 * a + n + 3) * Real.sqrt 2 * rho * |vraw i| := by
      ring

/-- Scaled active-column specialization to the actual Householder
constructor. -/
theorem fl_householderConstructApply_raw_entrywise_error_scaled
    (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (x b : Fin n → ℝ) (hx : x ≠ 0) (rho : ℝ) (hrho : 0 ≤ rho)
    (hb : vecNorm2 b ≤ rho * vecNorm2 x)
    (hvalid : gammaValid fp (11 * n + 23))
    (i : Fin n) :
    |fl_householderApply fp n
          (fl_householderNormalizedVector fp hn x) 1 b i -
        matMulVec n
          (householder n (householderVector hn x)
            (householderBetaFromScale hn x)) b i| ≤
      fp.u * |b i| + gamma fp (11 * n + 23) * Real.sqrt 2 * rho *
        |householderVector hn x i| := by
  let a : ℕ := 5 * n + 10
  let beta := householderBetaFromScale hn x
  let vraw := householderVector hn x
  have hvalid_vec : gammaValid fp (8 * n + 16) :=
    gammaValid_mono fp (by omega) hvalid
  have hvec : HouseholderVectorError n
      (householderNormalizedVector n vraw beta)
      (fl_householderNormalizedVector fp hn x) (gamma fp a) := by
    simpa [a, beta, vraw] using
      fl_householderVectorError fp hn x hx hvalid_vec
  have hvalid_a : gammaValid fp a :=
    gammaValid_mono fp (by unfold a; omega) hvalid
  have hbeta_nonneg : 0 ≤ beta :=
    le_of_lt (householderBetaFromScale_pos_of_ne_zero hn x hx)
  have hbeta : beta * vecNorm2 vraw ^ 2 = 2 := by
    rw [vecNorm2_sq]
    simpa [beta, vraw, vecNorm2Sq, pow_two] using
      householderBetaFromScale_mul_norm_sq hn x hx
  have hvalid_apply : gammaValid fp (2 * a + n + 3) := by
    have hidx : 2 * a + n + 3 = 11 * n + 23 := by
      unfold a
      omega
    simpa [hidx] using hvalid
  have hsigma : 0 < |householderScale hn x| :=
    abs_pos.mpr (householderScale_ne_zero_of_ne_zero hn x hx)
  have hvnorm :
      Real.sqrt 2 * |householderScale hn x| ≤ vecNorm2 vraw := by
    simpa [vraw, abs_householderScale_eq_vecNorm2 hn x] using
      householderVector_sign_norm_bound hn x
  have hbscale : vecNorm2 b ≤ rho * |householderScale hn x| := by
    simpa [abs_householderScale_eq_vecNorm2 hn x] using hb
  have happ := fl_householderApply_raw_entrywise_error_scaled fp a n vraw
    (fl_householderNormalizedVector fp hn x) b beta
    (householderScale hn x) (gamma fp a) rho hrho
    hbeta_nonneg hvec (gamma_nonneg fp hvalid_a) le_rfl hsigma hvnorm
    hbscale hbeta hvalid_apply i
  have hidx : 2 * a + n + 3 = 11 * n + 23 := by
    unfold a
    omega
  simpa [a, beta, vraw, hidx] using happ

/-- The raw vector produced by the stable sign choice has norm at most twice
the norm of its constructor input. -/
theorem householderVector_vecNorm2_le_two {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) :
    vecNorm2 (householderVector hn x) ≤ 2 * vecNorm2 x := by
  let first : Fin n := ⟨0, hn⟩
  let e : Fin n → ℝ := finiteBasisVec first
  have hv : householderVector hn x =
      fun i => x i + householderScale hn x * e i := by
    funext i
    by_cases hi : i = first
    · subst i
      simp [first, e, finiteBasisVec, householderVector]
    · simp [first, e, finiteBasisVec, householderVector, hi]
  have he : vecNorm2 e = 1 := by
    simpa [e] using vecNorm2_finiteBasisVec first
  rw [hv]
  calc
    vecNorm2 (fun i => x i + householderScale hn x * e i) ≤
        vecNorm2 x +
          vecNorm2 (fun i => householderScale hn x * e i) :=
      vecNorm2_add_le x (fun i => householderScale hn x * e i)
    _ = vecNorm2 x + |householderScale hn x| * vecNorm2 e := by
      rw [vecNorm2_smul]
    _ = 2 * vecNorm2 x := by
      rw [he, abs_householderScale_eq_vecNorm2 hn x]
      ring

/-- Euclidean norm consequence of a two-term componentwise error budget. -/
theorem vecNorm2_le_of_abs_le_two_term {n : ℕ}
    (f b v : Fin n → ℝ) (c d : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hentry : ∀ i, |f i| ≤ c * |b i| + d * |v i|) :
    vecNorm2 f ≤ c * vecNorm2 b + d * vecNorm2 v := by
  let cb : Fin n → ℝ := fun i => c * |b i|
  let dv : Fin n → ℝ := fun i => d * |v i|
  have hpoint : ∀ i, |f i| ≤ cb i + dv i := by
    intro i
    simpa [cb, dv] using hentry i
  have hmono := vecNorm2_le_of_abs_le f (fun i => cb i + dv i) hpoint
  calc
    vecNorm2 f ≤ vecNorm2 (fun i => cb i + dv i) := hmono
    _ ≤ vecNorm2 cb + vecNorm2 dv := vecNorm2_add_le cb dv
    _ = c * vecNorm2 b + d * vecNorm2 v := by
      have hcb : vecNorm2 cb = c * vecNorm2 b := by
        rw [show cb = fun i => c * (fun q => |b q|) i by rfl,
          vecNorm2_smul, abs_of_nonneg hc, vecNorm2_abs]
      have hdv : vecNorm2 dv = d * vecNorm2 v := by
        rw [show dv = fun i => d * (fun q => |v q|) i by rfl,
          vecNorm2_smul, abs_of_nonneg hd, vecNorm2_abs]
      rw [hcb, hdv]

/-- Norm form of the scaled implementation residual.  This is the rounded
feedback quantity used to control the growth of later pivot columns and the
transport of the paired RHS error. -/
theorem fl_householderConstructApply_residual_vecNorm2_le_scaled
    (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (x b : Fin n → ℝ) (hx : x ≠ 0) (rho : ℝ) (hrho : 0 ≤ rho)
    (hb : vecNorm2 b ≤ rho * vecNorm2 x)
    (hvalid : gammaValid fp (11 * n + 23)) :
    vecNorm2 (fun i =>
        fl_householderApply fp n
            (fl_householderNormalizedVector fp hn x) 1 b i -
          matMulVec n
            (householder n (householderVector hn x)
              (householderBetaFromScale hn x)) b i) ≤
      rho * (fp.u + 2 * Real.sqrt 2 * gamma fp (11 * n + 23)) *
        vecNorm2 x := by
  let f : Fin n → ℝ := fun i =>
    fl_householderApply fp n
        (fl_householderNormalizedVector fp hn x) 1 b i -
      matMulVec n
        (householder n (householderVector hn x)
          (householderBetaFromScale hn x)) b i
  let v := householderVector hn x
  let g := gamma fp (11 * n + 23) * Real.sqrt 2 * rho
  have hg : 0 ≤ g := mul_nonneg
    (mul_nonneg (gamma_nonneg fp hvalid) (Real.sqrt_nonneg _)) hrho
  have hfentry : ∀ i, |f i| ≤ fp.u * |b i| + g * |v i| := by
    intro i
    simpa [f, v, g, mul_assoc] using
      fl_householderConstructApply_raw_entrywise_error_scaled
        fp hn x b hx rho hrho hb hvalid i
  have hnorm := vecNorm2_le_of_abs_le_two_term f b v fp.u g
    fp.u_nonneg hg hfentry
  have hvnorm := householderVector_vecNorm2_le_two hn x
  have hgamma0 : 0 ≤ gamma fp (11 * n + 23) := gamma_nonneg fp hvalid
  calc
    vecNorm2 (fun i =>
        fl_householderApply fp n
            (fl_householderNormalizedVector fp hn x) 1 b i -
          matMulVec n
            (householder n (householderVector hn x)
              (householderBetaFromScale hn x)) b i) = vecNorm2 f := by rfl
    _ ≤ fp.u * vecNorm2 b + g * vecNorm2 v := hnorm
    _ ≤ fp.u * (rho * vecNorm2 x) +
        g * (2 * vecNorm2 x) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hb fp.u_nonneg)
        (mul_le_mul_of_nonneg_left hvnorm hg)
    _ = rho * (fp.u + 2 * Real.sqrt 2 * gamma fp (11 * n + 23)) *
        vecNorm2 x := by
      simp only [g]
      ring

/-- A rounded column whose exact shadow is orthogonal grows by at most one
plus its relative local residual coefficient. -/
theorem rounded_orthogonal_column_norm_le
    {n : ℕ} (P : Fin n → Fin n → ℝ) (b e : Fin n → ℝ)
    (sigma delta : ℝ) (hP : IsOrthogonal n P)
    (hb : vecNorm2 b ≤ sigma)
    (he : vecNorm2 e ≤ delta * sigma) :
    vecNorm2 (fun i => matMulVec n P b i + e i) ≤
      (1 + delta) * sigma := by
  calc
    vecNorm2 (fun i => matMulVec n P b i + e i) ≤
        vecNorm2 (matMulVec n P b) + vecNorm2 e :=
      vecNorm2_add_le (matMulVec n P b) e
    _ = vecNorm2 b + vecNorm2 e := by rw [vecNorm2_orthogonal P b hP]
    _ ≤ sigma + delta * sigma := add_le_add hb he
    _ = (1 + delta) * sigma := by ring

/-- Iteration of a nonnegative one-step scale-growth estimate. -/
theorem scale_le_pow_mul_of_step
    (sigma : ℕ → ℝ) (g : ℝ) (hg : 0 ≤ g)
    (hstep : ∀ k, sigma (k + 1) ≤ g * sigma k)
    (q d : ℕ) :
    sigma (q + d) ≤ g ^ d * sigma q := by
  induction d with
  | zero => simp
  | succ d ih =>
      calc
        sigma (q + (d + 1)) = sigma ((q + d) + 1) := by
          congr 1
        _ ≤ g * sigma (q + d) := hstep (q + d)
        _ ≤ g * (g ^ d * sigma q) :=
          mul_le_mul_of_nonneg_left ih hg
        _ = g ^ (d + 1) * sigma q := by
          rw [pow_succ]
          ring

/-- Ratio consequence of stage-scale growth and the standard raw-vector
upper/lower norm comparisons. -/
theorem raw_vector_norm_ratio_le_of_scale_growth
    (sigma : ℕ → ℝ) (v : ℕ → Fin n → ℝ) (g : ℝ)
    (hg : 0 ≤ g)
    (hstep : ∀ k, sigma (k + 1) ≤ g * sigma k)
    (hvupper : ∀ k, vecNorm2 (v k) ≤ 2 * sigma k)
    (hvlower : ∀ k, sigma k ≤ vecNorm2 (v k))
    (q k : ℕ) (hqk : q ≤ k) (hsigmaq : 0 < sigma q) :
    vecNorm2 (v k) / vecNorm2 (v q) ≤ 2 * g ^ (k - q) := by
  have hdecomp : q + (k - q) = k := Nat.add_sub_of_le hqk
  have hscale : sigma k ≤ g ^ (k - q) * sigma q := by
    simpa only [hdecomp] using
      scale_le_pow_mul_of_step sigma g hg hstep q (k - q)
  have hgpow : 0 ≤ g ^ (k - q) := pow_nonneg hg _
  have hvk : vecNorm2 (v k) ≤ 2 * g ^ (k - q) * sigma q := by
    calc
      vecNorm2 (v k) ≤ 2 * sigma k := hvupper k
      _ ≤ 2 * (g ^ (k - q) * sigma q) :=
        mul_le_mul_of_nonneg_left hscale (by norm_num)
      _ = 2 * g ^ (k - q) * sigma q := by ring
  have hvqpos : 0 < vecNorm2 (v q) :=
    lt_of_lt_of_le hsigmaq (hvlower q)
  apply (div_le_iff₀ hvqpos).2
  calc
    vecNorm2 (v k) ≤ 2 * g ^ (k - q) * sigma q := hvk
    _ ≤ 2 * g ^ (k - q) * vecNorm2 (v q) :=
      mul_le_mul_of_nonneg_left (hvlower q)
        (mul_nonneg (by norm_num) hgpow)

/-- General-coefficient version of the Cox--Higham prefix transport.  It
separates the local error coefficient from the raw-vector row coefficient and
from the cross-stage norm ratio, which is necessary once rounded signed-pivot
storage changes the exact factor `2`. -/
theorem applyProd_rawHouseholder_entrywise_le_general {m : ℕ}
    (v : ℕ → Fin m → ℝ) (beta : ℕ → ℝ) (f : Fin m → ℝ)
    (alpha : Fin m → ℝ) (rawCoeff eta localCoeff : ℝ)
    (i : ℕ) (l : Fin m)
    (hrawCoeff : 0 ≤ rawCoeff)
    (halpha : ∀ r, 0 ≤ alpha r)
    (horth : ∀ k, IsOrthogonal m (householder m (v k) (beta k)))
    (hvpos : ∀ k < i, 0 < vecNorm2 (v k))
    (hbeta : ∀ k < i, beta k * vecNorm2 (v k) ^ 2 = 2)
    (hvrow : ∀ k < i, ∀ r, |v k r| ≤ rawCoeff * alpha r)
    (hratio : ∀ k < i, vecNorm2 f / vecNorm2 (v k) ≤ eta)
    (hfrow : |f l| ≤ localCoeff * alpha l) :
    |Wave19.applyProd (fun t => householder m (v t) (beta t)) 0 i f l| ≤
      (localCoeff + 2 * rawCoeff * (i : ℝ) * eta) * alpha l := by
  let P : ℕ → Fin m → Fin m → ℝ :=
    fun t => householder m (v t) (beta t)
  let zterm : ℕ → Fin m → ℝ := rawHouseholderZTerm v beta f i
  have hexpand := applyProd_rawHouseholder_coordinate_expansion v beta f i l
  have hz : ∀ k ∈ Finset.range i,
      |zterm k l| ≤ 2 * rawCoeff * eta * alpha l := by
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
    have hratioW : vecNorm2 wk / vecNorm2 (v k) ≤ eta := by
      rw [hwknorm]
      exact hratio k hki
    have hscale0 : 0 ≤ 4 * alpha0 :=
      mul_nonneg (by norm_num) halpha0
    have hbound :
        |(2 / vecNorm2 (v k) ^ 2) * v k l *
            (∑ s : Fin m, v k s * wk s)| ≤
          4 * alpha0 * eta := by
      calc
        |(2 / vecNorm2 (v k) ^ 2) * v k l *
            (∑ s : Fin m, v k s * wk s)| ≤
            4 * alpha0 * (vecNorm2 wk / vecNorm2 (v k)) := hrank
        _ ≤ 4 * alpha0 * eta :=
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
    calc
      |(2 / vecNorm2 (v k) ^ 2) * v k l *
          (∑ s : Fin m, v k s * wk s)| ≤ 4 * alpha0 * eta := hbound
      _ = 2 * rawCoeff * eta * alpha l := by
        simp [alpha0]
        ring
  have hsumAbs :
      |∑ k ∈ Finset.range i, zterm k l| ≤
        (i : ℝ) * (2 * rawCoeff * eta * alpha l) := by
    calc
      |∑ k ∈ Finset.range i, zterm k l| ≤
          ∑ k ∈ Finset.range i, |zterm k l| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range i,
          (2 * rawCoeff * eta * alpha l) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hz k hk
      _ = (i : ℝ) * (2 * rawCoeff * eta * alpha l) := by
        simp
  have hsub := abs_sub_le (f l) 0
    (∑ k ∈ Finset.range i, zterm k l)
  rw [hexpand]
  calc
    |f l - ∑ k ∈ Finset.range i, zterm k l| ≤
        |f l| + |∑ k ∈ Finset.range i, zterm k l| := by
      simpa using hsub
    _ ≤ localCoeff * alpha l +
        (i : ℝ) * (2 * rawCoeff * eta * alpha l) :=
      add_le_add hfrow hsumAbs
    _ = (localCoeff + 2 * rawCoeff * (i : ℝ) * eta) * alpha l := by
      ring

end Theorem20_7

end NumStability
