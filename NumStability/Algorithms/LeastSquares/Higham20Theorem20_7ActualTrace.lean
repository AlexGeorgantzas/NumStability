import NumStability.Algorithms.LeastSquares.Higham20Theorem20_7SourceTrace

namespace NumStability

open scoped BigOperators

namespace Theorem20_7

/-!
# The actually rounded Cox--Higham stored trace

`Higham20Theorem20_7SourceTrace` isolates the source storage convention and
the exact signed-vector geometry.  Its reflector constructor is deliberately
exact, however, so it is not by itself an implementation of the algorithm
analysed in Cox--Higham.

This module adds the missing implementation layer.  At an active stage the
pivot row is exchanged with row zero in an analysis-local work array, the
inactive prefix is masked, and the repository's concrete
`fl_householderScale`, `fl_householderVector`, and `fl_householderBeta`
constructor is used through `fl_householderNormalizedVector`.  The rounded
dot/scale/subtract application is then performed by
`fl_householderApplyMatrixRect`.  The result is exchanged back before the
source storage convention is imposed.  Thus every arithmetic operation in the
constructor and application is supplied by `FPModel`.

The row exchange is not an arithmetic operation.  It lets the existing
first-coordinate constructor be reused at every active pivot while retaining
one full-shape trace.  Masked prefix entries are exact zeros, so the work array
contains precisely the active tails used by column pivoting.
-/

/-- Exchange the active pivot row with the constructor's first coordinate. -/
def sourceConstructedRowSwap {m : ℕ} (hm : 0 < m) (row : Fin m) :
    Equiv.Perm (Fin m) :=
  Equiv.swap ⟨0, hm⟩ row

/-- Active work panel after the analysis-local row exchange.  Prefix rows are
masked because the stage reflector acts only on rows `k:m`. -/
noncomputable def sourceConstructedActivePanelPerm {m n : ℕ}
    (k : ℕ) (Srow : Equiv.Perm (Fin m))
    (As : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun q j => if (Srow q).val < k then 0 else As (Srow q) j

/-- The active pivot column presented to the concrete first-coordinate
Householder constructor. -/
noncomputable def sourceConstructedActiveInput {m n : ℕ}
    (k : ℕ) (Srow : Equiv.Perm (Fin m))
    (As : Fin m → Fin n → ℝ) (col : Fin n) : Fin m → ℝ :=
  fun q => sourceConstructedActivePanelPerm k Srow As q col

/-- One actually rounded source-stored panel step.

Completed columns and rows are copied.  The pivot diagonal stores the rounded
`alpha_hat = -s_hat`, the pivot tail is exactly zero, and the active trailing
rectangle is the concrete rounded constructor/application result. -/
noncomputable def fl_householderCoxHighamConstructedPanelStep
    (fp : FPModel) {m n : ℕ} (hm : 0 < m) (k : ℕ)
    (row : Fin m) (col : Fin n) (As : Fin m → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  let Srow := sourceConstructedRowSwap hm row
  let Aactive := sourceConstructedActivePanelPerm k Srow As
  let x := sourceConstructedActiveInput k Srow As col
  if hx : x = 0 then
    fun i j =>
      if j.val < k then
        As i j
      else if i.val < k then
        As i j
      else if j.val = k then
        0
      else
        As i j
  else
    let alphaHat := fl_householderAlpha fp hm x
    let wHat := fl_householderNormalizedVector fp hm x
    let rawPerm := fl_householderApplyMatrixRect fp m n wHat 1 Aactive
    fun i j =>
      if j.val < k then
        As i j
      else if i.val < k then
        As i j
      else if j.val = k then
        if i.val = k then alphaHat else 0
      else
        rawPerm (Srow i) j

theorem fl_householderCoxHighamConstructedPanelStep_prevColumn_eq
    (fp : FPModel) {m n k : ℕ} (hm : 0 < m)
    (row : Fin m) (col : Fin n) (As : Fin m → Fin n → ℝ)
    {i : Fin m} {j : Fin n} (hj : j.val < k) :
    fl_householderCoxHighamConstructedPanelStep fp hm k row col As i j =
      As i j := by
  by_cases hx : sourceConstructedActiveInput k
      (sourceConstructedRowSwap hm row) As col = 0 <;>
    simp [fl_householderCoxHighamConstructedPanelStep, hx, hj]

theorem fl_householderCoxHighamConstructedPanelStep_prevRow_eq
    (fp : FPModel) {m n k : ℕ} (hm : 0 < m)
    (row : Fin m) (col : Fin n) (As : Fin m → Fin n → ℝ)
    {i : Fin m} {j : Fin n} (hi : i.val < k) :
    fl_householderCoxHighamConstructedPanelStep fp hm k row col As i j =
      As i j := by
  by_cases hx : sourceConstructedActiveInput k
      (sourceConstructedRowSwap hm row) As col = 0 <;>
  by_cases hj : j.val < k <;>
    simp [fl_householderCoxHighamConstructedPanelStep, hx, hj, hi]

theorem fl_householderCoxHighamConstructedPanelStep_pivot_eq
    (fp : FPModel) {m n k : ℕ} (hm : 0 < m)
    (row : Fin m) (col : Fin n) (As : Fin m → Fin n → ℝ)
    {i : Fin m} {j : Fin n} (hi : i.val = k) (hj : j.val = k) :
    fl_householderCoxHighamConstructedPanelStep fp hm k row col As i j =
      let x := sourceConstructedActiveInput k
        (sourceConstructedRowSwap hm row) As col
      if x = 0 then 0 else fl_householderAlpha fp hm x := by
  have hni : ¬ i.val < k := by omega
  have hnj : ¬ j.val < k := by omega
  by_cases hx : sourceConstructedActiveInput k
      (sourceConstructedRowSwap hm row) As col = 0 <;>
    simp [fl_householderCoxHighamConstructedPanelStep, hx, hni, hnj, hi, hj]

theorem fl_householderCoxHighamConstructedPanelStep_pivotTail_eq_zero
    (fp : FPModel) {m n k : ℕ} (hm : 0 < m)
    (row : Fin m) (col : Fin n) (As : Fin m → Fin n → ℝ)
    {i : Fin m} {j : Fin n} (hi : k < i.val) (hj : j.val = k) :
    fl_householderCoxHighamConstructedPanelStep fp hm k row col As i j = 0 := by
  have hni : ¬ i.val < k := by omega
  have hnj : ¬ j.val < k := by omega
  have hine : ¬ i.val = k := by omega
  by_cases hx : sourceConstructedActiveInput k
      (sourceConstructedRowSwap hm row) As col = 0 <;>
    simp [fl_householderCoxHighamConstructedPanelStep, hx, hni, hnj, hine, hj]

/-! ## Executed active-max loop -/

/-- Full-shape, actively pivoted, actually rounded source-stored QR trace. -/
noncomputable def fl_sourceConstructedPivotedStoredQRMatrixSeq
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) : ℕ → Fin m → Fin n → ℝ
  | 0 => A
  | k + 1 =>
      if hk : k < n then
        let Aprev := fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A k
        let row := pivotedQRActiveRow hmn k hk
        let col := pivotedQRActiveCol k hk
        let q := householderActiveMaxPivotColumn row col Aprev
        let As := Wave13.columnPermuteMatrix Aprev (Equiv.swap col q)
        fl_householderCoxHighamConstructedPanelStep fp
          (lt_of_lt_of_le hn hmn) k row col As
      else
        fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A k

noncomputable def sourceConstructedPivotedStoredQRSwapSeq
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) : Equiv.Perm (Fin n) :=
  if hk : k < n then
    let row := pivotedQRActiveRow hmn k hk
    let col := pivotedQRActiveCol k hk
    Equiv.swap col
      (householderActiveMaxPivotColumn row col
        (fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A k))
  else
    Equiv.refl _

noncomputable def sourceConstructedPivotedStoredQRSwappedPanel
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) : Fin m → Fin n → ℝ :=
  Wave13.columnPermuteMatrix
    (fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A k)
    (sourceConstructedPivotedStoredQRSwapSeq fp hn hmn A k)

noncomputable def sourceConstructedPivotedStoredQRRowSwap
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) : Equiv.Perm (Fin m) :=
  if hk : k < n then
    sourceConstructedRowSwap (lt_of_lt_of_le hn hmn)
      (pivotedQRActiveRow hmn k hk)
  else
    Equiv.refl _

/-- Work-array active panel at stage `k`, including the local row exchange. -/
noncomputable def sourceConstructedPivotedStoredQRActivePanelPerm
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) : Fin m → Fin n → ℝ :=
  sourceConstructedActivePanelPerm k
    (sourceConstructedPivotedStoredQRRowSwap fp hn hmn A k)
    (sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k)

/-- Work-array pivot column consumed by the concrete rounded constructor. -/
noncomputable def sourceConstructedPivotedStoredQRActiveInput
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) : Fin m → ℝ :=
  if hk : k < n then
    sourceConstructedActiveInput k
      (sourceConstructedPivotedStoredQRRowSwap fp hn hmn A k)
      (sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k)
      (pivotedQRActiveCol k hk)
  else
    0

/-- Rounded signed diagonal value actually stored at stage `k`. -/
noncomputable def sourceConstructedPivotedStoredQRRoundedAlpha
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) : ℝ :=
  if _hk : k < n then
    let x := sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k
    if x = 0 then 0
    else fl_householderAlpha fp (lt_of_lt_of_le hn hmn) x
  else
    0

/-- Computed normalized reflector in work-array row coordinates. -/
noncomputable def sourceConstructedPivotedStoredQRComputedVectorPerm
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) : Fin m → ℝ :=
  let x := sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k
  if x = 0 then 0
  else fl_householderNormalizedVector fp (lt_of_lt_of_le hn hmn) x

/-- Exact raw constructor vector paired with the computed constructor, in
work-array row coordinates. -/
noncomputable def sourceConstructedPivotedStoredQRExactRawVectorPerm
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) : Fin m → ℝ :=
  householderVector (lt_of_lt_of_le hn hmn)
    (sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k)

/-- Exact raw constructor vector in the stored matrix's original row
coordinates. -/
noncomputable def sourceConstructedPivotedStoredQRExactRawVector
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) : Fin m → ℝ :=
  fun i => sourceConstructedPivotedStoredQRExactRawVectorPerm fp hn hmn A k
    (sourceConstructedPivotedStoredQRRowSwap fp hn hmn A k i)

noncomputable def sourceConstructedPivotedStoredQRExactBeta
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) : ℝ :=
  householderBetaFromScale (lt_of_lt_of_le hn hmn)
    (sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k)

/-- Orthogonal-shadow reflector used by the Cox--Higham residual telescope. -/
noncomputable def sourceConstructedPivotedStoredQRPseq
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) : Fin m → Fin m → ℝ :=
  householder m
    (sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A k)
    (sourceConstructedPivotedStoredQRExactBeta fp hn hmn A k)

theorem fl_sourceConstructedPivotedStoredQRMatrixSeq_succ_of_lt
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n) :
    fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A (k + 1) =
      fl_householderCoxHighamConstructedPanelStep fp
        (lt_of_lt_of_le hn hmn) k
        (pivotedQRActiveRow hmn k hk) (pivotedQRActiveCol k hk)
        (sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k) := by
  simp [fl_sourceConstructedPivotedStoredQRMatrixSeq,
    sourceConstructedPivotedStoredQRSwappedPanel,
    sourceConstructedPivotedStoredQRSwapSeq, hk]

theorem fl_sourceConstructedPivotedStoredQRMatrixSeq_succ_pivot_eq_alpha
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n) :
    fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A (k + 1)
        (pivotedQRActiveRow hmn k hk) (pivotedQRActiveCol k hk) =
      sourceConstructedPivotedStoredQRRoundedAlpha fp hn hmn A k := by
  rw [fl_sourceConstructedPivotedStoredQRMatrixSeq_succ_of_lt
    fp hn hmn A k hk]
  simpa [sourceConstructedPivotedStoredQRRoundedAlpha,
    sourceConstructedPivotedStoredQRActiveInput,
    sourceConstructedPivotedStoredQRRowSwap, hk] using
    fl_householderCoxHighamConstructedPanelStep_pivot_eq fp
      (lt_of_lt_of_le hn hmn)
      (pivotedQRActiveRow hmn k hk) (pivotedQRActiveCol k hk)
      (sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k)
      (i := pivotedQRActiveRow hmn k hk)
      (j := pivotedQRActiveCol k hk)
      (by simp [pivotedQRActiveRow]) (by simp [pivotedQRActiveCol])

/-! ## Exact-shadow geometry and active-maximality -/

theorem sourceConstructedPivotedStoredQRExactRawVector_eq_vecPermute
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) :
    sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A k =
      vecPermute (sourceConstructedPivotedStoredQRRowSwap fp hn hmn A k)
        (sourceConstructedPivotedStoredQRExactRawVectorPerm fp hn hmn A k) := by
  rfl

/-- The exact reflector shadow of the actually rounded constructor is
orthogonal whenever the active constructor input is nonzero.  No property of
the rounded vector or rounded beta is assumed. -/
theorem sourceConstructedPivotedStoredQRPseq_orthogonal_of_input_ne
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ)
    (hx : sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k ≠ 0) :
    IsOrthogonal m (sourceConstructedPivotedStoredQRPseq fp hn hmn A k) := by
  let hm : 0 < m := lt_of_lt_of_le hn hmn
  let x := sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k
  let S := sourceConstructedPivotedStoredQRRowSwap fp hn hmn A k
  let v0 := householderVector hm x
  let v := vecPermute S v0
  let beta := householderBetaFromScale hm x
  have hbeta0 : beta * (∑ q : Fin m, v0 q * v0 q) = 2 := by
    simpa [beta, v0, x, hm] using
      householderBetaFromScale_mul_norm_sq hm x hx
  have hsq : (∑ q : Fin m, v q * v q) = ∑ q : Fin m, v0 q * v0 q := by
    have h := vecNorm2Sq_permute S v0
    simpa [vecNorm2Sq, pow_two, v] using h
  apply householder_orthogonal m v beta
  rw [hsq]
  exact hbeta0

/-- Executed column exchanges fix every completed column position. -/
theorem sourceConstructedPivotedStoredQRSwapSeq_fix_prefix
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (j : Fin n)
    (hj : j.val < k) :
    sourceConstructedPivotedStoredQRSwapSeq fp hn hmn A k j = j := by
  by_cases hk : k < n
  · let row := pivotedQRActiveRow hmn k hk
    let col := pivotedQRActiveCol k hk
    let q := householderActiveMaxPivotColumn row col
      (fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A k)
    have hjc : j ≠ col := by
      intro h
      subst j
      exact Nat.lt_irrefl k hj
    have hqge : k ≤ q.val := by
      simpa [q, col] using householderActiveMaxPivotColumn_ge row col
        (fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A k)
    have hjq : j ≠ q := by
      intro h
      subst j
      omega
    simp only [sourceConstructedPivotedStoredQRSwapSeq, dif_pos hk]
    exact Equiv.swap_apply_of_ne_of_ne hjc hjq
  · simp [sourceConstructedPivotedStoredQRSwapSeq, hk]

/-- Executed column exchanges map the active suffix into itself. -/
theorem sourceConstructedPivotedStoredQRSwapSeq_maps_active
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (j : Fin n)
    (hj : k ≤ j.val) :
    k ≤ (sourceConstructedPivotedStoredQRSwapSeq fp hn hmn A k j).val := by
  by_cases hk : k < n
  · let row := pivotedQRActiveRow hmn k hk
    let col := pivotedQRActiveCol k hk
    let q := householderActiveMaxPivotColumn row col
      (fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A k)
    have hqge : k ≤ q.val := by
      simpa [q, col] using householderActiveMaxPivotColumn_ge row col
        (fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A k)
    simp only [sourceConstructedPivotedStoredQRSwapSeq, dif_pos hk]
    by_cases hjc : j = col
    · subst j
      rw [Equiv.swap_apply_left]
      exact hqge
    · by_cases hjq : j = q
      · subst j
        rw [Equiv.swap_apply_right]
        rfl
      · rw [Equiv.swap_apply_of_ne_of_ne hjc hjq]
        exact hj
  · simp [sourceConstructedPivotedStoredQRSwapSeq, hk]
    exact hj

/-- The executed selector places an active trailing-norm-maximal column at
the pivot position. -/
theorem sourceConstructedPivotedStoredQRSwappedPanel_pivot_max
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n) :
    ∀ l : Fin n, k ≤ l.val →
      householderTrailingColumnNorm2Sq
          (pivotedQRActiveRow hmn k hk)
          (sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k) l ≤
        householderTrailingColumnNorm2Sq
          (pivotedQRActiveRow hmn k hk)
          (sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k)
          (pivotedQRActiveCol k hk) := by
  let Aprev := fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A k
  let row := pivotedQRActiveRow hmn k hk
  let col := pivotedQRActiveCol k hk
  let q := householderActiveMaxPivotColumn row col Aprev
  have hswap : sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k =
      householderSwapColumns Aprev col q := by
    unfold sourceConstructedPivotedStoredQRSwappedPanel
    have hS : sourceConstructedPivotedStoredQRSwapSeq fp hn hmn A k =
        Equiv.swap col q := by
      simp [sourceConstructedPivotedStoredQRSwapSeq, hk, row, col, q, Aprev]
    rw [hS]
    exact columnPermuteMatrix_swap_eq_householderSwapColumns Aprev col q
  rw [hswap]
  exact householderSwapColumns_activeMaxPivotColumn_pivot_max row col Aprev

/-- A work-array column is the row permutation of the active trailing part of
the displayed panel column. -/
theorem sourceConstructedPivotedStoredQRActivePanelPerm_col_eq
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n) (j : Fin n) :
    (fun q => sourceConstructedPivotedStoredQRActivePanelPerm
        fp hn hmn A k q j) =
      vecPermute (sourceConstructedPivotedStoredQRRowSwap fp hn hmn A k)
        (householderTrailingPart m (pivotedQRActiveRow hmn k hk)
          (fun i => sourceConstructedPivotedStoredQRSwappedPanel
            fp hn hmn A k i j)) := by
  funext q
  simp [sourceConstructedPivotedStoredQRActivePanelPerm,
    sourceConstructedActivePanelPerm, vecPermute, householderTrailingPart,
    pivotedQRActiveRow]

/-- Masking and the local row exchange preserve the squared active-column
norm. -/
theorem sourceConstructedPivotedStoredQRActivePanelPerm_col_normSq
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n) (j : Fin n) :
    vecNorm2Sq (fun q => sourceConstructedPivotedStoredQRActivePanelPerm
        fp hn hmn A k q j) =
      householderTrailingColumnNorm2Sq
        (pivotedQRActiveRow hmn k hk)
        (sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k) j := by
  rw [sourceConstructedPivotedStoredQRActivePanelPerm_col_eq
    fp hn hmn A k hk j, vecNorm2Sq_permute]
  rfl

/-- The pivot column supplied to the concrete constructor has maximal
Euclidean norm among all active work-panel columns. -/
theorem sourceConstructedPivotedStoredQRActiveInput_pivot_max
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n) :
    ∀ j : Fin n, k ≤ j.val →
      vecNorm2 (fun q => sourceConstructedPivotedStoredQRActivePanelPerm
          fp hn hmn A k q j) ≤
        vecNorm2 (sourceConstructedPivotedStoredQRActiveInput
          fp hn hmn A k) := by
  intro j hj
  have hmax := sourceConstructedPivotedStoredQRSwappedPanel_pivot_max
    fp hn hmn A k hk j hj
  have hjSq := sourceConstructedPivotedStoredQRActivePanelPerm_col_normSq
    fp hn hmn A k hk j
  have hpSq := sourceConstructedPivotedStoredQRActivePanelPerm_col_normSq
    fp hn hmn A k hk (pivotedQRActiveCol k hk)
  have hinput : sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k =
      fun q => sourceConstructedPivotedStoredQRActivePanelPerm fp hn hmn A k q
        (pivotedQRActiveCol k hk) := by
    funext q
    simp [sourceConstructedPivotedStoredQRActiveInput,
      sourceConstructedPivotedStoredQRActivePanelPerm,
      sourceConstructedActiveInput, hk]
  apply (sq_le_sq₀ (vecNorm2_nonneg _)
    (vecNorm2_nonneg (sourceConstructedPivotedStoredQRActiveInput
      fp hn hmn A k))).mp
  rw [vecNorm2_sq, vecNorm2_sq, hinput]
  change vecNorm2Sq
      (fun q => sourceConstructedPivotedStoredQRActivePanelPerm
        fp hn hmn A k q j) ≤
    vecNorm2Sq
      (fun q => sourceConstructedPivotedStoredQRActivePanelPerm
        fp hn hmn A k q (pivotedQRActiveCol k hk))
  rw [hjSq, hpSq]
  exact hmax

/-- Exact active pivot scale of the work-array constructor input. -/
noncomputable def sourceConstructedPivotedStoredQRSigma
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) : ℝ :=
  vecNorm2 (sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k)

theorem sourceConstructedPivotedStoredQRActiveInput_ne_of_sigma_pos
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ)
    (hsigma : 0 < sourceConstructedPivotedStoredQRSigma fp hn hmn A k) :
    sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k ≠ 0 := by
  intro hx
  unfold sourceConstructedPivotedStoredQRSigma at hsigma
  rw [hx] at hsigma
  simpa [vecNorm2, vecNorm2Sq] using hsigma

theorem sourceConstructedPivotedStoredQRPseq_orthogonal
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ)
    (hsigma : 0 < sourceConstructedPivotedStoredQRSigma fp hn hmn A k) :
    IsOrthogonal m (sourceConstructedPivotedStoredQRPseq fp hn hmn A k) :=
  sourceConstructedPivotedStoredQRPseq_orthogonal_of_input_ne
    fp hn hmn A k
      (sourceConstructedPivotedStoredQRActiveInput_ne_of_sigma_pos
        fp hn hmn A k hsigma)

/-- Every exact shadow reflector used by the executed constructor is
orthogonal, including the zero-active-column branch where the reflector is
the identity.  This unconditional form is the one needed by the accumulated
residual telescope. -/
theorem sourceConstructedPivotedStoredQRPseq_orthogonal_unconditional
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) :
    IsOrthogonal m (sourceConstructedPivotedStoredQRPseq fp hn hmn A k) := by
  by_cases hx : sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k = 0
  · have hvPerm :
        sourceConstructedPivotedStoredQRExactRawVectorPerm fp hn hmn A k = 0 := by
      funext i
      simp [sourceConstructedPivotedStoredQRExactRawVectorPerm, hx,
        householderVector, householderScale]
    have hv : sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A k = 0 := by
      funext i
      simp [sourceConstructedPivotedStoredQRExactRawVector, hvPerm]
    have hbeta : sourceConstructedPivotedStoredQRExactBeta fp hn hmn A k = 0 := by
      simp [sourceConstructedPivotedStoredQRExactBeta, hx,
        householderBetaFromScale, householderVector, householderScale]
    have hP : sourceConstructedPivotedStoredQRPseq fp hn hmn A k = idMatrix m := by
      funext i j
      simp [sourceConstructedPivotedStoredQRPseq, hv, hbeta, householder]
    rw [hP]
    exact idMatrix_orthogonal m
  · exact sourceConstructedPivotedStoredQRPseq_orthogonal_of_input_ne
      fp hn hmn A k hx

/-- The guarded zero-active-column branch has the identity as its exact
shadow reflector. -/
theorem sourceConstructedPivotedStoredQRPseq_eq_id_of_input_eq_zero
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ)
    (hx : sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k = 0) :
    sourceConstructedPivotedStoredQRPseq fp hn hmn A k = idMatrix m := by
  have hvPerm :
      sourceConstructedPivotedStoredQRExactRawVectorPerm fp hn hmn A k = 0 := by
    funext i
    simp [sourceConstructedPivotedStoredQRExactRawVectorPerm, hx,
      householderVector, householderScale]
  have hv : sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A k = 0 := by
    funext i
    simp [sourceConstructedPivotedStoredQRExactRawVector, hvPerm]
  have hbeta : sourceConstructedPivotedStoredQRExactBeta fp hn hmn A k = 0 := by
    simp [sourceConstructedPivotedStoredQRExactBeta, hx,
      householderBetaFromScale, householderVector, householderScale]
  funext i j
  simp [sourceConstructedPivotedStoredQRPseq, hv, hbeta, householder]

/-- If the active constructor input is zero, then every stored coordinate of
the displayed pivot column in the active row suffix is zero. -/
theorem sourceConstructedPivotedStoredQRSwappedPanel_pivotColumn_eq_zero_of_input_eq_zero
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n)
    (hx : sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k = 0)
    (i : Fin m) (hi : k ≤ i.val) :
    sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k i
        (pivotedQRActiveCol k hk) = 0 := by
  let S := sourceConstructedPivotedStoredQRRowSwap fp hn hmn A k
  have hSinv : S (S i) = i := by
    simp [S, sourceConstructedPivotedStoredQRRowSwap,
      sourceConstructedRowSwap, hk]
  have hactive : ¬ (S (S i)).val < k := by
    rw [hSinv]
    exact Nat.not_lt.mpr hi
  have hpoint := congrFun hx (S i)
  simp only [sourceConstructedPivotedStoredQRActiveInput, dif_pos hk,
    sourceConstructedActiveInput,
    sourceConstructedPivotedStoredQRActivePanelPerm,
    sourceConstructedActivePanelPerm] at hpoint
  change (if (S (S i)).val < k then 0 else
      sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k
        (S (S i)) (pivotedQRActiveCol k hk)) = 0 at hpoint
  rw [if_neg hactive, hSinv] at hpoint
  exact hpoint

/-- The exact raw shadow vector has the same zero prefix as the executed
active-tail constructor. -/
theorem sourceConstructedPivotedStoredQRExactRawVector_zero_prefix
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n)
    (i : Fin m) (hi : i.val < k) :
    sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A k i = 0 := by
  let hm : 0 < m := lt_of_lt_of_le hn hmn
  let row := pivotedQRActiveRow hmn k hk
  let first : Fin m := ⟨0, hm⟩
  let S := sourceConstructedPivotedStoredQRRowSwap fp hn hmn A k
  let x := sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k
  have hS : S = Equiv.swap first row := by
    simp [S, sourceConstructedPivotedStoredQRRowSwap,
      sourceConstructedRowSwap, first, row, hk, hm]
  have hSi : S i ≠ first := by
    rw [hS]
    intro h
    have hback := congrArg (Equiv.swap first row) h
    simp only [Equiv.swap_apply_self, Equiv.swap_apply_left] at hback
    have hir : i = row := hback
    have hiv := congrArg Fin.val hir
    simp [row, pivotedQRActiveRow] at hiv
    omega
  have hSS : S (S i) = i := by
    simp [hS]
  have hxSi : x (S i) = 0 := by
    simp only [x, sourceConstructedPivotedStoredQRActiveInput, dif_pos hk,
      sourceConstructedActiveInput]
    change sourceConstructedActivePanelPerm k S
      (sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k)
      (S i) (pivotedQRActiveCol k hk) = 0
    simp [sourceConstructedActivePanelPerm, hSS, hi]
  rw [sourceConstructedPivotedStoredQRExactRawVector_eq_vecPermute]
  simp only [vecPermute]
  rw [show sourceConstructedPivotedStoredQRExactRawVectorPerm fp hn hmn A k =
      householderVector hm x by rfl]
  rw [householderVector_tail hm x (S i) hSi, hxSi]

/-- Copying completed columns and zeroing each completed pivot tail preserves
the exact lower-trapezoidal storage invariant. -/
theorem fl_sourceConstructedPivotedStoredQRMatrixSeq_prefix_lower_zero
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) :
    ∀ k, k ≤ n → ∀ (i : Fin m) (j : Fin n),
      j.val < k → j.val < i.val →
        fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A k i j = 0 := by
  intro k
  induction k with
  | zero =>
      intro _hk i j hj _hji
      exact (Nat.not_lt_zero j.val hj).elim
  | succ k ih =>
      intro hkSucc i j hjSucc hji
      have hk : k < n := Nat.lt_of_succ_le hkSucc
      have hstep :
          fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A (k + 1) i j =
            fl_householderCoxHighamConstructedPanelStep fp
              (lt_of_lt_of_le hn hmn) k
              (pivotedQRActiveRow hmn k hk) (pivotedQRActiveCol k hk)
              (sourceConstructedPivotedStoredQRSwappedPanel
                fp hn hmn A k) i j := by
        exact congrFun (congrFun
          (fl_sourceConstructedPivotedStoredQRMatrixSeq_succ_of_lt
            fp hn hmn A k hk) i) j
      rcases Nat.lt_succ_iff_lt_or_eq.mp hjSucc with hj | hj
      · have hfix := sourceConstructedPivotedStoredQRSwapSeq_fix_prefix
          fp hn hmn A k j hj
        calc
          fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A (k + 1) i j =
              fl_householderCoxHighamConstructedPanelStep fp
                (lt_of_lt_of_le hn hmn) k
                (pivotedQRActiveRow hmn k hk) (pivotedQRActiveCol k hk)
                (sourceConstructedPivotedStoredQRSwappedPanel
                  fp hn hmn A k) i j := hstep
          _ = sourceConstructedPivotedStoredQRSwappedPanel
                fp hn hmn A k i j := by
            exact fl_householderCoxHighamConstructedPanelStep_prevColumn_eq
              fp (lt_of_lt_of_le hn hmn)
              (pivotedQRActiveRow hmn k hk) (pivotedQRActiveCol k hk)
              (sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k) hj
          _ = fl_sourceConstructedPivotedStoredQRMatrixSeq
                fp hn hmn A k i j := by
            simp [sourceConstructedPivotedStoredQRSwappedPanel,
              Wave13.columnPermuteMatrix, hfix]
          _ = 0 := ih (Nat.le_of_lt hk) i j hj hji
      · let col : Fin n := ⟨k, hk⟩
        have hjfin : j = col := Fin.ext hj
        subst j
        have hki : k < i.val := by simpa [col] using hji
        rw [hstep]
        exact fl_householderCoxHighamConstructedPanelStep_pivotTail_eq_zero
          fp (lt_of_lt_of_le hn hmn)
          (pivotedQRActiveRow hmn k hk) (pivotedQRActiveCol k hk)
          (sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k)
          hki (by simp [col])

/-- The final actually rounded source-stored matrix is upper trapezoidal. -/
theorem fl_sourceConstructedPivotedStoredQRMatrixSeq_upperTrapezoidal
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) :
    IsUpperTrapezoidal m n
      (fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A n) := by
  intro i j hji
  exact fl_sourceConstructedPivotedStoredQRMatrixSeq_prefix_lower_zero
    fp hn hmn A n le_rfl i j j.isLt hji

/-- Individual exact-shadow residual of one actually rounded stage. -/
noncomputable def sourceConstructedPivotedStoredQREseq
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) : Fin m → Fin n → ℝ :=
  fun i j =>
    fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A (k + 1) i j -
      matMulRect m m n
        (sourceConstructedPivotedStoredQRPseq fp hn hmn A k)
        (sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k) i j

theorem sourceConstructedPivotedStoredQR_step_with_residual
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (i : Fin m) (j : Fin n) :
    fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A (k + 1) i j =
      matMulRect m m n
          (sourceConstructedPivotedStoredQRPseq fp hn hmn A k)
          (Wave13.columnPermuteMatrix
            (fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A k)
            (sourceConstructedPivotedStoredQRSwapSeq fp hn hmn A k)) i j +
        sourceConstructedPivotedStoredQREseq fp hn hmn A k i j := by
  simp only [sourceConstructedPivotedStoredQREseq,
    sourceConstructedPivotedStoredQRSwappedPanel]
  simp

/-- The guarded zero-active-column stage is exactly the identity-reflector
step on the displayed swapped panel. -/
theorem fl_sourceConstructedPivotedStoredQRMatrixSeq_succ_eq_swappedPanel_of_input_eq_zero
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n)
    (hx : sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k = 0) :
    fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A (k + 1) =
      sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k := by
  rw [fl_sourceConstructedPivotedStoredQRMatrixSeq_succ_of_lt
    fp hn hmn A k hk]
  funext i j
  let hm : 0 < m := lt_of_lt_of_le hn hmn
  let row := pivotedQRActiveRow hmn k hk
  let col := pivotedQRActiveCol k hk
  let As := sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k
  have hxDirect : sourceConstructedActiveInput k
      (sourceConstructedRowSwap hm row) As col = 0 := by
    simpa [hm, row, col, As, sourceConstructedPivotedStoredQRActiveInput,
      sourceConstructedPivotedStoredQRRowSwap, hk] using hx
  simp only [fl_householderCoxHighamConstructedPanelStep]
  rw [dif_pos hxDirect]
  by_cases hjPrev : j.val < k
  · simp [hjPrev]
  by_cases hiPrev : i.val < k
  · simp [hjPrev, hiPrev]
  by_cases hjPivot : j.val = k
  · have hjcol : j = pivotedQRActiveCol k hk := Fin.ext hjPivot
    subst j
    have hz :=
      sourceConstructedPivotedStoredQRSwappedPanel_pivotColumn_eq_zero_of_input_eq_zero
        fp hn hmn A k hk hx i (Nat.le_of_not_gt hiPrev)
    simpa [hjPrev, hiPrev, As, pivotedQRActiveCol] using hz.symm
  · simp [hjPrev, hiPrev, hjPivot]

/-- The named exact-shadow residual is zero in the guarded zero-active-column
branch. -/
theorem sourceConstructedPivotedStoredQREseq_eq_zero_of_input_eq_zero
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n)
    (hx : sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k = 0) :
    sourceConstructedPivotedStoredQREseq fp hn hmn A k = 0 := by
  funext i j
  rw [sourceConstructedPivotedStoredQREseq,
    congrFun (congrFun
      (fl_sourceConstructedPivotedStoredQRMatrixSeq_succ_eq_swappedPanel_of_input_eq_zero
        fp hn hmn A k hk hx) i) j,
    sourceConstructedPivotedStoredQRPseq_eq_id_of_input_eq_zero
      fp hn hmn A k hx,
    matMulRect_id_left]
  simp

/-! ## Row-conjugation and the implementation-backed one-step residual -/

/-- Conjugating a Householder vector and its argument by an involutive row
permutation conjugates the resulting matrix-vector product. -/
theorem matMulVec_householder_vecPermute_involution {m : ℕ}
    (S : Equiv.Perm (Fin m)) (v b : Fin m → ℝ) (beta : ℝ)
    (hS : ∀ q, S (S q) = q) (i : Fin m) :
    matMulVec m (householder m (vecPermute S v) beta) b i =
      matMulVec m (householder m v beta) (vecPermute S b) (S i) := by
  rw [householder_matMulVec_eq, householder_matMulVec_eq]
  have hsum : (∑ q : Fin m, v (S q) * b q) =
      ∑ q : Fin m, v q * b (S q) := by
    calc
      (∑ q : Fin m, v (S q) * b q) =
          ∑ q : Fin m, (fun r => v r * b (S r)) (S q) := by
            apply Finset.sum_congr rfl
            intro q _
            change v (S q) * b q = v (S q) * b (S (S q))
            rw [hS q]
      _ = ∑ q : Fin m, v q * b (S q) := by
        simpa using (Equiv.sum_comp S (fun r => v r * b (S r)))
  simp only [vecPermute]
  rw [hS, hsum]

/-- Two Householder products agree at a coordinate when the coordinate and
every weighted dot-product summand agree. -/
theorem matMulVec_householder_eq_of_coordinate_weighted_eq {m : ℕ}
    (v b c : Fin m → ℝ) (beta : ℝ) (i : Fin m)
    (hcoord : b i = c i)
    (hweighted : ∀ q, v q * b q = v q * c q) :
    matMulVec m (householder m v beta) b i =
      matMulVec m (householder m v beta) c i := by
  rw [householder_matMulVec_eq, householder_matMulVec_eq]
  change b i - beta * v i * (∑ q : Fin m, v q * b q) =
    c i - beta * v i * (∑ q : Fin m, v q * c q)
  rw [hcoord]
  congr 2
  apply Finset.sum_congr rfl
  intro q _
  exact hweighted q

/-- The exact constructor vector is zero at every work coordinate whose
stored-row image lies in the completed prefix. -/
theorem sourceConstructedPivotedStoredQRExactRawVectorPerm_zero_of_masked
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n)
    (q : Fin m)
    (hq : (sourceConstructedPivotedStoredQRRowSwap fp hn hmn A k q).val < k) :
    sourceConstructedPivotedStoredQRExactRawVectorPerm fp hn hmn A k q = 0 := by
  let hm : 0 < m := lt_of_lt_of_le hn hmn
  let row := pivotedQRActiveRow hmn k hk
  let first : Fin m := ⟨0, hm⟩
  let S := sourceConstructedPivotedStoredQRRowSwap fp hn hmn A k
  let x := sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k
  have hS : S = Equiv.swap first row := by
    simp [S, sourceConstructedPivotedStoredQRRowSwap,
      sourceConstructedRowSwap, first, row, hk]
  have hqFirst : q ≠ first := by
    intro h
    subst q
    have hrowval : (S first).val = k := by
      rw [hS, Equiv.swap_apply_left]
      simp [row, pivotedQRActiveRow]
    rw [hrowval] at hq
    omega
  have hxq : x q = 0 := by
    simp only [x, sourceConstructedPivotedStoredQRActiveInput, dif_pos hk,
      sourceConstructedActiveInput]
    change sourceConstructedActivePanelPerm k S
      (sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k)
      q (pivotedQRActiveCol k hk) = 0
    change (if (S q).val < k then 0 else
      sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k
        (S q) (pivotedQRActiveCol k hk)) = 0
    rw [if_pos (by simpa [S] using hq)]
  rw [show sourceConstructedPivotedStoredQRExactRawVectorPerm fp hn hmn A k =
      householderVector hm x by rfl]
  rw [householderVector_tail hm x q hqFirst, hxq]

/-- The exact shadow in stored-row coordinates is precisely the pullback of
the exact constructor acting on the masked work panel. -/
theorem sourceConstructedPivotedStoredQRPseq_matMulVec_eq_work
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n)
    (i : Fin m) (hi : k ≤ i.val) (j : Fin n) :
    matMulVec m (sourceConstructedPivotedStoredQRPseq fp hn hmn A k)
        (fun r => sourceConstructedPivotedStoredQRSwappedPanel
          fp hn hmn A k r j) i =
      matMulVec m
        (householder m
          (sourceConstructedPivotedStoredQRExactRawVectorPerm fp hn hmn A k)
          (sourceConstructedPivotedStoredQRExactBeta fp hn hmn A k))
        (fun q => sourceConstructedPivotedStoredQRActivePanelPerm
          fp hn hmn A k q j)
        (sourceConstructedPivotedStoredQRRowSwap fp hn hmn A k i) := by
  let S := sourceConstructedPivotedStoredQRRowSwap fp hn hmn A k
  let v0 := sourceConstructedPivotedStoredQRExactRawVectorPerm fp hn hmn A k
  let beta := sourceConstructedPivotedStoredQRExactBeta fp hn hmn A k
  let b : Fin m → ℝ := fun r =>
    sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k r j
  let bp := vecPermute S b
  let c : Fin m → ℝ := fun q =>
    sourceConstructedPivotedStoredQRActivePanelPerm fp hn hmn A k q j
  have hSinv : ∀ q, S (S q) = q := by
    intro q
    simp [S, sourceConstructedPivotedStoredQRRowSwap,
      sourceConstructedRowSwap, hk]
  have hconj :
      matMulVec m (householder m (vecPermute S v0) beta) b i =
        matMulVec m (householder m v0 beta) bp (S i) :=
    matMulVec_householder_vecPermute_involution S v0 b beta hSinv i
  have hcoord : bp (S i) = c (S i) := by
    change b (S (S i)) =
      (if (S (S i)).val < k then 0 else b (S (S i)))
    rw [hSinv i]
    simp [Nat.not_lt.mpr hi]
  have hweighted : ∀ q, v0 q * bp q = v0 q * c q := by
    intro q
    by_cases hq : (S q).val < k
    · have hv0 : v0 q = 0 := by
        exact sourceConstructedPivotedStoredQRExactRawVectorPerm_zero_of_masked
          fp hn hmn A k hk q (by simpa [S] using hq)
      simp [hv0]
    · change v0 q * b (S q) =
        v0 q * (if (S q).val < k then 0 else b (S q))
      rw [if_neg hq]
  have hmask := matMulVec_householder_eq_of_coordinate_weighted_eq
    v0 bp c beta (S i) hcoord hweighted
  rw [show sourceConstructedPivotedStoredQRPseq fp hn hmn A k =
      householder m (vecPermute S v0) beta by
        simp [sourceConstructedPivotedStoredQRPseq,
          sourceConstructedPivotedStoredQRExactRawVector_eq_vecPermute,
          S, v0, beta],
    show (fun r => sourceConstructedPivotedStoredQRSwappedPanel
      fp hn hmn A k r j) = b by rfl]
  exact hconj.trans hmask

/-- Cox--Higham Lemma 2.2 for every genuinely updated trailing entry of the
actually rounded source trace.  Construction and application errors are
derived by the concrete repository theorem; the only numerical premises are
active-pivot nonbreakdown and the standard gamma-validity guard. -/
theorem sourceConstructedPivotedStoredQREseq_activeTrailing_abs_le
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (k : ℕ) (hk : k < n)
    (hsigma : 0 < sourceConstructedPivotedStoredQRSigma fp hn hmn A k)
    (i : Fin m) (hi : k ≤ i.val) (j : Fin n) (hj : k < j.val) :
    |sourceConstructedPivotedStoredQREseq fp hn hmn A k i j| ≤
      fp.u *
          |sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k i j| +
        gamma fp (11 * m + 23) * Real.sqrt 2 *
          |sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A k i| := by
  let hm : 0 < m := lt_of_lt_of_le hn hmn
  let S := sourceConstructedPivotedStoredQRRowSwap fp hn hmn A k
  let As := sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k
  let Ap := sourceConstructedPivotedStoredQRActivePanelPerm fp hn hmn A k
  let x := sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k
  let v0 := sourceConstructedPivotedStoredQRExactRawVectorPerm fp hn hmn A k
  let beta := sourceConstructedPivotedStoredQRExactBeta fp hn hmn A k
  let row := pivotedQRActiveRow hmn k hk
  let col := pivotedQRActiveCol k hk
  have hSdef : S = sourceConstructedRowSwap hm row := by
    simp [S, row, sourceConstructedPivotedStoredQRRowSwap, hk]
  have hApdef : Ap = sourceConstructedActivePanelPerm k S As := by
    change sourceConstructedActivePanelPerm k S As =
      sourceConstructedActivePanelPerm k S As
    rfl
  have hxdef : x = sourceConstructedActiveInput k S As col := by
    dsimp [x]
    rw [sourceConstructedPivotedStoredQRActiveInput, dif_pos hk]
  have hv0def : v0 = householderVector hm x := by
    rfl
  have hbetadef : beta = householderBetaFromScale hm x := by
    rfl
  have hx : x ≠ 0 := by
    exact sourceConstructedPivotedStoredQRActiveInput_ne_of_sigma_pos
      fp hn hmn A k hsigma
  have hpivot : vecNorm2 (fun q => Ap q j) ≤ vecNorm2 x := by
    exact sourceConstructedPivotedStoredQRActiveInput_pivot_max
      fp hn hmn A k hk j (Nat.le_of_lt hj)
  have hraw := fl_householderConstructApply_raw_entrywise_error
    fp hm x (fun q => Ap q j) hx hpivot hvalid (S i)
  have hnext := fl_sourceConstructedPivotedStoredQRMatrixSeq_succ_of_lt
    fp hn hmn A k hk
  have hwork := sourceConstructedPivotedStoredQRPseq_matMulVec_eq_work
    fp hn hmn A k hk i hi j
  have hSinv : S (S i) = i := by
    simp [S, sourceConstructedPivotedStoredQRRowSwap,
      sourceConstructedRowSwap, hk]
  have hWorkActive : ¬ (S (S i)).val < k := by
    rw [hSinv]
    exact Nat.not_lt.mpr hi
  have hAp : Ap (S i) j = As i j := by
    change (if (S (S i)).val < k then 0 else As (S (S i)) j) = As i j
    rw [if_neg hWorkActive, hSinv]
  have hv : v0 (S i) =
      sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A k i := by
    rfl
  rw [sourceConstructedPivotedStoredQREseq,
    congrFun (congrFun hnext i) j]
  change
    |fl_householderCoxHighamConstructedPanelStep fp hm k
          (pivotedQRActiveRow hmn k hk) (pivotedQRActiveCol k hk) As i j -
      matMulVec m (sourceConstructedPivotedStoredQRPseq fp hn hmn A k)
        (fun r => As r j) i| ≤ _
  rw [hwork]
  have hjPrev : ¬ j.val < k := by omega
  have hjPivot : ¬ j.val = k := by omega
  have hxDirect : sourceConstructedActiveInput k
      (sourceConstructedRowSwap hm (pivotedQRActiveRow hmn k hk)) As
        (pivotedQRActiveCol k hk) ≠ 0 := by
    change sourceConstructedActiveInput k
      (sourceConstructedRowSwap hm row) As col ≠ 0
    rw [← hSdef, ← hxdef]
    exact hx
  simp only [fl_householderCoxHighamConstructedPanelStep]
  rw [dif_neg hxDirect]
  simp only [hjPrev, if_false, Nat.not_lt.mpr hi, hjPivot]
  simp only [fl_householderApplyMatrixRect, matMulRect]
  rw [← hSdef, ← hApdef, ← hxdef]
  change
    |fl_householderApply fp m (fl_householderNormalizedVector fp hm x) 1
          (fun q => Ap q j) (S i) -
        matMulVec m (householder m v0 beta) (fun q => Ap q j) (S i)| ≤
      fp.u * |As i j| + gamma fp (11 * m + 23) * Real.sqrt 2 *
        |sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A k i|
  rw [← hv]
  rw [← hv0def, ← hbetadef, hAp] at hraw
  exact hraw

/-- Unconditional active-trailing form of Cox--Higham Lemma 2.2.  A zero
active pivot uses the guarded identity branch and has zero residual; a nonzero
pivot is discharged by the concrete rounded constructor/application theorem. -/
theorem sourceConstructedPivotedStoredQREseq_activeTrailing_abs_le_unconditional
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (k : ℕ) (hk : k < n)
    (i : Fin m) (hi : k ≤ i.val) (j : Fin n) (hj : k < j.val) :
    |sourceConstructedPivotedStoredQREseq fp hn hmn A k i j| ≤
      fp.u *
          |sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k i j| +
        gamma fp (11 * m + 23) * Real.sqrt 2 *
          |sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A k i| := by
  let x := sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k
  by_cases hx : x = 0
  · have hE := sourceConstructedPivotedStoredQREseq_eq_zero_of_input_eq_zero
      fp hn hmn A k hk (by simpa [x] using hx)
    rw [congrFun (congrFun hE i) j]
    simp only [Pi.zero_apply, abs_zero]
    exact add_nonneg
      (mul_nonneg fp.u_nonneg (abs_nonneg _))
      (mul_nonneg
        (mul_nonneg (gamma_nonneg fp hvalid) (Real.sqrt_nonneg 2))
        (abs_nonneg _))
  · have hnorm_ne : vecNorm2 x ≠ 0 := by
      intro hnorm
      apply hx
      funext q
      exact (vecNorm2_eq_zero_iff x).mp hnorm q
    have hsigma :
        0 < sourceConstructedPivotedStoredQRSigma fp hn hmn A k := by
      change 0 < vecNorm2 x
      exact lt_of_le_of_ne (vecNorm2_nonneg x) (Ne.symm hnorm_ne)
    exact sourceConstructedPivotedStoredQREseq_activeTrailing_abs_le
      fp hn hmn A hvalid k hk hsigma i hi j hj

end Theorem20_7

end NumStability
