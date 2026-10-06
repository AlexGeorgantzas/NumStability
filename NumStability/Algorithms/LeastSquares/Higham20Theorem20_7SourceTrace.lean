import NumStability.Algorithms.LeastSquares.Higham20Theorem20_7Contract

namespace NumStability

open scoped BigOperators

namespace Theorem20_7

/-!
# A source-stored Cox--Higham pivoted QR trace

The original literal Chapter 20 trace calls `fl_householderStoredPanelStep`.
That kernel zeros the eliminated tail, but it leaves the rounded compact
update on the pivot diagonal and also evaluates the compact update on rows
above the active row.  The source QR algorithm instead preserves the completed
rows and stores the signed Householder pivot on the diagonal.

This file supplies that source storage convention without changing the older
runtime trace.  The reflector application on the active trailing panel is
still the repository's explicit rounded compact dot/scale/subtract kernel.
The signed reflector data are named independently so later Cox--Higham local
operation estimates can be proved from the execution rather than supplied as
policy fields.
-/

/-- One source-stored panel step.  Completed columns and completed rows are
copied, the active pivot column stores `alpha` followed by exact zeros, and
only the genuinely active trailing rectangle uses the rounded compact update. -/
noncomputable def fl_householderCoxHighamStoredPanelStep
    (fp : FPModel) (m n k : ℕ) (alpha : ℝ)
    (v : Fin m → ℝ) (beta : ℝ) (A : Fin m → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  let raw := fl_householderApplyCompactPanel fp m n v beta A
  fun i j =>
    if j.val < k then
      A i j
    else if i.val < k then
      A i j
    else if j.val = k then
      if i.val = k then alpha else 0
    else
      raw i j

theorem fl_householderCoxHighamStoredPanelStep_prevColumn_eq
    (fp : FPModel) {m n k : ℕ} (alpha : ℝ)
    (v : Fin m → ℝ) (beta : ℝ) (A : Fin m → Fin n → ℝ)
    {i : Fin m} {j : Fin n} (hj : j.val < k) :
    fl_householderCoxHighamStoredPanelStep fp m n k alpha v beta A i j =
      A i j := by
  simp [fl_householderCoxHighamStoredPanelStep, hj]

theorem fl_householderCoxHighamStoredPanelStep_prevRow_eq
    (fp : FPModel) {m n k : ℕ} (alpha : ℝ)
    (v : Fin m → ℝ) (beta : ℝ) (A : Fin m → Fin n → ℝ)
    {i : Fin m} {j : Fin n} (hi : i.val < k) :
    fl_householderCoxHighamStoredPanelStep fp m n k alpha v beta A i j =
      A i j := by
  by_cases hj : j.val < k
  · simp [fl_householderCoxHighamStoredPanelStep, hj]
  · simp [fl_householderCoxHighamStoredPanelStep, hj, hi]

theorem fl_householderCoxHighamStoredPanelStep_pivot_eq
    (fp : FPModel) {m n k : ℕ} (alpha : ℝ)
    (v : Fin m → ℝ) (beta : ℝ) (A : Fin m → Fin n → ℝ)
    {i : Fin m} {j : Fin n} (hi : i.val = k) (hj : j.val = k) :
    fl_householderCoxHighamStoredPanelStep fp m n k alpha v beta A i j =
      alpha := by
  have hni : ¬ i.val < k := by omega
  have hnj : ¬ j.val < k := by omega
  simp [fl_householderCoxHighamStoredPanelStep, hni, hnj, hi, hj]

theorem fl_householderCoxHighamStoredPanelStep_pivotTail_eq_zero
    (fp : FPModel) {m n k : ℕ} (alpha : ℝ)
    (v : Fin m → ℝ) (beta : ℝ) (A : Fin m → Fin n → ℝ)
    {i : Fin m} {j : Fin n} (hi : k < i.val) (hj : j.val = k) :
    fl_householderCoxHighamStoredPanelStep fp m n k alpha v beta A i j =
      0 := by
  have hni : ¬ i.val < k := by omega
  have hnj : ¬ j.val < k := by omega
  have hine : ¬ i.val = k := by omega
  simp [fl_householderCoxHighamStoredPanelStep, hni, hnj, hine, hj]

/-! ## Executed active-max trace and named reflector data -/

/-- Full-shape source-stored column-pivoted Householder QR trace. -/
noncomputable def fl_sourcePivotedStoredQRMatrixSeq
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) : ℕ → Fin m → Fin n → ℝ
  | 0 => A
  | k + 1 =>
      if hk : k < n then
        let Aprev := fl_sourcePivotedStoredQRMatrixSeq fp hmn A k
        let row := pivotedQRActiveRow hmn k hk
        let col := pivotedQRActiveCol k hk
        let q := householderActiveMaxPivotColumn row col Aprev
        let S : Equiv.Perm (Fin n) := Equiv.swap col q
        let As := Wave13.columnPermuteMatrix Aprev S
        let x : Fin m → ℝ := fun i => As i col
        let alpha := signedHouseholderAlpha
          (Real.sqrt (householderTrailingNorm2Sq m row x)) (x row)
        let v := householderTrailingActiveVector m row x alpha
        let beta := householderBetaSpec m v
        fl_householderCoxHighamStoredPanelStep
          fp m n k alpha v beta As
      else
        fl_sourcePivotedStoredQRMatrixSeq fp hmn A k

/-- Executed active-max column swap for the source-stored trace. -/
noncomputable def sourcePivotedStoredQRSwapSeq
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) : Equiv.Perm (Fin n) :=
  if hk : k < n then
    let row := pivotedQRActiveRow hmn k hk
    let col := pivotedQRActiveCol k hk
    Equiv.swap col
      (householderActiveMaxPivotColumn row col
        (fl_sourcePivotedStoredQRMatrixSeq fp hmn A k))
  else
    Equiv.refl _

/-- Panel after the source trace's executed active-max column exchange. -/
noncomputable def sourcePivotedStoredQRSwappedPanel
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) : Fin m → Fin n → ℝ :=
  Wave13.columnPermuteMatrix
    (fl_sourcePivotedStoredQRMatrixSeq fp hmn A k)
    (sourcePivotedStoredQRSwapSeq fp hmn A k)

/-- Signed pivot stored by source stage `k`. -/
noncomputable def sourcePivotedStoredQRAlpha
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) : ℝ :=
  if hk : k < n then
    let row := pivotedQRActiveRow hmn k hk
    let col := pivotedQRActiveCol k hk
    let As := sourcePivotedStoredQRSwappedPanel fp hmn A k
    let x : Fin m → ℝ := fun i => As i col
    signedHouseholderAlpha
      (Real.sqrt (householderTrailingNorm2Sq m row x)) (x row)
  else
    0

/-- Raw signed Householder vector formed by source stage `k`. -/
noncomputable def sourcePivotedStoredQRRawVector
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) : Fin m → ℝ :=
  if hk : k < n then
    let row := pivotedQRActiveRow hmn k hk
    let col := pivotedQRActiveCol k hk
    let As := sourcePivotedStoredQRSwappedPanel fp hmn A k
    let x : Fin m → ℝ := fun i => As i col
    householderTrailingActiveVector m row x
      (sourcePivotedStoredQRAlpha fp hmn A k)
  else
    0

/-- Exact beta specification paired with the source stage's raw vector. -/
noncomputable def sourcePivotedStoredQRBeta
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) : ℝ :=
  householderBetaSpec m (sourcePivotedStoredQRRawVector fp hmn A k)

/-- Exact reflector paired with one source-stored rounded stage. -/
noncomputable def sourcePivotedStoredQRPseq
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) : Fin m → Fin m → ℝ :=
  householder m (sourcePivotedStoredQRRawVector fp hmn A k)
    (sourcePivotedStoredQRBeta fp hmn A k)

/-- Euclidean norm of the displayed active pivot column. -/
noncomputable def sourcePivotedStoredQRSigma
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) : ℝ :=
  if hk : k < n then
    Real.sqrt
      (householderTrailingColumnNorm2Sq
        (pivotedQRActiveRow hmn k hk)
        (sourcePivotedStoredQRSwappedPanel fp hmn A k)
        (pivotedQRActiveCol k hk))
  else
    0

theorem fl_sourcePivotedStoredQRMatrixSeq_succ_of_lt
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n) :
    fl_sourcePivotedStoredQRMatrixSeq fp hmn A (k + 1) =
      fl_householderCoxHighamStoredPanelStep fp m n k
        (sourcePivotedStoredQRAlpha fp hmn A k)
        (sourcePivotedStoredQRRawVector fp hmn A k)
        (sourcePivotedStoredQRBeta fp hmn A k)
        (sourcePivotedStoredQRSwappedPanel fp hmn A k) := by
  simp [fl_sourcePivotedStoredQRMatrixSeq,
    sourcePivotedStoredQRAlpha, sourcePivotedStoredQRRawVector,
    sourcePivotedStoredQRBeta, sourcePivotedStoredQRSwappedPanel,
    sourcePivotedStoredQRSwapSeq, hk]

theorem sourcePivotedStoredQRPseq_orthogonal
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) :
    IsOrthogonal m (sourcePivotedStoredQRPseq fp hmn A k) := by
  exact householder_betaSpec_orthogonal m
    (sourcePivotedStoredQRRawVector fp hmn A k)

/-- Executed source-trace swaps fix every completed column position. -/
theorem sourcePivotedStoredQRSwapSeq_fix_prefix
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (j : Fin n)
    (hj : j.val < k) :
    sourcePivotedStoredQRSwapSeq fp hmn A k j = j := by
  by_cases hk : k < n
  · let row := pivotedQRActiveRow hmn k hk
    let col := pivotedQRActiveCol k hk
    let q := householderActiveMaxPivotColumn row col
      (fl_sourcePivotedStoredQRMatrixSeq fp hmn A k)
    have hjc : j ≠ col := by
      intro h
      subst j
      exact Nat.lt_irrefl k hj
    have hqge : k ≤ q.val := by
      simpa [q, col] using householderActiveMaxPivotColumn_ge row col
        (fl_sourcePivotedStoredQRMatrixSeq fp hmn A k)
    have hjq : j ≠ q := by
      intro h
      subst j
      omega
    simp only [sourcePivotedStoredQRSwapSeq, dif_pos hk]
    exact Equiv.swap_apply_of_ne_of_ne hjc hjq
  · simp [sourcePivotedStoredQRSwapSeq, hk]

/-- Executed source-trace swaps map the active suffix into itself. -/
theorem sourcePivotedStoredQRSwapSeq_maps_active
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (j : Fin n)
    (hj : k ≤ j.val) :
    k ≤ (sourcePivotedStoredQRSwapSeq fp hmn A k j).val := by
  by_cases hk : k < n
  · let row := pivotedQRActiveRow hmn k hk
    let col := pivotedQRActiveCol k hk
    let q := householderActiveMaxPivotColumn row col
      (fl_sourcePivotedStoredQRMatrixSeq fp hmn A k)
    have hqge : k ≤ q.val := by
      simpa [q, col] using householderActiveMaxPivotColumn_ge row col
        (fl_sourcePivotedStoredQRMatrixSeq fp hmn A k)
    simp only [sourcePivotedStoredQRSwapSeq, dif_pos hk]
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
  · simp [sourcePivotedStoredQRSwapSeq, hk]
    exact hj

/-- The source trace's executed selector puts an active trailing-norm-maximal
column in the displayed pivot position. -/
theorem sourcePivotedStoredQRSwappedPanel_pivot_max
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n) :
    ∀ l : Fin n, k ≤ l.val →
      householderTrailingColumnNorm2Sq
          (pivotedQRActiveRow hmn k hk)
          (sourcePivotedStoredQRSwappedPanel fp hmn A k) l ≤
        householderTrailingColumnNorm2Sq
          (pivotedQRActiveRow hmn k hk)
          (sourcePivotedStoredQRSwappedPanel fp hmn A k)
          (pivotedQRActiveCol k hk) := by
  let Aprev := fl_sourcePivotedStoredQRMatrixSeq fp hmn A k
  let row := pivotedQRActiveRow hmn k hk
  let col := pivotedQRActiveCol k hk
  let q := householderActiveMaxPivotColumn row col Aprev
  have hswap : sourcePivotedStoredQRSwappedPanel fp hmn A k =
      householderSwapColumns Aprev col q := by
    unfold sourcePivotedStoredQRSwappedPanel
    have hS : sourcePivotedStoredQRSwapSeq fp hmn A k =
        Equiv.swap col q := by
      simp [sourcePivotedStoredQRSwapSeq, hk, row, col, q, Aprev]
    rw [hS]
    exact columnPermuteMatrix_swap_eq_householderSwapColumns Aprev col q
  rw [hswap]
  exact householderSwapColumns_activeMaxPivotColumn_pivot_max row col Aprev

theorem sourcePivotedStoredQRRawVector_zero_prefix
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n)
    (i : Fin m) (hi : i.val < k) :
    sourcePivotedStoredQRRawVector fp hmn A k i = 0 := by
  simp only [sourcePivotedStoredQRRawVector, dif_pos hk]
  exact householderTrailingActiveVector_zero_prefix m
    (pivotedQRActiveRow hmn k hk)
    (fun r => sourcePivotedStoredQRSwappedPanel fp hmn A k r
      (pivotedQRActiveCol k hk))
    (sourcePivotedStoredQRAlpha fp hmn A k) i hi

/-- Storage and prefix-fixing swaps preserve the completed lower zeros. -/
theorem fl_sourcePivotedStoredQRMatrixSeq_prefix_lower_zero
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) :
    ∀ k, k ≤ n → ∀ (i : Fin m) (j : Fin n),
      j.val < k → j.val < i.val →
        fl_sourcePivotedStoredQRMatrixSeq fp hmn A k i j = 0 := by
  intro k
  induction k with
  | zero =>
      intro _hk i j hj _hji
      exact (Nat.not_lt_zero j.val hj).elim
  | succ k ih =>
      intro hkSucc i j hjSucc hji
      have hk : k < n := Nat.lt_of_succ_le hkSucc
      have hstep :
          fl_sourcePivotedStoredQRMatrixSeq fp hmn A (k + 1) i j =
            fl_householderCoxHighamStoredPanelStep fp m n k
              (sourcePivotedStoredQRAlpha fp hmn A k)
              (sourcePivotedStoredQRRawVector fp hmn A k)
              (sourcePivotedStoredQRBeta fp hmn A k)
              (sourcePivotedStoredQRSwappedPanel fp hmn A k) i j := by
        exact congrFun (congrFun
          (fl_sourcePivotedStoredQRMatrixSeq_succ_of_lt
            fp hmn A k hk) i) j
      rcases Nat.lt_succ_iff_lt_or_eq.mp hjSucc with hj | hj
      · have hfix := sourcePivotedStoredQRSwapSeq_fix_prefix
          fp hmn A k j hj
        calc
          fl_sourcePivotedStoredQRMatrixSeq fp hmn A (k + 1) i j =
              fl_householderCoxHighamStoredPanelStep fp m n k
                (sourcePivotedStoredQRAlpha fp hmn A k)
                (sourcePivotedStoredQRRawVector fp hmn A k)
                (sourcePivotedStoredQRBeta fp hmn A k)
                (sourcePivotedStoredQRSwappedPanel fp hmn A k) i j := hstep
          _ = sourcePivotedStoredQRSwappedPanel fp hmn A k i j := by
            simp [fl_householderCoxHighamStoredPanelStep, hj]
          _ = fl_sourcePivotedStoredQRMatrixSeq fp hmn A k i j := by
            simp [sourcePivotedStoredQRSwappedPanel,
              Wave13.columnPermuteMatrix, hfix]
          _ = 0 := ih (Nat.le_of_lt hk) i j hj hji
      · let col : Fin n := ⟨k, hk⟩
        have hjfin : j = col := Fin.ext hj
        subst j
        have hki : k < i.val := by simpa [col] using hji
        rw [hstep]
        exact fl_householderCoxHighamStoredPanelStep_pivotTail_eq_zero
          fp (sourcePivotedStoredQRAlpha fp hmn A k)
            (sourcePivotedStoredQRRawVector fp hmn A k)
            (sourcePivotedStoredQRBeta fp hmn A k)
            (sourcePivotedStoredQRSwappedPanel fp hmn A k)
            hki (by simp [col])

/-- The final source-stored matrix is upper trapezoidal. -/
theorem fl_sourcePivotedStoredQRMatrixSeq_upperTrapezoidal
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) :
    IsUpperTrapezoidal m n
      (fl_sourcePivotedStoredQRMatrixSeq fp hmn A n) := by
  intro i j hji
  exact fl_sourcePivotedStoredQRMatrixSeq_prefix_lower_zero
    fp hmn A n le_rfl i j j.isLt hji

/-- Final leading square block of the source-stored trace. -/
noncomputable def sourcePivotedStoredQRTopR
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => fl_sourcePivotedStoredQRMatrixSeq fp hmn A n
    ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j

/-- The source-stored recursion records the signed pivot exactly at the next
stage's active diagonal position. -/
theorem fl_sourcePivotedStoredQRMatrixSeq_succ_pivot_eq_alpha
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n) :
    fl_sourcePivotedStoredQRMatrixSeq fp hmn A (k + 1)
        (pivotedQRActiveRow hmn k hk) (pivotedQRActiveCol k hk) =
      sourcePivotedStoredQRAlpha fp hmn A k := by
  rw [fl_sourcePivotedStoredQRMatrixSeq_succ_of_lt fp hmn A k hk]
  exact fl_householderCoxHighamStoredPanelStep_pivot_eq
    fp (sourcePivotedStoredQRAlpha fp hmn A k)
      (sourcePivotedStoredQRRawVector fp hmn A k)
      (sourcePivotedStoredQRBeta fp hmn A k)
      (sourcePivotedStoredQRSwappedPanel fp hmn A k)
      (by simp [pivotedQRActiveRow]) (by simp [pivotedQRActiveCol])

theorem sourcePivotedStoredQRAlpha_abs_eq_sigma
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n) :
    |sourcePivotedStoredQRAlpha fp hmn A k| =
      sourcePivotedStoredQRSigma fp hmn A k := by
  simp only [sourcePivotedStoredQRAlpha, sourcePivotedStoredQRSigma,
    dif_pos hk]
  rw [show householderTrailingColumnNorm2Sq
      (pivotedQRActiveRow hmn k hk)
      (sourcePivotedStoredQRSwappedPanel fp hmn A k)
      (pivotedQRActiveCol k hk) =
      householderTrailingNorm2Sq m (pivotedQRActiveRow hmn k hk)
        (fun i => sourcePivotedStoredQRSwappedPanel fp hmn A k i
          (pivotedQRActiveCol k hk)) by rfl]
  unfold signedHouseholderAlpha
  split_ifs <;> simp [Real.sqrt_nonneg]

/-! ## Same-reflector residual and explicit local arithmetic budget -/

/-- After the QR horizon the source-stored trace is held fixed. -/
theorem fl_sourcePivotedStoredQRMatrixSeq_succ_of_ge
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : n ≤ k) :
    fl_sourcePivotedStoredQRMatrixSeq fp hmn A (k + 1) =
      fl_sourcePivotedStoredQRMatrixSeq fp hmn A k := by
  simp [fl_sourcePivotedStoredQRMatrixSeq, Nat.not_lt.mpr hk]

/-- One source stage's exact same-reflector residual. -/
noncomputable def sourcePivotedStoredQREseq
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) : Fin m → Fin n → ℝ :=
  fun i j =>
    fl_sourcePivotedStoredQRMatrixSeq fp hmn A (k + 1) i j -
      matMulRect m m n (sourcePivotedStoredQRPseq fp hmn A k)
        (sourcePivotedStoredQRSwappedPanel fp hmn A k) i j

theorem sourcePivotedStoredQR_step_with_residual
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ)
    (i : Fin m) (j : Fin n) :
    fl_sourcePivotedStoredQRMatrixSeq fp hmn A (k + 1) i j =
      matMulRect m m n (sourcePivotedStoredQRPseq fp hmn A k)
          (Wave13.columnPermuteMatrix
            (fl_sourcePivotedStoredQRMatrixSeq fp hmn A k)
            (sourcePivotedStoredQRSwapSeq fp hmn A k)) i j +
        sourcePivotedStoredQREseq fp hmn A k i j := by
  simp only [sourcePivotedStoredQREseq,
    sourcePivotedStoredQRSwappedPanel]
  ring

/-- The exact source-stage reflector preserves a completed stored column. -/
theorem sourcePivotedStoredQRPseq_completed_column_preservation
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n)
    (j : Fin n) (hj : j.val < k) :
    matMulVec m (sourcePivotedStoredQRPseq fp hmn A k)
        (fun r => sourcePivotedStoredQRSwappedPanel fp hmn A k r j) =
      fun r => fl_sourcePivotedStoredQRMatrixSeq fp hmn A k r j := by
  let v := sourcePivotedStoredQRRawVector fp hmn A k
  let beta := sourcePivotedStoredQRBeta fp hmn A k
  let xcol : Fin m → ℝ :=
    fun r => sourcePivotedStoredQRSwappedPanel fp hmn A k r j
  have hfix := sourcePivotedStoredQRSwapSeq_fix_prefix fp hmn A k j hj
  have hxcol : xcol =
      fun r => fl_sourcePivotedStoredQRMatrixSeq fp hmn A k r j := by
    funext r
    simp [xcol, sourcePivotedStoredQRSwappedPanel,
      Wave13.columnPermuteMatrix, hfix]
  have hvprefix : ∀ r : Fin m, r.val < k → v r = 0 := by
    intro r hr
    exact sourcePivotedStoredQRRawVector_zero_prefix
      fp hmn A k hk r hr
  have hsupport : ∀ r : Fin m, k ≤ r.val → xcol r = 0 := by
    intro r hr
    rw [hxcol]
    exact fl_sourcePivotedStoredQRMatrixSeq_prefix_lower_zero
      fp hmn A k (Nat.le_of_lt hk) r j hj (lt_of_lt_of_le hj hr)
  have hpres := matMulVec_householder_eq_self_of_zero_prefix_support
    m k v xcol beta hvprefix hsupport
  simpa [sourcePivotedStoredQRPseq, v, beta, xcol, hxcol] using hpres

/-- At a positive executed pivot, the exact reflector paired with the source
trace maps the displayed pivot column to the stored prefix/pivot/zero shape. -/
theorem sourcePivotedStoredQRPseq_pivot_column_shape
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n)
    (hsigma : 0 < |sourcePivotedStoredQRSigma fp hmn A k|)
    (i : Fin m) :
    matMulVec m (sourcePivotedStoredQRPseq fp hmn A k)
        (fun r => sourcePivotedStoredQRSwappedPanel fp hmn A k r
          (pivotedQRActiveCol k hk)) i =
      if i.val < k then
        sourcePivotedStoredQRSwappedPanel fp hmn A k i
          (pivotedQRActiveCol k hk)
      else if i = pivotedQRActiveRow hmn k hk then
        sourcePivotedStoredQRAlpha fp hmn A k
      else 0 := by
  let row := pivotedQRActiveRow hmn k hk
  let col := pivotedQRActiveCol k hk
  let As := sourcePivotedStoredQRSwappedPanel fp hmn A k
  let x : Fin m → ℝ := fun r => As r col
  let T := householderTrailingNorm2Sq m row x
  let alpha := signedHouseholderAlpha (Real.sqrt T) (x row)
  let v := householderTrailingActiveVector m row x alpha
  have hsigmaEq : sourcePivotedStoredQRSigma fp hmn A k =
      Real.sqrt T := by
    simp [sourcePivotedStoredQRSigma, hk, T, row, col, As, x,
      householderTrailingColumnNorm2Sq]
  have hsqrtPos : 0 < Real.sqrt T := by
    rw [hsigmaEq, abs_of_nonneg (Real.sqrt_nonneg _)] at hsigma
    exact hsigma
  have hTpos : 0 < T := Real.sqrt_pos.mp hsqrtPos
  have halpha : alpha * alpha = T := by
    simpa [alpha, T] using
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq m row x
  have hsign : alpha * x row ≤ 0 := by
    simpa [alpha, T] using
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos m row x
  have hpivotNe : x row ≠ alpha :=
    householder_pivot_ne_alpha_of_trailingNorm2Sq_pos_mul_nonpos
      m row x alpha halpha hTpos hsign
  have hden : (∑ r : Fin m, v r * v r) ≠ 0 := by
    simpa [v] using
      householderTrailingActiveVector_inner_self_ne_zero_of_pivot_ne_alpha
        m row x alpha hpivotNe
  have hshape :=
    matMulVec_householder_trailingActiveVector_eq_prefix_alpha_zero
      m row x alpha halpha hden i
  have halphaEq : sourcePivotedStoredQRAlpha fp hmn A k = alpha := by
    simp [sourcePivotedStoredQRAlpha, hk, alpha, T, row, col, As, x]
  have hvEq : sourcePivotedStoredQRRawVector fp hmn A k = v := by
    simp [sourcePivotedStoredQRRawVector, hk, halphaEq, v, row, col, As, x]
  simpa [sourcePivotedStoredQRPseq, sourcePivotedStoredQRBeta,
    hvEq, row, col, As, x, alpha, halphaEq, pivotedQRActiveRow] using hshape

/-- The explicit local compact-operation budget for a source-stored matrix
stage.  Copied entries and the exactly stored pivot column have zero budget. -/
noncomputable def sourcePivotedStoredQRComponentBudget
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ)
    (i : Fin m) (j : Fin n) : ℝ :=
  if j.val < k then 0
  else if i.val < k then 0
  else if j.val = k then 0
  else householderCompactComponentBudget fp m
    (sourcePivotedStoredQRRawVector fp hmn A k)
    (sourcePivotedStoredQRBeta fp hmn A k)
    (fun r => sourcePivotedStoredQRSwappedPanel fp hmn A k r j) i

theorem sourcePivotedStoredQRComponentBudget_nonneg
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (hm : gammaValid fp m)
    (k : ℕ) (i : Fin m) (j : Fin n) :
    0 ≤ sourcePivotedStoredQRComponentBudget fp hmn A k i j := by
  unfold sourcePivotedStoredQRComponentBudget
  split_ifs
  · rfl
  · rfl
  · rfl
  · exact householderCompactComponentBudget_nonneg fp m
      (sourcePivotedStoredQRRawVector fp hmn A k)
      (sourcePivotedStoredQRBeta fp hmn A k)
      (fun r => sourcePivotedStoredQRSwappedPanel fp hmn A k r j) hm i

/-- The actual source-stored stage residual is bounded by its explicit local
compact arithmetic budget. -/
theorem sourcePivotedStoredQREseq_abs_le_componentBudget
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (hm : gammaValid fp m)
    (k : ℕ) (hk : k < n)
    (hsigma : 0 < |sourcePivotedStoredQRSigma fp hmn A k|)
    (i : Fin m) (j : Fin n) :
    |sourcePivotedStoredQREseq fp hmn A k i j| ≤
      sourcePivotedStoredQRComponentBudget fp hmn A k i j := by
  let v := sourcePivotedStoredQRRawVector fp hmn A k
  let beta := sourcePivotedStoredQRBeta fp hmn A k
  let As := sourcePivotedStoredQRSwappedPanel fp hmn A k
  have hnext :
      fl_sourcePivotedStoredQRMatrixSeq fp hmn A (k + 1) =
        fl_householderCoxHighamStoredPanelStep fp m n k
          (sourcePivotedStoredQRAlpha fp hmn A k) v beta As := by
    simpa [v, beta, As] using
      fl_sourcePivotedStoredQRMatrixSeq_succ_of_lt fp hmn A k hk
  by_cases hjPrev : j.val < k
  · have hpres0 := congrFun
      (sourcePivotedStoredQRPseq_completed_column_preservation
        fp hmn A k hk j hjPrev) i
    have hfix := sourcePivotedStoredQRSwapSeq_fix_prefix
      fp hmn A k j hjPrev
    have hAs : As i j =
        fl_sourcePivotedStoredQRMatrixSeq fp hmn A k i j := by
      simp [As, sourcePivotedStoredQRSwappedPanel,
        Wave13.columnPermuteMatrix, hfix]
    have hpres : matMulVec m (sourcePivotedStoredQRPseq fp hmn A k)
        (fun r => As r j) i = As i j := by
      rw [hAs]
      simpa [As] using hpres0
    rw [sourcePivotedStoredQREseq, congrFun (congrFun hnext i) j]
    change
      |fl_householderCoxHighamStoredPanelStep fp m n k
          (sourcePivotedStoredQRAlpha fp hmn A k) v beta As i j -
        matMulVec m (sourcePivotedStoredQRPseq fp hmn A k)
          (fun r => As r j) i| ≤
        sourcePivotedStoredQRComponentBudget fp hmn A k i j
    rw [fl_householderCoxHighamStoredPanelStep_prevColumn_eq
      fp (sourcePivotedStoredQRAlpha fp hmn A k) v beta As hjPrev,
      hpres]
    simp [sourcePivotedStoredQRComponentBudget, hjPrev]
  · by_cases hiPrev : i.val < k
    · have hvzero : v i = 0 := by
        exact sourcePivotedStoredQRRawVector_zero_prefix
          fp hmn A k hk i hiPrev
      have hpres : matMulVec m (householder m v beta)
          (fun r => As r j) i = As i j := by
        rw [householder_matMulVec_eq]
        simp [hvzero]
      rw [sourcePivotedStoredQREseq, congrFun (congrFun hnext i) j]
      change
        |fl_householderCoxHighamStoredPanelStep fp m n k
            (sourcePivotedStoredQRAlpha fp hmn A k) v beta As i j -
          matMulVec m (householder m v beta) (fun r => As r j) i| ≤
          sourcePivotedStoredQRComponentBudget fp hmn A k i j
      rw [fl_householderCoxHighamStoredPanelStep_prevRow_eq
        fp (sourcePivotedStoredQRAlpha fp hmn A k) v beta As hiPrev,
        hpres]
      simp [sourcePivotedStoredQRComponentBudget, hjPrev, hiPrev]
    · by_cases hjPivot : j.val = k
      · have hjEq : j = pivotedQRActiveCol k hk := Fin.ext hjPivot
        subst j
        have hshape := sourcePivotedStoredQRPseq_pivot_column_shape
          fp hmn A k hk hsigma i
        rw [sourcePivotedStoredQREseq, congrFun
          (congrFun hnext i) (pivotedQRActiveCol k hk)]
        change
          |fl_householderCoxHighamStoredPanelStep fp m n k
              (sourcePivotedStoredQRAlpha fp hmn A k) v beta As i
                (pivotedQRActiveCol k hk) -
            matMulVec m (sourcePivotedStoredQRPseq fp hmn A k)
              (fun r => As r (pivotedQRActiveCol k hk)) i| ≤
            sourcePivotedStoredQRComponentBudget fp hmn A k i
              (pivotedQRActiveCol k hk)
        by_cases hiPivot : i.val = k
        · have hiEq : i = pivotedQRActiveRow hmn k hk := by
            apply Fin.ext
            simpa [pivotedQRActiveRow] using hiPivot
          subst i
          have hshape' :
              matMulVec m (sourcePivotedStoredQRPseq fp hmn A k)
                  (fun r => As r (pivotedQRActiveCol k hk))
                  (pivotedQRActiveRow hmn k hk) =
                sourcePivotedStoredQRAlpha fp hmn A k := by
            simpa [As, pivotedQRActiveRow] using hshape
          rw [fl_householderCoxHighamStoredPanelStep_pivot_eq
            fp (sourcePivotedStoredQRAlpha fp hmn A k) v beta As
              (by simp [pivotedQRActiveRow])
              (by simp [pivotedQRActiveCol]), hshape']
          simp [sourcePivotedStoredQRComponentBudget,
            pivotedQRActiveRow, pivotedQRActiveCol]
        · have hki : k < i.val := by omega
          have hiNe : i ≠ pivotedQRActiveRow hmn k hk := by
            intro h
            subst i
            simp [pivotedQRActiveRow] at hiPivot
          have hshape' :
              matMulVec m (sourcePivotedStoredQRPseq fp hmn A k)
                  (fun r => As r (pivotedQRActiveCol k hk)) i = 0 := by
            simpa [As, hiPrev, hiNe] using hshape
          rw [fl_householderCoxHighamStoredPanelStep_pivotTail_eq_zero
            fp (sourcePivotedStoredQRAlpha fp hmn A k) v beta As hki
              (by simp [pivotedQRActiveCol]), hshape']
          simp [sourcePivotedStoredQRComponentBudget,
            pivotedQRActiveCol]
      · have hraw := fl_householderApplyCompact_componentwise_error_bound
          fp m v beta (fun r => As r j) hm i
        rw [sourcePivotedStoredQREseq, congrFun (congrFun hnext i) j]
        change
          |fl_householderCoxHighamStoredPanelStep fp m n k
              (sourcePivotedStoredQRAlpha fp hmn A k) v beta As i j -
            matMulVec m (householder m v beta) (fun r => As r j) i| ≤
            sourcePivotedStoredQRComponentBudget fp hmn A k i j
        simpa [fl_householderCoxHighamStoredPanelStep, hjPrev, hiPrev,
          hjPivot, sourcePivotedStoredQRComponentBudget, v, beta, As]
          using hraw

/-- Norm form of the source matrix component-budget bound. -/
theorem sourcePivotedStoredQREseq_norm_le_componentBudget
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (hm : gammaValid fp m)
    (k : ℕ) (hk : k < n)
    (hsigma : 0 < |sourcePivotedStoredQRSigma fp hmn A k|)
    (j : Fin n) :
    vecNorm2 (fun i => sourcePivotedStoredQREseq fp hmn A k i j) ≤
      vecNorm2 (fun i =>
        sourcePivotedStoredQRComponentBudget fp hmn A k i j) := by
  apply vecNorm2_le_of_abs_le
  intro i
  exact sourcePivotedStoredQREseq_abs_le_componentBudget
    fp hmn A hm k hk hsigma i j

/-! ## Printed alpha scale and its premise-free raw-vector producer -/

/-- Literal printed numerator `max_{j,t} |a_ij^(t)|` for the source-stored
trace.  In particular, the recorded states include every signed pivot. -/
noncomputable def sourcePivotedStoredQRPrintedAlphaScale
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (i : Fin m) : ℝ :=
  Wave18D.rowInftyGrowthFactor
    (fl_sourcePivotedStoredQRMatrixSeq fp hmn A) n i

theorem sourcePivotedStoredQRPrintedAlphaScale_nonneg
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (i : Fin m) :
    0 ≤ sourcePivotedStoredQRPrintedAlphaScale fp hmn A i := by
  let j0 : Fin n := ⟨0, hn⟩
  exact Wave18D.rowInftyGrowthFactor_nonneg
    (fl_sourcePivotedStoredQRMatrixSeq fp hmn A) n i j0

theorem sourcePivotedStoredQRSwappedPanel_abs_le_printedAlphaScale
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n)
    (i : Fin m) (j : Fin n) :
    |sourcePivotedStoredQRSwappedPanel fp hmn A k i j| ≤
      sourcePivotedStoredQRPrintedAlphaScale fp hmn A i := by
  simpa [sourcePivotedStoredQRSwappedPanel,
    sourcePivotedStoredQRPrintedAlphaScale, Wave13.columnPermuteMatrix] using
    (Wave18D.abs_entry_le_rowInftyGrowthFactor
      (fl_sourcePivotedStoredQRMatrixSeq fp hmn A) n i k
      (Nat.le_of_lt hk) (sourcePivotedStoredQRSwapSeq fp hmn A k j))

theorem sourcePivotedStoredQRAlpha_abs_le_printedAlphaScale
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n) :
    |sourcePivotedStoredQRAlpha fp hmn A k| ≤
      sourcePivotedStoredQRPrintedAlphaScale fp hmn A
        (pivotedQRActiveRow hmn k hk) := by
  have h := Wave18D.abs_entry_le_rowInftyGrowthFactor
    (fl_sourcePivotedStoredQRMatrixSeq fp hmn A) n
    (pivotedQRActiveRow hmn k hk) (k + 1)
    (Nat.succ_le_iff.mpr hk) (pivotedQRActiveCol k hk)
  rw [fl_sourcePivotedStoredQRMatrixSeq_succ_pivot_eq_alpha
    fp hmn A k hk] at h
  simpa [sourcePivotedStoredQRPrintedAlphaScale] using h

/-- Source equation (2.10), produced directly from the executed stored trace.
The pivot row uses the two recorded quantities `x_k` and `alpha_k`; active
off-pivot rows are copied entries of the swapped current panel; prefix rows
are zero.  No row-policy or backward-error premise occurs. -/
theorem sourcePivotedStoredQRRawVector_abs_le_two_printedAlphaScale
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n)
    (i : Fin m) :
    |sourcePivotedStoredQRRawVector fp hmn A k i| ≤
      2 * sourcePivotedStoredQRPrintedAlphaScale fp hmn A i := by
  let row := pivotedQRActiveRow hmn k hk
  let col := pivotedQRActiveCol k hk
  let As := sourcePivotedStoredQRSwappedPanel fp hmn A k
  let alpha := sourcePivotedStoredQRAlpha fp hmn A k
  have hscale : 0 ≤ sourcePivotedStoredQRPrintedAlphaScale fp hmn A i :=
    sourcePivotedStoredQRPrintedAlphaScale_nonneg fp hn hmn A i
  by_cases hiPrefix : i.val < k
  · rw [sourcePivotedStoredQRRawVector_zero_prefix
      fp hmn A k hk i hiPrefix, abs_zero]
    positivity
  · by_cases hiPivot : i.val = k
    · have hirow : i = row := by
        apply Fin.ext
        simpa [row, pivotedQRActiveRow] using hiPivot
      subst i
      have hv : sourcePivotedStoredQRRawVector fp hmn A k row =
          As row col - alpha := by
        simp [sourcePivotedStoredQRRawVector, hk, row, col, As, alpha,
          householderTrailingActiveVector, householderActiveVector,
          householderTrailingPart, pivotedQRActiveRow]
      have hx := sourcePivotedStoredQRSwappedPanel_abs_le_printedAlphaScale
        fp hmn A k hk row col
      have ha := sourcePivotedStoredQRAlpha_abs_le_printedAlphaScale
        fp hmn A k hk
      rw [hv]
      calc
        |As row col - alpha| ≤ |As row col| + |alpha| := abs_sub _ _
        _ ≤ sourcePivotedStoredQRPrintedAlphaScale fp hmn A row +
            sourcePivotedStoredQRPrintedAlphaScale fp hmn A row :=
          add_le_add hx ha
        _ = 2 * sourcePivotedStoredQRPrintedAlphaScale fp hmn A row := by
          ring
    · have hki : k < i.val := by omega
      have hir : i ≠ row := by
        intro hir
        subst i
        simp [row, pivotedQRActiveRow] at hiPivot
      have hirowNot : ¬ i.val < row.val := by
        simp [row, pivotedQRActiveRow]
        omega
      have hir' : i ≠ pivotedQRActiveRow hmn k hk := by
        simpa [row] using hir
      have hirowNot' :
          ¬ i.val < (pivotedQRActiveRow hmn k hk).val := by
        simpa [row] using hirowNot
      have hv : sourcePivotedStoredQRRawVector fp hmn A k i =
          As i col := by
        simp [sourcePivotedStoredQRRawVector, hk, row, col, As, alpha,
          householderTrailingActiveVector, householderActiveVector,
          householderTrailingPart, hirowNot', hir']
      have hx := sourcePivotedStoredQRSwappedPanel_abs_le_printedAlphaScale
        fp hmn A k hk i col
      rw [hv]
      exact hx.trans (by linarith)

/-- Local Cox--Higham sign bound for the source trace's executed raw vector. -/
theorem sourcePivotedStoredQRRawVector_sigma_sign_bound
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n) :
    Real.sqrt 2 * |sourcePivotedStoredQRSigma fp hmn A k| ≤
      vecNorm2 (sourcePivotedStoredQRRawVector fp hmn A k) := by
  let row := pivotedQRActiveRow hmn k hk
  let col := pivotedQRActiveCol k hk
  let As := sourcePivotedStoredQRSwappedPanel fp hmn A k
  let x : Fin m → ℝ := fun i => As i col
  let T := householderTrailingNorm2Sq m row x
  let alpha := signedHouseholderAlpha (Real.sqrt T) (x row)
  let v := householderTrailingActiveVector m row x alpha
  have hT : 0 ≤ T := householderTrailingNorm2Sq_nonneg m row x
  have hraw : 2 * T ≤ ∑ i : Fin m, v i * v i := by
    simpa [T, v] using
      householderTrailingActiveVector_inner_self_ge_two_trailingNorm2Sq_signed
        m row x
  have hsigma : sourcePivotedStoredQRSigma fp hmn A k = Real.sqrt T := by
    simp [sourcePivotedStoredQRSigma, hk, T, row, col, As, x,
      householderTrailingColumnNorm2Sq]
  have halpha : sourcePivotedStoredQRAlpha fp hmn A k = alpha := by
    simp [sourcePivotedStoredQRAlpha, hk, alpha, T, row, col, As, x]
  have hv : sourcePivotedStoredQRRawVector fp hmn A k = v := by
    simp [sourcePivotedStoredQRRawVector, hk, halpha, v, row, col, As, x]
  rw [hsigma, abs_of_nonneg (Real.sqrt_nonneg _), hv]
  apply (sq_le_sq₀
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (vecNorm2_nonneg v)).mp
  calc
    (Real.sqrt 2 * Real.sqrt T) ^ 2 = 2 * T := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        Real.sq_sqrt hT]
    _ ≤ ∑ i : Fin m, v i * v i := hraw
    _ = vecNorm2 v ^ 2 := by
      rw [vecNorm2_sq]
      simp [vecNorm2Sq, pow_two]

/-- Once the Ch19 pivot history supplies the source cross-stage raw-norm
ratio, the executed reflector-prefix row estimate is produced from the
premise-free raw-vector bridge above.  This is the adapter point for the
Chapter 19.6 `StageDataReady` producer. -/
theorem sourcePivotedStoredQRRawVector_prefix_entrywise_le_of_normRatio
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hsigma : ∀ k, k < n →
      0 < |sourcePivotedStoredQRSigma fp hmn A k|)
    (hratio : ∀ k, k < n → ∀ q, q < k →
      vecNorm2 (sourcePivotedStoredQRRawVector fp hmn A k) /
          vecNorm2 (sourcePivotedStoredQRRawVector fp hmn A q) ≤ 2)
    (k : ℕ) (hk : k < n) (i : Fin m) :
    |Wave19.applyProd
        (fun q => householder m
          (sourcePivotedStoredQRRawVector fp hmn A q)
          (sourcePivotedStoredQRBeta fp hmn A q)) 0 k
        (sourcePivotedStoredQRRawVector fp hmn A k) i| ≤
      (1 + 4 * (k : ℝ)) * 2 *
        sourcePivotedStoredQRPrintedAlphaScale fp hmn A i := by
  apply applyProd_rawHouseholder_entrywise_le
    (fun q => sourcePivotedStoredQRRawVector fp hmn A q)
    (fun q => sourcePivotedStoredQRBeta fp hmn A q)
    (sourcePivotedStoredQRRawVector fp hmn A k)
    (sourcePivotedStoredQRPrintedAlphaScale fp hmn A) 2 k i
    (by norm_num)
    (sourcePivotedStoredQRPrintedAlphaScale_nonneg fp hn hmn A)
    (fun q => sourcePivotedStoredQRPseq_orthogonal fp hmn A q)
  · intro q hq
    have hqn : q < n := lt_trans hq hk
    have hlower := sourcePivotedStoredQRRawVector_sigma_sign_bound
      fp hmn A q hqn
    have hscale : 0 < Real.sqrt 2 *
        |sourcePivotedStoredQRSigma fp hmn A q| :=
      mul_pos (Real.sqrt_pos.mpr (by norm_num)) (hsigma q hqn)
    linarith
  · intro q hq
    apply householderBetaSpec_mul_vecNorm2_sq_eq_two_of_pos
    have hqn : q < n := lt_trans hq hk
    have hlower := sourcePivotedStoredQRRawVector_sigma_sign_bound
      fp hmn A q hqn
    have hscale : 0 < Real.sqrt 2 *
        |sourcePivotedStoredQRSigma fp hmn A q| :=
      mul_pos (Real.sqrt_pos.mpr (by norm_num)) (hsigma q hqn)
    linarith
  · intro q hq r
    exact sourcePivotedStoredQRRawVector_abs_le_two_printedAlphaScale
      fp hn hmn A q (lt_trans hq hk) r
  · intro q hq
    exact hratio k hk q hq
  · exact sourcePivotedStoredQRRawVector_abs_le_two_printedAlphaScale
      fp hn hmn A k hk i

/-! ## Paired rounded right-hand-side trace and printed beta data -/

noncomputable def fl_sourcePivotedStoredQRRhsSeq
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    ℕ → Fin m → ℝ
  | 0 => b
  | k + 1 =>
      if _hk : k < n then
        fl_householderStoredRhsStep fp m k
          (sourcePivotedStoredQRRawVector fp hmn A k)
          (sourcePivotedStoredQRBeta fp hmn A k)
          (fl_sourcePivotedStoredQRRhsSeq fp hmn A b k)
      else
        fl_sourcePivotedStoredQRRhsSeq fp hmn A b k

@[simp] theorem fl_sourcePivotedStoredQRRhsSeq_zero
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    fl_sourcePivotedStoredQRRhsSeq fp hmn A b 0 = b := rfl

theorem fl_sourcePivotedStoredQRRhsSeq_succ_of_lt
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (k : ℕ) (hk : k < n) :
    fl_sourcePivotedStoredQRRhsSeq fp hmn A b (k + 1) =
      fl_householderStoredRhsStep fp m k
        (sourcePivotedStoredQRRawVector fp hmn A k)
        (sourcePivotedStoredQRBeta fp hmn A k)
        (fl_sourcePivotedStoredQRRhsSeq fp hmn A b k) := by
  simp [fl_sourcePivotedStoredQRRhsSeq, hk]

noncomputable def sourcePivotedStoredQRRhsEseq
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (k : ℕ) : Fin m → ℝ :=
  fun i => fl_sourcePivotedStoredQRRhsSeq fp hmn A b (k + 1) i -
    matMulVec m (sourcePivotedStoredQRPseq fp hmn A k)
      (fl_sourcePivotedStoredQRRhsSeq fp hmn A b k) i

noncomputable def sourcePivotedStoredQRRhsComponentBudget
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (k : ℕ) (i : Fin m) : ℝ :=
  if i.val < k then 0
  else householderCompactComponentBudget fp m
    (sourcePivotedStoredQRRawVector fp hmn A k)
    (sourcePivotedStoredQRBeta fp hmn A k)
    (fl_sourcePivotedStoredQRRhsSeq fp hmn A b k) i

theorem sourcePivotedStoredQRRhsComponentBudget_nonneg
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hm : gammaValid fp m) (k : ℕ) (i : Fin m) :
    0 ≤ sourcePivotedStoredQRRhsComponentBudget fp hmn A b k i := by
  by_cases hi : i.val < k
  · simp [sourcePivotedStoredQRRhsComponentBudget, hi]
  · simp only [sourcePivotedStoredQRRhsComponentBudget, if_neg hi]
    exact householderCompactComponentBudget_nonneg fp m
      (sourcePivotedStoredQRRawVector fp hmn A k)
      (sourcePivotedStoredQRBeta fp hmn A k)
      (fl_sourcePivotedStoredQRRhsSeq fp hmn A b k) hm i

theorem sourcePivotedStoredQRRhsEseq_abs_le_componentBudget
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hm : gammaValid fp m) (k : ℕ) (hk : k < n) (i : Fin m) :
    |sourcePivotedStoredQRRhsEseq fp hmn A b k i| ≤
      sourcePivotedStoredQRRhsComponentBudget fp hmn A b k i := by
  let v := sourcePivotedStoredQRRawVector fp hmn A k
  let beta := sourcePivotedStoredQRBeta fp hmn A k
  let bk := fl_sourcePivotedStoredQRRhsSeq fp hmn A b k
  have hprefix : ∀ r : Fin m, r.val < k →
      matMulVec m (householder m v beta) bk r = bk r := by
    intro r hr
    have hvzero : v r = 0 :=
      sourcePivotedStoredQRRawVector_zero_prefix fp hmn A k hk r hr
    rw [householder_matMulVec_eq]
    simp [hvzero]
  have hbound := fl_householderStoredRhsStep_componentwise_error_bound
    fp m k v beta bk hm hprefix i
  rw [sourcePivotedStoredQRRhsEseq,
    fl_sourcePivotedStoredQRRhsSeq_succ_of_lt fp hmn A b k hk]
  simpa [sourcePivotedStoredQRRhsComponentBudget,
    sourcePivotedStoredQRPseq, v, beta, bk] using hbound

theorem sourcePivotedStoredQRRhsEseq_norm_le_componentBudget
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hm : gammaValid fp m) (k : ℕ) (hk : k < n) :
    vecNorm2 (sourcePivotedStoredQRRhsEseq fp hmn A b k) ≤
      vecNorm2 (fun i =>
        sourcePivotedStoredQRRhsComponentBudget fp hmn A b k i) := by
  apply vecNorm2_le_of_abs_le
  intro i
  exact sourcePivotedStoredQRRhsEseq_abs_le_componentBudget
    fp hmn A b hm k hk i

/-- Printed RHS history numerator `max_t |b_i^(t)|`. -/
noncomputable def sourcePivotedStoredQRRhsRowGrowthScale
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (i : Fin m) : ℝ :=
  ⨆ t : Fin (n + 1),
    |fl_sourcePivotedStoredQRRhsSeq fp hmn A b t.val i|

/-- Printed common-reflector tail ratio. -/
noncomputable def sourcePivotedStoredQRPrintedPhi
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) : ℝ :=
  ⨆ k : Fin n,
    vecNorm2
        (householderTrailingPart m (pivotedQRActiveRow hmn k.val k.isLt)
          (fl_sourcePivotedStoredQRRhsSeq fp hmn A b k.val)) /
      |sourcePivotedStoredQRSigma fp hmn A k.val|

/-- Printed beta numerator for the source-stored trace. -/
noncomputable def sourcePivotedStoredQRPrintedBetaScale
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (i : Fin m) : ℝ :=
  max
    (sourcePivotedStoredQRPrintedPhi fp hmn A b *
      sourcePivotedStoredQRPrintedAlphaScale fp hmn A i)
    (sourcePivotedStoredQRRhsRowGrowthScale fp hmn A b i)

theorem sourcePivotedStoredQRRhsRowGrowthScale_nonneg
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (i : Fin m) :
    0 ≤ sourcePivotedStoredQRRhsRowGrowthScale fp hmn A b i := by
  have h0 : 0 ≤ |fl_sourcePivotedStoredQRRhsSeq fp hmn A b 0 i| :=
    abs_nonneg _
  exact h0.trans (le_ciSup
    (Finite.bddAbove_range (fun t : Fin (n + 1) =>
      |fl_sourcePivotedStoredQRRhsSeq fp hmn A b t.val i|))
    (0 : Fin (n + 1)))

theorem sourcePivotedStoredQRPrintedBetaScale_nonneg
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (i : Fin m) :
    0 ≤ sourcePivotedStoredQRPrintedBetaScale fp hmn A b i := by
  apply le_max_of_le_right
  exact sourcePivotedStoredQRRhsRowGrowthScale_nonneg fp hmn A b i

/-- Leading transformed RHS paired with `sourcePivotedStoredQRTopR`. -/
noncomputable def sourcePivotedStoredQRTopRhs
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) : Fin n → ℝ :=
  fun i => fl_sourcePivotedStoredQRRhsSeq fp hmn A b n
    ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩

end Theorem20_7

end NumStability
