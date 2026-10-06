import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication
import NumStability.Algorithms.LinearSystems.QR.Householder.StoredQR
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.DiagonalDominance
import NumStability.Algorithms.LinearSystems.Triangular.InverseBounds
import NumStability.Analysis.MatrixAlgebra
import NumStability.FloatingPoint.Model

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-!
# StoredQR

Canonical reusable module extracted without change from LSQRSolve.
-/

/-- Final triangular top block read out of a stored rectangular QR sequence. -/
noncomputable def storedQRFinalR {m n : ℕ} (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
/-- Final top right-hand side read out of a stored rectangular QR sequence. -/
noncomputable def storedQRFinalTopRhs {m n : ℕ} (hmn : n ≤ m)
    (b_hat : ℕ → Fin m → ℝ) : Fin n → ℝ :=
  fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩
/-- The computed least-squares coefficients returned by the stored QR handoff. -/
noncomputable def storedQRBackSubSolution {m n : ℕ} (fp : FPModel)
    (hmn : n ≤ m) (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ) : Fin n → ℝ :=
  fl_backSub fp n (storedQRFinalR hmn A_hat)
    (storedQRFinalTopRhs hmn b_hat)
/-- Off-diagonal-control invariant for the unpivoted stored-QR route.

    This is the explicit stronger invariant chosen for the remaining
    rectangular QR/preconditioner bottleneck.  It is deliberately stronger than
    the bare exact no-pivot Householder recurrence: it requires each current
    local leading block to be nonsingular and diagonally dominant, and it also
    requires the stored compact-update sequence budget to be small relative to
    the displayed Higham diagonal-dominant triangular inverse budget.

    The route-elimination theorems above show that this invariant is not a
    generic consequence of full rank, exact QR shape, finite conditioning, or
    the standard exact no-pivot recurrence alone.  Future source-specific work
    may prove this invariant from stronger pivoting, sorting, or
    off-diagonal-control assumptions. -/
structure StoredQROffDiagonalControlInvariant
    {m n : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ) : Prop where
  leadingBlock_det_ne_zero : ∀ k (hk : k < n),
    Matrix.det
      (qrLeadingBlock (A_hat k)
        (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
        Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0
  leadingBlock_diagDominant : ∀ k (hk : k < n),
    IsDiagDominantUpper (k + 1)
      (qrLeadingBlock (A_hat k)
        (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
  compact_sequence_product_small : ∀ k (hk : k < n),
    2 *
        diagDominantUpperInvBudgetExpr (k + 1)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          ⟨k, Nat.lt_succ_self k⟩ *
      ((m : ℝ) *
        (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
          vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩)) ^ 2) <
      1
/-- Source-shaped off-diagonal-control data for the unpivoted stored-QR route.

    Compared with `StoredQROffDiagonalControlInvariant`, this exposes the
    local triangular/diagonal/off-diagonal facts separately.  The determinant
    and `IsDiagDominantUpper` fields are then derived by local matrix algebra
    rather than assumed as already-packaged facts. -/
structure StoredQRSourceOffDiagonalControl
    {m n : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ) : Prop where
  leadingBlock_upper : ∀ k (hk : k < n),
    ∀ i j : Fin (k + 1), j.val < i.val →
      qrLeadingBlock (A_hat k)
        (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i j = 0
  leadingBlock_diag_ne_zero : ∀ k (hk : k < n),
    ∀ i : Fin (k + 1),
      qrLeadingBlock (A_hat k)
        (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i ≠ 0
  leadingBlock_offdiag_le_diag : ∀ k (hk : k < n),
    ∀ i j : Fin (k + 1), i.val < j.val →
      |qrLeadingBlock (A_hat k)
        (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i j| ≤
      |qrLeadingBlock (A_hat k)
        (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|
  compact_sequence_product_small : ∀ k (hk : k < n),
    2 *
        diagDominantUpperInvBudgetExpr (k + 1)
          (qrLeadingBlock (A_hat k)
            (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
          ⟨k, Nat.lt_succ_self k⟩ *
      ((m : ℝ) *
        (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
          vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩)) ^ 2) <
      1
/-- The stored trailing Householder recurrence supplies the triangular-shape
    part of `StoredQRSourceOffDiagonalControl`.

    Thus the remaining source-shaped route-1 obligations are only the genuinely
    quantitative/domain-specific ones: nonzero displayed diagonals, row-wise
    off-diagonal domination, and compact-product smallness. -/
theorem StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diag_offdiag_product
    {m n : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hdiag : ∀ k (hk : k < n),
      ∀ i : Fin (k + 1),
        qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i ≠ 0)
    (hoffdiag : ∀ k (hk : k < n),
      ∀ i j : Fin (k + 1), i.val < j.val →
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i j| ≤
        |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i i|)
    (hproduct : ∀ k (hk : k < n),
      2 *
          diagDominantUpperInvBudgetExpr (k + 1)
            (qrLeadingBlock (A_hat k)
              (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
            ⟨k, Nat.lt_succ_self k⟩ *
        ((m : ℝ) *
          (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
            vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩)) ^ 2) <
        1) :
    StoredQRSourceOffDiagonalControl hmn fp A_hat b_hat alpha := by
  classical
  let v : ℕ → Fin m → ℝ := fun k =>
    if hk : k < n then
      householderTrailingActiveVector m
        ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩) (alpha k)
    else 0
  let β : ℕ → ℝ := fun k =>
    if hk : k < n then
      householderBetaSpec m
        (householderTrailingActiveVector m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
    else 0
  have hStep : ∀ k, k < n →
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k (v k) (β k) (A_hat k) := by
    intro k hk
    simpa [v, β, hk] using hStepA k hk
  have hlower :
      ∀ k, k ≤ n →
        ∀ (i : Fin m) (j : Fin n),
          j.val < k → j.val < i.val → A_hat k i j = 0 :=
    fl_householderStoredPanel_sequence_prefix_lower_zero fp v β A_hat hStep
  refine
    { leadingBlock_upper := ?_
      leadingBlock_diag_ne_zero := hdiag
      leadingBlock_offdiag_le_diag := hoffdiag
      compact_sequence_product_small := hproduct }
  intro k hk i j hji
  have hkm : k + 1 ≤ m :=
    Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)
  have hjk : (qrLeadingColumn n k hk j).val < k := by
    simp [qrLeadingColumn]
    omega
  have hji' :
      (qrLeadingColumn n k hk j).val <
        (qrLeadingRow m k hkm i).val := by
    simpa [qrLeadingColumn, qrLeadingRow] using hji
  have hzero :=
    hlower k (Nat.le_of_lt hk)
      (qrLeadingRow m k hkm i)
      (qrLeadingColumn n k hk j)
      hjk hji'
  simpa [qrLeadingBlock] using hzero
/-- The per-pivot compact-product expression used by the stored QR
    off-diagonal-control route. -/
noncomputable def storedQRCompactSequenceProductExpr
    {m n : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (k : Fin n) : ℝ :=
  2 *
      diagDominantUpperInvBudgetExpr (k.val + 1)
        (qrLeadingBlock (A_hat k.val)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le k.isLt hmn)) k.isLt)
        ⟨k.val, Nat.lt_succ_self k.val⟩ *
    ((m : ℝ) *
      (storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
        vecNorm2 (fun i : Fin m => A_hat k.val i k)) ^ 2)
/-- Source-denominator nonbreakdown from the signed Householder alpha
    equations and positive active trailing norms.

    This is the finite stored-QR adapter around the scalar Householder theorem
    `householderTrailingActiveVector_inner_self_ne_zero_of_trailingNorm2Sq_pos_mul_nonpos`.
    It removes the raw `v^T v != 0` field from later canonical route
    wrappers, replacing it by the source-shaped signed-alpha and positive
    trailing-norm hypotheses. -/
theorem storedQRSourceDenominator_ne_zero_of_trailingNorm2Sq_pos_mul_nonpos
    {m n : ℕ} (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (htrailingPos : ∀ k (hk : k < n),
      0 < householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0) :
    ∀ k (hk : k < n),
      (∑ i : Fin m,
        householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i *
          householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i) ≠ 0 := by
  intro k hk
  exact
    householderTrailingActiveVector_inner_self_ne_zero_of_trailingNorm2Sq_pos_mul_nonpos
      m ⟨k, lt_of_lt_of_le hk hmn⟩
      (fun a => A_hat k a ⟨k, hk⟩) (alpha k)
      (halpha k hk) (htrailingPos k hk) (hsign k hk)
/-- The stored Householder panel recurrence supplies the previous-column
    lower-zero shape consumed by the determinant-facing nonbreakdown bridge.

    This is just the existing prefix lower-zero theorem specialized to the
    signed trailing Householder vectors used by the least-squares QR loop. -/
theorem storedQRPreviousColumnLowerZero_of_stored_trailing_householder_sequence
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k)) :
    ∀ k (hk : k < n) (i : Fin m) (j : Fin k),
      k ≤ i.val → A_hat k i (qrPreviousColumn n k hk j) = 0 := by
  classical
  let v : ℕ → Fin m → ℝ := fun k =>
    if hk : k < n then
      householderTrailingActiveVector m
        ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩) (alpha k)
    else 0
  let β : ℕ → ℝ := fun k => householderBetaSpec m (v k)
  have hStep : ∀ k, k < n →
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k (v k) (β k) (A_hat k) := by
    intro k hk
    simpa [v, β, hk] using hStepA k hk
  have hprefix :=
    fl_householderStoredPanel_sequence_prefix_lower_zero
      fp v β A_hat hStep
  intro k hk i j hki
  exact
    hprefix k (Nat.le_of_lt hk) i (qrPreviousColumn n k hk j)
      (by simp [qrPreviousColumn])
      (lt_of_lt_of_le j.isLt hki)
/-- Source denominator nonbreakdown derived from the actual stored QR loop.

Local diagonal dominance supplies the current and previous leading-block
determinants, the stored recurrence supplies previous-column lower zeros, and
the signed Householder alpha definition supplies the scalar square/sign facts.
This removes the raw `v^T v != 0` field from active source-denominator
surfaces whenever these loop-facing hypotheses are already visible. -/
theorem storedQRSourceDenominator_ne_zero_of_diagDominant_signedAlphaDef_stored_trailing_sequence
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (hDD : ∀ k (hk : k < n),
      IsDiagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)) :
    ∀ k (hk : k < n),
      (∑ i : Fin m,
        householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i *
          householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i) ≠ 0 := by
  have halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩) := by
    intro k hk
    rw [hAlphaDef k hk]
    exact
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq
        m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩)
  have hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0 := by
    intro k hk
    rw [hAlphaDef k hk]
    exact
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos
        m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩)
  have hlowerPrev : ∀ k (hk : k < n) (i : Fin m) (j : Fin k),
      k ≤ i.val → A_hat k i (qrPreviousColumn n k hk j) = 0 :=
    storedQRPreviousColumnLowerZero_of_stored_trailing_householder_sequence
      fp hmn A_hat alpha hStepA
  have hdetPrev : ∀ k (hk : k < n),
      Matrix.det
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_of_lt (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin k) (Fin k) ℝ) ≠ 0 := by
    intro k hk
    exact
      qrPreviousLeadingBlockTranspose_det_ne_zero_of_diagDominant_leadingBlock
        (A_hat k) (le_of_lt (lt_of_lt_of_le hk hmn))
        (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk
        (hDD k hk)
  have hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0 := by
    intro k hk
    exact
      det_ne_zero_of_diagDominantUpper (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        (hDD k hk)
  have htrailingPos : ∀ k (hk : k < n),
      0 < householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩) := by
    intro k hk
    exact
      householderTrailingNorm2Sq_pos_of_leading_block_det_ne_zero
        (A_hat k) (lt_of_lt_of_le hk hmn) hk
        (hdetPrev k hk) (hdetLead k hk) (hlowerPrev k hk)
  exact
    storedQRSourceDenominator_ne_zero_of_trailingNorm2Sq_pos_mul_nonpos
      hmn A_hat alpha halpha htrailingPos hsign
/-- The finite active-pivot policy supplies the raw pivot-maximality field.

This is the local pivot-policy reduction used by the active/prefix QR route:
if the displayed pivot column is chosen by `householderActiveMaxPivotColumn`
at every stored stage, then the row-growth theorems may consume the usual
trailing-column-norm maximality inequality. -/
theorem storedQRActiveMaxPivotColumn_pivotMax
    {m n : ℕ} (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (hpivotChoice : ∀ t (ht : t < n),
      ⟨t, ht⟩ =
        householderActiveMaxPivotColumn
          ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat t)) :
    ∀ t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
      householderTrailingColumnNorm2Sq
          (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
          (A_hat t) l ≤
        householderTrailingColumnNorm2Sq
          (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
          (A_hat t) ⟨t, ht⟩ := by
  intro t ht l hl
  have hmax :=
    householderActiveMaxPivotColumn_pivot_max
      ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat t) l hl
  have hnormEq :
      householderTrailingColumnNorm2Sq
          (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
          (A_hat t)
          (householderActiveMaxPivotColumn
            ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩ (A_hat t)) =
        householderTrailingColumnNorm2Sq
          (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
          (A_hat t) ⟨t, ht⟩ := by
    rw [← hpivotChoice t ht]
  exact hmax.trans_eq hnormEq
/-- The source-shaped off-diagonal-control data imply the packaged invariant
    consumed by the solver-facing QR certificate. -/
theorem StoredQROffDiagonalControlInvariant.of_sourceOffDiagonalControl
    {m n : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (hoff : StoredQRSourceOffDiagonalControl hmn fp A_hat b_hat alpha) :
    StoredQROffDiagonalControlInvariant hmn fp A_hat b_hat alpha := by
  refine
    { leadingBlock_det_ne_zero := ?_
      leadingBlock_diagDominant := ?_
      compact_sequence_product_small := hoff.compact_sequence_product_small }
  · intro k hk
    exact
      det_ne_zero_of_upper_triangular_diag_ne_zero (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        (hoff.leadingBlock_upper k hk)
        (hoff.leadingBlock_diag_ne_zero k hk)
  · intro k hk
    exact
      ⟨hoff.leadingBlock_upper k hk,
        hoff.leadingBlock_diag_ne_zero k hk,
        hoff.leadingBlock_offdiag_le_diag k hk⟩

end NumStability
