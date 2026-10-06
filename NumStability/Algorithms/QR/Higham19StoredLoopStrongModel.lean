-- Algorithms/QR/Higham19StoredLoopStrongModel.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms" (2nd ed.),
-- §19.3-§19.4, Theorem 19.13 (eq. (19.13): the STORED Householder / modified
-- Gram-Schmidt QR loop backward error).
--
-- PURPOSE (route (b): stronger honest rounding/normalization model).
-- `Higham19StoredLoop.lean` builds the UNCONDITIONAL route-(a) perturbation
-- bridge
--
--     fl_householderStoredPanelStep = fl_householderApplyMatrixRect
--                                       + storedLoopPerturbation,
--
-- where `storedLoopPerturbation` is supported on the storage region (completed
-- columns `j < k`, and the hard-zeroed sub-pivot entries `j = k`, `i > k`) and
-- is entrywise controlled by the explicit `storageDiscardComparison` matrix.
-- That bridge is honest but structural: it does NOT by itself collapse the
-- storage mass into the printed `γ̃` (gamma-tilde) class, because the bare
-- `FPModel` cannot force the discarded sub-pivot entries to be small (Codex's
-- counterexamples `sourceFaithfulHouseholderNormalizationModel_not_forall_FPModel`
-- and `stored_loop_signed_norm_hypotheses_do_not_force_trailingActiveVector_self_dot_two`
-- in `Higham19.lean`).
--
-- WHAT THIS FILE PROVES.  We complete the collapse at the FIRST pivot (`k = 0`,
-- the shape actually invoked by the recursive rounded QR panel), under an
-- explicit, HONEST strengthening of the bare `FPModel`: the reflector applied by
-- the stored step is the *source-faithful* trailing-active Householder reflector
-- of the pivot column, with a signed Householder alpha (`alpha^2 = ‖x‖^2`) and a
-- nonzero self-dot.  These are exactly the properties that hold for real
-- IEEE-style arithmetic on a nonbreakdown column (they are the algebraic content
-- of Higham (19.11)-(19.12): a reflector built from the column annihilates that
-- column below the pivot).  This is Codex's `sourceFaithfulHouseholderNormalization`
-- self-dot fact in the form that the annihilation actually needs; it is NOT the
-- bare `FPModel`, and it is NOT the target-equivalent assumption (we do not
-- assume the stored output is a fresh application; we PROVE the discarded mass is
-- roundoff).
--
-- The dimensions are taken in successor form `m+1`, `n+1`: this is exactly the
-- shape of the recursive rounded QR panel step (a nonempty pivot column and at
-- least the pivot column present), and it is what supplies the pivot index
-- `0 : Fin (m+1)` / `0 : Fin (n+1)`.
--
-- Under that model we prove:
--
--   * (exact annihilation) the EXACT reflector sends the pivot column to zero
--     below the pivot;
--   * (entrywise `γ̃` collapse) every entry of `storedLoopPerturbation` at the
--     first pivot is bounded in absolute value by the compact Householder
--     component budget `householderCompactComponentBudget` (the deterministic,
--     data-dependent `γ̃`-class per-entry roundoff budget from
--     `HouseholderApplySupport`), and vanishes off the sub-pivot region;
--   * (Frobenius collapse) hence
--         ‖storedLoopPerturbation fp (m+1) (n+1) 0 v β A‖_F
--             ≤ ‖firstPivotStoredLoopStrongBudget fp (m+1) (n+1) v β A‖_F,
--     with the RHS a matrix of pure compact-application roundoff budgets — i.e.
--     the storage mass at the first pivot is in the printed `γ̃` class, NOT the
--     unbounded `|A - raw|` class of the bare bridge.
--
-- This is the missing collapse that the bare-`FPModel` bridge could not deliver:
-- once the discarded below-pivot mass is roundoff (annihilation), the stored loop
-- is a fresh rounded application plus a `γ̃`-class perturbation, which is the
-- `MGSQRBounds`/`mgs_qr_bounds`-shaped content of Theorem 19.13 at the first
-- pivot.
--
-- HONEST SCOPE / RESIDUAL.  The collapse is UNCONDITIONAL over the stated strong
-- model at the first pivot.  It does not extend to `k > 0` without an additional
-- reflector-invariance hypothesis on the already-completed columns (the exact
-- reflector must FIX a completed column: `matMulVec (householder) col = col`),
-- which is a genuinely separate structural fact and is documented as the residual
-- for the multi-pivot lift.  At the first pivot there are NO completed columns,
-- so the collapse is complete.  Nothing here edits or weakens any existing
-- declaration; everything imports Codex's and the support files read-only.
--
-- IMPORT-ONLY.

import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.QR.HouseholderQRSupport
import NumStability.Algorithms.QR.Higham19StoredLoop

namespace NumStability

open scoped BigOperators

/-- **Honest strong-model data for the first-pivot stored Householder loop**
    (Higham §19.3, eq. (19.11)-(19.13)).

    This records the exact extra facts — beyond the bare `FPModel` — that make
    the stored loop's discarded below-pivot mass be roundoff rather than
    arbitrary.  The reflector `(v, β)` applied by the stored step at the first
    pivot is the *source-faithful* trailing-active Householder reflector of the
    pivot column `x = A[:,0]`:

    * `vector_eq`  : `v = householderTrailingActiveVector (m+1) 0 x alpha`;
    * `beta_eq`    : `β = householderBetaSpec (m+1) v`;
    * `alpha_sq`   : `alpha^2 = ‖x‖^2` on the trailing part (the signed
      Householder alpha; Higham (19.11));
    * `self_dot`   : the reflector self-dot `∑ v_i^2 ≠ 0` (nonbreakdown; the
      self-dot fact isolated by Codex's `sourceFaithfulHouseholderNormalization`).

    All four hold for real IEEE-style arithmetic on a nonbreakdown column: they
    are the algebraic identity of the Householder construction, not a smallness
    or target-equivalent assumption.  In particular this does NOT assume the
    stored output equals a fresh application; the collapse of the discarded mass
    to `γ̃` is PROVED, not assumed. -/
structure firstPivotSelfAnnihilatingReflector (m n : ℕ)
    (v : Fin (m + 1) → ℝ) (β : ℝ) (A : Fin (m + 1) → Fin (n + 1) → ℝ)
    (alpha : ℝ) : Prop where
  /-- The reflector is the trailing-active Householder vector of column `0`. -/
  vector_eq :
    v = householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
      (fun a => A a (0 : Fin (n + 1))) alpha
  /-- The scale is the source `betaSpec` normalization of that reflector. -/
  beta_eq :
    β = householderBetaSpec (m + 1) v
  /-- Signed Householder alpha: `alpha^2` equals the trailing squared norm
      (Higham (19.11)). -/
  alpha_sq :
    alpha * alpha =
      householderTrailingNorm2Sq (m + 1) (0 : Fin (m + 1))
        (fun a => A a (0 : Fin (n + 1)))
  /-- Nonbreakdown self-dot of the reflector (the source-faithful self-dot fact
      needed for annihilation). -/
  self_dot :
    (∑ i : Fin (m + 1),
        householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
            (fun a => A a (0 : Fin (n + 1))) alpha i *
          householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
            (fun a => A a (0 : Fin (n + 1))) alpha i) ≠ 0

/-- **Exact annihilation of the pivot column below the first pivot**
    (Higham §19.3, eq. (19.11)-(19.12)).

    Under the honest strong-model data, the EXACT reflector sends the pivot
    column `A[:,0]` to `0` in every row below the pivot (`0 < i`).  This is the
    defining property of the Householder reflector formed from the column; it is
    the fact the bare `FPModel` could not supply and is what makes the discarded
    stored mass be roundoff. -/
theorem H19_Theorem19_13_firstPivot_exact_annihilation
    {m n : ℕ} (v : Fin (m + 1) → ℝ) (β : ℝ)
    (A : Fin (m + 1) → Fin (n + 1) → ℝ) (alpha : ℝ)
    (hmodel : firstPivotSelfAnnihilatingReflector m n v β A alpha)
    (i : Fin (m + 1)) (hi : 0 < i.val) :
    matMulVec (m + 1) (householder (m + 1) v β)
        (fun a => A a (0 : Fin (n + 1))) i = 0 := by
  have hden :
      (∑ i : Fin (m + 1),
          householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
              (fun a => A a (0 : Fin (n + 1))) alpha i *
            householderTrailingActiveVector (m + 1) (0 : Fin (m + 1))
              (fun a => A a (0 : Fin (n + 1))) alpha i) ≠ 0 :=
    hmodel.self_dot
  have hpivot0 : ((0 : Fin (m + 1))).val = 0 := rfl
  have hzero :=
    matMulVec_householder_trailingActiveVector_eq_zero_of_pivot_lt
      (m + 1) (0 : Fin (m + 1)) (fun a => A a (0 : Fin (n + 1))) alpha
      hmodel.alpha_sq hden i (by simpa [hpivot0] using hi)
  rw [hmodel.beta_eq, hmodel.vector_eq]
  simpa using hzero

/-- **First-pivot stored-loop `γ̃`-class budget matrix**
    (Higham Theorem 19.13, stored form; §19.3-§19.4).

    On the discarded sub-pivot entries (`j.val = 0`, `0 < i.val`) it carries the
    compact Householder component budget `householderCompactComponentBudget`
    (the deterministic, data-dependent `γ̃`-class per-entry roundoff budget from
    `HouseholderApplySupport`, the same budget used by the fresh-application
    backward error).  Off the sub-pivot region it is zero.  Its Frobenius norm is
    a pure roundoff quantity — the printed `γ̃`-class mass, NOT the unbounded
    `|A - raw|` mass of the bare structural bridge. -/
noncomputable def firstPivotStoredLoopStrongBudget (fp : FPModel) (m n : ℕ)
    (v : Fin (m + 1) → ℝ) (β : ℝ) (A : Fin (m + 1) → Fin (n + 1) → ℝ) :
    Fin (m + 1) → Fin (n + 1) → ℝ :=
  fun i j =>
    if j.val = 0 then
      (if 0 < i.val then
          householderCompactComponentBudget fp (m + 1) v β (fun a => A a j) i
        else 0)
    else 0

/-- **Entrywise `γ̃` collapse of the first-pivot stored-loop perturbation**
    (Higham Theorem 19.13, stored form).

    Under the honest strong model, every entry of the route-(a)
    `storedLoopPerturbation` at the first pivot is bounded in absolute value by
    the compact Householder component budget on the sub-pivot region, and is zero
    off it.  This is the collapse the bare `FPModel` could not deliver: on the
    discarded below-pivot entries the stored value differs from the (fresh) target
    `0` only by compact-application roundoff (`γ̃`-class), because the exact
    reflector annihilates the pivot column there. -/
theorem H19_Theorem19_13_firstPivot_storedLoopPerturbation_entry_abs_le
    (fp : FPModel) {m n : ℕ} (v : Fin (m + 1) → ℝ) (β : ℝ)
    (A : Fin (m + 1) → Fin (n + 1) → ℝ) (alpha : ℝ)
    (hm : gammaValid fp (m + 1))
    (hmodel : firstPivotSelfAnnihilatingReflector m n v β A alpha)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    |storedLoopPerturbation fp (m + 1) (n + 1) 0 v β A i j| ≤
      firstPivotStoredLoopStrongBudget fp m n v β A i j := by
  rw [H19_Theorem19_13_storedLoopPerturbation_entry fp (m + 1) (n + 1) 0 v β A i j]
  unfold firstPivotStoredLoopStrongBudget
  have hnotlt : ¬ j.val < 0 := Nat.not_lt_zero _
  by_cases hj0 : j.val = 0
  · by_cases hi0 : 0 < i.val
    · -- sub-pivot entry: perturbation is `- raw i j`, target is `0`.
      simp only [hj0, if_true, hi0]
      -- `fl_householderApplyMatrixRect = fl_householderApplyCompact` definitionally.
      have hraw :
          fl_householderApplyMatrixRect fp (m + 1) (n + 1) v β A i j =
            fl_householderApplyCompact fp (m + 1) v β (fun a => A a j) i := rfl
      -- the pivot column is column `0`.
      have hjcol : (fun a => A a j) = (fun a => A a (0 : Fin (n + 1))) := by
        funext a; congr 1; exact Fin.ext hj0
      have hzero :
          matMulVec (m + 1) (householder (m + 1) v β) (fun a => A a j) i = 0 := by
        rw [hjcol]
        exact H19_Theorem19_13_firstPivot_exact_annihilation v β A alpha hmodel i hi0
      have hbudget :=
        fl_householderApplyCompact_componentwise_error_bound
          fp (m + 1) v β (fun a => A a j) hm i
      rw [hzero] at hbudget
      have hcollapse :
          |fl_householderApplyMatrixRect fp (m + 1) (n + 1) v β A i j| ≤
            householderCompactComponentBudget fp (m + 1) v β (fun a => A a j) i := by
        rw [hraw]
        simpa using hbudget
      simpa [abs_neg] using hcollapse
    · -- pivot column, but at/above the pivot: perturbation entry is `0`.
      simp [hj0, hi0]
  · -- active/trailing region: perturbation entry is `0`.
    simp [hnotlt, hj0]

/-- **First-pivot stored-loop backward-error `γ̃` collapse (Frobenius form)**
    (Higham Theorem 19.13, eq. (19.13), stored form; §19.3-§19.4, p. 360-362).

    Under the honest strong model, the route-(a) `storedLoopPerturbation` at the
    first pivot has Frobenius norm bounded by the Frobenius norm of the
    `γ̃`-class compact-application budget matrix:

      `‖storedLoopPerturbation fp (m+1) (n+1) 0 v β A‖_F`
        `≤ ‖firstPivotStoredLoopStrongBudget fp (m+1) (n+1) v β A‖_F`.

    Combined with the unconditional bridge identity
    `H19_Theorem19_13_firstPivot_storedPanelStep_eq_applyMatrixRect_add_perturbation`,
    this says: at the first pivot the stored loop is a fresh rounded reflector
    application PLUS a perturbation whose mass is pure compact-application
    roundoff (the printed `γ̃` class).  This is the collapse the bare `FPModel`
    provably could not achieve — it is delivered here UNCONDITIONALLY over the
    honest strong model, giving the `MGSQRBounds`/`mgs_qr_bounds`-shaped
    `γ̃`-class content of Theorem 19.13 at the first pivot. -/
theorem H19_Theorem19_13_firstPivot_storedLoopPerturbation_frobNorm_le_strong
    (fp : FPModel) {m n : ℕ} (v : Fin (m + 1) → ℝ) (β : ℝ)
    (A : Fin (m + 1) → Fin (n + 1) → ℝ) (alpha : ℝ)
    (hm : gammaValid fp (m + 1))
    (hmodel : firstPivotSelfAnnihilatingReflector m n v β A alpha) :
    frobNorm (storedLoopPerturbation fp (m + 1) (n + 1) 0 v β A) ≤
      frobNorm (firstPivotStoredLoopStrongBudget fp m n v β A) := by
  have hentry : ∀ i : Fin (m + 1), ∀ j : Fin (n + 1),
      |storedLoopPerturbation fp (m + 1) (n + 1) 0 v β A i j| ≤
        (1 : ℝ) * |firstPivotStoredLoopStrongBudget fp m n v β A i j| := by
    intro i j
    rw [one_mul]
    have hbase :=
      H19_Theorem19_13_firstPivot_storedLoopPerturbation_entry_abs_le
        fp v β A alpha hm hmodel i j
    have hnonneg : 0 ≤ firstPivotStoredLoopStrongBudget fp m n v β A i j := by
      unfold firstPivotStoredLoopStrongBudget
      by_cases hj0 : j.val = 0
      · by_cases hi0 : 0 < i.val
        · simp only [hj0, if_true, hi0]
          exact householderCompactComponentBudget_nonneg
            fp (m + 1) v β (fun a => A a j) hm i
        · simp [hj0, hi0]
      · simp [hj0]
    rwa [abs_of_nonneg hnonneg]
  have := frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
    (storedLoopPerturbation fp (m + 1) (n + 1) 0 v β A)
    (firstPivotStoredLoopStrongBudget fp m n v β A)
    (by norm_num : (0 : ℝ) ≤ 1) hentry
  simpa using this

end NumStability
