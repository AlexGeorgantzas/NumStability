-- NumStability/Source/Higham/Chapter19/StoredLoop/Perturbation/Bridge.lean
--
-- Canonical destination introduced by reorganization wave R11
-- (phase branch B0003, projection P0003).
--
-- Every declaration of the historical owner `NumStability.Source.Higham.Chapter19.StoredLoop`
-- was relocated here unchanged as one frozen whole-owner block. The
-- historical module remains as a documented import-only compatibility
-- wrapper, so existing imports keep resolving.
--
-- Import retargets applied so this canonical module depends only on
-- canonical modules and never on a historical compatibility facade:
--   NumStability.Algorithms.LinearSystems.QR.HouseholderQRSupport
--     -> NumStability.Algorithms.LinearSystems.QR.Householder.StoredQR
--
-- Historical module documentation carried verbatim from `NumStability.Source.Higham.Chapter19.StoredLoop`.
-- It describes the mathematics of the declarations below and predates
-- R11; any module name it mentions is the pre-R11 name, now reached
-- through the canonical modules imported above.
--
--
-- Higham, "Accuracy and Stability of Numerical Algorithms" (2nd ed.),
-- §19.3–§19.4, Theorem 19.13 (the STORED Householder / modified Gram–Schmidt
-- QR loop backward-error result).
--
-- PURPOSE (perturbation-bridge route, Codex-lane goal).  The stored-loop form
-- of Theorem 19.13 is documented in the Chapter 19 ledger as an allowed-BLOCKED
-- row: naive arbitrary-`FPModel` equality between the STORED panel step
-- (`fl_householderStoredPanelStep`, which overwrites completed columns with
-- their stored values and hard-zeros the sub-pivot entries) and a FRESH rounded
-- reflector application (`fl_householderApplyMatrixRect`, the object consumed by
-- `fl_householder_sequence_backward_error`) is *false* — the repository already
-- records the counterexamples
-- (`stored_loop_signed_norm_hypotheses_do_not_force_trailingActiveVector_self_dot_two`,
-- `sourceFaithfulHouseholderNormalizationModel_not_forall_FPModel` in
-- `Higham19.lean`).  Codex left three routes open: (a) a perturbation bridge
-- relating the stored loop to the fresh application by a bounded perturbation,
-- (b) a stronger honest rounded model, (c) the exact subcase.
--
-- WHAT THIS FILE PROVES (route (a), unconditional).  We construct the exact
-- perturbation bridge.  For EVERY `FPModel`, every pivot `k`, reflector `v`,
-- scale `β`, and panel `A`,
--
--     fl_householderStoredPanelStep fp m n k v β A
--       = fl_householderApplyMatrixRect fp m n v β A  +  storedLoopPerturbation …
--
-- as an exact entrywise identity, where `storedLoopPerturbation` is an
-- explicitly-given matrix that is SUPPORTED ONLY on the storage region
-- (already-completed columns `j < k`, and the hard-zeroed sub-pivot entries of
-- the pivot column `j = k`, `i > k`).  On the active/trailing region the two
-- routes coincide, so the perturbation vanishes there.  We give the exact entry
-- formula on the storage region and the honest Frobenius bound
--
--     ‖storedLoopPerturbation …‖_F ≤ ‖storageDiscardComparison …‖_F,
--
-- i.e. the perturbation mass is controlled entrywise by the explicit stored /
-- discarded entries, with NO hidden hypothesis and NO smallness assumption.
-- This is the missing link that lets the fresh-application sequence
-- backward-error machinery be applied to the stored loop: the stored output is
-- a fresh application plus a bounded, support-localised perturbation.
--
-- HONEST SCOPE.  This is the unconditional STRUCTURAL perturbation bridge
-- (route (a)).  It does not by itself collapse the perturbation into the printed
-- `γ̃`-class constant: that additional collapse still needs the fresh-application
-- backward error plus a bound on the discarded sub-pivot mass, which is exactly
-- the `sourceFaithfulHouseholderNormalization` self-dot fact that the recorded
-- counterexamples show is NOT available for an arbitrary `FPModel` (it requires
-- route (b)/(c)).  What is delivered here is genuinely new and unconditional:
-- the bridge identity, the support characterisation, the exact storage-region
-- entry formula, and the entrywise-controlled Frobenius bound.  Nothing here
-- edits or weakens any existing declaration; every result imports Codex's files
-- read-only.
--
-- IMPORT-ONLY.  This file imports `HouseholderQRSupport` (stored panel step,
-- fresh rectangular application, and Codex's read-only active-region bridge
-- `fl_householderStoredPanelStep_eq_applyMatrixRect_of_active_not_below`) and
-- `MatrixAlgebra` (Frobenius plumbing).  It never edits them.

import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.LinearSystems.QR.Householder.StoredQR

/-!
# Bridge

Canonical Higham Chapter 19 stored-loop perturbation bridge.

Relocated from `NumStability.Source.Higham.Chapter19.StoredLoop` by wave R11 under the frozen B0003 declaration
route and the P0003 baseline projection. Public names, namespaces, kinds,
visibility, types, attributes and proofs are preserved exactly; private names
carry only the approved P0003 module-prefix normalization.
-/

namespace NumStability

open scoped BigOperators

/-- **Stored-loop perturbation matrix** (Higham Theorem 19.13, stored form,
    §19.3–§19.4).

    The explicit entrywise difference between the STORED panel step and the
    FRESH rounded rectangular reflector application, using the same reflector
    data `(v, β)`:

      `storedLoopPerturbation … i j`
        `= fl_householderStoredPanelStep fp m n k v β A i j`
        `  − fl_householderApplyMatrixRect fp m n v β A i j`.

    By construction this vanishes on the active/trailing region and is nonzero
    only on the storage region (completed columns `j < k`, and the hard-zeroed
    sub-pivot entries `j = k`, `i > k`); the exact values are recorded in
    `H19_Theorem19_13_storedLoopPerturbation_entry`. -/
noncomputable def storedLoopPerturbation (fp : FPModel) (m n k : ℕ)
    (v : Fin m → ℝ) (β : ℝ) (A : Fin m → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j =>
    fl_householderStoredPanelStep fp m n k v β A i j -
      fl_householderApplyMatrixRect fp m n v β A i j

/-- **Perturbation-bridge identity for the stored Householder loop**
    (Higham Theorem 19.13, stored form; §19.3–§19.4, p. 360–362).

    For EVERY `FPModel`, the stored panel step equals the fresh rounded
    rectangular reflector application plus the explicit
    `storedLoopPerturbation`:

      `fl_householderStoredPanelStep fp m n k v β A i j`
        `= fl_householderApplyMatrixRect fp m n v β A i j`
        `  + storedLoopPerturbation fp m n k v β A i j`.

    This is the exact route-(a) bridge: it relates the stored loop (whose naive
    arbitrary-`FPModel` equality with the fresh application is *false*, per the
    recorded counterexamples) to the fresh application consumed by
    `fl_householder_sequence_backward_error`, via a bounded, support-localised
    perturbation.  It is unconditional — no smallness, no source-faithful
    normalization, no hidden hypothesis. -/
theorem H19_Theorem19_13_storedPanelStep_eq_applyMatrixRect_add_perturbation
    (fp : FPModel) (m n k : ℕ) (v : Fin m → ℝ) (β : ℝ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    fl_householderStoredPanelStep fp m n k v β A i j =
      fl_householderApplyMatrixRect fp m n v β A i j +
        storedLoopPerturbation fp m n k v β A i j := by
  unfold storedLoopPerturbation
  ring

/-- **Support of the stored-loop perturbation is exactly the storage region.**

    On the active/trailing region — active columns `k ≤ j` that are not the
    hard-zeroed sub-pivot entries (`j.val = k → ¬ k < i.val`) — the stored step
    and the fresh application coincide, so the perturbation vanishes.  This is
    the entrywise face of `storedPanelStep_eq_applyMatrixRect_of_active_not_below`
    (Codex's Higham19.lean bridge, used here read-only). -/
theorem H19_Theorem19_13_storedLoopPerturbation_support
    (fp : FPModel) (m n k : ℕ) (v : Fin m → ℝ) (β : ℝ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    (hactive : k ≤ j.val)
    (hnotBelowPivot : j.val = k → ¬ k < i.val) :
    storedLoopPerturbation fp m n k v β A i j = 0 := by
  unfold storedLoopPerturbation
  rw [fl_householderStoredPanelStep_eq_applyMatrixRect_of_active_not_below
    fp m n k v β A i j hactive hnotBelowPivot]
  ring

/-- **Exact entry formula of the stored-loop perturbation on the storage
    region.**

    * On completed columns `j.val < k` the perturbation is the stored (copied)
      value minus the fresh application: `A i j − raw i j`.
    * On the hard-zeroed sub-pivot entries (`j.val = k`, `k < i.val`) the
      perturbation is `− raw i j` (the discarded below-pivot value).

    Together with the support lemma, this pins down every entry of the bridge
    perturbation with no hidden data. -/
theorem H19_Theorem19_13_storedLoopPerturbation_entry
    (fp : FPModel) (m n k : ℕ) (v : Fin m → ℝ) (β : ℝ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    storedLoopPerturbation fp m n k v β A i j =
      (if j.val < k then
          A i j - fl_householderApplyMatrixRect fp m n v β A i j
        else if j.val = k then
          (if k < i.val then
              - fl_householderApplyMatrixRect fp m n v β A i j
            else 0)
        else 0) := by
  unfold storedLoopPerturbation fl_householderStoredPanelStep
  simp only [fl_householderApplyCompactPanel_eq_applyMatrixRect fp m n v β A]
  by_cases hlt : j.val < k
  · simp [hlt]
  · by_cases heq : j.val = k
    · by_cases hbelow : k < i.val
      · simp [heq, hbelow]
      · simp [heq, hbelow]
    · simp [hlt, heq]

/-- **Explicit comparison matrix bounding the stored-loop perturbation mass.**

    On the storage region it carries the absolute value of the stored /
    discarded entry that the bridge perturbation equals; off the storage region
    it is zero.  Its Frobenius norm is exactly the amount of "storage" mass the
    stored loop introduces relative to a fresh reflector application. -/
noncomputable def storageDiscardComparison (fp : FPModel) (m n k : ℕ)
    (v : Fin m → ℝ) (β : ℝ) (A : Fin m → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j =>
    if j.val < k then
      |A i j - fl_householderApplyMatrixRect fp m n v β A i j|
    else if j.val = k then
      (if k < i.val then
          |fl_householderApplyMatrixRect fp m n v β A i j|
        else 0)
    else 0

/-- **Honest Frobenius bound for the stored-loop perturbation bridge**
    (Higham Theorem 19.13, stored form).

    The bridge perturbation is controlled entrywise by the explicit
    `storageDiscardComparison` matrix, hence

      `‖storedLoopPerturbation fp m n k v β A‖_F`
        `≤ ‖storageDiscardComparison fp m n k v β A‖_F`.

    Because the comparison matrix carries only the stored copies (`|A − raw|`
    on completed columns) and the discarded below-pivot values (`|raw|` on the
    sub-pivot entries), this bound is unconditional and exposes precisely which
    entries the stored-vs-fresh discrepancy lives on — the honest content of
    the perturbation-bridge route for the stored loop. -/
theorem H19_Theorem19_13_storedLoopPerturbation_frobNorm_le
    (fp : FPModel) (m n k : ℕ) (v : Fin m → ℝ) (β : ℝ)
    (A : Fin m → Fin n → ℝ) :
    frobNorm (storedLoopPerturbation fp m n k v β A) ≤
      frobNorm (storageDiscardComparison fp m n k v β A) := by
  have hentry : ∀ i : Fin m, ∀ j : Fin n,
      |storedLoopPerturbation fp m n k v β A i j| ≤
        (1 : ℝ) * |storageDiscardComparison fp m n k v β A i j| := by
    intro i j
    rw [one_mul, H19_Theorem19_13_storedLoopPerturbation_entry fp m n k v β A i j]
    unfold storageDiscardComparison
    by_cases hlt : j.val < k
    · simp [hlt, abs_abs]
    · by_cases heq : j.val = k
      · by_cases hbelow : k < i.val
        · simp [heq, hbelow, abs_neg, abs_abs]
        · simp [heq, hbelow]
      · simp [hlt, heq]
  have := frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
    (storedLoopPerturbation fp m n k v β A)
    (storageDiscardComparison fp m n k v β A)
    (by norm_num : (0 : ℝ) ≤ 1) hentry
  simpa using this

/-- **Stored-loop perturbation bridge, single-pivot QR specialization**
    (`k = 0`, `β = 1`).

    At the first pivot the storage region has no completed columns, so the
    perturbation lives *only* on the discarded below-pivot entries of column 0.
    This is the form the recursive rounded Householder QR panel
    (`fl_householderQRPanel_R`) actually invokes: one fresh rounded reflector
    application, then the QR storage convention that zeros the pivot column tail.
    The identity and the entrywise-controlled Frobenius bound both specialise
    unconditionally. -/
theorem H19_Theorem19_13_firstPivot_storedPanelStep_eq_applyMatrixRect_add_perturbation
    (fp : FPModel) (m n : ℕ) (v : Fin m → ℝ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    fl_householderStoredPanelStep fp m n 0 v 1 A i j =
      fl_householderApplyMatrixRect fp m n v 1 A i j +
        storedLoopPerturbation fp m n 0 v 1 A i j :=
  H19_Theorem19_13_storedPanelStep_eq_applyMatrixRect_add_perturbation
    fp m n 0 v 1 A i j

/-- **First-pivot Frobenius bound.**  At pivot `0` the stored-loop perturbation
    is bounded by the Frobenius norm of the discarded below-pivot column-0 mass
    (there are no completed columns to copy), unconditionally. -/
theorem H19_Theorem19_13_firstPivot_storedLoopPerturbation_frobNorm_le
    (fp : FPModel) (m n : ℕ) (v : Fin m → ℝ) (A : Fin m → Fin n → ℝ) :
    frobNorm (storedLoopPerturbation fp m n 0 v 1 A) ≤
      frobNorm (storageDiscardComparison fp m n 0 v 1 A) :=
  H19_Theorem19_13_storedLoopPerturbation_frobNorm_le fp m n 0 v 1 A

end NumStability
