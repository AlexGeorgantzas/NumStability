import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FieldSimp
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LinearSystems.LU.BlockLU.BlockMatrices
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum

/-!
# Block LU growth bounds

Reusable max-entry growth-factor and inverse-comparison bounds used by the
Block LU analysis.
-/

namespace NumStability

open scoped Matrix

/-- The source-facing growth-factor budget `rho * ||A||_max` is exactly the
    max-entry norm of the chosen growth matrix. -/
theorem growthFactorEntry_mul_maxEntryNormRect_eq_maxEntryNorm {n : ℕ}
    (hn : 0 < n) (A G : Fin n → Fin n → ℝ)
    (hA : 0 < maxEntryNorm hn A) :
    growthFactorEntry hn A G hA * maxEntryNormRect hn hn A =
      maxEntryNorm hn G := by
  unfold growthFactorEntry
  rw [maxEntryNormRect_eq_maxEntryNorm hn A]
  field_simp [ne_of_gt hA]

/-- Reindexing a matrix by an equivalence transports entrywise bounds on its
    constructive inverse.

    This is a max-entry analogue of the operator-norm reindexing bridges used
    elsewhere in the Chapter 13 Schur-complement route. -/
theorem invOf_entry_bound_of_reindex_eq
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (A : Matrix κ κ ℝ) (M : Matrix ι ι ℝ)
    [Invertible A] [Invertible M]
    (hM : M = fun i j : ι => A (e i) (e j))
    {bound : ℝ}
    (hA_entry : ∀ i j : κ, |(⅟A : Matrix κ κ ℝ) i j| ≤ bound) :
    ∀ i j : ι, |(⅟M : Matrix ι ι ℝ) i j| ≤ bound := by
  classical
  intro i j
  have h1 : ⅟M = M⁻¹ :=
    Matrix.invOf_eq_nonsing_inv M
  have h2 :
      M⁻¹ =
        ((A⁻¹ : Matrix κ κ ℝ).submatrix e e) := by
    rw [hM]
    exact Matrix.inv_submatrix_equiv A e e
  have hAinv : ⅟A = A⁻¹ :=
    Matrix.invOf_eq_nonsing_inv A
  have hentry :
      (⅟M : Matrix ι ι ℝ) i j = (⅟A : Matrix κ κ ℝ) (e i) (e j) := by
    calc
      (⅟M : Matrix ι ι ℝ) i j = M⁻¹ i j := by rw [h1]
      _ = A⁻¹ (e i) (e j) := by
            rw [h2]
            rfl
      _ = (⅟A : Matrix κ κ ℝ) (e i) (e j) := by rw [hAinv]
  rw [hentry]
  exact hA_entry (e i) (e j)

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    max-entry Schur-growth from the formal growth-factor definition.

    If the displayed Schur complement is bounded by the max-entry norm of the
    matrix `U` used in `growthFactorEntry`, then the book's Schur-growth
    certificate follows directly from
    `rho = maxEntryNorm U / maxEntryNorm A`.  The remaining source obligation
    is the GE bookkeeping theorem that places the Schur complement under that
    growth-factor matrix. -/
theorem maxEntryNormRect_le_growthFactorEntry_mul_of_le_maxEntryNorm
    {N s : ℕ} (hN : 0 < N) (hs : 0 < s)
    (A U : Fin N → Fin N → ℝ) (S : Fin s → Fin s → ℝ)
    (hApos : 0 < maxEntryNorm hN A)
    (hS_le_U : maxEntryNormRect hs hs S ≤ maxEntryNorm hN U) :
    maxEntryNormRect hs hs S ≤
      growthFactorEntry hN A U hApos * maxEntryNormRect hN hN A := by
  calc
    maxEntryNormRect hs hs S ≤ maxEntryNorm hN U := hS_le_U
    _ = growthFactorEntry hN A U hApos * maxEntryNormRect hN hN A := by
      rw [maxEntryNormRect_eq_maxEntryNorm hN A]
      unfold growthFactorEntry
      exact (div_mul_cancel₀ (maxEntryNorm hN U) (ne_of_gt hApos)).symm

/-- Higham, 2nd ed., Chapter 13, equation (13.21):
    square max-entry growth from the formal growth-factor definition.

    If a final upper factor `Ufac` is contained in the same source growth
    matrix `G`, then `‖Ufac‖_max <= ρ_n ‖A‖_max` for
    `ρ_n = growthFactorEntry A G`. -/
theorem maxEntryNorm_le_growthFactorEntry_mul_of_le_maxEntryNorm
    {N : ℕ} (hN : 0 < N)
    (A G Ufac : Fin N → Fin N → ℝ)
    (hApos : 0 < maxEntryNorm hN A)
    (hU_le_G : maxEntryNorm hN Ufac ≤ maxEntryNorm hN G) :
    maxEntryNorm hN Ufac ≤
      growthFactorEntry hN A G hApos * maxEntryNormRect hN hN A := by
  calc
    maxEntryNorm hN Ufac ≤ maxEntryNorm hN G := hU_le_G
    _ = growthFactorEntry hN A G hApos * maxEntryNormRect hN hN A := by
      rw [maxEntryNormRect_eq_maxEntryNorm hN A]
      unfold growthFactorEntry
      exact (div_mul_cancel₀ (maxEntryNorm hN G) (ne_of_gt hApos)).symm

/-- Higham, 2nd ed., Chapter 13, Problem 13.4 scalar support:
    compare two formal max-entry growth factors.

    If the local growth object is max-entry dominated by the global growth
    object and the local denominator is at least the global denominator, then
    the local `growthFactorEntry` is no larger than the global one.  This
    isolates the denominator side condition in the remaining source
    `rhoLocal <= rhoFull` comparison. -/
theorem growthFactorEntry_le_of_growth_le_of_base_le
    {nLocal nGlobal : ℕ} (hLocal : 0 < nLocal) (hGlobal : 0 < nGlobal)
    (Aloc Gloc : Fin nLocal → Fin nLocal → ℝ)
    (Aglob Gglob : Fin nGlobal → Fin nGlobal → ℝ)
    (hAlocPos : 0 < maxEntryNorm hLocal Aloc)
    (hAglobPos : 0 < maxEntryNorm hGlobal Aglob)
    (hGrowth : maxEntryNorm hLocal Gloc ≤ maxEntryNorm hGlobal Gglob)
    (hBase : maxEntryNorm hGlobal Aglob ≤ maxEntryNorm hLocal Aloc) :
    growthFactorEntry hLocal Aloc Gloc hAlocPos ≤
      growthFactorEntry hGlobal Aglob Gglob hAglobPos := by
  unfold growthFactorEntry
  rw [div_le_div_iff₀ hAlocPos hAglobPos]
  have hleft :
      maxEntryNorm hLocal Gloc * maxEntryNorm hGlobal Aglob ≤
        maxEntryNorm hGlobal Gglob * maxEntryNorm hGlobal Aglob :=
    mul_le_mul_of_nonneg_right hGrowth (maxEntryNorm_nonneg hGlobal Aglob)
  have hright :
      maxEntryNorm hGlobal Gglob * maxEntryNorm hGlobal Aglob ≤
        maxEntryNorm hGlobal Gglob * maxEntryNorm hLocal Aloc :=
    mul_le_mul_of_nonneg_left hBase (maxEntryNorm_nonneg hGlobal Gglob)
  exact le_trans hleft hright

/-- Higham, 2nd ed., Chapter 13, equations (13.21)--(13.22):
    block upper-factor growth from the formal max-entry growth factor.

    If a block upper factor is contained in the same source growth matrix `G`,
    its Chapter 13 block max norm satisfies the Eq.13.21-style bound with
    `ρ_n = growthFactorEntry A G`. -/
theorem blockMaxNorm_le_growthFactorEntry_mul_of_le_maxEntryNorm
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (A G : Fin N → Fin N → ℝ)
    (Ufac : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (hApos : 0 < maxEntryNorm hN A)
    (hU_le_G : blockMaxNorm hm hr Ufac ≤ maxEntryNorm hN G) :
    blockMaxNorm hm hr Ufac ≤
      growthFactorEntry hN A G hApos * maxEntryNormRect hN hN A := by
  calc
    blockMaxNorm hm hr Ufac ≤ maxEntryNorm hN G := hU_le_G
    _ = growthFactorEntry hN A G hApos * maxEntryNormRect hN hN A := by
      rw [maxEntryNormRect_eq_maxEntryNorm hN A]
      unfold growthFactorEntry
      exact (div_mul_cancel₀ (maxEntryNorm hN G) (ne_of_gt hApos)).symm

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    scalar local-to-global `rho^2 kappa` budget comparison from the two real
    remaining ingredients.

    If the local growth object is max-entry dominated by the ambient growth
    object, and the local inverse-to-input max-entry ratio is dominated by the
    ambient inverse-to-input ratio, then the full `rho^2 kappa` budget is
    dominated.  The inverse-ratio hypothesis is intentionally explicit: this
    lemma does not prove the hard condition-number comparison. -/
theorem growthFactorEntry_sq_kappa_budget_le_of_growth_le_inv_ratio
    {nLocal nGlobal : ℕ} (hLocal : 0 < nLocal) (hGlobal : 0 < nGlobal)
    (Aloc Gloc AlocInv : Fin nLocal → Fin nLocal → ℝ)
    (Aglob Gglob AglobInv : Fin nGlobal → Fin nGlobal → ℝ)
    (hAlocPos : 0 < maxEntryNorm hLocal Aloc)
    (hAglobPos : 0 < maxEntryNorm hGlobal Aglob)
    (hGrowth : maxEntryNorm hLocal Gloc ≤ maxEntryNorm hGlobal Gglob)
    (hInvRatio :
      maxEntryNormRect hLocal hLocal AlocInv *
          maxEntryNormRect hGlobal hGlobal Aglob ≤
        maxEntryNormRect hGlobal hGlobal AglobInv *
          maxEntryNormRect hLocal hLocal Aloc) :
    (growthFactorEntry hLocal Aloc Gloc hAlocPos) ^ 2 *
        (maxEntryNormRect hLocal hLocal Aloc *
          maxEntryNormRect hLocal hLocal AlocInv) ≤
      (growthFactorEntry hGlobal Aglob Gglob hAglobPos) ^ 2 *
        (maxEntryNormRect hGlobal hGlobal Aglob *
          maxEntryNormRect hGlobal hGlobal AglobInv) := by
  have hAlocRectPos : 0 < maxEntryNormRect hLocal hLocal Aloc := by
    simpa [maxEntryNormRect_eq_maxEntryNorm hLocal Aloc] using hAlocPos
  have hAglobRectPos : 0 < maxEntryNormRect hGlobal hGlobal Aglob := by
    simpa [maxEntryNormRect_eq_maxEntryNorm hGlobal Aglob] using hAglobPos
  have hInvDiv :
      maxEntryNormRect hLocal hLocal AlocInv /
          maxEntryNormRect hLocal hLocal Aloc ≤
        maxEntryNormRect hGlobal hGlobal AglobInv /
          maxEntryNormRect hGlobal hGlobal Aglob := by
    rw [div_le_div_iff₀ hAlocRectPos hAglobRectPos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hInvRatio
  have hGrowthSq :
      (maxEntryNorm hLocal Gloc) ^ 2 ≤ (maxEntryNorm hGlobal Gglob) ^ 2 :=
    pow_le_pow_left₀ (maxEntryNorm_nonneg hLocal Gloc) hGrowth 2
  have hInvDivNonneg :
      0 ≤ maxEntryNormRect hLocal hLocal AlocInv /
          maxEntryNormRect hLocal hLocal Aloc :=
    div_nonneg (maxEntryNormRect_nonneg hLocal hLocal AlocInv)
      (le_of_lt hAlocRectPos)
  have hGlobalSqNonneg : 0 ≤ (maxEntryNorm hGlobal Gglob) ^ 2 :=
    pow_nonneg (maxEntryNorm_nonneg hGlobal Gglob) 2
  have hProduct :
      (maxEntryNorm hLocal Gloc) ^ 2 *
          (maxEntryNormRect hLocal hLocal AlocInv /
            maxEntryNormRect hLocal hLocal Aloc) ≤
        (maxEntryNorm hGlobal Gglob) ^ 2 *
          (maxEntryNormRect hGlobal hGlobal AglobInv /
            maxEntryNormRect hGlobal hGlobal Aglob) :=
    mul_le_mul hGrowthSq hInvDiv hInvDivNonneg hGlobalSqNonneg
  have hLocalEq :
      (growthFactorEntry hLocal Aloc Gloc hAlocPos) ^ 2 *
          (maxEntryNormRect hLocal hLocal Aloc *
            maxEntryNormRect hLocal hLocal AlocInv) =
        (maxEntryNorm hLocal Gloc) ^ 2 *
          (maxEntryNormRect hLocal hLocal AlocInv /
            maxEntryNormRect hLocal hLocal Aloc) := by
    unfold growthFactorEntry
    rw [maxEntryNormRect_eq_maxEntryNorm hLocal Aloc]
    field_simp [ne_of_gt hAlocPos]
  have hGlobalEq :
      (growthFactorEntry hGlobal Aglob Gglob hAglobPos) ^ 2 *
          (maxEntryNormRect hGlobal hGlobal Aglob *
            maxEntryNormRect hGlobal hGlobal AglobInv) =
        (maxEntryNorm hGlobal Gglob) ^ 2 *
          (maxEntryNormRect hGlobal hGlobal AglobInv /
            maxEntryNormRect hGlobal hGlobal Aglob) := by
    unfold growthFactorEntry
    rw [maxEntryNormRect_eq_maxEntryNorm hGlobal Aglob]
    field_simp [ne_of_gt hAglobPos]
  calc
    (growthFactorEntry hLocal Aloc Gloc hAlocPos) ^ 2 *
        (maxEntryNormRect hLocal hLocal Aloc *
          maxEntryNormRect hLocal hLocal AlocInv)
        = (maxEntryNorm hLocal Gloc) ^ 2 *
            (maxEntryNormRect hLocal hLocal AlocInv /
              maxEntryNormRect hLocal hLocal Aloc) := hLocalEq
    _ ≤ (maxEntryNorm hGlobal Gglob) ^ 2 *
          (maxEntryNormRect hGlobal hGlobal AglobInv /
            maxEntryNormRect hGlobal hGlobal Aglob) := hProduct
    _ = (growthFactorEntry hGlobal Aglob Gglob hAglobPos) ^ 2 *
        (maxEntryNormRect hGlobal hGlobal Aglob *
          maxEntryNormRect hGlobal hGlobal AglobInv) := hGlobalEq.symm

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    a strong base/inverse comparison implies the cross-multiplied inverse-ratio
    comparison used by the recursive tail-budget transport.

    This is deliberately conditional.  The hypothesis
    `||A_global||_max <= ||A_local||_max` is stronger than ordinary containment
    in the direction needed for denominators, and is not asserted here to hold
    for Schur tails automatically. -/
theorem maxEntryNormRect_inverse_ratio_of_base_le_and_inverse_le
    {nLocal nGlobal : ℕ} (hLocal : 0 < nLocal) (hGlobal : 0 < nGlobal)
    (Aloc AlocInv : Fin nLocal → Fin nLocal → ℝ)
    (Aglob AglobInv : Fin nGlobal → Fin nGlobal → ℝ)
    (hBase :
      maxEntryNormRect hGlobal hGlobal Aglob ≤
        maxEntryNormRect hLocal hLocal Aloc)
    (hInv :
      maxEntryNormRect hLocal hLocal AlocInv ≤
        maxEntryNormRect hGlobal hGlobal AglobInv) :
    maxEntryNormRect hLocal hLocal AlocInv *
        maxEntryNormRect hGlobal hGlobal Aglob ≤
      maxEntryNormRect hGlobal hGlobal AglobInv *
        maxEntryNormRect hLocal hLocal Aloc := by
  have hGlobBaseNonneg :
      0 ≤ maxEntryNormRect hGlobal hGlobal Aglob :=
    maxEntryNormRect_nonneg hGlobal hGlobal Aglob
  have hGlobInvNonneg :
      0 ≤ maxEntryNormRect hGlobal hGlobal AglobInv :=
    maxEntryNormRect_nonneg hGlobal hGlobal AglobInv
  have hStepInv :
      maxEntryNormRect hLocal hLocal AlocInv *
          maxEntryNormRect hGlobal hGlobal Aglob ≤
        maxEntryNormRect hGlobal hGlobal AglobInv *
          maxEntryNormRect hGlobal hGlobal Aglob :=
    mul_le_mul_of_nonneg_right hInv hGlobBaseNonneg
  have hStepBase :
      maxEntryNormRect hGlobal hGlobal AglobInv *
          maxEntryNormRect hGlobal hGlobal Aglob ≤
        maxEntryNormRect hGlobal hGlobal AglobInv *
          maxEntryNormRect hLocal hLocal Aloc :=
    mul_le_mul_of_nonneg_left hBase hGlobInvNonneg
  exact le_trans hStepInv hStepBase

/-- Higham, 2nd ed., Chapter 13, equations (13.22)--(13.23):
    scalar local-to-global `rho^2 kappa` budget comparison from growth
    domination plus a strong base/inverse comparison.

    The theorem factors through
    `growthFactorEntry_sq_kappa_budget_le_of_growth_le_inv_ratio`, so the only
    new mathematics is the elementary product-order bridge from
    `maxEntryNormRect_inverse_ratio_of_base_le_and_inverse_le`. -/
theorem growthFactorEntry_sq_kappa_budget_le_of_growth_le_base_inverse
    {nLocal nGlobal : ℕ} (hLocal : 0 < nLocal) (hGlobal : 0 < nGlobal)
    (Aloc Gloc AlocInv : Fin nLocal → Fin nLocal → ℝ)
    (Aglob Gglob AglobInv : Fin nGlobal → Fin nGlobal → ℝ)
    (hAlocPos : 0 < maxEntryNorm hLocal Aloc)
    (hAglobPos : 0 < maxEntryNorm hGlobal Aglob)
    (hGrowth : maxEntryNorm hLocal Gloc ≤ maxEntryNorm hGlobal Gglob)
    (hBase :
      maxEntryNormRect hGlobal hGlobal Aglob ≤
        maxEntryNormRect hLocal hLocal Aloc)
    (hInv :
      maxEntryNormRect hLocal hLocal AlocInv ≤
        maxEntryNormRect hGlobal hGlobal AglobInv) :
    (growthFactorEntry hLocal Aloc Gloc hAlocPos) ^ 2 *
        (maxEntryNormRect hLocal hLocal Aloc *
          maxEntryNormRect hLocal hLocal AlocInv) ≤
      (growthFactorEntry hGlobal Aglob Gglob hAglobPos) ^ 2 *
        (maxEntryNormRect hGlobal hGlobal Aglob *
          maxEntryNormRect hGlobal hGlobal AglobInv) := by
  exact
    growthFactorEntry_sq_kappa_budget_le_of_growth_le_inv_ratio
      hLocal hGlobal Aloc Gloc AlocInv Aglob Gglob AglobInv
      hAlocPos hAglobPos hGrowth
      (maxEntryNormRect_inverse_ratio_of_base_le_and_inverse_le
        hLocal hGlobal Aloc AlocInv Aglob AglobInv hBase hInv)

/-- Constant nonnegative matrices have max-entry norm equal to the constant. -/
lemma maxEntryNorm_const_nonneg {n : ℕ} (hn : 0 < n) (c : ℝ)
    (hc : 0 ≤ c) :
    maxEntryNorm hn (fun (_ : Fin n) (_ : Fin n) => c) = c := by
  apply le_antisymm
  · have hrect :
        maxEntryNormRect hn hn (fun (_ : Fin n) (_ : Fin n) => c) ≤ c := by
      apply maxEntryNormRect_le_of_entry_abs_le
      intro i j
      simp [abs_of_nonneg hc]
    simpa [maxEntryNormRect_eq_maxEntryNorm hn] using hrect
  · have hentry :=
      entry_le_maxEntryNorm hn (fun (_ : Fin n) (_ : Fin n) => c)
        (⟨0, hn⟩ : Fin n) (⟨0, hn⟩ : Fin n)
    simpa [abs_of_nonneg hc] using hentry

end NumStability
