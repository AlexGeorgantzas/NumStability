import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum

/-!
# Source.Higham.Chapter13.Problem04.LocalNormBounds

This module formalizes the source-facing Chapter 13 statements for
`Problem04.LocalNormBounds`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    max-entry-norm product bridge for the lower-left solve
    `A₂₁ A₁₁⁻¹`.

    The source exercise sets `||A|| := max_ij |a_ij|`.  This theorem proves
    the exact max-entry product propagation once the growth-factor route has
    supplied `||A₂₁||_max <= rho ||A||`, the principal-inverse route has
    supplied `||A₁₁⁻¹||_max <= ||A⁻¹||`, and the displayed condition-number
    product has supplied `||A|| ||A⁻¹|| <= kappa(A)`. -/
theorem higham13_problem13_4_A21A11inv_maxEntryNormRect_from_growth_certificates
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (A21 : Fin s → Fin r → ℝ) (A11inv : Fin r → Fin r → ℝ)
    {normA normAinv rho kappaA : ℝ} (n : ℕ)
    (hRho : 0 ≤ rho) (hKappa : 0 ≤ kappaA)
    (hrn : (r : ℝ) ≤ (n : ℝ))
    (hA21_bound : maxEntryNormRect hs hr A21 ≤ rho * normA)
    (hA11inv_bound : maxEntryNormRect hr hr A11inv ≤ normAinv)
    (hkappa : normA * normAinv ≤ kappaA) :
    maxEntryNormRect hs hr (rectMatMul A21 A11inv) ≤
      (n : ℝ) * rho * kappaA := by
  let normA21 : ℝ := maxEntryNormRect hs hr A21
  let normA11inv : ℝ := maxEntryNormRect hr hr A11inv
  have hProduct :
      maxEntryNormRect hs hr (rectMatMul A21 A11inv) ≤
        (r : ℝ) * normA21 * normA11inv := by
    simpa [normA21, normA11inv] using
      maxEntryNormRect_rectMatMul_le hs hr hr A21 A11inv
  have hNormA21_nonneg : 0 ≤ normA21 :=
    maxEntryNormRect_nonneg hs hr A21
  have hNormA11inv_nonneg : 0 ≤ normA11inv :=
    maxEntryNormRect_nonneg hr hr A11inv
  have hRhoNormA_nonneg : 0 ≤ rho * normA :=
    le_trans hNormA21_nonneg (by simpa [normA21] using hA21_bound)
  have hAinv_nonneg : 0 ≤ normAinv :=
    le_trans hNormA11inv_nonneg (by simpa [normA11inv] using hA11inv_bound)
  have hNormProduct :
      normA21 * normA11inv ≤ rho * kappaA := by
    have hmul :
        normA21 * normA11inv ≤ (rho * normA) * normAinv :=
      mul_le_mul
        (by simpa [normA21] using hA21_bound)
        (by simpa [normA11inv] using hA11inv_bound)
        hNormA11inv_nonneg hRhoNormA_nonneg
    calc
      normA21 * normA11inv ≤ (rho * normA) * normAinv := hmul
      _ = rho * (normA * normAinv) := by ring
      _ ≤ rho * kappaA := mul_le_mul_of_nonneg_left hkappa hRho
  have hScaleR :
      (r : ℝ) * normA21 * normA11inv ≤ (r : ℝ) * (rho * kappaA) := by
    calc
      (r : ℝ) * normA21 * normA11inv = (r : ℝ) * (normA21 * normA11inv) := by
        ring
      _ ≤ (r : ℝ) * (rho * kappaA) :=
        mul_le_mul_of_nonneg_left hNormProduct (Nat.cast_nonneg r)
  have hScaleN :
      (r : ℝ) * (rho * kappaA) ≤ (n : ℝ) * (rho * kappaA) :=
    mul_le_mul_of_nonneg_right hrn (mul_nonneg hRho hKappa)
  calc
    maxEntryNormRect hs hr (rectMatMul A21 A11inv)
        ≤ (r : ℝ) * normA21 * normA11inv := hProduct
    _ ≤ (r : ℝ) * (rho * kappaA) := hScaleR
    _ ≤ (n : ℝ) * (rho * kappaA) := hScaleN
    _ = (n : ℝ) * rho * kappaA := by ring

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    entrywise version of the max-entry lower-left solve bridge. -/
theorem higham13_problem13_4_A21A11inv_maxEntryNormRect_from_entrywise_A21_bound
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (A21 : Fin s → Fin r → ℝ) (A11inv : Fin r → Fin r → ℝ)
    {normA normAinv rho kappaA : ℝ} (n : ℕ)
    (hRho : 0 ≤ rho) (hKappa : 0 ≤ kappaA)
    (hrn : (r : ℝ) ≤ (n : ℝ))
    (hA21_entry : ∀ i : Fin s, ∀ j : Fin r, |A21 i j| ≤ rho * normA)
    (hA11inv_bound : maxEntryNormRect hr hr A11inv ≤ normAinv)
    (hkappa : normA * normAinv ≤ kappaA) :
    maxEntryNormRect hs hr (rectMatMul A21 A11inv) ≤
      (n : ℝ) * rho * kappaA :=
  higham13_problem13_4_A21A11inv_maxEntryNormRect_from_growth_certificates
    hr hs A21 A11inv n hRho hKappa hrn
    (maxEntryNormRect_le_of_entry_abs_le hs hr A21 (rho * normA) hA21_entry)
    hA11inv_bound hkappa

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    the lower-left block `A₂₁` inherits a max-entry certificate from a full
    partitioned-matrix entrywise bound.  The source growth factor only weakens
    the entrywise max bound when `rho_n >= 1`. -/
theorem higham13_problem13_4_A21_maxEntryNormRect_of_full_entry_bound
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (A : (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    {normA rho : ℝ}
    (hRho_ge_one : 1 ≤ rho)
    (hA_entry : ∀ i j : Fin r ⊕ Fin s, |A i j| ≤ normA)
    (hA21 : A21 = fun (i : Fin s) (j : Fin r) =>
      A (Sum.inr i) (Sum.inl j)) :
    maxEntryNormRect hs hr A21 ≤ rho * normA := by
  let i0 : Fin r := ⟨0, hr⟩
  have hNormA_nonneg : 0 ≤ normA :=
    le_trans (abs_nonneg (A (Sum.inl i0) (Sum.inl i0)))
      (hA_entry (Sum.inl i0) (Sum.inl i0))
  have hA21_entry : ∀ i : Fin s, ∀ j : Fin r, |A21 i j| ≤ normA := by
    intro i j
    calc
      |A21 i j| = |A (Sum.inr i) (Sum.inl j)| := by rw [hA21]
      _ ≤ normA := hA_entry (Sum.inr i) (Sum.inl j)
  have hA21_norm : maxEntryNormRect hs hr A21 ≤ normA :=
    maxEntryNormRect_le_of_entry_abs_le hs hr A21 normA hA21_entry
  have hscale : normA ≤ rho * normA := by
    calc
      normA = (1 : ℝ) * normA := by ring
      _ ≤ rho * normA :=
        mul_le_mul_of_nonneg_right hRho_ge_one hNormA_nonneg
  exact le_trans hA21_norm hscale

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    max-entry lower-left solve bridge where the `A₂₁` certificate is inherited
    from the full partitioned matrix's entrywise max bound. -/
theorem higham13_problem13_4_A21A11inv_maxEntryNormRect_from_full_entry_bound
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (A : (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → ℝ)
    (A21 : Fin s → Fin r → ℝ) (A11inv : Fin r → Fin r → ℝ)
    {normA normAinv rho kappaA : ℝ} (n : ℕ)
    (hRho_ge_one : 1 ≤ rho) (hKappa : 0 ≤ kappaA)
    (hrn : (r : ℝ) ≤ (n : ℝ))
    (hA_entry : ∀ i j : Fin r ⊕ Fin s, |A i j| ≤ normA)
    (hA21 : A21 = fun (i : Fin s) (j : Fin r) =>
      A (Sum.inr i) (Sum.inl j))
    (hA11inv_bound : maxEntryNormRect hr hr A11inv ≤ normAinv)
    (hkappa : normA * normAinv ≤ kappaA) :
    maxEntryNormRect hs hr (rectMatMul A21 A11inv) ≤
      (n : ℝ) * rho * kappaA :=
  higham13_problem13_4_A21A11inv_maxEntryNormRect_from_growth_certificates
    hr hs A21 A11inv n (le_trans zero_le_one hRho_ge_one) hKappa hrn
    (higham13_problem13_4_A21_maxEntryNormRect_of_full_entry_bound
      hr hs A A21 hRho_ge_one hA_entry hA21)
    hA11inv_bound hkappa

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    if a supplied `A₁₁⁻¹` is the upper-left block of a supplied full inverse,
    then it inherits the full inverse's max-entry bound.

    This is a certificate bridge only; for the source Problem 13.4, one still
    has to prove that the displayed `A₁₁⁻¹` is controlled by the chosen inverse
    certificate. -/
theorem higham13_problem13_4_A11inv_maxEntryNormRect_of_full_inverse_entry_bound
    {r s : ℕ} (hr : 0 < r)
    (Ainv : (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → ℝ)
    (A11inv : Fin r → Fin r → ℝ)
    {normAinv : ℝ}
    (hAinv_entry : ∀ i j : Fin r ⊕ Fin s, |Ainv i j| ≤ normAinv)
    (hA11inv : A11inv = fun (i : Fin r) (j : Fin r) =>
      Ainv (Sum.inl i) (Sum.inl j)) :
    maxEntryNormRect hr hr A11inv ≤ normAinv := by
  have hA11inv_entry : ∀ i : Fin r, ∀ j : Fin r, |A11inv i j| ≤ normAinv := by
    intro i j
    calc
      |A11inv i j| = |Ainv (Sum.inl i) (Sum.inl j)| := by rw [hA11inv]
      _ ≤ normAinv := hAinv_entry (Sum.inl i) (Sum.inl j)
  exact maxEntryNormRect_le_of_entry_abs_le hr hr A11inv normAinv hA11inv_entry

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    the displayed inverse block `A₁₁⁻¹` has the required max-entry certificate
    once that certificate is supplied entrywise for the displayed inverse
    itself.

    This avoids routing the source object through an upper-left full-inverse
    block equality.  The remaining source obligation is proving the entrywise
    certificate from the Problem 13.4 growth/inverse hypotheses. -/
theorem higham13_problem13_4_A11inv_maxEntryNormRect_from_entrywise_bound
    {r : ℕ} (hr : 0 < r)
    (A11inv : Fin r → Fin r → ℝ)
    {normAinv : ℝ}
    (hA11inv_entry : ∀ i : Fin r, ∀ j : Fin r, |A11inv i j| ≤ normAinv) :
    maxEntryNormRect hr hr A11inv ≤ normAinv :=
  maxEntryNormRect_le_of_entry_abs_le hr hr A11inv normAinv hA11inv_entry

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    max-entry lower-left solve bridge using full-block entrywise certificates
    for `A` and for a supplied full inverse.

    This discharges the `A₂₁` and upper-left inverse-block max-entry
    inheritance steps from explicit block equalities.  It remains a conditional
    certificate theorem: the source theorem still needs the genuine
    growth-factor/GE argument that supplies the appropriate inverse certificate
    for the particular `A₁₁⁻¹` in the partition. -/
theorem higham13_problem13_4_A21A11inv_maxEntryNormRect_from_full_block_entry_bound
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (A Ainv : (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → ℝ)
    (A21 : Fin s → Fin r → ℝ) (A11inv : Fin r → Fin r → ℝ)
    {normA normAinv rho kappaA : ℝ} (n : ℕ)
    (hRho_ge_one : 1 ≤ rho) (hKappa : 0 ≤ kappaA)
    (hrn : (r : ℝ) ≤ (n : ℝ))
    (hA_entry : ∀ i j : Fin r ⊕ Fin s, |A i j| ≤ normA)
    (hA21 : A21 = fun (i : Fin s) (j : Fin r) =>
      A (Sum.inr i) (Sum.inl j))
    (hAinv_entry : ∀ i j : Fin r ⊕ Fin s, |Ainv i j| ≤ normAinv)
    (hA11inv : A11inv = fun (i : Fin r) (j : Fin r) =>
      Ainv (Sum.inl i) (Sum.inl j))
    (hkappa : normA * normAinv ≤ kappaA) :
    maxEntryNormRect hs hr (rectMatMul A21 A11inv) ≤
      (n : ℝ) * rho * kappaA :=
  higham13_problem13_4_A21A11inv_maxEntryNormRect_from_full_entry_bound
    hr hs A A21 A11inv n hRho_ge_one hKappa hrn hA_entry hA21
    (higham13_problem13_4_A11inv_maxEntryNormRect_of_full_inverse_entry_bound
      hr Ainv A11inv hAinv_entry hA11inv)
    hkappa

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    lower-left solve bridge using the actual displayed inverse block
    `A₁₁⁻¹`.

    The source exercise sets `||A|| := max_ij |a_ij|`.  This theorem combines
    the full-matrix entrywise certificate for `A₂₁` with an entrywise
    certificate for the displayed `A₁₁⁻¹`, then feeds the existing max-entry
    product bridge.  It is still conditional on the hard source step that
    proves the displayed-inverse entrywise certificate. -/
theorem higham13_problem13_4_A21A11inv_maxEntryNormRect_from_displayed_inverse_entry_bound
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (A : (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → ℝ)
    (A21 : Fin s → Fin r → ℝ) (A11inv : Fin r → Fin r → ℝ)
    {normA normAinv rho kappaA : ℝ} (n : ℕ)
    (hRho_ge_one : 1 ≤ rho) (hKappa : 0 ≤ kappaA)
    (hrn : (r : ℝ) ≤ (n : ℝ))
    (hA_entry : ∀ i j : Fin r ⊕ Fin s, |A i j| ≤ normA)
    (hA21 : A21 = fun (i : Fin s) (j : Fin r) =>
      A (Sum.inr i) (Sum.inl j))
    (hA11inv_entry : ∀ i : Fin r, ∀ j : Fin r, |A11inv i j| ≤ normAinv)
    (hkappa : normA * normAinv ≤ kappaA) :
    maxEntryNormRect hs hr (rectMatMul A21 A11inv) ≤
      (n : ℝ) * rho * kappaA :=
  higham13_problem13_4_A21A11inv_maxEntryNormRect_from_full_entry_bound
    hr hs A A21 A11inv n hRho_ge_one hKappa hrn hA_entry hA21
    (higham13_problem13_4_A11inv_maxEntryNormRect_from_entrywise_bound
      hr A11inv hA11inv_entry)
    hkappa

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    the lower-left block `A₂₁` inherits a rectangular operator-2 certificate
    from the full block matrix.  The source growth factor `ρₙ` only weakens the
    inherited full-matrix bound when `ρₙ ≥ 1`. -/
theorem higham13_problem13_4_A21_rectOpNorm2Le_of_full_operator_bound
    {r s : ℕ} [Nonempty (Fin r)]
    (A : (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → ℝ)
    {normA rho : ℝ}
    (hRho_ge_one : 1 ≤ rho)
    (hA : finiteOpNorm2Le A normA) :
    rectOpNorm2Le (fun (i : Fin s) (j : Fin r) => A (Sum.inr i) (Sum.inl j))
      (rho * normA) := by
  classical
  let i0 : Fin r := Classical.choice (inferInstance : Nonempty (Fin r))
  haveI : Nonempty (Fin r ⊕ Fin s) := ⟨Sum.inl i0⟩
  have hNormA_nonneg : 0 ≤ normA := finiteOpNorm2Le_radius_nonneg A hA
  have hscale : normA ≤ rho * normA := by
    calc
      normA = (1 : ℝ) * normA := by ring
      _ ≤ rho * normA := mul_le_mul_of_nonneg_right hRho_ge_one hNormA_nonneg
  exact rectOpNorm2Le_mono hscale
    (rectOpNorm2Le_sumInr_sumInl_of_finiteOpNorm2Le A hA)

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    source-facing equality wrapper for the lower-left block operator
    certificate inherited from the full matrix. -/
theorem higham13_problem13_4_A21_rectOpNorm2Le_of_full_operator_bound_eq
    {r s : ℕ} [Nonempty (Fin r)]
    (A : (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    {normA rho : ℝ}
    (hA21 : A21 =
      fun (i : Fin s) (j : Fin r) => A (Sum.inr i) (Sum.inl j))
    (hRho_ge_one : 1 ≤ rho)
    (hA : finiteOpNorm2Le A normA) :
    rectOpNorm2Le A21 (rho * normA) := by
  rw [hA21]
  exact higham13_problem13_4_A21_rectOpNorm2Le_of_full_operator_bound
    A hRho_ge_one hA

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    the upper-left inverse principal block inherits a rectangular operator-2
    certificate from the full inverse matrix. -/
theorem higham13_problem13_4_A11inv_rectOpNorm2Le_of_full_inverse_block
    {r s : ℕ}
    (Ainv : (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → ℝ)
    {normAinv : ℝ}
    (hAinv : finiteOpNorm2Le Ainv normAinv) :
    rectOpNorm2Le (fun i j : Fin r => Ainv (Sum.inl i) (Sum.inl j)) normAinv :=
  rectOpNorm2Le_of_finiteOpNorm2Le _
    (finiteOpNorm2Le_sumInl_principal Ainv hAinv)

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    source-facing equality wrapper for the upper-left inverse principal block
    operator certificate inherited from the full inverse matrix. -/
theorem higham13_problem13_4_A11inv_rectOpNorm2Le_of_full_inverse_block_eq
    {r s : ℕ}
    (Ainv : (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → ℝ)
    (A11inv : Fin r → Fin r → ℝ)
    {normAinv : ℝ}
    (hA11inv : A11inv = fun i j : Fin r => Ainv (Sum.inl i) (Sum.inl j))
    (hAinv : finiteOpNorm2Le Ainv normAinv) :
    rectOpNorm2Le A11inv normAinv := by
  rw [hA11inv]
  exact higham13_problem13_4_A11inv_rectOpNorm2Le_of_full_inverse_block
    Ainv hAinv

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    certificate-level bridge for the displayed lower-left solve bound
    `‖A₂₁ A₁₁⁻¹‖ ≤ n ρₙ κ(A)`.

    The theorem proves the product/norm propagation once separate operator
    certificates have supplied `‖A₂₁‖ ≤ ρₙ ‖A‖`, `‖A₁₁⁻¹‖ ≤ ‖A⁻¹‖`, and the
    condition-number product `‖A‖‖A⁻¹‖ ≤ κ(A)`.  It does not prove those
    growth-factor or inverse-principal-block certificates. -/
theorem higham13_problem13_4_A21A11inv_rectOpNorm2Le_from_growth_certificates
    {r s : ℕ} [Nonempty (Fin r)]
    (A21 : Fin s → Fin r → ℝ) (A11inv : Fin r → Fin r → ℝ)
    {normA21 normA11inv normA normAinv rho kappaA : ℝ} (n : ℕ)
    (hNormA_nonneg : 0 ≤ normA) (hRho : 0 ≤ rho) (hKappa : 0 ≤ kappaA)
    (hn : 1 ≤ (n : ℝ))
    (hA21 : rectOpNorm2Le A21 normA21)
    (hA11inv : rectOpNorm2Le A11inv normA11inv)
    (hA21_bound : normA21 ≤ rho * normA)
    (hA11inv_bound : normA11inv ≤ normAinv)
    (hkappa : normA * normAinv ≤ kappaA) :
    rectOpNorm2Le (rectMatMul A21 A11inv) ((n : ℝ) * rho * kappaA) := by
  have hNormA21_nonneg : 0 ≤ normA21 :=
    rectOpNorm2Le_radius_nonneg A21 hA21
  have hNormA11inv_nonneg : 0 ≤ normA11inv :=
    rectOpNorm2Le_radius_nonneg A11inv hA11inv
  have hProductCert :
      rectOpNorm2Le (rectMatMul A21 A11inv) (normA21 * normA11inv) :=
    rectOpNorm2Le_rectMatMul A21 A11inv hNormA21_nonneg hA21 hA11inv
  have hAinv_nonneg : 0 ≤ normAinv :=
    le_trans hNormA11inv_nonneg hA11inv_bound
  have hSolveProduct :
      normA21 * normA11inv ≤ rho * kappaA := by
    have hmul :
        normA21 * normA11inv ≤ (rho * normA) * normAinv :=
      mul_le_mul hA21_bound hA11inv_bound hNormA11inv_nonneg
        (mul_nonneg hRho hNormA_nonneg)
    calc
      normA21 * normA11inv ≤ (rho * normA) * normAinv := hmul
      _ = rho * (normA * normAinv) := by ring
      _ ≤ rho * kappaA := mul_le_mul_of_nonneg_left hkappa hRho
  have hSourceProduct :
      rho * kappaA ≤ (n : ℝ) * rho * kappaA := by
    have hscale :
        rho * kappaA ≤ (n : ℝ) * (rho * kappaA) := by
      calc
        rho * kappaA = (1 : ℝ) * (rho * kappaA) := by ring
        _ ≤ (n : ℝ) * (rho * kappaA) :=
          mul_le_mul_of_nonneg_right hn (mul_nonneg hRho hKappa)
    simpa [mul_assoc] using hscale
  exact rectOpNorm2Le_mono (le_trans hSolveProduct hSourceProduct) hProductCert

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    lower-left solve certificate using the full-block operator certificate for
    `A`, while keeping the inverse-principal-block certificate explicit.

    This discharges the source-shaped `‖A₂₁‖ ≤ ρₙ‖A‖` premise from the full
    matrix bound and `ρₙ ≥ 1`; it deliberately leaves the hard
    `‖A₁₁⁻¹‖ ≤ ‖A⁻¹‖`/condition-number part as a visible hypothesis. -/
theorem higham13_problem13_4_A21A11inv_rectOpNorm2Le_from_full_A_certificate
    {r s : ℕ} [Nonempty (Fin r)]
    (A : (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → ℝ)
    (A21 : Fin s → Fin r → ℝ) (A11inv : Fin r → Fin r → ℝ)
    {normA normA11inv normAinv rho kappaA : ℝ} (n : ℕ)
    (hRho_ge_one : 1 ≤ rho)
    (hn : 1 ≤ (n : ℝ))
    (hA21 : A21 =
      fun (i : Fin s) (j : Fin r) => A (Sum.inr i) (Sum.inl j))
    (hA : finiteOpNorm2Le A normA)
    (hA11inv : rectOpNorm2Le A11inv normA11inv)
    (hA11inv_bound : normA11inv ≤ normAinv)
    (hkappa : normA * normAinv ≤ kappaA) :
    rectOpNorm2Le (rectMatMul A21 A11inv) ((n : ℝ) * rho * kappaA) := by
  classical
  let i0 : Fin r := Classical.choice (inferInstance : Nonempty (Fin r))
  haveI : Nonempty (Fin r ⊕ Fin s) := ⟨Sum.inl i0⟩
  have hNormA_nonneg : 0 ≤ normA := finiteOpNorm2Le_radius_nonneg A hA
  have hNormA11inv_nonneg : 0 ≤ normA11inv :=
    rectOpNorm2Le_radius_nonneg A11inv hA11inv
  have hNormAinv_nonneg : 0 ≤ normAinv :=
    le_trans hNormA11inv_nonneg hA11inv_bound
  have hRho_nonneg : 0 ≤ rho := le_trans zero_le_one hRho_ge_one
  have hKappa_nonneg : 0 ≤ kappaA :=
    le_trans (mul_nonneg hNormA_nonneg hNormAinv_nonneg) hkappa
  exact
    higham13_problem13_4_A21A11inv_rectOpNorm2Le_from_growth_certificates
      (A21 := A21) (A11inv := A11inv) (n := n)
      (hNormA_nonneg := hNormA_nonneg) (hRho := hRho_nonneg)
      (hKappa := hKappa_nonneg) (hn := hn)
      (hA21 :=
        higham13_problem13_4_A21_rectOpNorm2Le_of_full_operator_bound_eq
          A A21 hA21 hRho_ge_one hA)
      (hA11inv := hA11inv)
      (hA21_bound := le_rfl) (hA11inv_bound := hA11inv_bound)
      (hkappa := hkappa)

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    lower-left solve certificate using full-block operator certificates for
    `A` and `A⁻¹`.

    Compared with
    `higham13_problem13_4_A21A11inv_rectOpNorm2Le_from_growth_certificates`,
    this theorem derives the `A₂₁` and `A₁₁⁻¹` operator certificates from the
    full matrix and full inverse.  The remaining source obligations are the
    full inverse certificate, `ρₙ ≥ 1`, and the condition-number product. -/
theorem higham13_problem13_4_A21A11inv_rectOpNorm2Le_from_full_block_certificates
    {r s : ℕ} [Nonempty (Fin r)]
    (A Ainv : (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → ℝ)
    (A21 : Fin s → Fin r → ℝ) (A11inv : Fin r → Fin r → ℝ)
    {normA normAinv rho kappaA : ℝ} (n : ℕ)
    (hRho_ge_one : 1 ≤ rho)
    (hn : 1 ≤ (n : ℝ))
    (hA21 : A21 =
      fun (i : Fin s) (j : Fin r) => A (Sum.inr i) (Sum.inl j))
    (hA11inv : A11inv = fun i j : Fin r => Ainv (Sum.inl i) (Sum.inl j))
    (hA : finiteOpNorm2Le A normA)
    (hAinv : finiteOpNorm2Le Ainv normAinv)
    (hkappa : normA * normAinv ≤ kappaA) :
    rectOpNorm2Le (rectMatMul A21 A11inv) ((n : ℝ) * rho * kappaA) := by
  classical
  let i0 : Fin r := Classical.choice (inferInstance : Nonempty (Fin r))
  haveI : Nonempty (Fin r ⊕ Fin s) := ⟨Sum.inl i0⟩
  have hNormA_nonneg : 0 ≤ normA := finiteOpNorm2Le_radius_nonneg A hA
  have hNormAinv_nonneg : 0 ≤ normAinv :=
    finiteOpNorm2Le_radius_nonneg Ainv hAinv
  have hRho_nonneg : 0 ≤ rho := le_trans zero_le_one hRho_ge_one
  have hKappa_nonneg : 0 ≤ kappaA :=
    le_trans (mul_nonneg hNormA_nonneg hNormAinv_nonneg) hkappa
  exact
    higham13_problem13_4_A21A11inv_rectOpNorm2Le_from_growth_certificates
      (A21 := A21) (A11inv := A11inv) (n := n)
      (hNormA_nonneg := hNormA_nonneg) (hRho := hRho_nonneg)
      (hKappa := hKappa_nonneg) (hn := hn)
      (hA21 :=
        higham13_problem13_4_A21_rectOpNorm2Le_of_full_operator_bound_eq
          A A21 hA21 hRho_ge_one hA)
      (hA11inv :=
        higham13_problem13_4_A11inv_rectOpNorm2Le_of_full_inverse_block_eq
          Ainv A11inv hA11inv hAinv)
      (hA21_bound := le_rfl) (hA11inv_bound := le_rfl) (hkappa := hkappa)

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    max-entry certificate bridge for the Schur-complement condition-number
    bound `κ(S) ≤ ρₙ κ(A)`.

    The source exercise sets `||M|| := max_ij |m_ij|`.  This theorem proves the
    scalar condition-product propagation once `||S||_max ≤ ρₙ ||A||`,
    `||S⁻¹||_max ≤ ||A⁻¹||`, and `||A|| ||A⁻¹|| ≤ κ(A)` have been supplied. -/
theorem higham13_problem13_4_schur_kappa_maxEntryNormRect_from_certificates
    {s : ℕ} (hs : 0 < s)
    (S Sinv : Fin s → Fin s → ℝ)
    {normA normAinv rho kappaA : ℝ}
    (hRho : 0 ≤ rho)
    (hS_bound : maxEntryNormRect hs hs S ≤ rho * normA)
    (hSinv_bound : maxEntryNormRect hs hs Sinv ≤ normAinv)
    (hkappa : normA * normAinv ≤ kappaA) :
    maxEntryNormRect hs hs S * maxEntryNormRect hs hs Sinv ≤
      rho * kappaA := by
  have hSinv_nonneg : 0 ≤ maxEntryNormRect hs hs Sinv :=
    maxEntryNormRect_nonneg hs hs Sinv
  have hSupper_nonneg : 0 ≤ rho * normA :=
    le_trans (maxEntryNormRect_nonneg hs hs S) hS_bound
  have hmul :
      maxEntryNormRect hs hs S * maxEntryNormRect hs hs Sinv ≤
        (rho * normA) * normAinv :=
    mul_le_mul hS_bound hSinv_bound hSinv_nonneg hSupper_nonneg
  calc
    maxEntryNormRect hs hs S * maxEntryNormRect hs hs Sinv
        ≤ (rho * normA) * normAinv := hmul
    _ = rho * (normA * normAinv) := by ring
    _ ≤ rho * kappaA := mul_le_mul_of_nonneg_left hkappa hRho

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    max-entry Schur-complement condition bridge where the Schur norm
    certificate is supplied entrywise by the growth-factor route. -/
theorem higham13_problem13_4_schur_kappa_maxEntryNormRect_from_entrywise_schur_bound
    {s : ℕ} (hs : 0 < s)
    (S Sinv : Fin s → Fin s → ℝ)
    {normA normAinv rho kappaA : ℝ}
    (hRho : 0 ≤ rho)
    (hS_entry : ∀ i : Fin s, ∀ j : Fin s, |S i j| ≤ rho * normA)
    (hSinv_bound : maxEntryNormRect hs hs Sinv ≤ normAinv)
    (hkappa : normA * normAinv ≤ kappaA) :
    maxEntryNormRect hs hs S * maxEntryNormRect hs hs Sinv ≤
      rho * kappaA :=
  higham13_problem13_4_schur_kappa_maxEntryNormRect_from_certificates
    hs S Sinv hRho
    (maxEntryNormRect_le_of_entry_abs_le hs hs S (rho * normA) hS_entry)
    hSinv_bound hkappa

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    if `S⁻¹` is the lower-right block of a supplied full inverse, then it
    inherits the full inverse's max-entry bound. -/
theorem higham13_problem13_4_Sinv_maxEntryNormRect_of_full_inverse_entry_bound
    {r s : ℕ} (hs : 0 < s)
    (Ainv : (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → ℝ)
    (Sinv : Fin s → Fin s → ℝ)
    {normAinv : ℝ}
    (hAinv_entry : ∀ i j : Fin r ⊕ Fin s, |Ainv i j| ≤ normAinv)
    (hSinv : Sinv = fun (i : Fin s) (j : Fin s) =>
      Ainv (Sum.inr i) (Sum.inr j)) :
    maxEntryNormRect hs hs Sinv ≤ normAinv := by
  have hSinv_entry : ∀ i : Fin s, ∀ j : Fin s, |Sinv i j| ≤ normAinv := by
    intro i j
    calc
      |Sinv i j| = |Ainv (Sum.inr i) (Sum.inr j)| := by rw [hSinv]
      _ ≤ normAinv := hAinv_entry (Sum.inr i) (Sum.inr j)
  exact maxEntryNormRect_le_of_entry_abs_le hs hs Sinv normAinv hSinv_entry

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    the displayed Schur inverse `S⁻¹` has the required max-entry certificate
    once that certificate is supplied entrywise for `S⁻¹` itself. -/
theorem higham13_problem13_4_Sinv_maxEntryNormRect_from_entrywise_bound
    {s : ℕ} (hs : 0 < s)
    (Sinv : Fin s → Fin s → ℝ)
    {normAinv : ℝ}
    (hSinv_entry : ∀ i : Fin s, ∀ j : Fin s, |Sinv i j| ≤ normAinv) :
    maxEntryNormRect hs hs Sinv ≤ normAinv :=
  maxEntryNormRect_le_of_entry_abs_le hs hs Sinv normAinv hSinv_entry

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    source max-entry Schur condition bridge using a full-inverse lower-right
    block certificate for `S⁻¹`.  The remaining source obligation is the block
    inverse identity that identifies this lower-right block with `S⁻¹`. -/
theorem higham13_problem13_4_schur_kappa_maxEntryNormRect_from_full_inverse_entry_bound
    {r s : ℕ} (hs : 0 < s)
    (Ainv : (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → ℝ)
    (S Sinv : Fin s → Fin s → ℝ)
    {normA normAinv rho kappaA : ℝ}
    (hRho : 0 ≤ rho)
    (hS_entry : ∀ i : Fin s, ∀ j : Fin s, |S i j| ≤ rho * normA)
    (hAinv_entry : ∀ i j : Fin r ⊕ Fin s, |Ainv i j| ≤ normAinv)
    (hSinv : Sinv = fun (i : Fin s) (j : Fin s) =>
      Ainv (Sum.inr i) (Sum.inr j))
    (hkappa : normA * normAinv ≤ kappaA) :
    maxEntryNormRect hs hs S * maxEntryNormRect hs hs Sinv ≤
      rho * kappaA :=
  higham13_problem13_4_schur_kappa_maxEntryNormRect_from_entrywise_schur_bound
    hs S Sinv hRho hS_entry
    (higham13_problem13_4_Sinv_maxEntryNormRect_of_full_inverse_entry_bound
      hs Ainv Sinv hAinv_entry hSinv)
    hkappa

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    Schur condition-product bridge using entrywise certificates for the actual
    displayed `S` and `S⁻¹`.

    This is the source-object variant of
    `higham13_problem13_4_schur_kappa_maxEntryNormRect_from_full_inverse_entry_bound`.
    It leaves visible the hard growth/inverse step that must provide the
    entrywise certificate for `S⁻¹`. -/
theorem higham13_problem13_4_schur_kappa_maxEntryNormRect_from_entrywise_inverse_bound
    {s : ℕ} (hs : 0 < s)
    (S Sinv : Fin s → Fin s → ℝ)
    {normA normAinv rho kappaA : ℝ}
    (hRho : 0 ≤ rho)
    (hS_entry : ∀ i : Fin s, ∀ j : Fin s, |S i j| ≤ rho * normA)
    (hSinv_entry : ∀ i : Fin s, ∀ j : Fin s, |Sinv i j| ≤ normAinv)
    (hkappa : normA * normAinv ≤ kappaA) :
    maxEntryNormRect hs hs S * maxEntryNormRect hs hs Sinv ≤
      rho * kappaA :=
  higham13_problem13_4_schur_kappa_maxEntryNormRect_from_entrywise_schur_bound
    hs S Sinv hRho hS_entry
    (higham13_problem13_4_Sinv_maxEntryNormRect_from_entrywise_bound
      hs Sinv hSinv_entry)
    hkappa

/-- Higham, 2nd ed., Chapter 13, Problem 13.4:
    certificate-level bridge for the Schur-complement condition-number bound
    `κ(S) ≤ ρₙ κ(A)`.

    Once operator certificates have supplied `‖S‖ ≤ ρₙ ‖A‖`,
    `‖S⁻¹‖ ≤ ‖A⁻¹‖`, and `‖A‖‖A⁻¹‖ ≤ κ(A)`, the displayed condition-number
    product follows by scalar monotonicity.  The hard source obligation is
    still deriving those certificates from the Schur-complement and growth
    assumptions. -/
theorem higham13_problem13_4_schur_kappa_bound_from_operator_certificates
    {s : ℕ} [Nonempty (Fin s)]
    (S Sinv : Fin s → Fin s → ℝ)
    {normS normSinv normA normAinv rho kappaA : ℝ}
    (hRho : 0 ≤ rho)
    (hS : finiteOpNorm2Le S normS)
    (hSinv : finiteOpNorm2Le Sinv normSinv)
    (hS_bound : normS ≤ rho * normA)
    (hSinv_bound : normSinv ≤ normAinv)
    (hkappa : normA * normAinv ≤ kappaA) :
    normS * normSinv ≤ rho * kappaA := by
  have hNormSinv_nonneg : 0 ≤ normSinv :=
    finiteOpNorm2Le_radius_nonneg Sinv hSinv
  have hSupper_nonneg : 0 ≤ rho * normA :=
    le_trans (finiteOpNorm2Le_radius_nonneg S hS) hS_bound
  have hmul :
      normS * normSinv ≤ (rho * normA) * normAinv :=
    mul_le_mul hS_bound hSinv_bound hNormSinv_nonneg
      hSupper_nonneg
  calc
    normS * normSinv ≤ (rho * normA) * normAinv := hmul
    _ = rho * (normA * normAinv) := by ring
    _ ≤ rho * kappaA := mul_le_mul_of_nonneg_left hkappa hRho

end NumStability
