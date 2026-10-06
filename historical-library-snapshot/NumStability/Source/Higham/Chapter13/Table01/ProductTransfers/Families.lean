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
import NumStability.Analysis.FirstOrder.AsymptoticFamilies
import NumStability.Source.Higham.Chapter13.Equation22
import NumStability.Source.Higham.Chapter13.Equation23.ProductBounds.PointRow
import NumStability.Source.Higham.Chapter13.Table01.DiagonalDominance.Bounds

/-!
# Higham Table 13.1, product-transfer families

Canonical declaration owner created by the frozen B0004/R12 route map.
-/

namespace NumStability

open Filter Asymptotics
open scoped Topology

/-- Column block-diagonal-dominance product transfer from the two component
bounds printed before Table 13.1. -/
theorem higham13_table13_1_col_bdd_product_family_from_source_norms
    {ι : Type*} {l : Filter ι} (Uround : RoundoffFamily ι l)
    (m : ℕ) (normA normL normU : ι → ℝ)
    (hU : ∀ t, 0 ≤ normU t)
    (hNormL : ∀ t, normL t ≤ (m : ℝ))
    (hNormU : ∀ t, normU t ≤ (m : ℝ) ^ 2 * normA t) :
    FamilyLinearRemainderLe l Uround.unit
      (fun t => (m : ℝ) ^ 3 * normA t)
      (fun t => normL t * normU t) := by
  apply FamilyLinearRemainderLe.of_le
  intro t
  exact higham13_col_bdd_stability_bound
    (normL t) (normU t) (normA t) m (hU t) (hNormL t) (hNormU t)

/-- Point column-diagonal-dominance product transfer from its source lower-
and upper-factor bounds. -/
theorem higham13_table13_1_point_col_bdd_product_family_from_source_norms
    {ι : Type*} {l : Filter ι} (Uround : RoundoffFamily ι l)
    (normA normL normU : ι → ℝ)
    (hL : ∀ t, 0 ≤ normL t) (hU : ∀ t, 0 ≤ normU t)
    (hA : ∀ t, 0 ≤ normA t)
    (hNormL : ∀ t, normL t ≤ 1)
    (hNormU : ∀ t, normU t ≤ 2 * normA t) :
    FamilyLinearRemainderLe l Uround.unit
      (fun t => 2 * normA t) (fun t => normL t * normU t) := by
  apply FamilyLinearRemainderLe.of_le
  intro t
  exact block_lu_stability_point_diagDom_col
    (normL t) (normU t) (normA t)
    (hL t) (hU t) (hA t) (hNormL t) (hNormU t)

/-- Arbitrary-matrix (and block-row-BDD) equation-(13.22) product transfer
from the source growth/condition component estimates. -/
theorem higham13_table13_1_arbitrary_product_family_from_eq13_22_source_norms
    {ι : Type*} {l : Filter ι} (Uround : RoundoffFamily ι l)
    (n : ℕ) (rho kappa : ι → ℝ) (normA normL normU : ι → ℝ)
    (hU : ∀ t, 0 ≤ normU t) (hRho : ∀ t, 0 ≤ rho t)
    (hKappa : ∀ t, 0 ≤ kappa t)
    (hNormL : ∀ t,
      normL t ≤ (n : ℝ) * (rho t) ^ 2 * kappa t)
    (hNormU : ∀ t, normU t ≤ rho t * normA t) :
    FamilyLinearRemainderLe l Uround.unit
      (fun t => (n : ℝ) * (rho t) ^ 3 * kappa t * normA t)
      (fun t => normL t * normU t) := by
  apply FamilyLinearRemainderLe.of_le
  intro t
  exact block_lu_normLU_bound_general_higham_13_22
    (normL t) (normU t) (normA t) (rho t) (kappa t) n
    (hU t) (hRho t) (hKappa t) (hNormL t) (hNormU t)

/-- Point row-diagonal-dominance equation-(13.23) product transfer, including
the proved source growth specialization `rho <= 2`. -/
theorem higham13_table13_1_point_row_product_family_from_eq13_23_source_norms
    {ι : Type*} {l : Filter ι} (Uround : RoundoffFamily ι l)
    (n : ℕ) (rho kappa : ι → ℝ) (normA normL normU : ι → ℝ)
    (hU : ∀ t, 0 ≤ normU t) (hA : ∀ t, 0 ≤ normA t)
    (hRho : ∀ t, 0 ≤ rho t) (hRhoTwo : ∀ t, rho t ≤ 2)
    (hKappa : ∀ t, 0 ≤ kappa t)
    (hNormL : ∀ t,
      normL t ≤ (n : ℝ) * (rho t) ^ 2 * kappa t)
    (hNormU : ∀ t, normU t ≤ rho t * normA t) :
    FamilyLinearRemainderLe l Uround.unit
      (fun t => 8 * (n : ℝ) * kappa t * normA t)
      (fun t => normL t * normU t) := by
  apply FamilyLinearRemainderLe.of_le
  intro t
  exact higham13_eq13_23_point_row_from_growth
    (normL t) (normU t) (normA t) (rho t) (kappa t) n
    (hU t) (hA t) (hRho t) (hRhoTwo t) (hKappa t)
    (hNormL t) (hNormU t)

/-- SPD equation-(13.24) product transfer from the two displayed factor
bounds. -/
theorem higham13_table13_1_spd_product_family_from_eq13_24_source_norms
    {ι : Type*} {l : Filter ι} (Uround : RoundoffFamily ι l)
    (m : ℕ) (kappa normA normL normU : ι → ℝ)
    (hU : ∀ t, 0 ≤ normU t)
    (hNormL : ∀ t, normL t ≤ 1 + (m : ℝ) * Real.sqrt (kappa t))
    (hNormU : ∀ t, normU t ≤ Real.sqrt (m : ℝ) * normA t) :
    FamilyLinearRemainderLe l Uround.unit
      (fun t => Real.sqrt (m : ℝ) *
        (1 + (m : ℝ) * Real.sqrt (kappa t)) * normA t)
      (fun t => normL t * normU t) := by
  apply FamilyLinearRemainderLe.of_le
  intro t
  have hLbound0 : 0 ≤ 1 + (m : ℝ) * Real.sqrt (kappa t) := by
    positivity
  have hmul := mul_le_mul (hNormL t) (hNormU t) (hU t) hLbound0
  calc
    normL t * normU t ≤
        (1 + (m : ℝ) * Real.sqrt (kappa t)) *
          (Real.sqrt (m : ℝ) * normA t) := hmul
    _ = Real.sqrt (m : ℝ) *
        (1 + (m : ℝ) * Real.sqrt (kappa t)) * normA t := by ring

end NumStability
