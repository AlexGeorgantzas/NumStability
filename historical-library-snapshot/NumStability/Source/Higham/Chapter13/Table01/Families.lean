import Mathlib.Tactic.Ring
import NumStability.Analysis.FirstOrder.AsymptoticFamilies
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum

/-!
# Higham Table 13.1 family composition

Uniform family-level product-transfer results associated with Table 13.1.
-/

namespace NumStability

open Filter Asymptotics
open scoped Topology

/-- Uniform Table 13.1 composition.  The product comparison is `O(u)`, so
substitution into the outer Theorem 13.6 factor contributes only `O(u²)`. -/
theorem higham13_table13_1_family_from_product_transfer
    {ι : Type*} {l : Filter ι} (U : RoundoffFamily ι l)
    (c tableValue : ℝ)
    (normA computedProduct err : ι → ℝ)
    (hc : 0 ≤ c)
    (hErr : FamilyFirstOrderLe l U.unit
      (fun t => c * U.unit t * (normA t + computedProduct t)) err)
    (hProductTransfer : FamilyLinearRemainderLe l U.unit
      (fun t => tableValue * normA t) computedProduct) :
    FamilyFirstOrderLe l U.unit
      (fun t => c * U.unit t * ((1 + tableValue) * normA t)) err := by
  have h := FamilyFirstOrderLe.coefficient_of_linear_transfer_to
    hc U.unit_nonneg hErr hProductTransfer
  convert h using 1
  funext t
  ring

/-- Table 13.1 bridge with every scalar in the premise and conclusion tied to
the displayed matrix families' actual max-entry norms. -/
theorem higham13_table13_1_family_actual_maxEntry
    {ι : Type*} {l : Filter ι} (Uround : RoundoffFamily ι l)
    {n : ℕ} (hn : 0 < n) (c tableValue : ℝ)
    (A Lhat Uhat Delta : ι → Matrix (Fin n) (Fin n) ℝ)
    (hc : 0 ≤ c)
    (hTheorem13_6 : FamilyFirstOrderLe l Uround.unit
      (fun t => c * Uround.unit t *
        (maxEntryNorm hn (A t) +
          maxEntryNorm hn (Lhat t) * maxEntryNorm hn (Uhat t)))
      (fun t => maxEntryNorm hn (Delta t)))
    (hProductTransfer : FamilyLinearRemainderLe l Uround.unit
      (fun t => tableValue * maxEntryNorm hn (A t))
      (fun t => maxEntryNorm hn (Lhat t) * maxEntryNorm hn (Uhat t))) :
    FamilyFirstOrderLe l Uround.unit
      (fun t => c * Uround.unit t *
        ((1 + tableValue) * maxEntryNorm hn (A t)))
      (fun t => maxEntryNorm hn (Delta t)) :=
  higham13_table13_1_family_from_product_transfer Uround c tableValue
    (fun t => maxEntryNorm hn (A t))
    (fun t => maxEntryNorm hn (Lhat t) * maxEntryNorm hn (Uhat t))
    (fun t => maxEntryNorm hn (Delta t)) hc hTheorem13_6 hProductTransfer

end NumStability
