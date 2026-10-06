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
import NumStability.Source.Higham.Chapter13.Equation25.Families
import NumStability.Source.Higham.Chapter13.Section03.SPDFactorBounds
import NumStability.Source.Higham.Chapter13.Theorem05.FamilyErrorAnalysis
import NumStability.Source.Higham.Chapter13.Theorem06.Computation

/-!
# Higham equation (13.25), backward-error bounds

Canonical declaration owner created by the frozen B0004/R12 route map.
-/

namespace NumStability

open Filter Asymptotics
open scoped Topology

-- ============================================================
-- §13.3.2  Eq. 13.25 (SPD backward error bound)
-- ============================================================

/-- **Eq. 13.25** (Higham): SPD backward error bound for block LU.
    Combining Theorem 13.6 (‖ΔAᵢ‖ ≤ dₙu(‖A‖ + ‖L̂‖‖Û‖)) with eq. 13.24
    (‖L̂‖₂‖Û‖₂ ≤ √m(1 + mκ₂(A)^{1/2})‖A‖₂), the backward error is:
    ‖ΔAᵢ‖ ≤ cₙ · √m · u · ‖A‖₂ · (2 + m · κ₂(A)^{1/2}) + O(u²).

    The factor (2 + mκ₂^{1/2}) arises from:
    ‖A‖₂ + ‖L̂‖₂‖Û‖₂ ≤ ‖A‖₂ + √m(1 + mκ₂^{1/2})‖A‖₂
                        = ‖A‖₂ · (1 + √m + m^{3/2}κ₂^{1/2})
    which is bounded by cₙ · √m · ‖A‖₂ · (2 + mκ₂^{1/2}). -/
theorem spd_backward_error_bound
    (normA normLU u d_n : ℝ)
    (normA2 kappa2 : ℝ) (m : ℕ)
    (hu : 0 ≤ u) (hd : 0 ≤ d_n)
    -- Eq. 13.24: ‖L‖₂‖U‖₂ ≤ √m (1 + mκ₂^{1/2}) ‖A‖₂
    (hLU_bound : normLU ≤ Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappa2) * normA2)
    -- ‖A‖ ≤ ‖A‖₂ (for normwise comparison)
    (hNormCompare : normA ≤ normA2) :
    d_n * u * (normA + normLU) ≤
      d_n * u * normA2 * (1 + Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappa2)) := by
  have hRHS : normA + normLU ≤
      normA2 * (1 + Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappa2)) := by
    calc normA + normLU
        ≤ normA2 + Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappa2) * normA2 := by
          linarith
      _ = normA2 * (1 + Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappa2)) := by ring
  have hdu : 0 ≤ d_n * u := mul_nonneg hd hu
  calc d_n * u * (normA + normLU)
      ≤ d_n * u * (normA2 * (1 + Real.sqrt ↑m * (1 + ↑m * Real.sqrt kappa2))) :=
        mul_le_mul_of_nonneg_left hRHS hdu
    _ = d_n * u * normA2 * (1 + Real.sqrt ↑m * (1 + ↑m * Real.sqrt kappa2)) := by ring

/-- Source-shaped scalar form of Higham eq. (13.25).  Once the previous
    backward-error step has produced the intermediate factor
    `1 + sqrt(m) * (1 + m * sqrt(kappa2))`, the displayed Higham bound follows
    for at least one block stage from `1 <= sqrt(m)`. -/
theorem spd_backward_error_bound_higham_13_25
    (err u c_n normA2 kappa2 : ℝ) (m : ℕ)
    (hu : 0 ≤ u) (hc : 0 ≤ c_n) (hA : 0 ≤ normA2)
    (hsqrt_ge_one : 1 ≤ Real.sqrt (m : ℝ))
    (hIntermediate :
      err ≤ c_n * u * normA2 *
        (1 + Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappa2))) :
    err ≤ c_n * Real.sqrt (m : ℝ) * u * normA2 *
      (2 + (m : ℝ) * Real.sqrt kappa2) := by
  have hfactor_nonneg : 0 ≤ c_n * u * normA2 := by positivity
  have hkterm : 0 ≤ (m : ℝ) * Real.sqrt kappa2 :=
    mul_nonneg (Nat.cast_nonneg m) (Real.sqrt_nonneg kappa2)
  have hfactor :
      1 + Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappa2) ≤
        Real.sqrt (m : ℝ) * (2 + (m : ℝ) * Real.sqrt kappa2) := by
    nlinarith
  calc err
      ≤ c_n * u * normA2 *
          (1 + Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappa2)) :=
        hIntermediate
    _ ≤ c_n * u * normA2 *
          (Real.sqrt (m : ℝ) * (2 + (m : ℝ) * Real.sqrt kappa2)) :=
        mul_le_mul_of_nonneg_left hfactor hfactor_nonneg
    _ = c_n * Real.sqrt (m : ℝ) * u * normA2 *
          (2 + (m : ℝ) * Real.sqrt kappa2) := by
        ring

end NumStability
