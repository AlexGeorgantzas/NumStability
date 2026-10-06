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

/-!
# Source.Higham.Chapter13.Equation24

This module formalizes the source-facing Chapter 13 statements for
`Equation24`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, §13.3.2, equation (13.24):
    source-shaped scalar product bound for the SPD case.  From the
    source-derived premises `‖L‖₂ ≤ 1 + m κ₂(A)^{1/2}` and
    `‖U‖₂ ≤ √m ‖A‖₂`, the printed bound
    `‖L‖₂‖U‖₂ ≤ √m(1 + mκ₂(A)^{1/2})‖A‖₂` follows.  Lemmas 13.9--13.10 are
    still the open source obligations that supply those premises. -/
theorem higham13_eq13_24_spd_scalar_bound
    (normL2 normU2 normA2 kappa2 : ℝ) (m : ℕ)
    (hU : 0 ≤ normU2)
    (hNormL : normL2 ≤ 1 + (m : ℝ) * Real.sqrt kappa2)
    (hNormU : normU2 ≤ Real.sqrt (m : ℝ) * normA2) :
    normL2 * normU2 ≤
      Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappa2) * normA2 := by
  have hLbound_nonneg : 0 ≤ 1 + (m : ℝ) * Real.sqrt kappa2 := by
    linarith [mul_nonneg (Nat.cast_nonneg m) (Real.sqrt_nonneg kappa2)]
  have hmul := mul_le_mul hNormL hNormU hU hLbound_nonneg
  calc
    normL2 * normU2
        ≤ (1 + (m : ℝ) * Real.sqrt kappa2) *
            (Real.sqrt (m : ℝ) * normA2) := hmul
    _ = Real.sqrt (m : ℝ) * (1 + (m : ℝ) * Real.sqrt kappa2) * normA2 := by
      ring

end NumStability
