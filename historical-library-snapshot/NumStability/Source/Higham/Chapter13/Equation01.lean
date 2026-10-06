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
# Source.Higham.Chapter13.Equation01

This module formalizes the source-facing Chapter 13 statements for
`Equation01`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


-- ============================================================
-- §13.1  Exact 2-by-2 block identities (eqs. 13.1--13.2)
-- ============================================================

/-- **Equation (13.1)**, exact partitioned outer-product LU identity.
    If the four block equations `L₁₁ U₁₁ = A₁₁`, `L₁₁ U₁₂ = A₁₂`,
    `L₂₁ U₁₁ = A₂₁`, and `L₂₁ U₁₂ + S = A₂₂` hold, then the displayed
    2-by-2 block LU product equals the original block matrix. -/
theorem higham13_eq13_1_partitioned_outer_product_lu
    {m n α : Type*} [Fintype m] [Fintype n] [DecidableEq n] [CommRing α]
    (L11 U11 A11 : Matrix m m α) (U12 A12 : Matrix m n α)
    (L21 A21 : Matrix n m α) (S A22 : Matrix n n α)
    (h11 : L11 * U11 = A11) (h12 : L11 * U12 = A12)
    (h21 : L21 * U11 = A21) (h22 : L21 * U12 + S = A22) :
    Matrix.fromBlocks A11 A12 A21 A22 =
      Matrix.fromBlocks L11 0 L21 1 * Matrix.fromBlocks U11 U12 0 S := by
  rw [Matrix.fromBlocks_multiply]
  simp [h11, h12, h21, h22]

end NumStability
