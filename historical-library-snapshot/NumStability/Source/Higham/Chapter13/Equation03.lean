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
# Source.Higham.Chapter13.Equation03

This module formalizes the source-facing Chapter 13 statements for
`Equation03`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- **Equation (13.3)**, exact recursive partitioned-LU identity.
    In the half-size recursive partition, if
    `[A₁₁; A₂₁] = [L₁₁; L₂₁] U₁₁`, `L₁₁ U₁₂ = A₁₂`, and
    `S = A₂₂ - L₂₁ U₁₂`, then the displayed three-factor product in Algorithm
    13.4 reconstructs the original 2-by-2 block matrix. -/
theorem higham13_eq13_3_recursive_partitioned_lu
    {n α : Type*} [Fintype n] [DecidableEq n] [CommRing α]
    (L11 U11 A11 U12 A12 L21 A21 S A22 : Matrix n n α)
    (h11 : L11 * U11 = A11) (h12 : L11 * U12 = A12)
    (h21 : L21 * U11 = A21) (h22 : L21 * U12 + S = A22) :
    Matrix.fromBlocks A11 A12 A21 A22 =
      Matrix.fromBlocks L11 0 L21 1 * Matrix.fromBlocks 1 0 0 S *
        Matrix.fromBlocks U11 U12 0 1 := by
  rw [Matrix.mul_assoc]
  rw [Matrix.fromBlocks_multiply]
  rw [Matrix.fromBlocks_multiply]
  simp [h11, h12, h21, h22]

end NumStability
