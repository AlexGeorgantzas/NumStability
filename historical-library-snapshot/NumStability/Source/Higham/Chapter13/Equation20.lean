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
# Source.Higham.Chapter13.Equation20

This module formalizes the source-facing Chapter 13 statements for
`Equation20`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


-- ============================================================
-- §13.3.1  Partition displays for entrywise max-norm analysis
-- ============================================================

/-- **Equation (13.20)**, exact 2-by-2 partition display.
    Higham switches here to the entrywise max norm and writes
    `A = [[A₁₁, A₁₂], [A₂₁, A₂₂]]`.  In Mathlib this is exactly the
    `fromBlocks` reconstruction from the four canonical block projections. -/
theorem higham13_eq13_20_partition {r s α : Type*}
    (A : Matrix (r ⊕ s) (r ⊕ s) α) :
    A = Matrix.fromBlocks A.toBlocks₁₁ A.toBlocks₁₂ A.toBlocks₂₁ A.toBlocks₂₂ := by
  exact (Matrix.fromBlocks_toBlocks A).symm

end NumStability
