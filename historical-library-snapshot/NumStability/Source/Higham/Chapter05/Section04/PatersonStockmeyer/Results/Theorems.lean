-- NumStability/Source/Higham/Chapter05/Section04/PatersonStockmeyer/Results/Theorems.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Whole-owner block relocation.
-- Historical owner: `NumStability.Algorithms.Higham5PatersonStockmeyer`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Data.Nat.Sqrt
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Tactic
import NumStability.Source.Higham.Chapter05.Section04.PatersonStockmeyer.Basic

/-!
# Theorems

Relocated from `NumStability.Algorithms.Higham5PatersonStockmeyer` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


/-!
# Higham5PatersonStockmeyer (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.Higham5PatersonStockmeyer`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

open scoped BigOperators

noncomputable section

namespace NumStability

private theorem higham5_ps_horner_eq_sum {m : ℕ}
    (B : ℕ → Higham5SquareMatrix m) (Y : Higham5SquareMatrix m) :
    ∀ k : ℕ, higham5PSHorner B Y k =
      Finset.sum (Finset.range k) (fun q => B q * Y ^ q) := by
  intro k
  induction k using Nat.twoStepInduction generalizing B with
  | zero => simp [higham5PSHorner]
  | one => simp [higham5PSHorner]
  | more k ih0 ih1 =>
      rw [higham5PSHorner]
      rw [ih1 (fun q => B (q + 1))]
      conv_rhs => rw [Finset.sum_range_succ']
      simp only [pow_zero, mul_one]
      conv_rhs => rw [add_comm]
      apply congrArg (B 0 + ·)
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      simp only [pow_succ]
      simp [mul_assoc]

/-- The literal block-Horner execution equals the closed-form grouped
evaluator. -/
theorem higham5_patersonStockmeyerHorner_eq {n m : ℕ}
    (a : Fin (n + 1) → ℂ) (X : Higham5SquareMatrix m) :
    higham5PatersonStockmeyerHorner a X =
      higham5PatersonStockmeyer a X := by
  rw [higham5PatersonStockmeyerHorner, higham5_ps_horner_eq_sum]
  rfl

private theorem higham5_ps_block_index_lt {n : ℕ} (i : Fin (n + 1)) :
    i.1 / higham5PSBlockSize n < higham5PSBlockSize n := by
  have hs : 0 < higham5PSBlockSize n := by
    simp [higham5PSBlockSize]
  apply (Nat.div_lt_iff_lt_mul hs).2
  exact lt_of_lt_of_le i.2 (by
    simpa [higham5PSBlockSize, pow_two] using Nat.succ_le_succ_sqrt n)

/-- Exact correctness of the p. 102 Paterson--Stockmeyer evaluator for the
source dimensions and coefficient field.  No commutativity of arbitrary
matrices is assumed: the proof only combines powers of the same matrix `X`. -/
theorem higham5_patersonStockmeyer_eq_P1 {n m : ℕ}
    (a : Fin (n + 1) → ℂ) (X : Higham5SquareMatrix m) :
    higham5PatersonStockmeyer a X = higham5P1 a X := by
  simp only [higham5PatersonStockmeyer, higham5PSBlock, higham5P1,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single (i.1 / higham5PSBlockSize n)]
  · simp only [if_true]
    rw [smul_mul_assoc]
    rw [← pow_mul, ← pow_add]
    rw [Nat.mod_add_div]
  · intro q hq hne
    simp [Ne.symm hne]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (higham5_ps_block_index_lt i))).elim

/-- Correctness of the executable block-Horner form. -/
theorem higham5_patersonStockmeyerHorner_eq_P1 {n m : ℕ}
    (a : Fin (n + 1) → ℂ) (X : Higham5SquareMatrix m) :
    higham5PatersonStockmeyerHorner a X = higham5P1 a X := by
  rw [higham5_patersonStockmeyerHorner_eq,
    higham5_patersonStockmeyer_eq_P1]

/-- One theorem packages the exact evaluator equality and both quantitative
claims made on p. 102. -/
theorem higham5_patersonStockmeyer_source_claim {n m : ℕ}
    (a : Fin (n + 1) → ℂ) (X : Higham5SquareMatrix m) (hn : 0 < n) :
    higham5PatersonStockmeyerHorner a X = higham5P1 a X ∧
      higham5PSMatrixMultiplications n ≤ 2 * Nat.sqrt n ∧
      higham5PSStoredElements m n ≤ 5 * (m * m) * Nat.sqrt n := by
  exact ⟨higham5_patersonStockmeyerHorner_eq_P1 a X,
    higham5_ps_matrix_multiplications_le n,
    higham5_ps_stored_elements_le m n hn⟩

end NumStability

end
