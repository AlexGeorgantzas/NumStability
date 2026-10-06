-- Algorithms/Higham5PatersonStockmeyer.lean
--
-- A source-dimensional closure of the Paterson--Stockmeyer statement in
-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 5, p. 102.  The source polynomial is
--
--   P(X) = a₀ I + a₁ X + ⋯ + aₙ Xⁿ,
--
-- with scalar coefficients in ℂ and X an m-by-m complex matrix.

import Mathlib.Data.Nat.Sqrt
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Tactic

namespace NumStability

open scoped BigOperators

noncomputable section

/-! ## The source polynomial and the Paterson--Stockmeyer blocks -/

/-- The square complex matrices occurring in Higham's displayed polynomial
`P₁` on p. 102. -/
abbrev Higham5SquareMatrix (m : ℕ) := Matrix (Fin m) (Fin m) ℂ

/-- Higham's source polynomial `P₁ = a₀ I + a₁ X + ⋯ + aₙ Xⁿ`.  Using
`Fin (n+1)` makes the coefficient range, including both endpoints, exact. -/
def higham5P1 {n m : ℕ} (a : Fin (n + 1) → ℂ)
    (X : Higham5SquareMatrix m) : Higham5SquareMatrix m :=
  ∑ i, a i • X ^ i.1

/-- The Paterson--Stockmeyer block size.  The choice `⌊√n⌋+1` guarantees
that all `n+1` powers fit in fewer than `s²+1` slots. -/
def higham5PSBlockSize (n : ℕ) : ℕ := Nat.sqrt n + 1

/-- The `q`th baby-step block
`B_q(X) = ∑_{i / s = q} a_i X^(i mod s)`. -/
def higham5PSBlock {n m : ℕ} (a : Fin (n + 1) → ℂ)
    (X : Higham5SquareMatrix m) (q : ℕ) : Higham5SquareMatrix m :=
  ∑ i, if i.1 / higham5PSBlockSize n = q then
      a i • X ^ (i.1 % higham5PSBlockSize n)
    else 0

/-- The Paterson--Stockmeyer evaluator, grouped into baby-step blocks and
giant powers of `Y = X^s`:
`∑_{q<s} B_q(X) (X^s)^q`.

The definition exposes the reusable baby powers and giant base appearing in
the source algorithm; `higham5_patersonStockmeyer_eq_P1` below proves that it
is exactly the displayed matrix polynomial. -/
def higham5PatersonStockmeyer {n m : ℕ} (a : Fin (n + 1) → ℂ)
    (X : Higham5SquareMatrix m) : Higham5SquareMatrix m :=
  ∑ q ∈ Finset.range (higham5PSBlockSize n),
    higham5PSBlock a X q * (X ^ higham5PSBlockSize n) ^ q

/-- Reverse Horner evaluation of the first `k` coefficients of a matrix
polynomial `B₀ + B₁Y + ⋯`.  The `k+2` branch contains exactly one matrix
multiplication; the zero- and one-block branches contain none. -/
def higham5PSHorner {m : ℕ} (B : ℕ → Higham5SquareMatrix m)
    (Y : Higham5SquareMatrix m) : ℕ → Higham5SquareMatrix m
  | 0 => 0
  | 1 => B 0
  | k + 2 =>
      B 0 + higham5PSHorner (fun q => B (q + 1)) Y (k + 1) * Y

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

/-- The literal block-Horner execution of Paterson--Stockmeyer.  Unlike the
closed-form block sum, this definition exposes the `s-1` giant-step matrix
multiplications used by the operation count. -/
def higham5PatersonStockmeyerHorner {n m : ℕ} (a : Fin (n + 1) → ℂ)
    (X : Higham5SquareMatrix m) : Higham5SquareMatrix m :=
  higham5PSHorner (higham5PSBlock a X) (X ^ higham5PSBlockSize n)
    (higham5PSBlockSize n)

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

/-! ## Explicit operation and storage certificates -/

/-- The reusable power table used by the baby-step phase.  The input supplies
`X` itself; repeated use of `higham5_ps_powerTable_succ` produces
`X², …, X^s`. -/
def higham5PSPowerTable {m : ℕ} (X : Higham5SquareMatrix m) (r : ℕ) :
    Higham5SquareMatrix m := X ^ r

/-- One matrix multiplication advances one entry in the reusable power
chain. -/
theorem higham5_ps_powerTable_succ {m : ℕ} (X : Higham5SquareMatrix m)
    (r : ℕ) :
    higham5PSPowerTable X (r + 1) = higham5PSPowerTable X r * X := by
  simp [higham5PSPowerTable, pow_succ]

/-- Starting from the supplied `X`, producing the remaining baby powers and
the giant base `X^s` takes `s-1` matrix multiplications. -/
def higham5PSBabyPowerMultiplications (n : ℕ) : ℕ :=
  higham5PSBlockSize n - 1

/-- The recursive block-Horner evaluator has no multiplication in its zero-
and one-block branches and one in every `k+2` branch, hence `k-1` for `k`
blocks. -/
def higham5PSHornerMultiplications (k : ℕ) : ℕ := k - 1

theorem higham5_ps_horner_multiplications_zero :
    higham5PSHornerMultiplications 0 = 0 := by
  rfl

theorem higham5_ps_horner_multiplications_one :
    higham5PSHornerMultiplications 1 = 0 := by
  rfl

theorem higham5_ps_horner_multiplications_succ_succ (k : ℕ) :
    higham5PSHornerMultiplications (k + 2) =
      higham5PSHornerMultiplications (k + 1) + 1 := by
  simp [higham5PSHornerMultiplications]

/-- Matrix multiplications in the standard operational schedule: form the
reusable baby powers through `X^s`, then run the literal block-Horner
evaluator.  Scalar-matrix products and matrix additions are not matrix
multiplications, exactly as in the source's count. -/
def higham5PSMatrixMultiplications (n : ℕ) : ℕ :=
  higham5PSBabyPowerMultiplications n +
    higham5PSHornerMultiplications (higham5PSBlockSize n)

/-- The total count is definitionally split between the two actual phases. -/
theorem higham5_ps_matrix_multiplications_operational (n : ℕ) :
    higham5PSMatrixMultiplications n =
      higham5PSBabyPowerMultiplications n +
        higham5PSHornerMultiplications (higham5PSBlockSize n) := by
  rfl

/-- An explicit live-storage schedule uses the `s` baby matrices, the giant
base `X^s`, a block work matrix, and the accumulator: `s+3` matrices. -/
def higham5PSStoredMatrices (n : ℕ) : ℕ :=
  higham5PSBlockSize n + 3

/-- Number of complex matrix elements stored by that schedule. -/
def higham5PSStoredElements (m n : ℕ) : ℕ :=
  higham5PSStoredMatrices n * (m * m)

/-- The multiplication count is not merely asymptotic: it is exactly
`2⌊√n⌋` for every degree `n`. -/
theorem higham5_ps_matrix_multiplications_exact (n : ℕ) :
    higham5PSMatrixMultiplications n = 2 * Nat.sqrt n := by
  simp [higham5PSMatrixMultiplications, higham5PSBabyPowerMultiplications,
    higham5PSHornerMultiplications, higham5PSBlockSize, two_mul]

/-- Explicit `O(√n)` matrix-multiplication certificate. -/
theorem higham5_ps_matrix_multiplications_le (n : ℕ) :
    higham5PSMatrixMultiplications n ≤ 2 * Nat.sqrt n := by
  rw [higham5_ps_matrix_multiplications_exact]

/-- The live-storage formula is exactly `(⌊√n⌋+4)m²` elements. -/
theorem higham5_ps_stored_elements_exact (m n : ℕ) :
    higham5PSStoredElements m n = (Nat.sqrt n + 4) * (m * m) := by
  simp [higham5PSStoredElements, higham5PSStoredMatrices,
    higham5PSBlockSize]

/-- Explicit `O(m²√n)` stored-element certificate (for the source's
nonconstant case `n>0`). -/
theorem higham5_ps_stored_elements_le (m n : ℕ) (hn : 0 < n) :
    higham5PSStoredElements m n ≤ 5 * (m * m) * Nat.sqrt n := by
  rw [higham5_ps_stored_elements_exact]
  have hr : 1 ≤ Nat.sqrt n := by
    exact (Nat.sqrt_pos.2 hn)
  have hc : Nat.sqrt n + 4 ≤ 5 * Nat.sqrt n := by omega
  have hm := Nat.mul_le_mul_right (m * m) hc
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hm

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

end

end NumStability
