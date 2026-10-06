/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import NumStability.Source.Higham.Chapter23.BlockAlgorithms
import NumStability.Source.Higham.Chapter23.Theorem02.RecursiveMatrix

namespace NumStability

/-!
# Higham Problems 23.8--23.9: recursive inversion

Problem 23.8's block inverse identity and exact operation-count recurrence,
together with the Problem 23.9 upper-triangular specialization. The latter is
intentionally co-located here because it is a direct specialization of the
Problem 23.8 formula.
-/

section BlockInverse

variable {R : Type*} [Ring R]

/-- The identity element in the `2 × 2` block presentation. -/
def higham23Problem23_8BlockOne : Higham23Block2 (R := R) :=
  { c11 := 1, c12 := 0, c21 := 0, c22 := 1 }

/-- The six products and the assembled inverse printed in Problem 23.8.

`P1` is a two-sided inverse of `A11`; `P6` is a two-sided inverse of
`P5 = A21 * P1 * A12 - A22`.  The common products `P3*P6` and `P6*P2`
are shared in the assembled blocks, giving six block multiplications outside
the two recursive inversions. -/
def higham23Problem23_8Candidate
    (A12 A21 P1 P6 : R) : Higham23Block2 (R := R) :=
  let P2 := A21 * P1
  let P3 := P1 * A12
  { c11 := P1 - (P3 * P6) * P2
    c12 := P3 * P6
    c21 := P6 * P2
    c22 := -P6 }

/-- Left-inverse half of the block formula in Problem 23.8. -/
theorem higham23_problem23_8_left_inverse
    (A11 A12 A21 A22 P1 P6 : R)
    (hP1 : A11 * P1 = 1)
    (hP6 : (A21 * (P1 * A12) - A22) * P6 = 1) :
    higham23BlockMul
        { c11 := A11, c12 := A12, c21 := A21, c22 := A22 }
        (higham23Problem23_8Candidate A12 A21 P1 P6) =
      higham23Problem23_8BlockOne := by
  apply Higham23Block2.ext <;>
    simp only [higham23BlockMul, higham23Problem23_8Candidate,
      higham23Problem23_8BlockOne]
  · calc
      A11 * (P1 - P1 * A12 * P6 * (A21 * P1)) +
          A12 * (P6 * (A21 * P1)) =
          A11 * P1 + (A12 - (A11 * P1) * A12) * P6 * (A21 * P1) := by
            noncomm_ring
      _ = 1 := by rw [hP1]; simp
  · calc
      A11 * (P1 * A12 * P6) + A12 * -P6 =
          (A11 * P1 - 1) * A12 * P6 := by noncomm_ring
      _ = 0 := by rw [hP1]; simp
  · calc
      A21 * (P1 - P1 * A12 * P6 * (A21 * P1)) +
          A22 * (P6 * (A21 * P1)) =
          A21 * P1 - ((A21 * (P1 * A12) - A22) * P6) * (A21 * P1) := by
            noncomm_ring
      _ = 0 := by rw [hP6]; simp
  · calc
      A21 * (P1 * A12 * P6) + A22 * -P6 =
          (A21 * (P1 * A12) - A22) * P6 := by noncomm_ring
      _ = 1 := hP6

/-- Right-inverse half of the block formula in Problem 23.8. -/
theorem higham23_problem23_8_right_inverse
    (A11 A12 A21 A22 P1 P6 : R)
    (hP1 : P1 * A11 = 1)
    (hP6 : P6 * (A21 * (P1 * A12) - A22) = 1) :
    higham23BlockMul
        (higham23Problem23_8Candidate A12 A21 P1 P6)
        { c11 := A11, c12 := A12, c21 := A21, c22 := A22 } =
      higham23Problem23_8BlockOne := by
  apply Higham23Block2.ext <;>
    simp only [higham23BlockMul, higham23Problem23_8Candidate,
      higham23Problem23_8BlockOne]
  · calc
      (P1 - P1 * A12 * P6 * (A21 * P1)) * A11 +
          P1 * A12 * P6 * A21 =
          P1 * A11 + P1 * A12 * P6 * (A21 - (A21 * P1) * A11) := by
            noncomm_ring
      _ = P1 * A11 + P1 * A12 * P6 * (A21 * (1 - P1 * A11)) := by
        noncomm_ring
      _ = 1 := by rw [hP1]; simp
  · calc
      (P1 - P1 * A12 * P6 * (A21 * P1)) * A12 +
          P1 * A12 * P6 * A22 =
          P1 * A12 - P1 * A12 *
            (P6 * (A21 * (P1 * A12) - A22)) := by noncomm_ring
      _ = 0 := by rw [hP6]; simp
  · calc
      P6 * (A21 * P1) * A11 + -P6 * A21 =
          P6 * (A21 * (P1 * A11) - A21) := by noncomm_ring
      _ = 0 := by rw [hP1]; simp
  · calc
      P6 * (A21 * P1) * A12 + -P6 * A22 =
          P6 * (A21 * (P1 * A12) - A22) := by noncomm_ring
      _ = 1 := hP6

/-- The source formula is a genuine two-sided inverse whenever its two
recursive inverses are genuine two-sided inverses. -/
theorem higham23_problem23_8_block_inverse
    (A11 A12 A21 A22 P1 P6 : R)
    (hP1l : A11 * P1 = 1) (hP1r : P1 * A11 = 1)
    (hP6l : (A21 * (P1 * A12) - A22) * P6 = 1)
    (hP6r : P6 * (A21 * (P1 * A12) - A22) = 1) :
    higham23BlockMul
        { c11 := A11, c12 := A12, c21 := A21, c22 := A22 }
        (higham23Problem23_8Candidate A12 A21 P1 P6) =
        higham23Problem23_8BlockOne ∧
      higham23BlockMul
        (higham23Problem23_8Candidate A12 A21 P1 P6)
        { c11 := A11, c12 := A12, c21 := A21, c22 := A22 } =
        higham23Problem23_8BlockOne :=
  ⟨higham23_problem23_8_left_inverse A11 A12 A21 A22 P1 P6 hP1l hP6l,
    higham23_problem23_8_right_inverse A11 A12 A21 A22 P1 P6 hP1r hP6r⟩

/-- Problem 23.9 specializes the Problem 23.8 formula to a zero lower-left
block, producing the familiar upper-triangular inverse and therefore the
Method-2B recursion discussed in Chapter 14. -/
theorem higham23_problem23_8_upper_triangular_specialization
    (A12 P1 P22 : R) :
    higham23Problem23_8Candidate A12 0 P1 (-P22) =
      { c11 := P1, c12 := -(P1 * A12 * P22), c21 := 0, c22 := P22 } := by
  ext <;> simp [higham23Problem23_8Candidate, mul_assoc]

end BlockInverse

section Cost

/-- Exact scalar-operation recurrence for recursive inversion in Problem
23.8 when one multiplication at recursion level `k` costs `7^k`: two
half-size inversions and the six printed block products. -/
def higham23Problem23_8InverseCost : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 * higham23Problem23_8InverseCost k + 6 * 7 ^ k

/-- Division-free closed form for the inversion recurrence:
`T_k = (6·7^k - 2^k)/5`. -/
theorem higham23_problem23_8_inverseCost_closed (k : ℕ) :
    5 * higham23Problem23_8InverseCost k + 2 ^ k = 6 * 7 ^ k := by
  induction k with
  | zero => simp [higham23Problem23_8InverseCost]
  | succ k ih =>
      simp only [higham23Problem23_8InverseCost, pow_succ]
      omega

/-- The recursive inversion costs at most twice a Strassen multiplication at
the same depth.  This is the concrete big-O witness on power-of-two orders. -/
theorem higham23_problem23_8_inverseCost_le (k : ℕ) :
    higham23Problem23_8InverseCost k ≤ 2 * 7 ^ k := by
  induction k with
  | zero => simp [higham23Problem23_8InverseCost]
  | succ k ih =>
      simp only [higham23Problem23_8InverseCost, pow_succ]
      omega

/-- On order `n = 2^k`, the Strassen term `7^k` is exactly
`n^(log₂ 7)`, making the exponent in Problem 23.8 literal rather than an
informal change of variables. -/
theorem higham23_problem23_8_power_exponent (k : ℕ) :
    Real.rpow ((2 : ℝ) ^ k) (Real.logb 2 7) = (7 : ℝ) ^ k := by
  calc
    Real.rpow ((2 : ℝ) ^ k) (Real.logb 2 7) =
        Real.rpow 2 ((k : ℝ) * Real.logb 2 7) :=
      (Real.rpow_natCast_mul (x := (2 : ℝ)) (by positivity) k
        (Real.logb 2 7)).symm
    _ = Real.rpow 2 (Real.logb 2 7 * (k : ℝ)) := by rw [mul_comm]
    _ = (Real.rpow 2 (Real.logb 2 7)) ^ k :=
      Real.rpow_mul_natCast (x := (2 : ℝ)) (by positivity) (Real.logb 2 7) k
    _ = (7 : ℝ) ^ k := by
      exact congrArg (fun x : ℝ => x ^ k)
        (Real.rpow_logb (b := (2 : ℝ)) (x := (7 : ℝ))
          (by norm_num) (by norm_num) (by norm_num))

end Cost

end NumStability
