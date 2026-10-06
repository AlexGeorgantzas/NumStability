/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

namespace NumStability

/-!
# Higham Chapter 23: Block algorithms

Exact Strassen and Winograd block algorithms and operation counts from Higham, Chapter 23.
-/

section BlockAlgorithms

variable {R : Type*} [NonUnitalNonAssocRing R]

/-- A `2 × 2` block matrix, used only to state the exact algebraic algorithms
without imposing commutativity on the blocks. -/
@[ext] structure Higham23Block2 where
  c11 : R
  c12 : R
  c21 : R
  c22 : R

/-- Conventional `2 × 2` block multiplication, equation (23.3). -/
def higham23BlockMul (A B : Higham23Block2 (R := R)) : Higham23Block2 (R := R) where
  c11 := A.c11 * B.c11 + A.c12 * B.c21
  c12 := A.c11 * B.c12 + A.c12 * B.c22
  c21 := A.c21 * B.c11 + A.c22 * B.c21
  c22 := A.c21 * B.c12 + A.c22 * B.c22

/-- Equation (23.4): Strassen's seven-product construction. -/
def higham23Strassen2 (A B : Higham23Block2 (R := R)) : Higham23Block2 (R := R) :=
  let p1 := (A.c11 + A.c22) * (B.c11 + B.c22)
  let p2 := (A.c21 + A.c22) * B.c11
  let p3 := A.c11 * (B.c12 - B.c22)
  let p4 := A.c22 * (B.c21 - B.c11)
  let p5 := (A.c11 + A.c12) * B.c22
  let p6 := (A.c21 - A.c11) * (B.c11 + B.c12)
  let p7 := (A.c12 - A.c22) * (B.c21 + B.c22)
  { c11 := p1 + p4 - p5 + p7
    c12 := p3 + p5
    c21 := p2 + p4
    c22 := p1 + p3 - p2 + p6 }

/-- Exact correctness of Strassen's formulas (23.4), valid for noncommutative
blocks and hence for matrix blocks. -/
theorem higham23_eq23_4_strassen_correct (A B : Higham23Block2 (R := R)) :
    higham23Strassen2 A B = higham23BlockMul A B := by
  cases A
  cases B
  apply Higham23Block2.ext <;>
    simp [higham23Strassen2, higham23BlockMul] <;>
    noncomm_ring

/-- The symbolic small-entry example on p. 442.  Conventional multiplication
    produces `ε²` in the lower-right entry, while Strassen's literal operation
    graph forms the displayed cancellation of four order-one terms.  This is
    the exact algebraic content of the example; the following `O(u/ε²)` prose
    requires a quantified floating-point family and is intentionally separate. -/
theorem higham23_strassen_small_entry_example (ε : ℝ) :
    let A : Higham23Block2 (R := ℝ) :=
      { c11 := 1, c12 := 0, c21 := 0, c22 := 1 }
    let B : Higham23Block2 (R := ℝ) :=
      { c11 := 1, c12 := ε, c21 := ε, c22 := ε ^ 2 }
    (higham23BlockMul A B).c22 = ε ^ 2 ∧
      (higham23Strassen2 A B).c22 =
        2 * (1 + ε ^ 2) + (ε - ε ^ 2) - 1 - (1 + ε) ∧
      2 * (1 + ε ^ 2) + (ε - ε ^ 2) - 1 - (1 + ε) = ε ^ 2 := by
  dsimp [higham23BlockMul, higham23Strassen2]
  constructor
  · ring
  constructor <;> ring

/-- Equation (23.6): Winograd's 15-addition variant of Strassen's method. -/
def higham23WinogradStrassen2
    (A B : Higham23Block2 (R := R)) : Higham23Block2 (R := R) :=
  let s1 := A.c21 + A.c22
  let s2 := s1 - A.c11
  let s3 := A.c11 - A.c21
  let s4 := A.c12 - s2
  let s5 := B.c12 - B.c11
  let s6 := B.c22 - s5
  let s7 := B.c22 - B.c12
  let s8 := s6 - B.c21
  let m1 := s2 * s6
  let m2 := A.c11 * B.c11
  let m3 := A.c12 * B.c21
  let m4 := s3 * s7
  let m5 := s1 * s5
  let m6 := s4 * B.c22
  let m7 := A.c22 * s8
  let t1 := m1 + m2
  let t2 := t1 + m4
  { c11 := m2 + m3
    c12 := t1 + m5 + m6
    c21 := t2 - m7
    c22 := t2 + m5 }

/-- Exact correctness of Winograd's variant (23.6). -/
theorem higham23_eq23_6_winogradStrassen_correct
    (A B : Higham23Block2 (R := R)) :
    higham23WinogradStrassen2 A B = higham23BlockMul A B := by
  cases A
  cases B
  apply Higham23Block2.ext <;>
    simp [higham23WinogradStrassen2, higham23BlockMul] <;>
    noncomm_ring

/-- Exact recursive operation semantics underlying equation (23.5).  The
second argument is the number of Strassen levels above the conventional
threshold `2^r`; the pair stores multiplication and addition counts. -/
def higham23StrassenCosts (r : ℕ) : ℕ → ℕ × ℕ
  | 0 => (8 ^ r, 4 ^ r * (2 ^ r - 1))
  | depth + 1 =>
      let previous := higham23StrassenCosts r depth
      (7 * previous.1, 7 * previous.2 + 18 * 4 ^ (r + depth))

/-- The multiplication-count solution in (23.5). -/
theorem higham23_strassenCosts_mul (r depth : ℕ) :
    (higham23StrassenCosts r depth).1 = 7 ^ depth * 8 ^ r := by
  induction depth with
  | zero => simp [higham23StrassenCosts]
  | succ depth ih =>
      simp [higham23StrassenCosts, ih, pow_succ]
      ring

/-- Subtraction-free form of the addition-count solution in (23.5). -/
theorem higham23_strassenCosts_add_augmented (r depth : ℕ) :
    (higham23StrassenCosts r depth).2 + 6 * 4 ^ (r + depth) =
      4 ^ r * (2 ^ r + 5) * 7 ^ depth := by
  induction depth with
  | zero =>
      have hpow : 1 ≤ 2 ^ r := Nat.one_le_two_pow
      simp only [higham23StrassenCosts, Nat.add_zero, pow_zero,
        Nat.mul_one]
      rw [Nat.mul_comm 6 (4 ^ r), ← Nat.mul_add]
      congr 1
      omega
  | succ depth ih =>
      simp only [higham23StrassenCosts]
      rw [← Nat.add_assoc r depth 1, pow_succ]
      calc
        7 * (higham23StrassenCosts r depth).2 + 18 * 4 ^ (r + depth) +
            6 * (4 ^ (r + depth) * 4) =
            7 * ((higham23StrassenCosts r depth).2 +
              6 * 4 ^ (r + depth)) := by ring
        _ = 7 * (4 ^ r * (2 ^ r + 5) * 7 ^ depth) := by rw [ih]
        _ = 4 ^ r * (2 ^ r + 5) * 7 ^ (depth + 1) := by
          rw [pow_succ]
          ring

/-- Equation (23.5), obtained from the recursive operation semantics. -/
theorem higham23_eq23_5_strassen_costs (r k : ℕ) (hrk : r ≤ k) :
    higham23StrassenCosts r (k - r) =
      (7 ^ (k - r) * 8 ^ r,
        4 ^ r * (2 ^ r + 5) * 7 ^ (k - r) - 6 * 4 ^ k) := by
  apply Prod.ext
  · exact higham23_strassenCosts_mul r (k - r)
  · simp only
    apply Nat.eq_sub_of_add_eq
    have h := higham23_strassenCosts_add_augmented r (k - r)
    rwa [Nat.add_sub_of_le hrk] at h

end BlockAlgorithms

end NumStability
