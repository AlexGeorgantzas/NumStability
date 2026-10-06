/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter23.ConventionalMultiplication
import NumStability.Source.Higham.Chapter23.Theorem02.ErrorRelations
import NumStability.Source.Higham.Chapter23.Theorem02.RecursiveMatrix

namespace NumStability

/-!
# Higham Chapter 23, Theorem 23.2: recursive Strassen execution

This module defines the literal recursively rounded Strassen evaluator. Its
base case uses conventional rounded multiplication and every block operation
follows the evaluation order of equation (23.4).
-/

/-- Literal recursive Strassen evaluation.  The base case calls the actual
left-to-right rounded dot-product matrix multiplication; every block sum and
output recombination is rounded entrywise in the order printed in (23.4). -/
noncomputable def higham23FlStrassenRecursive (fp : FPModel) (r : ℕ) :
    (depth : ℕ) → Higham23RecursiveMatrix r depth →
      Higham23RecursiveMatrix r depth → Higham23RecursiveMatrix r depth
  | 0, A, B => higham23FlMatrixMul fp A B
  | depth + 1, A, B =>
      let p1 := higham23FlStrassenRecursive fp r depth
        (higham23RecursiveFlAdd fp r depth A.c11 A.c22)
        (higham23RecursiveFlAdd fp r depth B.c11 B.c22)
      let p2 := higham23FlStrassenRecursive fp r depth
        (higham23RecursiveFlAdd fp r depth A.c21 A.c22) B.c11
      let p3 := higham23FlStrassenRecursive fp r depth A.c11
        (higham23RecursiveFlSub fp r depth B.c12 B.c22)
      let p4 := higham23FlStrassenRecursive fp r depth A.c22
        (higham23RecursiveFlSub fp r depth B.c21 B.c11)
      let p5 := higham23FlStrassenRecursive fp r depth
        (higham23RecursiveFlAdd fp r depth A.c11 A.c12) B.c22
      let p6 := higham23FlStrassenRecursive fp r depth
        (higham23RecursiveFlSub fp r depth A.c21 A.c11)
        (higham23RecursiveFlAdd fp r depth B.c11 B.c12)
      let p7 := higham23FlStrassenRecursive fp r depth
        (higham23RecursiveFlSub fp r depth A.c12 A.c22)
        (higham23RecursiveFlAdd fp r depth B.c21 B.c22)
      { c11 := higham23RecursiveFlAdd fp r depth
          (higham23RecursiveFlSub fp r depth
            (higham23RecursiveFlAdd fp r depth p1 p4) p5) p7
        c12 := higham23RecursiveFlAdd fp r depth p3 p5
        c21 := higham23RecursiveFlAdd fp r depth p2 p4
        c22 := higham23RecursiveFlAdd fp r depth
          (higham23RecursiveFlSub fp r depth
            (higham23RecursiveFlAdd fp r depth p1 p3) p2) p6 }

end NumStability
