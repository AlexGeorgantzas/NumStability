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
# Higham Chapter 23, Theorem 23.3: Winograd-Strassen execution

This module defines the literal recursively rounded Winograd-Strassen
evaluator with the fifteen additions performed in the dependency order of
equation (23.6).
-/

/-- Literal recursive Winograd--Strassen evaluation, with all 15 additions
rounded in the dependency order of (23.6). -/
noncomputable def higham23FlWinogradStrassenRecursive
    (fp : FPModel) (r : ℕ) :
    (depth : ℕ) → Higham23RecursiveMatrix r depth →
      Higham23RecursiveMatrix r depth → Higham23RecursiveMatrix r depth
  | 0, A, B => higham23FlMatrixMul fp A B
  | depth + 1, A, B =>
      let s1 := higham23RecursiveFlAdd fp r depth A.c21 A.c22
      let s2 := higham23RecursiveFlSub fp r depth s1 A.c11
      let s3 := higham23RecursiveFlSub fp r depth A.c11 A.c21
      let s4 := higham23RecursiveFlSub fp r depth A.c12 s2
      let s5 := higham23RecursiveFlSub fp r depth B.c12 B.c11
      let s6 := higham23RecursiveFlSub fp r depth B.c22 s5
      let s7 := higham23RecursiveFlSub fp r depth B.c22 B.c12
      let s8 := higham23RecursiveFlSub fp r depth s6 B.c21
      let m1 := higham23FlWinogradStrassenRecursive fp r depth s2 s6
      let m2 := higham23FlWinogradStrassenRecursive fp r depth A.c11 B.c11
      let m3 := higham23FlWinogradStrassenRecursive fp r depth A.c12 B.c21
      let m4 := higham23FlWinogradStrassenRecursive fp r depth s3 s7
      let m5 := higham23FlWinogradStrassenRecursive fp r depth s1 s5
      let m6 := higham23FlWinogradStrassenRecursive fp r depth s4 B.c22
      let m7 := higham23FlWinogradStrassenRecursive fp r depth A.c22 s8
      let t1 := higham23RecursiveFlAdd fp r depth m1 m2
      let t2 := higham23RecursiveFlAdd fp r depth t1 m4
      { c11 := higham23RecursiveFlAdd fp r depth m2 m3
        c12 := higham23RecursiveFlAdd fp r depth
          (higham23RecursiveFlAdd fp r depth t1 m5) m6
        c21 := higham23RecursiveFlSub fp r depth t2 m7
        c22 := higham23RecursiveFlAdd fp r depth t2 m5 }

end NumStability
