/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter23.BlockAlgorithms
import NumStability.Source.Higham.Chapter23.ConventionalMultiplication
import NumStability.Source.Higham.Chapter23.ErrorRecurrences
import NumStability.Source.Higham.Chapter23.GammaAsymptotics
import NumStability.Source.Higham.Chapter23.Theorem02.ErrorRelations
import NumStability.Source.Higham.Chapter23.Theorem02.ExactMajorant
import NumStability.Source.Higham.Chapter23.Theorem02.Execution
import NumStability.Source.Higham.Chapter23.Theorem02.RecursiveMatrix

namespace NumStability

open scoped BigOperators Topology
open Filter

/-!
# Higham Chapter 23, Theorem 23.2: Strassen error bound

This module proves the exact nonlinear bound for the literal recursive
Strassen evaluator, separates its first-order coefficient and quadratic
remainder, and derives the closed coefficient stated in Theorem 23.2.
-/

/-- Theorem 23.2 at exact nonlinear radius.  Unlike the scalar recurrence
surface, this theorem is proved by induction over the actual recursively
rounded Strassen evaluator. -/
theorem higham23_theorem23_2_strassen_exactMajorant
    (fp : FPModel) (r : ℕ) (hvalid : gammaValid fp (2 ^ r)) :
    ∀ depth (A B : Higham23RecursiveMatrix r depth) (a b : ℝ),
      0 ≤ a → 0 ≤ b →
      Higham23RecursiveMaxNormLe r depth A a →
      Higham23RecursiveMaxNormLe r depth B b →
      Higham23RecursiveErrorLe r depth (A * B)
        (higham23FlStrassenRecursive fp r depth A B)
        (higham23StrassenExactMajorant fp r depth * a * b) := by
  intro depth
  induction depth with
  | zero =>
      intro A B a b ha _hb hA hB
      intro i j
      have hcomp := higham23_eq23_10_conventional_componentwise
        fp A B hvalid i j
      have hsum : (∑ k : Fin (2 ^ r), |A i k| * |B k j|) ≤
          ((2 ^ r : ℕ) : ℝ) * a * b := by
        calc
          (∑ k : Fin (2 ^ r), |A i k| * |B k j|) ≤
              ∑ _k : Fin (2 ^ r), a * b := by
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul (hA i k) (hB k j) (abs_nonneg _) ha
          _ = ((2 ^ r : ℕ) : ℝ) * a * b := by simp; ring
      change |(A * B) i j - higham23FlMatrixMul fp A B i j| ≤ _
      calc
        |(A * B) i j - higham23FlMatrixMul fp A B i j| ≤
            gamma fp (2 ^ r) *
              ∑ k : Fin (2 ^ r), |A i k| * |B k j| := hcomp
        _ ≤ gamma fp (2 ^ r) *
            (((2 ^ r : ℕ) : ℝ) * a * b) :=
          mul_le_mul_of_nonneg_left hsum (gamma_nonneg fp hvalid)
        _ = higham23StrassenExactMajorant fp r 0 * a * b := by
          simp [higham23StrassenExactMajorant]
          ring
  | succ depth ih =>
      intro A B a b ha hb hA hB
      rcases hA with ⟨hA11, hA12, hA21, hA22⟩
      rcases hB with ⟨hB11, hB12, hB21, hB22⟩
      let u := fp.u
      let m : ℝ := (2 ^ (r + depth) : ℕ)
      let e := higham23StrassenExactMajorant fp r depth
      let HE := higham23StrassenHeavyError m e u
      let LE := higham23StrassenLightError m e u
      let HN := higham23StrassenHeavyNorm m e u
      let LN := higham23StrassenLightNorm m e u
      let q1N := (1 + u) * (HN + LN)
      let q2N := (1 + u) * (q1N + LN)
      let roundN := u * (HN + LN) + u * (q1N + LN) + u * (q2N + HN)
      have he0 : 0 ≤ e := higham23_strassenExactMajorant_nonneg fp r depth hvalid
      have hm0 : 0 ≤ m := by dsimp [m]; positivity
      have hu1 : 0 ≤ 1 + u := by dsimp [u]; linarith [fp.u_nonneg]
      have haHat : 0 ≤ 2 * (1 + u) * a := by positivity
      have hbHat : 0 ≤ 2 * (1 + u) * b := by positivity
      have hHE0 : 0 ≤ HE := by
        dsimp [HE, higham23StrassenHeavyError, u]
        have hp : 0 ≤ 8 * fp.u + 4 * fp.u ^ 2 := by
          nlinarith [fp.u_nonneg, sq_nonneg fp.u]
        positivity
      have hLE0 : 0 ≤ LE := by
        dsimp [LE, higham23StrassenLightError, u]
        exact add_nonneg
          (mul_nonneg hm0 (mul_nonneg (by norm_num) fp.u_nonneg))
          (mul_nonneg (mul_nonneg (by norm_num) hu1) he0)
      have hHN0 : 0 ≤ HN := by
        dsimp [HN, higham23StrassenHeavyNorm]
        positivity
      have hLN0 : 0 ≤ LN := by
        dsimp [LN, higham23StrassenLightNorm]
        positivity
      have hq1N0 : 0 ≤ q1N := by dsimp [q1N]; positivity
      have hq2N0 : 0 ≤ q2N := by dsimp [q2N]; positivity
      have hroundN0 : 0 ≤ roundN := by
        dsimp [roundN]
        exact add_nonneg
          (add_nonneg
            (mul_nonneg fp.u_nonneg (add_nonneg hHN0 hLN0))
            (mul_nonneg fp.u_nonneg (add_nonneg hq1N0 hLN0)))
          (mul_nonneg fp.u_nonneg (add_nonneg hq2N0 hHN0))
      have hstepRadius :
          (2 * HE + 2 * LE) * a * b + roundN * a * b =
            higham23StrassenExactMajorant fp r (depth + 1) * a * b := by
        dsimp [higham23StrassenExactMajorant, roundN, q1N, q2N,
          HE, LE, HN, LN, u, m, e]
        ring

      let x1 := higham23RecursiveFlAdd fp r depth A.c11 A.c22
      let y1 := higham23RecursiveFlAdd fp r depth B.c11 B.c22
      let x2 := higham23RecursiveFlAdd fp r depth A.c21 A.c22
      let y3 := higham23RecursiveFlSub fp r depth B.c12 B.c22
      let y4 := higham23RecursiveFlSub fp r depth B.c21 B.c11
      let x5 := higham23RecursiveFlAdd fp r depth A.c11 A.c12
      let x6 := higham23RecursiveFlSub fp r depth A.c21 A.c11
      let y6 := higham23RecursiveFlAdd fp r depth B.c11 B.c12
      let x7 := higham23RecursiveFlSub fp r depth A.c12 A.c22
      let y7 := higham23RecursiveFlAdd fp r depth B.c21 B.c22
      let p1 := higham23FlStrassenRecursive fp r depth x1 y1
      let p2 := higham23FlStrassenRecursive fp r depth x2 B.c11
      let p3 := higham23FlStrassenRecursive fp r depth A.c11 y3
      let p4 := higham23FlStrassenRecursive fp r depth A.c22 y4
      let p5 := higham23FlStrassenRecursive fp r depth x5 B.c22
      let p6 := higham23FlStrassenRecursive fp r depth x6 y6
      let p7 := higham23FlStrassenRecursive fp r depth x7 y7

      have hx1 := higham23_recursiveFlAdd_pair fp r depth
        A.c11 A.c22 a ha hA11 hA22
      have hy1 := higham23_recursiveFlAdd_pair fp r depth
        B.c11 B.c22 b hb hB11 hB22
      have hx2 := higham23_recursiveFlAdd_pair fp r depth
        A.c21 A.c22 a ha hA21 hA22
      have hy3 := higham23_recursiveFlSub_pair fp r depth
        B.c12 B.c22 b hb hB12 hB22
      have hy4 := higham23_recursiveFlSub_pair fp r depth
        B.c21 B.c11 b hb hB21 hB11
      have hx5 := higham23_recursiveFlAdd_pair fp r depth
        A.c11 A.c12 a ha hA11 hA12
      have hx6 := higham23_recursiveFlSub_pair fp r depth
        A.c21 A.c11 a ha hA21 hA11
      have hy6 := higham23_recursiveFlAdd_pair fp r depth
        B.c11 B.c12 b hb hB11 hB12
      have hx7 := higham23_recursiveFlSub_pair fp r depth
        A.c12 A.c22 a ha hA12 hA22
      have hy7 := higham23_recursiveFlAdd_pair fp r depth
        B.c21 B.c22 b hb hB21 hB22
      have hBsum11_22 := higham23_recursiveMaxNormLe_add r depth
        B.c11 B.c22 hB11 hB22
      have hBsub12_22 := higham23_recursiveMaxNormLe_sub r depth
        B.c12 B.c22 hB12 hB22
      have hBsub21_11 := higham23_recursiveMaxNormLe_sub r depth
        B.c21 B.c11 hB21 hB11
      have hBsum11_12 := higham23_recursiveMaxNormLe_add r depth
        B.c11 B.c12 hB11 hB12
      have hBsum21_22 := higham23_recursiveMaxNormLe_add r depth
        B.c21 B.c22 hB21 hB22

      have hp1Rec := ih x1 y1 (2 * (1 + u) * a) (2 * (1 + u) * b)
        haHat hbHat (by simpa [x1, u] using hx1.1) (by simpa [y1, u] using hy1.1)
      have hp1 := higham23_strassenHeavyProduct_transfer fp r depth
        (A.c11 + A.c22) x1 (B.c11 + B.c22) y1 p1 a b e ha hb
        (by simpa [x1, u] using hx1.1)
        (by convert hBsum11_22 using 1 <;> ring)
        (by simpa [y1, u] using hy1.1)
        (by simpa [x1, u] using hx1.2)
        (by simpa [y1, u] using hy1.2)
        (by simpa [p1, e] using hp1Rec)

      have hp2Rec := ih x2 B.c11 (2 * (1 + u) * a) b
        haHat hb (by simpa [x2, u] using hx2.1) hB11
      have hp2 := higham23_strassenLightLeftProduct_transfer fp r depth
        (A.c21 + A.c22) x2 B.c11 p2 a b e ha hb
        (by simpa [x2, u] using hx2.1) hB11
        (by simpa [x2, u] using hx2.2)
        (by simpa [p2, e] using hp2Rec)

      have hp3Rec := ih A.c11 y3 a (2 * (1 + u) * b)
        ha hbHat hA11 (by simpa [y3, u] using hy3.1)
      have hp3 := higham23_strassenLightRightProduct_transfer fp r depth
        A.c11 (B.c12 - B.c22) y3 p3 a b e ha hb hA11
        (by convert hBsub12_22 using 1 <;> ring)
        (by simpa [y3, u] using hy3.1)
        (by simpa [y3, u] using hy3.2)
        (by simpa [p3, e] using hp3Rec)

      have hp4Rec := ih A.c22 y4 a (2 * (1 + u) * b)
        ha hbHat hA22 (by simpa [y4, u] using hy4.1)
      have hp4 := higham23_strassenLightRightProduct_transfer fp r depth
        A.c22 (B.c21 - B.c11) y4 p4 a b e ha hb hA22
        (by convert hBsub21_11 using 1 <;> ring)
        (by simpa [y4, u] using hy4.1)
        (by simpa [y4, u] using hy4.2)
        (by simpa [p4, e] using hp4Rec)

      have hp5Rec := ih x5 B.c22 (2 * (1 + u) * a) b
        haHat hb (by simpa [x5, u] using hx5.1) hB22
      have hp5 := higham23_strassenLightLeftProduct_transfer fp r depth
        (A.c11 + A.c12) x5 B.c22 p5 a b e ha hb
        (by simpa [x5, u] using hx5.1) hB22
        (by simpa [x5, u] using hx5.2)
        (by simpa [p5, e] using hp5Rec)

      have hp6Rec := ih x6 y6 (2 * (1 + u) * a) (2 * (1 + u) * b)
        haHat hbHat (by simpa [x6, u] using hx6.1) (by simpa [y6, u] using hy6.1)
      have hp6 := higham23_strassenHeavyProduct_transfer fp r depth
        (A.c21 - A.c11) x6 (B.c11 + B.c12) y6 p6 a b e ha hb
        (by simpa [x6, u] using hx6.1)
        (by convert hBsum11_12 using 1 <;> ring)
        (by simpa [y6, u] using hy6.1)
        (by simpa [x6, u] using hx6.2)
        (by simpa [y6, u] using hy6.2)
        (by simpa [p6, e] using hp6Rec)

      have hp7Rec := ih x7 y7 (2 * (1 + u) * a) (2 * (1 + u) * b)
        haHat hbHat (by simpa [x7, u] using hx7.1) (by simpa [y7, u] using hy7.1)
      have hp7 := higham23_strassenHeavyProduct_transfer fp r depth
        (A.c12 - A.c22) x7 (B.c21 + B.c22) y7 p7 a b e ha hb
        (by simpa [x7, u] using hx7.1)
        (by convert hBsum21_22 using 1 <;> ring)
        (by simpa [y7, u] using hy7.1)
        (by simpa [x7, u] using hx7.2)
        (by simpa [y7, u] using hy7.2)
        (by simpa [p7, e] using hp7Rec)

      have hnH0 : 0 ≤ HN * a * b := by positivity
      have hnL0 : 0 ≤ LN * a * b := by positivity
      have hRound11raw := higham23_recursiveFourTermRecombination_error
        fp r depth p1 p4 p5 p7 (HN * a * b) (LN * a * b)
          (LN * a * b) (HN * a * b) hnH0 hnL0 hnL0 hnH0
          hp1.2 hp4.2 hp5.2 hp7.2
      have hRound11 : Higham23RecursiveErrorLe r depth
          (p1 + p4 - p5 + p7)
          (higham23RecursiveFlAdd fp r depth
            (higham23RecursiveFlSub fp r depth
              (higham23RecursiveFlAdd fp r depth p1 p4) p5) p7)
          (roundN * a * b) := by
        convert hRound11raw using 1 <;> dsimp [roundN, q1N, q2N, u] <;> ring
      have hProducts11a := higham23_recursiveErrorLe_add r depth
        ((A.c11 + A.c22) * (B.c11 + B.c22)) p1
        (A.c22 * (B.c21 - B.c11)) p4 hp1.1 hp4.1
      have hProducts11b := higham23_recursiveErrorLe_sub r depth
        ((A.c11 + A.c22) * (B.c11 + B.c22) + A.c22 * (B.c21 - B.c11))
        (p1 + p4) ((A.c11 + A.c12) * B.c22) p5 hProducts11a hp5.1
      have hProducts11c := higham23_recursiveErrorLe_add r depth
        ((A.c11 + A.c22) * (B.c11 + B.c22) + A.c22 * (B.c21 - B.c11) -
          (A.c11 + A.c12) * B.c22) (p1 + p4 - p5)
        ((A.c12 - A.c22) * (B.c21 + B.c22)) p7 hProducts11b hp7.1
      have hProducts11 : Higham23RecursiveErrorLe r depth
          ((A.c11 + A.c22) * (B.c11 + B.c22) + A.c22 * (B.c21 - B.c11) -
            (A.c11 + A.c12) * B.c22 + (A.c12 - A.c22) * (B.c21 + B.c22))
          (p1 + p4 - p5 + p7) ((2 * HE + 2 * LE) * a * b) := by
        convert hProducts11c using 1 <;> dsimp [HE, LE] <;> ring
      have h11raw := higham23_recursiveErrorLe_trans r depth _ _ _
        hProducts11 hRound11
      have h11 : Higham23RecursiveErrorLe r depth (A * B).c11
          (higham23FlStrassenRecursive fp r (depth + 1) A B).c11
          (higham23StrassenExactMajorant fp r (depth + 1) * a * b) := by
        have hc := congrArg (fun X : Higham23Block2
            (R := Higham23RecursiveMatrix r depth) ↦ X.c11)
          (higham23_eq23_4_strassen_correct A B)
        change (higham23Strassen2 A B).c11 = (A * B).c11 at hc
        rw [← hc, ← hstepRadius]
        simpa [higham23Strassen2, higham23FlStrassenRecursive, p1, p4, p5, p7,
          x1, y1, y4, x5, x7, y7] using h11raw

      have hProducts22a := higham23_recursiveErrorLe_add r depth
        ((A.c11 + A.c22) * (B.c11 + B.c22)) p1
        (A.c11 * (B.c12 - B.c22)) p3 hp1.1 hp3.1
      have hProducts22b := higham23_recursiveErrorLe_sub r depth
        ((A.c11 + A.c22) * (B.c11 + B.c22) + A.c11 * (B.c12 - B.c22))
        (p1 + p3) ((A.c21 + A.c22) * B.c11) p2 hProducts22a hp2.1
      have hProducts22c := higham23_recursiveErrorLe_add r depth
        ((A.c11 + A.c22) * (B.c11 + B.c22) + A.c11 * (B.c12 - B.c22) -
          (A.c21 + A.c22) * B.c11) (p1 + p3 - p2)
        ((A.c21 - A.c11) * (B.c11 + B.c12)) p6 hProducts22b hp6.1
      have hProducts22 : Higham23RecursiveErrorLe r depth
          ((A.c11 + A.c22) * (B.c11 + B.c22) + A.c11 * (B.c12 - B.c22) -
            (A.c21 + A.c22) * B.c11 +
              (A.c21 - A.c11) * (B.c11 + B.c12))
          (p1 + p3 - p2 + p6)
          ((2 * HE + 2 * LE) * a * b) := by
        convert hProducts22c using 1 <;> dsimp [HE, LE] <;> ring
      have hRound22raw := higham23_recursiveFourTermRecombination_error
        fp r depth p1 p3 p2 p6 (HN * a * b) (LN * a * b)
          (LN * a * b) (HN * a * b) hnH0 hnL0 hnL0 hnH0
          hp1.2 hp3.2 hp2.2 hp6.2
      have hRound22 : Higham23RecursiveErrorLe r depth
          (p1 + p3 - p2 + p6)
          (higham23RecursiveFlAdd fp r depth
            (higham23RecursiveFlSub fp r depth
              (higham23RecursiveFlAdd fp r depth p1 p3) p2) p6)
          (roundN * a * b) := by
        convert hRound22raw using 1 <;> dsimp [roundN, q1N, q2N, u] <;> ring
      have h22raw := higham23_recursiveErrorLe_trans r depth _ _ _
        hProducts22 hRound22
      have h22 : Higham23RecursiveErrorLe r depth (A * B).c22
          (higham23FlStrassenRecursive fp r (depth + 1) A B).c22
          (higham23StrassenExactMajorant fp r (depth + 1) * a * b) := by
        have hc := congrArg (fun X : Higham23Block2
            (R := Higham23RecursiveMatrix r depth) ↦ X.c22)
          (higham23_eq23_4_strassen_correct A B)
        change (higham23Strassen2 A B).c22 = (A * B).c22 at hc
        rw [← hc, ← hstepRadius]
        simpa [higham23Strassen2, higham23FlStrassenRecursive, p1, p2, p3, p6,
          x1, y1, x2, y3, x6, y6] using h22raw

      have hHNgeLN : LN ≤ HN := by
        dsimp [LN, HN, higham23StrassenLightNorm,
          higham23StrassenHeavyNorm]
        have hs : 0 ≤ 2 * (1 + u) * (m + e) := by positivity
        have hfac : 0 ≤ 2 * (1 + u) - 1 := by
          dsimp [u]
          linarith [fp.u_nonneg]
        nlinarith [mul_nonneg hs hfac]
      have hSmallRadius :
          (2 * LE * a * b + u * (2 * LN * a * b)) ≤
            higham23StrassenExactMajorant fp r (depth + 1) * a * b := by
        have hab0 : 0 ≤ a * b := mul_nonneg ha hb
        have hu0 : 0 ≤ u := by exact fp.u_nonneg
        have hfirst : u * (2 * LN) ≤ u * (HN + LN) := by
          exact mul_le_mul_of_nonneg_left (by linarith) hu0
        have hroundLower : u * (2 * LN) ≤ roundN := by
          have ht2 : 0 ≤ u * (q1N + LN) :=
            mul_nonneg hu0 (add_nonneg hq1N0 hLN0)
          have ht3 : 0 ≤ u * (q2N + HN) :=
            mul_nonneg hu0 (add_nonneg hq2N0 hHN0)
          dsimp [roundN]
          linarith
        have hcoef :
            2 * LE + u * (2 * LN) ≤ 2 * HE + 2 * LE + roundN := by
          linarith
        calc
          2 * LE * a * b + u * (2 * LN * a * b) =
              (2 * LE + u * (2 * LN)) * (a * b) := by ring
          _ ≤ (2 * HE + 2 * LE + roundN) * (a * b) :=
            mul_le_mul_of_nonneg_right hcoef hab0
          _ = (2 * HE + 2 * LE) * a * b + roundN * a * b := by ring
          _ = _ := hstepRadius
      have h12prod := higham23_recursiveErrorLe_add r depth
        (A.c11 * (B.c12 - B.c22)) p3 ((A.c11 + A.c12) * B.c22) p5
        hp3.1 hp5.1
      have h12round := higham23_recursiveFlAdd_error fp r depth p3 p5
        (LN * a * b) (LN * a * b) hnL0 hnL0 hp3.2 hp5.2
      have h12raw := higham23_recursiveErrorLe_trans r depth _ _ _ h12prod h12round
      have h12 : Higham23RecursiveErrorLe r depth (A * B).c12
          (higham23FlStrassenRecursive fp r (depth + 1) A B).c12
          (higham23StrassenExactMajorant fp r (depth + 1) * a * b) := by
        have hc := congrArg (fun X : Higham23Block2
            (R := Higham23RecursiveMatrix r depth) ↦ X.c12)
          (higham23_eq23_4_strassen_correct A B)
        change (higham23Strassen2 A B).c12 = (A * B).c12 at hc
        have hm := higham23_recursiveErrorLe_mono r depth _ _ h12raw
          (by
            calc
              LE * a * b + LE * a * b + fp.u * (LN * a * b + LN * a * b) =
                  2 * LE * a * b + u * (2 * LN * a * b) := by dsimp [u]; ring
              _ ≤ _ := hSmallRadius)
        rw [← hc]
        simpa [higham23Strassen2, higham23FlStrassenRecursive, p3, p5,
          y3, x5] using hm
      have h21prod := higham23_recursiveErrorLe_add r depth
        ((A.c21 + A.c22) * B.c11) p2 (A.c22 * (B.c21 - B.c11)) p4
        hp2.1 hp4.1
      have h21round := higham23_recursiveFlAdd_error fp r depth p2 p4
        (LN * a * b) (LN * a * b) hnL0 hnL0 hp2.2 hp4.2
      have h21raw := higham23_recursiveErrorLe_trans r depth _ _ _ h21prod h21round
      have h21 : Higham23RecursiveErrorLe r depth (A * B).c21
          (higham23FlStrassenRecursive fp r (depth + 1) A B).c21
          (higham23StrassenExactMajorant fp r (depth + 1) * a * b) := by
        have hc := congrArg (fun X : Higham23Block2
            (R := Higham23RecursiveMatrix r depth) ↦ X.c21)
          (higham23_eq23_4_strassen_correct A B)
        change (higham23Strassen2 A B).c21 = (A * B).c21 at hc
        have hm := higham23_recursiveErrorLe_mono r depth _ _ h21raw
          (by
            calc
              LE * a * b + LE * a * b + fp.u * (LN * a * b + LN * a * b) =
                  2 * LE * a * b + u * (2 * LN * a * b) := by dsimp [u]; ring
              _ ≤ _ := hSmallRadius)
        rw [← hc]
        simpa [higham23Strassen2, higham23FlStrassenRecursive, p2, p4,
          x2, y4] using hm
      exact ⟨h11, h12, h21, h22⟩

/-! ## First-order source coefficient and genuine quadratic remainder -/

/-- The exact one-level scalar majorant generated by the literal Strassen
dataflow. -/
noncomputable def higham23StrassenStepMajorant (m e u : ℝ) : ℝ :=
  let heavyError := higham23StrassenHeavyError m e u
  let lightError := higham23StrassenLightError m e u
  let heavyNorm := higham23StrassenHeavyNorm m e u
  let lightNorm := higham23StrassenLightNorm m e u
  let q1Norm := (1 + u) * (heavyNorm + lightNorm)
  let q2Norm := (1 + u) * (q1Norm + lightNorm)
  2 * heavyError + 2 * lightError +
    u * (heavyNorm + lightNorm) + u * (q1Norm + lightNorm) +
      u * (q2Norm + heavyNorm)

/-- Nonlinear part left after removing the source's one-level linearization
`46*m*u + 12*e`. -/
noncomputable def higham23StrassenStepResidual (m e u : ℝ) : ℝ :=
  higham23StrassenStepMajorant m e u - (46 * m * u + 12 * e)

private noncomputable def higham23StrassenStepMQuadratic (u : ℝ) : ℝ :=
  70 + 54 * u + 22 * u ^ 2 + 4 * u ^ 3

private noncomputable def higham23StrassenStepEQuadratic (u : ℝ) : ℝ :=
  46 + 70 * u + 54 * u ^ 2 + 22 * u ^ 3 + 4 * u ^ 4

/-- Exact factorization showing that every term discarded by the 12/46
linearization has total order at least two when `e = O(u)`. -/
theorem higham23_strassenStepResidual_factor (m e u : ℝ) :
    higham23StrassenStepResidual m e u =
      m * u ^ 2 * higham23StrassenStepMQuadratic u +
        e * u * higham23StrassenStepEQuadratic u := by
  unfold higham23StrassenStepResidual higham23StrassenStepMajorant
    higham23StrassenStepMQuadratic higham23StrassenStepEQuadratic
    higham23StrassenHeavyError higham23StrassenLightError
    higham23StrassenHeavyNorm higham23StrassenLightNorm
  ring

private theorem higham23_strassenStepMQuadratic_continuousAt :
    ContinuousAt higham23StrassenStepMQuadratic 0 := by
  unfold higham23StrassenStepMQuadratic
  fun_prop

private theorem higham23_strassenStepEQuadratic_continuousAt :
    ContinuousAt higham23StrassenStepEQuadratic 0 := by
  unfold higham23StrassenStepEQuadratic
  fun_prop

/-- A one-level Strassen residual preserves quadratic order whenever the
recursive error entering that level is first order. -/
theorem higham23_strassenStepResidual_isBigO_u_sq
    (m : ℝ) (e : ℝ → ℝ)
    (he : e =O[𝓝 0] (fun u : ℝ ↦ u)) :
    (fun u : ℝ ↦ higham23StrassenStepResidual m (e u) u)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
  have huSq : (fun u : ℝ ↦ u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) :=
    Asymptotics.isBigO_refl _ _
  have hMCoeff :
      (fun u : ℝ ↦ m * higham23StrassenStepMQuadratic u)
        =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    (continuousAt_const.mul higham23_strassenStepMQuadratic_continuousAt).isBigO_one ℝ
  have hMTerm :
      (fun u : ℝ ↦ m * u ^ 2 * higham23StrassenStepMQuadratic u)
        =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    have h := huSq.mul hMCoeff
    simpa only [mul_one, mul_assoc, mul_comm, mul_left_comm] using h
  have hu : (fun u : ℝ ↦ u) =O[𝓝 0] (fun u : ℝ ↦ u) :=
    Asymptotics.isBigO_refl _ _
  have hECoeff :
      (fun u : ℝ ↦ higham23StrassenStepEQuadratic u)
        =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    higham23_strassenStepEQuadratic_continuousAt.isBigO_one ℝ
  have hETerm :
      (fun u : ℝ ↦ e u * u * higham23StrassenStepEQuadratic u)
        =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    have h := (he.mul hu).mul hECoeff
    simpa only [pow_two, mul_one, mul_assoc] using h
  have h := hMTerm.add hETerm
  apply h.congr'
  · exact Filter.Eventually.of_forall fun u ↦ by
      exact (higham23_strassenStepResidual_factor m (e u) u).symm
  · exact Filter.EventuallyEq.rfl

/-- The exact nonlinear Strassen majorant as a function of a variable unit
roundoff.  At depth zero it is the exact gamma split; recursive levels use
the literal one-level majorant. -/
noncomputable def higham23StrassenMajorantFamily (r : ℕ) : ℕ → ℝ → ℝ
  | 0, u =>
      (4 : ℝ) ^ r * u +
        ((2 ^ r : ℕ) : ℝ) * higham23GammaRemainder (2 ^ r) u
  | depth + 1, u =>
      higham23StrassenStepMajorant ((2 ^ (r + depth) : ℕ) : ℝ)
        (higham23StrassenMajorantFamily r depth u) u

/-- The remainder after removing the canonical 12/46 first-order
coefficient from the exact nonlinear majorant family. -/
noncomputable def higham23StrassenMajorantRemainder
    (r depth : ℕ) (u : ℝ) : ℝ :=
  higham23StrassenMajorantFamily r depth u -
    higham23StrassenErrorCoefficient r depth * u

/-- The fixed-`FPModel` exact majorant is the variable-roundoff family
evaluated at `fp.u`. -/
theorem higham23_strassenExactMajorant_eq_family
    (fp : FPModel) (r depth : ℕ) (hvalid : gammaValid fp (2 ^ r)) :
    higham23StrassenExactMajorant fp r depth =
      higham23StrassenMajorantFamily r depth fp.u := by
  induction depth with
  | zero =>
      rw [higham23StrassenExactMajorant, higham23StrassenMajorantFamily,
        higham23_gamma_split fp (2 ^ r) hvalid]
      norm_num [Nat.cast_pow]
      have hp : (2 : ℝ) ^ r * (2 : ℝ) ^ r = (4 : ℝ) ^ r := by
        rw [← mul_pow]
        norm_num
      calc
        (2 : ℝ) ^ r *
              ((2 : ℝ) ^ r * fp.u + higham23GammaRemainder (2 ^ r) fp.u) =
            ((2 : ℝ) ^ r * (2 : ℝ) ^ r) * fp.u +
              (2 : ℝ) ^ r * higham23GammaRemainder (2 ^ r) fp.u := by ring
        _ = _ := by rw [hp]
  | succ depth ih =>
      rw [higham23StrassenExactMajorant, higham23StrassenMajorantFamily]
      unfold higham23StrassenStepMajorant
      rw [ih]

/-- The source's second-order term is genuinely `O(u²)` for every fixed
threshold and recursion depth. -/
theorem higham23_strassenMajorantRemainder_isBigO_u_sq (r depth : ℕ) :
    (fun u : ℝ ↦ higham23StrassenMajorantRemainder r depth u)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
  induction depth with
  | zero =>
      have h := (higham23_gammaRemainder_isBigO_u_sq (2 ^ r)).const_mul_left
        (((2 ^ r : ℕ) : ℝ))
      simpa only [higham23StrassenMajorantRemainder,
        higham23StrassenMajorantFamily,
        higham23_strassenErrorCoefficient_zero, add_sub_cancel_left] using h
  | succ depth ih =>
      let e : ℝ → ℝ := higham23StrassenMajorantFamily r depth
      let c := higham23StrassenErrorCoefficient r depth
      let m : ℝ := ((2 ^ (r + depth) : ℕ) : ℝ)
      have hu : (fun u : ℝ ↦ u) =O[𝓝 0] (fun u : ℝ ↦ u) :=
        Asymptotics.isBigO_refl _ _
      have huOne : (fun u : ℝ ↦ u) =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
        continuousAt_id.isBigO_one ℝ
      have huSqOu : (fun u : ℝ ↦ u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u) := by
        simpa only [pow_two, mul_one] using hu.mul huOne
      have hLinear : (fun u : ℝ ↦ c * u) =O[𝓝 0] (fun u : ℝ ↦ u) :=
        hu.const_mul_left c
      have he : e =O[𝓝 0] (fun u : ℝ ↦ u) := by
        have hsum := hLinear.add (ih.trans huSqOu)
        apply hsum.congr'
        · exact Filter.Eventually.of_forall fun u ↦ by
            dsimp [e, c, higham23StrassenMajorantRemainder]
            ring
        · exact Filter.EventuallyEq.rfl
      have hStep := higham23_strassenStepResidual_isBigO_u_sq m e he
      have hPrevious := ih.const_mul_left (12 : ℝ)
      have h := hStep.add hPrevious
      apply h.congr'
      · exact Filter.Eventually.of_forall fun u ↦ by
          dsimp [higham23StrassenMajorantRemainder,
            higham23StrassenMajorantFamily, e, c, m]
          rw [higham23_eq23_16_strassen_coefficient]
          unfold higham23StrassenStepResidual
          norm_num [Nat.cast_pow, pow_add]
          ring
      · exact Filter.EventuallyEq.rfl

/-- Theorem 23.2 with the exact 12/46 recurrence coefficient and its
explicit remainder family. -/
theorem higham23_theorem23_2_strassen_firstOrder
    (fp : FPModel) (r depth : ℕ) (hvalid : gammaValid fp (2 ^ r))
    (A B : Higham23RecursiveMatrix r depth) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : Higham23RecursiveMaxNormLe r depth A a)
    (hB : Higham23RecursiveMaxNormLe r depth B b) :
    Higham23RecursiveErrorLe r depth (A * B)
      (higham23FlStrassenRecursive fp r depth A B)
      ((higham23StrassenErrorCoefficient r depth * fp.u +
          higham23StrassenMajorantRemainder r depth fp.u) * a * b) := by
  have h := higham23_theorem23_2_strassen_exactMajorant fp r hvalid
    depth A B a b ha hb hA hB
  rw [higham23_strassenExactMajorant_eq_family fp r depth hvalid] at h
  have hsplit :
      higham23StrassenMajorantFamily r depth fp.u =
        higham23StrassenErrorCoefficient r depth * fp.u +
          higham23StrassenMajorantRemainder r depth fp.u := by
    unfold higham23StrassenMajorantRemainder
    ring
  rwa [hsplit] at h

/-- Theorem 23.2 with the closed coefficient printed in (23.14); the same
quadratic remainder is retained explicitly. -/
theorem higham23_theorem23_2_strassen_closedCoefficient_firstOrder
    (fp : FPModel) (r depth : ℕ) (hvalid : gammaValid fp (2 ^ r))
    (A B : Higham23RecursiveMatrix r depth) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : Higham23RecursiveMaxNormLe r depth A a)
    (hB : Higham23RecursiveMaxNormLe r depth B b) :
    Higham23RecursiveErrorLe r depth (A * B)
      (higham23FlStrassenRecursive fp r depth A B)
      ((higham23StrassenClosedCoefficient r depth * fp.u +
          higham23StrassenMajorantRemainder r depth fp.u) * a * b) := by
  have h := higham23_theorem23_2_strassen_firstOrder fp r depth hvalid
    A B a b ha hb hA hB
  apply higham23_recursiveErrorLe_mono r depth _ _ h
  have hc := higham23_strassenErrorCoefficient_le r depth
  have hs : 0 ≤ fp.u * a * b :=
    mul_nonneg (mul_nonneg fp.u_nonneg ha) hb
  have hm := mul_le_mul_of_nonneg_right hc hs
  dsimp [higham23StrassenClosedCoefficient] at hm ⊢
  nlinarith

end NumStability
