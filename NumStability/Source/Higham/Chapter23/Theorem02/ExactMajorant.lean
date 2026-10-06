/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Analysis.Rounding
import NumStability.Source.Higham.Chapter23.Theorem02.ErrorRelations
import NumStability.Source.Higham.Chapter23.Theorem02.RecursiveMatrix

namespace NumStability

/-!
# Higham Chapter 23, Theorem 23.2: exact nonlinear majorant

This module derives the exact nonlinear error majorant for one recursive
Strassen level, including the rounded four-term recombination and heavy/light
product-transfer bounds used by Theorem 23.2.
-/

/-- Rounding the three output operations in a four-term Strassen
recombination. -/
theorem higham23_recursiveFourTermRecombination_error
    (fp : FPModel) (r depth : ℕ)
    (P1 P2 P3 P4 : Higham23RecursiveMatrix r depth)
    (n1 n2 n3 n4 : ℝ)
    (hn1 : 0 ≤ n1) (hn2 : 0 ≤ n2) (hn3 : 0 ≤ n3) (hn4 : 0 ≤ n4)
    (hP1 : Higham23RecursiveMaxNormLe r depth P1 n1)
    (hP2 : Higham23RecursiveMaxNormLe r depth P2 n2)
    (hP3 : Higham23RecursiveMaxNormLe r depth P3 n3)
    (hP4 : Higham23RecursiveMaxNormLe r depth P4 n4) :
    let q1Norm := (1 + fp.u) * (n1 + n2)
    let q2Norm := (1 + fp.u) * (q1Norm + n3)
    Higham23RecursiveErrorLe r depth (P1 + P2 - P3 + P4)
      (higham23RecursiveFlAdd fp r depth
        (higham23RecursiveFlSub fp r depth
          (higham23RecursiveFlAdd fp r depth P1 P2) P3) P4)
      (fp.u * (n1 + n2) + fp.u * (q1Norm + n3) +
        fp.u * (q2Norm + n4)) := by
  dsimp only
  let Q1 := higham23RecursiveFlAdd fp r depth P1 P2
  let Q2 := higham23RecursiveFlSub fp r depth Q1 P3
  let q1Norm := (1 + fp.u) * (n1 + n2)
  let q2Norm := (1 + fp.u) * (q1Norm + n3)
  have hu1 : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
  have hq1n0 : 0 ≤ q1Norm :=
    mul_nonneg hu1 (add_nonneg hn1 hn2)
  have hq2n0 : 0 ≤ q2Norm :=
    mul_nonneg hu1 (add_nonneg hq1n0 hn3)
  have hE1 := higham23_recursiveFlAdd_error fp r depth
    P1 P2 n1 n2 hn1 hn2 hP1 hP2
  have hN1 := higham23_recursiveFlAdd_norm fp r depth
    P1 P2 n1 n2 hn1 hn2 hP1 hP2
  have hE2local := higham23_recursiveFlSub_error fp r depth
    Q1 P3 q1Norm n3 hq1n0 hn3 (by simpa [Q1, q1Norm] using hN1) hP3
  have hE1sub := higham23_recursiveErrorLe_sub r depth
    (P1 + P2) Q1 P3 P3 hE1 (higham23_recursiveErrorLe_refl r depth P3)
  have hE12raw := higham23_recursiveErrorLe_trans r depth
    (P1 + P2 - P3) (Q1 - P3) Q2 hE1sub hE2local
  have hE12 : Higham23RecursiveErrorLe r depth
      (P1 + P2 - P3) Q2
      (fp.u * (n1 + n2) + fp.u * (q1Norm + n3)) := by
    exact higham23_recursiveErrorLe_mono r depth _ _ hE12raw (by ring_nf; linarith)
  have hN2 := higham23_recursiveFlSub_norm fp r depth
    Q1 P3 q1Norm n3 hq1n0 hn3 (by simpa [Q1, q1Norm] using hN1) hP3
  have hE3local := higham23_recursiveFlAdd_error fp r depth
    Q2 P4 q2Norm n4 hq2n0 hn4 (by simpa [Q2, q2Norm] using hN2) hP4
  have hE12add := higham23_recursiveErrorLe_add r depth
    (P1 + P2 - P3) Q2 P4 P4 hE12
      (higham23_recursiveErrorLe_refl r depth P4)
  have hAll := higham23_recursiveErrorLe_trans r depth
    (P1 + P2 - P3 + P4) (Q2 + P4)
      (higham23RecursiveFlAdd fp r depth Q2 P4) hE12add hE3local
  exact higham23_recursiveErrorLe_mono r depth _ _ hAll (by ring_nf; linarith)

noncomputable def higham23StrassenHeavyError (m e u : ℝ) : ℝ :=
  m * (8 * u + 4 * u ^ 2) + 4 * (1 + u) ^ 2 * e

noncomputable def higham23StrassenLightError (m e u : ℝ) : ℝ :=
  m * (2 * u) + 2 * (1 + u) * e

noncomputable def higham23StrassenHeavyNorm (m e u : ℝ) : ℝ :=
  4 * (1 + u) ^ 2 * (m + e)

noncomputable def higham23StrassenLightNorm (m e u : ℝ) : ℝ :=
  2 * (1 + u) * (m + e)

/-- Two rounded input sums followed by a recursive product. -/
theorem higham23_strassenHeavyProduct_transfer
    (fp : FPModel) (r depth : ℕ)
    (X Xhat Y Yhat P : Higham23RecursiveMatrix r depth)
    (a b e : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hXhat : Higham23RecursiveMaxNormLe r depth Xhat
      (2 * (1 + fp.u) * a))
    (hY : Higham23RecursiveMaxNormLe r depth Y (2 * b))
    (hYhat : Higham23RecursiveMaxNormLe r depth Yhat
      (2 * (1 + fp.u) * b))
    (hXerr : Higham23RecursiveErrorLe r depth Xhat X (2 * fp.u * a))
    (hYerr : Higham23RecursiveErrorLe r depth Yhat Y (2 * fp.u * b))
    (hRec : Higham23RecursiveErrorLe r depth (Xhat * Yhat) P
      (e * (2 * (1 + fp.u) * a) * (2 * (1 + fp.u) * b))) :
    Higham23RecursiveErrorLe r depth (X * Y) P
        (higham23StrassenHeavyError
          ((2 ^ (r + depth) : ℕ) : ℝ) e fp.u * a * b) ∧
      Higham23RecursiveMaxNormLe r depth P
        (higham23StrassenHeavyNorm
          ((2 ^ (r + depth) : ℕ) : ℝ) e fp.u * a * b) := by
  have ht := higham23_recursiveProduct_transfer r depth X Xhat Y Yhat P
    (2 * (1 + fp.u) * a) (2 * b) (2 * fp.u * a) (2 * fp.u * b) e
    (mul_nonneg (mul_nonneg (by norm_num) (by linarith [fp.u_nonneg])) ha)
    (mul_nonneg (by norm_num) hb)
    (mul_nonneg (mul_nonneg (by norm_num) fp.u_nonneg) ha)
    (mul_nonneg (mul_nonneg (by norm_num) fp.u_nonneg) hb)
    hXhat hY (by convert hYhat using 1 <;> ring) hXerr hYerr
    (by convert hRec using 1 <;> ring)
  constructor
  · convert ht.1 using 1 <;> dsimp [higham23StrassenHeavyError] <;> ring
  · convert ht.2 using 1 <;> dsimp [higham23StrassenHeavyNorm] <;> ring

/-- One rounded left input sum followed by a recursive product. -/
theorem higham23_strassenLightLeftProduct_transfer
    (fp : FPModel) (r depth : ℕ)
    (X Xhat Y P : Higham23RecursiveMatrix r depth)
    (a b e : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hXhat : Higham23RecursiveMaxNormLe r depth Xhat
      (2 * (1 + fp.u) * a))
    (hY : Higham23RecursiveMaxNormLe r depth Y b)
    (hXerr : Higham23RecursiveErrorLe r depth Xhat X (2 * fp.u * a))
    (hRec : Higham23RecursiveErrorLe r depth (Xhat * Y) P
      (e * (2 * (1 + fp.u) * a) * b)) :
    Higham23RecursiveErrorLe r depth (X * Y) P
        (higham23StrassenLightError
          ((2 ^ (r + depth) : ℕ) : ℝ) e fp.u * a * b) ∧
      Higham23RecursiveMaxNormLe r depth P
        (higham23StrassenLightNorm
          ((2 ^ (r + depth) : ℕ) : ℝ) e fp.u * a * b) := by
  have ht := higham23_recursiveProduct_transfer r depth X Xhat Y Y P
    (2 * (1 + fp.u) * a) b (2 * fp.u * a) 0 e
    (mul_nonneg (mul_nonneg (by norm_num) (by linarith [fp.u_nonneg])) ha)
    hb (mul_nonneg (mul_nonneg (by norm_num) fp.u_nonneg) ha) (by norm_num)
    hXhat hY (by simpa using hY) hXerr
    (higham23_recursiveErrorLe_refl r depth Y)
    (by convert hRec using 1 <;> ring)
  constructor
  · convert ht.1 using 1 <;> dsimp [higham23StrassenLightError] <;> ring
  · convert ht.2 using 1 <;> dsimp [higham23StrassenLightNorm] <;> ring

/-- One rounded right input sum followed by a recursive product. -/
theorem higham23_strassenLightRightProduct_transfer
    (fp : FPModel) (r depth : ℕ)
    (X Y Yhat P : Higham23RecursiveMatrix r depth)
    (a b e : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hX : Higham23RecursiveMaxNormLe r depth X a)
    (hY : Higham23RecursiveMaxNormLe r depth Y (2 * b))
    (hYhat : Higham23RecursiveMaxNormLe r depth Yhat
      (2 * (1 + fp.u) * b))
    (hYerr : Higham23RecursiveErrorLe r depth Yhat Y (2 * fp.u * b))
    (hRec : Higham23RecursiveErrorLe r depth (X * Yhat) P
      (e * a * (2 * (1 + fp.u) * b))) :
    Higham23RecursiveErrorLe r depth (X * Y) P
        (higham23StrassenLightError
          ((2 ^ (r + depth) : ℕ) : ℝ) e fp.u * a * b) ∧
      Higham23RecursiveMaxNormLe r depth P
        (higham23StrassenLightNorm
          ((2 ^ (r + depth) : ℕ) : ℝ) e fp.u * a * b) := by
  have ht := higham23_recursiveProduct_transfer r depth X X Y Yhat P
    a (2 * b) 0 (2 * fp.u * b) e ha (mul_nonneg (by norm_num) hb)
    (by norm_num) (mul_nonneg (mul_nonneg (by norm_num) fp.u_nonneg) hb)
    hX hY (by convert hYhat using 1 <;> ring)
    (higham23_recursiveErrorLe_refl r depth X) hYerr
    (by convert hRec using 1 <;> ring)
  constructor
  · convert ht.1 using 1 <;> dsimp [higham23StrassenLightError] <;> ring
  · convert ht.2 using 1 <;> dsimp [higham23StrassenLightNorm] <;> ring

/-- Exact nonlinear coefficient proved for the literal recursive Strassen
evaluator.  Its linearization is the 12/46 recurrence in (23.16). -/
noncomputable def higham23StrassenExactMajorant
    (fp : FPModel) (r : ℕ) : ℕ → ℝ
  | 0 => ((2 ^ r : ℕ) : ℝ) * gamma fp (2 ^ r)
  | depth + 1 =>
      let u := fp.u
      let m : ℝ := (2 ^ (r + depth) : ℕ)
      let e := higham23StrassenExactMajorant fp r depth
      let heavyError := higham23StrassenHeavyError m e u
      let lightError := higham23StrassenLightError m e u
      let heavyNorm := higham23StrassenHeavyNorm m e u
      let lightNorm := higham23StrassenLightNorm m e u
      let q1Norm := (1 + u) * (heavyNorm + lightNorm)
      let q2Norm := (1 + u) * (q1Norm + lightNorm)
      2 * heavyError + 2 * lightError +
        u * (heavyNorm + lightNorm) + u * (q1Norm + lightNorm) +
          u * (q2Norm + heavyNorm)

theorem higham23_strassenExactMajorant_nonneg
    (fp : FPModel) (r depth : ℕ) (hvalid : gammaValid fp (2 ^ r)) :
    0 ≤ higham23StrassenExactMajorant fp r depth := by
  induction depth with
  | zero =>
      rw [higham23StrassenExactMajorant]
      exact mul_nonneg (Nat.cast_nonneg _) (gamma_nonneg fp hvalid)
  | succ depth ih =>
      dsimp only [higham23StrassenExactMajorant, higham23StrassenHeavyError,
        higham23StrassenLightError, higham23StrassenHeavyNorm,
        higham23StrassenLightNorm]
      have hu1 : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
      have hm : 0 ≤ ((2 ^ (r + depth) : ℕ) : ℝ) := Nat.cast_nonneg _
      have hpoly : 0 ≤ 8 * fp.u + 4 * fp.u ^ 2 := by
        nlinarith [fp.u_nonneg, sq_nonneg fp.u]
      have hHeavyError : 0 ≤
          ((2 ^ (r + depth) : ℕ) : ℝ) *
              (8 * fp.u + 4 * fp.u ^ 2) +
            4 * (1 + fp.u) ^ 2 * higham23StrassenExactMajorant fp r depth :=
        add_nonneg (mul_nonneg hm hpoly)
          (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) ih)
      have hLightError : 0 ≤
          ((2 ^ (r + depth) : ℕ) : ℝ) * (2 * fp.u) +
            2 * (1 + fp.u) * higham23StrassenExactMajorant fp r depth :=
        add_nonneg (mul_nonneg hm (mul_nonneg (by norm_num) fp.u_nonneg))
          (mul_nonneg (mul_nonneg (by norm_num) hu1) ih)
      have hHeavyNorm : 0 ≤ 4 * (1 + fp.u) ^ 2 *
          (((2 ^ (r + depth) : ℕ) : ℝ) +
            higham23StrassenExactMajorant fp r depth) := by positivity
      have hLightNorm : 0 ≤ 2 * (1 + fp.u) *
          (((2 ^ (r + depth) : ℕ) : ℝ) +
            higham23StrassenExactMajorant fp r depth) := by positivity
      have hq1 : 0 ≤ (1 + fp.u) *
          (4 * (1 + fp.u) ^ 2 *
              (((2 ^ (r + depth) : ℕ) : ℝ) +
                higham23StrassenExactMajorant fp r depth) +
            2 * (1 + fp.u) *
              (((2 ^ (r + depth) : ℕ) : ℝ) +
                higham23StrassenExactMajorant fp r depth)) := by positivity
      have hq2 : 0 ≤ (1 + fp.u) *
          ((1 + fp.u) *
              (4 * (1 + fp.u) ^ 2 *
                  (((2 ^ (r + depth) : ℕ) : ℝ) +
                    higham23StrassenExactMajorant fp r depth) +
                2 * (1 + fp.u) *
                  (((2 ^ (r + depth) : ℕ) : ℝ) +
                    higham23StrassenExactMajorant fp r depth)) +
            2 * (1 + fp.u) *
              (((2 ^ (r + depth) : ℕ) : ℝ) +
                higham23StrassenExactMajorant fp r depth)) := by positivity
      have ht1 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hHeavyError
      have ht2 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hLightError
      have ht3 := mul_nonneg fp.u_nonneg (add_nonneg hHeavyNorm hLightNorm)
      have ht4 := mul_nonneg fp.u_nonneg (add_nonneg hq1 hLightNorm)
      have ht5 := mul_nonneg fp.u_nonneg (add_nonneg hq2 hHeavyNorm)
      nlinarith

end NumStability
