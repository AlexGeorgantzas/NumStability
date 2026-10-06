/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter23.Theorem02.ErrorBound
import NumStability.Source.Higham.Chapter23.Theorem02.ExactMajorant
import NumStability.Source.Higham.Chapter23.ThreeMStrassen.Execution

namespace NumStability

open scoped Topology
open Filter

/-!
# Higham Chapter 23: combined 3M--Strassen exact majorant

The exact real and imaginary error majorants for the combined 3M--Strassen evaluator.
-/

/-- Exact nonlinear error theorem for the actual combined evaluator. The
`sA*sB ≤ 2*a*b` hypothesis is the scalar form of the source inequality
`(|A₁|+|A₂|)(|B₁|+|B₂|) ≤ 2|A||B|`. -/
theorem higham23_threeMStrassen_exactMajorant
    (fp : FPModel) (r depth : ℕ) (hvalid : gammaValid fp (2 ^ r))
    (A B : Higham23RecursiveComplex r depth) (a b sA sB : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hsA : 0 ≤ sA) (hsB : 0 ≤ sB)
    (hA1 : Higham23RecursiveMaxNormLe r depth A.1 a)
    (hA2 : Higham23RecursiveMaxNormLe r depth A.2 a)
    (hB1 : Higham23RecursiveMaxNormLe r depth B.1 b)
    (hB2 : Higham23RecursiveMaxNormLe r depth B.2 b)
    (hAsum : Higham23RecursiveMaxNormLe r depth (A.1 + A.2) sA)
    (hBsum : Higham23RecursiveMaxNormLe r depth (B.1 + B.2) sB)
    (hSumProduct : sA * sB ≤ 2 * a * b) :
    let n : ℝ := ((2 ^ (r + depth) : ℕ) : ℝ)
    let e := higham23StrassenExactMajorant fp r depth
    Higham23RecursiveComplexErrorLe r depth
      (higham23ThreeMExactRecursive r depth A B)
      (higham23FlThreeMStrassen fp r depth A B)
      (higham23ThreeMStrassenRealMajorant n e fp.u * a * b)
      (higham23ThreeMStrassenImagMajorant n e fp.u * a * b) := by
  dsimp only
  let n : ℝ := ((2 ^ (r + depth) : ℕ) : ℝ)
  let e := higham23StrassenExactMajorant fp r depth
  let u := fp.u
  let As := higham23RecursiveFlAdd fp r depth A.1 A.2
  let Bs := higham23RecursiveFlAdd fp r depth B.1 B.2
  let P1 := higham23FlStrassenRecursive fp r depth A.1 B.1
  let P2 := higham23FlStrassenRecursive fp r depth A.2 B.2
  let P3 := higham23FlStrassenRecursive fp r depth As Bs
  let Q := (A.1 + A.2) * (B.1 + B.2)
  let N1 := higham23ThreeMStrassenP1Norm n e
  let T := higham23ThreeMStrassenP3Error n e u
  let N3 := higham23ThreeMStrassenP3Norm n e u
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have he : 0 ≤ e := higham23_strassenExactMajorant_nonneg fp r depth hvalid
  have hu : 0 ≤ u := fp.u_nonneg
  have hu1 : 0 ≤ 1 + u := by linarith
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hsprod : 0 ≤ sA * sB := mul_nonneg hsA hsB
  have hN1 : 0 ≤ N1 := by dsimp [N1, higham23ThreeMStrassenP1Norm]; positivity
  have hT : 0 ≤ T := by
    dsimp [T, higham23ThreeMStrassenP3Error]
    positivity
  have hN3 : 0 ≤ N3 := by
    dsimp [N3, higham23ThreeMStrassenP3Norm]
    positivity
  have hAsErr : Higham23RecursiveErrorLe r depth (A.1 + A.2) As (u * sA) := by
    simpa [As, u] using
      higham23_recursiveFlAdd_error_of_sum_norm fp r depth A.1 A.2 sA hsA hAsum
  have hBsErr : Higham23RecursiveErrorLe r depth (B.1 + B.2) Bs (u * sB) := by
    simpa [Bs, u] using
      higham23_recursiveFlAdd_error_of_sum_norm fp r depth B.1 B.2 sB hsB hBsum
  have hAsNorm : Higham23RecursiveMaxNormLe r depth As ((1 + u) * sA) := by
    simpa [As, u] using
      higham23_recursiveFlAdd_norm_of_sum_norm fp r depth A.1 A.2 sA hsA hAsum
  have hBsNorm : Higham23RecursiveMaxNormLe r depth Bs ((1 + u) * sB) := by
    simpa [Bs, u] using
      higham23_recursiveFlAdd_norm_of_sum_norm fp r depth B.1 B.2 sB hsB hBsum
  have hP1err : Higham23RecursiveErrorLe r depth (A.1 * B.1) P1 (e * a * b) := by
    simpa [P1, e] using higham23_theorem23_2_strassen_exactMajorant
      fp r hvalid depth A.1 B.1 a b ha hb hA1 hB1
  have hP2err : Higham23RecursiveErrorLe r depth (A.2 * B.2) P2 (e * a * b) := by
    simpa [P2, e] using higham23_theorem23_2_strassen_exactMajorant
      fp r hvalid depth A.2 B.2 a b ha hb hA2 hB2
  have hP1exact := higham23_recursiveMaxNormLe_mul r depth A.1 B.1 a b ha hb hA1 hB1
  have hP2exact := higham23_recursiveMaxNormLe_mul r depth A.2 B.2 a b ha hb hA2 hB2
  have hP1normRaw := higham23_recursiveMaxNormLe_of_error r depth
    (A.1 * B.1) P1 hP1exact hP1err
  have hP2normRaw := higham23_recursiveMaxNormLe_of_error r depth
    (A.2 * B.2) P2 hP2exact hP2err
  have hP1norm : Higham23RecursiveMaxNormLe r depth P1 (N1 * a * b) := by
    convert hP1normRaw using 1 <;>
      dsimp [N1, n, e, higham23ThreeMStrassenP1Norm] <;> ring
  have hP2norm : Higham23RecursiveMaxNormLe r depth P2 (N1 * a * b) := by
    convert hP2normRaw using 1 <;>
      dsimp [N1, n, e, higham23ThreeMStrassenP1Norm] <;> ring
  have hP3rec : Higham23RecursiveErrorLe r depth (As * Bs) P3
      (e * ((1 + u) * sA) * ((1 + u) * sB)) := by
    simpa [P3, e] using higham23_theorem23_2_strassen_exactMajorant
      fp r hvalid depth As Bs ((1 + u) * sA) ((1 + u) * sB)
      (by positivity) (by positivity) hAsNorm hBsNorm
  have hBsNorm' : Higham23RecursiveMaxNormLe r depth Bs (sB + u * sB) := by
    convert hBsNorm using 1 <;> ring
  have hP3transfer := higham23_recursiveProduct_transfer r depth
    (A.1 + A.2) As (B.1 + B.2) Bs P3
    ((1 + u) * sA) sB (u * sA) (u * sB) e
    (by positivity) hsB (by positivity) (by positivity)
    hAsNorm hBsum hBsNorm'
    (higham23_recursiveErrorLe_symm r depth _ _ hAsErr)
    (higham23_recursiveErrorLe_symm r depth _ _ hBsErr)
    (by convert hP3rec using 1 <;> ring)
  have hP3err : Higham23RecursiveErrorLe r depth Q P3 (T * a * b) := by
    apply higham23_recursiveErrorLe_mono r depth _ _ hP3transfer.1
    have hcore : 0 ≤ n * u + n * u * (1 + u) + e * (1 + u) ^ 2 := by
      positivity
    have hscale := mul_le_mul_of_nonneg_left hSumProduct hcore
    dsimp [Q, T, n, e, u, higham23ThreeMStrassenP3Error] at hscale ⊢
    convert hscale using 1 <;> ring
  have hP3norm : Higham23RecursiveMaxNormLe r depth P3 (N3 * a * b) := by
    apply higham23_recursiveMaxNormLe_mono r depth _ hP3transfer.2
    have hcore : 0 ≤ (n + e) * (1 + u) ^ 2 := by positivity
    have hscale := mul_le_mul_of_nonneg_left hSumProduct hcore
    dsimp [N3, n, e, u, higham23ThreeMStrassenP3Norm] at hscale ⊢
    convert hscale using 1 <;> ring
  have hRealProd := higham23_recursiveErrorLe_sub r depth
    (A.1 * B.1) P1 (A.2 * B.2) P2 hP1err hP2err
  have hRealRound := higham23_recursiveFlSub_error fp r depth P1 P2
    (N1 * a * b) (N1 * a * b) (by positivity) (by positivity) hP1norm hP2norm
  have hRealRaw := higham23_recursiveErrorLe_trans r depth _ _ _ hRealProd hRealRound
  have hReal : Higham23RecursiveErrorLe r depth
      (A.1 * B.1 - A.2 * B.2)
      (higham23RecursiveFlSub fp r depth P1 P2)
      (higham23ThreeMStrassenRealMajorant n e u * a * b) := by
    convert hRealRaw using 1 <;>
      dsimp [N1, higham23ThreeMStrassenRealMajorant,
        higham23ThreeMStrassenP1Norm] <;> ring
  let Q1 := higham23RecursiveFlSub fp r depth P3 P1
  have hQ1prod := higham23_recursiveErrorLe_sub r depth Q P3
    (A.1 * B.1) P1 hP3err hP1err
  have hQ1round := higham23_recursiveFlSub_error fp r depth P3 P1
    (N3 * a * b) (N1 * a * b) (by positivity) (by positivity) hP3norm hP1norm
  have hQ1raw := higham23_recursiveErrorLe_trans r depth _ _ _ hQ1prod hQ1round
  have hQ1 : Higham23RecursiveErrorLe r depth (Q - A.1 * B.1) Q1
      ((T + e + u * (N3 + N1)) * a * b) := by
    convert hQ1raw using 1 <;> dsimp [Q1] <;> ring
  have hQ1normRaw := higham23_recursiveFlSub_norm fp r depth P3 P1
    (N3 * a * b) (N1 * a * b) (by positivity) (by positivity) hP3norm hP1norm
  have hQ1norm : Higham23RecursiveMaxNormLe r depth Q1
      ((1 + u) * (N3 + N1) * a * b) := by
    convert hQ1normRaw using 1 <;> dsimp [Q1] <;> ring
  have hImagProd := higham23_recursiveErrorLe_sub r depth
    (Q - A.1 * B.1) Q1 (A.2 * B.2) P2 hQ1 hP2err
  have hImagRound := higham23_recursiveFlSub_error fp r depth Q1 P2
    ((1 + u) * (N3 + N1) * a * b) (N1 * a * b)
    (by positivity) (by positivity) hQ1norm hP2norm
  have hImagRaw := higham23_recursiveErrorLe_trans r depth _ _ _ hImagProd hImagRound
  have hImag : Higham23RecursiveErrorLe r depth
      (Q - A.1 * B.1 - A.2 * B.2)
      (higham23RecursiveFlSub fp r depth Q1 P2)
      (higham23ThreeMStrassenImagMajorant n e u * a * b) := by
    convert hImagRaw using 1 <;>
      dsimp [higham23ThreeMStrassenImagMajorant, N1, N3, T, Q1] <;> ring
  constructor
  · simpa [Higham23RecursiveComplexErrorLe, higham23ThreeMExactRecursive,
      higham23ThreeM, higham23FlThreeMStrassen, As, Bs, P1, P2, P3,
      n, e, u] using hReal
  · simpa [Higham23RecursiveComplexErrorLe, higham23ThreeMExactRecursive,
      higham23ThreeM, higham23FlThreeMStrassen, As, Bs, P1, P2, P3, Q, Q1,
      n, e, u] using hImag

end NumStability
