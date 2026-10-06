/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter23.ErrorRecurrences
import NumStability.Source.Higham.Chapter23.Theorem02.ErrorBound
import NumStability.Source.Higham.Chapter23.Theorem02.ExactMajorant
import NumStability.Source.Higham.Chapter23.ThreeMStrassen.ExactMajorant
import NumStability.Source.Higham.Chapter23.ThreeMStrassen.Execution

namespace NumStability

open scoped Topology
open Filter

/-!
# Higham Chapter 23: combined 3M--Strassen first-order bound

First-order real and imaginary coefficients, quadratic remainders, and the final source coefficient.
-/

/-! ### First-order split -/

noncomputable def higham23ThreeMStrassenRealFamily (r depth : ℕ) (u : ℝ) : ℝ :=
  higham23ThreeMStrassenRealMajorant (((2 ^ (r + depth) : ℕ) : ℝ))
    (higham23StrassenMajorantFamily r depth u) u

noncomputable def higham23ThreeMStrassenImagFamily (r depth : ℕ) (u : ℝ) : ℝ :=
  higham23ThreeMStrassenImagMajorant (((2 ^ (r + depth) : ℕ) : ℝ))
    (higham23StrassenMajorantFamily r depth u) u

noncomputable def higham23ThreeMStrassenRealFirstOrder (r depth : ℕ) : ℝ :=
  2 * higham23StrassenErrorCoefficient r depth +
    2 * (((2 ^ (r + depth) : ℕ) : ℝ))

noncomputable def higham23ThreeMStrassenImagFirstOrder (r depth : ℕ) : ℝ :=
  4 * higham23StrassenErrorCoefficient r depth +
    11 * (((2 ^ (r + depth) : ℕ) : ℝ))

noncomputable def higham23ThreeMStrassenRealRemainder
    (r depth : ℕ) (u : ℝ) : ℝ :=
  higham23ThreeMStrassenRealFamily r depth u -
    higham23ThreeMStrassenRealFirstOrder r depth * u

noncomputable def higham23ThreeMStrassenImagRemainder
    (r depth : ℕ) (u : ℝ) : ℝ :=
  higham23ThreeMStrassenImagFamily r depth u -
    higham23ThreeMStrassenImagFirstOrder r depth * u

theorem higham23_threeMStrassenMajorants_eq_families
    (fp : FPModel) (r depth : ℕ) (hvalid : gammaValid fp (2 ^ r)) :
    higham23ThreeMStrassenRealMajorant (((2 ^ (r + depth) : ℕ) : ℝ))
        (higham23StrassenExactMajorant fp r depth) fp.u =
      higham23ThreeMStrassenRealFamily r depth fp.u ∧
    higham23ThreeMStrassenImagMajorant (((2 ^ (r + depth) : ℕ) : ℝ))
        (higham23StrassenExactMajorant fp r depth) fp.u =
      higham23ThreeMStrassenImagFamily r depth fp.u := by
  rw [higham23_strassenExactMajorant_eq_family fp r depth hvalid]
  exact ⟨rfl, rfl⟩

theorem higham23_threeMStrassenRemainders_isBigO_u_sq (r depth : ℕ) :
    (fun u : ℝ ↦ higham23ThreeMStrassenRealRemainder r depth u)
        =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) ∧
      (fun u : ℝ ↦ higham23ThreeMStrassenImagRemainder r depth u)
        =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
  let n : ℝ := (((2 ^ (r + depth) : ℕ) : ℝ))
  let c := higham23StrassenErrorCoefficient r depth
  let e : ℝ → ℝ := higham23StrassenMajorantFamily r depth
  let F : ℝ → ℝ := fun u ↦
    higham23ThreeMStrassenP3Norm n (e u) u +
      higham23ThreeMStrassenP1Norm n (e u)
  let G : ℝ → ℝ := fun u ↦
    (1 + u) * F u + higham23ThreeMStrassenP1Norm n (e u)
  have hu : (fun u : ℝ ↦ u) =O[𝓝 0] (fun u : ℝ ↦ u) :=
    Asymptotics.isBigO_refl _ _
  have huOne : (fun u : ℝ ↦ u) =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    continuousAt_id.isBigO_one ℝ
  have huSq : (fun u : ℝ ↦ u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) :=
    Asymptotics.isBigO_refl _ _
  have huSqOu : (fun u : ℝ ↦ u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u) := by
    simpa only [pow_two, mul_one] using hu.mul huOne
  have heR : (fun u : ℝ ↦ e u - c * u)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    simpa [e, c, higham23StrassenMajorantRemainder] using
      higham23_strassenMajorantRemainder_isBigO_u_sq r depth
  have he : e =O[𝓝 0] (fun u : ℝ ↦ u) := by
    have hsum := (hu.const_mul_left c).add (heR.trans huSqOu)
    apply hsum.congr'
    · exact Filter.Eventually.of_forall fun u ↦ by
        dsimp [e, c, higham23StrassenMajorantRemainder]
        ring
    · exact Filter.EventuallyEq.rfl
  have heOne := he.trans huOne
  have hue : (fun u : ℝ ↦ u * e u) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    simpa only [pow_two] using hu.mul he
  have huSqe : (fun u : ℝ ↦ u ^ 2 * e u)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    simpa only [mul_one] using huSq.mul heOne
  have hRealRaw := (heR.const_mul_left 2).add (hue.const_mul_left 2)
  have hReal : (fun u : ℝ ↦ higham23ThreeMStrassenRealRemainder r depth u)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    apply hRealRaw.congr'
    · exact Filter.Eventually.of_forall fun u ↦ by
        dsimp [higham23ThreeMStrassenRealRemainder,
          higham23ThreeMStrassenRealFamily,
          higham23ThreeMStrassenRealFirstOrder,
          higham23ThreeMStrassenRealMajorant,
          higham23ThreeMStrassenP1Norm, n, c, e]
        ring
    · exact Filter.EventuallyEq.rfl
  have hTresRaw :=
    (((huSq.const_mul_left n).add heR).add
      (hue.const_mul_left 2)).add huSqe
  have hTres : (fun u : ℝ ↦
      higham23ThreeMStrassenP3Error n (e u) u - (2 * c + 4 * n) * u)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    have h := hTresRaw.const_mul_left 2
    apply h.congr'
    · exact Filter.Eventually.of_forall fun u ↦ by
        dsimp [higham23ThreeMStrassenP3Error]
        ring
    · exact Filter.EventuallyEq.rfl
  have hFminus : (fun u : ℝ ↦ F u - 3 * n)
      =O[𝓝 0] (fun u : ℝ ↦ u) := by
    have heuOu := hue.trans huSqOu
    have huSqeOu := huSqe.trans huSqOu
    have hsum :=
      (((he.const_mul_left 3).add (hu.const_mul_left (4 * n))).add
        (heuOu.const_mul_left 4)).add
        ((huSqOu.const_mul_left (2 * n)).add (huSqeOu.const_mul_left 2))
    apply hsum.congr'
    · exact Filter.Eventually.of_forall fun u ↦ by
        dsimp [F, higham23ThreeMStrassenP3Norm,
          higham23ThreeMStrassenP1Norm]
        ring
    · exact Filter.EventuallyEq.rfl
  have hConst : (fun _ : ℝ ↦ 3 * n) =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    continuousAt_const.isBigO_one ℝ
  have hFOne : F =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) := by
    have hsum := (hFminus.trans huOne).add hConst
    apply hsum.congr'
    · exact Filter.Eventually.of_forall fun u ↦ by ring
    · exact Filter.EventuallyEq.rfl
  have huF : (fun u : ℝ ↦ u * F u) =O[𝓝 0] (fun u : ℝ ↦ u) := by
    simpa only [mul_one] using hu.mul hFOne
  have hGminus : (fun u : ℝ ↦ G u - 4 * n)
      =O[𝓝 0] (fun u : ℝ ↦ u) := by
    have hsum := (hFminus.add huF).add he
    apply hsum.congr'
    · exact Filter.Eventually.of_forall fun u ↦ by
        dsimp [G, F, higham23ThreeMStrassenP1Norm]
        ring
    · exact Filter.EventuallyEq.rfl
  have huFminus : (fun u : ℝ ↦ u * (F u - 3 * n))
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    simpa only [pow_two] using hu.mul hFminus
  have huGminus : (fun u : ℝ ↦ u * (G u - 4 * n))
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    simpa only [pow_two] using hu.mul hGminus
  have hImagRaw := (((hTres.add (heR.const_mul_left 2)).add huFminus).add huGminus)
  have hImag : (fun u : ℝ ↦ higham23ThreeMStrassenImagRemainder r depth u)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    apply hImagRaw.congr'
    · exact Filter.Eventually.of_forall fun u ↦ by
        dsimp [higham23ThreeMStrassenImagRemainder,
          higham23ThreeMStrassenImagFamily,
          higham23ThreeMStrassenImagFirstOrder,
          higham23ThreeMStrassenImagMajorant, F, G, n, c, e]
        ring
    · exact Filter.EventuallyEq.rfl
  exact ⟨hReal, hImag⟩

/-- First-order form for the actual combined evaluator. -/
theorem higham23_threeMStrassen_firstOrder
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
    Higham23RecursiveComplexErrorLe r depth
      (higham23ThreeMExactRecursive r depth A B)
      (higham23FlThreeMStrassen fp r depth A B)
      ((higham23ThreeMStrassenRealFirstOrder r depth * fp.u +
          higham23ThreeMStrassenRealRemainder r depth fp.u) * a * b)
      ((higham23ThreeMStrassenImagFirstOrder r depth * fp.u +
          higham23ThreeMStrassenImagRemainder r depth fp.u) * a * b) := by
  have hExact := higham23_threeMStrassen_exactMajorant fp r depth hvalid
    A B a b sA sB ha hb hsA hsB hA1 hA2 hB1 hB2 hAsum hBsum hSumProduct
  rcases hExact with ⟨hReal, hImag⟩
  have hFamilies := higham23_threeMStrassenMajorants_eq_families fp r depth hvalid
  rw [hFamilies.1] at hReal
  rw [hFamilies.2] at hImag
  have hRealSplit : higham23ThreeMStrassenRealFamily r depth fp.u =
      higham23ThreeMStrassenRealFirstOrder r depth * fp.u +
        higham23ThreeMStrassenRealRemainder r depth fp.u := by
    unfold higham23ThreeMStrassenRealRemainder
    ring
  have hImagSplit : higham23ThreeMStrassenImagFamily r depth fp.u =
      higham23ThreeMStrassenImagFirstOrder r depth * fp.u +
        higham23ThreeMStrassenImagRemainder r depth fp.u := by
    unfold higham23ThreeMStrassenImagRemainder
    ring
  exact ⟨by simpa [hRealSplit] using hReal, by simpa [hImagSplit] using hImag⟩

theorem higham23_strassenErrorCoefficient_ge_order_sq (r : ℕ) :
    ∀ depth, ((2 : ℝ) ^ (r + depth)) ^ 2 ≤
      higham23StrassenErrorCoefficient r depth
  | 0 => by
      simp [higham23StrassenErrorCoefficient, pow_two, ← mul_pow]
      norm_num
  | depth + 1 => by
      rw [higham23_eq23_16_strassen_coefficient]
      have ih := higham23_strassenErrorCoefficient_ge_order_sq r depth
      have hx : 0 ≤ (2 : ℝ) ^ (r + depth) := by positivity
      have hc := higham23_strassenErrorCoefficient_nonneg r depth
      calc
        ((2 : ℝ) ^ (r + (depth + 1))) ^ 2 =
            4 * ((2 : ℝ) ^ (r + depth)) ^ 2 := by
          rw [show r + (depth + 1) = (r + depth) + 1 by omega, pow_succ]
          ring
        _ ≤ 12 * higham23StrassenErrorCoefficient r depth +
            46 * (2 : ℝ) ^ (r + depth) := by nlinarith

theorem higham23_strassenClosedCoefficient_ge_order_sq (r depth : ℕ) :
    ((2 : ℝ) ^ (r + depth)) ^ 2 ≤ higham23StrassenClosedCoefficient r depth := by
  exact (higham23_strassenErrorCoefficient_ge_order_sq r depth).trans
    (by simpa [higham23StrassenClosedCoefficient] using
      higham23_strassenErrorCoefficient_le r depth)

theorem higham23_threeMStrassenRealFirstOrder_le_source (r depth : ℕ) :
    higham23ThreeMStrassenRealFirstOrder r depth ≤
      higham23ThreeMStrassenCoefficient r depth := by
  let n : ℝ := (2 : ℝ) ^ (r + depth)
  let c := higham23StrassenErrorCoefficient r depth
  let C := higham23StrassenClosedCoefficient r depth
  have hn : 1 ≤ n := by
    dsimp [n]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hn2 : n ≤ n ^ 2 := by nlinarith
  have hC2 : n ^ 2 ≤ C := by
    simpa [n] using higham23_strassenClosedCoefficient_ge_order_sq r depth
  have hcC : c ≤ C := by
    simpa [c, C, higham23StrassenClosedCoefficient] using
      higham23_strassenErrorCoefficient_le r depth
  have hC0 := higham23_strassenClosedCoefficient_nonneg r depth
  dsimp [higham23ThreeMStrassenRealFirstOrder,
    higham23ThreeMStrassenCoefficient, n, c, C]
  norm_num [Nat.cast_pow]
  nlinarith

theorem higham23_threeMStrassenImagFirstOrder_le_source (r depth : ℕ) :
    higham23ThreeMStrassenImagFirstOrder r depth ≤
      higham23ThreeMStrassenCoefficient r depth := by
  let n : ℝ := (2 : ℝ) ^ (r + depth)
  let c := higham23StrassenErrorCoefficient r depth
  let C := higham23StrassenClosedCoefficient r depth
  have hC2 : n ^ 2 ≤ C := by
    simpa [n] using higham23_strassenClosedCoefficient_ge_order_sq r depth
  have hcC : c ≤ C := by
    simpa [c, C, higham23StrassenClosedCoefficient] using
      higham23_strassenErrorCoefficient_le r depth
  have hquad : 11 * n ≤ 2 * n ^ 2 + 24 := by
    nlinarith [sq_nonneg (4 * n - 11)]
  dsimp [higham23ThreeMStrassenImagFirstOrder,
    higham23ThreeMStrassenCoefficient, n, c, C]
  norm_num [Nat.cast_pow]
  nlinarith

/-- The source's combined 3M--Strassen statement: the same (23.14)
coefficient with multiplier six and four added, for the literal evaluator. -/
theorem higham23_threeMStrassen_sourceCoefficient
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
    Higham23RecursiveComplexErrorLe r depth
      (higham23ThreeMExactRecursive r depth A B)
      (higham23FlThreeMStrassen fp r depth A B)
      ((higham23ThreeMStrassenCoefficient r depth * fp.u +
          higham23ThreeMStrassenRealRemainder r depth fp.u) * a * b)
      ((higham23ThreeMStrassenCoefficient r depth * fp.u +
          higham23ThreeMStrassenImagRemainder r depth fp.u) * a * b) := by
  rcases higham23_threeMStrassen_firstOrder fp r depth hvalid
    A B a b sA sB ha hb hsA hsB hA1 hA2 hB1 hB2 hAsum hBsum hSumProduct with
    ⟨hReal, hImag⟩
  constructor
  · apply higham23_recursiveErrorLe_mono r depth _ _ hReal
    have hc := higham23_threeMStrassenRealFirstOrder_le_source r depth
    have hs := mul_le_mul_of_nonneg_right hc fp.u_nonneg
    have hab : 0 ≤ a * b := mul_nonneg ha hb
    calc
      _ = (higham23ThreeMStrassenRealFirstOrder r depth * fp.u +
          higham23ThreeMStrassenRealRemainder r depth fp.u) * (a * b) := by ring
      _ ≤ (higham23ThreeMStrassenCoefficient r depth * fp.u +
          higham23ThreeMStrassenRealRemainder r depth fp.u) * (a * b) :=
        mul_le_mul_of_nonneg_right (add_le_add hs le_rfl) hab
      _ = _ := by ring
  · apply higham23_recursiveErrorLe_mono r depth _ _ hImag
    have hc := higham23_threeMStrassenImagFirstOrder_le_source r depth
    have hs := mul_le_mul_of_nonneg_right hc fp.u_nonneg
    have hab : 0 ≤ a * b := mul_nonneg ha hb
    calc
      _ = (higham23ThreeMStrassenImagFirstOrder r depth * fp.u +
          higham23ThreeMStrassenImagRemainder r depth fp.u) * (a * b) := by ring
      _ ≤ (higham23ThreeMStrassenCoefficient r depth * fp.u +
          higham23ThreeMStrassenImagRemainder r depth fp.u) * (a * b) :=
        mul_le_mul_of_nonneg_right (add_le_add hs le_rfl) hab
      _ = _ := by ring

end NumStability
