/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter23.ErrorRecurrences
import NumStability.Source.Higham.Chapter23.GammaAsymptotics
import NumStability.Source.Higham.Chapter23.Theorem03.Certificates
import NumStability.Source.Higham.Chapter23.Theorem03.ExactMajorant
import NumStability.Source.Higham.Chapter23.Theorem03.Execution

namespace NumStability

open scoped BigOperators Topology
open Filter

/-!
# Higham Chapter 23, Theorem 23.3: Winograd-Strassen error bound

This module linearizes the exact recursive majorant, proves its quadratic
remainder estimate, and derives the closed first-order coefficient stated in
Theorem 23.3 and equation (23.18).
-/

/-! ## The 18/89 linearization in (23.18) -/

noncomputable def higham23WinogradStepResidual (m e u : ℝ) : ℝ :=
  higham23WinogradStepMajorant m e u - (89 * m * u + 18 * e)

private noncomputable def higham23WinogradStepMQuadratic (u : ℝ) : ℝ :=
  197 + 256 * u + 211 * u ^ 2 + 109 * u ^ 3 + 32 * u ^ 4 + 4 * u ^ 5

private noncomputable def higham23WinogradStepEQuadratic (u : ℝ) : ℝ :=
  89 + 197 * u + 256 * u ^ 2 + 211 * u ^ 3 + 109 * u ^ 4 +
    32 * u ^ 5 + 4 * u ^ 6

theorem higham23_winogradStepResidual_factor (m e u : ℝ) :
    higham23WinogradStepResidual m e u =
      m * u ^ 2 * higham23WinogradStepMQuadratic u +
        e * u * higham23WinogradStepEQuadratic u := by
  unfold higham23WinogradStepResidual higham23WinogradStepMajorant
    higham23WinogradQError higham23WinogradQNorm
    higham23WinogradT1Error higham23WinogradT1Norm
    higham23WinogradP1Error higham23WinogradP1Norm
    higham23WinogradP4Error higham23WinogradP4Norm
    higham23WinogradP6Error higham23WinogradP6Norm
    higham23WinogradProductError higham23WinogradProductNorm
    higham23WinogradN1 higham23WinogradE1
    higham23WinogradN2 higham23WinogradE2
    higham23WinogradN4 higham23WinogradE4
    higham23WinogradStepMQuadratic higham23WinogradStepEQuadratic
  simp only [higham23WinogradN1, higham23WinogradE1,
    higham23WinogradN2, higham23WinogradE2,
    higham23WinogradN4, higham23WinogradE4]
  ring

private theorem higham23_winogradStepMQuadratic_continuousAt :
    ContinuousAt higham23WinogradStepMQuadratic 0 := by
  unfold higham23WinogradStepMQuadratic
  fun_prop

private theorem higham23_winogradStepEQuadratic_continuousAt :
    ContinuousAt higham23WinogradStepEQuadratic 0 := by
  unfold higham23WinogradStepEQuadratic
  fun_prop

theorem higham23_winogradStepResidual_isBigO_u_sq
    (m : ℝ) (e : ℝ → ℝ)
    (he : e =O[𝓝 0] (fun u : ℝ ↦ u)) :
    (fun u : ℝ ↦ higham23WinogradStepResidual m (e u) u)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
  have huSq : (fun u : ℝ ↦ u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) :=
    Asymptotics.isBigO_refl _ _
  have hMCoeff :
      (fun u : ℝ ↦ m * higham23WinogradStepMQuadratic u)
        =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    (continuousAt_const.mul higham23_winogradStepMQuadratic_continuousAt).isBigO_one ℝ
  have hMTerm :
      (fun u : ℝ ↦ m * u ^ 2 * higham23WinogradStepMQuadratic u)
        =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    have h := huSq.mul hMCoeff
    simpa only [mul_one, mul_assoc, mul_comm, mul_left_comm] using h
  have hu : (fun u : ℝ ↦ u) =O[𝓝 0] (fun u : ℝ ↦ u) :=
    Asymptotics.isBigO_refl _ _
  have hECoeff :
      (fun u : ℝ ↦ higham23WinogradStepEQuadratic u)
        =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    higham23_winogradStepEQuadratic_continuousAt.isBigO_one ℝ
  have hETerm :
      (fun u : ℝ ↦ e u * u * higham23WinogradStepEQuadratic u)
        =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
    have h := (he.mul hu).mul hECoeff
    simpa only [pow_two, mul_one, mul_assoc] using h
  have h := hMTerm.add hETerm
  apply h.congr'
  · exact Filter.Eventually.of_forall fun u ↦ by
      exact (higham23_winogradStepResidual_factor m (e u) u).symm
  · exact Filter.EventuallyEq.rfl

noncomputable def higham23WinogradMajorantFamily (r : ℕ) : ℕ → ℝ → ℝ
  | 0, u =>
      (4 : ℝ) ^ r * u +
        ((2 ^ r : ℕ) : ℝ) * higham23GammaRemainder (2 ^ r) u
  | depth + 1, u =>
      higham23WinogradStepMajorant ((2 ^ (r + depth) : ℕ) : ℝ)
        (higham23WinogradMajorantFamily r depth u) u

noncomputable def higham23WinogradMajorantRemainder
    (r depth : ℕ) (u : ℝ) : ℝ :=
  higham23WinogradMajorantFamily r depth u -
    higham23WinogradStrassenErrorCoefficient r depth * u

theorem higham23_winogradExactMajorant_eq_family
    (fp : FPModel) (r depth : ℕ) (hvalid : gammaValid fp (2 ^ r)) :
    higham23WinogradExactMajorant fp r depth =
      higham23WinogradMajorantFamily r depth fp.u := by
  induction depth with
  | zero =>
      rw [higham23WinogradExactMajorant, higham23WinogradMajorantFamily,
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
      rw [higham23WinogradExactMajorant, higham23WinogradMajorantFamily, ih]

theorem higham23_winogradMajorantRemainder_isBigO_u_sq (r depth : ℕ) :
    (fun u : ℝ ↦ higham23WinogradMajorantRemainder r depth u)
      =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
  induction depth with
  | zero =>
      have h := (higham23_gammaRemainder_isBigO_u_sq (2 ^ r)).const_mul_left
        (((2 ^ r : ℕ) : ℝ))
      simpa only [higham23WinogradMajorantRemainder,
        higham23WinogradMajorantFamily,
        higham23_winogradStrassenErrorCoefficient_zero,
        add_sub_cancel_left] using h
  | succ depth ih =>
      let e : ℝ → ℝ := higham23WinogradMajorantFamily r depth
      let c := higham23WinogradStrassenErrorCoefficient r depth
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
            dsimp [e, c, higham23WinogradMajorantRemainder]
            ring
        · exact Filter.EventuallyEq.rfl
      have hStep := higham23_winogradStepResidual_isBigO_u_sq m e he
      have hPrevious := ih.const_mul_left (18 : ℝ)
      have h := hStep.add hPrevious
      apply h.congr'
      · exact Filter.Eventually.of_forall fun u ↦ by
          dsimp [higham23WinogradMajorantRemainder,
            higham23WinogradMajorantFamily, e, c, m]
          rw [higham23_winogradStrassenErrorCoefficient_step]
          unfold higham23WinogradStepResidual
          norm_num [Nat.cast_pow, pow_add]
          ring
      · exact Filter.EventuallyEq.rfl

theorem higham23_theorem23_3_winograd_firstOrder
    (fp : FPModel) (r depth : ℕ) (hvalid : gammaValid fp (2 ^ r))
    (A B : Higham23RecursiveMatrix r depth) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : Higham23RecursiveMaxNormLe r depth A a)
    (hB : Higham23RecursiveMaxNormLe r depth B b) :
    Higham23RecursiveErrorLe r depth (A * B)
      (higham23FlWinogradStrassenRecursive fp r depth A B)
      ((higham23WinogradStrassenErrorCoefficient r depth * fp.u +
          higham23WinogradMajorantRemainder r depth fp.u) * a * b) := by
  have h := higham23_theorem23_3_winograd_exactMajorant fp r hvalid
    depth A B a b ha hb hA hB
  rw [higham23_winogradExactMajorant_eq_family fp r depth hvalid] at h
  have hsplit : higham23WinogradMajorantFamily r depth fp.u =
      higham23WinogradStrassenErrorCoefficient r depth * fp.u +
        higham23WinogradMajorantRemainder r depth fp.u := by
    unfold higham23WinogradMajorantRemainder
    ring
  rwa [hsplit] at h

/-- Theorem 23.3 in the closed form printed in (23.18). -/
theorem higham23_theorem23_3_winograd_closedCoefficient_firstOrder
    (fp : FPModel) (r depth : ℕ) (hvalid : gammaValid fp (2 ^ r))
    (A B : Higham23RecursiveMatrix r depth) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : Higham23RecursiveMaxNormLe r depth A a)
    (hB : Higham23RecursiveMaxNormLe r depth B b) :
    Higham23RecursiveErrorLe r depth (A * B)
      (higham23FlWinogradStrassenRecursive fp r depth A B)
      ((higham23WinogradStrassenClosedCoefficient r depth * fp.u +
          higham23WinogradMajorantRemainder r depth fp.u) * a * b) := by
  have h := higham23_theorem23_3_winograd_firstOrder fp r depth hvalid
    A B a b ha hb hA hB
  apply higham23_recursiveErrorLe_mono r depth _ _ h
  have hc := higham23_winogradStrassenErrorCoefficient_le r depth
  have hs : 0 ≤ fp.u * a * b :=
    mul_nonneg (mul_nonneg fp.u_nonneg ha) hb
  have hm := mul_le_mul_of_nonneg_right hc hs
  dsimp [higham23WinogradStrassenClosedCoefficient] at hm ⊢
  nlinarith

end NumStability
