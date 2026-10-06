/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Topology.Basic
import NumStability.Algorithms.DotProduct

namespace NumStability

open scoped BigOperators Topology
open Filter

/-!
# Higham Chapter 23: Gamma asymptotics

Exact first-order splitting and asymptotics of the standard gamma factors used in Higham, Chapter 23.
-/

section GammaAsymptotics

/-- The exact quadratic-and-higher remainder in `gamma_k`. -/
noncomputable def higham23GammaRemainder (k : ℕ) (u : ℝ) : ℝ :=
  (((k : ℝ) * u) ^ 2) / (1 - (k : ℝ) * u)

noncomputable def higham23GammaRemainderCoefficient (k : ℕ) (u : ℝ) : ℝ :=
  (k : ℝ) ^ 2 / (1 - (k : ℝ) * u)

theorem higham23_gamma_split (fp : FPModel) (k : ℕ)
    (hvalid : gammaValid fp k) :
    gamma fp k = (k : ℝ) * fp.u + higham23GammaRemainder k fp.u := by
  simpa [higham23GammaRemainder] using
    gamma_eq_linear_plus_quadratic_remainder fp k hvalid

theorem higham23_gammaRemainder_factor (k : ℕ) (u : ℝ) :
    higham23GammaRemainder k u =
      u ^ 2 * higham23GammaRemainderCoefficient k u := by
  unfold higham23GammaRemainder higham23GammaRemainderCoefficient
  ring

theorem higham23_gammaRemainderCoefficient_continuousAt_zero (k : ℕ) :
    ContinuousAt (higham23GammaRemainderCoefficient k) 0 := by
  unfold higham23GammaRemainderCoefficient
  exact continuousAt_const.div
    (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
    (by norm_num)

/-- The remainder in the source's first-order gamma expansion is genuinely
`O(u²)` as `u → 0`, with the operation count fixed. -/
theorem higham23_gammaRemainder_isBigO_u_sq (k : ℕ) :
    (fun u : ℝ ↦ higham23GammaRemainder k u) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) := by
  have huSq : (fun u : ℝ ↦ u ^ 2) =O[𝓝 0] (fun u : ℝ ↦ u ^ 2) :=
    Asymptotics.isBigO_refl _ _
  have hCoeff :
      (fun u : ℝ ↦ higham23GammaRemainderCoefficient k u) =O[𝓝 0]
        (fun _ : ℝ ↦ (1 : ℝ)) :=
    (higham23_gammaRemainderCoefficient_continuousAt_zero k).isBigO_one ℝ
  have hProduct := huSq.mul hCoeff
  simpa only [higham23_gammaRemainder_factor, mul_one] using hProduct

/-- Rewrite any exact-gamma error bound into its printed linear term plus the
explicit quadratic remainder. -/
theorem higham23_error_bound_gamma_split (fp : FPModel) (k : ℕ)
    (error budget : ℝ) (hvalid : gammaValid fp k)
    (h : error ≤ gamma fp k * budget) :
    error ≤ (k : ℝ) * fp.u * budget +
      higham23GammaRemainder k fp.u * budget := by
  rw [higham23_gamma_split fp k hvalid] at h
  nlinarith

end GammaAsymptotics

end NumStability
