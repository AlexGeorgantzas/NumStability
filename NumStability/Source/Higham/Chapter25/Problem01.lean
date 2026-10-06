/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.IterativeRefinement
import Mathlib.Analysis.SpecificLimits.Normed

namespace NumStability

open Filter

/-! # Higham Chapter 25, Problem 25.1

The printed problem and Appendix A solution analyze an inexact contraction
`x_{k+1} = G(x_k) + e_k` with `‖e_k‖ ≤ α` and contraction factor
`0 ≤ β < 1`.  The declarations below formalize the one-step estimate (A.15),
the invariant limiting ball, strict decrease outside that ball, a uniform
bound, and the stated bound on subsequential limits.
-/

section InexactContraction

variable {E : Type*} [NormedAddCommGroup E]

/-- Higham, 2nd ed., Appendix A, solution 25.1, equation (A.15), printed
page 569: one inexact contraction step obeys an affine norm recurrence. -/
theorem higham25_problem25_1_A15
    (G : E → E) (x e : ℕ → E) (a : E) (α β : ℝ)
    (hcontract : ∀ y, ‖G y - a‖ ≤ β * ‖y - a‖)
    (herror : ∀ k, ‖e k‖ ≤ α)
    (hstep : ∀ k, x (k + 1) = G (x k) + e k) :
    ∀ k, ‖x (k + 1) - a‖ ≤ β * ‖x k - a‖ + α := by
  intro k
  calc
    ‖x (k + 1) - a‖ = ‖(G (x k) - a) + e k‖ := by rw [hstep k]; congr 1; abel
    _ ≤ ‖G (x k) - a‖ + ‖e k‖ := norm_add_le _ _
    _ ≤ β * ‖x k - a‖ + α := add_le_add (hcontract (x k)) (herror k)

/-- The contraction hypothesis forces the center `a` to be a fixed point,
as noted immediately after equation (25.15). -/
theorem higham25_problem25_1_fixed_point
    (G : E → E) (a : E) (β : ℝ)
    (hcontract : ∀ y, ‖G y - a‖ ≤ β * ‖y - a‖) :
    G a = a := by
  have hzero : ‖G a - a‖ = 0 := by
    apply le_antisymm
    · simpa using hcontract a
    · exact norm_nonneg _
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-- Higham, 2nd ed., Problem 25.1(a), printed page 469: the ball of radius
`α/(1-β)` around the fixed point is invariant under every inexact step. -/
theorem higham25_problem25_1_invariant_ball
    (G : E → E) (x e : ℕ → E) (a : E) (α β : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hcontract : ∀ y, ‖G y - a‖ ≤ β * ‖y - a‖)
    (herror : ∀ k, ‖e k‖ ≤ α)
    (hstep : ∀ k, x (k + 1) = G (x k) + e k)
    {k : ℕ} (hk : ‖x k - a‖ ≤ α / (1 - β)) :
    ‖x (k + 1) - a‖ ≤ α / (1 - β) := by
  have hden : 0 < 1 - β := by linarith
  have hrec := higham25_problem25_1_A15 G x e a α β hcontract herror hstep k
  have hmul := mul_le_mul_of_nonneg_left hk hβ0
  calc
    ‖x (k + 1) - a‖ ≤ β * ‖x k - a‖ + α := hrec
    _ ≤ β * (α / (1 - β)) + α := by linarith
    _ = α / (1 - β) := by field_simp [ne_of_gt hden]; ring

/-- Higham, 2nd ed., Problem 25.1(a), printed page 469: outside the limiting
ball an inexact contraction step strictly decreases the distance to `a`. -/
theorem higham25_problem25_1_strict_decrease_outside
    (G : E → E) (x e : ℕ → E) (a : E) (α β : ℝ)
    (hβ1 : β < 1)
    (hcontract : ∀ y, ‖G y - a‖ ≤ β * ‖y - a‖)
    (herror : ∀ k, ‖e k‖ ≤ α)
    (hstep : ∀ k, x (k + 1) = G (x k) + e k)
    {k : ℕ} (hk : α / (1 - β) < ‖x k - a‖) :
    ‖x (k + 1) - a‖ < ‖x k - a‖ := by
  have hden : 0 < 1 - β := by linarith
  have hαlt : α < ‖x k - a‖ * (1 - β) :=
    (div_lt_iff₀ hden).mp (by simpa [div_eq_mul_inv] using hk)
  have hrec := higham25_problem25_1_A15 G x e a α β hcontract herror hstep k
  nlinarith

/-- A closed geometric envelope for Problem 25.1.  This reuses the repository's
proved affine-contraction theorem rather than duplicating it. -/
theorem higham25_problem25_1_geometric_envelope
    (G : E → E) (x e : ℕ → E) (a : E) (α β : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hα : 0 ≤ α)
    (hcontract : ∀ y, ‖G y - a‖ ≤ β * ‖y - a‖)
    (herror : ∀ k, ‖e k‖ ≤ α)
    (hstep : ∀ k, x (k + 1) = G (x k) + e k) :
    ∀ k, ‖x k - a‖ ≤ β ^ k * ‖x 0 - a‖ + α / (1 - β) := by
  apply linear_contraction (fun k => ‖x k - a‖) β α hβ0 hβ1 hα
  exact higham25_problem25_1_A15 G x e a α β hcontract herror hstep

/-- Higham, 2nd ed., Problem 25.1(b), printed page 469 and Appendix A printed
page 570: the full inexact-contraction sequence is uniformly bounded. -/
theorem higham25_problem25_1_bounded
    (G : E → E) (x e : ℕ → E) (a : E) (α β : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hα : 0 ≤ α)
    (hcontract : ∀ y, ‖G y - a‖ ≤ β * ‖y - a‖)
    (herror : ∀ k, ‖e k‖ ≤ α)
    (hstep : ∀ k, x (k + 1) = G (x k) + e k) :
    ∀ k, ‖x k‖ ≤ ‖x 0 - a‖ + α / (1 - β) + ‖a‖ := by
  have hsteady : ∀ k, ‖x k - a‖ ≤ ‖x 0 - a‖ + α / (1 - β) :=
    linear_contraction_steady_state (fun k => ‖x k - a‖) β α
      hβ0 hβ1 hα
      (higham25_problem25_1_A15 G x e a α β hcontract herror hstep)
      (norm_nonneg _)
  intro k
  calc
    ‖x k‖ = ‖(x k - a) + a‖ := by congr 1; abel
    _ ≤ ‖x k - a‖ + ‖a‖ := norm_add_le _ _
    _ ≤ ‖x 0 - a‖ + α / (1 - β) + ‖a‖ :=
      add_le_add (hsteady k) (le_refl _)

/-- Higham, 2nd ed., Problem 25.1(b), printed page 469: every subsequential
limit lies in the closed ball of radius `α/(1-β)` around `a`.  A point of
accumulation is represented explicitly by a cofinal convergent subsequence. -/
theorem higham25_problem25_1_subsequential_limit
    (G : E → E) (x e : ℕ → E) (a z : E) (α β : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hα : 0 ≤ α)
    (hcontract : ∀ y, ‖G y - a‖ ≤ β * ‖y - a‖)
    (herror : ∀ k, ‖e k‖ ≤ α)
    (hstep : ∀ k, x (k + 1) = G (x k) + e k)
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
    (hz : Tendsto (fun k => x (φ k)) atTop (nhds z)) :
    ‖z - a‖ ≤ α / (1 - β) := by
  have hleft : Tendsto (fun k => ‖x (φ k) - a‖) atTop (nhds ‖z - a‖) :=
    (hz.sub tendsto_const_nhds).norm
  have hpow : Tendsto (fun k => β ^ φ k) atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).comp hφ
  have hright :
      Tendsto (fun k => β ^ φ k * ‖x 0 - a‖ + α / (1 - β)) atTop
        (nhds (α / (1 - β))) := by
    simpa using (hpow.mul_const ‖x 0 - a‖).add_const (α / (1 - β))
  exact le_of_tendsto_of_tendsto' hleft hright fun k =>
    higham25_problem25_1_geometric_envelope G x e a α β hβ0 hβ1 hα
      hcontract herror hstep (φ k)

end InexactContraction

end NumStability
