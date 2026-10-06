/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace NumStability

/-!
# Fast matrix multiplication recurrences

Reusable recurrence specifications for the error coefficients of Strassen and
Winograd--Strassen multiplication. Source-numbered Chapter 23 consequences
live under `NumStability.Source.Higham.Chapter23`; the unsupported historical
bound placeholders remain internal to the FastMatMul family.
-/

/-- The error coefficient recurrence for recursive Strassen multiplication. -/
structure StrassenRecurrence (r : ℕ) (c : ℕ → ℝ) : Prop where
  /-- Base case: `c r = (2^r)² = 4^r`. -/
  base : c r = (4 : ℝ) ^ r
  /-- Recurrence above the crossover level. -/
  step : ∀ k, r < k → c k = 12 * c (k - 1) + 46 * (2 : ℝ) ^ (k - 1)

/-- A positive Strassen recurrence coefficient grows at the next level. -/
theorem strassen_recurrence_monotone (r : ℕ) (c : ℕ → ℝ)
    (hRec : StrassenRecurrence r c) (k : ℕ) (hk : r < k + 1)
    (hc_pos : 0 < c k) :
    c k < c (k + 1) := by
  have hstep := hRec.step (k + 1) hk
  simp only [show k + 1 - 1 = k from by omega] at hstep
  rw [hstep]
  have h46 : (0 : ℝ) < 46 * 2 ^ k := by positivity
  linarith

/-- The error coefficient recurrence for recursive Winograd--Strassen
multiplication. -/
structure WinogradStrassenRecurrence (r : ℕ) (c : ℕ → ℝ) : Prop where
  base : c r = (4 : ℝ) ^ r
  step : ∀ k, r < k → c k = 18 * c (k - 1) + 89 * (2 : ℝ) ^ (k - 1)

end NumStability
