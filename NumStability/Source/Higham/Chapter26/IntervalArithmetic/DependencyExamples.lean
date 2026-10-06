/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter26.IntervalArithmetic.ExactOperations
import Mathlib.Tactic

namespace NumStability

/-! # Higham Chapter 26: Interval-Dependency Examples

The subtraction and division dependency examples from Section 26.4.
-/

namespace RealInterval

/-- Reusing the same uncertain interval twice can widen a subtraction: for
`[1,2]`, the interval result is exactly `[-1,1]`, as in Section 26.4. -/
theorem dependency_sub_example :
    let x : RealInterval := ⟨1, 2, by norm_num⟩
    (x.sub x).lower = -1 ∧ (x.sub x).upper = 1 := by
  change (1 - 2 : ℝ) = -1 ∧ (2 - 1 : ℝ) = 1
  norm_num

/-- Reusing the same uncertain interval twice also widens division: for
`[1,2]`, the interval result is exactly `[1/2,2]`, rather than the point
interval `[1,1]`, as stated in Section 26.4. -/
theorem dependency_div_example :
    let x : RealInterval := ⟨1, 2, by norm_num⟩
    let hzero : ¬ x.Contains 0 := by
      norm_num [Contains]
    (x.div x hzero).lower = 1 / 2 ∧
      (x.div x hzero).upper = 2 := by
  norm_num [div, mul, reciprocal]
  change
    min (min ((1 : ℝ) / 2) 1) (2 * min ((1 : ℝ) / 2) 1) = (1 : ℝ) / 2 ∧
      max ((1 : ℝ) / 2) 1 = 1
  norm_num [min_def, max_def]
  intro hbad
  exact (not_lt_of_ge (by norm_num : (1 / 2 : ℝ) ≤ 1) hbad).elim

end RealInterval


end NumStability
