/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace NumStability

/-! # Higham Chapter 26: Exact Interval Operations

Closed real intervals, exact endpoint operations, and containment theorems from Section 26.4.
-/

/-! ## Exact interval arithmetic from Section 26.4 -/

/-- A nonempty closed real interval, represented by ordered endpoints. -/
structure RealInterval where
  lower : ℝ
  upper : ℝ
  ordered : lower ≤ upper

namespace RealInterval

/-- Membership in a closed real interval. -/
def Contains (x : RealInterval) (a : ℝ) : Prop :=
  x.lower ≤ a ∧ a ≤ x.upper

/-- Higham, 2nd ed., Section 26.4, p. 481: interval width. -/
def width (x : RealInterval) : ℝ :=
  x.upper - x.lower

theorem width_nonneg (x : RealInterval) : 0 ≤ x.width := by
  exact sub_nonneg.mpr x.ordered

/-- Exact endpoint formula for interval addition. -/
def add (x y : RealInterval) : RealInterval where
  lower := x.lower + y.lower
  upper := x.upper + y.upper
  ordered := add_le_add x.ordered y.ordered

/-- Exact endpoint formula for interval subtraction. -/
def sub (x y : RealInterval) : RealInterval where
  lower := x.lower - y.upper
  upper := x.upper - y.lower
  ordered := sub_le_sub x.ordered y.ordered

/-- Exact endpoint formula for interval multiplication. -/
def mul (x y : RealInterval) : RealInterval where
  lower := min (min (x.lower * y.lower) (x.lower * y.upper))
    (min (x.upper * y.lower) (x.upper * y.upper))
  upper := max (max (x.lower * y.lower) (x.lower * y.upper))
    (max (x.upper * y.lower) (x.upper * y.upper))
  ordered := by
    exact le_trans (min_le_left _ _)
      (le_trans (min_le_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))

/-- Reciprocal endpoint hull.  Under the source side condition that zero is
not in the interval, this is the printed interval `[1/upper, 1/lower]`. -/
noncomputable def reciprocal (x : RealInterval) : RealInterval where
  lower := min (1 / x.upper) (1 / x.lower)
  upper := max (1 / x.upper) (1 / x.lower)
  ordered := min_le_max

/-- Exact interval-division construction from Section 26.4.  The explicit
side condition rules out the source's division-by-zero breakdown. -/
noncomputable def div (x y : RealInterval) (_hzero : ¬ y.Contains 0) : RealInterval :=
  x.mul y.reciprocal

/-- Addition soundness for the set interpretation of intervals. -/
theorem add_contains {x y : RealInterval} {a b : ℝ}
    (ha : x.Contains a) (hb : y.Contains b) :
    (x.add y).Contains (a + b) := by
  exact ⟨add_le_add ha.1 hb.1, add_le_add ha.2 hb.2⟩

/-- Subtraction soundness for the set interpretation of intervals. -/
theorem sub_contains {x y : RealInterval} {a b : ℝ}
    (ha : x.Contains a) (hb : y.Contains b) :
    (x.sub y).Contains (a - b) := by
  exact ⟨sub_le_sub ha.1 hb.2, sub_le_sub ha.2 hb.1⟩

/-- Multiplication by a fixed real sends an interval to the hull of its two
endpoint products. -/
private theorem fixed_mul_endpoint_bounds (k : ℝ) {y : RealInterval} {b : ℝ}
    (hb : y.Contains b) :
    min (k * y.lower) (k * y.upper) ≤ k * b ∧
      k * b ≤ max (k * y.lower) (k * y.upper) := by
  by_cases hk : 0 ≤ k
  · exact
      ⟨le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hb.1 hk),
        le_trans (mul_le_mul_of_nonneg_left hb.2 hk) (le_max_right _ _)⟩
  · have hk' : k ≤ 0 := le_of_not_ge hk
    exact
      ⟨le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hb.2 hk'),
        le_trans (mul_le_mul_of_nonpos_left hb.1 hk') (le_max_left _ _)⟩

/-- Multiplication soundness for the set interpretation of the four-corner
endpoint formula in Section 26.4. -/
theorem mul_contains {x y : RealInterval} {a b : ℝ}
    (ha : x.Contains a) (hb : y.Contains b) :
    (x.mul y).Contains (a * b) := by
  have hLower := fixed_mul_endpoint_bounds x.lower hb
  have hUpper := fixed_mul_endpoint_bounds x.upper hb
  by_cases hb0 : 0 ≤ b
  · constructor
    · exact le_trans (min_le_left _ _)
        (le_trans hLower.1 (mul_le_mul_of_nonneg_right ha.1 hb0))
    · exact le_trans (mul_le_mul_of_nonneg_right ha.2 hb0)
        (le_trans hUpper.2 (le_max_right _ _))
  · have hb0' : b ≤ 0 := le_of_not_ge hb0
    constructor
    · exact le_trans (min_le_right _ _)
        (le_trans hUpper.1 (mul_le_mul_of_nonpos_right ha.2 hb0'))
    · exact le_trans (mul_le_mul_of_nonpos_right ha.1 hb0')
        (le_trans hLower.2 (le_max_left _ _))

/-- Reciprocal soundness under the source side condition that zero is not in
the denominator interval. -/
theorem reciprocal_contains {x : RealInterval} {a : ℝ}
    (hzero : ¬ x.Contains 0) (ha : x.Contains a) :
    x.reciprocal.Contains (1 / a) := by
  have hside : x.upper < 0 ∨ 0 < x.lower := by
    by_contra h
    push_neg at h
    exact hzero ⟨h.2, h.1⟩
  rcases hside with hneg | hpos
  · have haNeg : a < 0 := lt_of_le_of_lt ha.2 hneg
    constructor
    · exact le_trans (min_le_left _ _)
        (one_div_le_one_div_of_neg_of_le hneg ha.2)
    · exact le_trans (one_div_le_one_div_of_neg_of_le haNeg ha.1)
        (le_max_right _ _)
  · have haPos : 0 < a := lt_of_lt_of_le hpos ha.1
    constructor
    · exact le_trans (min_le_left _ _)
        (one_div_le_one_div_of_le haPos ha.2)
    · exact le_trans (one_div_le_one_div_of_le hpos ha.1)
        (le_max_right _ _)

/-- Division soundness follows from multiplication and reciprocal soundness. -/
theorem div_contains {x y : RealInterval} {a b : ℝ}
    (hzero : ¬ y.Contains 0) (ha : x.Contains a) (hb : y.Contains b) :
    (x.div y hzero).Contains (a / b) := by
  simpa [div_eq_mul_inv, div] using
    mul_contains ha (reciprocal_contains hzero hb)

/-- The multiplication endpoints are exactly the four-corner formula printed
in Section 26.4. -/
theorem mul_endpoints (x y : RealInterval) :
    (x.mul y).lower =
        min (min (x.lower * y.lower) (x.lower * y.upper))
          (min (x.upper * y.lower) (x.upper * y.upper)) ∧
      (x.mul y).upper =
        max (max (x.lower * y.lower) (x.lower * y.upper))
          (max (x.upper * y.lower) (x.upper * y.upper)) := by
  exact ⟨rfl, rfl⟩


end RealInterval


end NumStability
