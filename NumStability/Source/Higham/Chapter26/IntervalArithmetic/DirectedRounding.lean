/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Analysis.FloatingPointArithmetic
import NumStability.Source.Higham.Chapter26.IntervalArithmetic.ExactOperations

namespace NumStability

/-! # Higham Chapter 26: Outward-Directed Interval Rounding

Finite-range endpoint conditions, outward rounding, and containment for the four interval operations.
-/

namespace RealInterval

/-! ### Concrete outward-directed floating-point endpoint production -/

/-- The real-valued finite rounding layer can enclose an endpoint whenever it
is in either the gradual-underflow range or the finite normal range.  Values in
the IEEE overflow range require the separate infinity-valued result layer. -/
def EndpointInFiniteRange (fmt : FloatingPointFormat) (a : ℝ) : Prop :=
  fmt.finiteUnderflowRange a ∨ fmt.finiteNormalRange a

theorem finiteRoundTowardNegative_le_of_endpointRange
    (fmt : FloatingPointFormat) {a : ℝ} (ha : EndpointInFiniteRange fmt a) :
    fmt.finiteRoundTowardNegative a ≤ a := by
  rcases ha with ha | ha
  · exact fmt.finiteRoundTowardNegative_le_of_finiteUnderflowRange ha
  · exact fmt.finiteRoundTowardNegative_le_of_finiteNormalRange ha

theorem le_finiteRoundTowardPositive_of_endpointRange
    (fmt : FloatingPointFormat) {a : ℝ} (ha : EndpointInFiniteRange fmt a) :
    a ≤ fmt.finiteRoundTowardPositive a := by
  rcases ha with ha | ha
  · exact fmt.le_finiteRoundTowardPositive_of_finiteUnderflowRange ha
  · exact fmt.le_finiteRoundTowardPositive_of_finiteNormalRange ha

/-- Page 481's computed producer at the finite-real layer: round the exact left
endpoint toward negative infinity and the exact right endpoint toward positive
infinity.  The range evidence is exactly what makes both rounded endpoints
finite reals instead of IEEE infinities. -/
noncomputable def outwardRounded
    (fmt : FloatingPointFormat) (x : RealInterval)
    (hlower : EndpointInFiniteRange fmt x.lower)
    (hupper : EndpointInFiniteRange fmt x.upper) : RealInterval where
  lower := fmt.finiteRoundTowardNegative x.lower
  upper := fmt.finiteRoundTowardPositive x.upper
  ordered :=
    (finiteRoundTowardNegative_le_of_endpointRange fmt hlower).trans
      (x.ordered.trans (le_finiteRoundTowardPositive_of_endpointRange fmt hupper))

/-- The outward-directed computed interval contains every real already
contained by the exact endpoint interval. -/
theorem outwardRounded_contains
    (fmt : FloatingPointFormat) (x : RealInterval)
    (hlower : EndpointInFiniteRange fmt x.lower)
    (hupper : EndpointInFiniteRange fmt x.upper) {a : ℝ}
    (ha : x.Contains a) :
    (outwardRounded fmt x hlower hupper).Contains a := by
  exact
    ⟨(finiteRoundTowardNegative_le_of_endpointRange fmt hlower).trans ha.1,
      ha.2.trans (le_finiteRoundTowardPositive_of_endpointRange fmt hupper)⟩

/-- Concrete computed interval addition from page 481. -/
noncomputable def outwardAdd (fmt : FloatingPointFormat) (x y : RealInterval)
    (hlower : EndpointInFiniteRange fmt (x.add y).lower)
    (hupper : EndpointInFiniteRange fmt (x.add y).upper) : RealInterval :=
  outwardRounded fmt (x.add y) hlower hupper

theorem outwardAdd_contains (fmt : FloatingPointFormat) {x y : RealInterval}
    (hlower : EndpointInFiniteRange fmt (x.add y).lower)
    (hupper : EndpointInFiniteRange fmt (x.add y).upper) {a b : ℝ}
    (ha : x.Contains a) (hb : y.Contains b) :
    (outwardAdd fmt x y hlower hupper).Contains (a + b) :=
  outwardRounded_contains fmt (x.add y) hlower hupper (add_contains ha hb)

/-- Concrete computed interval subtraction from page 481. -/
noncomputable def outwardSub (fmt : FloatingPointFormat) (x y : RealInterval)
    (hlower : EndpointInFiniteRange fmt (x.sub y).lower)
    (hupper : EndpointInFiniteRange fmt (x.sub y).upper) : RealInterval :=
  outwardRounded fmt (x.sub y) hlower hupper

theorem outwardSub_contains (fmt : FloatingPointFormat) {x y : RealInterval}
    (hlower : EndpointInFiniteRange fmt (x.sub y).lower)
    (hupper : EndpointInFiniteRange fmt (x.sub y).upper) {a b : ℝ}
    (ha : x.Contains a) (hb : y.Contains b) :
    (outwardSub fmt x y hlower hupper).Contains (a - b) :=
  outwardRounded_contains fmt (x.sub y) hlower hupper (sub_contains ha hb)

/-- Concrete computed interval multiplication from page 481. -/
noncomputable def outwardMul (fmt : FloatingPointFormat) (x y : RealInterval)
    (hlower : EndpointInFiniteRange fmt (x.mul y).lower)
    (hupper : EndpointInFiniteRange fmt (x.mul y).upper) : RealInterval :=
  outwardRounded fmt (x.mul y) hlower hupper

theorem outwardMul_contains (fmt : FloatingPointFormat) {x y : RealInterval}
    (hlower : EndpointInFiniteRange fmt (x.mul y).lower)
    (hupper : EndpointInFiniteRange fmt (x.mul y).upper) {a b : ℝ}
    (ha : x.Contains a) (hb : y.Contains b) :
    (outwardMul fmt x y hlower hupper).Contains (a * b) :=
  outwardRounded_contains fmt (x.mul y) hlower hupper (mul_contains ha hb)

/-- Concrete computed interval division from page 481. -/
noncomputable def outwardDiv (fmt : FloatingPointFormat) (x y : RealInterval)
    (hzero : ¬ y.Contains 0)
    (hlower : EndpointInFiniteRange fmt (x.div y hzero).lower)
    (hupper : EndpointInFiniteRange fmt (x.div y hzero).upper) : RealInterval :=
  outwardRounded fmt (x.div y hzero) hlower hupper

theorem outwardDiv_contains (fmt : FloatingPointFormat) {x y : RealInterval}
    (hzero : ¬ y.Contains 0)
    (hlower : EndpointInFiniteRange fmt (x.div y hzero).lower)
    (hupper : EndpointInFiniteRange fmt (x.div y hzero).upper) {a b : ℝ}
    (ha : x.Contains a) (hb : y.Contains b) :
    (outwardDiv fmt x y hzero hlower hupper).Contains (a / b) :=
  outwardRounded_contains fmt (x.div y hzero) hlower hupper
    (div_contains hzero ha hb)

end RealInterval


end NumStability
