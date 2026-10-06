-- Analysis/RelativePrecision.lean
--
-- Olver/Pryce relative precision notation from Higham Chapter 3, Section 3.4.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace NumStability

/-!
# Relative Precision

Higham Chapter 3 describes Olver's relative precision relation by writing that
`y` is related to `x` with relative precision `a` when
`y = exp(delta) * x` for some `|delta| < a`.  This file records the scalar
notation and the elementary symmetry/additivity rules used in the source text.
-/

/-- Olver's scalar relative precision relation:
`relPrecision a x y` means `y = exp(delta) * x` for some `|delta| < a`. -/
noncomputable def relPrecision (a x y : ℝ) : Prop :=
  ∃ delta : ℝ, |delta| < a ∧ y = Real.exp delta * x

/-- Any scalar has relative precision `a` with itself when `a > 0`. -/
theorem relPrecision_refl {a x : ℝ} (ha : 0 < a) :
    relPrecision a x x := by
  refine ⟨0, ?_, ?_⟩
  · simpa using ha
  · simp

/-- Olver's scalar relative precision relation is symmetric. -/
theorem relPrecision_symm {a x y : ℝ}
    (hxy : relPrecision a x y) :
    relPrecision a y x := by
  rcases hxy with ⟨delta, hdelta, rfl⟩
  refine ⟨-delta, ?_, ?_⟩
  · simpa [abs_neg] using hdelta
  · rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero delta]

/-- Chaining relative precision bounds adds the exponents. -/
theorem relPrecision_trans {a b x y z : ℝ}
    (hxy : relPrecision a x y) (hyz : relPrecision b y z) :
    relPrecision (a + b) x z := by
  rcases hxy with ⟨delta, hdelta, hy⟩
  rcases hyz with ⟨epsilon, hepsilon, hz⟩
  refine ⟨epsilon + delta, ?_, ?_⟩
  · calc
      |epsilon + delta| ≤ |epsilon| + |delta| := abs_add_le epsilon delta
      _ < b + a := add_lt_add hepsilon hdelta
      _ = a + b := by ring
  · rw [hz, hy, Real.exp_add]
    ring

/-- Pryce's `1(a)` notation, represented as relative precision from `1`. -/
noncomputable def pryceOne (a theta : ℝ) : Prop :=
  relPrecision a 1 theta

/-- Expands Pryce's `1(a)` notation into the explicit exponential witness. -/
theorem pryceOne_iff {a theta : ℝ} :
    pryceOne a theta ↔ ∃ delta : ℝ, |delta| < a ∧ theta = Real.exp delta := by
  unfold pryceOne relPrecision
  constructor
  · rintro ⟨delta, hdelta, htheta⟩
    refine ⟨delta, hdelta, ?_⟩
    simpa using htheta
  · rintro ⟨delta, hdelta, htheta⟩
    refine ⟨delta, hdelta, ?_⟩
    simp [htheta]

/-- Nonzero scalars related by relative precision have the same sign. -/
theorem relPrecision_same_sign_of_nonzero {a x y : ℝ}
    (hxy : relPrecision a x y) (hx : x ≠ 0) :
    0 < x * y := by
  rcases hxy with ⟨delta, _, rfl⟩
  have hexp : 0 < Real.exp delta := Real.exp_pos delta
  have hsq : 0 < x * x := mul_self_pos.mpr hx
  calc
    0 < Real.exp delta * (x * x) := mul_pos hexp hsq
    _ = x * (Real.exp delta * x) := by ring

end NumStability
