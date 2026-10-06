import Mathlib

namespace HighamBench

open scoped BigOperators

abbrev P32Vector (n : ℕ) := Fin n → ℝ

abbrev P32CoefficientMap (n t : ℕ) := Fin n → Fin t → ℝ

/-- Componentwise perturbation boxes for the structured parameters and right-hand side. -/
def P32Admissible {n t : ℕ}
    (g : P32Vector t) (f : P32Vector n)
    (dp : P32Vector t) (db : P32Vector n) : Prop :=
  (∀ j, |dp j| ≤ g j) ∧ (∀ i, |db i| ≤ f i)

/-- The first-order response `A⁻¹ Δb - A⁻¹ X B Δp` in equation (3.2). -/
noncomputable def p32LinearResponse {n t : ℕ}
    (K : P32CoefficientMap n t) (H : P32CoefficientMap n n)
    (dp : P32Vector t) (db : P32Vector n) : P32Vector n :=
  fun i ↦ ∑ j, H i j * db j - ∑ j, K i j * dp j

/-- The attainable relative first-order response norms in the perturbation box. -/
noncomputable def p32LinearizedValues {n t : ℕ}
    (K : P32CoefficientMap n t) (H : P32CoefficientMap n n)
    (g : P32Vector t) (f : P32Vector n) (xNorm : ℝ) : Set ℝ :=
  {q | ∃ dp db, P32Admissible g f dp db ∧
      q = ‖p32LinearResponse K H dp db‖ / xNorm}

/-- The worst attainable relative first-order response. -/
noncomputable def p32LinearizedCondition {n t : ℕ}
    (K : P32CoefficientMap n t) (H : P32CoefficientMap n n)
    (g : P32Vector t) (f : P32Vector n) (xNorm : ℝ) : ℝ :=
  sSup (p32LinearizedValues K H g f xNorm)

/-- The componentwise radius on the right-hand side of equation (3.3). -/
noncomputable def p32ConditionRadius {n t : ℕ}
    (K : P32CoefficientMap n t) (H : P32CoefficientMap n n)
    (g : P32Vector t) (f : P32Vector n) : P32Vector n :=
  fun i ↦ ∑ j, |K i j| * g j + ∑ j, |H i j| * f j

/-- The explicit structured condition formula in equation (3.4). -/
noncomputable def p32ConditionFormula {n t : ℕ}
    (K : P32CoefficientMap n t) (H : P32CoefficientMap n n)
    (g : P32Vector t) (f : P32Vector n) (xNorm : ℝ) : ℝ :=
  ‖p32ConditionRadius K H g f‖ / xNorm

end HighamBench
