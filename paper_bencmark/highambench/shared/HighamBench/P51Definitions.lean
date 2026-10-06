import Mathlib

open scoped BigOperators

namespace HighamBench

/-- The partial-fraction Padé expression in equation (1.1). -/
noncomputable def p51Pade {m : ℕ} (a b : Fin m → ℝ) (z : ℂ) : ℂ :=
  ∑ j : Fin m, (a j : ℂ) * z / (1 + (b j : ℂ) * z)

/-- The scalar spectral-radius majorant displayed in Lemma 2.1. -/
noncomputable def p51PadeRadiusBound {m : ℕ}
    (a b : Fin m → ℝ) (r : ℝ) : ℝ :=
  ∑ j : Fin m, a j * r / (1 - b j * r)

end HighamBench
