import Mathlib

open scoped BigOperators

namespace HighamBench

noncomputable def p56NodePolynomial {k : ℕ}
    (nodes : Fin k → ℝ) : Polynomial ℝ :=
  ∏ i, (Polynomial.X - Polynomial.C (nodes i))

noncomputable def p56Correction {k : ℕ}
    (nodes : Fin k → ℝ) : Polynomial ℝ :=
  let phi := p56NodePolynomial nodes;
  -(Polynomial.C ((Polynomial.eval 0 phi)⁻¹) * phi.divX)

noncomputable def p56ExtendedApproximant {k : ℕ}
    (nodes : Fin k → ℝ) (p : Polynomial ℝ) : Polynomial ℝ :=
  let phi := p56NodePolynomial nodes;
  p56Correction nodes +
    Polynomial.C ((Polynomial.eval 0 phi)⁻¹) * phi * p

noncomputable def p56IntervalFactor {k : ℕ}
    (a b : ℝ) (nodes : Fin k → ℝ) : ℝ :=
  |(Polynomial.eval 0 (p56NodePolynomial nodes))⁻¹| *
    ∏ i, max (b - nodes i) (nodes i - a)

end HighamBench
