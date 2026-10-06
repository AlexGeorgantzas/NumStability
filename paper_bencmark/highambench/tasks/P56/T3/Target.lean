import HighamBench.P56Definitions

open scoped BigOperators

namespace HighamBench

/-- P56-T3: the exceptional-point construction in Lemma 4.2. -/
theorem p56_t3_exceptional_point_approximation
    (k n : ℕ) (a b epsilon : ℝ)
    (nodes : Fin k → ℝ) (p : Polynomial ℝ)
    (ha : 0 < a) (hab : a < b)
    (hnodes : ∀ i, 0 < nodes i)
    (hinj : Function.Injective nodes)
    (hpdegree : p.natDegree ≤ n)
    (hpapprox : ∀ t, a ≤ t → t ≤ b →
      |t⁻¹ - Polynomial.eval t p| ≤ epsilon) :
    (p56ExtendedApproximant nodes p).natDegree ≤ n + k ∧
      (∀ i, Polynomial.eval (nodes i)
        (p56ExtendedApproximant nodes p) = (nodes i)⁻¹) ∧
      ∀ t, a ≤ t → t ≤ b →
        |t⁻¹ - Polynomial.eval t (p56ExtendedApproximant nodes p)| ≤
          p56IntervalFactor a b nodes * epsilon := by
  -- PROOF_START P56-T3-H001
  sorry

end HighamBench
