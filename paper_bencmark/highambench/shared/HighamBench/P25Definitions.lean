import Mathlib

namespace HighamBench

open scoped BigOperators Topology

/-- The matrix power series `h_ℓ(A)` from Theorems 1.1 and 4.2.  It is
stated for a complex Banach algebra, which includes the paper's finite complex
matrix algebras equipped with a submultiplicative norm. -/
noncomputable def p25SeriesValue {E : Type*}
    [NormedRing E] [NormedAlgebra ℂ E] [CompleteSpace E]
    (c : ℕ → ℂ) (A : E) : E :=
  ∑' k : ℕ, c k • A ^ k

/-- The absolute scalar power series `h̃_ℓ(r)` used to majorize the matrix
series in Theorems 1.1 and 4.2. -/
noncomputable def p25AbsoluteSeries (c : ℕ → ℂ) (r : ℝ) : ℝ :=
  ∑' k : ℕ, ‖c k‖ * r ^ k

/-- The convergence and norm conclusion of the power-series bounds in
Theorem 4.2. -/
def P25SeriesBound {E : Type*}
    [NormedRing E] [NormOneClass E] [NormedAlgebra ℂ E] [CompleteSpace E]
    (c : ℕ → ℂ) (A : E) (r : ℝ) : Prop :=
  Summable (fun k : ℕ ↦ c k • A ^ k) ∧
    ‖p25SeriesValue c A‖ ≤ p25AbsoluteSeries c r

end HighamBench
