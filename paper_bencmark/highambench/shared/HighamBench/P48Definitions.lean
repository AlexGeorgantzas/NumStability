import Mathlib

namespace HighamBench

/-- The Laurent--Krylov space
`span {v_j | -m <= j < m}` used in Proposition 3.4.  Under the paper's
recurrence, `v_j = A^j B`, with negative indices interpreted using `A⁻¹`. -/
def p48LaurentSpan {V : Type*} [AddCommGroup V] [Module ℝ V]
    (v : ℤ → V) (m : ℕ) : Submodule ℝ V :=
  Submodule.span ℝ (v '' Set.Ico (-(m : ℤ)) (m : ℤ))

/-- The two new directions at iteration `m`, after quotienting out the old
Laurent--Krylov space.  Their dependence is exactly the rank-loss hypothesis
in Proposition 3.4. -/
def p48BreakdownDirections {V : Type*} [AddCommGroup V] [Module ℝ V]
    (v : ℤ → V) (m : ℕ) : Fin 2 → V ⧸ p48LaurentSpan v m :=
  ![Submodule.Quotient.mk (v (-((m : ℤ)) - 1)),
    Submodule.Quotient.mk (v (m : ℤ))]

end HighamBench
