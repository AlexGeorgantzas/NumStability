import HighamBench.P62Definitions

namespace HighamBench

open scoped BigOperators

/-- Method 1 triangular-inverse right residual. -/
theorem p62_t1_method1_inverse_right_residual
    (fp : P62FPModel) (n : ℕ) (L : P62Matrix n n)
    (hLdiag : ∀ i, L i i ≠ 0)
    (hLtri : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hvalid : P62GammaValid fp.u n) :
    ∀ i j : Fin n,
      |((1 : P62Matrix n n) - L * p62LowerInverse fp n L) i j| ≤
        p62Gamma fp.u n *
          ∑ k : Fin n, |L i k| * |p62LowerInverse fp n L k j| := by
  -- PROOF_START P62-T1-H001
  sorry

end HighamBench
