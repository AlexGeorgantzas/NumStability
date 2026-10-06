import HighamBench.P62Definitions

namespace HighamBench

open scoped BigOperators

/-- Method D with Method 1 triangular inverses: the exact right-residual
    decomposition corresponding to the paragraph following (3.9). -/
theorem p62_t2_methodD_right_residual
    (fp : P62FPModel) (n : ℕ)
    (A L U E : P62Matrix n n)
    (hfactor : L * U = A + E)
    (hLdiag : ∀ i, L i i ≠ 0)
    (hLtri : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hUdiag : ∀ i, U i i ≠ 0)
    (hUtri : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hvalid : P62GammaValid fp.u n) :
    ∃ DL DU DM : P62Matrix n n,
      (∀ i j, |DL i j| ≤ p62Gamma fp.u n *
        (∑ k : Fin n, |L i k| * |p62LowerInverse fp n L k j|)) ∧
      (∀ i j, |DU i j| ≤ p62Gamma fp.u n *
        (∑ k : Fin n, |U i k| * |p62UpperInverse fp n U k j|)) ∧
      (∀ i j, |DM i j| ≤ p62Gamma fp.u n *
        (∑ k : Fin n,
          |p62UpperInverse fp n U i k| * |p62LowerInverse fp n L k j|)) ∧
      A * p62ComputedInverse fp n L U - 1 =
        -DL - L * DU * p62LowerInverse fp n L + A * DM -
          E * p62UpperInverse fp n U * p62LowerInverse fp n L := by
  -- PROOF_START P62-T2-H001
  sorry

end HighamBench
