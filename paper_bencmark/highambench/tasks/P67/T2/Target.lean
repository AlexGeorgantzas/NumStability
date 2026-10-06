import HighamBench.P67Definitions

namespace HighamBench

open scoped BigOperators

/-- Equation (2.5), exact-split one-entry case with p² enumerated word pairs. -/
theorem p67_t2_multiword_product_error
    (fp : P67FPModel) (p n : ℕ)
    (pairs : Fin (p * p) ≃ Fin p × Fin p)
    (a b : Fin p → Fin n → ℝ)
    (hp : 0 < p)
    (hvalid : P67GammaValid fp.u (n + (p * p - 1))) :
    |p67MultiwordDotMany fp p n pairs a b -
      ∑ t : Fin (p * p), ∑ j : Fin n,
        a (pairs t).1 j * b (pairs t).2 j| ≤
      p67Gamma fp.u (n + (p * p - 1)) *
        ∑ t : Fin (p * p), ∑ j : Fin n,
          |a (pairs t).1 j * b (pairs t).2 j| := by
  -- PROOF_START P67-T2-H001
  sorry

end HighamBench
