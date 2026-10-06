import HighamBench.P45Definitions

open scoped BigOperators

namespace HighamBench

/-- P45-T1: the Givens-product coefficient estimate in Lemma 5.1. -/
theorem p45_t1_gmres_coefficient_bound
    {n : ℕ} (steps : List (P45GivensStep n))
    (row : P45Vector n) (j : Fin n)
    (residual sigma eta : ℝ)
    (hsigma : 0 < sigma)
    (hrow : p45VecNorm row ≤ sigma⁻¹)
    (heta : eta = residual *
      p45Inner row (p45MatVec (p45GivensProduct steps) (p45Basis j))) :
    |eta| ≤ sigma⁻¹ * |residual| := by
  -- PROOF_START P45-T1-H001
  sorry

end HighamBench
