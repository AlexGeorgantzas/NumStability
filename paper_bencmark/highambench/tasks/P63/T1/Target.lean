import HighamBench.P63Definitions

namespace HighamBench

open scoped BigOperators

/-- Equation (2.3): the two-precision computed residual bound. -/
theorem p63_t1_two_precision_residual
    (fpHi fpLo : P63FPModel) (n : ℕ)
    (A : P63Matrix n n) (x b : Fin n → ℝ)
    (hvalid : P63GammaValid fpHi.u (n + 1))
    (_hprecision : fpHi.u ≤ fpLo.u) :
    ∀ i : Fin n,
      |p63StoredResidual fpHi fpLo n A x b i -
        (b i - ∑ j : Fin n, A i j * x j)| ≤
      fpLo.u * |b i - ∑ j : Fin n, A i j * x j| +
        (1 + fpLo.u) * p63Gamma fpHi.u (n + 1) *
          (|b i| + ∑ j : Fin n, |A i j| * |x j|) := by
  -- PROOF_START P63-T1-H001
  sorry

end HighamBench
