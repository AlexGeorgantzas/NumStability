import HighamBench.P49Definitions

open scoped BigOperators

namespace HighamBench

/-- P49-T1: the real nondegenerate perturbation witness in Theorem 2.3. -/
theorem p49_t1_real_symmetric_backward_witness {n : ℕ}
    (A B : P49Matrix n) (x y : P49Vector n)
    (hA : p49Symmetric A) (hB : p49Symmetric B)
    (henergy : p49Dot x x = p49Dot y y) (hxy : x ≠ y)
    (c e f lambda : ℝ)
    (hres : ∀ i, c * y i = lambda * p49MatVec B x i - p49MatVec A x i)
    (hc : 0 ≤ c) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hlambda : 0 < lambda) (hden : 0 < e + lambda * f) :
    ∃ dA dB : P49Matrix n,
      p49Symmetric dA ∧ p49Symmetric dB ∧
      (∀ i, p49MatVec A x i + p49MatVec dA x i =
        lambda * (p49MatVec B x i + p49MatVec dB x i)) ∧
      p49OpNormBound dA (e / (e + lambda * f) * c) ∧
      p49OpNormBound dB (f / (e + lambda * f) * c) := by
  -- PROOF_START P49-T1-H001
  sorry

end HighamBench
