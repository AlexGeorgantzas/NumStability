import HighamBench.P68Definitions

namespace HighamBench

open scoped BigOperators

/-- Algorithm 3.1, one-row variable-bucket gamma form of (3.5)–(3.6). -/
theorem p68_t2_adaptive_row_many_error
    (q n : ℕ) (outer : P68FPModel) (bucket : Fin q → P68FPModel)
    (a x : Fin q → Fin n → ℝ)
    (hq : 0 < q)
    (hprecision : ∀ k, outer.u ≤ (bucket k).u)
    (hvalidBucket : ∀ k, P68GammaValid (bucket k).u n)
    (hvalidOuter : P68GammaValid outer.u (q - 1)) :
    |p68AdaptiveRowMany q n outer bucket a x -
      ∑ k : Fin q, ∑ j : Fin n, a k j * x k j| ≤
      p68Gamma outer.u (q - 1) *
        (∑ k : Fin q, ∑ j : Fin n, |a k j * x k j|) +
      (1 + p68Gamma outer.u (q - 1)) *
        (∑ k : Fin q, p68Gamma (bucket k).u n *
          (∑ j : Fin n, |a k j * x k j|)) := by
  -- PROOF_START P68-T2-H001
  sorry

end HighamBench
