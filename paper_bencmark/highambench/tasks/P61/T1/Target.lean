import HighamBench.P61Definitions

namespace HighamBench

open scoped BigOperators

/-- One fan-in node product error propagated through a left factor. -/
theorem p61_t1_fanin_one_node_propagated_error
    (fp : P61FPModel) (r m n p : ℕ)
    (L : P61Matrix r m) (A : P61Matrix m n) (B : P61Matrix n p)
    (hvalid : P61GammaValid fp.u n) :
    ∀ i : Fin r, ∀ j : Fin p,
      |∑ k : Fin m, L i k *
        (p61RoundedMatMul fp A B k j - p61MatMul A B k j)| ≤
      p61Gamma fp.u n *
        ∑ k : Fin m, |L i k| *
          (∑ t : Fin n, |A k t| * |B t j|) := by
  -- PROOF_START P61-T1-H001
  sorry

end HighamBench
