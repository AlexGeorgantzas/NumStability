import HighamBench.P41Definitions

open scoped BigOperators Topology Matrix
open Matrix

namespace HighamBench

/-- P41-T3: the augmented-matrix phi-function column identity of Theorem 2.1. -/
theorem p41_t3_augmented_phi_column {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (τ : ℂ) (ell : ℕ) (j : Fin p) (i : Fin n) :
    p41Phi ell (τ • p41Augmented A W) (Sum.inl i) (Sum.inr j) =
      ∑ r : Fin (j.val + 1),
        τ ^ (r.val + 1) *
          (Matrix.mulVec (p41Phi (ell + r.val + 1) (τ • A))
            (p41ReverseColumn W j r)) i := by
  -- PROOF_START P41-T3-H001
  sorry

end HighamBench
