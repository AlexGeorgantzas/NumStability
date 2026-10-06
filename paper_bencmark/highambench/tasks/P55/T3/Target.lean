import HighamBench.P55Definitions

namespace HighamBench

open Matrix

/-- P55-T3: Theorem 4.1, equations (4.6)--(4.7). -/
theorem p55_t3_loss_of_biorthogonality
    (k : ℕ)
    (T C Delta D F G K L N M : P55Matrix (k + 1))
    (a b z w : P55Vector (k + 1))
    (beta gamma theta : ℝ)
    (ha : a (Fin.last k) = 0)
    (hb : b (Fin.last k) = 0)
    (hmaster :
      gamma • p55Outer (p55LastBasis k) a -
          beta • p55Outer b (p55LastBasis k) =
        (C * T - T * C) + (Delta * T - T * Delta) +
          (D * T - T * D) + (F - G))
    (hDelta : Delta * T - T * Delta = K - L)
    (herror : F - G = N - M)
    (hCT : p55StrictLower (C * T - T * C))
    (hDT : p55StrictUpper (D * T - T * D))
    (hK : p55StrictLower K) (hL : p55StrictUpper L)
    (hN : p55StrictLower N) (hM : p55StrictUpper M)
    (hz : T *ᵥ z = theta • z)
    (hw : w ᵥ* T = theta • w)
    (hgamma : gamma * (w ⬝ᵥ p55LastBasis k) ≠ 0)
    (hbeta : beta * (p55LastBasis k ⬝ᵥ z) ≠ 0) :
    a ⬝ᵥ z =
        (w ⬝ᵥ ((K + N) *ᵥ z)) /
          (gamma * (w ⬝ᵥ p55LastBasis k)) ∧
      w ⬝ᵥ b =
        (w ⬝ᵥ ((L + M) *ᵥ z)) /
          (beta * (p55LastBasis k ⬝ᵥ z)) := by
  -- PROOF_START P55-T3-H001
  sorry

end HighamBench
