import HighamBench.P61Definitions

namespace HighamBench

open scoped BigOperators

/-- The Method B off-diagonal block estimate in the proof of (6.1). -/
theorem p61_t2_methodB_offdiagonal_residual
    (fp : P61FPModel) (n r p : ℕ)
    (L22 : P61Matrix n n) (L21 : P61Matrix n r)
    (X11 : P61Matrix r p)
    (hdiag : ∀ i, L22 i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L22 i j = 0)
    (hn : P61GammaValid fp.u n)
    (hr : P61GammaValid fp.u r) :
    ∀ i j,
      |(∑ k : Fin n, L22 i k * p61MethodBOffDiagonal fp L22 L21 X11 k j) +
        (∑ k : Fin r, L21 i k * X11 k j)| ≤
      p61Gamma fp.u n *
        (∑ k : Fin n, |L22 i k| * |p61MethodBOffDiagonal fp L22 L21 X11 k j|) +
      p61Gamma fp.u r *
        (∑ k : Fin r, |L21 i k| * |X11 k j|) := by
  -- PROOF_START P61-T2-H001
  sorry

end HighamBench
