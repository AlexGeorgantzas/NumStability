import HighamBench.P53Definitions

open scoped BigOperators

namespace HighamBench

/-- P53-T3: the subdiagonal product and nontriviality result of Theorem 4.5. -/
theorem p53_t3_core_subdiagonal_product
    (n : ℕ) (hn : 0 < n) (run : P53CoreRollupRun n)
    (x : P53Vector n) (alpha a0 : ℂ)
    (hx : x = alpha • run.state n)
    (hxlast : x ⟨n, by omega⟩ = -1)
    (halpha : ‖alpha‖ = p53VecNorm2 x)
    (hvw : ∀ i, ‖run.v i‖ = ‖run.w i‖)
    (Ctail Rtail Htail : P53Matrix n)
    (hCdiag : ∀ i, Ctail i i = run.w i)
    (hCtri : Ctail.BlockTriangular id)
    (hRtri : Rtail.BlockTriangular id)
    (hHtail : Htail = Ctail * Rtail)
    (hdetR : ‖Matrix.det Rtail‖ = ‖a0‖)
    (ha0 : a0 ≠ 0) :
    (∀ i, 0 < ‖Htail i i‖) ∧
      (∏ i, ‖Htail i i‖) = ‖a0‖ / p53VecNorm2 x := by
  -- PROOF_START P53-T3-H001
  sorry

end HighamBench
