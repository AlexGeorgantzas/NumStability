import HighamBench.P54Definitions

open scoped BigOperators

namespace HighamBench

/-- P54-T3: the inverse secular construction in equations (3.2)--(3.3). -/
theorem p54_t3_inverse_secular_construction
    (n : ℕ) (hn : 0 < n)
    (d lambda : P54Vector n)
    (hd : StrictMono d)
    (hlower : ∀ i, d i < lambda i)
    (hupper : ∀ i j, i < j → lambda i < d j) :
    (∀ i, 0 < p54SecularWeight d lambda i) ∧
      p54Characteristic lambda =
        p54Characteristic d +
          ∑ i, Polynomial.C (p54SecularWeight d lambda i) *
            p54DeletedCharacteristic d i := by
  -- PROOF_START P54-T3-H001
  sorry

end HighamBench
