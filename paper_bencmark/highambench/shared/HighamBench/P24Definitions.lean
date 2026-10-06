import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

namespace HighamBench

open scoped BigOperators Topology

/-- The widths at successive outside-inside scaling cycles in the proof of
Lemma 21. Cycle indexing replaces the paper's indices `t₀, t₀+2, ...`. -/
structure P24WidthSequence where
  width : ℕ → ℝ
  width_nonneg : ∀ n, 0 ≤ width n
  width_half : ∀ n, width (n + 1) ≤ (1 / 2 : ℝ) * width n

/-- The two relative distances in each outside-inside cycle, together with
the estimates established immediately before the majorant is introduced in
Lemma 21. -/
structure P24Lemma21Data extends P24WidthSequence where
  relativeEven : ℕ → ℝ
  relativeOdd : ℕ → ℝ
  relative_even_tail : ∀ n,
    relativeEven n ≤
      Real.exp (∑' k : ℕ, 2 * width (n + 1 + k)) - 1
  relative_odd_le_even : ∀ n, relativeOdd n ≤ relativeEven n

/-- The explicit infinite-tail majorant `nu` constructed in Lemma 21. -/
noncomputable def p24WidthTail (run : P24WidthSequence) (n : ℕ) : ℝ :=
  ∑' k : ℕ, 2 * run.width (n + 1 + k)

noncomputable def p24LinearMajorant (run : P24WidthSequence) (n : ℕ) : ℝ :=
  Real.exp (p24WidthTail run n) - 1

end HighamBench
