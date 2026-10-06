-- Source/Higham/Chapter02/Problem02.lean
--
-- Problem-specific theorem surface for Higham Chapter 2, Problem 2.2.

import NumStability.Analysis.FloatingPointArithmetic

namespace NumStability

noncomputable section

namespace FloatingPointFormat

/-!
# Higham Chapter 2, Problem 2.2

Problem 2.2 asks for a proof of Lemma 2.1.  The repository proves the
structural and real-order normalized-adjacency theorem in
`FloatingPointArithmetic.lean`; this file gives the exercise-level theorem
surface, with both possible choices of the named endpoint.
-/

/-- Problem 2.2 / Lemma 2.1, with the displayed bounds measured from the
first endpoint of an adjacent normalized pair. -/
theorem problem2_2_lemma2_1_spacing_bounds_left
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y) :
    fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon * |x| ≤ |x - y| ∧
      |x - y| ≤ fmt.machineEpsilon * |x| :=
  fmt.realOrderAdjacentNormalized_spacing_bounds_left h

/-- Problem 2.2 / Lemma 2.1, with the displayed bounds measured from the
neighbor endpoint of an adjacent normalized pair. -/
theorem problem2_2_lemma2_1_spacing_bounds_right
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y) :
    fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon * |y| ≤ |x - y| ∧
      |x - y| ≤ fmt.machineEpsilon * |y| := by
  have hb :=
    fmt.realOrderAdjacentNormalized_spacing_bounds_left
      (fmt.realOrderAdjacentNormalized_symm h)
  simpa [abs_sub_comm] using hb

/-- Problem 2.2 / Lemma 2.1, packaged for either endpoint of an adjacent
normalized pair. -/
theorem problem2_2_lemma2_1_spacing_bounds
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y) :
    (fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon * |x| ≤ |x - y| ∧
      |x - y| ≤ fmt.machineEpsilon * |x|) ∧
    (fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon * |y| ≤ |x - y| ∧
      |x - y| ≤ fmt.machineEpsilon * |y|) :=
  ⟨fmt.problem2_2_lemma2_1_spacing_bounds_left h,
    fmt.problem2_2_lemma2_1_spacing_bounds_right h⟩

end FloatingPointFormat

end

end NumStability
