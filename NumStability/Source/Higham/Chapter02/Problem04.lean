import NumStability.Analysis.FloatingPointArithmetic

namespace NumStability

noncomputable section

namespace FloatingPointFormat

/-!
# Higham Chapter 2, Problem 2.4

Problem 2.4 asks for a proof of Theorem 2.3, the inverse relative-error
representation `fl(x) = x / (1 + δ)`.  The finite-format proof is developed in
`FloatingPointArithmetic.lean`; this file exposes source-shaped problem-set
wrappers for the relation-valued theorem and the main finite selectors.
-/

/-- Problem 2.4 / Theorem 2.3 for the finite nearest-rounding relation. -/
theorem problem2_4_theorem2_3_nearest_finite
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ 1 + δ ≠ 0 ∧ y = x / (1 + δ) := by
  rcases
    fmt.exists_nearestRoundingToFinite_inverseRelErrorWitness_finiteNormalRange
      hx with
    ⟨y, δ, hround, hδ, hrepr⟩
  rcases hrepr with ⟨hden, hy⟩
  exact ⟨y, δ, hround, hδ, hden, hy⟩

/-- Problem 2.4 / Theorem 2.3 for the source-style finite-normal choice `fl`. -/
theorem problem2_4_theorem2_3_finiteNormalFl
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      |δ| ≤ fmt.unitRoundoff ∧
        1 + δ ≠ 0 ∧ fmt.finiteNormalFl x hx = x / (1 + δ) := by
  rcases fmt.finiteNormalFl_inverseRelErrorWitness hx with
    ⟨δ, _hround, hδ, hrepr⟩
  rcases hrepr with ⟨hden, hy⟩
  exact ⟨δ, hδ, hden, hy⟩

/-- Problem 2.4 / Theorem 2.3 for the total finite round-to-even selector,
restricted to finite-normal inputs as in the theorem's range hypothesis. -/
theorem problem2_4_theorem2_3_finiteRoundToEven
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite x (fmt.finiteRoundToEven x) ∧
        |δ| ≤ fmt.unitRoundoff ∧
          1 + δ ≠ 0 ∧ fmt.finiteRoundToEven x = x / (1 + δ) := by
  rcases fmt.finiteRoundToEven_inverseRelErrorWitness_of_finiteNormalRange hx with
    ⟨δ, hround, hδ, hrepr⟩
  rcases hrepr with ⟨hden, hy⟩
  exact ⟨δ, hround, hδ, hden, hy⟩

end FloatingPointFormat

end

end NumStability
