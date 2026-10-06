import Mathlib

namespace HighamBenchCandidate

/-- A nonempty binary summation tree. Each internal node records the relative
rounding error of its addition; leaves are exact input values. -/
inductive SummationTree where
  | input (x : ℝ) : SummationTree
  | add (left right : SummationTree) (δ : ℝ) : SummationTree

/-- The exact partial sum at the root of a subtree. -/
def exactSum : SummationTree → ℝ
  | .input x => x
  | .add left right _ => exactSum left + exactSum right

/-- At each node, add the computed child values and round that addition. -/
def computedSum : SummationTree → ℝ
  | .input x => x
  | .add left right δ => (computedSum left + computedSum right) * (1 + δ)

/-- The standard relative-error bound holds at every addition. -/
def roundoffBounded (u : ℝ) : SummationTree → Prop
  | .input _ => True
  | .add left right δ => |δ| ≤ u ∧ roundoffBounded u left ∧ roundoffBounded u right

/-- One list entry per internal node, weighted by the product of rounding
factors at its strict ancestors. `ancestorProduct` is the product already
accumulated above this subtree. -/
def errorTerms : SummationTree → ℝ → List ℝ
  | .input _, _ => []
  | .add left right δ, ancestorProduct =>
      ((exactSum (.add left right δ) * δ) * ancestorProduct) ::
        (errorTerms left (ancestorProduct * (1 + δ)) ++
          errorTerms right (ancestorProduct * (1 + δ)))

/-- Lemma 2.2, equation (2.3): the forward error of any binary summation
tree is the sum of its local errors, propagated through strict ancestors. -/
theorem target :
    ∀ (u : ℝ) (tree : SummationTree),
      0 ≤ u → roundoffBounded u tree →
        computedSum tree - exactSum tree = (errorTerms tree 1).sum := by
  sorry

end HighamBenchCandidate
