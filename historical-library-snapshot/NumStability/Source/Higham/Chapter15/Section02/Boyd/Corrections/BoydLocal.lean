import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Sequences
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# Chapter15 Section02 Boyd Corrections BoydLocal

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter15BoydSourceLocal` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open Filter Function Set

open scoped BigOperators Topology

/-- A strict maximum need not be nondegenerate: `-t^4` has a strict maximum
at zero but its quadratic term vanishes.  This finite witness is the precise
logical error in the printed premise of Boyd Theorem 3; it does not challenge
the corrected nondegenerate theorem used by Higham's word "strong". -/
theorem strictMaximum_does_not_imply_negative_quadratic_term :
    (∀ t : ℝ, t ≠ 0 → -(t ^ 4) < -(0 ^ 4)) ∧
      ¬ (∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, -(t ^ 4) ≤ -c * t ^ 2) := by
  constructor
  · intro t ht
    have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
    nlinarith [sq_nonneg (t ^ 2)]
  · rintro ⟨c, hc, hquad⟩
    let t : ℝ := Real.sqrt (c / 2)
    have hc2 : 0 < c / 2 := by positivity
    have ht2 : t ^ 2 = c / 2 := by
      dsimp [t]
      rw [Real.sq_sqrt (le_of_lt hc2)]
    have h := hquad t
    rw [ht2, show t ^ 4 = (t ^ 2) ^ 2 by ring, ht2] at h
    nlinarith

end Ch15
end NumStability
