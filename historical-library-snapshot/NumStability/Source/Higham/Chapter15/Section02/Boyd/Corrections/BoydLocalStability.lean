import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
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
# Chapter15 Section02 Boyd Corrections BoydLocalStability

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter15BoydLocalStability` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open Filter Function

open scoped BigOperators Topology

/-- A two-dimensional nilpotent derivative with transient amplification. -/
noncomputable def higham15TransientNilpotent :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (2 • ContinuousLinearMap.inl ℝ ℝ ℝ).comp
    (ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem higham15TransientNilpotent_apply (x : ℝ × ℝ) :
    higham15TransientNilpotent x = (2 * x.2, 0) := by
  simp [higham15TransientNilpotent]

theorem higham15TransientNilpotent_sq :
    higham15TransientNilpotent ^ 2 = 0 := by
  ext <;> simp [pow_two, higham15TransientNilpotent_apply]

theorem higham15TransientNilpotent_norm_ge_two :
    (2 : ℝ) ≤ ‖higham15TransientNilpotent‖ := by
  have h := higham15TransientNilpotent.le_opNorm (0, 1)
  simpa [higham15TransientNilpotent_apply] using h

/-- Finite discrepancy witness: a derivative can be power-stable (indeed,
nilpotent of index two) while failing `‖L‖ < 1` in the repository's default
norm.  Thus the adapted-norm bridge above is mathematically necessary. -/
theorem higham15_power_stable_not_default_norm_contraction_witness :
    higham15TransientNilpotent ^ 2 = 0 ∧
      ¬ ‖higham15TransientNilpotent‖ < 1 := by
  refine ⟨higham15TransientNilpotent_sq, ?_⟩
  linarith [higham15TransientNilpotent_norm_ge_two]

end Ch15
end NumStability
