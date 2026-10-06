import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
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
import NumStability.Algorithms.NormEstimation.PNorm.Duality.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormGeneral
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# NumStability Algorithms NormEstimation PNorm PowerMethod BoydInterface

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter15BoydBridges` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open Filter Function Set

open scoped BigOperators Topology

/-- The literal initial normalization `x := x₀ / ‖x₀‖_p` in Algorithm
15.1. -/
noncomputable def realLpNormalizedStart {n : ℕ} (p : ℝ)
    (x0 : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (realVecLpNorm p x0)⁻¹ * x0 i

/-- A strictly positive raw start remains strictly positive after Algorithm
15.1's initial normalization. -/
theorem realLpNormalizedStart_pos {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp : 1 ≤ p) (x0 : Fin n → ℝ) (hx0 : ∀ i, 0 < x0 i) :
    ∀ i, 0 < realLpNormalizedStart p x0 i := by
  have hx0ne : x0 ≠ 0 := by
    intro hzero
    let i0 : Fin n := ⟨0, hn⟩
    have hi := congrFun hzero i0
    exact (ne_of_gt (hx0 i0)) (by simpa using hi)
  have hnorm : 0 < realVecLpNorm p x0 := realVecLpNorm_pos hp hx0ne
  intro i
  exact mul_pos (inv_pos.mpr hnorm) (hx0 i)

/-- The normalized positive start has exact unit `p`-norm. -/
theorem realLpNormalizedStart_norm_eq_one {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp : 1 ≤ p) (x0 : Fin n → ℝ) (hx0 : ∀ i, 0 < x0 i) :
    realVecLpNorm p (realLpNormalizedStart p x0) = 1 := by
  have hx0ne : x0 ≠ 0 := by
    intro hzero
    let i0 : Fin n := ⟨0, hn⟩
    have hi := congrFun hzero i0
    exact (ne_of_gt (hx0 i0)) (by simpa using hi)
  have hnorm : 0 < realVecLpNorm p x0 := realVecLpNorm_pos hp hx0ne
  rw [show realLpNormalizedStart p x0 =
      (fun i => (realVecLpNorm p x0)⁻¹ * x0 i) from rfl,
    realVecLpNorm_smul_real hp]
  rw [abs_of_pos (inv_pos.mpr hnorm)]
  exact inv_mul_cancel₀ (ne_of_gt hnorm)

end Ch15
end NumStability
