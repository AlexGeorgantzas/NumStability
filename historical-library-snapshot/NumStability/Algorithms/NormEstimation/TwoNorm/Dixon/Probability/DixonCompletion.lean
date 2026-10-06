import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.Algebra.DixonCompletion
import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.Probability.DixonProbability
import NumStability.Analysis.TestMatrices.Orthogonal.OrthogonalCoordinates
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic
import NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic

/-!
# NumStability Algorithms NormEstimation TwoNorm Dixon Probability DixonCompletion

Canonical destination for material split out of
`NumStability.Algorithms.Ch15DixonClosure` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open MeasureTheory Set

open scoped BigOperators Matrix MatrixOrder RealInnerProductSpace

set_option maxHeartbeats 800000

theorem ch15Closure_ch15SphereInner_unitSphereOfFiniteVec (d : ℕ)
    (v : Fin (d + 1) → ℝ) (hv : (∑ i, v i ^ 2) = 1)
    (x : OrthogonalSphere (d + 1)) :
    ch15SphereInner d (ch15Closure_unitSphereOfFiniteVec d v hv) x =
      ∑ i : Fin (d + 1), v i *
        WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1))) i := by
  have hscalar (a b : ℝ) : @inner ℝ ℝ _ a b = a * b := by
    calc
      @inner ℝ ℝ _ a b = @inner ℝ ℝ _ (a • (1 : ℝ)) (b • (1 : ℝ)) := by
        congr <;> simp
      _ = a * b * @inner ℝ ℝ _ (1 : ℝ) 1 := by
        rw [real_inner_smul_left, real_inner_smul_right]
        ring
      _ = a * b := by simp
  simp only [ch15SphereInner, ch15Closure_unitSphereOfFiniteVec, PiLp.inner_apply]
  simp_rw [hscalar]

end NumStability
