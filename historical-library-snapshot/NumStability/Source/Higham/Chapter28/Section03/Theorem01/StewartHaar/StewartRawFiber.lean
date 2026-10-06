import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.Matrix
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Probability.Haar.HomogeneousSpaceUniqueness
import NumStability.Analysis.TestMatrices.Gaussian.GaussianDirection
import NumStability.Analysis.TestMatrices.Gaussian.GaussianOrthogonal
import NumStability.Analysis.TestMatrices.Orthogonal.OrthogonalCoordinates
import NumStability.Analysis.TestMatrices.Orthogonal.OrthogonalFibers
import NumStability.Analysis.TestMatrices.Orthogonal.OrthogonalHaar
import NumStability.Analysis.TestMatrices.Orthogonal.OrthogonalSphere

/-!
# Chapter28 Section03 Theorem01 StewartHaar StewartRawFiber

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28StewartRawFiber` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open MeasureTheory ProbabilityTheory

open scoped RealInnerProductSpace

noncomputable def stewartRawFiberProducer (d : ℕ)
    (p : RealOrthogonalGroup d × (Fin (d + 1) → ℝ)) :
    RealOrthogonalGroup (d + 1) :=
  orthogonalTailEmbedding d p.1 * stewartFirstSection d p.2

noncomputable def stewartRawFiberMeasure (d : ℕ) :
    Measure (RealOrthogonalGroup (d + 1)) :=
  Measure.map (stewartRawFiberProducer d)
    ((normalizedOrthogonalHaar d).prod
      (standardGaussianVectorMeasure (d + 1)))

theorem orthogonalFirstRow_stewartFirstSection_of_ne_zero (d : ℕ)
    (x : Fin (d + 1) → ℝ) (hx : x ≠ 0) :
    orthogonalFirstRow d (stewartFirstSection d x) =
      gaussianUnitDirection d x := by
  apply Subtype.ext
  apply WithLp.ofLp_injective
  funext j
  change (stewartFirstSection d x :
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) 0 j =
    WithLp.ofLp ((gaussianUnitDirection d x : OrthogonalSphere (d + 1)) :
      EuclideanSpace ℝ (Fin (d + 1))) j
  rw [stewartFirstSection_firstRow_of_ne_zero d x hx j]
  simp [gaussianUnitDirection, gaussianUnitDirectionValue, hx]

theorem orthogonalFirstRow_stewartRawFiberProducer_of_ne_zero (d : ℕ)
    (p : RealOrthogonalGroup d × (Fin (d + 1) → ℝ))
    (hp : p.2 ≠ 0) :
    orthogonalFirstRow d (stewartRawFiberProducer d p) =
      gaussianUnitDirection d p.2 := by
  rw [stewartRawFiberProducer,
    orthogonalFirstRow_mul_of_fixesFirstRow _ _
      (orthogonalTailEmbedding_fixesFirstRow d p.1),
    orthogonalFirstRow_stewartFirstSection_of_ne_zero d p.2 hp]

end NumStability
