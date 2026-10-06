import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.MatrixPowers.ComputedIteration.Model
import NumStability.Algorithms.PolynomialEvaluation.MatrixNorms
import NumStability.Analysis.Conditioning.DistanceToSingularity
import NumStability.Analysis.FunctionalCalculus.Resolvent.Analyticity
import NumStability.Analysis.FunctionalCalculus.Resolvent.DunfordResidue
import NumStability.Analysis.LinearOperators.MatrixPowers.BaiDemmelGu.DistanceToInstability
import NumStability.Analysis.LinearOperators.MatrixPowers.BaiDemmelGu.StabilityRadius
import NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.Complex
import NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.Real
import NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.Complex
import NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.RealDiagonal
import NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.RealJordan
import NumStability.Analysis.LinearOperators.MatrixPowers.Kreiss.ResolventBound
import NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarAlgebra
import NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarAnalysis
import NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarArcLength.Variation
import NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.ProjectionIntegral
import NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.Rational
import NumStability.Analysis.LinearOperators.Pseudospectra.Perturbation.ConvergenceCriterion
import NumStability.Analysis.LinearOperators.Pseudospectra.Perturbation.Definitions
import NumStability.Analysis.LinearOperators.Pseudospectra.PowerBounds.Contour
import NumStability.Analysis.LinearOperators.Pseudospectra.Resolvent.LowerBounds
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Basic
import NumStability.Analysis.MatrixNorms.SpectralRadius
import NumStability.Analysis.Rounding
import NumStability.Analysis.SingularValues.Basic
import NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.Equations04And05.RealDiagonal
import NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.Equations04And05.RealJordan
import NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.BaiDemmelGu
import NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.Kreiss
import NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.SpijkerKreiss
import NumStability.Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Equations08To14.ComplexSimilarity
import NumStability.Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Equations08To14.ComputedIteration
import NumStability.Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Equations08To14.PowerBound
import NumStability.Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Theorems01And02.ComplexJordan
import NumStability.Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Theorems01And02.PseudospectralCriterion
import NumStability.Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Theorems01And02.PseudospectralPackaging
import NumStability.Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Theorems01And02.RealCases
import NumStability.Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Theorems01And02.RealJordan

/-!
# Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.SpijkerKreissUnconditional.Bounds

R07 canonical `source` leaf. Exact Higham Chapter 18 unconditional Kreiss correspondence aliases (`NumStability.higham18_kreiss_two_sided_proved`, `NumStability.higham18_kreiss_upper_proved`); the dedicated source-strength family keeps them separate from the reusable finite-dimensional bounds.

Whole declaration commands are copied byte-for-byte from `NumStability.Analysis.MatrixPowersSpijkerClosure`. Declaration names, visibility, namespaces, signatures, and proofs are unchanged; authored-private names are re-mangled only by their reviewed destination module.
-/


namespace NumStability

open scoped Real Topology ComplexOrder
open Complex Metric Set MeasureTheory

noncomputable section

/-- Unconditional literal upper endpoint in Higham's notation. -/
theorem higham18_kreiss_upper_proved
    {n : ℕ} [Nonempty (Fin n)]
    (A : CStarMatrix (Fin n) (Fin n) ℂ)
    (hres : ∀ z : ℂ, 1 < ‖z‖ → z ∈ resolventSet ℂ A)
    (hbdd : BddAbove (kreissResolventValueSet A)) :
    matrixPowerNormSup A ≤
      Real.exp 1 * n * kreissConstant A :=
  higham18_kreiss_upper_of_spijker
    (spijkerArcLengthBound_proved n) A hres hbdd

/-- Unconditional two-sided finite-dimensional Kreiss theorem, closing the
Chapter 18 Spijker dependency. -/
theorem higham18_kreiss_two_sided_proved
    {n : ℕ} [Nonempty (Fin n)]
    (A : CStarMatrix (Fin n) (Fin n) ℂ)
    (hres : ∀ z : ℂ, 1 < ‖z‖ → z ∈ resolventSet ℂ A)
    (hbdd : BddAbove (kreissResolventValueSet A)) :
    kreissConstant A ≤ matrixPowerNormSup A ∧
      matrixPowerNormSup A ≤ Real.exp 1 * n * kreissConstant A :=
  higham18_kreiss_two_sided_of_spijker
    (spijkerArcLengthBound_proved n) A hres hbdd

end
end NumStability
