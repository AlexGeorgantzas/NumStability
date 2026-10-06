import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Sym.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Instances.Matrix
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Probability.Gaussian.AbsoluteMoment
import NumStability.Analysis.Probability.Haar.HomogeneousSpaceUniqueness
import NumStability.Analysis.TestMatrices.RealGinibre.GinibreRoots
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.Incidence.GinibreIncidence
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.Incidence.GinibreSignedIncidenceAlgebra
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.InvariantPlanes.GinibreOrthogonalFiber
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.RootMeasurability.GinibreRoots
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.SignedIncidence.GinibreSignedRank

/-!
# Chapter28 Section02 RealGinibre SignedIncidence GinibreSignedIncidence

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28GinibreSignedIncidence` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

open Matrix MeasureTheory ProbabilityTheory Set Filter

open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.Frobenius

/-- The signed deflated determinant differs from the incidence derivative
determinant only by the dimension parity. -/
theorem det_ginibreIncidenceDeflatedShift_eq_negOnePow_mul_derivativeDet
    {n : ℕ} (q : GinibreIncidenceCoordinates n) :
    (ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat n)).det =
      (-1 : ℝ) ^ n * (ginibreIncidenceDerivativeLinearMap q).det := by
  rw [ginibreIncidenceDerivativeLinearMap_det]
  have hneg : ginibreIncidenceDeflatedBlock q -
      ginibreIncidenceEigenvalue q • (1 : RSqMat n) =
      -(ginibreIncidenceTangentMatrix q) := by
    ext i j
    simp [ginibreIncidenceTangentMatrix]
  rw [hneg, Matrix.det_neg, Fintype.card_fin]

/-- Characteristic-polynomial form of the alternating number of roots below
the marked scalar. -/
def ginibreAlternatingBelowCharpoly (P : Polynomial ℝ) (x : ℝ) : ℝ :=
  ginibreAlternatingCount ((P.roots.filter fun z => z < x).card)

theorem ginibreAlternatingBelowCharpoly_charpoly (n : ℕ)
    (A : RSqMat n) (x : ℝ) :
    ginibreAlternatingBelowCharpoly (Matrix.charpoly (Matrix.of A)) x =
      ginibreAlternatingCount (realEigenvalueBelowCount (A, x)) := rfl

/-- Polynomial weight which simultaneously imposes `u < x` and evaluates
the full shifted determinant after the second incidence factorization. -/
def ginibreTruncatedExternalShiftWeight (m : ℕ) (x : ℝ)
    (P : Polynomial ℝ) (u : ℝ) : ℝ :=
  if u < x then (u - x) * ((-1 : ℝ) ^ m * P.eval x) else 0

theorem ginibreTruncatedExternalShiftWeight_charpoly
    (m : ℕ) (x : ℝ) (A : RSqMat m) (u : ℝ) :
    ginibreTruncatedExternalShiftWeight m x
        (Matrix.charpoly (Matrix.of A)) u =
      if u < x then
        (u - x) * (A - x • (1 : RSqMat m)).det else 0 := by
  unfold ginibreTruncatedExternalShiftWeight
  by_cases hux : u < x
  · rw [if_pos hux, if_pos hux,
      det_sub_smul_one_eq_neg_one_pow_mul_charpoly_eval]
  · rw [if_neg hux, if_neg hux]

theorem ginibreTruncatedExternalShiftWeight_incidence
    {m : ℕ} (q : GinibreIncidenceCoordinates m) (x : ℝ) :
    ginibreTruncatedExternalShiftWeight m x
        (Matrix.charpoly (Matrix.of (ginibreIncidenceDeflatedBlock q)))
        (ginibreIncidenceEigenvalue q) =
      if ginibreIncidenceEigenvalue q < x then
        ((show RSqMat (m + 1) from
          ginibreCoordinatesFinMatrix (ginibreIncidenceChart q)) -
            x • (1 : RSqMat (m + 1))).det
      else 0 := by
  rw [ginibreTruncatedExternalShiftWeight_charpoly]
  by_cases hux : ginibreIncidenceEigenvalue q < x
  · rw [if_pos hux, if_pos hux,
      det_ginibreIncidenceFull_sub_externalShift]
  · rw [if_neg hux, if_neg hux]

end NumStability

end
