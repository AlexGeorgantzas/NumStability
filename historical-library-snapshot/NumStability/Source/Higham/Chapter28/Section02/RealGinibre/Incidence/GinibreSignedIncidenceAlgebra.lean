import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Sym.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.Incidence.GinibreIncidence
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.InvariantPlanes.GinibreOrthogonalFiber

/-!
# Chapter28 Section02 RealGinibre Incidence GinibreSignedIncidenceAlgebra

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28GinibreSignedIncidenceAlgebra` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

/-- At an incidence point with distinguished eigenvalue `u`, evaluating the
full shifted determinant at an external parameter `x` contributes the scalar
factor `u - x` times the shifted determinant of the deflated block. -/
theorem det_ginibreIncidenceFull_sub_externalShift
    {m : ℕ} (q : GinibreIncidenceCoordinates m) (x : ℝ) :
    ((show RSqMat (m + 1) from
        ginibreCoordinatesFinMatrix (ginibreIncidenceChart q)) -
        x • (1 : RSqMat (m + 1))).det =
      (ginibreIncidenceEigenvalue q - x) *
        (ginibreIncidenceDeflatedBlock q -
          x • (1 : RSqMat m)).det := by
  have hchar :
      (Matrix.of
        (ginibreCoordinatesFinMatrix (ginibreIncidenceChart q))).charpoly =
        (ginibreIncidenceDeflatedBlock q).charpoly *
          (Polynomial.X -
            Polynomial.C (ginibreIncidenceEigenvalue q)) := by
    calc
      (Matrix.of
        (ginibreCoordinatesFinMatrix (ginibreIncidenceChart q))).charpoly =
          (ginibreCoordinatesMatrix (ginibreIncidenceChart q)).charpoly :=
        ginibreCoordinatesFinMatrix_charpoly (ginibreIncidenceChart q)
      _ = (ginibreIncidenceMatrix q).charpoly := by
        rw [ginibreCoordinatesMatrix_chart]
      _ = _ := ginibreIncidenceMatrix_charpoly_factor q
  rw [det_sub_smul_one_eq_neg_one_pow_mul_charpoly_eval,
    det_sub_smul_one_eq_neg_one_pow_mul_charpoly_eval]
  rw [hchar, Polynomial.eval_mul]
  have hlinear :
      (Polynomial.X - Polynomial.C (ginibreIncidenceEigenvalue q)).eval x =
        x - ginibreIncidenceEigenvalue q := by
    simp
  rw [hlinear]
  have hblock :
      (Matrix.of (ginibreIncidenceDeflatedBlock q)).charpoly =
        (ginibreIncidenceDeflatedBlock q).charpoly := by
    rfl
  rw [hblock]
  rw [pow_succ]
  ring

end NumStability

end
