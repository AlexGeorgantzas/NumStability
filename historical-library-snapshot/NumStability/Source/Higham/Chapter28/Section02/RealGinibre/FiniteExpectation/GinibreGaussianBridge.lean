import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Sym.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Instances.Matrix
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.RealGinibre.GinibreRoots
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.Incidence.GinibreIncidence

/-!
# Chapter28 Section02 RealGinibre FiniteExpectation GinibreGaussianBridge

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28GinibreGaussianBridge` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal BigOperators

/-- Extract the four affine blocks from a matrix whose last row and column
are distinguished by `ginibreBlockIndexEquiv`. -/
def ginibreFinMatrixCoordinates {n : ℕ}
    (A : GinibreRawMatrix (n + 1)) : GinibreIncidenceCoordinates n :=
  let M : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
    Matrix.reindex (ginibreBlockIndexEquiv n).symm
      (ginibreBlockIndexEquiv n).symm (Matrix.of A)
  (((fun i j => M (Sum.inl i) (Sum.inl j),
      fun j => M (Sum.inr ()) (Sum.inl j)),
    M (Sum.inr ()) (Sum.inr ())),
    fun i => M (Sum.inl i) (Sum.inr ()))

/-- Reassembling affine matrix coordinates and extracting them again are
inverse linear operations. -/
noncomputable def ginibreCoordinatesLinearEquiv (n : ℕ) :
    GinibreIncidenceCoordinates n ≃ₗ[ℝ] GinibreRawMatrix (n + 1) where
  toFun := ginibreCoordinatesFinMatrix
  invFun := ginibreFinMatrixCoordinates
  left_inv p := by
    rcases p with ⟨⟨⟨B, w⟩, b⟩, v⟩
    simp [ginibreFinMatrixCoordinates, ginibreCoordinatesFinMatrix,
      ginibreCoordinatesMatrix, Matrix.reindex]
  right_inv A := by
    ext i j
    let ii := (ginibreBlockIndexEquiv n).symm i
    let jj := (ginibreBlockIndexEquiv n).symm j
    have hi : ginibreBlockIndexEquiv n ii = i :=
      (ginibreBlockIndexEquiv n).apply_symm_apply i
    have hj : ginibreBlockIndexEquiv n jj = j :=
      (ginibreBlockIndexEquiv n).apply_symm_apply j
    change Matrix.fromBlocks _ _ _ _ ii jj = A i j
    rcases ii with ii | ii <;> rcases jj with jj | jj
    all_goals simp [ginibreFinMatrixCoordinates, Matrix.reindex] at hi hj ⊢
    all_goals simp_all
  map_add' p q := by
    ext i j
    change ginibreCoordinatesMatrix (p + q)
        ((ginibreBlockIndexEquiv n).symm i)
        ((ginibreBlockIndexEquiv n).symm j) =
      ginibreCoordinatesMatrix p ((ginibreBlockIndexEquiv n).symm i)
          ((ginibreBlockIndexEquiv n).symm j) +
        ginibreCoordinatesMatrix q ((ginibreBlockIndexEquiv n).symm i)
          ((ginibreBlockIndexEquiv n).symm j)
    generalize (ginibreBlockIndexEquiv n).symm i = ii
    generalize (ginibreBlockIndexEquiv n).symm j = jj
    rcases ii with ii | ii <;> rcases jj with jj | jj
    all_goals simp [ginibreCoordinatesMatrix]
  map_smul' c p := by
    ext i j
    change ginibreCoordinatesMatrix (c • p)
        ((ginibreBlockIndexEquiv n).symm i)
        ((ginibreBlockIndexEquiv n).symm j) =
      c * ginibreCoordinatesMatrix p ((ginibreBlockIndexEquiv n).symm i)
        ((ginibreBlockIndexEquiv n).symm j)
    generalize (ginibreBlockIndexEquiv n).symm i = ii
    generalize (ginibreBlockIndexEquiv n).symm j = jj
    rcases ii with ii | ii <;> rcases jj with jj | jj
    all_goals simp [ginibreCoordinatesMatrix]

/-- The affine block assembly equivalence, with its automatic
finite-dimensional continuity. -/
noncomputable def ginibreCoordinatesContinuousLinearEquiv (n : ℕ) :
    GinibreIncidenceCoordinates n ≃L[ℝ] GinibreRawMatrix (n + 1) :=
  (ginibreCoordinatesLinearEquiv n).toContinuousLinearEquiv

/-- Standard matrix Lebesgue measure pulled back to affine incidence
coordinates. -/
noncomputable def ginibreIncidenceLebesgueMeasure (n : ℕ) :
    Measure (GinibreIncidenceCoordinates n) :=
  Measure.map (ginibreCoordinatesContinuousLinearEquiv n).symm
    (volume : Measure (GinibreRawMatrix (n + 1)))

end NumStability

end
