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
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Instances.Matrix
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.Incidence.GinibrePlaneIncidence

/-!
# Chapter28 Section02 RealGinibre InvariantPlanes GinibrePlaneChart

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28GinibrePlaneChart` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

open scoped BigOperators

/-- The blocks of a matrix other than its upper-right `m × 2` block. -/
abbrev GinibrePlaneChartNuisance (m : ℕ) :=
  ((RSqMat m × Matrix (Fin 2) (Fin m) ℝ) × RSqMat 2)

/-- Square affine-chart coordinates `(((B,W),E),Y)`. -/
abbrev GinibrePlaneChartCoordinates (m : ℕ) :=
  GinibrePlaneChartNuisance m × Matrix (Fin m) (Fin 2) ℝ

/-- The action induced on the graph of `Y`. -/
def ginibrePlaneChartAction {m : ℕ}
    (q : GinibrePlaneChartCoordinates m) : RSqMat 2 :=
  q.1.2 + q.1.1.2 * q.2

/-- The quotient block in graph-adapted coordinates. -/
def ginibrePlaneChartDeflatedBlock {m : ℕ}
    (q : GinibrePlaneChartCoordinates m) : RSqMat m :=
  q.1.1.1 - q.2 * q.1.1.2

/-- The upper-right block forced by invariance of the graph. -/
def ginibrePlaneChartTopRight {m : ℕ}
    (q : GinibrePlaneChartCoordinates m) :
    Matrix (Fin m) (Fin 2) ℝ :=
  q.2 * ginibrePlaneChartAction q - q.1.1.1 * q.2

/-- The square incidence chart, in block-coordinate order. -/
def ginibrePlaneChart {m : ℕ}
    (q : GinibrePlaneChartCoordinates m) :
    GinibrePlaneChartCoordinates m :=
  (q.1, ginibrePlaneChartTopRight q)

/-- Assemble block coordinates into the corresponding square matrix. -/
def ginibrePlaneChartMatrix {m : ℕ}
    (p : GinibrePlaneChartCoordinates m) :
    Matrix (Fin m ⊕ Fin 2) (Fin m ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks p.1.1.1 p.2 p.1.1.2 p.1.2

/-- Reinterpret chart coordinates as the invariant-plane coordinates whose
distinguished block is the represented action `C`. -/
def ginibrePlaneChartIncidenceCoordinates {m : ℕ}
    (q : GinibrePlaneChartCoordinates m) :
    GinibrePlaneIncidenceCoordinates m :=
  (((q.1.1.1, q.1.1.2), ginibrePlaneChartAction q), q.2)

theorem ginibrePlaneChartMatrix_chart_eq_incidence {m : ℕ}
    (q : GinibrePlaneChartCoordinates m) :
    ginibrePlaneChartMatrix (ginibrePlaneChart q) =
      ginibrePlaneIncidenceMatrix
        (ginibrePlaneChartIncidenceCoordinates q) := by
  ext (i | i) (j | j) <;>
    simp [ginibrePlaneChartMatrix, ginibrePlaneChart,
      ginibrePlaneChartTopRight, ginibrePlaneChartAction,
      ginibrePlaneChartIncidenceCoordinates, ginibrePlaneIncidenceMatrix,
      ginibrePlaneTopRight, ginibrePlaneBottomRight, Matrix.mul_apply]

/-- Consequently the chart matrix has the exact invariant-plane
characteristic-polynomial factorization. -/
theorem ginibrePlaneChartMatrix_charpoly_factor {m : ℕ}
    (q : GinibrePlaneChartCoordinates m) :
    (ginibrePlaneChartMatrix (ginibrePlaneChart q)).charpoly =
      (ginibrePlaneChartDeflatedBlock q).charpoly *
        (ginibrePlaneChartAction q).charpoly := by
  rw [ginibrePlaneChartMatrix_chart_eq_incidence,
    ginibrePlaneIncidenceMatrix_charpoly_factor]
  rfl

/-- The nontrivial diagonal block of the chart derivative. -/
def ginibrePlaneSylvesterLinearMap {m : ℕ}
    (q : GinibrePlaneChartCoordinates m) :
    Matrix (Fin m) (Fin 2) ℝ →ₗ[ℝ] Matrix (Fin m) (Fin 2) ℝ where
  toFun X :=
    X * ginibrePlaneChartAction q -
      ginibrePlaneChartDeflatedBlock q * X
  map_add' X Z := by
    simp only [Matrix.add_mul, Matrix.mul_add, sub_eq_add_neg,
      neg_add_rev, add_assoc]
    abel
  map_smul' c X := by
    simp only [RingHom.id_apply, Matrix.smul_mul, Matrix.mul_smul, smul_sub]

/-- Dependence of the forced block on variations of the nuisance blocks. -/
def ginibrePlaneChartNuisanceDerivative {m : ℕ}
    (q : GinibrePlaneChartCoordinates m) :
    GinibrePlaneChartNuisance m →ₗ[ℝ] Matrix (Fin m) (Fin 2) ℝ where
  toFun dq :=
    q.2 * dq.2 + q.2 * dq.1.2 * q.2 - dq.1.1 * q.2
  map_add' p r := by
    simp only [Prod.fst_add, Prod.snd_add, Matrix.mul_add,
      Matrix.add_mul, sub_eq_add_neg, neg_add_rev]
    abel
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply,
      Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    module

end NumStability

end
