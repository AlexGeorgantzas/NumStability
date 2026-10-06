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

/-!
# Chapter28 Section02 RealGinibre Incidence GinibrePlaneIncidence

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28GinibrePlaneIncidence` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

open scoped BigOperators

/-- Coordinates `(((B,W),C),Y)` for a matrix with an invariant two-plane.
Here `Y` is the graph coordinate, `C` is the represented action on the
plane, and `B,W` are free nuisance blocks. -/
abbrev GinibrePlaneIncidenceCoordinates (m : ℕ) :=
  (((RSqMat m × Matrix (Fin 2) (Fin m) ℝ) × RSqMat 2) ×
    Matrix (Fin m) (Fin 2) ℝ)

/-- The quotient/deflated block after the invariant-plane shear. -/
def ginibrePlaneDeflatedBlock {m : ℕ}
    (q : GinibrePlaneIncidenceCoordinates m) : RSqMat m :=
  q.1.1.1 - q.2 * q.1.1.2

/-- The upper-right block forced by invariance of the graph of `Y`. -/
def ginibrePlaneTopRight {m : ℕ}
    (q : GinibrePlaneIncidenceCoordinates m) :
    Matrix (Fin m) (Fin 2) ℝ :=
  q.2 * q.1.2 - q.1.1.1 * q.2

/-- The lower-right block forced by invariance of the graph of `Y`. -/
def ginibrePlaneBottomRight {m : ℕ}
    (q : GinibrePlaneIncidenceCoordinates m) : RSqMat 2 :=
  q.1.2 - q.1.1.2 * q.2

/-- The full block matrix represented by invariant-plane coordinates. -/
def ginibrePlaneIncidenceMatrix {m : ℕ}
    (q : GinibrePlaneIncidenceCoordinates m) :
    Matrix (Fin m ⊕ Fin 2) (Fin m ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks q.1.1.1 (ginibrePlaneTopRight q)
    q.1.1.2 (ginibrePlaneBottomRight q)

/-- The graph-basis shear `[I Y; 0 I]`. -/
def ginibrePlaneShear {m : ℕ}
    (q : GinibrePlaneIncidenceCoordinates m) :
    Matrix (Fin m ⊕ Fin 2) (Fin m ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks 1 q.2 0 1

/-- The inverse graph-basis shear `[I -Y; 0 I]`. -/
def ginibrePlaneShearInv {m : ℕ}
    (q : GinibrePlaneIncidenceCoordinates m) :
    Matrix (Fin m ⊕ Fin 2) (Fin m ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks 1 (-q.2) 0 1

/-- The block-triangular matrix obtained in graph coordinates. -/
def ginibrePlaneTriangular {m : ℕ}
    (q : GinibrePlaneIncidenceCoordinates m) :
    Matrix (Fin m ⊕ Fin 2) (Fin m ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks (ginibrePlaneDeflatedBlock q) 0 q.1.1.2 q.1.2

theorem ginibrePlaneShear_mul_inv {m : ℕ}
    (q : GinibrePlaneIncidenceCoordinates m) :
    ginibrePlaneShear q * ginibrePlaneShearInv q = 1 := by
  simp [ginibrePlaneShear, ginibrePlaneShearInv,
    Matrix.fromBlocks_multiply]

theorem ginibrePlaneShear_inv_mul {m : ℕ}
    (q : GinibrePlaneIncidenceCoordinates m) :
    ginibrePlaneShearInv q * ginibrePlaneShear q = 1 := by
  simp [ginibrePlaneShear, ginibrePlaneShearInv,
    Matrix.fromBlocks_multiply]

/-- Exact graph-shear triangularization of the invariant-plane incidence
matrix. -/
theorem ginibrePlane_inv_mul_matrix_mul_shear {m : ℕ}
    (q : GinibrePlaneIncidenceCoordinates m) :
    ginibrePlaneShearInv q * ginibrePlaneIncidenceMatrix q *
        ginibrePlaneShear q =
      ginibrePlaneTriangular q := by
  simp [ginibrePlaneShear, ginibrePlaneShearInv,
    ginibrePlaneIncidenceMatrix, ginibrePlaneTriangular,
    ginibrePlaneTopRight, ginibrePlaneBottomRight,
    ginibrePlaneDeflatedBlock, Matrix.fromBlocks_multiply]
  constructor
  · trivial
  · change
      (q.1.1.1 - q.2 * q.1.1.2) * q.2 +
          (q.2 * q.1.2 - q.1.1.1 * q.2 -
            q.2 * (q.1.2 - q.1.1.2 * q.2)) = 0
    rw [Matrix.sub_mul, Matrix.mul_sub]
    simp only [Matrix.mul_assoc]
    abel

/-- The invariant-plane characteristic polynomial factors into the
deflated block and the distinguished real `2 × 2` block. -/
theorem ginibrePlaneIncidenceMatrix_charpoly_factor {m : ℕ}
    (q : GinibrePlaneIncidenceCoordinates m) :
    (ginibrePlaneIncidenceMatrix q).charpoly =
      (ginibrePlaneDeflatedBlock q).charpoly * q.1.2.charpoly := by
  have hcomm := Matrix.charpoly_mul_comm
    (ginibrePlaneShearInv q * ginibrePlaneIncidenceMatrix q)
    (ginibrePlaneShear q)
  rw [ginibrePlane_inv_mul_matrix_mul_shear] at hcomm
  have hright : ginibrePlaneShear q *
      (ginibrePlaneShearInv q * ginibrePlaneIncidenceMatrix q) =
        ginibrePlaneIncidenceMatrix q := by
    rw [← Matrix.mul_assoc, ginibrePlaneShear_mul_inv, one_mul]
  rw [hright] at hcomm
  rw [← hcomm]
  unfold ginibrePlaneTriangular
  exact Matrix.charpoly_fromBlocks_zero₁₂ _ _ _

/-- The graph basis whose columns are `[Y;I₂]`. -/
def ginibrePlaneGraphBasis {m : ℕ}
    (q : GinibrePlaneIncidenceCoordinates m) :
    Matrix (Fin m ⊕ Fin 2) (Fin 2) ℝ
  | Sum.inl i, j => q.2 i j
  | Sum.inr i, j => (1 : RSqMat 2) i j

/-- The columns of `[Y;I₂]` span an invariant plane, and the represented
action on that plane is exactly `C`. -/
theorem ginibrePlaneIncidenceMatrix_mul_graphBasis {m : ℕ}
    (q : GinibrePlaneIncidenceCoordinates m) :
    ginibrePlaneIncidenceMatrix q * ginibrePlaneGraphBasis q =
      ginibrePlaneGraphBasis q * q.1.2 := by
  ext (i | i) j
  · fin_cases j <;>
      simp [ginibrePlaneIncidenceMatrix, ginibrePlaneTopRight,
        ginibrePlaneGraphBasis, Matrix.mul_apply]
  · fin_cases i <;> fin_cases j <;>
      simp [ginibrePlaneIncidenceMatrix, ginibrePlaneBottomRight,
        ginibrePlaneGraphBasis, Matrix.mul_apply]

end NumStability

end
