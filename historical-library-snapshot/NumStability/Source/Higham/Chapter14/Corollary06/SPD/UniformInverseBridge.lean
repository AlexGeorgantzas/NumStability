import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.FirstOrder.MatrixFamilies.AsymptoticFamilies
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter07.Corollary06.LinearSystemsConditioning.Results
import NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.InverseBoundsPrelude
import NumStability.Source.Higham.Chapter09.Problems
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter09.Section03
import NumStability.Source.Higham.Chapter09.Section04
import NumStability.Source.Higham.Chapter09.Section05
import NumStability.Source.Higham.Chapter09.Section06
import NumStability.Source.Higham.Chapter09.Section08
import NumStability.Source.Higham.Chapter09.Section10
import NumStability.Source.Higham.Chapter09.Section11
import NumStability.Source.Higham.Chapter10.Equation07.AbsoluteFactorNorm.Endpoints
import NumStability.Source.Higham.Chapter14.Problem15

/-!
# Chapter14 Corollary06 SPD UniformInverseBridge

Canonical destination for material split out of
`NumStability.Algorithms.Ch14Cor146UniformInverseBridge` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open Filter Asymptotics
open scoped BigOperators Topology
open NumStability

namespace NumStability

namespace Ch14Ext

/-- Continuity of the finite-dimensional matrix inverse turns convergence to
a nonsingular fixed matrix into entrywise `O(1)` control of the repository's
canonical inverse. -/
theorem ch14ext_nonsingInv_family_isBigOOne_of_tendsto
    {I : Type*} {l : Filter I} {n : Nat}
    {A : Fin n -> Fin n -> Real}
    {B : I -> Fin n -> Fin n -> Real}
    (hB : Tendsto B l (nhds A))
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0) :
    MatrixFamilyIsBigOOne l (fun t => nonsingInv n (B t)) := by
  have hBmat : Tendsto
      (fun t => (B t : Matrix (Fin n) (Fin n) Real)) l
      (nhds (A : Matrix (Fin n) (Fin n) Real)) := hB
  have hinvMat :=
    (continuousAt_matrix_inv (A : Matrix (Fin n) (Fin n) Real)
      (by
        simpa using
          (NormedRing.inverse_continuousAt
            (Units.mk0
              (Matrix.det (A : Matrix (Fin n) (Fin n) Real)) hdet)))).tendsto.comp hBmat
  have hinv : Tendsto (fun t => nonsingInv n (B t)) l
      (nhds (nonsingInv n A)) := by
    simpa only [nonsingInv] using hinvMat
  intro i j
  exact ((tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp hinv) i)) j).isBigO_one Real

end Ch14Ext
end NumStability
