import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
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
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.AsymptoticFamilies
import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ForwardErrorEndpoint

/-!
# Chapter14 Problem05 InverseBasedSolve AsymptoticFamilies

Canonical destination for material split out of
`NumStability.Algorithms.Ch14AsymptoticFamilies` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open Filter Asymptotics
open scoped BigOperators Topology
open NumStability

namespace NumStability

namespace Ch14Ext

/-- The varying right-inverse remainder from Problem 14.5. -/
noncomputable def ch14ext_problem14_5_right_familyRemainder
    {ι : Type*} {l : Filter ι} (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (F : Ch14Problem145RightFamily ι l n A) (i : Fin n) (t : ι) : ℝ :=
  (F.model t).u ^ 2 *
    (ch14ext_gammaQuadraticCoefficient (F.model t) (n + 1) *
        matMulVec n (absMatrix n A_inv)
          (matMulVec n (absMatrix n A)
            (matMulVec n (absMatrix n A_inv) (absVec n b))) i +
      ch14ext_gammaUnitCoefficient (F.model t) (n + 1) *
        matMulVec n (absMatrix n A_inv)
          (matMulVec n (absMatrix n A)
            (matMulVec n
              (ch14ext_rightResidualEnvelopeRemainder n A A_inv (F.inverse t))
              (absVec n b))) i)

noncomputable def ch14ext_problem14_5_left_familyRemainder
    {ι : Type*} {l : Filter ι} (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (F : Ch14Problem145LeftFamily ι l n A) (i : Fin n) (t : ι) : ℝ :=
  (F.model t).u ^ 2 *
    (ch14ext_gammaQuadraticCoefficient (F.model t) (n + 1) *
        matMulVec n (absMatrix n A_inv)
          (matMulVec n (absMatrix n A) (absVec n x)) i +
      ch14ext_gammaUnitCoefficient (F.model t) (n + 1) *
        matMulVec n
          (ch14ext_leftResidualEnvelopeRemainder n A A_inv (F.inverse t))
          (matMulVec n (absMatrix n A) (absVec n x)) i)

end Ch14Ext
end NumStability
