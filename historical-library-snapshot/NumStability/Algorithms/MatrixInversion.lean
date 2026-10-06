import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatrixInversion.LUFactors.ErrorAnalysis.MatrixInversion
import NumStability.Algorithms.MatrixInversion.LUFactors.Methods.MatrixInversion
import NumStability.Algorithms.MatrixInversion.Residuals.MatrixInversion
import NumStability.Algorithms.MatrixInversion.Triangular.ErrorAnalysis.MatrixInversion
import NumStability.Algorithms.MatrixInversion.Triangular.Specifications.MatrixInversion
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.MatrixProducts.Contracts.MatrixInversion
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter14.Equation34.DeterminantFromLU.MatrixInversion
import NumStability.Source.Higham.Chapter14.Equation35.HymanBlockFactorization.MatrixInversion
import NumStability.Source.Higham.Chapter14.Equation36.HymanDeterminant.MatrixInversion
import NumStability.Source.Higham.Chapter14.Problem03.ResidualComparison.MatrixInversion
import NumStability.Source.Higham.Chapter14.Problem04.ResidualCounterexample.MatrixInversion
import NumStability.Source.Higham.Chapter14.Problem05.InverseBasedSolve.MatrixInversion
import NumStability.Source.Higham.Chapter14.Problem07.OnesVector.MatrixInversion
import NumStability.Source.Higham.Chapter14.Problem08.ComplexInverseRealBlock.MatrixInversion
import NumStability.Source.Higham.Chapter14.Problem10.EntryPerturbation.MatrixInversion
import NumStability.Source.Higham.Chapter14.Problem11.HadamardCondition.MatrixInversion
import NumStability.Source.Higham.Chapter14.Problem12.ConditionNumberExamples.StressAndPeiMatrices
import NumStability.Source.Higham.Chapter14.Problem12.HadamardExamples.MatrixInversion
import NumStability.Source.Higham.Chapter14.Problem13.GEJBound.MatrixInversion
import NumStability.Source.Higham.Chapter14.Problem14.HymanDeterminant.MatrixInversion
import NumStability.Source.Higham.Chapter14.Problem15.DeterminantPerturbation.MatrixInversion
import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.MatrixInversion
import NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2B.MatrixInversion
import NumStability.Source.Higham.Chapter14.Section03.LUFactorInversion.MethodD.MatrixInversion

/-!
# MatrixInversion (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.MatrixInversion` keep
resolving. Every declaration moved unchanged to `NumStability.Source.Higham.Chapter14.Problem12.ConditionNumberExamples.StressAndPeiMatrices`.
The module's own original imports are re-stated so consumers reaching an
identifier transitively through this path still see the same surface.
-/
