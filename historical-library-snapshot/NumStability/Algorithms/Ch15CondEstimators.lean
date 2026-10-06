import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.CondEstimation
import NumStability.Algorithms.NormEstimation.OneNorm.LINPACK.Basic
import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.Algebra.CondEstimators
import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.PowerBounds.CondEstimators
import NumStability.Analysis.ConditionEstimatorLowerBound
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter15.Algorithm05.LINPACKConditionEstimator.Basic
import NumStability.Source.Higham.Chapter15.Algorithm05.LINPACKConditionEstimator.InverseNormBound.TriangularSolve
import NumStability.Source.Higham.Chapter15.Equation07.DixonBound.Basic

/-!
# Ch15CondEstimators (compatibility wrapper)

Import-only historical path, retained so existing imports of `NumStability.Algorithms.Ch15CondEstimators`
keep resolving. Its whole declaration block moved unchanged to
`NumStability.Source.Higham.Chapter15.Algorithm05.LINPACKConditionEstimator.InverseNormBound.TriangularSolve`, which is imported above. The module's own original imports are
re-stated so consumers that reached an identifier transitively through this
path still see the same surface. This module declares nothing.
-/
