import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import NumStability.Algorithms.Ch14BlockTriInverse
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatrixInversion
import NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2C.BlockResidual.LeftResidualBounds
import NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2C.Method2C

/-!
# Ch14Method2C (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.Ch14Method2C` keep
resolving. Every declaration moved unchanged to `NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2C.BlockResidual.LeftResidualBounds`.
The module's own original imports are re-stated so consumers reaching an
identifier transitively through this path still see the same surface.
-/
