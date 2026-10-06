import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.Cholesky.CholeskySpec
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Cholesky.Solve.Basic
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# CholeskySolve (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.Cholesky.CholeskySolve`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/

