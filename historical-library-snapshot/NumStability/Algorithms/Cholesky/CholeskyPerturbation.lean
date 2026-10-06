import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.Cholesky.CholeskySpec
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LinearSystems.Cholesky.Perturbation.Basic
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# CholeskyPerturbation (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.Cholesky.CholeskyPerturbation`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/

