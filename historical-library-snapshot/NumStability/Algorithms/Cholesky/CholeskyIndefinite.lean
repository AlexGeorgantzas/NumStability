import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.BlockLDLT
import NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.BlockLDLTStep
import NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.Predicates
import NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.SkewSymmetric
import NumStability.Algorithms.LinearSystems.SymmetricIndefinite.Pivoting.Basic
import NumStability.Algorithms.LinearSystems.SymmetricIndefinite.Pivoting.Tridiagonal
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter11.Theorem07.TridiagonalTwoByTwoResidual.Basic

/-!
# CholeskyIndefinite (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.Cholesky.CholeskyIndefinite`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/

