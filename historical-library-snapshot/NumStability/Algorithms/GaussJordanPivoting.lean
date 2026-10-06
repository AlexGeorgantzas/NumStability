import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Linarith
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter14.Algorithm04.Pivoting.GaussJordanPivoting

/-!
# GaussJordanPivoting (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.GaussJordanPivoting`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
