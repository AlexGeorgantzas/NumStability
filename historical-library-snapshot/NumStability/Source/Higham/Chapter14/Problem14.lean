import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter14.Problem14.FloatingPointDeterminant.HymanBackwardError
import NumStability.Source.Higham.Chapter14.Problem14.HymanDeterminant.MatrixInversion

/-!
# Problem14

Declaration-free source aggregate. Every declaration moved unchanged to
`NumStability.Source.Higham.Chapter14.Problem14.FloatingPointDeterminant.HymanBackwardError` during wave R08; this module imports the canonical children so
existing imports of this path keep resolving and the family contract is
advertised from one place.
-/
