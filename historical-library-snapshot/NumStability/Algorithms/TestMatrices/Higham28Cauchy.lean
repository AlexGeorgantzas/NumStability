import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import NumStability.Algorithms.TestMatrices.Higham28Contracts
import NumStability.Analysis.TestMatrices.Cauchy.Cauchy
import NumStability.Source.Higham.Chapter28.Section01.Cauchy.Cauchy
import NumStability.Source.Higham.Chapter28.Section01.HilbertConditioning.Cauchy

/-!
# Higham28Cauchy (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.TestMatrices.Higham28Cauchy`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
