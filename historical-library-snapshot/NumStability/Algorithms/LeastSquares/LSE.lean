import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LeastSquares.LSQRSolve
import NumStability.Algorithms.LinearSystems.LeastSquares.Equality.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.Equality.GQR
import NumStability.Algorithms.LinearSystems.LeastSquares.Equality.KKT
import NumStability.Algorithms.LinearSystems.QR.GramSchmidtPolar
import NumStability.Algorithms.QR.Higham19
import NumStability.Algorithms.QR.Higham19Thm6ColPivot
import NumStability.Algorithms.QR.Higham19Thm6CoxHigham
import NumStability.Algorithms.QR.Higham19Thm6CoxHighamConcrete
import NumStability.Algorithms.QR.Higham19Thm6ElementwisePackaged
import NumStability.Algorithms.QR.Higham19Thm6RowSpecific
import NumStability.Algorithms.Underdetermined.UnderdeterminedSpec
import NumStability.Analysis.Perturbation.LeastSquares.Equality.MixedStability
import NumStability.Analysis.Perturbation.LeastSquares.Equality.Perturbation
import NumStability.Analysis.Perturbation.LeastSquares.Equality.RowwiseBackwardError
import NumStability.Source.Higham.Chapter20.Theorem08.LSE

/-!
# LSE (historical compatibility wrapper)

Import-only wrapper retained so historical imports of
`NumStability.Algorithms.LeastSquares.LSE`
keep resolving. Its declarations moved unchanged to the canonical
modules imported above. Its own historical imports are re-stated so
consumers that reached an identifier transitively through this module
still see the same surface.
-/
