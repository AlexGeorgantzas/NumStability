import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LeastSquares.LSPerturbation
import NumStability.Algorithms.LinearSystems.LeastSquares.AugmentedSystem
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.GramBasis
import NumStability.Algorithms.LinearSystems.LeastSquares.MGS
import NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations
import NumStability.Algorithms.LinearSystems.LeastSquares.QRSolve
import NumStability.Algorithms.LinearSystems.LeastSquares.RankGeometry
import NumStability.Algorithms.LinearSystems.LeastSquares.StoredQR
import NumStability.Algorithms.LinearSystems.QR.Householder.StoredQR
import NumStability.Algorithms.LinearSystems.QR.QRSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.InverseBounds
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.AugmentedSystem
import NumStability.Analysis.Perturbation.LeastSquares.BackwardError
import NumStability.Analysis.Perturbation.LeastSquares.Basic
import NumStability.Analysis.Perturbation.LeastSquares.GramBasis
import NumStability.Analysis.Perturbation.LeastSquares.NormalEquations
import NumStability.Analysis.Perturbation.LeastSquares.Normwise
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.SingularValues.Realification
import NumStability.Source.Higham.Chapter20.Theorem03.QRSolve

/-!
# LSQRSolve (historical compatibility wrapper)

Import-only wrapper retained so historical imports of
`NumStability.Algorithms.LeastSquares.LSQRSolve`
keep resolving. Its declarations moved unchanged to the canonical
modules imported above. Its own historical imports are re-stated so
consumers that reached an identifier transitively through this module
still see the same surface.
-/
