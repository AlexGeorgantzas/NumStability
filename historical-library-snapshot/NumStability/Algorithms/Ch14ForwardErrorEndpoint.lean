import Mathlib.Analysis.Asymptotics.Lemmas
import NumStability.Algorithms.MatrixInversion
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter14.Problem05.InverseBasedSolve.ForwardErrorEndpoint
import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ForwardErrorEndpoint
import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ScaledPerturbationEndpoints.ForwardError
import NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method1.ForwardErrorEndpoint

/-!
# Ch14ForwardErrorEndpoint (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.Ch14ForwardErrorEndpoint` keep
resolving. Every declaration moved unchanged to `NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ScaledPerturbationEndpoints.ForwardError`.
The module's own original imports are re-stated so consumers reaching an
identifier transitively through this path still see the same surface.
-/
