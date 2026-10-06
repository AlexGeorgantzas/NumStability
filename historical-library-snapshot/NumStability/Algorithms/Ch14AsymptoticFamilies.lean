import Mathlib.Analysis.Asymptotics.Lemmas
import NumStability.Algorithms.Ch14ForwardErrorEndpoint
import NumStability.Analysis.FirstOrder.MatrixFamilies.AsymptoticFamilies
import NumStability.Source.Higham.Chapter14.Problem05.InverseBasedSolve.AsymptoticFamilies
import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.AsymptoticFamilies
import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ComposedCoefficientFamilies.RemainderAsymptotics
import NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method1.AsymptoticFamilies

/-!
# Ch14AsymptoticFamilies (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.Ch14AsymptoticFamilies` keep
resolving. Every declaration moved unchanged to `NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ComposedCoefficientFamilies.RemainderAsymptotics`.
The module's own original imports are re-stated so consumers reaching an
identifier transitively through this path still see the same surface.
-/
