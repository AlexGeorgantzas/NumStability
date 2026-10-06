import NumStability.Algorithms.Ch14MethodDUpperCertificate
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Assembly.Core
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Basic
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Source.Higham.Chapter14.Section03.LUFactorInversion.MethodB.MethodsBC
import NumStability.Source.Higham.Chapter14.Section03.LUFactorInversion.MethodC.MethodsBC

/-!
# Ch14MethodsBC (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.Ch14MethodsBC`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
