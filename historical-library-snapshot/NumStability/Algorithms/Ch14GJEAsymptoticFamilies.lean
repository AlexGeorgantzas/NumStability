import NumStability.Algorithms.Ch14AsymptoticFamilies
import NumStability.Algorithms.Ch14GaussJordanQConstruction
import NumStability.Source.Higham.Chapter14.Theorem05.EliminationFamilies.CoefficientAsymptotics
import NumStability.Source.Higham.Chapter14.Theorem05.ForwardError.GJEAsymptoticFamilies

/-!
# Ch14GJEAsymptoticFamilies (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.Ch14GJEAsymptoticFamilies` keep
resolving. Every declaration moved unchanged to `NumStability.Source.Higham.Chapter14.Theorem05.EliminationFamilies.CoefficientAsymptotics`.
The module's own original imports are re-stated so consumers reaching an
identifier transitively through this path still see the same surface.
-/
