import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatrixInversion
import NumStability.Analysis.Error.MatrixProducts.EvaluationTrees.ProductErrorNotation
import NumStability.Source.Higham.Chapter14.Section01.ProductErrorNotation.ProductErrorNotation

/-!
# Ch14ProductErrorNotation (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.Ch14ProductErrorNotation`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
