import NumStability.Algorithms.Ch14Method2Loop
import NumStability.Algorithms.LinearSystems.LU.BlockLU.FirstOrderModels
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatrixInversion
import NumStability.Analysis.FirstOrder.FixedPrecision
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter13.Section01.OperationModels
import NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2B.MatrixInversionMethod2BInstance

/-!
# MatrixInversionMethod2BInstance (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.MatrixInversionMethod2BInstance`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
