import NumStability.Algorithms.Ch14GaussJordanAccumulation
import NumStability.Algorithms.Ch14GaussJordanStep
import NumStability.Algorithms.GaussJordan
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter14.Algorithm04.SecondStage.GaussJordanQConstruction
import NumStability.Source.Higham.Chapter14.Theorem05.ForwardError.GaussJordanQConstruction

/-!
# Ch14GaussJordanQConstruction (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.Ch14GaussJordanQConstruction`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
