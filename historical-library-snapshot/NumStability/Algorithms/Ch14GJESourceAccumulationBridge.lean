import NumStability.Algorithms.Ch14GaussJordanSourceClosure
import NumStability.Source.Higham.Chapter14.Algorithm04.Accumulation.GJESourceAccumulationBridge

/-!
# Ch14GJESourceAccumulationBridge (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.Ch14GJESourceAccumulationBridge`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
