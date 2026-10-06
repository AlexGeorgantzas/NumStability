import Mathlib.Analysis.SpecialFunctions.Stirling
import NumStability.Algorithms.TestMatrices.Higham28Exact
import NumStability.Analysis.TestMatrices.Hilbert.Asymptotics
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.Asymptotics.Asymptotics

/-!
# Higham28Asymptotics (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.TestMatrices.Higham28Asymptotics`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
