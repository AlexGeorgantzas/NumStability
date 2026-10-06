import NumStability.Algorithms.TestMatrices.Higham28
import NumStability.Analysis.TestMatrices.Hilbert.Exact
import NumStability.Analysis.TestMatrices.Pascal.Exact
import NumStability.Source.Higham.Chapter28.Equation01.HilbertInverse.Exact
import NumStability.Source.Higham.Chapter28.Equation02.ExactHilbertDeterminant.Exact
import NumStability.Source.Higham.Chapter28.Equation03.HilbertCholeskyFactor.Exact

/-!
# Higham28Exact (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.TestMatrices.Higham28Exact`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
