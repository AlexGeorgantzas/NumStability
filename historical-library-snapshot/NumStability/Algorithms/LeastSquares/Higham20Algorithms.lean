import NumStability.Algorithms.LeastSquares.LSQRSolve
import NumStability.Algorithms.LinearSystems.LeastSquares.Refinement
import NumStability.Analysis.Perturbation.LeastSquares.Basic
import NumStability.Source.Higham.Chapter20.Section02.Algorithms

/-!
# Higham20Algorithms (historical compatibility wrapper)

Import-only wrapper retained so historical imports of
`NumStability.Algorithms.LeastSquares.Higham20Algorithms`
keep resolving. Its declarations moved unchanged to the canonical
modules imported above. Its own historical imports are re-stated so
consumers that reached an identifier transitively through this module
still see the same surface.
-/
