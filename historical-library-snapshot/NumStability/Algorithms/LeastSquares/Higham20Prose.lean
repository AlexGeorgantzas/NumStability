import NumStability.Algorithms.LeastSquares.LSQRSolve
import NumStability.Algorithms.Underdetermined.Higham21ProjectorNorm
import NumStability.Analysis.Perturbation.LeastSquares.Conditioning
import NumStability.Source.Higham.Chapter20.Prose

/-!
# Higham20Prose (historical compatibility wrapper)

Import-only wrapper retained so historical imports of
`NumStability.Algorithms.LeastSquares.Higham20Prose`
keep resolving. Its declarations moved unchanged to the canonical
modules imported above. Its own historical imports are re-stated so
consumers that reached an identifier transitively through this module
still see the same surface.
-/
