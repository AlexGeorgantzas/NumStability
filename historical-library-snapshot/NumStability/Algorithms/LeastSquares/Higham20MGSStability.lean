import NumStability.Algorithms.LeastSquares.LSQRSolve
import NumStability.Algorithms.QR.Higham19
import NumStability.Algorithms.QR.Higham19Alg12MGSRepair
import NumStability.Algorithms.QR.Higham19Alg12MGSRounded
import NumStability.Source.Higham.Chapter20.Problem05.MGSStability

/-!
# Higham20MGSStability (historical compatibility wrapper)

Import-only wrapper retained so historical imports of
`NumStability.Algorithms.LeastSquares.Higham20MGSStability`
keep resolving. Its declarations moved unchanged to the canonical
modules imported above. Its own historical imports are re-stated so
consumers that reached an identifier transitively through this module
still see the same surface.
-/
