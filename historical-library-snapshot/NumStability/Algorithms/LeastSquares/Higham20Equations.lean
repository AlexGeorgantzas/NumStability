import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LeastSquares.LSNormalEquations
import NumStability.Algorithms.LeastSquares.LSQRSolve
import NumStability.Analysis.Perturbation.LeastSquares.Basic
import NumStability.Source.Higham.Chapter12.IterativeRefinement.Results.Theorems
import NumStability.Source.Higham.Chapter20.Equations

/-!
# Higham20Equations (historical compatibility wrapper)

Import-only wrapper retained so historical imports of
`NumStability.Algorithms.LeastSquares.Higham20Equations`
keep resolving. Its declarations moved unchanged to the canonical
modules imported above. Its own historical imports are re-stated so
consumers that reached an identifier transitively through this module
still see the same surface.
-/
