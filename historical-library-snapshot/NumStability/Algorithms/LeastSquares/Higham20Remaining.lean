import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.HighamChapter10
import NumStability.Algorithms.LeastSquares.LSE
import NumStability.Algorithms.LeastSquares.LSNormalEquations
import NumStability.Source.Higham.Chapter20.Remaining

/-!
# Higham20Remaining (historical compatibility wrapper)

Import-only wrapper retained so historical imports of
`NumStability.Algorithms.LeastSquares.Higham20Remaining`
keep resolving. Its declarations moved unchanged to the canonical
modules imported above. Its own historical imports are re-stated so
consumers that reached an identifier transitively through this module
still see the same surface.
-/
