import Batteries.Data.RBMap.Depth
import Batteries.Data.RBMap.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.Summation.Insertion.ActiveList
import NumStability.Algorithms.Summation.Recursive.Core
import NumStability.Algorithms.Summation.Tree.Core
import NumStability.Source.Higham.Chapter04.Equation05.OrderingExamples.Basic

/-!
# OrderingExamples (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.OrderingExamples`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
