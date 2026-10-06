import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import NumStability.Source.Higham.Chapter01.Problem02.NearIntegerTable.Basic

/-!
# NearInteger (compatibility module)

Import-only module retained so existing imports of `NumStability.Analysis.NearInteger`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
