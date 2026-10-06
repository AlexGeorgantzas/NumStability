import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Source.Higham.Chapter01.Problem08.MullerRecurrence.Basic

/-!
# MullerRecurrence (compatibility module)

Import-only module retained so existing imports of `NumStability.Analysis.MullerRecurrence`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
