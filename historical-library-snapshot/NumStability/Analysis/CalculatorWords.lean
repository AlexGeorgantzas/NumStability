import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.NormNum
import NumStability.Source.Higham.Chapter01.Problem06.CalculatorWords.Basic

/-!
# CalculatorWords (compatibility module)

Import-only module retained so existing imports of `NumStability.Analysis.CalculatorWords`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
