import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.RingTheory.Algebraic.Basic
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Source.Higham.Chapter02.Section10.Tablemaker.FiniteSeparation.Basic

/-!
# HighamChapter2Tablemaker (compatibility module)

Import-only module retained so existing imports of `NumStability.Analysis.HighamChapter2Tablemaker`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
