import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Basic
import NumStability.Analysis.FloatingPointArithmetic.Format
import NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError
import NumStability.Analysis.Rounding
import NumStability.Source.Higham.Chapter01.Problem05.CompensatedLogarithm.Basic
import NumStability.Source.Higham.Chapter01.Section11.Accumulation.Basic

/-!
# Accumulation (compatibility module)

Import-only module retained so existing imports of `NumStability.Analysis.Accumulation`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
