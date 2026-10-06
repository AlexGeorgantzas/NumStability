import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Tactic
import NumStability.Algorithms.PolynomialEvaluation.DerivativeEvaluation.ErrorBounds
import NumStability.Source.Higham.Chapter05.Problem04.LejaOrdering.Basic

/-!
# Ch5LejaProducer (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.Ch5LejaProducer`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
