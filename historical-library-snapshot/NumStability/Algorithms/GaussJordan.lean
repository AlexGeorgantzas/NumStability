import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.GaussJordan.ErrorAnalysis.GaussJordan
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Analysis.ForwardError
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter09.Problems
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter09.Section03
import NumStability.Source.Higham.Chapter09.Section04
import NumStability.Source.Higham.Chapter09.Section05
import NumStability.Source.Higham.Chapter09.Section06
import NumStability.Source.Higham.Chapter09.Section08
import NumStability.Source.Higham.Chapter09.Section10
import NumStability.Source.Higham.Chapter09.Section11
import NumStability.Source.Higham.Chapter14.Corollary07.RowDominantCertificates.CumulativeProductBounds

/-!
# GaussJordan (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.GaussJordan` keep
resolving. Every declaration moved unchanged to `NumStability.Source.Higham.Chapter14.Corollary07.RowDominantCertificates.CumulativeProductBounds`.
The module's own original imports are re-stated so consumers reaching an
identifier transitively through this path still see the same surface.
-/
