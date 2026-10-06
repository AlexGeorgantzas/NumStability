-- NumStability/Algorithms/LU/Doolittle.lean
--
-- Import-only compatibility wrapper retained by reorganization wave R03
-- (phase branch B0005, projection P0005). This historical path is preserved,
-- not deleted and not Git-renamed, so every existing `import` keeps resolving.
-- All of its declarations moved unchanged to the canonical module(s) below.

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Assembly.Core
import NumStability.Algorithms.LinearSystems.LU.Doolittle.BackwardError
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Basic
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Budgets
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Certificates
import NumStability.Algorithms.LinearSystems.LU.Doolittle.RoundedEntries
import NumStability.Analysis.Rounding
import NumStability.Analysis.SubtractionFold
import NumStability.FloatingPoint.Model

/-!
# Doolittle (compatibility wrapper)

Declaration-free import-only wrapper. Canonical module(s):

* `NumStability.Algorithms.LinearSystems.LU.Doolittle.Assembly.Core`

Retained by wave R03 so historical imports continue to resolve unchanged.
-/
