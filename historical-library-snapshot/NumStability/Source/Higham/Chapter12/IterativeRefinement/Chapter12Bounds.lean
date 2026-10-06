-- NumStability/Source/Higham/Chapter12/IterativeRefinement/Chapter12Bounds.lean
--
-- Import-only compatibility wrapper retained by reorganization wave R03
-- (phase branch B0005, projection P0005). This historical path is preserved,
-- not deleted and not Git-renamed, so every existing `import` keeps resolving.
-- All of its declarations moved unchanged to the canonical module(s) below.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.LinearSystems.IterativeRefinement.Core
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.MatVec
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter12.IterativeRefinement.ForwardErrorBounds.Results

/-!
# Chapter12Bounds (compatibility wrapper)

Declaration-free import-only wrapper. Canonical module(s):

* `NumStability.Source.Higham.Chapter12.IterativeRefinement.ForwardErrorBounds.Results`

Retained by wave R03 so historical imports continue to resolve unchanged.
-/
