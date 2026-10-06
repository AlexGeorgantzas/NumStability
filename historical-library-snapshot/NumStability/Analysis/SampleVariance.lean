-- NumStability/Analysis/SampleVariance.lean
--
-- Import-only compatibility wrapper retained by reorganization wave R03
-- (phase branch B0005, projection P0005). This historical path is preserved,
-- not deleted and not Git-renamed, so every existing `import` keeps resolving.
-- All of its declarations moved unchanged to the canonical module(s) below.

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Basic
import NumStability.Analysis.Error.Measures.ScalarDefinitions
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Statistics.SampleVariance.Core
import NumStability.Analysis.Statistics.SampleVariance.RoundingErrorBounds.Theorems
import NumStability.Analysis.Statistics.SampleVariance.TwoPass
import NumStability.Analysis.Statistics.SampleVariance.Updating
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.Source.Higham.Chapter01.Problem07.SampleVarianceConditioning.ConditionNumbers
import NumStability.Source.Higham.Chapter01.Problem10.TwoPassSampleVariance.Bounds
import NumStability.Source.Higham.Chapter01.Problem10.TwoPassSampleVariance.RemainderBound.Theorem
import NumStability.Source.Higham.Chapter01.Section09.SampleVariance.Examples
import NumStability.Source.Higham.Chapter01.Section09.SampleVariance.IeeeSingleOnePassCounterexample.Results

/-!
# SampleVariance (compatibility wrapper)

Declaration-free import-only wrapper. Canonical module(s):

* `NumStability.Analysis.Statistics.SampleVariance.RoundingErrorBounds.Theorems`
* `NumStability.Source.Higham.Chapter01.Problem10.TwoPassSampleVariance.RemainderBound.Theorem`
* `NumStability.Source.Higham.Chapter01.Section09.SampleVariance.IeeeSingleOnePassCounterexample.Results`

Retained by wave R03 so historical imports continue to resolve unchanged.
-/
