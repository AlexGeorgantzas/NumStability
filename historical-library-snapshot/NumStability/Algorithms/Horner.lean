-- NumStability/Algorithms/Horner.lean
--
-- Import-only compatibility wrapper retained by reorganization wave R03
-- (phase branch B0005, projection P0005). This historical path is preserved,
-- not deleted and not Git-renamed, so every existing `import` keeps resolving.
-- All of its declarations moved unchanged to the canonical module(s) below.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.PolynomialEvaluation.DerivativeEvaluation.ErrorBounds
import NumStability.Algorithms.PolynomialEvaluation.ElementaryErrorBounds
import NumStability.Algorithms.PolynomialEvaluation.MatrixNorms
import NumStability.Algorithms.PolynomialEvaluation.RootProduct
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter05.Equation14.MatrixPolynomialForms.Basic
import NumStability.Source.Higham.Chapter05.Problem01.DifferentiatedHorner.Basic
import NumStability.Source.Higham.Chapter05.Problem02.PowerBuilding.Basic
import NumStability.Source.Higham.Chapter05.Problem03.EvenOddSplitting.Basic
import NumStability.Source.Higham.Chapter05.Problem06.MatrixPolynomialHorner.Basic
import NumStability.Source.Higham.Chapter05.Section01.Horner.Basic
import NumStability.Source.Higham.Chapter05.Section01.RelativeError.Basic
import NumStability.Source.Higham.Chapter05.Section02.DerivativeEvaluation.Bidiagonal
import NumStability.Source.Higham.Chapter05.Section02.DerivativeEvaluation.SyntheticDivision
import NumStability.Source.Higham.Chapter05.Section03.DividedDifferences.Basic
import NumStability.Source.Higham.Chapter05.Section03.LejaOrdering.Basic
import NumStability.Source.Higham.Chapter05.Section03.NewtonEvaluation.HornerBasis

/-!
# Horner (compatibility wrapper)

Declaration-free import-only wrapper. Canonical module(s):

* `NumStability.Algorithms.PolynomialEvaluation.DerivativeEvaluation.ErrorBounds`

Retained by wave R03 so historical imports continue to resolve unchanged.
-/
