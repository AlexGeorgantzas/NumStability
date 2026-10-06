-- NumStability/Analysis/HighamChapter7.lean
--
-- Import-only compatibility wrapper retained by reorganization wave R03
-- (phase branch B0005, projection P0005). This historical path is preserved,
-- not deleted and not Git-renamed, so every existing `import` keeps resolving.
-- All of its declarations moved unchanged to the canonical module(s) below.

import Mathlib.Algebra.Order.GroupWithZero.Finset
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import NumStability.Algorithms.CondEstimation
import NumStability.Analysis.Asymptotics.Bounds
import NumStability.Analysis.Conditioning.DistanceToSingularity
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.Conditioning.LinearSystems.SubordinatePerturbation
import NumStability.Analysis.MatrixNorms.SpectralRadius
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Summation.Signs
import NumStability.Source.Higham.Chapter06.Problem05
import NumStability.Source.Higham.Chapter07.Corollary06.LinearSystemsConditioning.Basic
import NumStability.Source.Higham.Chapter07.Corollary06.LinearSystemsConditioning.Results
import NumStability.Source.Higham.Chapter07.Equation17.KahanConditioningExample
import NumStability.Source.Higham.Chapter07.Equation25.InverseConditioning.ExactPerturbation
import NumStability.Source.Higham.Chapter07.Equation26.DistanceToSingularity.Results
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.ComputedResidual
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.ConditionNumbers
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Equation05
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Equation32
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Equation33
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.ForwardErrorKernels
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Lemma09
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem01
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem02
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem04
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem05
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem06Columnwise
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem06Rowwise
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem07
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem08RectangularBackwardError
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem09Exact
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem09Linearized
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem10Bauer.Part01
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem10Bauer.Part02
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem10Bauer.Part03
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem10OneNorm
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem13SparseResidual
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem15Hadamard
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.RowScaling
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem02
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem04
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem05.Part01
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem05.Part02
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem05.Part03
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem05.Part04
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem05.Part05
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem05.Part06
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem05.RowInfinityScaleCounterexample.Theorems
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem07FrobeniusScaling
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem08Aliases

/-!
# HighamChapter7 (compatibility wrapper)

Declaration-free import-only wrapper. Canonical module(s):

* `NumStability.Source.Higham.Chapter07.Equation17.KahanConditioningExample`
* `NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem05.RowInfinityScaleCounterexample.Theorems`

Retained by wave R03 so historical imports continue to resolve unchanged.
-/
