import Mathlib.Analysis.Matrix.Order
import NumStability.Algorithms.Ch15CondEstimators
import NumStability.Algorithms.Ch15DixonProbability
import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.Algebra.DixonCompletion
import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.PowerBounds.DixonCompletion
import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.Probability.DixonCompletion
import NumStability.Algorithms.TestMatrices.Higham28OrthogonalCoordinates
import NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic
import NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic
import NumStability.Source.Higham.Chapter15.Theorem06.Dixon.Basic

/-!
# Ch15DixonClosure (compatibility wrapper)

Declaration-free reviewed owner. Its imports are normalized to the exact
canonical and source targets that now hold the material it used to reach
through historical paths, and the historical path itself is retained so
existing imports of `NumStability.Algorithms.Ch15DixonClosure` keep resolving. This module declares nothing.
-/
