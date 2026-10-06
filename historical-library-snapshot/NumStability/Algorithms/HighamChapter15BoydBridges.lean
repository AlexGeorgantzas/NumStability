import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.Compact
import NumStability.Algorithms.HighamChapter15ConvergenceProse
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Carrier.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.FixedPoints.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.LocalStability.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Convergence.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Duality.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.BoydInterface
import NumStability.Algorithms.PNormPowerMethodRect
import NumStability.Source.Higham.Chapter15.Lemma02.PNormPowerMethod.BoydInterface
import NumStability.Source.Higham.Chapter15.Section02.Boyd.GlobalConvergence.BoydInterface
import NumStability.Source.Higham.Chapter15.Section02.Boyd.LocalConvergence.BoydInterface

/-!
# HighamChapter15BoydBridges (compatibility wrapper)

Declaration-free reviewed owner. Its imports are normalized to the exact
canonical and source targets that now hold the material it used to reach
through historical paths, and the historical path itself is retained so
existing imports of `NumStability.Algorithms.HighamChapter15BoydBridges` keep resolving. This module declares nothing.
-/
