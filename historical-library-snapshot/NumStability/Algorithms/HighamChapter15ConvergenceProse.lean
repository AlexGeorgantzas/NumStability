import Mathlib.Order.Fin.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Sequences
import NumStability.Algorithms.NormEstimation.PNorm.Convergence.ConvergenceStatements
import NumStability.Algorithms.NormEstimation.PNorm.Duality.ConvergenceStatements
import NumStability.Algorithms.NormEstimation.PNorm.Endpoints.ConvergenceStatements
import NumStability.Algorithms.PNormPowerMethodGeneralP
import NumStability.Source.Higham.Chapter15.Algorithm01.PNormPowerMethod.ConvergenceStatements
import NumStability.Source.Higham.Chapter15.Equation03.GradientQuotient.ConvergenceStatements
import NumStability.Source.Higham.Chapter15.Section02.Boyd.Corrections.ConvergenceStatements
import NumStability.Source.Higham.Chapter15.Section02.Boyd.EndpointTermination.ConvergenceStatements
import NumStability.Source.Higham.Chapter15.Section02.Boyd.GlobalConvergence.ConvergenceStatements

/-!
# HighamChapter15ConvergenceProse (compatibility wrapper)

Declaration-free reviewed owner. Its imports are normalized to the exact
canonical and source targets that now hold the material it used to reach
through historical paths, and the historical path itself is retained so
existing imports of `NumStability.Algorithms.HighamChapter15ConvergenceProse` keep resolving. This module declares nothing.
-/
