import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.CondEstimation
import NumStability.Algorithms.NormEstimation.OneNorm.PowerMethod.PNormPowerMethod
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormPowerMethod
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormPowerMethod
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter15.Algorithm01.PNormPowerMethod.PNormPowerMethod
import NumStability.Source.Higham.Chapter15.Equation02.Subgradient.PNormPowerMethod
import NumStability.Source.Higham.Chapter15.Equation03.GradientQuotient.PNormPowerMethod
import NumStability.Source.Higham.Chapter15.Equation04.NormalizedDualDiscrepancy.Basic
import NumStability.Source.Higham.Chapter15.Equation05.SubgradientInequality.Basic
import NumStability.Source.Higham.Chapter15.Lemma02.PNormPowerMethod.PNormPowerMethod

/-!
# PNormPowerMethod (compatibility wrapper)

Declaration-free reviewed owner. Its imports are normalized to the exact
canonical and source targets that now hold the material it used to reach
through historical paths, and the historical path itself is retained so
existing imports of `NumStability.Algorithms.PNormPowerMethod` keep resolving. This module declares nothing.
-/
