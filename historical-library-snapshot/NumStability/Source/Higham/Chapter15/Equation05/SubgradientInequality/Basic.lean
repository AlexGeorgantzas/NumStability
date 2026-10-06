import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormPowerMethod
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter15.Equation02.Subgradient.PNormPowerMethod

/-!
# Chapter15 Equation05 SubgradientInequality Basic

Canonical destination for material split out of
`NumStability.Algorithms.PNormPowerMethod` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open scoped BigOperators

namespace PNormPair

variable {n : ℕ} (P : PNormPair n)

/-- **Equation (15.5).**  Written with the source names `u`, `v`, and `g`,
the subgradient inequality for `F(x)=‖Ax‖ₚ` follows unconditionally for the
specific subgradient `g=Aᵀ dualp(Au)` used by the power method. -/
theorem eq15_5_subgradient_inequality (u v : Fin n → ℝ) :
    P.pN (P.yof u) + (∑ i : Fin n, P.zof u i * (v i - u i)) ≤
      P.pN (P.yof v) :=
  P.eq15_2_zof_isSubgradient u v

end PNormPair

namespace SmoothPNormPair

variable {n : ℕ} (S : SmoothPNormPair n)

/-- **Equation (15.5), general `1 < p < ∞` source strength.**

The tangent with normal `z(u)=Aᵀ dualp(Au)` globally supports `‖A·‖_p`.
This is stronger than the displayed unit-ball specialization. -/
theorem eq15_5_subgradient_inequality (u v : Fin n → ℝ) :
    S.P.pN (S.P.yof u) +
      (∑ i : Fin n, S.P.zof u i * (v i - u i)) ≤
      S.P.pN (S.P.yof v) :=
  S.P.eq15_5_subgradient_inequality u v

end SmoothPNormPair
end Ch15
end NumStability
