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
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormPowerMethod
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormPowerMethod
import NumStability.Analysis.MatrixAlgebra

/-!
# Chapter15 Equation02 Subgradient PNormPowerMethod

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

/-- **Equation (15.2), constructive subgradient direction.**  The vector
`Aᵀ dualp(Ax)` computed by Algorithm 15.1 is a subgradient of
`x ↦ ‖Ax‖ₚ`.  For full-rank `A`, `1<p<∞`, and `x≠0`, differentiability makes
this subgradient unique, giving the source singleton formula. -/
theorem eq15_2_zof_isSubgradient (x : Fin n → ℝ) :
    IsSubgradient (fun v => P.pN (P.yof v)) x (P.zof x) := by
  intro v
  have hsub := P.dp_isSubgradient (P.yof x) (P.yof v)
  unfold IsSubgradient at hsub
  have hdot : (∑ i : Fin n, P.zof x i * (v i - x i)) =
      ∑ i : Fin n, P.dp (P.yof x) i * (P.yof v i - P.yof x i) := by
    rw [P.z_dot x (fun i => v i - x i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (∑ j : Fin n, P.A i j * (v j - x j)) =
        P.yof v i - P.yof x i from congrFun (P.yof_sub v x) i]
  change P.pN (P.yof x) + (∑ i : Fin n, P.zof x i * (v i - x i)) ≤
    P.pN (P.yof v)
  rw [hdot]
  exact hsub

end PNormPair

namespace SmoothPNormPair

variable {n : ℕ} (S : SmoothPNormPair n)

/-- **Equation (15.2), general `1 < p < ∞` source strength.**

If `A` has full column rank and `x ≠ 0`, the subdifferential of
`x ↦ ‖Ax‖_p` is exactly the singleton `{Aᵀ dualp(Ax)}`. -/
theorem eq15_2_subdifferential_singleton (x : Fin n → ℝ)
    (hfull : Function.Injective S.P.yof) (hx : x ≠ 0) :
    ∀ g, IsSubgradient (fun v => S.P.pN (S.P.yof v)) x g ↔
      g = S.P.zof x := by
  have hy : S.P.yof x ≠ 0 := by
    intro hy0
    apply hx
    apply hfull
    rw [hy0]
    ext i
    simp [PNormPair.yof]
  have hgrad := S.composite_hasDirectionalGradientAt x hy
  intro g
  constructor
  · intro hg
    exact unique_subgradient_of_directional_gradient
      (fun v => S.P.pN (S.P.yof v)) x (S.P.zof x) g hgrad hg
  · intro hg
    subst g
    exact S.P.eq15_2_zof_isSubgradient x

end SmoothPNormPair
end Ch15
end NumStability
