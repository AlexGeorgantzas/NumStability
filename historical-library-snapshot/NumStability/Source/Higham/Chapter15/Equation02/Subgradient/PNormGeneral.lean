import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormPowerMethod
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormPowerMethod
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormGeneral
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification
import NumStability.Source.Higham.Chapter15.Equation02.Subgradient.PNormPowerMethod

/-!
# Chapter15 Equation02 Subgradient PNormGeneral

Canonical destination for material split out of
`NumStability.Algorithms.PNormPowerMethodGeneralP` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open scoped BigOperators

/-- The concrete square-matrix form of Higham's singleton subdifferential
formula (15.2), valid for every real Holder-conjugate `1 < p,q < infinity`. -/
theorem eq15_2_subdifferential_singleton_general {n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hfull : Function.Injective
      (fun v : Fin n → ℝ => fun i => ∑ j : Fin n, A i j * v j))
    (hx : x ≠ 0) :
    ∀ g, IsSubgradient
        (fun v : Fin n → ℝ =>
          realVecLpNorm p (fun i => ∑ j : Fin n, A i j * v j)) x g ↔
      g = fun j => ∑ i : Fin n, A i j *
        realLpDual hpq (fun r => ∑ k : Fin n, A r k * x k) i := by
  let S := SmoothPNormPair.general hn hpq A
  simpa [S, SmoothPNormPair.general, pNormPair_general,
    PNormPair.yof, PNormPair.zof] using
    S.eq15_2_subdifferential_singleton x hfull hx

/-- **Higham (15.2), literal rectangular source strength.**  For a full
column-rank real `m x n` matrix and nonzero `x`, the subdifferential of
`x |-> ||A x||_p` is the displayed singleton for every `1 < p < infinity`. -/
theorem eq15_2_subdifferential_singleton_general_rect {m n : ℕ}
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hfull : Function.Injective (realRectMatVec A)) (hx : x ≠ 0) :
    ∀ g, IsSubgradient
        (fun v => realVecLpNorm p (realRectMatVec A v)) x g ↔
      g = realRectTransposeVec A (realLpDual hpq (realRectMatVec A x)) := by
  have hy : realRectMatVec A x ≠ 0 := by
    intro hy0
    apply hx
    apply hfull
    rw [hy0]
    funext i
    simp [realRectMatVec]
  have hgrad := realRectLpComposite_hasDirectionalGradientAt hpq A x hy
  intro g
  constructor
  · intro hg
    exact unique_subgradient_of_directional_gradient _ x _ g hgrad hg
  · intro hg
    subst g
    exact realRectLpComposite_isSubgradient hpq A x

end Ch15
end NumStability
