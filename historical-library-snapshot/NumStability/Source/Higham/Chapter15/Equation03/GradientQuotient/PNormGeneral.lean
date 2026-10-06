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
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormPowerMethod
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormPowerMethod
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormGeneral
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification
import NumStability.Source.Higham.Chapter15.Equation03.GradientQuotient.PNormPowerMethod

/-!
# Chapter15 Equation03 GradientQuotient PNormGeneral

Canonical destination for material split out of
`NumStability.Algorithms.PNormPowerMethodGeneralP` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open scoped BigOperators

/-- The concrete homogeneous quotient from Higham equation (15.3). -/
noncomputable def realLpQuotient {n : ℕ} (p : ℝ)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  realVecLpNorm p (fun i => ∑ j : Fin n, A i j * x j) /
    realVecLpNorm p x

/-- The concrete right-hand side of Higham equation (15.3). -/
noncomputable def realLpQuotientGradient {n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (A : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j =>
    (∑ i : Fin n, A i j *
      realLpDual hpq (fun r => ∑ k : Fin n, A r k * x k) i) /
        realVecLpNorm p x -
      (realVecLpNorm p (fun r => ∑ k : Fin n, A r k * x k) /
        realVecLpNorm p x ^ 2) * realLpDual hpq x j

/-- Concrete, source-hypothesis form of equation (15.3): full rank and
`x ≠ 0` imply the displayed general-`p` quotient gradient. -/
theorem eq15_3_directional_general_of_full_rank {n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hfull : Function.Injective
      (fun v : Fin n → ℝ => fun i => ∑ j : Fin n, A i j * v j))
    (hx : x ≠ 0) :
    HasDirectionalGradientAt (realLpQuotient p A)
      (realLpQuotientGradient hpq A x) x := by
  let S := SmoothPNormPair.general hn hpq A
  simpa [S, SmoothPNormPair.general, pNormPair_general,
    SmoothPNormPair.eq15_3_F, SmoothPNormPair.eq15_3_gradient,
    PNormPair.yof, PNormPair.zof, realLpQuotient,
    realLpQuotientGradient] using
    S.eq15_3_directional_of_full_rank x hfull hx

noncomputable def realRectLpQuotient {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  realVecLpNorm p (realRectMatVec A x) / realVecLpNorm p x

noncomputable def realRectLpQuotientGradient {m n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j =>
    realRectTransposeVec A (realLpDual hpq (realRectMatVec A x)) j /
        realVecLpNorm p x -
      (realVecLpNorm p (realRectMatVec A x) / realVecLpNorm p x ^ 2) *
        realLpDual hpq x j

/-- **Higham (15.3), literal rectangular source strength.**  Full column rank
and `x ≠ 0` suffice for the displayed quotient gradient. -/
theorem eq15_3_directional_general_rect_of_full_rank {m n : ℕ}
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hfull : Function.Injective (realRectMatVec A)) (hx : x ≠ 0) :
    HasDirectionalGradientAt (realRectLpQuotient p A)
      (realRectLpQuotientGradient hpq A x) x := by
  have hy : realRectMatVec A x ≠ 0 := by
    intro hy0
    apply hx
    apply hfull
    rw [hy0]
    funext i
    simp [realRectMatVec]
  intro h
  have hnum := realRectLpComposite_hasDirectionalGradientAt hpq A x hy h
  have hden := realLpDual_hasDirectionalGradientAt hpq x hx h
  have hxnorm : realVecLpNorm p x ≠ 0 :=
    ne_of_gt (realVecLpNorm_pos (le_of_lt hpq.lt) hx)
  have hxnorm0 : realVecLpNorm p (fun i => x i + 0 * h i) ≠ 0 := by
    simpa using hxnorm
  have hquot := hnum.div hden hxnorm0
  change HasDerivAt
    (fun t : ℝ => realRectLpQuotient p A (fun i => x i + t * h i))
    (∑ i : Fin n, realRectLpQuotientGradient hpq A x i * h i) 0
  convert hquot using 1
  simp only [zero_mul, add_zero]
  unfold realRectLpQuotientGradient
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  rw [show (∑ i : Fin n,
        realRectTransposeVec A (realLpDual hpq (realRectMatVec A x)) i /
          realVecLpNorm p x * h i) =
        (∑ i : Fin n,
          realRectTransposeVec A (realLpDual hpq (realRectMatVec A x)) i * h i) /
            realVecLpNorm p x by
      calc
        _ = (realVecLpNorm p x)⁻¹ *
            (∑ i : Fin n,
              realRectTransposeVec A (realLpDual hpq (realRectMatVec A x)) i * h i) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i _hi
                rw [div_eq_mul_inv]
                ring
        _ = _ := by rw [div_eq_mul_inv]; ring]
  rw [show (∑ i : Fin n,
        realVecLpNorm p (realRectMatVec A x) / realVecLpNorm p x ^ 2 *
          realLpDual hpq x i * h i) =
        (realVecLpNorm p (realRectMatVec A x) / realVecLpNorm p x ^ 2) *
          (∑ i : Fin n, realLpDual hpq x i * h i) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring]
  field_simp [hxnorm]

end Ch15
end NumStability
