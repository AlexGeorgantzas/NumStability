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
# Chapter15 Equation03 GradientQuotient PNormPowerMethod

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

end PNormPair

namespace SmoothPNormPair

variable {n : ℕ} (S : SmoothPNormPair n)

/-- Higham's homogeneous quotient `F(x) = ‖Ax‖_p / ‖x‖_p` in (15.3). -/
noncomputable def eq15_3_F (x : Fin n → ℝ) : ℝ :=
  S.P.pN (S.P.yof x) / S.P.pN x

/-- The general normalized-dual gradient displayed in equation (15.3). -/
noncomputable def eq15_3_gradient (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j => S.P.zof x j / S.P.pN x -
    (S.P.pN (S.P.yof x) / S.P.pN x ^ 2) * S.P.dp x j

/-- **Equation (15.3), general `1 < p < ∞` source strength.**

At nonzero `x` and `Ax`, the quotient `F(x)=‖Ax‖_p/‖x‖_p` has the
directional gradient printed by Higham. -/
theorem eq15_3_directional (x : Fin n → ℝ)
    (hx : x ≠ 0) (hy : S.P.yof x ≠ 0) :
    HasDirectionalGradientAt S.eq15_3_F (S.eq15_3_gradient x) x := by
  intro h
  have hnum := S.composite_hasDirectionalGradientAt x hy h
  have hden := S.pN_gradient x hx h
  have hxnorm : S.P.pN x ≠ 0 := ne_of_gt (S.pN_pos x hx)
  have hxnorm0 : S.P.pN (fun i => x i + 0 * h i) ≠ 0 := by
    simpa using hxnorm
  have hquot := hnum.div hden hxnorm0
  change HasDerivAt
    (fun t : ℝ => S.eq15_3_F (fun i => x i + t * h i))
    (∑ i : Fin n, S.eq15_3_gradient x i * h i) 0
  convert hquot using 1
  simp only [zero_mul, add_zero]
  unfold eq15_3_gradient
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  rw [show (∑ i : Fin n, S.P.zof x i / S.P.pN x * h i) =
        (∑ i : Fin n, S.P.zof x i * h i) / S.P.pN x by
    calc
      (∑ i : Fin n, S.P.zof x i / S.P.pN x * h i) =
          (S.P.pN x)⁻¹ * (∑ i : Fin n, S.P.zof x i * h i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [div_eq_mul_inv]
        ring
      _ = (∑ i : Fin n, S.P.zof x i * h i) / S.P.pN x := by
        rw [div_eq_mul_inv]
        ring]
  rw [show (∑ i : Fin n,
        S.P.pN (S.P.yof x) / S.P.pN x ^ 2 * S.P.dp x i * h i) =
        (S.P.pN (S.P.yof x) / S.P.pN x ^ 2) *
          (∑ i : Fin n, S.P.dp x i * h i) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  field_simp [hxnorm]

/-- Under Higham's full-rank hypothesis, `Ax ≠ 0` follows from `x ≠ 0`, so
equation (15.3) needs only the hypotheses stated in the source. -/
theorem eq15_3_directional_of_full_rank (x : Fin n → ℝ)
    (hfull : Function.Injective S.P.yof) (hx : x ≠ 0) :
    HasDirectionalGradientAt S.eq15_3_F (S.eq15_3_gradient x) x := by
  apply S.eq15_3_directional x hx
  intro hy0
  apply hx
  apply hfull
  rw [hy0]
  ext i
  simp [PNormPair.yof]

end SmoothPNormPair

/-- The Euclidean specialization of Higham's quotient
`F(x) = ‖Ax‖₂ / ‖x‖₂` from equation (15.3). -/
noncomputable def eq15_3_F_two {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  vecNorm2 ((pNormPair_two hn A).yof x) / vecNorm2 x

/-- The right-hand side of equation (15.3) at `p=q=2`, with
`z = Aᵀ normalize₂(Ax)`. -/
noncomputable def eq15_3_gradient_two {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j =>
    (pNormPair_two hn A).zof x j / vecNorm2 x -
      (vecNorm2 ((pNormPair_two hn A).yof x) / vecNorm2 x ^ 2) *
        normalize2 hn x j

/-- **Equation (15.3), concrete source-strength `p=2` endpoint.**

For `x ≠ 0` and `Ax ≠ 0`, the quotient `F(x)=‖Ax‖₂/‖x‖₂` has directional
gradient
`Aᵀ normalize₂(Ax)/‖x‖₂ - (‖Ax‖₂/‖x‖₂²) normalize₂(x)`.
Both nonzero conditions are exactly the differentiability conditions used by
the displayed formula; no gradient conclusion is assumed. -/
theorem eq15_3_directional_two {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hx : x ≠ 0) (hy : (pNormPair_two hn A).yof x ≠ 0) :
    HasDirectionalGradientAt (eq15_3_F_two hn A)
      (eq15_3_gradient_two hn A x) x := by
  unfold HasDirectionalGradientAt
  intro h
  let P := pNormPair_two hn A
  have haffine : ∀ t : ℝ,
      P.yof (fun i => x i + t * h i) =
        fun i => P.yof x i + t * P.yof h i := by
    intro t
    funext i
    simp only [PNormPair.yof, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hnum0 := vecNorm2_hasDirectionalGradientAt hn (P.yof x) hy (P.yof h)
  have hnum : HasDerivAt
      (fun t : ℝ => vecNorm2 (P.yof (fun i => x i + t * h i)))
      (∑ i : Fin n, normalize2 hn (P.yof x) i * P.yof h i) 0 := by
    convert hnum0 using 1
    funext t
    rw [haffine t]
  have hden := vecNorm2_hasDirectionalGradientAt hn x hx h
  have hxnorm : vecNorm2 x ≠ 0 := ne_of_gt (vecNorm2_pos_of_ne x hx)
  have hxnorm0 : vecNorm2 (fun i => x i + 0 * h i) ≠ 0 := by
    simpa using hxnorm
  have hquot := hnum.div hden hxnorm0
  change HasDerivAt
    (fun t : ℝ => eq15_3_F_two hn A (fun i => x i + t * h i))
    (∑ i : Fin n, eq15_3_gradient_two hn A x i * h i) 0
  convert hquot using 1
  simp only [zero_mul, add_zero]
  have hz : (∑ i : Fin n, normalize2 hn (P.yof x) i * P.yof h i) =
        ∑ i : Fin n, P.zof x i * h i := by
    change (∑ i : Fin n, P.dp (P.yof x) i *
      (∑ j : Fin n, P.A i j * h j)) = _
    exact (P.z_dot x h).symm
  rw [hz]
  unfold eq15_3_gradient_two
  change (∑ i : Fin n,
      (P.zof x i / vecNorm2 x -
        vecNorm2 (P.yof x) / vecNorm2 x ^ 2 * normalize2 hn x i) * h i) = _
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  rw [show (∑ i : Fin n, P.zof x i / vecNorm2 x * h i) =
        (∑ i : Fin n, P.zof x i * h i) / vecNorm2 x by
    calc
      (∑ i : Fin n, P.zof x i / vecNorm2 x * h i) =
          (vecNorm2 x)⁻¹ * (∑ i : Fin n, P.zof x i * h i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [div_eq_mul_inv]
        ring
      _ = (∑ i : Fin n, P.zof x i * h i) / vecNorm2 x := by
        rw [div_eq_mul_inv]
        ring]
  rw [show (∑ i : Fin n,
        vecNorm2 (P.yof x) / vecNorm2 x ^ 2 * normalize2 hn x i * h i) =
        (vecNorm2 (P.yof x) / vecNorm2 x ^ 2) *
          (∑ i : Fin n, normalize2 hn x i * h i) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  field_simp [hxnorm]

end Ch15
end NumStability
