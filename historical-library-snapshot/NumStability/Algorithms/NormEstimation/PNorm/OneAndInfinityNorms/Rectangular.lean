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
import NumStability.Algorithms.NormEstimation.OneNorm.PowerMethod.CondEstimation
import NumStability.Algorithms.NormEstimation.OneNorm.PowerMethod.PNormPowerMethod
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormRectangular
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# Rectangular

Canonical destination for the frozen declaration block of
`NumStability.Algorithms.NormEstimation.PNorm.Endpoints.PNormRectangular`, routed by wave R02 of the August 2026 repository reorganization
completion phase. Declaration names, kinds, visibilities, signatures and
proofs are unchanged; only the module they live in has changed. Private
declarations keep their logical names and are re-mangled against this module,
exactly as recorded in the reviewed private normalization.
-/

/-!
# NumStability Algorithms NormEstimation PNorm Endpoints PNormRectangular

Canonical destination for material split out of
`NumStability.Algorithms.PNormPowerMethodRect` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

open Ch15

namespace RectPNormPair

variable {m n : ℕ} (P : RectPNormPair m n)

/-- Exact rectangular induced 1-norm inequality. -/
theorem oneNormVec_rectMatVec_le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    oneNormVec (fun i => ∑ j : Fin n, A i j * x j) ≤
      oneNormRect A * oneNormVec x := by
  unfold oneNormVec
  calc
    (∑ i : Fin m, |∑ j : Fin n, A i j * x j|) ≤
        ∑ i : Fin m, ∑ j : Fin n, |A i j * x j| :=
      Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ j : Fin n, |x j| * ∑ i : Fin m, |A i j| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _hj
      simp_rw [abs_mul]
      rw [← Finset.sum_mul]
      ring
    _ ≤ ∑ j : Fin n, |x j| * oneNormRect A :=
      Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left (col_sum_le_oneNormRect A j) (abs_nonneg _))
    _ = oneNormRect A * ∑ j : Fin n, |x j| := by
      rw [← Finset.sum_mul]
      ring

/-- Exact rectangular induced infinity-norm inequality. -/
theorem infNormVec_rectMatVec_le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    infNormVec (fun i => ∑ j : Fin n, A i j * x j) ≤
      infNormRect A * infNormVec x := by
  apply infNormVec_le_of_abs_le
  · intro i
    calc
      |∑ j : Fin n, A i j * x j| ≤ ∑ j : Fin n, |A i j * x j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n, |A i j| * |x j| := by simp_rw [abs_mul]
      _ ≤ ∑ j : Fin n, |A i j| * infNormVec x :=
        Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_left (abs_le_infNormVec x j) (abs_nonneg _))
      _ = (∑ j : Fin n, |A i j|) * infNormVec x := by rw [Finset.sum_mul]
      _ ≤ infNormRect A * infNormVec x :=
        mul_le_mul_of_nonneg_right (row_sum_le_infNormRect A i)
          (infNormVec_nonneg x)
  · exact mul_nonneg (infNormRect_nonneg A) (infNormVec_nonneg x)

/-- Literal rectangular endpoint instance `p=1`, `q=infinity`. -/
noncomputable def one {m n : ℕ} (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) : RectPNormPair m n where
  A := A
  pIn := oneNormVec
  qIn := infNormVec
  pOut := oneNormVec
  qOut := infNormVec
  opP := oneNormRect A
  dpOut := signVec
  dqIn := dualq_one hn
  pIn_nonneg := oneNormVec_nonneg
  pOut_nonneg := oneNormVec_nonneg
  dpOut_attains := sign_attains_one
  dpOut_qunit := sign_qunit_one
  dqIn_attains := dualq_one_attains hn
  dqIn_punit := dualq_one_punit hn
  holderIn := holder_one
  holderOut := holder_one
  op_bound := oneNormVec_rectMatVec_le A

lemma signVec_infNorm_eq_one {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    infNormVec (signVec x) = 1 := by
  apply le_antisymm (sign_qunit_one x)
  let i0 : Fin n := ⟨0, hn⟩
  have h := abs_le_infNormVec (signVec x) i0
  simpa [abs_signVec] using h

/-- Holder inequality in the orientation `l^1`-dual against `l^infinity`. -/
lemma holder_inf {n : ℕ} (u v : Fin n → ℝ) :
    (∑ i : Fin n, u i * v i) ≤ oneNormVec u * infNormVec v := by
  have h := holder_one v u
  calc
    (∑ i : Fin n, u i * v i) = ∑ i : Fin n, v i * u i := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ ≤ infNormVec v * oneNormVec u := h
    _ = oneNormVec u * infNormVec v := by ring

/-- Literal rectangular endpoint instance `p=infinity`, `q=1`. -/
noncomputable def infinity {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) : RectPNormPair m n where
  A := A
  pIn := infNormVec
  qIn := oneNormVec
  pOut := infNormVec
  qOut := oneNormVec
  opP := infNormRect A
  dpOut := dualq_one hm
  dqIn := signVec
  pIn_nonneg := infNormVec_nonneg
  pOut_nonneg := infNormVec_nonneg
  dpOut_attains := dualq_one_attains hm
  dpOut_qunit := fun v => by rw [dualq_one_punit hm]
  dqIn_attains := sign_attains_one
  dqIn_punit := signVec_infNorm_eq_one hn
  holderIn := holder_inf
  holderOut := holder_inf
  op_bound := infNormVec_rectMatVec_le A

end RectPNormPair
end NumStability
