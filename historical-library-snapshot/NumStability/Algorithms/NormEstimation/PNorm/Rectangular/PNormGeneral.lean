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
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# NumStability Algorithms NormEstimation PNorm Rectangular PNormGeneral

Canonical destination for material split out of
`NumStability.Algorithms.PNormPowerMethodGeneralP` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open scoped BigOperators

noncomputable def realRectMatVec {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => ∑ j : Fin n, A i j * x j

noncomputable def realRectTransposeVec {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (u : Fin m → ℝ) : Fin n → ℝ :=
  fun j => ∑ i : Fin m, A i j * u i

lemma realRectTranspose_pairing {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (u : Fin m → ℝ)
    (v : Fin n → ℝ) :
    (∑ j : Fin n, realRectTransposeVec A u j * v j) =
      ∑ i : Fin m, u i * realRectMatVec A v i := by
  unfold realRectTransposeVec realRectMatVec
  calc
    (∑ j : Fin n, (∑ i : Fin m, A i j * u i) * v j) =
        ∑ j : Fin n, ∑ i : Fin m, (A i j * u i) * v j := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [Finset.sum_mul]
    _ = ∑ i : Fin m, ∑ j : Fin n, (A i j * u i) * v j :=
      Finset.sum_comm
    _ = ∑ i : Fin m, u i * ∑ j : Fin n, A i j * v j := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring

lemma realRectMatVec_add_smul {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ) (t : ℝ) :
    realRectMatVec A (fun j => x j + t * h j) =
      fun i => realRectMatVec A x i + t * realRectMatVec A h i := by
  funext i
  unfold realRectMatVec
  calc
    (∑ j : Fin n, A i j * (x j + t * h j)) =
        ∑ j : Fin n, (A i j * x j + t * (A i j * h j)) := by
          apply Finset.sum_congr rfl
          intro j _hj
          ring
    _ = (∑ j : Fin n, A i j * x j) +
        ∑ j : Fin n, t * (A i j * h j) := Finset.sum_add_distrib
    _ = (∑ j : Fin n, A i j * x j) +
        t * ∑ j : Fin n, A i j * h j := by rw [Finset.mul_sum]

/-- Chain rule for the literal rectangular numerator `x |-> ||A x||_p`. -/
theorem realRectLpComposite_hasDirectionalGradientAt {m n : ℕ}
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hy : realRectMatVec A x ≠ 0) :
    HasDirectionalGradientAt
      (fun v => realVecLpNorm p (realRectMatVec A v))
      (realRectTransposeVec A (realLpDual hpq (realRectMatVec A x))) x := by
  intro h
  have hbase := realLpDual_hasDirectionalGradientAt hpq
    (realRectMatVec A x) hy (realRectMatVec A h)
  convert hbase using 1
  · funext t
    change realVecLpNorm p (realRectMatVec A (fun i => x i + t * h i)) = _
    rw [realRectMatVec_add_smul]
  · exact realRectTranspose_pairing A _ h

/-- The transpose dual produced from `A x` is a global subgradient of the
literal rectangular map `x |-> ||A x||_p`. -/
theorem realRectLpComposite_isSubgradient {m n : ℕ}
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    IsSubgradient (fun v => realVecLpNorm p (realRectMatVec A v)) x
      (realRectTransposeVec A (realLpDual hpq (realRectMatVec A x))) := by
  intro v
  have hbase := realLpDual_isSubgradient hpq (realRectMatVec A x)
    (realRectMatVec A v)
  calc
    realVecLpNorm p (realRectMatVec A x) +
        (∑ j : Fin n,
          realRectTransposeVec A (realLpDual hpq (realRectMatVec A x)) j *
            (v j - x j)) =
      realVecLpNorm p (realRectMatVec A x) +
        (∑ i : Fin m, realLpDual hpq (realRectMatVec A x) i *
          (realRectMatVec A v i - realRectMatVec A x i)) := by
            congr 1
            rw [realRectTranspose_pairing]
            apply Finset.sum_congr rfl
            intro i _hi
            congr 1
            unfold realRectMatVec
            calc
              (∑ j : Fin n, A i j * (v j - x j)) =
                  ∑ j : Fin n, (A i j * v j - A i j * x j) := by
                    apply Finset.sum_congr rfl
                    intro j _hj
                    ring
              _ = (∑ j : Fin n, A i j * v j) -
                  ∑ j : Fin n, A i j * x j := by
                    rw [Finset.sum_sub_distrib]
    _ ≤ realVecLpNorm p (realRectMatVec A v) := hbase

end Ch15
end NumStability
