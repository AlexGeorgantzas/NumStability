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
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# NumStability Algorithms NormEstimation PNorm Boyd Differentiation PNormGeneral

Canonical destination for material split out of
`NumStability.Algorithms.PNormPowerMethodGeneralP` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open scoped BigOperators

/-- The finite power sum underlying the concrete `l^p` norm. -/
noncomputable def realLpPowerSum {n : ℕ} (p : ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, |x i| ^ p

/-- The explicit gradient of the finite-dimensional real `l^p` norm away
from zero.  The formula remains total at zero by Lean's `rpow` convention,
but it is only used as a gradient when `x ≠ 0`. -/
noncomputable def realLpGradient {n : ℕ} (p : ℝ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (realLpPowerSum p x) ^ (p⁻¹ - 1) *
    (|x i| ^ (p - 2) * x i)

lemma realLpPowerSum_pos {n : ℕ} {p : ℝ} (hp : 1 < p)
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    0 < realLpPowerSum p x := by
  have hnormpos : 0 < realVecLpNorm p x :=
    realVecLpNorm_pos (le_of_lt hp) hx
  have hsum_nonneg : 0 ≤ realLpPowerSum p x := by
    exact Finset.sum_nonneg
      (fun i _ => Real.rpow_nonneg (abs_nonneg (x i)) p)
  have hsum_ne : realLpPowerSum p x ≠ 0 := by
    intro hzero
    rw [realVecLpNorm_eq_sum_rpow (zero_lt_one.trans hp),
      show (∑ i : Fin n, |x i| ^ p) = realLpPowerSum p x by rfl,
      hzero, Real.zero_rpow (inv_ne_zero (ne_of_gt (zero_lt_one.trans hp)))] at hnormpos
    exact (lt_irrefl 0 hnormpos)
  exact lt_of_le_of_ne hsum_nonneg (Ne.symm hsum_ne)

/-- Direct calculus proof that the concrete finite-dimensional real `l^p`
norm is differentiable away from zero, with its standard gradient. -/
theorem realVecLpNorm_hasDirectionalGradientAt {n : ℕ} {p : ℝ}
    (hp : 1 < p) (x : Fin n → ℝ) (hx : x ≠ 0) :
    HasDirectionalGradientAt (realVecLpNorm p) (realLpGradient p x) x := by
  intro h
  let S : ℝ := realLpPowerSum p x
  let D : ℝ := ∑ i : Fin n, |x i| ^ (p - 2) * x i * h i
  have hsum : HasDerivAt
      (fun t : ℝ => ∑ i : Fin n, |x i + t * h i| ^ p)
      (p * D) 0 := by
    have hterms : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        HasDerivAt (fun t : ℝ => |x i + t * h i| ^ p)
          (p * |x i| ^ (p - 2) * x i * h i) 0 := by
      intro i _hi
      have hline : HasDerivAt (fun t : ℝ => x i + t * h i) (h i) 0 := by
        have hline' := (hasDerivAt_const (x := (0 : ℝ)) (x i)).add
          ((hasDerivAt_id (𝕜 := ℝ) 0).const_mul (h i))
        convert hline' using 1
        · funext t
          simp only [Pi.add_apply, id_eq]
          ring
        · ring
      have hbase : HasDerivAt (fun u : ℝ => |u| ^ p)
          (p * |x i| ^ (p - 2) * x i) (x i + 0 * h i) := by
        simpa using hasDerivAt_abs_rpow (x i) hp
      convert hbase.comp 0 hline using 1 <;> ring
    convert HasDerivAt.fun_sum hterms using 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hSpos : 0 < S := realLpPowerSum_pos hp hx
  have hrpow := hsum.rpow_const (p := p⁻¹) (Or.inl (by
    simpa [S, realLpPowerSum] using ne_of_gt hSpos))
  have hfun :
      (fun t : ℝ => realVecLpNorm p (fun i => x i + t * h i)) =
        (fun t : ℝ =>
          (∑ i : Fin n, |x i + t * h i| ^ p) ^ p⁻¹) := by
    funext t
    exact realVecLpNorm_eq_sum_rpow (zero_lt_one.trans hp) _
  rw [hfun]
  convert hrpow using 1
  unfold realLpGradient
  rw [show (∑ i : Fin n,
      (realLpPowerSum p x) ^ (p⁻¹ - 1) *
        (|x i| ^ (p - 2) * x i) * h i) =
      (realLpPowerSum p x) ^ (p⁻¹ - 1) * D by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring]
  field_simp [ne_of_gt (zero_lt_one.trans hp)]
  <;> unfold realLpPowerSum
  <;> ring_nf

/-- The chosen concrete normalized dual is the actual gradient of the
finite-dimensional real `l^p` norm; this is derived from direct calculus and
Holder duality, not included as interface data. -/
theorem realLpDual_hasDirectionalGradientAt {n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (x : Fin n → ℝ) (hx : x ≠ 0) :
    HasDirectionalGradientAt (realVecLpNorm p) (realLpDual hpq x) x := by
  have hraw := realVecLpNorm_hasDirectionalGradientAt hpq.lt x hx
  have hsub : IsSubgradient (realVecLpNorm p) x (realLpDual hpq x) := by
    intro v
    have hvnonneg : 0 ≤ realVecLpNorm p v := by
      haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
        rw [ENNReal.one_le_ofReal]
        exact le_of_lt hpq.lt⟩
      exact (complexVecLpNorm_isComplexVectorNorm
        (n := n) (ENNReal.ofReal p)).nonneg _
    have hdot : (∑ i : Fin n, realLpDual hpq x i * v i) ≤
        realVecLpNorm p v := by
      calc
        (∑ i : Fin n, realLpDual hpq x i * v i) ≤
            |∑ i : Fin n, realLpDual hpq x i * v i| := le_abs_self _
        _ ≤ realVecLpNorm q (realLpDual hpq x) * realVecLpNorm p v :=
          realVecLpNorm_holder hpq _ _
        _ ≤ 1 * realVecLpNorm p v :=
          mul_le_mul_of_nonneg_right (realLpDual_spec hpq x).1 hvnonneg
        _ = realVecLpNorm p v := one_mul _
    calc
      realVecLpNorm p x +
          (∑ i : Fin n, realLpDual hpq x i * (v i - x i)) =
          ∑ i : Fin n, realLpDual hpq x i * v i := by
            rw [← (realLpDual_spec hpq x).2]
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ ≤ realVecLpNorm p v := hdot
  have heq := unique_subgradient_of_directional_gradient
    (realVecLpNorm p) x (realLpGradient p x) (realLpDual hpq x)
    hraw hsub
  simpa [heq] using hraw

end Ch15
end NumStability
