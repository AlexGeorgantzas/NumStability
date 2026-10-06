import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Sequences
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormGeneral
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# NumStability Algorithms NormEstimation PNorm Duality BoydUniqueness

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter15BoydUniqueness` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open Filter Function Set

open scoped BigOperators Topology

lemma rpow_sub_two_mul_self_eq_rpow_sub_one {a p : ℝ}
    (ha : 0 < a) :
    |a| ^ (p - 2) * a = a ^ (p - 1) := by
  rw [abs_of_pos ha, ← Real.rpow_add_one ha.ne']
  congr 1
  ring

lemma rpow_sub_two_mul_self_eq_rpow_sub_one_of_nonneg {a p : ℝ}
    (hp : 1 < p) (ha : 0 ≤ a) :
    |a| ^ (p - 2) * a = a ^ (p - 1) := by
  rcases ha.eq_or_lt with rfl | ha
  · rw [abs_zero, mul_zero, Real.zero_rpow (sub_ne_zero.mpr (ne_of_gt hp))]
  · exact rpow_sub_two_mul_self_eq_rpow_sub_one ha

lemma rpow_one_sub_mul_rpow_sub_one {a p : ℝ}
    (ha : 0 < a) :
    a ^ (1 - p) * a ^ (p - 1) = 1 := by
  rw [← Real.rpow_add ha]
  rw [show 1 - p + (p - 1) = 0 by ring, Real.rpow_zero a]

lemma rpow_div_rpow_cancel {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    (a / b) ^ p * b ^ p = a ^ p := by
  rw [Real.div_rpow ha hb.le, div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hb p))]

lemma realLpPowerSum_eq_one_of_unit {n : ℕ} {p : ℝ} (hp : 0 < p)
    {x : Fin n → ℝ} (hxunit : realVecLpNorm p x = 1) :
    realLpPowerSum p x = 1 := by
  have hsum_nonneg : 0 ≤ realLpPowerSum p x :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg (x i)) p
  have hformula := realVecLpNorm_eq_sum_rpow hp x
  have hrpow : (realLpPowerSum p x) ^ p⁻¹ = (1 : ℝ) ^ p⁻¹ := by
    simpa [realLpPowerSum, hxunit] using hformula.symm
  exact (Real.rpow_left_inj hsum_nonneg zero_le_one
    (inv_ne_zero (ne_of_gt hp))).mp hrpow

lemma realLpGradient_coord_eq_rpow_sub_one_of_pos_unit {n : ℕ}
    {p : ℝ} (hp : 1 < p) {x : Fin n → ℝ}
    (hxunit : realVecLpNorm p x = 1) (i : Fin n) (hxi : 0 < x i) :
    realLpGradient p x i = (x i) ^ (p - 1) := by
  rw [realLpGradient, realLpPowerSum_eq_one_of_unit (zero_lt_one.trans hp)
    hxunit, Real.one_rpow, one_mul,
    rpow_sub_two_mul_self_eq_rpow_sub_one hxi]

end Ch15
end NumStability
