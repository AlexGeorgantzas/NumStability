import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Seminorm
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
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# NumStability Algorithms NormEstimation PNorm Boyd Scalar BoydLocal

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter15BoydSourceLocal` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open Filter Function Set

open scoped BigOperators Topology

/-- Scalar derivative needed for the Hessian/linearization identity. -/
theorem hasDerivAt_abs_rpow_sub_two_mul_self (p x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => |t| ^ (p - 2) * t)
      ((p - 1) * |x| ^ (p - 2)) x := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have habs := hasDerivAt_abs_neg hxneg
    have hpow := habs.rpow_const
      (p := p - 2) (Or.inl (abs_ne_zero.mpr hx))
    have h := hpow.mul (hasDerivAt_id x)
    convert h using 1
    have habspos : 0 < |x| := abs_pos.mpr hx
    have hx_eq : x = -|x| := by rw [abs_of_neg hxneg]; ring
    rw [hx_eq]
    have hrpow : |x| ^ (p - 3) * |x| = |x| ^ (p - 2) := by
      rw [← Real.rpow_add_one (ne_of_gt habspos) (p - 3)]
      congr 1
      ring
    simp only [abs_neg, abs_abs, id_eq, neg_one_mul, mul_one]
    rw [show p - 2 - 1 = p - 3 by ring]
    calc
      (p - 1) * |x| ^ (p - 2) =
          (p - 2) * |x| ^ (p - 2) + |x| ^ (p - 2) := by ring
      _ = (p - 2) * (|x| ^ (p - 3) * |x|) + |x| ^ (p - 2) := by
        rw [hrpow]
      _ = -(p - 2) * |x| ^ (p - 3) * -|x| + |x| ^ (p - 2) := by
        ring
  · have habs := hasDerivAt_abs_pos hxpos
    have hpow := habs.rpow_const
      (p := p - 2) (Or.inl (abs_ne_zero.mpr hx))
    have h := hpow.mul (hasDerivAt_id x)
    convert h using 1
    have habspos : 0 < |x| := abs_pos.mpr hx
    have hx_eq : x = |x| := by rw [abs_of_pos hxpos]
    rw [hx_eq]
    have hrpow : |x| ^ (p - 3) * |x| = |x| ^ (p - 2) := by
      rw [← Real.rpow_add_one (ne_of_gt habspos) (p - 3)]
      congr 1
      ring
    simp only [abs_abs, id_eq, one_mul, mul_one]
    rw [show p - 2 - 1 = p - 3 by ring]
    calc
      (p - 1) * |x| ^ (p - 2) =
          (p - 2) * |x| ^ (p - 2) + |x| ^ (p - 2) := by ring
      _ = (p - 2) * (|x| ^ (p - 3) * |x|) + |x| ^ (p - 2) := by
        rw [hrpow]
      _ = (p - 2) * |x| ^ (p - 3) * |x| + |x| ^ (p - 2) := by
        ring

lemma boyd_weight_mul_inverse_weight {p a : ℝ} (ha : a ≠ 0) :
    |a| ^ (p - 2) * |a| ^ (2 - p) = 1 := by
  rw [← Real.rpow_add (abs_pos.mpr ha)]
  rw [show p - 2 + (2 - p) = 0 by ring, Real.rpow_zero]

lemma boyd_weight_mul_self {p a : ℝ} (ha : a ≠ 0) :
    |a| ^ (p - 2) * a * a = |a| ^ p := by
  calc
    |a| ^ (p - 2) * a * a = |a| ^ (p - 2) * |a| ^ (2 : ℝ) := by
      rw [Real.rpow_two, sq_abs]
      ring
    _ = |a| ^ p := by
      rw [← Real.rpow_add (abs_pos.mpr ha)]
      congr 1
      ring

lemma boyd_holder_sub_one_mul_sub_one {p q : ℝ}
    (hpq : p.HolderConjugate q) : (p - 1) * (q - 1) = 1 := by
  have h := hpq.sub_one_mul_conj
  nlinarith

lemma boyd_holder_sub_one_mul_sub_two {p q : ℝ}
    (hpq : p.HolderConjugate q) : (p - 1) * (q - 2) = 2 - p := by
  have h := hpq.sub_one_mul_conj
  nlinarith

lemma boyd_abs_dualCoordinate {p a : ℝ} (ha : a ≠ 0) :
    |(|a| ^ (p - 2) * a)| = |a| ^ (p - 1) := by
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg a) _)]
  rw [← Real.rpow_add_one (abs_ne_zero.mpr ha)]
  congr 1
  ring

lemma boyd_dualCoordinate_ne_zero {p a : ℝ} (ha : a ≠ 0) :
    |a| ^ (p - 2) * a ≠ 0 := by
  exact mul_ne_zero (ne_of_gt (Real.rpow_pos_of_pos (abs_pos.mpr ha) _)) ha

lemma boyd_dualCoordinate_abs_rpow_q {p q a : ℝ}
    (hpq : p.HolderConjugate q) (ha : a ≠ 0) :
    |(|a| ^ (p - 2) * a)| ^ q = |a| ^ p := by
  rw [boyd_abs_dualCoordinate (p := p) ha]
  rw [← Real.rpow_mul (abs_nonneg a)]
  rw [hpq.sub_one_mul_conj]

lemma boyd_dualCoordinate_weight {p q a : ℝ}
    (hpq : p.HolderConjugate q) (ha : a ≠ 0) :
    |(|a| ^ (p - 2) * a)| ^ (q - 2) = |a| ^ (2 - p) := by
  rw [boyd_abs_dualCoordinate (p := p) ha]
  rw [← Real.rpow_mul (abs_nonneg a)]
  rw [boyd_holder_sub_one_mul_sub_two hpq]

lemma boyd_dualCoordinate_involution {p q a : ℝ}
    (hpq : p.HolderConjugate q) (ha : a ≠ 0) :
    |(|a| ^ (p - 2) * a)| ^ (q - 2) *
        (|a| ^ (p - 2) * a) = a := by
  rw [boyd_dualCoordinate_weight hpq ha]
  have hw := boyd_weight_mul_inverse_weight (p := p) ha
  calc
    |a| ^ (2 - p) * (|a| ^ (p - 2) * a) =
        (|a| ^ (p - 2) * |a| ^ (2 - p)) * a := by ring
    _ = a := by rw [hw, one_mul]

lemma boyd_scaled_dualCoordinate_weight {p q α a : ℝ}
    (hpq : p.HolderConjugate q) (hα : 0 < α) (ha : a ≠ 0) :
    |α * (|a| ^ (p - 2) * a)| ^ (q - 2) =
      α ^ (q - 2) * |a| ^ (2 - p) := by
  rw [abs_mul, abs_of_pos hα, Real.mul_rpow hα.le (abs_nonneg _)]
  rw [boyd_dualCoordinate_weight hpq ha]

lemma boyd_scaled_dualCoordinate_involution {p q α a : ℝ}
    (hpq : p.HolderConjugate q) (hα : 0 < α) (ha : a ≠ 0) :
    |α * (|a| ^ (p - 2) * a)| ^ (q - 2) *
        (α * (|a| ^ (p - 2) * a)) = α ^ (q - 1) * a := by
  rw [boyd_scaled_dualCoordinate_weight hpq hα ha]
  have hw := boyd_weight_mul_inverse_weight (p := p) ha
  calc
    (α ^ (q - 2) * |a| ^ (2 - p)) *
        (α * (|a| ^ (p - 2) * a)) =
      (α ^ (q - 2) * α) *
        (|a| ^ (2 - p) * (|a| ^ (p - 2) * a)) := by ring
    _ = α ^ (q - 1) * a := by
      rw [show |a| ^ (2 - p) * (|a| ^ (p - 2) * a) = a by
        calc
          |a| ^ (2 - p) * (|a| ^ (p - 2) * a) =
              (|a| ^ (p - 2) * |a| ^ (2 - p)) * a := by ring
          _ = a := by rw [hw, one_mul]]
      rw [show α ^ (q - 2) * α = α ^ (q - 1) by
        calc
          α ^ (q - 2) * α = α ^ (q - 2) * α ^ (1 : ℝ) := by
            rw [Real.rpow_one]
          _ = α ^ ((q - 2) + 1) := (Real.rpow_add hα (q - 2) 1).symm
          _ = α ^ (q - 1) := by congr 1 <;> ring]

lemma boyd_scaled_gradient_coefficient {q α : ℝ}
    (hq : q ≠ 0) (hα : 0 < α) :
    (α ^ q) ^ (q⁻¹ - 1) * α ^ (q - 1) = 1 := by
  rw [← Real.rpow_mul hα.le]
  rw [show q * (q⁻¹ - 1) = 1 - q by field_simp]
  rw [← Real.rpow_add hα]
  rw [show (1 - q) + (q - 1) = 0 by ring, Real.rpow_zero]

lemma boyd_scale_coefficient {p q S : ℝ}
    (hpq : p.HolderConjugate q) (hS : 0 < S) :
    (q - 1) * ((S ^ p⁻¹) ^ q) ^ (q⁻¹ - 1) *
        ((p - 1) * S ^ (p⁻¹ - 1)) * (S ^ p⁻¹) ^ (q - 2) = S⁻¹ := by
  let α := S ^ p⁻¹
  have hα : 0 < α := Real.rpow_pos_of_pos hS _
  have hpow : S ^ (p⁻¹ - 1) = α / S := by
    simpa [α] using Real.rpow_sub_one (ne_of_gt hS) p⁻¹
  have hαstep : α ^ (q - 2) * α = α ^ (q - 1) := by
    calc
      α ^ (q - 2) * α = α ^ (q - 2) * α ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = α ^ ((q - 2) + 1) := (Real.rpow_add hα (q - 2) 1).symm
      _ = α ^ (q - 1) := by congr 1 <;> ring
  have hgrad := boyd_scaled_gradient_coefficient hpq.symm.ne_zero hα
  have hholder := boyd_holder_sub_one_mul_sub_one hpq
  change (q - 1) * (α ^ q) ^ (q⁻¹ - 1) *
      ((p - 1) * S ^ (p⁻¹ - 1)) * α ^ (q - 2) = S⁻¹
  calc
    (q - 1) * (α ^ q) ^ (q⁻¹ - 1) *
        ((p - 1) * S ^ (p⁻¹ - 1)) * α ^ (q - 2) =
      ((p - 1) * (q - 1)) *
        ((α ^ q) ^ (q⁻¹ - 1) * α ^ (q - 1)) * S⁻¹ := by
      rw [hpow]
      rw [div_eq_mul_inv]
      rw [← hαstep]
      ring
    _ = S⁻¹ := by rw [hholder, hgrad, one_mul, one_mul]

end Ch15
end NumStability
