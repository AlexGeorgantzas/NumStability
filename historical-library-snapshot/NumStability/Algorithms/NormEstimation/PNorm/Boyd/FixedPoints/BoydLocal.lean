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
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Carrier.BoydLocal
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Scalar.BoydLocal
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# NumStability Algorithms NormEstimation PNorm Boyd FixedPoints BoydLocal

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

/-- Raw stationary scaling identifies the actual outer input of Boyd's
normalized update. -/
theorem boyd_stationarity_inner_vector {m n : ℕ} {p : ℝ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hSpos : 0 < realLpPowerSum p (boydRectActionCLM A x))
    (hstationary : ∀ j,
      (∑ i : Fin m, A i j *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i)) =
      realLpPowerSum p (boydRectActionCLM A x) *
        (|x j| ^ (p - 2) * x j)) :
    boydRectTransposeActionCLM A
        (realLpGradient p (boydRectActionCLM A x)) =
      fun j => (realLpPowerSum p (boydRectActionCLM A x)) ^ p⁻¹ *
        (|x j| ^ (p - 2) * x j) := by
  let S := realLpPowerSum p (boydRectActionCLM A x)
  have hS : S ≠ 0 := ne_of_gt hSpos
  funext j
  rw [boydRectTransposeActionCLM_apply]
  unfold realLpGradient
  change (∑ i : Fin m, A i j *
      (S ^ (p⁻¹ - 1) *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i))) = _
  calc
    (∑ i : Fin m, A i j *
      (S ^ (p⁻¹ - 1) *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i))) =
      S ^ (p⁻¹ - 1) *
        (∑ i : Fin m, A i j *
          (|boydRectActionCLM A x i| ^ (p - 2) *
            boydRectActionCLM A x i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = S ^ (p⁻¹ - 1) *
        (S * (|x j| ^ (p - 2) * x j)) := by
      rw [hstationary j]
    _ = S ^ p⁻¹ * (|x j| ^ (p - 2) * x j) := by
      rw [Real.rpow_sub_one hS]
      field_simp

/-- The outer coordinate regularity needed by Lemma 2 follows from positive
stationary scaling and nonzero coordinates of `x`; it is not an extra
assumption. -/
theorem boyd_stationarity_outer_coord_ne {m n : ℕ} {p : ℝ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hSpos : 0 < realLpPowerSum p (boydRectActionCLM A x))
    (hstationary : ∀ j,
      (∑ i : Fin m, A i j *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i)) =
      realLpPowerSum p (boydRectActionCLM A x) *
        (|x j| ^ (p - 2) * x j)) :
    ∀ j, boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)) j ≠ 0 := by
  intro j
  rw [boyd_stationarity_inner_vector A x hSpos hstationary]
  exact mul_ne_zero
    (ne_of_gt (Real.rpow_pos_of_pos hSpos _))
    (boyd_dualCoordinate_ne_zero (p := p) (hxcoord j))

/-- Raw stationarity gives Boyd's radial eigenidentity `B x = S x`. -/
theorem boyd_stationarity_Bx {m n : ℕ} {p : ℝ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hstationary : ∀ j,
      (∑ i : Fin m, A i j *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i)) =
      realLpPowerSum p (boydRectActionCLM A x) *
        (|x j| ^ (p - 2) * x j)) :
    boydLemma3B p A x x = fun j =>
      realLpPowerSum p (boydRectActionCLM A x) * x j := by
  funext j
  unfold boydLemma3B
  rw [show (∑ i : Fin m, A i j *
      |boydRectActionCLM A x i| ^ (p - 2) *
        boydRectActionCLM A x i) =
      ∑ i : Fin m, A i j *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i) by
    apply Finset.sum_congr rfl
    intro i _hi
    ring]
  rw [hstationary j]
  have hw := boyd_weight_mul_inverse_weight (p := p) (hxcoord j)
  calc
    |x j| ^ (2 - p) *
        (realLpPowerSum p (boydRectActionCLM A x) *
          (|x j| ^ (p - 2) * x j)) =
      realLpPowerSum p (boydRectActionCLM A x) *
        (|x j| ^ (p - 2) * |x j| ^ (2 - p)) * x j := by ring
    _ = realLpPowerSum p (boydRectActionCLM A x) * x j := by
      rw [hw, mul_one]

/-- The same raw stationarity and unit normalization give the fixed-point
equation for the explicit smooth update; fixedness is derived, not assumed. -/
theorem boydSmoothRectUpdate_eq_of_stationarity
    {m n : ℕ} {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hunit : realLpPowerSum p x = 1)
    (hSpos : 0 < realLpPowerSum p (boydRectActionCLM A x))
    (hstationary : ∀ j,
      (∑ i : Fin m, A i j *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i)) =
      realLpPowerSum p (boydRectActionCLM A x) *
        (|x j| ^ (p - 2) * x j)) :
    boydSmoothRectUpdate (p := p) (q := q) A x = x := by
  let S := realLpPowerSum p (boydRectActionCLM A x)
  let α := S ^ p⁻¹
  have hα : 0 < α := Real.rpow_pos_of_pos hSpos _
  rw [show boydSmoothRectUpdate (p := p) (q := q) A x =
      realLpGradient q
        (boydRectTransposeActionCLM A
          (realLpGradient p (boydRectActionCLM A x))) by rfl]
  rw [boyd_stationarity_inner_vector A x hSpos hstationary]
  exact realLpGradient_scaled_dual_eq hpq x hα hxcoord hunit

end Ch15
end NumStability
