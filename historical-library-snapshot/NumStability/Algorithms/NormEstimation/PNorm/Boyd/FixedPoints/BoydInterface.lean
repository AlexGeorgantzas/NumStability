import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
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
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Carrier.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Duality.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormRectangular
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# NumStability Algorithms NormEstimation PNorm Boyd FixedPoints BoydInterface

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter15BoydBridges` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open Filter Function Set

open scoped BigOperators Topology

theorem complex_rect_action_le_abs_real_action {m n : ℕ}
    {p : ℝ} (hp : 1 ≤ p) (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (z : CVec n) :
    complexVecLpNorm (ENNReal.ofReal p)
        (complexMatrixVecMul (realRectToCMatrix A) z) ≤
      realVecLpNorm p (fun i : Fin m => ∑ j : Fin n, A i j * ‖z j‖) := by
  have hcoord : componentwiseAbsLe
      (complexMatrixVecMul (realRectToCMatrix A) z)
      (realVecToComplex (fun i : Fin m => ∑ j : Fin n, A i j * ‖z j‖)) := by
    intro i
    change ‖∑ j : Fin n, (A i j : ℂ) * z j‖ ≤
      ‖((∑ j : Fin n, A i j * ‖z j‖ : ℝ) : ℂ)‖
    have hsum_nonneg : 0 ≤ ∑ j : Fin n, A i j * ‖z j‖ :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (norm_nonneg _)
    calc
      ‖∑ j : Fin n, (A i j : ℂ) * z j‖ ≤
          ∑ j : Fin n, ‖(A i j : ℂ) * z j‖ := norm_sum_le _ _
      _ = ∑ j : Fin n, A i j * ‖z j‖ := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hA i j)]
      _ = ‖((∑ j : Fin n, A i j * ‖z j‖ : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsum_nonneg]
  exact (complexVecLpNorm_ofReal_monotone (n := m) (p := p) hp
    (complexMatrixVecMul (realRectToCMatrix A) z)
    (realVecToComplex (fun i : Fin m => ∑ j : Fin n, A i j * ‖z j‖)) hcoord).trans_eq rfl

/-- A nonnegative-carrier maximizer realizes the repository's complex induced
matrix `p`-norm.  The complex-to-real direction uses `|Az| ≤ A|z|`; the
reverse direction embeds the real maximizing vector. -/
theorem boydCarrier_maximum_eq_opP {m n : ℕ}
    (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q) (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    {xbar : Fin n → ℝ}
    (hxbar : xbar ∈ boydNonnegativeUnitCarrier p)
    (hmax : ∀ x ∈ boydNonnegativeUnitCarrier p,
      realVecLpNorm p ((RectPNormPair.general hn hpq A).yof x) ≤
        realVecLpNorm p ((RectPNormPair.general hn hpq A).yof xbar)) :
    realVecLpNorm p ((RectPNormPair.general hn hpq A).yof xbar) =
      (RectPNormPair.general hn hpq A).opP := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hpq.lt⟩
  let P := RectPNormPair.general hn hpq A
  let c := realVecLpNorm p (P.yof xbar)
  have hc_le : c ≤ P.opP := by
    have h := P.op_bound xbar
    change realVecLpNorm p (P.yof xbar) ≤
      P.opP * realVecLpNorm p xbar at h
    rw [hxbar.2, mul_one] at h
    exact h
  have hbound : MixedSubordinateMatrixBound
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := m) (ENNReal.ofReal p))
      (realRectToCMatrix A) c := by
    intro z
    by_cases hz : z = 0
    · subst z
      have hsrc : complexVecLpNorm (n := n) (ENNReal.ofReal p)
          (0 : CVec n) = 0 :=
        (complexVecLpNorm_isComplexVectorNorm
          (n := n) (ENNReal.ofReal p)).eq_zero_iff _ |>.2 rfl
      have houtvec : complexMatrixVecMul (realRectToCMatrix A)
          (0 : CVec n) = (0 : CVec m) := by
        funext i
        simp [complexMatrixVecMul]
      have hout : complexVecLpNorm (n := m) (ENNReal.ofReal p)
          (complexMatrixVecMul (realRectToCMatrix A) (0 : CVec n)) = 0 :=
        (complexVecLpNorm_isComplexVectorNorm
          (n := m) (ENNReal.ofReal p)).eq_zero_iff _ |>.2 houtvec
      rw [hout, hsrc, mul_zero]
    · let a : Fin n → ℝ := fun j => ‖z j‖
      let r : ℝ := complexVecLpNorm (ENNReal.ofReal p) z
      have hrpos : 0 < r := by
        have hnorm := complexVecLpNorm_isComplexVectorNorm
          (n := n) (ENNReal.ofReal p)
        exact lt_of_le_of_ne (hnorm.nonneg z)
          (Ne.symm ((hnorm.eq_zero_iff z).not.mpr hz))
      have har : realVecLpNorm p a = r := by
        simpa [a, r, realVecLpNorm, complexAbsVec] using
          (complexVecLpNorm_ofReal_abs_eq hpq.pos z)
      let u : Fin n → ℝ := fun j => r⁻¹ * a j
      have hu : u ∈ boydNonnegativeUnitCarrier p := by
        constructor
        · intro j
          exact mul_nonneg (inv_nonneg.mpr hrpos.le) (norm_nonneg _)
        · rw [show u = fun j => r⁻¹ * a j from rfl,
            realVecLpNorm_smul_real (le_of_lt hpq.lt), har,
            abs_of_pos (inv_pos.mpr hrpos), inv_mul_cancel₀ (ne_of_gt hrpos)]
      have hy_scale : P.yof u = fun i => r⁻¹ * P.yof a i := by
        funext i
        unfold RectPNormPair.yof
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        dsimp [u]
        ring
      have hscaled := hmax u hu
      have hya_le : realVecLpNorm p (P.yof a) ≤ r * c := by
        rw [hy_scale, realVecLpNorm_smul_real (le_of_lt hpq.lt),
          abs_of_pos (inv_pos.mpr hrpos)] at hscaled
        have hscaled' : r⁻¹ * realVecLpNorm p (P.yof a) ≤ c := by
          simpa [c] using hscaled
        have hmul := mul_le_mul_of_nonneg_left hscaled' hrpos.le
        calc
          realVecLpNorm p (P.yof a) =
              r * (r⁻¹ * realVecLpNorm p (P.yof a)) := by
                field_simp
          _ ≤ r * c := hmul
      calc
        complexVecLpNorm (ENNReal.ofReal p)
            (complexMatrixVecMul (realRectToCMatrix A) z) ≤
            realVecLpNorm p (P.yof a) := by
          simpa [P, RectPNormPair.yof, a] using
            complex_rect_action_le_abs_real_action
              (le_of_lt hpq.lt) A hA z
        _ ≤ c * complexVecLpNorm (ENNReal.ofReal p) z := by
          simpa [r, mul_comm] using hya_le
  have hop_le : P.opP ≤ c := by
    have hvalue := complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
      hn p (le_of_lt hpq.lt) (realRectToCMatrix A)
    exact hvalue.2 c hbound
  exact le_antisymm hc_le hop_le

end Ch15
end NumStability
