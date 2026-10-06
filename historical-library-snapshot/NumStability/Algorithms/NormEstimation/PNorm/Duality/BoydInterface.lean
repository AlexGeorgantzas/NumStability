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
import NumStability.Algorithms.NormEstimation.OneNorm.FiniteIndex.Basic
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormPowerMethod
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# NumStability Algorithms NormEstimation PNorm Duality BoydInterface

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

/-- In the smooth range, the normalized dual selected by Holder attainment is
the explicit gradient of the finite-dimensional real `l^p` norm.  This
extracts an equality that was previously only used internally in the proof of
`realLpDual_hasDirectionalGradientAt`. -/
theorem realLpDual_eq_realLpGradient {n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (x : Fin n → ℝ) (hx : x ≠ 0) :
    realLpDual hpq x = realLpGradient p x := by
  have hdual := realLpDual_hasDirectionalGradientAt hpq x hx
  have hgrad := realVecLpNorm_hasDirectionalGradientAt hpq.lt x hx
  funext i
  have hi := (hdual (basisVec i)).unique (hgrad (basisVec i))
  simpa [basisVec] using hi

/-- A positive coordinate of a nonzero vector gives a positive coordinate of
the explicit smooth `l^p` gradient. -/
theorem realLpGradient_pos_of_pos_coord {n : ℕ} {p : ℝ}
    (hp : 1 < p) (x : Fin n → ℝ) (hx : x ≠ 0) (i : Fin n)
    (hi : 0 < x i) :
    0 < realLpGradient p x i := by
  have hsum : 0 < realLpPowerSum p x := realLpPowerSum_pos hp hx
  have hsumPow : 0 < (realLpPowerSum p x) ^ (p⁻¹ - 1) :=
    Real.rpow_pos_of_pos hsum _
  have habs : 0 < |x i| := abs_pos.mpr (ne_of_gt hi)
  have hcoordPow : 0 < |x i| ^ (p - 2) :=
    Real.rpow_pos_of_pos habs _
  unfold realLpGradient
  exact mul_pos hsumPow (mul_pos hcoordPow hi)

/-- A nonnegative coordinate gives a nonnegative coordinate of the smooth
`l^p` gradient (away from the zero vector). -/
theorem realLpGradient_nonneg_of_nonneg_coord {n : ℕ} {p : ℝ}
    (hp : 1 < p) (x : Fin n → ℝ) (hx : x ≠ 0) (i : Fin n)
    (hi : 0 ≤ x i) :
    0 ≤ realLpGradient p x i := by
  rcases hi.eq_or_lt with hzero | hpos
  · have hxi : x i = 0 := hzero.symm
    simp [realLpGradient, hxi]
  · exact (realLpGradient_pos_of_pos_coord hp x hx i hpos).le

/-- The canonical normalized dual of a strictly positive vector is strictly
positive coordinatewise. -/
theorem realLpDual_pos_of_pos {n : ℕ} (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q) (x : Fin n → ℝ)
    (hxpos : ∀ i, 0 < x i) :
    ∀ i, 0 < realLpDual hpq x i := by
  have hx : x ≠ 0 := by
    intro hzero
    let i0 : Fin n := ⟨0, hn⟩
    have hi := congrFun hzero i0
    exact (ne_of_gt (hxpos i0)) (by simpa using hi)
  rw [realLpDual_eq_realLpGradient hpq x hx]
  intro i
  exact realLpGradient_pos_of_pos_coord hpq.lt x hx i (hxpos i)

/-- The smooth normalized dual of a nonzero nonnegative vector is
nonnegative coordinatewise. -/
theorem realLpDual_nonneg_of_nonneg {n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (x : Fin n → ℝ) (hx : x ≠ 0)
    (hxnonneg : ∀ i, 0 ≤ x i) :
    ∀ i, 0 ≤ realLpDual hpq x i := by
  rw [realLpDual_eq_realLpGradient hpq x hx]
  intro i
  exact realLpGradient_nonneg_of_nonneg_coord hpq.lt x hx i (hxnonneg i)

/-- The total unit dual agrees with the smooth dual, and hence is positive,
away from zero. -/
theorem realLpDualUnit_pos_of_pos {n : ℕ} (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q) (x : Fin n → ℝ)
    (hxpos : ∀ i, 0 < x i) :
    ∀ i, 0 < realLpDualUnit hn hpq x i := by
  have hx : x ≠ 0 := by
    intro hzero
    let i0 : Fin n := ⟨0, hn⟩
    have hi := congrFun hzero i0
    exact (ne_of_gt (hxpos i0)) (by simpa using hi)
  simpa [realLpDualUnit, hx] using realLpDual_pos_of_pos hn hpq x hxpos

/-- Continuity of the concrete finite-dimensional real `l^p` norm in the
smooth range.  This is used below to make the Algorithm 15.1 objective an
actual Lyapunov function, rather than an abstract scalar interface. -/
theorem continuous_realVecLpNorm {n : ℕ} {p : ℝ} (hp : 0 < p) :
    Continuous (realVecLpNorm (n := n) p) := by
  rw [show realVecLpNorm (n := n) p =
      fun x : Fin n → ℝ => (∑ i : Fin n, |x i| ^ p) ^ p⁻¹ by
    funext x
    exact realVecLpNorm_eq_sum_rpow hp x]
  have hsum : Continuous (fun x : Fin n → ℝ =>
      ∑ i : Fin n, |x i| ^ p) := by
    apply continuous_finset_sum
    intro i _hi
    exact (continuous_apply i).abs.rpow_const (fun _ => Or.inr hp.le)
  exact hsum.rpow_const (fun _ => Or.inr (inv_nonneg.mpr hp.le))

/-- Real scalar homogeneity of the concrete finite-dimensional `l^p` norm. -/
theorem realVecLpNorm_smul_real {n : ℕ} {p : ℝ} (hp : 1 ≤ p)
    (c : ℝ) (x : Fin n → ℝ) :
    realVecLpNorm p (fun i => c * x i) = |c| * realVecLpNorm p x := by
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  have h := (complexVecLpNorm_isComplexVectorNorm
    (n := n) (ENNReal.ofReal p)).smul (c : ℂ)
      (fun i : Fin n => (x i : ℂ))
  simpa [realVecLpNorm, complexVecSMul, Complex.norm_real,
    Real.norm_eq_abs] using h

/-- Uniqueness of the Holder normer in the smooth range.  A unit `p`-norm
vector attaining the dual pairing against nonzero `z` is the canonical
normalized `q`-dual of `z`. -/
theorem realLpNormer_eq_dual {n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (z x : Fin n → ℝ)
    (hz : z ≠ 0) (hxunit : realVecLpNorm p x = 1)
    (hattain : (∑ i : Fin n, x i * z i) = realVecLpNorm q z) :
    x = realLpDual hpq.symm z := by
  have hsub : IsSubgradient (realVecLpNorm q) z x := by
    intro v
    have hvnonneg : 0 ≤ realVecLpNorm q v := by
      haveI : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
        rw [ENNReal.one_le_ofReal]
        exact le_of_lt hpq.symm.lt⟩
      exact (complexVecLpNorm_isComplexVectorNorm
        (n := n) (ENNReal.ofReal q)).nonneg _
    have hdot : (∑ i : Fin n, x i * v i) ≤ realVecLpNorm q v := by
      calc
        (∑ i : Fin n, x i * v i) ≤ |∑ i : Fin n, x i * v i| :=
          le_abs_self _
        _ ≤ realVecLpNorm p x * realVecLpNorm q v :=
          realVecLpNorm_holder hpq.symm x v
        _ = realVecLpNorm q v := by rw [hxunit, one_mul]
    calc
      realVecLpNorm q z + (∑ i : Fin n, x i * (v i - z i))
          = ∑ i : Fin n, x i * v i := by
            rw [← hattain]
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ ≤ realVecLpNorm q v := hdot
  exact unique_subgradient_of_directional_gradient
    (realVecLpNorm q) z (realLpDual hpq.symm z) x
    (realLpDual_hasDirectionalGradientAt hpq.symm z hz) hsub

/-- A signed positive real power written without a discontinuous sign
function. -/
noncomputable def realLpSignedPower (r : ℝ) (t : ℝ) : ℝ :=
  (max t 0) ^ r - (max (-t) 0) ^ r

theorem continuous_realLpSignedPower {r : ℝ} (hr : 0 ≤ r) :
    Continuous (realLpSignedPower r) := by
  apply Continuous.sub
  · exact (continuous_id.max continuous_const).rpow_const
      (fun _ => Or.inr hr)
  · exact (continuous_id.neg.max continuous_const).rpow_const
      (fun _ => Or.inr hr)

theorem realLpGradient_coord_eq_signedPower {p t : ℝ} (hp : 1 < p) :
    |t| ^ (p - 2) * t = realLpSignedPower (p - 1) t := by
  by_cases ht0 : t = 0
  · subst t
    simp [realLpSignedPower, Real.zero_rpow (sub_pos.mpr hp).ne']
  rcases lt_or_gt_of_ne ht0 with ht | ht
  · have hnegpos : 0 < -t := neg_pos.mpr ht
    have habs : |t| = -t := abs_of_neg ht
    have hpow : (-t) ^ (p - 2) * (-t) = (-t) ^ (p - 1) := by
      calc
        (-t) ^ (p - 2) * (-t) =
            (-t) ^ (p - 2) * (-t) ^ (1 : ℝ) := by
              rw [Real.rpow_one]
        _ = (-t) ^ ((p - 2) + 1) :=
          (Real.rpow_add hnegpos (p - 2) 1).symm
        _ = (-t) ^ (p - 1) := by congr 1; ring
    rw [habs]
    simp [realLpSignedPower, le_of_lt ht, le_of_lt hnegpos,
      Real.zero_rpow (sub_pos.mpr hp).ne']
    nlinarith
  · have habs : |t| = t := abs_of_pos ht
    have hpow : t ^ (p - 2) * t = t ^ (p - 1) := by
      calc
        t ^ (p - 2) * t = t ^ (p - 2) * t ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = t ^ ((p - 2) + 1) :=
          (Real.rpow_add ht (p - 2) 1).symm
        _ = t ^ (p - 1) := by congr 1; ring
    rw [habs, hpow]
    simp [realLpSignedPower, le_of_lt ht, le_of_lt (neg_neg_of_pos ht),
      Real.zero_rpow (sub_pos.mpr hp).ne']

theorem continuous_realLpGradient_coordFactor {p : ℝ} (hp : 1 < p) :
    Continuous (fun t : ℝ => |t| ^ (p - 2) * t) := by
  rw [show (fun t : ℝ => |t| ^ (p - 2) * t) =
      realLpSignedPower (p - 1) by
    funext t
    exact realLpGradient_coord_eq_signedPower hp]
  exact continuous_realLpSignedPower (sub_nonneg.mpr (le_of_lt hp))

theorem continuous_realLpPowerSum {n : ℕ} {p : ℝ} (hp : 0 < p) :
    Continuous (realLpPowerSum (n := n) p) := by
  unfold realLpPowerSum
  apply continuous_finset_sum
  intro i _hi
  exact (continuous_apply i).abs.rpow_const (fun _ => Or.inr hp.le)

theorem continuousAt_realLpGradient {n : ℕ} {p : ℝ} (hp : 1 < p)
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    ContinuousAt (realLpGradient p) x := by
  apply continuousAt_pi'
  intro i
  unfold realLpGradient
  have hsumpos : 0 < realLpPowerSum p x := realLpPowerSum_pos hp hx
  have hscale : ContinuousAt
      (fun y : Fin n → ℝ => (realLpPowerSum p y) ^ (p⁻¹ - 1)) x :=
    (continuous_realLpPowerSum (zero_lt_one.trans hp)).continuousAt.rpow_const
      (Or.inl (ne_of_gt hsumpos))
  have hcoord : ContinuousAt
      (fun y : Fin n → ℝ => |y i| ^ (p - 2) * y i) x :=
    (continuous_realLpGradient_coordFactor hp).continuousAt.comp
      (continuousAt_apply i x)
  exact hscale.mul hcoord

theorem continuousAt_realLpDual {n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) {x : Fin n → ℝ} (hx : x ≠ 0) :
    ContinuousAt (realLpDual hpq) x := by
  have heq : Filter.EventuallyEq (nhds x) (realLpDual hpq) (realLpGradient p) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact realLpDual_eq_realLpGradient hpq y hy
  exact (continuousAt_congr heq).2 (continuousAt_realLpGradient hpq.lt hx)

theorem continuousAt_realLpDualUnit {n : ℕ} (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q) {x : Fin n → ℝ} (hx : x ≠ 0) :
    ContinuousAt (realLpDualUnit hn hpq) x := by
  have heq : Filter.EventuallyEq (nhds x)
      (realLpDualUnit hn hpq) (realLpDual hpq) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp [realLpDualUnit, hy]
  exact (continuousAt_congr heq).2 (continuousAt_realLpDual hpq hx)

end Ch15
end NumStability
