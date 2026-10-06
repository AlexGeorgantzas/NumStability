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
import NumStability.Algorithms.NormEstimation.OneNorm.FiniteIndex.Basic
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Carrier.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Uniqueness.Basic
import NumStability.Algorithms.NormEstimation.PNorm.Duality.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Duality.BoydUniqueness
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormRectangular
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification
import NumStability.Source.Higham.Chapter15.Lemma02.PNormPowerMethod.BoydInterface
import NumStability.Source.Higham.Chapter15.Lemma02.PNormPowerMethod.PNormRectangular

/-!
# Chapter15 Lemma02 PNormPowerMethod BoydUniqueness

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

/-- At a positive normalized fixed point, the concrete adjoint vector is the
objective norm times the coordinatewise `(p-1)` power. -/
theorem rect_general_zof_coord_eq_norm_mul_rpow_of_fixed
    {m n : ℕ} [Nontrivial (Fin n)] (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ))
    {x : Fin n → ℝ} (hx : x ∈ boydNonnegativeUnitCarrier p)
    (hfixed : (RectPNormPair.general hn hpq A).xnext x = x)
    (j : Fin n) :
    (RectPNormPair.general hn hpq A).zof x j =
      realVecLpNorm p ((RectPNormPair.general hn hpq A).yof x) *
        (x j) ^ (p - 1) := by
  let P := RectPNormPair.general hn hpq A
  let y := P.yof x
  let z := P.zof x
  have hxpos : ∀ k, 0 < x k :=
    boydCarrier_fixedPoint_pos hn hpq A hA hGram hx hfixed
  have hyne : y ≠ 0 :=
    rect_general_yof_ne_zero_of_mem_boydCarrier hn hpq A hA hGram hx
  have hzne : z ≠ 0 :=
    rect_general_zof_ne_zero_of_mem_boydCarrier hn hpq A hA hGram hx
  have hynormpos : 0 < realVecLpNorm p y :=
    realVecLpNorm_pos (le_of_lt hpq.lt) hyne
  have hfixedDual : realLpDual hpq.symm z = x := by
    have hfixed' : realLpDualUnit hn hpq.symm z = x := hfixed
    simpa [realLpDualUnit, hzne] using hfixed'
  have hpairZ : (∑ k : Fin n, x k * z k) = realVecLpNorm q z := by
    rw [← hfixedDual]
    exact (realLpDual_spec hpq.symm z).2
  have hnormZ : realVecLpNorm q z = realVecLpNorm p y := by
    rw [← hpairZ]
    calc
      (∑ k : Fin n, x k * z k) = ∑ k : Fin n, z k * x k := by
        apply Finset.sum_congr rfl
        intro k _hk
        ring
      _ = realVecLpNorm p y := P.higham15_lemma15_2a_rectangular x
  let d : Fin n → ℝ := fun k => (realVecLpNorm p y)⁻¹ * z k
  have hdunit : realVecLpNorm q d = 1 := by
    rw [show d = fun k => (realVecLpNorm p y)⁻¹ * z k from rfl,
      realVecLpNorm_smul_real (le_of_lt hpq.symm.lt), hnormZ,
      abs_of_pos (inv_pos.mpr hynormpos), inv_mul_cancel₀ (ne_of_gt hynormpos)]
  have hPpair : (∑ k : Fin n, z k * x k) = realVecLpNorm p y := by
    simpa [P, y, z, RectPNormPair.general] using
      P.higham15_lemma15_2a_rectangular x
  have hdattain : (∑ k : Fin n, d k * x k) = realVecLpNorm p x := by
    change (∑ k : Fin n, (realVecLpNorm p y)⁻¹ * z k * x k) =
      realVecLpNorm p x
    calc
      (∑ k : Fin n, (realVecLpNorm p y)⁻¹ * z k * x k) =
          (realVecLpNorm p y)⁻¹ * ∑ k : Fin n, z k * x k := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _hk
            ring
      _ = (realVecLpNorm p y)⁻¹ * realVecLpNorm p y := by
        rw [hPpair]
      _ = realVecLpNorm p x := by
        rw [inv_mul_cancel₀ (ne_of_gt hynormpos), hx.2]
  have hddual : d = realLpDual hpq x :=
    realLpNormer_eq_dual hpq.symm x d
      (boydCarrier_ne_zero (le_of_lt hpq.lt) hx) hdunit hdattain
  have hdgrad : d j = (x j) ^ (p - 1) := by
    rw [hddual, realLpDual_eq_realLpGradient hpq x
      (boydCarrier_ne_zero (le_of_lt hpq.lt) hx)]
    exact realLpGradient_coord_eq_rpow_sub_one_of_pos_unit hpq.lt hx.2 j (hxpos j)
  change z j = realVecLpNorm p y * (x j) ^ (p - 1)
  have hscaled := congrArg (fun t : ℝ => realVecLpNorm p y * t) hdgrad
  change realVecLpNorm p y * ((realVecLpNorm p y)⁻¹ * z j) =
    realVecLpNorm p y * (x j) ^ (p - 1) at hscaled
  rw [mul_inv_cancel_left₀ (ne_of_gt hynormpos)] at hscaled
  exact hscaled

/-- The unnormalized nonlinear adjoint eigen-equation at a positive fixed
point.  Its eigenvalue is the raw `p`-power objective. -/
theorem boydRawAdjoint_coord_eq_objective_mul_rpow_of_fixed
    {m n : ℕ} [Nontrivial (Fin n)] (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ))
    {x : Fin n → ℝ} (hx : x ∈ boydNonnegativeUnitCarrier p)
    (hfixed : (RectPNormPair.general hn hpq A).xnext x = x)
    (j : Fin n) :
    boydRawAdjoint p A x j =
      boydRawPowerObjective p A x * (x j) ^ (p - 1) := by
  let P := RectPNormPair.general hn hpq A
  let y := P.yof x
  let S := boydRawPowerObjective p A x
  have hxpos : ∀ k, 0 < x k :=
    boydCarrier_fixedPoint_pos hn hpq A hA hGram hx hfixed
  have hyne : y ≠ 0 :=
    rect_general_yof_ne_zero_of_mem_boydCarrier hn hpq A hA hGram hx
  have hSpos : 0 < S := by
    rw [show S = realLpPowerSum p y by
      rw [show y = fun i => ∑ j : Fin n, A i j * x j by rfl]
      exact boydRawPowerObjective_eq_realLpPowerSum (p := p) hA hx.1]
    exact realLpPowerSum_pos hpq.lt hyne
  have hzraw := rect_general_zof_eq_scale_mul_boydRawAdjoint
    hn hpq A hA hx.1 hyne j
  have hzfixed := rect_general_zof_coord_eq_norm_mul_rpow_of_fixed
    hn hpq A hA hGram hx hfixed j
  have hnorm : realVecLpNorm p y = S ^ p⁻¹ := by
    rw [realVecLpNorm_eq_sum_rpow hpq.pos]
    congr 1
    symm
    simpa [P, y, S, RectPNormPair.general, RectPNormPair.yof] using
      boydRawPowerObjective_eq_realLpPowerSum (p := p) hA hx.1
  have hscaleS : S ^ (p⁻¹ - 1) * S = realVecLpNorm p y := by
    rw [hnorm, ← Real.rpow_add_one hSpos.ne']
    congr 1
    ring
  have hscaled : S ^ (p⁻¹ - 1) * boydRawAdjoint p A x j =
      S ^ (p⁻¹ - 1) * (S * (x j) ^ (p - 1)) := by
    rw [← mul_assoc, hscaleS]
    exact hzraw.symm.trans hzfixed
  exact mul_left_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hSpos _)) hscaled

theorem boydSimplexTangentCoeff_eq_objective_mul_rpow_of_fixed
    {m n : ℕ} [Nontrivial (Fin n)] (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ))
    {x : Fin n → ℝ} (hx : x ∈ boydNonnegativeUnitCarrier p)
    (hfixed : (RectPNormPair.general hn hpq A).xnext x = x)
    (j : Fin n) :
    boydSimplexTangentCoeff p A x j =
      boydRawPowerObjective p A x * (x j) ^ p := by
  have hxpos : ∀ k, 0 < x k :=
    boydCarrier_fixedPoint_pos hn hpq A hA hGram hx hfixed
  rw [boydSimplexTangentCoeff_eq_mul_boydRawAdjoint hpq.lt A hA hxpos,
    boydRawAdjoint_coord_eq_objective_mul_rpow_of_fixed
      hn hpq A hA hGram hx hfixed j]
  calc
    x j * (boydRawPowerObjective p A x * x j ^ (p - 1)) =
        boydRawPowerObjective p A x * (x j ^ (p - 1) * x j) := by ring
    _ = boydRawPowerObjective p A x * x j ^ p := by
      rw [← Real.rpow_add_one (ne_of_gt (hxpos j)) (p - 1)]
      congr 2
      ring

/-- Every positive normalized fixed point is a global maximizer of the raw
objective on Boyd's nonnegative unit carrier. -/
theorem boydCarrier_fixedPoint_isMax_rawPower
    {m n : ℕ} [Nontrivial (Fin n)] (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ))
    {x : Fin n → ℝ} (hx : x ∈ boydNonnegativeUnitCarrier p)
    (hfixed : (RectPNormPair.general hn hpq A).xnext x = x) :
    ∀ u ∈ boydNonnegativeUnitCarrier p,
      boydRawPowerObjective p A u ≤ boydRawPowerObjective p A x := by
  intro u hu
  have hxpos : ∀ j, 0 < x j :=
    boydCarrier_fixedPoint_pos hn hpq A hA hGram hx hfixed
  have htangent := boydRawPowerObjective_le_simplex_tangent
    (le_of_lt hpq.lt) A hA hxpos hu.1
  calc
    boydRawPowerObjective p A u ≤
        ∑ j : Fin n, boydSimplexTangentCoeff p A x j *
          (u j / x j) ^ p := htangent
    _ = ∑ j : Fin n, boydRawPowerObjective p A x * (u j) ^ p := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [boydSimplexTangentCoeff_eq_objective_mul_rpow_of_fixed
        hn hpq A hA hGram hx hfixed j]
      rw [mul_assoc, show (x j) ^ p * (u j / x j) ^ p = (u j) ^ p by
        rw [mul_comm, rpow_div_rpow_cancel (hu.1 j) (hxpos j)]]
    _ = boydRawPowerObjective p A x := by
      rw [← Finset.mul_sum]
      have hupower : (∑ j : Fin n, (u j) ^ p) = 1 := by
        rw [← realLpPowerSum_eq_one_of_unit hpq.pos hu.2]
        unfold realLpPowerSum
        apply Finset.sum_congr rfl
        intro j _hj
        rw [abs_of_nonneg (hu.1 j)]
      rw [hupower, mul_one]

theorem boydSimplexTangent_sum_eq_objective_of_fixed
    {m n : ℕ} [Nontrivial (Fin n)] (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ))
    {x u : Fin n → ℝ} (hx : x ∈ boydNonnegativeUnitCarrier p)
    (hfixed : (RectPNormPair.general hn hpq A).xnext x = x)
    (hu : u ∈ boydNonnegativeUnitCarrier p) :
    (∑ j : Fin n, boydSimplexTangentCoeff p A x j *
      (u j / x j) ^ p) = boydRawPowerObjective p A x := by
  have hxpos : ∀ j, 0 < x j :=
    boydCarrier_fixedPoint_pos hn hpq A hA hGram hx hfixed
  calc
    (∑ j : Fin n, boydSimplexTangentCoeff p A x j *
        (u j / x j) ^ p) =
        ∑ j : Fin n, boydRawPowerObjective p A x * (u j) ^ p := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [boydSimplexTangentCoeff_eq_objective_mul_rpow_of_fixed
        hn hpq A hA hGram hx hfixed j]
      rw [mul_assoc, show (x j) ^ p * (u j / x j) ^ p = (u j) ^ p by
        rw [mul_comm, rpow_div_rpow_cancel (hu.1 j) (hxpos j)]]
    _ = boydRawPowerObjective p A x := by
      rw [← Finset.mul_sum]
      have hupower : (∑ j : Fin n, (u j) ^ p) = 1 := by
        rw [← realLpPowerSum_eq_one_of_unit hpq.pos hu.2]
        unfold realLpPowerSum
        apply Finset.sum_congr rfl
        intro j _hj
        rw [abs_of_nonneg (hu.1 j)]
      rw [hupower, mul_one]

/-- The printed nonnegative/irreducible-Gram hypotheses force uniqueness of
the normalized nonlinear fixed point on Boyd's carrier. -/
theorem boydCarrier_fixedPoint_unique
    {m n : ℕ} [Nontrivial (Fin n)] (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ))
    {x u : Fin n → ℝ}
    (hx : x ∈ boydNonnegativeUnitCarrier p)
    (hxfixed : (RectPNormPair.general hn hpq A).xnext x = x)
    (hu : u ∈ boydNonnegativeUnitCarrier p)
    (hufixed : (RectPNormPair.general hn hpq A).xnext u = u) :
    u = x := by
  have hxpos : ∀ j, 0 < x j :=
    boydCarrier_fixedPoint_pos hn hpq A hA hGram hx hxfixed
  have hupos : ∀ j, 0 < u j :=
    boydCarrier_fixedPoint_pos hn hpq A hA hGram hu hufixed
  have hobj : boydRawPowerObjective p A u = boydRawPowerObjective p A x :=
    le_antisymm
      (boydCarrier_fixedPoint_isMax_rawPower hn hpq A hA hGram hx hxfixed u hu)
      (boydCarrier_fixedPoint_isMax_rawPower hn hpq A hA hGram hu hufixed x hx)
  let rowL : Fin m → ℝ := fun i => (∑ j : Fin n, A i j * u j) ^ p
  let rowR : Fin m → ℝ := fun i =>
    (∑ j : Fin n, A i j * x j) ^ p *
      ∑ j : Fin n,
        ((A i j * x j) / (∑ k : Fin n, A i k * x k)) *
          (u j / x j) ^ p
  have hrowle : ∀ i, rowL i ≤ rowR i := by
    intro i
    exact boyd_row_power_tangent_le (le_of_lt hpq.lt)
      (A i) x u (hA i) hxpos hu.1
  have hsumL : (∑ i : Fin m, rowL i) = boydRawPowerObjective p A u := rfl
  have hsumR : (∑ i : Fin m, rowR i) = boydRawPowerObjective p A x := by
    calc
      (∑ i : Fin m, rowR i) =
          ∑ j : Fin n, boydSimplexTangentCoeff p A x j *
            (u j / x j) ^ p := by
        dsimp [rowR]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        unfold boydSimplexTangentCoeff
        apply Finset.sum_congr rfl
        intro j _hj
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = boydRawPowerObjective p A x :=
        boydSimplexTangent_sum_eq_objective_of_fixed
          hn hpq A hA hGram hx hxfixed hu
  have hgapSum : (∑ i : Fin m, (rowR i - rowL i)) = 0 := by
    rw [Finset.sum_sub_distrib, hsumR, hsumL, hobj]
    ring
  have hroweq : ∀ i, rowL i = rowR i := by
    intro i
    have hgap : rowR i - rowL i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun r (_hr : r ∈ (Finset.univ : Finset (Fin m))) =>
          sub_nonneg.mpr (hrowle r))).mp hgapSum i (Finset.mem_univ i)
    linarith
  let M : Matrix (Fin n) (Fin n) ℝ := Matrix.of (rectGram A)
  have hMnonneg : ∀ j k, 0 ≤ M j k := hGram.1
  have hedge : ∀ {j k : Fin n}, 0 < M j k → u j / x j = u k / x k := by
    intro j k hjk
    change 0 < ∑ i : Fin m, A i j * A i k at hjk
    have hterms : ∀ i ∈ (Finset.univ : Finset (Fin m)),
        0 ≤ A i j * A i k := fun i _ => mul_nonneg (hA i j) (hA i k)
    obtain ⟨i, _hi, hprod⟩ := (Finset.sum_pos_iff_of_nonneg hterms).mp hjk
    have haij : 0 < A i j := by nlinarith [hA i j, hA i k]
    have haik : 0 < A i k := by nlinarith [hA i j, hA i k]
    exact boyd_row_power_tangent_eq_ratio hpq.lt (A i) x u
      (hA i) hxpos hu.1 (hroweq i) haij haik
  have hpow : ∀ r : ℕ, ∀ j k : Fin n,
      0 < (M ^ r) j k → u j / x j = u k / x k := by
    intro r
    induction r with
    | zero =>
        intro j k hjk
        have hjkeq : j = k := by
          by_contra hne
          simp [hne] at hjk
        rw [hjkeq]
    | succ r ihr =>
        intro j k hjk
        rw [pow_succ'] at hjk
        change 0 < ∑ l : Fin n, M j l * (M ^ r) l k at hjk
        have hterms : ∀ l ∈ (Finset.univ : Finset (Fin n)),
            0 ≤ M j l * (M ^ r) l k := fun l _ =>
          mul_nonneg (hMnonneg j l)
            (Matrix.pow_apply_nonneg hMnonneg r l k)
        obtain ⟨l, _hl, hprod⟩ :=
          (Finset.sum_pos_iff_of_nonneg hterms).mp hjk
        have hjl : 0 < M j l := by
          nlinarith [hMnonneg j l, Matrix.pow_apply_nonneg hMnonneg r l k]
        have hlk : 0 < (M ^ r) l k := by
          nlinarith [hMnonneg j l, Matrix.pow_apply_nonneg hMnonneg r l k]
        exact (hedge hjl).trans (ihr l k hlk)
  have hratio : ∀ j k : Fin n, u j / x j = u k / x k := by
    intro j k
    have hexists : ∃ r > 0, 0 < (M ^ r) j k := by
      simpa [M] using
        ((Matrix.isIrreducible_iff_exists_pow_pos hMnonneg).mp hGram j k)
    obtain ⟨r, _hr, hrpos⟩ := hexists
    exact hpow r j k hrpos
  let j0 : Fin n := ⟨0, hn⟩
  let c : ℝ := u j0 / x j0
  have hcpos : 0 < c := div_pos (hupos j0) (hxpos j0)
  have hux : u = fun j => c * x j := by
    funext j
    have hr : u j / x j = c := by
      simpa [c] using hratio j j0
    field_simp [ne_of_gt (hxpos j), ne_of_gt (hxpos j0)] at hr
    nlinarith
  have hnorm : realVecLpNorm p u = c * realVecLpNorm p x := by
    rw [hux, realVecLpNorm_smul_real (le_of_lt hpq.lt), abs_of_pos hcpos]
  rw [hu.2, hx.2, mul_one] at hnorm
  have hc : c = 1 := hnorm.symm
  rw [hux, hc]
  simp

end Ch15
end NumStability
