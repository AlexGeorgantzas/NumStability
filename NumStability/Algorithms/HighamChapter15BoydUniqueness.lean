import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import NumStability.Algorithms.HighamChapter15BoydBridges

namespace NumStability.Ch15

open Filter Function Set
open scoped BigOperators Topology

noncomputable def boydRawPowerObjective {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin m, (∑ j : Fin n, A i j * x j) ^ p

noncomputable def boydRawAdjoint {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j => ∑ i : Fin m,
    A i j * (∑ k : Fin n, A i k * x k) ^ (p - 1)

noncomputable def boydSimplexTangentCoeff {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j => ∑ i : Fin m,
    (∑ k : Fin n, A i k * x k) ^ p *
      ((A i j * x j) / (∑ k : Fin n, A i k * x k))

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

lemma rpow_mul_mul_div_eq {a x y p : ℝ} (hp : 1 < p)
    (hy : 0 ≤ y) :
    y ^ p * ((a * x) / y) = x * (a * y ^ (p - 1)) := by
  rcases hy.eq_or_lt with rfl | hy
  · simp [Real.zero_rpow (ne_of_gt (zero_lt_one.trans hp)),
      Real.zero_rpow (sub_ne_zero.mpr (ne_of_gt hp))]
  · rw [Real.rpow_sub_one hy.ne' p]
    field_simp [hy.ne']

/-- Rowwise tangent inequality behind Boyd's simplex concavity argument. -/
theorem boyd_row_power_tangent_le {n : ℕ} {p : ℝ} (hp : 1 ≤ p)
    (a x u : Fin n → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hx : ∀ j, 0 < x j)
    (hu : ∀ j, 0 ≤ u j) :
    (∑ j : Fin n, a j * u j) ^ p ≤
      (∑ j : Fin n, a j * x j) ^ p *
        ∑ j : Fin n,
          ((a j * x j) / (∑ k : Fin n, a k * x k)) *
            (u j / x j) ^ p := by
  let y : ℝ := ∑ j : Fin n, a j * x j
  have hy : 0 ≤ y := Finset.sum_nonneg fun j _ =>
    mul_nonneg (ha j) (hx j).le
  rcases hy.eq_or_lt with hyzero | hypos
  · have haj : ∀ j, a j = 0 := by
      intro j
      have hterm : a j * x j = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun k (_hk : k ∈ (Finset.univ : Finset (Fin n))) =>
            mul_nonneg (ha k) (hx k).le)).mp hyzero.symm j (Finset.mem_univ j)
      exact (mul_eq_zero.mp hterm).resolve_right (ne_of_gt (hx j))
    simp [haj, Real.zero_rpow (ne_of_gt (lt_of_lt_of_le zero_lt_one hp))]
  · have hw_nonneg : ∀ j ∈ (Finset.univ : Finset (Fin n)),
        0 ≤ (a j * x j) / y := by
      intro j _hj
      exact div_nonneg (mul_nonneg (ha j) (hx j).le) hypos.le
    have hw_sum : (∑ j : Fin n, (a j * x j) / y) = 1 := by
      rw [← Finset.sum_div, show (∑ j : Fin n, a j * x j) = y from rfl,
        div_self (ne_of_gt hypos)]
    have hz_nonneg : ∀ j ∈ (Finset.univ : Finset (Fin n)),
        0 ≤ u j / x j := by
      intro j _hj
      exact div_nonneg (hu j) (hx j).le
    have hjensen := Real.rpow_arith_mean_le_arith_mean_rpow
      (Finset.univ : Finset (Fin n))
      (fun j => (a j * x j) / y) (fun j => u j / x j)
      hw_nonneg hw_sum hz_nonneg hp
    have havg : (∑ j : Fin n,
        (a j * x j / y) * (u j / x j)) =
        (∑ j : Fin n, a j * u j) / y := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _hj
      field_simp [ne_of_gt (hx j)]
    rw [havg] at hjensen
    have hmul := mul_le_mul_of_nonneg_right hjensen
      (Real.rpow_nonneg hy p)
    rw [rpow_div_rpow_cancel
      (Finset.sum_nonneg fun j _ => mul_nonneg (ha j) (hu j)) hypos] at hmul
    simpa [y, mul_comm] using hmul

/-- Equality in the rowwise tangent bound forces equal coordinate ratios
across every pair of positive coefficients in that row. -/
theorem boyd_row_power_tangent_eq_ratio {n : ℕ} {p : ℝ} (hp : 1 < p)
    (a x u : Fin n → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hx : ∀ j, 0 < x j)
    (hu : ∀ j, 0 ≤ u j)
    (heq : (∑ j : Fin n, a j * u j) ^ p =
      (∑ j : Fin n, a j * x j) ^ p *
        ∑ j : Fin n,
          ((a j * x j) / (∑ k : Fin n, a k * x k)) *
            (u j / x j) ^ p)
    {j k : Fin n} (haj : 0 < a j) (hak : 0 < a k) :
    u j / x j = u k / x k := by
  let y : ℝ := ∑ r : Fin n, a r * x r
  have hypos : 0 < y := by
    apply Finset.sum_pos'
    · intro r _hr
      exact mul_nonneg (ha r) (hx r).le
    · exact ⟨j, Finset.mem_univ j, mul_pos haj (hx j)⟩
  have hw_nonneg : ∀ r ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ (a r * x r) / y := by
    intro r _hr
    exact div_nonneg (mul_nonneg (ha r) (hx r).le) hypos.le
  have hw_sum : (∑ r : Fin n, (a r * x r) / y) = 1 := by
    rw [← Finset.sum_div, show (∑ r : Fin n, a r * x r) = y from rfl,
      div_self (ne_of_gt hypos)]
  have hz_nonneg : ∀ r ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ u r / x r := by
    intro r _hr
    exact div_nonneg (hu r) (hx r).le
  have havg : (∑ r : Fin n,
      (a r * x r / y) * (u r / x r)) =
      (∑ r : Fin n, a r * u r) / y := by
    rw [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _hr
    field_simp [ne_of_gt (hx r)]
  have hprod :
      ((∑ r : Fin n, (a r * x r / y) * (u r / x r)) ^ p) * y ^ p =
        (∑ r : Fin n, (a r * x r / y) * (u r / x r) ^ p) * y ^ p := by
    rw [havg, rpow_div_rpow_cancel
      (Finset.sum_nonneg fun r _ => mul_nonneg (ha r) (hu r)) hypos]
    simpa [y, mul_comm] using heq
  have hyPow : y ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hypos p)
  have hjensenEq :
      (∑ r : Fin n, (a r * x r / y) * (u r / x r)) ^ p =
        ∑ r : Fin n, (a r * x r / y) * (u r / x r) ^ p :=
    mul_right_cancel₀ hyPow hprod
  have hrigid := (strictConvexOn_rpow hp).map_sum_eq_iff'
    hw_nonneg hw_sum hz_nonneg |>.mp hjensenEq
  have hwj : a j * x j / y ≠ 0 :=
    ne_of_gt (div_pos (mul_pos haj (hx j)) hypos)
  have hwk : a k * x k / y ≠ 0 :=
    ne_of_gt (div_pos (mul_pos hak (hx k)) hypos)
  exact (hrigid j (Finset.mem_univ j) hwj).trans
    (hrigid k (Finset.mem_univ k) hwk).symm

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

lemma boydRawPowerObjective_eq_realLpPowerSum {m n : ℕ} {p : ℝ}
    {A : Fin m → Fin n → ℝ} {x : Fin n → ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hx : ∀ j, 0 ≤ x j) :
    boydRawPowerObjective p A x =
      realLpPowerSum p (fun i => ∑ j : Fin n, A i j * x j) := by
  unfold boydRawPowerObjective realLpPowerSum
  apply Finset.sum_congr rfl
  intro i _hi
  rw [abs_of_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (hx j))]

lemma realVecLpNorm_rpow_eq_boydRawPowerObjective {m n : ℕ}
    {p : ℝ} (hp : 0 < p) {A : Fin m → Fin n → ℝ}
    {x : Fin n → ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hx : ∀ j, 0 ≤ x j) :
    (realVecLpNorm p (fun i => ∑ j : Fin n, A i j * x j)) ^ p =
      boydRawPowerObjective p A x := by
  rw [realVecLpNorm_eq_sum_rpow hp,
    boydRawPowerObjective_eq_realLpPowerSum hA hx]
  unfold realLpPowerSum
  exact Real.rpow_inv_rpow
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) p)
    (ne_of_gt hp)

/-- The concrete normalized output dual is the raw power adjoint multiplied
by the common gradient scale. -/
theorem rect_general_zof_eq_scale_mul_boydRawAdjoint
    {m n : ℕ} (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q) (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) {x : Fin n → ℝ}
    (hx : ∀ j, 0 ≤ x j)
    (hyne : (RectPNormPair.general hn hpq A).yof x ≠ 0)
    (j : Fin n) :
    (RectPNormPair.general hn hpq A).zof x j =
      (boydRawPowerObjective p A x) ^ (p⁻¹ - 1) *
        boydRawAdjoint p A x j := by
  let P := RectPNormPair.general hn hpq A
  let y := P.yof x
  have hynonneg : ∀ i, 0 ≤ y i := by
    intro i
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hA i k) (hx k)
  have hpower : realLpPowerSum p y = boydRawPowerObjective p A x := by
    symm
    simpa [P, y, RectPNormPair.general, RectPNormPair.yof] using
      boydRawPowerObjective_eq_realLpPowerSum (p := p) hA hx
  change (∑ i : Fin m, A i j * realLpDual hpq y i) = _
  rw [realLpDual_eq_realLpGradient hpq y hyne]
  unfold realLpGradient boydRawAdjoint
  rw [hpower, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [rpow_sub_two_mul_self_eq_rpow_sub_one_of_nonneg hpq.lt (hynonneg i)]
  rw [show y i = ∑ k : Fin n, A i k * x k by rfl]
  ring

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

theorem boydSimplexTangentCoeff_eq_mul_boydRawAdjoint
    {m n : ℕ} {p : ℝ} (hp : 1 < p)
    (A : Fin m → Fin n → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {x : Fin n → ℝ} (hx : ∀ j, 0 < x j) (j : Fin n) :
    boydSimplexTangentCoeff p A x j = x j * boydRawAdjoint p A x j := by
  unfold boydSimplexTangentCoeff boydRawAdjoint
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  exact rpow_mul_mul_div_eq hp
    (Finset.sum_nonneg fun k _ => mul_nonneg (hA i k) (hx k).le)

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

/-- Concavity supporting inequality for the raw `p`-power objective in the
simplex coordinates `u_j^p`. -/
theorem boydRawPowerObjective_le_simplex_tangent
    {m n : ℕ} {p : ℝ} (hp : 1 ≤ p)
    (A : Fin m → Fin n → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {x u : Fin n → ℝ} (hx : ∀ j, 0 < x j)
    (hu : ∀ j, 0 ≤ u j) :
    boydRawPowerObjective p A u ≤
      ∑ j : Fin n, boydSimplexTangentCoeff p A x j *
        (u j / x j) ^ p := by
  have hrows : ∀ i : Fin m,
      (∑ j : Fin n, A i j * u j) ^ p ≤
        (∑ j : Fin n, A i j * x j) ^ p *
          ∑ j : Fin n,
            ((A i j * x j) / (∑ k : Fin n, A i k * x k)) *
              (u j / x j) ^ p := by
    intro i
    exact boyd_row_power_tangent_le hp (A i) x u (hA i) hx hu
  calc
    boydRawPowerObjective p A u ≤
        ∑ i : Fin m, (∑ j : Fin n, A i j * x j) ^ p *
          ∑ j : Fin n,
            ((A i j * x j) / (∑ k : Fin n, A i k * x k)) *
              (u j / x j) ^ p := by
      unfold boydRawPowerObjective
      exact Finset.sum_le_sum fun i _ => hrows i
    _ = ∑ j : Fin n, boydSimplexTangentCoeff p A x j *
          (u j / x j) ^ p := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      unfold boydSimplexTangentCoeff
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _hi
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

/-- Higham p. 291 / Boyd's global convergence statement at the printed
rectangular dimensions and hypotheses.  The raw strictly positive start is
normalized exactly as Algorithm 15.1 prescribes.  The actual iterates converge
to the unique positive maximizing fixed point, and the actual norm estimates
converge to the exact induced `p`-norm. -/
theorem higham15_boyd_global_of_nonnegative_irreducibleGram
    {m n : ℕ} [Nontrivial (Fin n)] (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hGram : Matrix.IsIrreducible
      (Matrix.of (rectGram A) : Matrix (Fin n) (Fin n) ℝ))
    (x0 : Fin n → ℝ) (hx0 : ∀ j, 0 < x0 j) :
    ∃ xbar : Fin n → ℝ,
      xbar ∈ boydNonnegativeUnitCarrier p ∧
      (∀ j, 0 < xbar j) ∧
      (RectPNormPair.general hn hpq A).xnext xbar = xbar ∧
      realVecLpNorm p ((RectPNormPair.general hn hpq A).yof xbar) =
        (RectPNormPair.general hn hpq A).opP ∧
      Tendsto ((RectPNormPair.general hn hpq A).xseq
        (realLpNormalizedStart p x0)) atTop (nhds xbar) ∧
      Tendsto ((RectPNormPair.general hn hpq A).gammaSeq
        (realLpNormalizedStart p x0)) atTop
        (nhds (RectPNormPair.general hn hpq A).opP) := by
  let P := RectPNormPair.general hn hpq A
  let s := boydNonnegativeUnitCarrier (n := n) p
  let xstart := realLpNormalizedStart p x0
  obtain ⟨xbar, hxbar, hxbarpos, hfixed, hoptimal⟩ :=
    exists_boydCarrier_positive_opP_fixedPoint hn hpq A hA hGram
  have hxstart : xstart ∈ s := by
    constructor
    · intro j
      exact (realLpNormalizedStart_pos hn (le_of_lt hpq.lt) x0 hx0 j).le
    · exact realLpNormalizedStart_norm_eq_one
        hn (le_of_lt hpq.lt) x0 hx0
  have hunique : ∀ x ∈ s, P.xnext x = x → x = xbar := by
    intro x hx hxfixed
    exact boydCarrier_fixedPoint_unique hn hpq A hA hGram
      hxbar hfixed hx hxfixed
  have hconv := higham15_boyd_global_of_compact_unique_optimal_fixed
    hn hpq A s (isCompact_boydNonnegativeUnitCarrier hpq)
    xstart xbar hxstart
    (rect_general_xnext_mapsTo_boydCarrier hn hpq A hA hGram)
    (fun x hx => hx.2)
    (fun x hx => rect_general_zof_ne_zero_of_mem_boydCarrier
      hn hpq A hA hGram hx)
    (continuousOn_rect_general_xnext_boydCarrier
      hn hpq A hA hGram)
    hunique hoptimal
  exact ⟨xbar, hxbar, hxbarpos, hfixed, hoptimal, hconv⟩

end NumStability.Ch15
