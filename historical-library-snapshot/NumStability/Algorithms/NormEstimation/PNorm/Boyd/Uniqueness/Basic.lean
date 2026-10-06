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
import NumStability.Algorithms.NormEstimation.PNorm.Duality.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Duality.BoydUniqueness
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormRectangular
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# NumStability Algorithms NormEstimation PNorm Boyd Uniqueness Basic

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

end Ch15
end NumStability
