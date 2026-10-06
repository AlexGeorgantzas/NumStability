import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
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
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.LocalStability.BoydInterface
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# NumStability Algorithms NormEstimation PNorm Boyd LocalStability BoydLocalStability

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter15BoydLocalStability` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open Filter Function

open scoped BigOperators Topology

/-- If a positive power of the derivative is contractive, the corresponding
iterate of the nonlinear map is a genuine local contraction.  Unlike a bound
on `‖L‖`, this condition is insensitive to transient growth caused by a
non-normal derivative. -/
theorem exists_isLocalContractionTo_iterate_of_hasFDerivAt_pow_norm_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : E → E} {xbar : E} {L : E →L[ℝ] E} {N : ℕ} {K : NNReal}
    (hfixed : T xbar = xbar)
    (hderiv : HasFDerivAt T L xbar)
    (hpow : ‖L ^ N‖ < (K : ℝ)) (hK : K < 1) :
    ∃ δ : ℝ, 0 < δ ∧ IsLocalContractionTo T^[N] xbar K δ := by
  apply exists_isLocalContractionTo_of_hasFDerivAt_norm_lt
    (iterate_fixed hfixed N) (hderiv.iterate hfixed N) hpow hK

/-- Gelfand extraction in a complex Banach algebra: spectral radius below a
positive real `r` makes `‖a^k‖ ≤ r^k` eventually. -/
theorem eventually_norm_pow_le_of_spectralRadius_lt
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (a : A) {r : ℝ} (hr : 0 < r)
    (hspec : spectralRadius ℂ a < ENNReal.ofReal r) :
    ∀ᶠ k : ℕ in atTop, ‖a ^ k‖ ≤ r ^ k := by
  have hgel := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a
  have hev : ∀ᶠ k : ℕ in atTop,
      ENNReal.ofReal (‖a ^ k‖ ^ (1 / (k : ℝ))) < ENNReal.ofReal r :=
    hgel.eventually_lt_const hspec
  filter_upwards [hev, eventually_ge_atTop 1] with k hk hk1
  have hklt : ‖a ^ k‖ ^ (1 / (k : ℝ)) < r :=
    (ENNReal.ofReal_lt_ofReal_iff hr).mp hk
  have hknorm : 0 ≤ ‖a ^ k‖ := norm_nonneg _
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk1
  have hroot : ‖a ^ k‖ = (‖a ^ k‖ ^ (1 / (k : ℝ))) ^ k := by
    rw [← Real.rpow_natCast (‖a ^ k‖ ^ (1 / (k : ℝ))) k,
      ← Real.rpow_mul hknorm, one_div,
      inv_mul_cancel₀ (ne_of_gt hkpos), Real.rpow_one]
  rw [hroot]
  exact pow_le_pow_left₀ (Real.rpow_nonneg hknorm _) (le_of_lt hklt) k

/-- In particular, spectral radius below `r` supplies one positive derivative
power certificate, the exact finite input used by the adapted-norm theorem. -/
theorem exists_pos_norm_pow_le_of_spectralRadius_lt
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (a : A) {r : ℝ} (hr : 0 < r)
    (hspec : spectralRadius ℂ a < ENNReal.ofReal r) :
    ∃ N : ℕ, 0 < N ∧ ‖a ^ N‖ ≤ r ^ N := by
  have hev := eventually_norm_pow_le_of_spectralRadius_lt a hr hspec
  obtain ⟨N, hN, hbound⟩ :=
    (hev.and (eventually_ge_atTop (1 : ℕ))).exists
  exact ⟨N, hbound, hN⟩

/-- The finite-power adapted norm
`Σ_{k<N} c⁻ᵏ ‖Lᵏx‖`, bundled as a seminorm.  For `N > 0` it is a norm because
its zeroth summand is `‖x‖`. -/
noncomputable def powerAdaptedSeminorm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] E) (c : NNReal) (N : ℕ) : Seminorm ℝ E :=
  ∑ k ∈ Finset.range N,
    (c ^ k)⁻¹ • (normSeminorm ℝ E).comp (L ^ k).toLinearMap

theorem powerAdaptedSeminorm_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] E) (c : NNReal) (N : ℕ) (x : E) :
    powerAdaptedSeminorm L c N x =
      ∑ k ∈ Finset.range N, ((c ^ k)⁻¹ : NNReal) * ‖(L ^ k) x‖ := by
  let f : ℕ → Seminorm ℝ E := fun k =>
    (c ^ k)⁻¹ • (normSeminorm ℝ E).comp (L ^ k).toLinearMap
  have hsum : ∀ s : Finset ℕ,
      (∑ k ∈ s, f k) x =
        ∑ k ∈ s, (((c ^ k)⁻¹ : NNReal) : ℝ) * ‖(L ^ k) x‖ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert k s hk ih =>
        simp [hk, ih, f]
        change (((((c ^ k)⁻¹ : NNReal) : ℝ) * ‖(L ^ k) x‖) =
          ((c : ℝ) ^ k)⁻¹ * ‖(L ^ k) x‖)
        push_cast
        rfl
  simpa [powerAdaptedSeminorm, f] using hsum (Finset.range N)

/-- The adapted seminorm is separating when at least one derivative power is
included.  This is the lower half of its equivalence with the original norm. -/
theorem norm_le_powerAdaptedSeminorm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] E) (c : NNReal) {N : ℕ} (hN : 0 < N) (x : E) :
    ‖x‖ ≤ powerAdaptedSeminorm L c N x := by
  rw [powerAdaptedSeminorm_apply]
  have hmem : 0 ∈ Finset.range N := Finset.mem_range.mpr hN
  have hsingle :
      ((↑((c ^ 0)⁻¹) : ℝ) * ‖(L ^ 0) x‖) ≤
        ∑ k ∈ Finset.range N, ((c ^ k)⁻¹ : NNReal) * ‖(L ^ k) x‖ :=
    by
      let f : ℕ → ℝ := fun k =>
        (((c ^ k)⁻¹ : NNReal) : ℝ) * ‖(L ^ k) x‖
      have hf : ∀ k ∈ Finset.range N, 0 ≤ f k := by
        intro k _hk
        exact mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _)
      have h := Finset.single_le_sum (s := Finset.range N) (f := f) hf hmem
      simpa [f] using h
  simpa using hsingle

/-- Explicit equivalence constant from the adapted norm to the original
norm. -/
noncomputable def powerAdaptedBound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] E) (c : NNReal) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, ((c ^ k)⁻¹ : NNReal) * ‖L ^ k‖

theorem powerAdaptedSeminorm_le_bound_mul_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] E) (c : NNReal) (N : ℕ) (x : E) :
    powerAdaptedSeminorm L c N x ≤
      powerAdaptedBound L c N * ‖x‖ := by
  rw [powerAdaptedSeminorm_apply]
  unfold powerAdaptedBound
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  calc
    (((c ^ k)⁻¹ : NNReal) : ℝ) * ‖(L ^ k) x‖ ≤
        (((c ^ k)⁻¹ : NNReal) : ℝ) * (‖L ^ k‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left ((L ^ k).le_opNorm x)
        (NNReal.coe_nonneg _)
    _ = (((c ^ k)⁻¹ : NNReal) : ℝ) * ‖L ^ k‖ * ‖x‖ := by ring

theorem powerAdaptedSeminorm_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] E) (c : NNReal) (N : ℕ) (x : E) :
    powerAdaptedSeminorm L c (N + 1) x =
      powerAdaptedSeminorm L c N x +
        ((c ^ N)⁻¹ : NNReal) * ‖(L ^ N) x‖ := by
  rw [powerAdaptedSeminorm_apply, powerAdaptedSeminorm_apply]
  simp [Finset.sum_range_succ]

/-- Exact shift identity for the finite-power adapted norm. -/
theorem powerAdaptedSeminorm_map_identity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] E) {c : NNReal} (hc : 0 < c) (N : ℕ) (x : E) :
    powerAdaptedSeminorm L c N (L x) =
      (c : ℝ) * powerAdaptedSeminorm L c N x - (c : ℝ) * ‖x‖ +
        (c : ℝ) * ((c ^ N)⁻¹ : NNReal) * ‖(L ^ N) x‖ := by
  induction N with
  | zero => simp [powerAdaptedSeminorm]
  | succ N ih =>
      rw [show N + 1 = N.succ by omega,
        powerAdaptedSeminorm_succ, powerAdaptedSeminorm_succ, ih]
      have hpow_apply : (L ^ N) (L x) = (L ^ (N + 1)) x := by
        rw [pow_succ]
        rfl
      rw [hpow_apply]
      have hc0 : (c : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hc)
      push_cast
      simp only [Nat.succ_eq_add_one, pow_succ]
      field_simp [hc0]
      ring_nf

/-- A finite power bound makes the derivative contractive in the explicit
adapted norm. -/
theorem powerAdaptedSeminorm_map_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] E) {c : NNReal} (hc : 0 < c) (N : ℕ)
    (hpow : ‖L ^ N‖ ≤ (c : ℝ) ^ N) (x : E) :
    powerAdaptedSeminorm L c N (L x) ≤
      (c : ℝ) * powerAdaptedSeminorm L c N x := by
  rw [powerAdaptedSeminorm_map_identity L hc]
  have hcN : 0 < (c : ℝ) ^ N := pow_pos (by exact_mod_cast hc) N
  have haction : ‖(L ^ N) x‖ ≤ (c : ℝ) ^ N * ‖x‖ :=
    (L ^ N).le_opNorm x |>.trans
      (mul_le_mul_of_nonneg_right hpow (norm_nonneg x))
  have hboundary :
      (↑((c ^ N)⁻¹) : ℝ) * ‖(L ^ N) x‖ ≤ ‖x‖ := by
    calc
      (↑((c ^ N)⁻¹) : ℝ) * ‖(L ^ N) x‖
          ≤ ((c : ℝ) ^ N)⁻¹ * ((c : ℝ) ^ N * ‖x‖) := by
            push_cast
            exact mul_le_mul_of_nonneg_left haction (inv_nonneg.mpr hcN.le)
      _ = ‖x‖ := by field_simp [ne_of_gt hcN]
  have hc_nonneg : 0 ≤ (c : ℝ) := NNReal.coe_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hboundary hc_nonneg]

/-- Radial contraction measured in a separating seminorm, on a ball measured
by that same seminorm. -/
def IsLocalSeminormContractionTo
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (T : E → E) (xbar : E)
    (K : NNReal) (δ : ℝ) : Prop :=
  K < 1 ∧ 0 ≤ δ ∧ T xbar = xbar ∧
    ∀ x, p (x - xbar) ≤ δ →
      p (T x - xbar) ≤ (K : ℝ) * p (x - xbar)

theorem iterate_seminorm_le_geometric_of_localSeminormContraction
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {p : Seminorm ℝ E} {T : E → E} {xbar x0 : E}
    {K : NNReal} {δ : ℝ}
    (hlocal : IsLocalSeminormContractionTo p T xbar K δ)
    (hx0 : p (x0 - xbar) ≤ δ) :
    ∀ k : ℕ,
      p (T^[k] x0 - xbar) ≤ (K : ℝ) ^ k * p (x0 - xbar) ∧
      p (T^[k] x0 - xbar) ≤ δ := by
  intro k
  induction k with
  | zero => simpa using And.intro (le_refl (p (x0 - xbar))) hx0
  | succ k ih =>
      have hstep := hlocal.2.2.2 (T^[k] x0) ih.2
      have hKle : (K : ℝ) ≤ 1 := le_of_lt (by exact_mod_cast hlocal.1)
      constructor
      · rw [iterate_succ_apply']
        calc
          p (T (T^[k] x0) - xbar)
              ≤ (K : ℝ) * p (T^[k] x0 - xbar) := hstep
          _ ≤ (K : ℝ) * ((K : ℝ) ^ k * p (x0 - xbar)) :=
            mul_le_mul_of_nonneg_left ih.1 K.coe_nonneg
          _ = (K : ℝ) ^ (k + 1) * p (x0 - xbar) := by ring
      · rw [iterate_succ_apply']
        calc
          p (T (T^[k] x0) - xbar)
              ≤ (K : ℝ) * p (T^[k] x0 - xbar) := hstep
          _ ≤ 1 * p (T^[k] x0 - xbar) :=
            mul_le_mul_of_nonneg_right hKle (apply_nonneg p _)
          _ ≤ δ := by simpa using ih.2

theorem tendsto_iterate_of_localSeminormContraction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : Seminorm ℝ E} {T : E → E} {xbar x0 : E}
    {K : NNReal} {δ : ℝ}
    (hnorm : ∀ x, ‖x‖ ≤ p x)
    (hlocal : IsLocalSeminormContractionTo p T xbar K δ)
    (hx0 : p (x0 - xbar) ≤ δ) :
    Tendsto (fun k : ℕ => T^[k] x0) atTop (nhds xbar) := by
  apply tendsto_iff_dist_tendsto_zero.2
  let g : ℕ → ℝ := fun k =>
    (K : ℝ) ^ k * p (x0 - xbar)
  refine squeeze_zero (g := g) (fun _ => dist_nonneg) ?_ ?_
  · intro k
    rw [dist_eq_norm]
    exact (hnorm _).trans
      (iterate_seminorm_le_geometric_of_localSeminormContraction
        hlocal hx0 k).1
  · simpa [g] using ((tendsto_pow_atTop_nhds_zero_of_lt_one K.coe_nonneg
      (by exact_mod_cast hlocal.1)).mul_const (p (x0 - xbar)))

/-- A power-stable derivative constructs a genuine local contraction in the
explicit adapted norm.  The Frechet remainder is transferred using the two
explicit norm-equivalence inequalities above. -/
theorem exists_local_powerAdaptedSeminormContraction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : E → E} {xbar : E} {L : E →L[ℝ] E}
    {N : ℕ} (hN : 0 < N) {c K : NNReal}
    (hc : 0 < c) (hcK : c < K) (hK : K < 1)
    (hpow : ‖L ^ N‖ ≤ (c : ℝ) ^ N)
    (hfixed : T xbar = xbar) (hderiv : HasFDerivAt T L xbar) :
    ∃ δ : ℝ, 0 < δ ∧
      IsLocalSeminormContractionTo
        (powerAdaptedSeminorm L c N) T xbar K δ := by
  let pstar := powerAdaptedSeminorm L c N
  let B := powerAdaptedBound L c N
  let C := B + 1
  let ε := ((K : ℝ) - (c : ℝ)) / C
  have hBnonneg : 0 ≤ B := by
    dsimp [B, powerAdaptedBound]
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (inv_nonneg.mpr (pow_nonneg (NNReal.coe_nonneg _) _))
        (norm_nonneg _)
  have hCpos : 0 < C := by dsimp [C]; linarith
  have hεpos : 0 < ε := by
    dsimp [ε]
    have hcKR : (c : ℝ) < (K : ℝ) := by exact_mod_cast hcK
    exact div_pos (sub_pos.mpr hcKR) hCpos
  have hrem : ∀ᶠ x in nhds xbar,
      ‖T x - T xbar - L (x - xbar)‖ ≤ ε * ‖x - xbar‖ :=
    hderiv.isLittleO.def hεpos
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.1 hrem
  refine ⟨r / 2, half_pos hr, hK, (half_pos hr).le, hfixed, ?_⟩
  intro x hx
  have hnorm_le : ‖x - xbar‖ ≤ pstar (x - xbar) := by
    exact norm_le_powerAdaptedSeminorm L c hN _
  have hxball : x ∈ Metric.ball xbar r := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact hnorm_le.trans_lt (hx.trans_lt (half_lt_self hr))
  have hremainder := hrsub hxball
  rw [hfixed] at hremainder
  let rem := T x - xbar - L (x - xbar)
  have hprem : pstar rem ≤ B * ‖rem‖ := by
    exact powerAdaptedSeminorm_le_bound_mul_norm L c N rem
  have hB_le_C : B ≤ C := by dsimp [C]; linarith
  have hpL : pstar (L (x - xbar)) ≤ (c : ℝ) * pstar (x - xbar) := by
    exact powerAdaptedSeminorm_map_le L hc N hpow _
  calc
    pstar (T x - xbar) = pstar (rem + L (x - xbar)) := by
      congr 1
      dsimp [rem]
      abel
    _ ≤ pstar rem + pstar (L (x - xbar)) := map_add_le_add _ _ _
    _ ≤ B * ‖rem‖ + (c : ℝ) * pstar (x - xbar) :=
      add_le_add hprem hpL
    _ ≤ C * ‖rem‖ + (c : ℝ) * pstar (x - xbar) := by
      gcongr
    _ ≤ C * (ε * ‖x - xbar‖) +
          (c : ℝ) * pstar (x - xbar) := by
      gcongr
      simpa [rem] using hremainder
    _ ≤ C * (ε * pstar (x - xbar)) +
          (c : ℝ) * pstar (x - xbar) := by
      gcongr
    _ = (K : ℝ) * pstar (x - xbar) := by
      dsimp [ε]
      field_simp [ne_of_gt hCpos]
      ring

end Ch15
end NumStability
