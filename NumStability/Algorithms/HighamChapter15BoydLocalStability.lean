-- Algorithms/HighamChapter15BoydLocalStability.lean
--
-- The local statement attributed to Boyd is a spectral-stability statement,
-- not an operator-norm contraction in an arbitrary pre-existing norm.  This
-- file supplies the missing norm-independent bridge: it is enough that one
-- positive power of the derivative be a strict contraction.  This is the
-- finite certificate produced either by an adapted norm or, in finite
-- dimension, by spectral radius strictly below one.

import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Seminorm
import NumStability.Algorithms.HighamChapter15BoydBridges

namespace NumStability.Ch15

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

/-- Power-stable derivative bridge for the literal Algorithm 15.1 trace.
It gives a geometric error estimate and convergence on every `N`th iterate.
This is the exact local conclusion needed before the routine finite-residue
argument (or an adapted-norm argument) upgrades it to the full trace. -/
theorem higham15_boyd_local_linear_subsequence_of_fderiv_pow_norm_lt
    {m n : ℕ} (P : RectPNormPair m n)
    (x0 xbar : Fin n → ℝ)
    (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (N : ℕ) (K : NNReal)
    (hfixed : P.xnext xbar = xbar)
    (hderiv : HasFDerivAt P.xnext L xbar)
    (hpow : ‖L ^ N‖ < (K : ℝ)) (hK : K < 1) :
    ∃ δ : ℝ, 0 < δ ∧
      (dist x0 xbar ≤ δ →
        (∀ k : ℕ,
          dist (P.xseq x0 (N * k)) xbar ≤
            (K : ℝ) ^ k * dist x0 xbar) ∧
        Tendsto (fun k : ℕ => P.xseq x0 (N * k)) atTop (nhds xbar)) := by
  obtain ⟨δ, hδ, hlocal⟩ :=
    exists_isLocalContractionTo_iterate_of_hasFDerivAt_pow_norm_lt
      hfixed hderiv hpow hK
  refine ⟨δ, hδ, fun hx0 => ?_⟩
  have hgeom := iterate_dist_le_geometric_of_isLocalContractionTo hlocal hx0
  have hconv := tendsto_iterate_of_isLocalContractionTo hlocal hx0
  constructor
  · intro k
    rw [rectPNormPair_xseq_eq_iterate P x0 (N * k),
      Function.iterate_mul]
    exact (hgeom k).1
  · convert hconv using 1
    funext k
    rw [rectPNormPair_xseq_eq_iterate P x0 (N * k),
      Function.iterate_mul]

/-! ## Spectral radius produces a finite power certificate -/

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

/-! ## An explicit finite-power adapted norm

For `N > 0`, the following seminorm contains the original norm as its zeroth
summand, so it is separating.  If `‖L^N‖ ≤ c^N`, its weights make `L` a
one-step contraction by `c`.  This is the constructive adapted-norm argument
that removes the unjustified default-norm condition `‖L‖ < 1`. -/

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

/-! ## Nonlinear contraction and full-trace convergence in the adapted norm -/

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

/-- Full-trace local linear convergence for Algorithm 15.1 from a stable
derivative.  The finite power certificate is what spectral radius below one
supplies in finite dimension; the theorem constructs the adapted norm rather
than assuming contraction in the repository's default norm. -/
theorem higham15_boyd_local_linear_of_fderiv_power_stable
    {m n : ℕ} (P : RectPNormPair m n)
    (x0 xbar : Fin n → ℝ)
    (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    {N : ℕ} (hN : 0 < N) {c K : NNReal}
    (hc : 0 < c) (hcK : c < K) (hK : K < 1)
    (hpow : ‖L ^ N‖ ≤ (c : ℝ) ^ N)
    (hfixed : P.xnext xbar = xbar)
    (hderiv : HasFDerivAt P.xnext L xbar) :
    ∃ δ : ℝ, 0 < δ ∧
      (powerAdaptedSeminorm L c N (x0 - xbar) ≤ δ →
        (∀ k : ℕ,
          powerAdaptedSeminorm L c N (P.xseq x0 k - xbar) ≤
            (K : ℝ) ^ k * powerAdaptedSeminorm L c N (x0 - xbar)) ∧
        Tendsto (P.xseq x0) atTop (nhds xbar)) := by
  obtain ⟨δ, hδ, hlocal⟩ :=
    exists_local_powerAdaptedSeminormContraction
      hN hc hcK hK hpow hfixed hderiv
  refine ⟨δ, hδ, fun hx0 => ?_⟩
  have hgeom :=
    iterate_seminorm_le_geometric_of_localSeminormContraction hlocal hx0
  have hconv := tendsto_iterate_of_localSeminormContraction
    (fun x => norm_le_powerAdaptedSeminorm L c hN x) hlocal hx0
  constructor
  · intro k
    rw [rectPNormPair_xseq_eq_iterate P x0 k]
    exact (hgeom k).1
  · rw [show P.xseq x0 = (fun k : ℕ => P.xnext^[k] x0) by
      funext k
      exact rectPNormPair_xseq_eq_iterate P x0 k]
    exact hconv

/-! ## Why the default-norm derivative hypothesis is too strong -/

/-- A two-dimensional nilpotent derivative with transient amplification. -/
noncomputable def higham15TransientNilpotent :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (2 • ContinuousLinearMap.inl ℝ ℝ ℝ).comp
    (ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem higham15TransientNilpotent_apply (x : ℝ × ℝ) :
    higham15TransientNilpotent x = (2 * x.2, 0) := by
  simp [higham15TransientNilpotent]

theorem higham15TransientNilpotent_sq :
    higham15TransientNilpotent ^ 2 = 0 := by
  ext <;> simp [pow_two, higham15TransientNilpotent_apply]

theorem higham15TransientNilpotent_norm_ge_two :
    (2 : ℝ) ≤ ‖higham15TransientNilpotent‖ := by
  have h := higham15TransientNilpotent.le_opNorm (0, 1)
  simpa [higham15TransientNilpotent_apply] using h

/-- Finite discrepancy witness: a derivative can be power-stable (indeed,
nilpotent of index two) while failing `‖L‖ < 1` in the repository's default
norm.  Thus the adapted-norm bridge above is mathematically necessary. -/
theorem higham15_power_stable_not_default_norm_contraction_witness :
    higham15TransientNilpotent ^ 2 = 0 ∧
      ¬ ‖higham15TransientNilpotent‖ < 1 := by
  refine ⟨higham15TransientNilpotent_sq, ?_⟩
  linarith [higham15TransientNilpotent_norm_ge_two]

end NumStability.Ch15
