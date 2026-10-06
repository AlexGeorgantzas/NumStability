import NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.BlockLDLT
import NumStability.Algorithms.LinearSystems.SymmetricIndefinite.Pivoting.Basic

/-!
# Higham Chapter 11: CompletePivoting

Canonical owner materialized from the reviewed Chapter 11 route contract.
-/

namespace NumStability

open scoped BigOperators

/-! ## §11.1.1 Complete pivoting -/

/-- **Algorithm 11.1** pivoting parameter
`alpha = (1 + sqrt 17) / 8`. -/
noncomputable def higham11_1_bunchParlettAlpha : ℝ :=
  bunchParlettAlpha

/-- **Algorithm 11.1** source decision predicate for the first
Bunch-Parlett complete-pivoting step. -/
abbrev higham11_1_BunchParlettCompletePivotChoice
    (α μ0 μ1 : ℝ) (s : PivotSize) : Prop :=
  BunchParlettCompletePivotChoice α μ0 μ1 s

/-- The Bunch-Parlett parameter is the positive root selected from
`4 alpha^2 - alpha - 1 = 0`. -/
theorem higham11_1_bunch_parlett_alpha_root :
    4 * higham11_1_bunchParlettAlpha ^ 2 -
      higham11_1_bunchParlettAlpha - 1 = 0 :=
  bunch_parlett_alpha_root

/-- **§11.1.1 α-derivation**: `α = (1+√17)/8` is exactly the value balancing the
two single-step growth bounds `(1 + 1/α)²` (two 1×1 steps) and `1 + 2/(1−α)`
(one 2×2 step).  Connects `higham11_1_oneByOne_schur_growth` and
`higham11_4_twoByTwo_schur_growth`. -/
theorem higham11_1_growth_balance :
    (1 + 1 / higham11_1_bunchParlettAlpha) ^ 2 =
      1 + 2 / (1 - higham11_1_bunchParlettAlpha) :=
  bunch_parlett_growth_balance

/-- **§11.1.1 growth-factor recursion**: a stage-maximum sequence `r` obeying the
single-step ratio bound `r(k+1) ≤ (1 + 1/α)·r k` (supplied for each stage by
`higham11_1_oneByOne_schur_growth` / `higham11_4_twoByTwo_schur_growth`) satisfies
`r n ≤ (1 + 1/α)^n · ρ₀`, the derivation of the printed `ρₙ ≤ (1 + α⁻¹)^{n−1}`. -/
theorem higham11_1_growth_factor_recursion (α ρ0 : ℝ) (r : ℕ → ℝ)
    (hα : 0 < α) (h0 : r 0 = ρ0)
    (hstep : ∀ k, r (k + 1) ≤ (1 + 1 / α) * r k) :
    ∀ n, r n ≤ (1 + 1 / α) ^ n * ρ0 :=
  geom_growth_iterate α ρ0 r hα h0 hstep

/-- **§11.1.1 finite-prefix growth recursion**: the same growth-factor
iteration as `higham11_1_growth_factor_recursion`, but with one-step bounds
available only for the finite active prefix `k < m`.  This is the shape needed
when a concrete pivot path supplies stage bounds only up to the final Schur
complement. -/
theorem higham11_1_growth_factor_recursion_prefix (α ρ0 : ℝ) (r : ℕ → ℝ)
    (m : ℕ) (hα : 0 < α) (h0 : r 0 = ρ0)
    (hstep : ∀ k, k < m → r (k + 1) ≤ (1 + 1 / α) * r k) :
    ∀ n, n ≤ m → r n ≤ (1 + 1 / α) ^ n * ρ0 := by
  have hfactor_nonneg : 0 ≤ 1 + 1 / α := by
    have hdiv_nonneg : 0 ≤ 1 / α := div_nonneg zero_le_one (le_of_lt hα)
    linarith
  intro n
  induction n with
  | zero =>
      intro _hm
      simp [h0]
  | succ k ih =>
      intro hk_succ
      have hk_lt : k < m := Nat.lt_of_succ_le hk_succ
      have hk_le : k ≤ m := Nat.le_of_lt hk_lt
      calc
        r (k + 1) ≤ (1 + 1 / α) * r k := hstep k hk_lt
        _ ≤ (1 + 1 / α) * ((1 + 1 / α) ^ k * ρ0) :=
          mul_le_mul_of_nonneg_left (ih hk_le) hfactor_nonneg
        _ = (1 + 1 / α) ^ (k + 1) * ρ0 := by ring

/-- **§11.1.1 printed-alpha finite-prefix growth recursion**: specialization
of `higham11_1_growth_factor_recursion_prefix` to the Bunch-Parlett value of
`α` and the final active stage `n-1`. -/
theorem higham11_1_growth_factor_bound_of_prefix_steps
    (n : ℕ) (ρ0 : ℝ) (r : ℕ → ℝ)
    (h0 : r 0 = ρ0)
    (hstep : ∀ k, k < n - 1 →
      r (k + 1) ≤ (1 + higham11_1_bunchParlettAlpha⁻¹) * r k) :
    r (n - 1) ≤ (1 + higham11_1_bunchParlettAlpha⁻¹) ^ (n - 1) * ρ0 := by
  have hα : 0 < higham11_1_bunchParlettAlpha := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
  have hstep' : ∀ k, k < n - 1 →
      r (k + 1) ≤ (1 + 1 / higham11_1_bunchParlettAlpha) * r k := by
    intro k hk
    simpa [one_div] using hstep k hk
  have h :=
    higham11_1_growth_factor_recursion_prefix
      higham11_1_bunchParlettAlpha ρ0 r (n - 1) hα h0 hstep' (n - 1)
      (le_refl _)
  simpa [one_div] using h

/-- **§11.1.1 normalized growth-factor bound**: if a concrete active pivot
path has normalized initial maximum `ρ₀ ≤ 1`, each prefix stage grows by at
most `1+α⁻¹`, and the advertised growth factor `ρₙ` is bounded by the final
stage maximum, then `ρₙ ≤ (1+α⁻¹)^(n-1)`. -/
theorem higham11_1_bunch_parlett_growth_bound_of_prefix_steps
    (n : ℕ) (ρ_n ρ0 : ℝ) (r : ℕ → ℝ)
    (h0 : r 0 = ρ0) (hρ0 : ρ0 ≤ 1)
    (hρn : ρ_n ≤ r (n - 1))
    (hstep : ∀ k, k < n - 1 →
      r (k + 1) ≤ (1 + higham11_1_bunchParlettAlpha⁻¹) * r k) :
    ρ_n ≤ (1 + higham11_1_bunchParlettAlpha⁻¹) ^ (n - 1) := by
  have hα : 0 < higham11_1_bunchParlettAlpha := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
  have hfactor_nonneg :
      0 ≤ (1 + higham11_1_bunchParlettAlpha⁻¹) ^ (n - 1) := by
    have hinv_nonneg : 0 ≤ higham11_1_bunchParlettAlpha⁻¹ :=
      inv_nonneg.mpr (le_of_lt hα)
    exact pow_nonneg (by linarith) _
  calc
    ρ_n ≤ r (n - 1) := hρn
    _ ≤ (1 + higham11_1_bunchParlettAlpha⁻¹) ^ (n - 1) * ρ0 :=
      higham11_1_growth_factor_bound_of_prefix_steps n ρ0 r h0 hstep
    _ ≤ (1 + higham11_1_bunchParlettAlpha⁻¹) ^ (n - 1) * 1 :=
      mul_le_mul_of_nonneg_left hρ0 hfactor_nonneg
    _ = (1 + higham11_1_bunchParlettAlpha⁻¹) ^ (n - 1) := by ring

/-- **Equation (11.4)**, the scalar entry of the 2 by 2 Schur complement
`b_ij - [c_i1 c_i2] E^{-1} [c_j1, c_j2]^T`. -/
noncomputable def higham11_4_twoByTwoSchurEntry
    (bij ci1 ci2 cj1 cj2 e11 e12 e21 e22 : ℝ) : ℝ :=
  bij - (ci1 * (e11 * cj1 + e12 * cj2) +
    ci2 * (e21 * cj1 + e22 * cj2))

/-- Complete-pivoting growth-bound interface:
`rho_n <= (1 + alpha^{-1})^(n-1)`. -/
theorem higham11_1_bunch_parlett_growth_bound (n : ℕ) (hn : 0 < n)
    (ρ_n : ℝ)
    (hρ : ρ_n ≤ (1 + higham11_1_bunchParlettAlpha⁻¹) ^ (n - 1)) :
    ρ_n ≤ (1 + higham11_1_bunchParlettAlpha⁻¹) ^ (n - 1) :=
  bunch_parlett_growth_bound n hn ρ_n hρ

/-- Complete-pivoting multiplier bound interface:
`|L_ij| <= max {1/alpha, 1/(1-alpha)}`. -/
theorem higham11_1_bunch_parlett_L_bound (n : ℕ)
    (L : Fin n → Fin n → ℝ)
    (c_bound : ℝ)
    (hc : c_bound =
      max (1 / higham11_1_bunchParlettAlpha)
          (1 / (1 - higham11_1_bunchParlettAlpha)))
    (hL : ∀ i j : Fin n, |L i j| ≤ c_bound) :
    ∀ i j : Fin n, |L i j| ≤ c_bound :=
  bunch_parlett_L_bound n L c_bound hc hL

/-- **§11.1.1 multiplier bound**, proved from the pivot-acceptance test: a 1×1
pivot `e` with `α·ω ≤ |e|` and off-pivot entries bounded by `ω` gives
multipliers `|c/e| ≤ 1/α`.  This is the honest derivation behind the
`bunch_parlett_L_bound` interface (`|L_ij| ≤ max{1/α, 1/(1-α)}`). -/
theorem higham11_1_oneByOne_multiplier_bound (c e ω α : ℝ)
    (hα : 0 < α) (hω : 0 < ω) (hc : |c| ≤ ω) (he : α * ω ≤ |e|) :
    |c / e| ≤ 1 / α :=
  oneByOne_multiplier_bound c e ω α hα hω hc he

/-- For the Bunch-Parlett/Bunch-Kaufman value `α=(1+√17)/8`, the scalar
one-pivot multiplier-row constant `1/α` is bounded by the source row-sum
constant `6`. -/
theorem higham11_4_oneByOne_multiplier_row_sum_const_le_six :
    1 / higham11_1_bunchParlettAlpha ≤ 6 := by
  have hlt : 1 / higham11_1_bunchParlettAlpha < 2 := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_kaufman_recip_alpha_lt_two
  linarith

/-- **Theorem 11.4 local 1×1 multiplier row-sum cap**: a scalar accepted pivot
with `αω≤|e|` gives the source-shaped one-entry row-sum cap `≤6`. -/
theorem higham11_4_oneByOne_multiplier_row_sum_le_six
    (c e ω : ℝ) (hω : 0 < ω)
    (he : higham11_1_bunchParlettAlpha * ω ≤ |e|)
    (hc : |c| ≤ ω) :
    |c / e| ≤ 6 := by
  have hα : 0 < higham11_1_bunchParlettAlpha := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
  exact
    (higham11_1_oneByOne_multiplier_bound
      c e ω higham11_1_bunchParlettAlpha hα hω hc he).trans
      higham11_4_oneByOne_multiplier_row_sum_const_le_six

/-- **§11.1.1 single-step element growth for a 1×1 pivot**:
`|b − c₁c₂/e| ≤ (1 + 1/α)·μ₀` when `α·μ₀ ≤ |e|` and all active entries are
bounded by `μ₀`.  This is the printed bound `|ã_ij| ≤ μ₀ + μ₀²/μ₁ ≤ (1+1/α)μ₀`
and the mechanism behind the growth-factor bound `ρₙ ≤ (1+α⁻¹)^{n−1}`. -/
theorem higham11_1_oneByOne_schur_growth (b c1 c2 e μ0 α : ℝ)
    (hα : 0 < α) (hμ : 0 < μ0)
    (hb : |b| ≤ μ0) (hc1 : |c1| ≤ μ0) (hc2 : |c2| ≤ μ0)
    (he : α * μ0 ≤ |e|) :
    |b - c1 * c2 / e| ≤ (1 + 1 / α) * μ0 :=
  oneByOne_schur_growth b c1 c2 e μ0 α hα hμ hb hc1 hc2 he

/-- **§11.1.1 2×2 pivot determinant bound**:
`det E = e₁₁e₂₂ − e₂₁² ≤ (α² − 1)μ₀²` for a complete-pivoting 2×2 block, and,
for `α ∈ [0,1)`, `|det E| ≥ (1 − α²)μ₀²`. -/
theorem higham11_4_twoByTwo_det_bound (e11 e22 e21 μ0 μ1 α : ℝ)
    (hμ1 : 0 ≤ μ1)
    (he11 : |e11| ≤ μ1) (he22 : |e22| ≤ μ1)
    (he21 : e21 ^ 2 = μ0 ^ 2) (hμ1α : μ1 ≤ α * μ0) :
    e11 * e22 - e21 ^ 2 ≤ (α ^ 2 - 1) * μ0 ^ 2 :=
  twoByTwo_completePivot_det_bound e11 e22 e21 μ0 μ1 α hμ1 he11 he22 he21 hμ1α

/-- **§11.1.1 2×2 pivot nonsingularity magnitude bound**:
`|det E| ≥ (1 − α²)μ₀²` for `α ∈ [0,1)`, the printed estimate used to bound
`E⁻¹` and hence the 2×2-step element growth `(1 + 2/(1−α))μ₀`. -/
theorem higham11_4_twoByTwo_absdet_lower (e11 e22 e21 μ0 μ1 α : ℝ)
    (hμ1 : 0 ≤ μ1) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (he11 : |e11| ≤ μ1) (he22 : |e22| ≤ μ1)
    (he21 : e21 ^ 2 = μ0 ^ 2) (hμ1α : μ1 ≤ α * μ0) :
    (1 - α ^ 2) * μ0 ^ 2 ≤ |e11 * e22 - e21 ^ 2| :=
  twoByTwo_completePivot_absdet_lower e11 e22 e21 μ0 μ1 α
    hμ1 hα0 hα1 he11 he22 he21 hμ1α

/-- **Eq (11.4) element growth for a 2×2 complete-pivoting step**:
the Schur entry `higham11_4_twoByTwoSchurEntry` built from inverse-block entries
`e₁₁,e₁₂,e₂₁,e₂₂` bounded by `|e₁₁|,|e₂₂| ≤ αK`, `|e₁₂|,|e₂₁| ≤ K` with
`K = 1/((1−α²)μ₀)`, and active entries `≤ μ₀`, satisfies
`|ã| ≤ (1 + 2/(1−α))·μ₀`.  This is the printed §11.1.1 bound and, with
`higham11_1_oneByOne_schur_growth`, completes both single-step growth bounds. -/
theorem higham11_4_twoByTwo_schur_growth
    (bij ci1 ci2 cj1 cj2 e11 e12 e21 e22 μ0 α K : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hμ : 0 < μ0)
    (hK : (1 - α ^ 2) * μ0 * K = 1)
    (hb : |bij| ≤ μ0)
    (hci1 : |ci1| ≤ μ0) (hci2 : |ci2| ≤ μ0)
    (hcj1 : |cj1| ≤ μ0) (hcj2 : |cj2| ≤ μ0)
    (he11 : |e11| ≤ α * K) (he12 : |e12| ≤ K)
    (he21 : |e21| ≤ K) (he22 : |e22| ≤ α * K) :
    |higham11_4_twoByTwoSchurEntry bij ci1 ci2 cj1 cj2 e11 e12 e21 e22|
      ≤ (1 + 2 / (1 - α)) * μ0 := by
  unfold higham11_4_twoByTwoSchurEntry
  exact twoByTwo_schur_growth bij ci1 ci2 cj1 cj2 e11 e12 e21 e22 μ0 α K
    hα0 hα1 hμ hK hb hci1 hci2 hcj1 hcj2 he11 he12 he21 he22

/-- **§11.1.1 printed inverse bound** `|E⁻¹| ≤ K·[[α,1],[1,α]]`, `K = 1/((1−α²)μ₀)`:
the entrywise bounds on `E⁻¹ = d⁻¹[[e₂₂,−e₂₁],[−e₂₁,e₁₁]]` for a complete-pivoting
2×2 block, derived from the determinant magnitude bound. -/
theorem higham11_4_twoByTwo_inverse_entry_bounds (e11 e22 e21 μ0 μ1 α K : ℝ)
    (hμ1 : 0 ≤ μ1) (hα0 : 0 ≤ α) (hα1 : α < 1) (hμ : 0 < μ0)
    (he11 : |e11| ≤ μ1) (he22 : |e22| ≤ μ1)
    (he21 : e21 ^ 2 = μ0 ^ 2) (hμ1α : μ1 ≤ α * μ0)
    (hK : (1 - α ^ 2) * μ0 * K = 1) :
    |e22 / (e11 * e22 - e21 ^ 2)| ≤ α * K
      ∧ |e11 / (e11 * e22 - e21 ^ 2)| ≤ α * K
      ∧ |e21 / (e11 * e22 - e21 ^ 2)| ≤ K :=
  twoByTwo_inverse_entry_bounds e11 e22 e21 μ0 μ1 α K
    hμ1 hα0 hα1 hμ he11 he22 he21 hμ1α hK

/-- **Theorem 11.4 local 2×2 multiplier row cap**, inverse-entry form:
if `|E⁻¹| ≤ K[[α,1],[1,α]]`, `K=1/((1−α²)μ₀)`, and the two entries of a
trailing row `C` are bounded by `μ₀`, then each component of `C E⁻¹` is bounded
by `1/(1−α)`.  This is the local 2×2 branch companion to the case-(1)/(3)
scalar multiplier caps from Algorithm 11.2. -/
theorem higham11_4_twoByTwo_multiplier_row_bound_of_inverse_entries
    (c1 c2 f11 f12 f21 f22 μ0 α K : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hμ : 0 < μ0)
    (hK : (1 - α ^ 2) * μ0 * K = 1)
    (hc1 : |c1| ≤ μ0) (hc2 : |c2| ≤ μ0)
    (hf11 : |f11| ≤ α * K) (hf12 : |f12| ≤ K)
    (hf21 : |f21| ≤ K) (hf22 : |f22| ≤ α * K) :
    |c1 * f11 + c2 * f21| ≤ 1 / (1 - α) ∧
      |c1 * f12 + c2 * f22| ≤ 1 / (1 - α) := by
  have hμ0 : 0 ≤ μ0 := le_of_lt hμ
  have hα2 : α ^ 2 < 1 := by nlinarith [hα0, hα1]
  have hden : 0 < (1 - α ^ 2) * μ0 := mul_pos (by linarith [hα2]) hμ
  have hK0 : 0 ≤ K := by nlinarith [hK, hden]
  have hαK : 0 ≤ α * K := mul_nonneg hα0 hK0
  have h1α : (0 : ℝ) < 1 - α := by linarith
  have hdiag :
      μ0 * (α * K) + μ0 * K = 1 / (1 - α) := by
    rw [eq_div_iff (ne_of_gt h1α)]
    nlinarith [hK]
  have hoff :
      μ0 * K + μ0 * (α * K) = 1 / (1 - α) := by
    rw [eq_div_iff (ne_of_gt h1α)]
    nlinarith [hK]
  have hc1f11 : |c1 * f11| ≤ μ0 * (α * K) := by
    rw [abs_mul]
    exact mul_le_mul hc1 hf11 (abs_nonneg _) hμ0
  have hc2f21 : |c2 * f21| ≤ μ0 * K := by
    rw [abs_mul]
    exact mul_le_mul hc2 hf21 (abs_nonneg _) hμ0
  have hc1f12 : |c1 * f12| ≤ μ0 * K := by
    rw [abs_mul]
    exact mul_le_mul hc1 hf12 (abs_nonneg _) hμ0
  have hc2f22 : |c2 * f22| ≤ μ0 * (α * K) := by
    rw [abs_mul]
    exact mul_le_mul hc2 hf22 (abs_nonneg _) hμ0
  refine ⟨?_, ?_⟩
  · calc
      |c1 * f11 + c2 * f21| ≤ |c1 * f11| + |c2 * f21| := abs_add_le _ _
      _ ≤ μ0 * (α * K) + μ0 * K := add_le_add hc1f11 hc2f21
      _ = 1 / (1 - α) := hdiag
  · calc
      |c1 * f12 + c2 * f22| ≤ |c1 * f12| + |c2 * f22| := abs_add_le _ _
      _ ≤ μ0 * K + μ0 * (α * K) := add_le_add hc1f12 hc2f22
      _ = 1 / (1 - α) := hoff

/-- **Theorem 11.4 local 2×2 multiplier row-sum cap**, inverse-entry form:
the two-component absolute row sum of `C E⁻¹` is bounded by `2/(1−α)`. -/
theorem higham11_4_twoByTwo_multiplier_row_sum_bound_of_inverse_entries
    (c1 c2 f11 f12 f21 f22 μ0 α K : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hμ : 0 < μ0)
    (hK : (1 - α ^ 2) * μ0 * K = 1)
    (hc1 : |c1| ≤ μ0) (hc2 : |c2| ≤ μ0)
    (hf11 : |f11| ≤ α * K) (hf12 : |f12| ≤ K)
    (hf21 : |f21| ≤ K) (hf22 : |f22| ≤ α * K) :
    |c1 * f11 + c2 * f21| + |c1 * f12 + c2 * f22| ≤
      2 / (1 - α) := by
  obtain ⟨hcol1, hcol2⟩ :=
    higham11_4_twoByTwo_multiplier_row_bound_of_inverse_entries
      c1 c2 f11 f12 f21 f22 μ0 α K hα0 hα1 hμ hK
      hc1 hc2 hf11 hf12 hf21 hf22
  have h1α : (0 : ℝ) < 1 - α := by linarith
  calc
    |c1 * f11 + c2 * f21| + |c1 * f12 + c2 * f22|
        ≤ 1 / (1 - α) + 1 / (1 - α) := add_le_add hcol1 hcol2
    _ = 2 / (1 - α) := by
          field_simp [ne_of_gt h1α]
          ring

/-- **Theorem 11.4 local 2×2 multiplier row cap**, pivot-block form:
instantiates the inverse-entry row cap with the actual inverse of
`E = [[e₁₁,e₂₁],[e₂₁,e₂₂]]`. -/
theorem higham11_4_twoByTwo_multiplier_row_bound_of_block
    (c1 c2 e11 e22 e21 μ0 μ1 α K : ℝ)
    (hμ1 : 0 ≤ μ1) (hα0 : 0 ≤ α) (hα1 : α < 1) (hμ : 0 < μ0)
    (he11 : |e11| ≤ μ1) (he22 : |e22| ≤ μ1)
    (he21 : e21 ^ 2 = μ0 ^ 2) (hμ1α : μ1 ≤ α * μ0)
    (hK : (1 - α ^ 2) * μ0 * K = 1)
    (hc1 : |c1| ≤ μ0) (hc2 : |c2| ≤ μ0) :
    |c1 * (e22 / (e11 * e22 - e21 ^ 2)) +
        c2 * (-(e21 / (e11 * e22 - e21 ^ 2)))| ≤ 1 / (1 - α) ∧
      |c1 * (-(e21 / (e11 * e22 - e21 ^ 2))) +
        c2 * (e11 / (e11 * e22 - e21 ^ 2))| ≤ 1 / (1 - α) := by
  obtain ⟨hInv22, hInv11, hInv21⟩ :=
    higham11_4_twoByTwo_inverse_entry_bounds e11 e22 e21 μ0 μ1 α K
      hμ1 hα0 hα1 hμ he11 he22 he21 hμ1α hK
  exact
    higham11_4_twoByTwo_multiplier_row_bound_of_inverse_entries c1 c2
      (e22 / (e11 * e22 - e21 ^ 2))
      (-(e21 / (e11 * e22 - e21 ^ 2)))
      (-(e21 / (e11 * e22 - e21 ^ 2)))
      (e11 / (e11 * e22 - e21 ^ 2)) μ0 α K
      hα0 hα1 hμ hK hc1 hc2 hInv22
      (by rw [abs_neg]; exact hInv21)
      (by rw [abs_neg]; exact hInv21) hInv11

/-- **Theorem 11.4 local 2×2 multiplier row-sum cap**, pivot-block form. -/
theorem higham11_4_twoByTwo_multiplier_row_sum_bound_of_block
    (c1 c2 e11 e22 e21 μ0 μ1 α K : ℝ)
    (hμ1 : 0 ≤ μ1) (hα0 : 0 ≤ α) (hα1 : α < 1) (hμ : 0 < μ0)
    (he11 : |e11| ≤ μ1) (he22 : |e22| ≤ μ1)
    (he21 : e21 ^ 2 = μ0 ^ 2) (hμ1α : μ1 ≤ α * μ0)
    (hK : (1 - α ^ 2) * μ0 * K = 1)
    (hc1 : |c1| ≤ μ0) (hc2 : |c2| ≤ μ0) :
    |c1 * (e22 / (e11 * e22 - e21 ^ 2)) +
        c2 * (-(e21 / (e11 * e22 - e21 ^ 2)))| +
      |c1 * (-(e21 / (e11 * e22 - e21 ^ 2))) +
        c2 * (e11 / (e11 * e22 - e21 ^ 2))| ≤ 2 / (1 - α) := by
  obtain ⟨hcol1, hcol2⟩ :=
    higham11_4_twoByTwo_multiplier_row_bound_of_block c1 c2 e11 e22 e21
      μ0 μ1 α K hμ1 hα0 hα1 hμ he11 he22 he21 hμ1α hK hc1 hc2
  have h1α : (0 : ℝ) < 1 - α := by linarith
  calc
    |c1 * (e22 / (e11 * e22 - e21 ^ 2)) +
        c2 * (-(e21 / (e11 * e22 - e21 ^ 2)))| +
      |c1 * (-(e21 / (e11 * e22 - e21 ^ 2))) +
        c2 * (e11 / (e11 * e22 - e21 ^ 2))|
        ≤ 1 / (1 - α) + 1 / (1 - α) := add_le_add hcol1 hcol2
    _ = 2 / (1 - α) := by
          field_simp [ne_of_gt h1α]
          ring

/-- The local 2×2 multiplier row-sum constant `2/(1−α)` is at most `6` when
`α≤2/3`. -/
theorem higham11_4_twoByTwo_multiplier_row_sum_const_le_six_of_alpha_le_two_thirds
    (α : ℝ) (hα : α ≤ 2 / 3) :
    2 / (1 - α) ≤ 6 := by
  have hden : (0 : ℝ) < 1 - α := by nlinarith
  rw [div_le_iff₀ hden]
  nlinarith

/-- For the Bunch-Parlett/Bunch-Kaufman value `α=(1+√17)/8`, the local 2×2
multiplier row-sum constant satisfies `2/(1−α)≤6`. -/
theorem higham11_4_twoByTwo_multiplier_row_sum_const_le_six :
    2 / (1 - higham11_1_bunchParlettAlpha) ≤ 6 := by
  have hα : higham11_1_bunchParlettAlpha ≤ 2 / 3 := by
    unfold higham11_1_bunchParlettAlpha bunchParlettAlpha
    have hsqrt : Real.sqrt 17 ≤ 13 / 3 := by
      rw [show (13 : ℝ) / 3 = Real.sqrt ((13 / 3) ^ 2) from
        (Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 13 / 3)).symm]
      exact Real.sqrt_le_sqrt (by norm_num : (17 : ℝ) ≤ (13 / 3) ^ 2)
    linarith
  exact higham11_4_twoByTwo_multiplier_row_sum_const_le_six_of_alpha_le_two_thirds
    higham11_1_bunchParlettAlpha hα

/-- **Theorem 11.4 local 2×2 multiplier row-sum cap**, source-alpha form:
with `α=(1+√17)/8`, the row sum of `C E⁻¹` is bounded by the source-shaped
constant `6`. -/
theorem higham11_4_twoByTwo_multiplier_row_sum_le_six_of_inverse_entries
    (c1 c2 f11 f12 f21 f22 μ0 K : ℝ)
    (hμ : 0 < μ0)
    (hK : (1 - higham11_1_bunchParlettAlpha ^ 2) * μ0 * K = 1)
    (hc1 : |c1| ≤ μ0) (hc2 : |c2| ≤ μ0)
    (hf11 : |f11| ≤ higham11_1_bunchParlettAlpha * K) (hf12 : |f12| ≤ K)
    (hf21 : |f21| ≤ K) (hf22 : |f22| ≤ higham11_1_bunchParlettAlpha * K) :
    |c1 * f11 + c2 * f21| + |c1 * f12 + c2 * f22| ≤ 6 := by
  have hα0 : 0 ≤ higham11_1_bunchParlettAlpha := by
    exact le_of_lt (by simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos)
  have hα1 : higham11_1_bunchParlettAlpha < 1 := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_lt_one
  exact
    (higham11_4_twoByTwo_multiplier_row_sum_bound_of_inverse_entries
      c1 c2 f11 f12 f21 f22 μ0 higham11_1_bunchParlettAlpha K
      hα0 hα1 hμ hK hc1 hc2 hf11 hf12 hf21 hf22).trans
      higham11_4_twoByTwo_multiplier_row_sum_const_le_six

/-- **Theorem 11.4 local 2×2 multiplier row-sum cap**, source-alpha pivot-block
form: the actual symmetric pivot block inverse gives row sum at most `6`. -/
theorem higham11_4_twoByTwo_multiplier_row_sum_le_six_of_block
    (c1 c2 e11 e22 e21 μ0 μ1 K : ℝ)
    (hμ1 : 0 ≤ μ1) (hμ : 0 < μ0)
    (he11 : |e11| ≤ μ1) (he22 : |e22| ≤ μ1)
    (he21 : e21 ^ 2 = μ0 ^ 2)
    (hμ1α : μ1 ≤ higham11_1_bunchParlettAlpha * μ0)
    (hK : (1 - higham11_1_bunchParlettAlpha ^ 2) * μ0 * K = 1)
    (hc1 : |c1| ≤ μ0) (hc2 : |c2| ≤ μ0) :
    |c1 * (e22 / (e11 * e22 - e21 ^ 2)) +
        c2 * (-(e21 / (e11 * e22 - e21 ^ 2)))| +
      |c1 * (-(e21 / (e11 * e22 - e21 ^ 2))) +
        c2 * (e11 / (e11 * e22 - e21 ^ 2))| ≤ 6 := by
  have hα0 : 0 ≤ higham11_1_bunchParlettAlpha := by
    exact le_of_lt (by simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos)
  have hα1 : higham11_1_bunchParlettAlpha < 1 := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_lt_one
  exact
    (higham11_4_twoByTwo_multiplier_row_sum_bound_of_block c1 c2 e11 e22 e21
      μ0 μ1 higham11_1_bunchParlettAlpha K hμ1 hα0 hα1 hμ he11 he22 he21
      hμ1α hK hc1 hc2).trans higham11_4_twoByTwo_multiplier_row_sum_const_le_six

/-- **§11.1.1 self-contained 2×2 growth**: substituting the actual inverse block
`E⁻¹` into the eq-(11.4) Schur entry, `|ã| ≤ (1 + 2/(1−α))μ₀` holds using only the
pivot-block data (no assumed inverse-entry bounds). -/
theorem higham11_4_twoByTwo_schur_growth_of_block
    (bij ci1 ci2 cj1 cj2 e11 e22 e21 μ0 μ1 α K : ℝ)
    (hμ1 : 0 ≤ μ1) (hα0 : 0 ≤ α) (hα1 : α < 1) (hμ : 0 < μ0)
    (he11 : |e11| ≤ μ1) (he22 : |e22| ≤ μ1)
    (he21 : e21 ^ 2 = μ0 ^ 2) (hμ1α : μ1 ≤ α * μ0)
    (hK : (1 - α ^ 2) * μ0 * K = 1)
    (hb : |bij| ≤ μ0)
    (hci1 : |ci1| ≤ μ0) (hci2 : |ci2| ≤ μ0)
    (hcj1 : |cj1| ≤ μ0) (hcj2 : |cj2| ≤ μ0) :
    |higham11_4_twoByTwoSchurEntry bij ci1 ci2 cj1 cj2
        (e22 / (e11 * e22 - e21 ^ 2)) (-(e21 / (e11 * e22 - e21 ^ 2)))
        (-(e21 / (e11 * e22 - e21 ^ 2))) (e11 / (e11 * e22 - e21 ^ 2))|
      ≤ (1 + 2 / (1 - α)) * μ0 := by
  unfold higham11_4_twoByTwoSchurEntry
  exact twoByTwo_schur_growth_of_block bij ci1 ci2 cj1 cj2 e11 e22 e21 μ0 μ1 α K
    hμ1 hα0 hα1 hμ he11 he22 he21 hμ1α hK hb hci1 hci2 hcj1 hcj2


end NumStability
