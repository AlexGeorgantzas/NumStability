/-
Chapter 11, Theorem 11.7 — **bounded element growth for Bunch's symmetric
tridiagonal pivoting (Algorithm 11.6), the derivation of `hfactor`.**

This module begins the multi-session derivation that discharges the tridiagonal
factor-norm hypothesis `hfactor` of `higham11_7_bunch_tridiagonal_backward_error`
*from the algorithm* (Route B of
`docs/source_coverage/higham_ch11_thm117_growth_blueprint.md`), replacing the
assumed `TriPivotData`.

Higham's Algorithm 11.6 uses a **fixed** scale `σ = ‖A‖_M =: M₀`, computed once at
the start, in every stage's pivot test.  With that fixed scale the element growth
is bounded by the **constant** `K = (1+γ₃)(1 + 1/α)` (α = (√5−1)/2), independent
of `n`, because:

  * each reduced-matrix corner is `(a non-corner diagonal ≤ M₀) − (correction)`
    (no compounding — the correction uses the fixed `M₀`, not the grown corner);
  * the per-step correction is `≤ M₀/α` for both pivot sizes
    (`flSchurCompl_corner_bound`, `flSchurCompl2_corner_bound`, already proved).

This file (session 1) establishes the foundational pieces:
  * `growthK` and its positivity;
  * `twoByTwo_corner_small` — a 2×2 pivot is chosen only when the corner is small
    (`|a₁₁| < α·M₀`), so a grown corner always forces a 1×1 step;
  * `oneByOne_corner_growth` / `twoByTwo_corner_growth` — the single-stage corner
    growth bounds at the fixed scale `σ = M₀`, packaging the existing per-step
    corner bounds into the uniform `≤ K·M₀` form.

The schedule-level induction (the growth invariant) and the product-entry
assembly are the subsequent sessions (see the blueprint).

No `sorry`/`admit`/`axiom`/`native_decide`.
-/
import NumStability.Algorithms.Cholesky.BunchTridiagonalFactorBoundCh11Closure

open scoped BigOperators

namespace NumStability.Ch11Closure.TriGrowthInv

open NumStability
open NumStability.Ch11Closure
open NumStability.Ch11Closure.Mixed
open NumStability.Ch11Closure.BunchTri
open NumStability.Ch11Closure.BunchTriGrowth
open NumStability.Ch11Closure.BunchTriFactor

/-- The tridiagonal-Bunch growth constant `K = (1+γ₃)(1 + 1/α)` (≈ 2.618·(1+γ₃)),
independent of the matrix dimension. -/
noncomputable def growthK (fp : FPModel) : ℝ :=
  (1 + gamma fp 3) * (1 + 1 / bunchTridiagonalAlpha)

theorem growthK_pos (fp : FPModel) (hval : gammaValid fp 3) : 0 < growthK fp := by
  have hγ : 0 ≤ gamma fp 3 := gamma_nonneg fp hval
  have hα : 0 < bunchTridiagonalAlpha := bunch_tridiagonal_alpha_pos
  have hinv : 0 < 1 / bunchTridiagonalAlpha := by positivity
  have : 0 < 1 + gamma fp 3 := by linarith
  have : 0 < 1 + 1 / bunchTridiagonalAlpha := by linarith
  unfold growthK; positivity

/-- **2×2 ⇒ small corner.**  If Algorithm 11.6 with the fixed scale `σ = M₀`
selects a 2×2 pivot, the pivot corner is small: `|a₁₁| < α·M₀ < M₀`.  Hence a
grown (`> α·M₀`) corner always triggers a 1×1 step — the mechanism that stops the
growth from compounding. -/
theorem twoByTwo_corner_small (M0 a11 a21 : ℝ) (hM0 : 0 < M0)
    (ha21 : |a21| ≤ M0)
    (hchoice : BunchTridiagonalPivotChoice M0 a11 a21 PivotSize.two) :
    |a11| < bunchTridiagonalAlpha * M0 := by
  have hthr : M0 * |a11| < bunchTridiagonalAlpha * a21 ^ 2 :=
    bunch_tridiagonal_pivot_choice_two_threshold M0 a11 a21 hchoice
  have hα : 0 < bunchTridiagonalAlpha := bunch_tridiagonal_alpha_pos
  have hsq : a21 ^ 2 ≤ M0 ^ 2 := by
    nlinarith [ha21, abs_nonneg a21, sq_abs a21]
  nlinarith [hthr, hsq, hα, hM0, mul_pos hM0 hM0]

/-- Helper: `(1+γ₃)·(M₀ + M₀/α) = K·M₀`.  (Pure ring identity — `M₀/α = M₀·α⁻¹`
is treated atomically, no `α ≠ 0` needed.) -/
theorem growth_rhs_eq (fp : FPModel) (M0 : ℝ) :
    (1 + gamma fp 3) * (M0 + M0 / bunchTridiagonalAlpha) = growthK fp * M0 := by
  unfold growthK; ring

/-- **Single-stage 1×1 corner growth (fixed scale).**  For a symmetric tridiagonal
stage whose fed diagonal `A₁₁` (the entry that becomes the new corner) is `≤ M₀`
and whose 1×1 pivot is accepted at the fixed scale `σ = M₀`, the reduced corner
satisfies `|flSchurCompl A 0 0| ≤ K·M₀`. -/
theorem oneByOne_corner_growth (fp : FPModel) (hval : gammaValid fp 3) {n : ℕ}
    (A : Fin (n + 2) → Fin (n + 2) → ℝ) (hA : IsSymTridiagonal (n + 2) A)
    (M0 : ℝ) (hM0 : 0 < M0)
    (hfed : |A ((0 : Fin (n + 1)).succ) ((0 : Fin (n + 1)).succ)| ≤ M0)
    (hchoice : BunchTridiagonalPivotChoice M0 (A 0 0)
      (A ((0 : Fin (n + 1)).succ) 0) PivotSize.one)
    (ha11 : A 0 0 ≠ 0) :
    |flSchurCompl (n + 1) fp A 0 0| ≤ growthK fp * M0 := by
  have hb := flSchurCompl_corner_bound fp hval A hA M0 M0 (le_refl M0) hchoice ha11
  have hγ : 0 ≤ 1 + gamma fp 3 := by have := gamma_nonneg fp hval; linarith
  calc |flSchurCompl (n + 1) fp A 0 0|
      ≤ (1 + gamma fp 3) *
          (|A ((0 : Fin (n + 1)).succ) ((0 : Fin (n + 1)).succ)|
            + M0 / bunchTridiagonalAlpha) := hb
    _ ≤ (1 + gamma fp 3) * (M0 + M0 / bunchTridiagonalAlpha) := by
        apply mul_le_mul_of_nonneg_left _ hγ
        linarith [hfed]
    _ = growthK fp * M0 := growth_rhs_eq fp M0

/-- **Single-stage 2×2 corner growth (fixed scale).**  For a symmetric tridiagonal
stage whose fed diagonal `A₂₂` and off-corner coupling `anext = A₂₁` are `≤ M₀` and
whose 2×2 pivot is accepted at the fixed scale `σ = M₀`, the reduced corner
satisfies `|flSchurCompl2 A 0 0| ≤ K·M₀`.  (The `anext²/(M₀·α)` correction is
`≤ M₀/α` because `anext ≤ M₀`.) -/
theorem twoByTwo_corner_growth (fp : FPModel) (hval : gammaValid fp 3) {m : ℕ}
    (A : Fin (m + 3) → Fin (m + 3) → ℝ) (hA : IsSymTridiagonal (m + 3) A)
    (M0 : ℝ) (hM0 : 0 < M0)
    (hfed : |A ((0 : Fin (m + 1)).succ.succ) ((0 : Fin (m + 1)).succ.succ)| ≤ M0)
    (hanext : |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| ≤ M0)
    (ha22 : |A (oneIdx (m + 1)) (oneIdx (m + 1))| ≤ M0)
    (hchoice : BunchTridiagonalPivotChoice M0 (A 0 0)
      (A (oneIdx (m + 1)) 0) PivotSize.two) :
    |flSchurCompl2 (m + 1) fp A 0 0| ≤ growthK fp * M0 := by
  have hb := flSchurCompl2_corner_bound fp hval A hA M0 hM0 hchoice ha22
  have hγ : 0 ≤ 1 + gamma fp 3 := by have := gamma_nonneg fp hval; linarith
  have hα : 0 < bunchTridiagonalAlpha := bunch_tridiagonal_alpha_pos
  have hden : 0 < M0 * bunchTridiagonalAlpha := mul_pos hM0 hα
  set anext := A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1)) with hanextdef
  have hsq : anext ^ 2 ≤ M0 ^ 2 := by nlinarith [hanext, abs_nonneg anext, sq_abs anext]
  have hcorr : anext ^ 2 / (M0 * bunchTridiagonalAlpha) ≤ M0 / bunchTridiagonalAlpha := by
    have heq : M0 / bunchTridiagonalAlpha - anext ^ 2 / (M0 * bunchTridiagonalAlpha)
        = (M0 ^ 2 - anext ^ 2) / (M0 * bunchTridiagonalAlpha) := by
      field_simp [ne_of_gt hM0, ne_of_gt hα]
    have hnn : 0 ≤ (M0 ^ 2 - anext ^ 2) / (M0 * bunchTridiagonalAlpha) :=
      div_nonneg (by linarith [hsq]) (le_of_lt hden)
    have : 0 ≤ M0 / bunchTridiagonalAlpha - anext ^ 2 / (M0 * bunchTridiagonalAlpha) := by
      rw [heq]; exact hnn
    linarith
  calc |flSchurCompl2 (m + 1) fp A 0 0|
      ≤ (1 + gamma fp 3) *
          (|A ((0 : Fin (m + 1)).succ.succ) ((0 : Fin (m + 1)).succ.succ)|
            + anext ^ 2 / (M0 * bunchTridiagonalAlpha)) := hb
    _ ≤ (1 + gamma fp 3) * (M0 + M0 / bunchTridiagonalAlpha) := by
        apply mul_le_mul_of_nonneg_left _ hγ
        linarith [hfed, hcorr]
    _ = growthK fp * M0 := growth_rhs_eq fp M0

/-! ## Session 2 building block — the decoupled determinant lower bound

For the schedule induction the pivot test is at the fixed scale `σ = M₀`, but the
reduced-matrix entries at stage `ℓ` are only bounded by `τ := (1+u)^ℓ M₀ ≥ σ` (each
off-corner entry picks up one `(1+u)` per stage).  The existing 2×2 determinant lower
bound requires `|a₂₂| ≤ σ` (the test scale); here we **decouple** the entry bound `τ`
from the test scale `σ`.  Because `|a₁₁| ≤ α a₂₁²/σ` (2×2 test) and `|a₂₂| ≤ τ`,

  `|det| = |a₁₁a₂₂ − a₂₁²| ≥ a₂₁² − |a₁₁||a₂₂| ≥ a₂₁²·(1 − α·τ/σ)`,

which stays positive as long as `α·τ/σ < 1` (e.g. `τ/σ = (1+u)^ℓ ≤ 1.01 < 1/α`). -/
theorem twoByTwo_absdet_lower_decoupled (σ τ a11 a21 a22 : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσ : 0 < σ) (hτ : |a22| ≤ τ) :
    a21 ^ 2 * (1 - bunchTridiagonalAlpha * τ / σ) ≤ |a11 * a22 - a21 ^ 2| := by
  have hα : 0 < bunchTridiagonalAlpha := bunch_tridiagonal_alpha_pos
  have htest := bunch_tridiagonal_pivot_choice_two_threshold σ a11 a21 hchoice
  have ha11 : |a11| ≤ bunchTridiagonalAlpha * a21 ^ 2 / σ := by
    rw [le_div_iff₀ hσ]; nlinarith [htest]
  have hb_nonneg : (0 : ℝ) ≤ bunchTridiagonalAlpha * a21 ^ 2 / σ :=
    div_nonneg (mul_nonneg (le_of_lt hα) (sq_nonneg a21)) (le_of_lt hσ)
  have hprod : |a11 * a22| ≤ bunchTridiagonalAlpha * a21 ^ 2 / σ * τ := by
    rw [abs_mul]; exact mul_le_mul ha11 hτ (abs_nonneg _) hb_nonneg
  have hrev : a21 ^ 2 - |a11 * a22| ≤ |a11 * a22 - a21 ^ 2| := by
    have h := abs_sub_abs_le_abs_sub (a21 ^ 2) (a11 * a22)
    rwa [abs_of_nonneg (sq_nonneg a21), abs_sub_comm] at h
  calc a21 ^ 2 * (1 - bunchTridiagonalAlpha * τ / σ)
      = a21 ^ 2 - bunchTridiagonalAlpha * a21 ^ 2 / σ * τ := by ring
    _ ≤ a21 ^ 2 - |a11 * a22| := by linarith [hprod]
    _ ≤ |a11 * a22 - a21 ^ 2| := hrev

/-- Division-free form of the decoupled determinant lower bound:
`a₂₁²·(σ − α·τ) ≤ σ·|det|` (nlinarith-friendly for downstream use). -/
theorem twoByTwo_absdet_lower_decoupled' (σ τ a11 a21 a22 : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσ : 0 < σ) (hτ : |a22| ≤ τ) :
    a21 ^ 2 * (σ - bunchTridiagonalAlpha * τ) ≤ σ * |a11 * a22 - a21 ^ 2| := by
  have hα : 0 < bunchTridiagonalAlpha := bunch_tridiagonal_alpha_pos
  have htest := bunch_tridiagonal_pivot_choice_two_threshold σ a11 a21 hchoice
  have hrev : a21 ^ 2 - |a11 * a22| ≤ |a11 * a22 - a21 ^ 2| := by
    have h := abs_sub_abs_le_abs_sub (a21 ^ 2) (a11 * a22)
    rwa [abs_of_nonneg (sq_nonneg a21), abs_sub_comm] at h
  have hprod : σ * |a11 * a22| ≤ bunchTridiagonalAlpha * a21 ^ 2 * τ := by
    rw [abs_mul]
    calc σ * (|a11| * |a22|) = (σ * |a11|) * |a22| := by ring
      _ ≤ (bunchTridiagonalAlpha * a21 ^ 2) * τ :=
          mul_le_mul (le_of_lt htest) hτ (abs_nonneg _)
            (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hrev (le_of_lt hσ), hprod]

/-- **Decoupled 2×2 corner correction bound.**  With the pivot test at scale `σ`
and the block diagonal `a₂₂` bounded by `τ ≥ σ` (the entry scale), the exact 2×2
Schur correction satisfies

  `|anext²·(a₁₁/det)| ≤ anext²·α / (σ − α·τ)`,

provided `α·τ < σ` (so `det ≠ 0`).  This is the `(1+u)`-slack-tolerant analogue of
`tridiag_twoByTwo_corner_correction_le_of_choice`; with `τ = σ` it reduces to
`anext²·α/(σ(1−α)) = anext²/(σα)` (using `α² = 1−α`). -/
theorem tridiag_twoByTwo_corner_correction_le_decoupled
    (σ τ a11 a21 a22 anext : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσ : 0 < σ) (hτ : |a22| ≤ τ) (hslack : bunchTridiagonalAlpha * τ < σ) :
    |anext * anext * (a11 / (a11 * a22 - a21 ^ 2))|
      ≤ anext ^ 2 * bunchTridiagonalAlpha / (σ - bunchTridiagonalAlpha * τ) := by
  have hα : 0 < bunchTridiagonalAlpha := bunch_tridiagonal_alpha_pos
  have htest := bunch_tridiagonal_pivot_choice_two_threshold σ a11 a21 hchoice
  have ha21 : a21 ≠ 0 :=
    bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_sigma_nonneg σ a11 a21 hchoice (le_of_lt hσ)
  have ha21sq : 0 < a21 ^ 2 := sq_pos_of_ne_zero ha21
  have hd : 0 < σ - bunchTridiagonalAlpha * τ := by linarith
  have hdet_lb : a21 ^ 2 * (σ - bunchTridiagonalAlpha * τ) ≤ σ * |a11 * a22 - a21 ^ 2| :=
    twoByTwo_absdet_lower_decoupled' σ τ a11 a21 a22 hchoice hσ hτ
  have hσdet : 0 < σ * |a11 * a22 - a21 ^ 2| := lt_of_lt_of_le (mul_pos ha21sq hd) hdet_lb
  have hdetpos : 0 < |a11 * a22 - a21 ^ 2| := by
    rcases (abs_nonneg (a11 * a22 - a21 ^ 2)).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hσdet; exact absurd hσdet (lt_irrefl 0)
  -- key scalar inequality |a11|·(σ−ατ) ≤ α·|det|
  have hkey : |a11| * (σ - bunchTridiagonalAlpha * τ)
      ≤ bunchTridiagonalAlpha * |a11 * a22 - a21 ^ 2| := by
    have h1 : σ * (|a11| * (σ - bunchTridiagonalAlpha * τ))
        ≤ σ * (bunchTridiagonalAlpha * |a11 * a22 - a21 ^ 2|) := by
      nlinarith [mul_le_mul_of_nonneg_right (le_of_lt htest) (le_of_lt hd),
        mul_le_mul_of_nonneg_left hdet_lb (le_of_lt hα)]
    exact le_of_mul_le_mul_left h1 hσ
  have hLHS : |anext * anext * (a11 / (a11 * a22 - a21 ^ 2))|
      = anext ^ 2 * |a11| / |a11 * a22 - a21 ^ 2| := by
    rw [abs_mul, abs_div]
    have hsq : |anext * anext| = anext ^ 2 := by
      rw [← pow_two, abs_of_nonneg (sq_nonneg anext)]
    rw [hsq]; ring
  rw [hLHS, div_le_iff₀ hdetpos, div_mul_eq_mul_div, le_div_iff₀ hd]
  nlinarith [mul_le_mul_of_nonneg_left hkey (sq_nonneg anext)]

/-- **Decoupled per-step corner bound (2×2).**  The `(1+u)`-slack-tolerant analogue
of `flSchurCompl2_corner_bound`: the pivot test is at scale `σ` (the fixed `M₀`),
while the fed diagonal `a₂₂` is only bounded by `τ ≥ σ`.  The reduced corner then
satisfies

  `|flSchurCompl2 A 0 0| ≤ (1+γ₃)·(|A₂₂| + anext²·α/(σ − α·τ))`,

with `anext = A₂₁` the off-corner coupling.  This is the schedule-induction-ready
2×2 corner bound (Route B step 2). -/
theorem flSchurCompl2_corner_bound_decoupled (fp : FPModel) (hval : gammaValid fp 3) {m : ℕ}
    (A : Fin (m + 3) → Fin (m + 3) → ℝ) (hA : IsSymTridiagonal (m + 3) A)
    (σ τ : ℝ) (hσpos : 0 < σ)
    (hchoice : BunchTridiagonalPivotChoice σ (A 0 0) (A (oneIdx (m + 1)) 0) PivotSize.two)
    (hτa22 : |A (oneIdx (m + 1)) (oneIdx (m + 1))| ≤ τ)
    (hslack : bunchTridiagonalAlpha * τ < σ) :
    |flSchurCompl2 (m + 1) fp A 0 0|
      ≤ (1 + gamma fp 3) *
          (|A ((0 : Fin (m + 1)).succ.succ) ((0 : Fin (m + 1)).succ.succ)|
            + (A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))) ^ 2
                * bunchTridiagonalAlpha / (σ - bunchTridiagonalAlpha * τ)) := by
  set b := A ((0 : Fin (m + 1)).succ.succ) ((0 : Fin (m + 1)).succ.succ) with hb
  set anext := A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1)) with hanext
  set a11 := A 0 0 with ha11
  set a22 := A (oneIdx (m + 1)) (oneIdx (m + 1)) with ha22
  set a21 := A (oneIdx (m + 1)) 0 with ha21
  have hsym : A 0 (oneIdx (m + 1)) = a21 := hA.1 0 (oneIdx (m + 1))
  have hdeteq : mixedDet2 (m + 1) A = a11 * a22 - a21 ^ 2 := by
    unfold mixedDet2; rw [hsym]; ring
  have hcorner := flSchurCompl2_corner_eq fp A hA
  rw [hdeteq] at hcorner
  obtain ⟨Δ, hΔ, hstep⟩ :=
    fl_tridiagonal_twoByTwo_schur_step_error fp b anext (a11 / (a11 * a22 - a21 ^ 2)) hval
  rw [hstep] at hcorner
  have hcorr : |anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext|
      ≤ anext ^ 2 * bunchTridiagonalAlpha / (σ - bunchTridiagonalAlpha * τ) := by
    have hcomm : anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext
        = anext * anext * (a11 / (a11 * a22 - a21 ^ 2)) := by ring
    rw [hcomm]
    exact tridiag_twoByTwo_corner_correction_le_decoupled σ τ a11 a21 a22 anext
      hchoice hσpos hτa22 hslack
  have hγ0 : 0 ≤ gamma fp 3 := gamma_nonneg fp hval
  rw [hcorner]
  have htri : |(b - anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext) + Δ|
      ≤ |b - anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext| + |Δ| := abs_add_le _ _
  have hsub : |b - anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext|
      ≤ |b| + |anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext| := abs_sub _ _
  calc |(b - anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext) + Δ|
      ≤ |b - anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext| + |Δ| := htri
    _ ≤ (|b| + |anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext|)
          + gamma fp 3 * (|b| + |anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext|) :=
        add_le_add hsub hΔ
    _ = (1 + gamma fp 3) * (|b| + |anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext|) := by ring
    _ ≤ (1 + gamma fp 3) *
          (|b| + anext ^ 2 * bunchTridiagonalAlpha / (σ - bunchTridiagonalAlpha * τ)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        linarith [hcorr]

/-! ## Session 3 — growth-invariant prerequisites

Building blocks for the schedule-level growth induction (Route B): the sharper `α`
bound needed for the slack condition, the `(1+u)^ℓ` band-growth cap, the 1×1
off-corner reduction (the missing analogue of `flSchurCompl2_eq_sub_zero_of_ne_corner`),
and the fixed-`M₀` run predicate `TriGrowthData`. -/

/-- Sharper bound `α < 3/4` (from `√5 < 5/2`), needed for the slack
`α·(1+u)^ℓ < 1` (since `α·(1+γₙ) ≤ (3/4)(1+1/99) < 1`). -/
theorem alpha_lt_three_quarters : bunchTridiagonalAlpha < 3 / 4 := by
  unfold bunchTridiagonalAlpha
  have h : Real.sqrt 5 < 5 / 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  linarith

/-- **Band-growth cap.**  Off-corner entries pick up one `(1+u)` per stage, so over
`ℓ ≤ n` stages the accumulated factor is `≤ 1 + γₙ`. -/
theorem one_add_u_pow_le (fp : FPModel) {n l : ℕ} (hln : l ≤ n)
    (hvaln : gammaValid fp n) (hval1 : gammaValid fp 1) :
    (1 + fp.u) ^ l ≤ 1 + gamma fp n := by
  have hu1 : fp.u < 1 := by have h := hval1; unfold gammaValid at h; simpa using h
  have hu_le : fp.u ≤ gamma fp 1 := by
    unfold gamma
    rw [Nat.cast_one, one_mul, le_div_iff₀ (by linarith : (0 : ℝ) < 1 - fp.u)]
    nlinarith [fp.u_nonneg, sq_nonneg fp.u]
  have hvaln1 : gammaValid fp (n * 1) := by rw [Nat.mul_one]; exact hvaln
  have hn := one_add_pow_sub_one_le_gamma_mul_of_le_gamma fp n 1 fp.u_nonneg hu_le hvaln1
  rw [Nat.mul_one] at hn
  have hbase : (1 : ℝ) ≤ 1 + fp.u := by have := fp.u_nonneg; linarith
  have hpow : (1 + fp.u) ^ l ≤ (1 + fp.u) ^ n := pow_le_pow_right₀ hbase hln
  linarith [hpow, hn]

/-- **1×1 off-corner reduction** (the missing analogue of
`flSchurCompl2_eq_sub_zero_of_ne_corner`).  For a symmetric tridiagonal `A` with
nonzero pivot, every non-corner entry of the 1×1 Schur complement is the trailing
datum through a single subtraction from zero. -/
theorem flSchurCompl_eq_sub_zero_of_ne_corner (fp : FPModel) {n : ℕ}
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) (hA : IsSymTridiagonal (n + 1) A)
    (hA00 : A 0 0 ≠ 0) (i j : Fin n) (hne : i.val ≠ 0 ∨ j.val ≠ 0) :
    flSchurCompl n fp A i j = fp.fl_sub (A i.succ j.succ) 0 := by
  have hcorr : fp.fl_mul (fp.fl_div (A i.succ 0) (A 0 0)) (A 0 j.succ) = 0 := by
    rcases Nat.eq_zero_or_pos j.val with hj | hj
    · have hi1 : 1 ≤ i.val := by rcases hne with h | h <;> omega
      have hci0 : A i.succ 0 = 0 := by
        apply hA.2; right; simp only [Fin.val_succ, Fin.val_zero]; omega
      rw [hci0, fl_div_zero_left fp (A 0 0) hA00, fl_mul_left_zero]
    · have hcj : A 0 j.succ = 0 := by
        apply hA.2; left; simp only [Fin.val_succ, Fin.val_zero]; omega
      rw [hcj, fl_mul_right_zero]
  unfold flSchurCompl
  rw [hcorr]

/-- **Off-corner band-growth step (1×1).**  `|flSchurCompl A i j| ≤ (1+u)·|A_{i+1,j+1}|`
for `(i,j) ≠ (0,0)` — the 1×1 analogue of `flSchurCompl2_offcorner_bound`. -/
theorem flSchurCompl_offcorner_bound (fp : FPModel) {n : ℕ}
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) (hA : IsSymTridiagonal (n + 1) A)
    (hA00 : A 0 0 ≠ 0) (i j : Fin n) (hne : i.val ≠ 0 ∨ j.val ≠ 0) :
    |flSchurCompl n fp A i j| ≤ (1 + fp.u) * |A i.succ j.succ| := by
  rw [flSchurCompl_eq_sub_zero_of_ne_corner fp A hA hA00 i j hne]
  obtain ⟨δ, hδ, heq⟩ := fl_sub_zero_right fp (A i.succ j.succ)
  rw [heq, abs_mul]
  have h1 : |1 + δ| ≤ 1 + fp.u := by
    calc |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ ≤ 1 + fp.u := by rw [abs_one]; linarith
  calc |A i.succ j.succ| * |1 + δ| ≤ |A i.succ j.succ| * (1 + fp.u) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = (1 + fp.u) * |A i.succ j.succ| := by ring

/-- **Fixed-`M₀` Bunch run predicate.**  Records, along the schedule, only the
structural facts and the Algorithm-11.6 pivot choices *at the fixed scale
`σ = M₀ = ‖A‖_M`* (Higham's "compute σ once").  Unlike `TriPivotData` it does NOT
bundle a per-stage "σ bounds all entries" clause — the entry bound `(1+u)^ℓ·M₀` is
the *conclusion* of the growth induction, not a hypothesis. -/
def TriGrowthData (fp : FPModel) (M0 : ℝ) :
    {k : ℕ} → PivotSchedule k → (Fin k → Fin k → ℝ) → Prop
  | 0, .nil, _ => True
  | n + 1, .consOne s, A =>
      IsSymTridiagonal (n + 1) A ∧ A 0 0 ≠ 0 ∧
      (∀ i : Fin n, BunchTridiagonalPivotChoice M0 (A 0 0) (A i.succ 0) PivotSize.one) ∧
      TriGrowthData fp M0 s (flSchurCompl n fp A)
  | n + 2, .consTwo s, A =>
      IsSymTridiagonal (n + 2) A ∧
      BunchTridiagonalPivotChoice M0 (A 0 0) (A (oneIdx n) 0) PivotSize.two ∧
      TriGrowthData fp M0 s (flSchurCompl2 n fp A)

@[simp] theorem TriGrowthData_consOne (fp : FPModel) (M0 : ℝ) {n : ℕ}
    (s : PivotSchedule n) (A : Fin (n + 1) → Fin (n + 1) → ℝ) :
    TriGrowthData fp M0 s.consOne A ↔
      (IsSymTridiagonal (n + 1) A ∧ A 0 0 ≠ 0 ∧
        (∀ i : Fin n, BunchTridiagonalPivotChoice M0 (A 0 0) (A i.succ 0) PivotSize.one) ∧
        TriGrowthData fp M0 s (flSchurCompl n fp A)) := Iff.rfl

@[simp] theorem TriGrowthData_consTwo (fp : FPModel) (M0 : ℝ) {n : ℕ}
    (s : PivotSchedule n) (A : Fin (n + 2) → Fin (n + 2) → ℝ) :
    TriGrowthData fp M0 s.consTwo A ↔
      (IsSymTridiagonal (n + 2) A ∧
        BunchTridiagonalPivotChoice M0 (A 0 0) (A (oneIdx n) 0) PivotSize.two ∧
        TriGrowthData fp M0 s (flSchurCompl2 n fp A)) := Iff.rfl

/-! ## The actual Algorithm 11.6 schedule

`TriGrowthData` records a completed run, but the schedule itself need not be an
input.  The following function performs the printed threshold test at every
rounded Schur complement.  The accompanying theorem proves that this computed
schedule carries `TriGrowthData`; its only extra premise is scalar-pivot
nonbreakdown on the branches on which the printed test selects a `1 × 1`
pivot.  This is a domain-of-definition condition, not a stability conclusion.
-/

/-- The pivot-size schedule computed by Higham's Algorithm 11.6, using the
fixed initial scale `M0` at every rounded Schur-complement stage. -/
noncomputable def bunchTridiagonalSchedule (fp : FPModel) (M0 : ℝ) :
    {n : ℕ} → (Fin n → Fin n → ℝ) → PivotSchedule n
  | 0, _ => .nil
  | 1, _ => .consOne .nil
  | n + 2, A =>
      if M0 * |A 0 0| ≥ bunchTridiagonalAlpha * (A (oneIdx n) 0) ^ 2 then
        .consOne (bunchTridiagonalSchedule fp M0 (flSchurCompl (n + 1) fp A))
      else
        .consTwo (bunchTridiagonalSchedule fp M0 (flSchurCompl2 n fp A))

/-- Scalar-pivot nonbreakdown for a specified mixed-pivot run.  Two-by-two
pivots need no clause here: Algorithm 11.6 plus the stage entry bound proves
their exact nonsingularity separately. -/
def BunchTridiagonalScalarNoBreakdown (fp : FPModel) :
    {n : ℕ} → PivotSchedule n → (Fin n → Fin n → ℝ) → Prop
  | 0, .nil, _ => True
  | n + 1, .consOne s, A =>
      A 0 0 ≠ 0 ∧
        BunchTridiagonalScalarNoBreakdown fp s (flSchurCompl n fp A)
  | n + 2, .consTwo s, A =>
      BunchTridiagonalScalarNoBreakdown fp s (flSchurCompl2 n fp A)

/-- The schedule producer satisfies the fixed-scale Algorithm 11.6 run
predicate.  In a tridiagonal matrix the non-corner entries of the first column
are zero, so a selected `1 × 1` test against the first subdiagonal automatically
certifies the same branch predicate for every trailing row. -/
theorem TriGrowthData_bunchTridiagonalSchedule (fp : FPModel) (M0 : ℝ)
    (hM0 : 0 ≤ M0) : ∀ {n : ℕ} (A : Fin n → Fin n → ℝ),
      IsSymTridiagonal n A →
      BunchTridiagonalScalarNoBreakdown fp (bunchTridiagonalSchedule fp M0 A) A →
      TriGrowthData fp M0 (bunchTridiagonalSchedule fp M0 A) A
  | 0, A, _, _ => True.intro
  | 1, A, hA, hnb => by
      rw [show bunchTridiagonalSchedule fp M0 A = (.nil : PivotSchedule 0).consOne by
        rfl]
      refine ⟨hA, ?_, ?_, True.intro⟩
      · exact hnb.1
      · intro i
        exact Fin.elim0 i
  | n + 2, A, hA, hnb => by
      by_cases htest :
          M0 * |A 0 0| ≥ bunchTridiagonalAlpha * (A (oneIdx n) 0) ^ 2
      · rw [bunchTridiagonalSchedule, if_pos htest]
        rw [bunchTridiagonalSchedule, if_pos htest] at hnb
        refine ⟨hA, hnb.1, ?_, ?_⟩
        · intro i
          by_cases hi : i.val = 0
          · have hi0 : i = 0 := Fin.ext hi
            subst hi0
            exact bunch_tridiagonal_pivot_choice_one_of_threshold M0 (A 0 0)
              (A (oneIdx n) 0) htest
          · have hzero : A i.succ 0 = 0 := by
              apply hA.2
              right
              simp only [Fin.val_succ, Fin.val_zero]
              omega
            apply bunch_tridiagonal_pivot_choice_one_of_threshold
            rw [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
            exact mul_nonneg hM0 (abs_nonneg _)
        · exact TriGrowthData_bunchTridiagonalSchedule fp M0 hM0
            (flSchurCompl (n + 1) fp A)
            (flSchurCompl_isSymTridiagonal fp A hA hnb.1) hnb.2
      · rw [bunchTridiagonalSchedule, if_neg htest]
        rw [bunchTridiagonalSchedule, if_neg htest] at hnb
        refine ⟨hA, ?_, ?_⟩
        · exact bunch_tridiagonal_pivot_choice_two_of_threshold M0 (A 0 0)
            (A (oneIdx n) 0) (lt_of_not_ge htest)
        · exact TriGrowthData_bunchTridiagonalSchedule fp M0 hM0
            (flSchurCompl2 n fp A)
            (flSchurCompl2_isSymTridiagonal fp A hA) hnb

/-! ## Session 4 — decoupled 2x2 product-path arithmetic cores
(σ = fixed test scale M0; τ ≥ σ = entry bound; adapted from the coupled
`corner_quadform_core` / `corner_rowcol_le_core` via the decoupled determinant
identity `a21²·(σ−ατ) ≤ σ·D`.  At τ=σ they reduce to the coupled bounds via α²=1−α.) -/

theorem corner_quadform_core_decoupled
    (u σ τ a11abs a21abs a22abs anextabs w0 w1 D : ℝ)
    (hu : 0 ≤ u) (hσ : 0 < σ)
    (ha11abs : 0 ≤ a11abs) (ha21abs : 0 < a21abs)
    (ha22abs : 0 ≤ a22abs) (hanextabs : 0 ≤ anextabs)
    (hw0 : 0 ≤ w0) (hw1 : 0 ≤ w1) (hDpos : 0 < D)
    (hslack : bunchTridiagonalAlpha * τ < σ)
    (hDlow : a21abs ^ 2 * (σ - bunchTridiagonalAlpha * τ) ≤ σ * D)
    (htest : σ * a11abs ≤ bunchTridiagonalAlpha * a21abs ^ 2)
    (ha22 : a22abs ≤ τ) (hanext : anextabs ≤ τ) :
    w0 * D ≤ (1 + u) * anextabs * a21abs → w1 * D ≤ (1 + u) * anextabs * a11abs →
    w0 ^ 2 * a11abs + 2 * w0 * w1 * a21abs + w1 ^ 2 * a22abs
      ≤ (1 + u) ^ 2 * bunchTridiagonalAlpha * τ ^ 2 * (3 * σ + bunchTridiagonalAlpha * τ)
          / (σ - bunchTridiagonalAlpha * τ) ^ 2 := by
  intro hw0D hw1D
  have hα : 0 < bunchTridiagonalAlpha := bunch_tridiagonal_alpha_pos
  have hα1 : bunchTridiagonalAlpha < 1 := bunch_tridiagonal_alpha_lt_one
  set α := bunchTridiagonalAlpha with hαdef
  have h1u : (0 : ℝ) ≤ 1 + u := by linarith
  have hσ0 : 0 ≤ σ := le_of_lt hσ
  have hτ : (0 : ℝ) ≤ τ := le_trans ha22abs ha22
  -- local squaring monotonicity (the private helper is inaccessible)
  have sqmono : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → a ^ 2 ≤ b ^ 2 := by
    intro a b ha hab; rw [pow_two, pow_two]; exact mul_self_le_mul_self ha hab
  set s := σ - α * τ with hsdef
  have hs : (0 : ℝ) < s := by rw [hsdef]; linarith
  set R := (1 + u) ^ 2 * α * τ ^ 2 * (3 * σ + α * τ) with hR
  have hRHSnn : 0 ≤ R := by rw [hR]; positivity
  have hw0Dnn : 0 ≤ w0 * D := mul_nonneg hw0 hDpos.le
  have hw1Dnn : 0 ≤ w1 * D := mul_nonneg hw1 hDpos.le
  have hP0nn : 0 ≤ (1 + u) * anextabs * a21abs :=
    mul_nonneg (mul_nonneg h1u hanextabs) ha21abs.le
  -- squared / cross multiplier bounds (clearing `D`)
  have e0 : (w0 * D) ^ 2 ≤ ((1 + u) * anextabs * a21abs) ^ 2 := sqmono hw0Dnn hw0D
  have e1 : (w1 * D) ^ 2 ≤ ((1 + u) * anextabs * a11abs) ^ 2 := sqmono hw1Dnn hw1D
  have ecross : (w0 * D) * (w1 * D)
      ≤ ((1 + u) * anextabs * a21abs) * ((1 + u) * anextabs * a11abs) :=
    mul_le_mul hw0D hw1D hw1Dnn hP0nn
  -- STEP (i): `Q · D² ≤ N`
  have hA : w0 ^ 2 * a11abs * D ^ 2 ≤ ((1 + u) * anextabs * a21abs) ^ 2 * a11abs := by
    have h := mul_le_mul_of_nonneg_right e0 ha11abs
    calc w0 ^ 2 * a11abs * D ^ 2 = (w0 * D) ^ 2 * a11abs := by ring
      _ ≤ ((1 + u) * anextabs * a21abs) ^ 2 * a11abs := h
  have hC : w1 ^ 2 * a22abs * D ^ 2 ≤ ((1 + u) * anextabs * a11abs) ^ 2 * a22abs := by
    have h := mul_le_mul_of_nonneg_right e1 ha22abs
    calc w1 ^ 2 * a22abs * D ^ 2 = (w1 * D) ^ 2 * a22abs := by ring
      _ ≤ ((1 + u) * anextabs * a11abs) ^ 2 * a22abs := h
  have hB : 2 * w0 * w1 * a21abs * D ^ 2
      ≤ 2 * (((1 + u) * anextabs * a21abs) * ((1 + u) * anextabs * a11abs)) * a21abs := by
    have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ecross ha21abs.le)
      (by norm_num : (0 : ℝ) ≤ 2)
    calc 2 * w0 * w1 * a21abs * D ^ 2 = 2 * ((w0 * D) * (w1 * D) * a21abs) := by ring
      _ ≤ 2 * (((1 + u) * anextabs * a21abs) * ((1 + u) * anextabs * a11abs) * a21abs) := h
      _ = 2 * (((1 + u) * anextabs * a21abs) * ((1 + u) * anextabs * a11abs)) * a21abs := by ring
  set N := (1 + u) ^ 2 * anextabs ^ 2 * (3 * a21abs ^ 2 * a11abs + a11abs ^ 2 * a22abs) with hN
  have stepi :
      (w0 ^ 2 * a11abs + 2 * w0 * w1 * a21abs + w1 ^ 2 * a22abs) * D ^ 2 ≤ N := by
    have hsum : (w0 ^ 2 * a11abs + 2 * w0 * w1 * a21abs + w1 ^ 2 * a22abs) * D ^ 2
        = w0 ^ 2 * a11abs * D ^ 2 + 2 * w0 * w1 * a21abs * D ^ 2 + w1 ^ 2 * a22abs * D ^ 2 := by
      ring
    have hNeq : ((1 + u) * anextabs * a21abs) ^ 2 * a11abs
        + 2 * (((1 + u) * anextabs * a21abs) * ((1 + u) * anextabs * a11abs)) * a21abs
        + ((1 + u) * anextabs * a11abs) ^ 2 * a22abs = N := by rw [hN]; ring
    rw [hsum, ← hNeq]
    exact add_le_add (add_le_add hA hB) hC
  -- STEP (ii): `Q ≤ N / D²`
  have hD2pos : (0 : ℝ) < D ^ 2 := by positivity
  have stepii : w0 ^ 2 * a11abs + 2 * w0 * w1 * a21abs + w1 ^ 2 * a22abs ≤ N / D ^ 2 :=
    (le_div_iff₀ hD2pos).mpr stepi
  -- reduced polynomial (numerator, scaled by σ²)
  have hanextsq : anextabs ^ 2 ≤ τ ^ 2 := sqmono hanextabs hanext
  have htestsq : (σ * a11abs) ^ 2 ≤ (α * a21abs ^ 2) ^ 2 :=
    sqmono (mul_nonneg hσ0 ha11abs) htest
  -- term 1
  have t1 : anextabs ^ 2 * (3 * a21abs ^ 2 * a11abs) * σ ^ 2 ≤ 3 * α * σ * τ ^ 2 * a21abs ^ 4 := by
    have hX : 0 ≤ 3 * a21abs ^ 2 * a11abs * σ ^ 2 := by positivity
    have stepA : anextabs ^ 2 * (3 * a21abs ^ 2 * a11abs * σ ^ 2)
        ≤ τ ^ 2 * (3 * a21abs ^ 2 * a11abs * σ ^ 2) := mul_le_mul_of_nonneg_right hanextsq hX
    have hσa : 3 * a21abs ^ 2 * τ ^ 2 * (σ * (σ * a11abs))
        ≤ 3 * a21abs ^ 2 * τ ^ 2 * (σ * (α * a21abs ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htest hσ0)
        (by positivity : (0 : ℝ) ≤ 3 * a21abs ^ 2 * τ ^ 2)
    calc anextabs ^ 2 * (3 * a21abs ^ 2 * a11abs) * σ ^ 2
        = anextabs ^ 2 * (3 * a21abs ^ 2 * a11abs * σ ^ 2) := by ring
      _ ≤ τ ^ 2 * (3 * a21abs ^ 2 * a11abs * σ ^ 2) := stepA
      _ = 3 * a21abs ^ 2 * τ ^ 2 * (σ * (σ * a11abs)) := by ring
      _ ≤ 3 * a21abs ^ 2 * τ ^ 2 * (σ * (α * a21abs ^ 2)) := hσa
      _ = 3 * α * σ * τ ^ 2 * a21abs ^ 4 := by ring
  -- term 2
  have t2 : anextabs ^ 2 * (a11abs ^ 2 * a22abs) * σ ^ 2 ≤ α ^ 2 * τ ^ 3 * a21abs ^ 4 := by
    have hY : 0 ≤ a11abs ^ 2 * a22abs * σ ^ 2 := by positivity
    have stepA' : anextabs ^ 2 * (a11abs ^ 2 * a22abs * σ ^ 2)
        ≤ τ ^ 2 * (a11abs ^ 2 * a22abs * σ ^ 2) := mul_le_mul_of_nonneg_right hanextsq hY
    have hstep1 : a22abs * (σ * a11abs) ^ 2 ≤ a22abs * (α * a21abs ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_left htestsq ha22abs
    have hstep2 : a22abs * (α ^ 2 * a21abs ^ 4) ≤ τ * (α ^ 2 * a21abs ^ 4) :=
      mul_le_mul_of_nonneg_right ha22 (by positivity : (0 : ℝ) ≤ α ^ 2 * a21abs ^ 4)
    calc anextabs ^ 2 * (a11abs ^ 2 * a22abs) * σ ^ 2
        = anextabs ^ 2 * (a11abs ^ 2 * a22abs * σ ^ 2) := by ring
      _ ≤ τ ^ 2 * (a11abs ^ 2 * a22abs * σ ^ 2) := stepA'
      _ = τ ^ 2 * (a22abs * (σ * a11abs) ^ 2) := by ring
      _ ≤ τ ^ 2 * (a22abs * (α * a21abs ^ 2) ^ 2) := mul_le_mul_of_nonneg_left hstep1 (sq_nonneg τ)
      _ = τ ^ 2 * (a22abs * (α ^ 2 * a21abs ^ 4)) := by ring
      _ ≤ τ ^ 2 * (τ * (α ^ 2 * a21abs ^ 4)) := mul_le_mul_of_nonneg_left hstep2 (sq_nonneg τ)
      _ = α ^ 2 * τ ^ 3 * a21abs ^ 4 := by ring
  have hcore : anextabs ^ 2 * (3 * a21abs ^ 2 * a11abs + a11abs ^ 2 * a22abs) * σ ^ 2
      ≤ α * τ ^ 2 * (3 * σ + α * τ) * a21abs ^ 4 := by
    have hdist : anextabs ^ 2 * (3 * a21abs ^ 2 * a11abs + a11abs ^ 2 * a22abs) * σ ^ 2
        = anextabs ^ 2 * (3 * a21abs ^ 2 * a11abs) * σ ^ 2
          + anextabs ^ 2 * (a11abs ^ 2 * a22abs) * σ ^ 2 := by ring
    have hrhs : α * τ ^ 2 * (3 * σ + α * τ) * a21abs ^ 4
        = 3 * α * σ * τ ^ 2 * a21abs ^ 4 + α ^ 2 * τ ^ 3 * a21abs ^ 4 := by ring
    rw [hdist, hrhs]; exact add_le_add t1 t2
  -- (A): N·σ² ≤ R·a21⁴
  have hAineq : N * σ ^ 2 ≤ R * a21abs ^ 4 := by
    have h := mul_le_mul_of_nonneg_left hcore (by positivity : (0 : ℝ) ≤ (1 + u) ^ 2)
    calc N * σ ^ 2
        = (1 + u) ^ 2 * (anextabs ^ 2 * (3 * a21abs ^ 2 * a11abs + a11abs ^ 2 * a22abs) * σ ^ 2) := by
          rw [hN]; ring
      _ ≤ (1 + u) ^ 2 * (α * τ ^ 2 * (3 * σ + α * τ) * a21abs ^ 4) := h
      _ = R * a21abs ^ 4 := by rw [hR]; ring
  -- (B): a21⁴·s² ≤ σ²·D²   (from hDlow squared)
  have hBineq : a21abs ^ 4 * s ^ 2 ≤ σ ^ 2 * D ^ 2 := by
    have hDlow_nn : 0 ≤ a21abs ^ 2 * s := mul_nonneg (sq_nonneg _) hs.le
    have hsq : (a21abs ^ 2 * s) ^ 2 ≤ (σ * D) ^ 2 := sqmono hDlow_nn hDlow
    calc a21abs ^ 4 * s ^ 2 = (a21abs ^ 2 * s) ^ 2 := by ring
      _ ≤ (σ * D) ^ 2 := hsq
      _ = σ ^ 2 * D ^ 2 := by ring
  -- combine (A) and (B), then cancel σ²
  have hσsq : (0 : ℝ) < σ ^ 2 := pow_pos hσ 2
  have combined : (N * s ^ 2) * σ ^ 2 ≤ (R * D ^ 2) * σ ^ 2 := by
    have hA' : N * σ ^ 2 * s ^ 2 ≤ R * a21abs ^ 4 * s ^ 2 :=
      mul_le_mul_of_nonneg_right hAineq (sq_nonneg s)
    have hB' : R * (a21abs ^ 4 * s ^ 2) ≤ R * (σ ^ 2 * D ^ 2) :=
      mul_le_mul_of_nonneg_left hBineq hRHSnn
    calc (N * s ^ 2) * σ ^ 2 = N * σ ^ 2 * s ^ 2 := by ring
      _ ≤ R * a21abs ^ 4 * s ^ 2 := hA'
      _ = R * (a21abs ^ 4 * s ^ 2) := by ring
      _ ≤ R * (σ ^ 2 * D ^ 2) := hB'
      _ = (R * D ^ 2) * σ ^ 2 := by ring
  have hNs : N * s ^ 2 ≤ R * D ^ 2 := le_of_mul_le_mul_right combined hσsq
  -- STEP (iii): assemble
  have hs2pos : (0 : ℝ) < s ^ 2 := pow_pos hs 2
  refine (le_div_iff₀ hs2pos).mpr ?_
  calc (w0 ^ 2 * a11abs + 2 * w0 * w1 * a21abs + w1 ^ 2 * a22abs) * s ^ 2
      ≤ (N / D ^ 2) * s ^ 2 := mul_le_mul_of_nonneg_right stepii (sq_nonneg s)
    _ = N * s ^ 2 / D ^ 2 := by ring
    _ ≤ R := (div_le_iff₀ hD2pos).mpr hNs

theorem corner_rowcol_le_core_decoupled
    (u σ τ a11abs a21abs a22abs anextabs w0 w1 D : ℝ)
    (hu : 0 ≤ u) (hσ : 0 < σ)
    (ha11abs : 0 ≤ a11abs) (ha21abs : 0 < a21abs)
    (ha22abs : 0 ≤ a22abs) (hanextabs : 0 ≤ anextabs)
    (hDpos : 0 < D)
    (hslack : bunchTridiagonalAlpha * τ < σ)
    (hDlow : a21abs ^ 2 * (σ - bunchTridiagonalAlpha * τ) ≤ σ * D)
    (htest : σ * a11abs ≤ bunchTridiagonalAlpha * a21abs ^ 2)
    (ha21 : a21abs ≤ τ) (ha22 : a22abs ≤ τ) (hanext : anextabs ≤ τ)
    (hw0D : w0 * D ≤ (1 + u) * anextabs * a21abs)
    (hw1D : w1 * D ≤ (1 + u) * anextabs * a11abs) :
    a11abs * w0 + a21abs * w1
        ≤ 2 * (1 + u) * bunchTridiagonalAlpha * τ ^ 2 / (σ - bunchTridiagonalAlpha * τ)
      ∧ a21abs * w0 + a22abs * w1
        ≤ 2 * (1 + u) * σ * τ / (σ - bunchTridiagonalAlpha * τ) := by
  have hα : 0 < bunchTridiagonalAlpha := bunch_tridiagonal_alpha_pos
  set α := bunchTridiagonalAlpha with hαdef
  set γ := σ - α * τ with hγdef
  have hγ : 0 < γ := by rw [hγdef]; linarith [hslack]
  have h1u : (0 : ℝ) ≤ 1 + u := by linarith
  have hσ0 : 0 ≤ σ := hσ.le
  have hτ0 : 0 ≤ τ := le_trans ha21abs.le ha21
  -- KA : linear cancellation numerator for the pivot-row a11/a21 paths
  have KA : a11abs * anextabs * a21abs * γ ≤ α * τ ^ 2 * D := by
    have hστ : σ * (a11abs * anextabs * a21abs * γ) ≤ σ * (α * τ ^ 2 * D) := by
      calc σ * (a11abs * anextabs * a21abs * γ)
          = (σ * a11abs) * (anextabs * a21abs * γ) := by ring
        _ ≤ (α * a21abs ^ 2) * (anextabs * a21abs * γ) :=
            mul_le_mul_of_nonneg_right htest
              (mul_nonneg (mul_nonneg hanextabs ha21abs.le) hγ.le)
        _ = (α * anextabs * a21abs) * (a21abs ^ 2 * γ) := by ring
        _ ≤ (α * anextabs * a21abs) * (σ * D) :=
            mul_le_mul_of_nonneg_left hDlow
              (mul_nonneg (mul_nonneg hα.le hanextabs) ha21abs.le)
        _ = σ * (α * (anextabs * a21abs) * D) := by ring
        _ ≤ σ * (α * (τ * τ) * D) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (mul_le_mul hanext ha21 ha21abs.le hτ0) hα.le)
                hDpos.le)
              hσ0
        _ = σ * (α * τ ^ 2 * D) := by ring
    exact le_of_mul_le_mul_left hστ hσ
  -- KC : linear cancellation numerator for the pivot-column a21 path
  have KC : anextabs * a21abs ^ 2 * γ ≤ σ * τ * D := by
    calc anextabs * a21abs ^ 2 * γ
        = anextabs * (a21abs ^ 2 * γ) := by ring
      _ ≤ anextabs * (σ * D) := mul_le_mul_of_nonneg_left hDlow hanextabs
      _ ≤ τ * (σ * D) := mul_le_mul_of_nonneg_right hanext (mul_nonneg hσ0 hDpos.le)
      _ = σ * τ * D := by ring
  -- KD : linear cancellation numerator for the pivot-column a22 path
  have KD : a22abs * anextabs * a11abs * γ ≤ α * τ ^ 2 * D := by
    have hστ : σ * (a22abs * anextabs * a11abs * γ) ≤ σ * (α * τ ^ 2 * D) := by
      calc σ * (a22abs * anextabs * a11abs * γ)
          = (σ * a11abs) * (a22abs * anextabs * γ) := by ring
        _ ≤ (α * a21abs ^ 2) * (a22abs * anextabs * γ) :=
            mul_le_mul_of_nonneg_right htest
              (mul_nonneg (mul_nonneg ha22abs hanextabs) hγ.le)
        _ = (α * a22abs * anextabs) * (a21abs ^ 2 * γ) := by ring
        _ ≤ (α * a22abs * anextabs) * (σ * D) :=
            mul_le_mul_of_nonneg_left hDlow
              (mul_nonneg (mul_nonneg hα.le ha22abs) hanextabs)
        _ = σ * (α * (a22abs * anextabs) * D) := by ring
        _ ≤ σ * (α * (τ * τ) * D) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (mul_le_mul ha22 hanext hanextabs hτ0) hα.le)
                hDpos.le)
              hσ0
        _ = σ * (α * τ ^ 2 * D) := by ring
    exact le_of_mul_le_mul_left hστ hσ
  -- the four term bounds
  have ta : a11abs * w0 ≤ (1 + u) * α * τ ^ 2 / γ := by
    have hmul : a11abs * w0 * γ * D ≤ (1 + u) * α * τ ^ 2 * D := by
      calc a11abs * w0 * γ * D
          = γ * a11abs * (w0 * D) := by ring
        _ ≤ γ * a11abs * ((1 + u) * anextabs * a21abs) :=
            mul_le_mul_of_nonneg_left hw0D (mul_nonneg hγ.le ha11abs)
        _ = (1 + u) * (a11abs * anextabs * a21abs * γ) := by ring
        _ ≤ (1 + u) * (α * τ ^ 2 * D) := mul_le_mul_of_nonneg_left KA h1u
        _ = (1 + u) * α * τ ^ 2 * D := by ring
    have h2 : a11abs * w0 * γ ≤ (1 + u) * α * τ ^ 2 := le_of_mul_le_mul_right hmul hDpos
    exact (le_div_iff₀ hγ).mpr h2
  have tb : a21abs * w1 ≤ (1 + u) * α * τ ^ 2 / γ := by
    have hmul : a21abs * w1 * γ * D ≤ (1 + u) * α * τ ^ 2 * D := by
      calc a21abs * w1 * γ * D
          = γ * a21abs * (w1 * D) := by ring
        _ ≤ γ * a21abs * ((1 + u) * anextabs * a11abs) :=
            mul_le_mul_of_nonneg_left hw1D (mul_nonneg hγ.le ha21abs.le)
        _ = (1 + u) * (a11abs * anextabs * a21abs * γ) := by ring
        _ ≤ (1 + u) * (α * τ ^ 2 * D) := mul_le_mul_of_nonneg_left KA h1u
        _ = (1 + u) * α * τ ^ 2 * D := by ring
    have h2 : a21abs * w1 * γ ≤ (1 + u) * α * τ ^ 2 := le_of_mul_le_mul_right hmul hDpos
    exact (le_div_iff₀ hγ).mpr h2
  have tc : a21abs * w0 ≤ (1 + u) * σ * τ / γ := by
    have hmul : a21abs * w0 * γ * D ≤ (1 + u) * σ * τ * D := by
      calc a21abs * w0 * γ * D
          = γ * a21abs * (w0 * D) := by ring
        _ ≤ γ * a21abs * ((1 + u) * anextabs * a21abs) :=
            mul_le_mul_of_nonneg_left hw0D (mul_nonneg hγ.le ha21abs.le)
        _ = (1 + u) * (anextabs * a21abs ^ 2 * γ) := by ring
        _ ≤ (1 + u) * (σ * τ * D) := mul_le_mul_of_nonneg_left KC h1u
        _ = (1 + u) * σ * τ * D := by ring
    have h2 : a21abs * w0 * γ ≤ (1 + u) * σ * τ := le_of_mul_le_mul_right hmul hDpos
    exact (le_div_iff₀ hγ).mpr h2
  have td : a22abs * w1 ≤ (1 + u) * α * τ ^ 2 / γ := by
    have hmul : a22abs * w1 * γ * D ≤ (1 + u) * α * τ ^ 2 * D := by
      calc a22abs * w1 * γ * D
          = γ * a22abs * (w1 * D) := by ring
        _ ≤ γ * a22abs * ((1 + u) * anextabs * a11abs) :=
            mul_le_mul_of_nonneg_left hw1D (mul_nonneg hγ.le ha22abs)
        _ = (1 + u) * (a22abs * anextabs * a11abs * γ) := by ring
        _ ≤ (1 + u) * (α * τ ^ 2 * D) := mul_le_mul_of_nonneg_left KD h1u
        _ = (1 + u) * α * τ ^ 2 * D := by ring
    have h2 : a22abs * w1 * γ ≤ (1 + u) * α * τ ^ 2 := le_of_mul_le_mul_right hmul hDpos
    exact (le_div_iff₀ hγ).mpr h2
  -- α·τ² ≤ σ·τ (from α·τ < σ), so the a22 path relaxes into the a21 constant
  have relax : (1 + u) * α * τ ^ 2 / γ ≤ (1 + u) * σ * τ / γ := by
    have hnum : (1 + u) * α * τ ^ 2 ≤ (1 + u) * σ * τ := by
      nlinarith [mul_nonneg h1u (mul_nonneg (sub_nonneg.mpr hslack.le) hτ0)]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnum (inv_pos.mpr hγ).le
  refine ⟨?_, ?_⟩
  · calc a11abs * w0 + a21abs * w1
        ≤ (1 + u) * α * τ ^ 2 / γ + (1 + u) * α * τ ^ 2 / γ := add_le_add ta tb
      _ = 2 * (1 + u) * α * τ ^ 2 / γ := by ring
  · calc a21abs * w0 + a22abs * w1
        ≤ (1 + u) * σ * τ / γ + (1 + u) * σ * τ / γ := add_le_add tc (le_trans td relax)
      _ = 2 * (1 + u) * σ * τ / γ := by ring

/-! ## Session 5 — decoupled corner pivot-path bounds -/

theorem pivotPath2Abs_corner_le_decoupled (fp : FPModel) {m : ℕ}
    (A : Fin (m + 3) → Fin (m + 3) → ℝ) (hA : IsSymTridiagonal (m + 3) A)
    (σ τ : ℝ) (hσpos : 0 < σ) (hslack : bunchTridiagonalAlpha * τ < σ)
    (hchoice : BunchTridiagonalPivotChoice σ (A 0 0) (A (oneIdx (m + 1)) 0) PivotSize.two)
    (hτa22 : |A (oneIdx (m + 1)) (oneIdx (m + 1))| ≤ τ)
    (hτanext : |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| ≤ τ) :
    pivotPath2Abs (m + 1) fp A 0 0
      ≤ (1 + fp.u) ^ 2 * bunchTridiagonalAlpha * τ ^ 2
          * (3 * σ + bunchTridiagonalAlpha * τ) / (σ - bunchTridiagonalAlpha * τ) ^ 2 := by
  have hu0 := fp.u_nonneg
  have hsym : A 0 (oneIdx (m + 1)) = A (oneIdx (m + 1)) 0 := hA.1 0 (oneIdx (m + 1))
  have ha21ne : A (oneIdx (m + 1)) 0 ≠ 0 :=
    bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_sigma_nonneg σ (A 0 0)
      (A (oneIdx (m + 1)) 0) hchoice hσpos.le
  have ha21abspos : 0 < |A (oneIdx (m + 1)) 0| := abs_pos.mpr ha21ne
  have hd : 0 < σ - bunchTridiagonalAlpha * τ := by linarith [hslack]
  -- determinant identity and decoupled lower bound
  have hdeteq : mixedDet2 (m + 1) A
      = A 0 0 * A (oneIdx (m + 1)) (oneIdx (m + 1)) - A (oneIdx (m + 1)) 0 ^ 2 := by
    unfold mixedDet2; rw [hsym]; ring
  have hDlow_raw := twoByTwo_absdet_lower_decoupled' σ τ (A 0 0)
    (A (oneIdx (m + 1)) 0) (A (oneIdx (m + 1)) (oneIdx (m + 1))) hchoice hσpos hτa22
  have hDlow : |A (oneIdx (m + 1)) 0| ^ 2 * (σ - bunchTridiagonalAlpha * τ)
      ≤ σ * |mixedDet2 (m + 1) A| := by
    rw [sq_abs, hdeteq]; exact hDlow_raw
  have hσdet : 0 < σ * |mixedDet2 (m + 1) A| :=
    lt_of_lt_of_le (mul_pos (pow_pos ha21abspos 2) hd) hDlow
  have hDgt : 0 < |mixedDet2 (m + 1) A| := by
    rcases (abs_nonneg (mixedDet2 (m + 1) A)).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hσdet; exact absurd hσdet (lt_irrefl 0)
  have htest : σ * |A 0 0| ≤ bunchTridiagonalAlpha * |A (oneIdx (m + 1)) 0| ^ 2 := by
    rw [sq_abs]
    exact le_of_lt (bunch_tridiagonal_pivot_choice_two_threshold σ (A 0 0)
      (A (oneIdx (m + 1)) 0) hchoice)
  -- multiplier rounding bounds (clearing `det`) — unchanged from the coupled proof
  obtain ⟨δ0, hδ0, hm0⟩ := fp.model_mul (A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1)))
    (-A (oneIdx (m + 1)) 0 / mixedDet2 (m + 1) A)
  obtain ⟨δ1, hδ1, hm1⟩ := fp.model_mul (A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1)))
    (A 0 0 / mixedDet2 (m + 1) A)
  have hw0val : flMixedMult2 (m + 1) fp A 0 0
      = A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))
          * (-A (oneIdx (m + 1)) 0 / mixedDet2 (m + 1) A) * (1 + δ0) := by
    rw [flMixedMult2_corner0 fp A hA]; exact hm0
  have hw1val : flMixedMult2 (m + 1) fp A 0 1
      = A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))
          * (A 0 0 / mixedDet2 (m + 1) A) * (1 + δ1) := by
    rw [flMixedMult2_corner1 fp A hA]; exact hm1
  have hcancel0 : |(-A (oneIdx (m + 1)) 0) / mixedDet2 (m + 1) A| * |mixedDet2 (m + 1) A|
      = |A (oneIdx (m + 1)) 0| := by
    rw [abs_div, abs_neg, div_mul_cancel₀ _ hDgt.ne']
  have hcancel1 : |A 0 0 / mixedDet2 (m + 1) A| * |mixedDet2 (m + 1) A| = |A 0 0| := by
    rw [abs_div, div_mul_cancel₀ _ hDgt.ne']
  have hw0D : |flMixedMult2 (m + 1) fp A 0 0| * |mixedDet2 (m + 1) A|
      ≤ (1 + fp.u) * |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
          * |A (oneIdx (m + 1)) 0| := by
    rw [hw0val, abs_mul, abs_mul]
    have hrw : |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
          * |(-A (oneIdx (m + 1)) 0) / mixedDet2 (m + 1) A| * |1 + δ0|
          * |mixedDet2 (m + 1) A|
        = |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
          * (|(-A (oneIdx (m + 1)) 0) / mixedDet2 (m + 1) A| * |mixedDet2 (m + 1) A|)
          * |1 + δ0| := by ring
    rw [hrw, hcancel0]
    calc |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| * |A (oneIdx (m + 1)) 0| * |1 + δ0|
        ≤ |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| * |A (oneIdx (m + 1)) 0|
            * (1 + fp.u) :=
          mul_le_mul_of_nonneg_left (abs_one_add_le fp hδ0)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = (1 + fp.u) * |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
            * |A (oneIdx (m + 1)) 0| := by ring
  have hw1D : |flMixedMult2 (m + 1) fp A 0 1| * |mixedDet2 (m + 1) A|
      ≤ (1 + fp.u) * |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| * |A 0 0| := by
    rw [hw1val, abs_mul, abs_mul]
    have hrw : |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
          * |A 0 0 / mixedDet2 (m + 1) A| * |1 + δ1| * |mixedDet2 (m + 1) A|
        = |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
          * (|A 0 0 / mixedDet2 (m + 1) A| * |mixedDet2 (m + 1) A|) * |1 + δ1| := by ring
    rw [hrw, hcancel1]
    calc |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| * |A 0 0| * |1 + δ1|
        ≤ |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| * |A 0 0| * (1 + fp.u) :=
          mul_le_mul_of_nonneg_left (abs_one_add_le fp hδ1)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = (1 + fp.u) * |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| * |A 0 0| := by ring
  -- expand `pivotPath2Abs` at the corner — unchanged
  have hexpand : pivotPath2Abs (m + 1) fp A 0 0
      = |flMixedMult2 (m + 1) fp A 0 0| ^ 2 * |A 0 0|
        + 2 * |flMixedMult2 (m + 1) fp A 0 0| * |flMixedMult2 (m + 1) fp A 0 1|
            * |A (oneIdx (m + 1)) 0|
        + |flMixedMult2 (m + 1) fp A 0 1| ^ 2 * |A (oneIdx (m + 1)) (oneIdx (m + 1))| := by
    rw [pivotPath2Abs, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [leadingTwoBlock_apply, embedTwo_zero, embedTwo_one_eq]
    rw [hsym]; ring
  rw [hexpand]
  exact corner_quadform_core_decoupled fp.u σ τ |A 0 0| |A (oneIdx (m + 1)) 0|
    |A (oneIdx (m + 1)) (oneIdx (m + 1))|
    |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
    |flMixedMult2 (m + 1) fp A 0 0| |flMixedMult2 (m + 1) fp A 0 1|
    |mixedDet2 (m + 1) A|
    hu0 hσpos (abs_nonneg _) ha21abspos (abs_nonneg _) (abs_nonneg _)
    (abs_nonneg _) (abs_nonneg _) hDgt hslack hDlow htest hτa22 hτanext hw0D hw1D

theorem pivotRowColPathAbs_corner_le_decoupled (fp : FPModel) {m : ℕ}
    (A : Fin (m + 3) → Fin (m + 3) → ℝ) (hA : IsSymTridiagonal (m + 3) A)
    (σ τ : ℝ) (hσpos : 0 < σ) (hslack : bunchTridiagonalAlpha * τ < σ)
    (hchoice : BunchTridiagonalPivotChoice σ (A 0 0) (A (oneIdx (m + 1)) 0) PivotSize.two)
    (hτa21 : |A (oneIdx (m + 1)) 0| ≤ τ)
    (hτa22 : |A (oneIdx (m + 1)) (oneIdx (m + 1))| ≤ τ)
    (hτanext : |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| ≤ τ) :
    pivotRowPathAbs (m + 1) fp A 0 0
        ≤ 2 * (1 + fp.u) * bunchTridiagonalAlpha * τ ^ 2 / (σ - bunchTridiagonalAlpha * τ)
      ∧ pivotRowPathAbs (m + 1) fp A 1 0
        ≤ 2 * (1 + fp.u) * σ * τ / (σ - bunchTridiagonalAlpha * τ)
      ∧ pivotColPathAbs (m + 1) fp A 0 0
        ≤ 2 * (1 + fp.u) * bunchTridiagonalAlpha * τ ^ 2 / (σ - bunchTridiagonalAlpha * τ)
      ∧ pivotColPathAbs (m + 1) fp A 0 1
        ≤ 2 * (1 + fp.u) * σ * τ / (σ - bunchTridiagonalAlpha * τ) := by
  have hu0 := fp.u_nonneg
  have hgap : 0 < σ - bunchTridiagonalAlpha * τ := by linarith [hslack]
  have hsym : A 0 (oneIdx (m + 1)) = A (oneIdx (m + 1)) 0 := hA.1 0 (oneIdx (m + 1))
  have ha21ne : A (oneIdx (m + 1)) 0 ≠ 0 :=
    bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_sigma_nonneg σ (A 0 0)
      (A (oneIdx (m + 1)) 0) hchoice hσpos.le
  have hdeteq : mixedDet2 (m + 1) A
      = A 0 0 * A (oneIdx (m + 1)) (oneIdx (m + 1)) - A (oneIdx (m + 1)) 0 ^ 2 := by
    unfold mixedDet2; rw [hsym]; ring
  have hDlow : |A (oneIdx (m + 1)) 0| ^ 2 * (σ - bunchTridiagonalAlpha * τ)
      ≤ σ * |mixedDet2 (m + 1) A| := by
    rw [sq_abs, hdeteq]
    exact twoByTwo_absdet_lower_decoupled' σ τ (A 0 0) (A (oneIdx (m + 1)) 0)
      (A (oneIdx (m + 1)) (oneIdx (m + 1))) hchoice hσpos hτa22
  have hσD : 0 < σ * |mixedDet2 (m + 1) A| :=
    lt_of_lt_of_le (mul_pos (pow_pos (abs_pos.mpr ha21ne) 2) hgap) hDlow
  have hDgt : 0 < |mixedDet2 (m + 1) A| := by
    rcases (abs_nonneg (mixedDet2 (m + 1) A)).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, mul_zero] at hσD; exact lt_irrefl 0 hσD
  have htest : σ * |A 0 0| ≤ bunchTridiagonalAlpha * |A (oneIdx (m + 1)) 0| ^ 2 := by
    rw [sq_abs]
    exact le_of_lt (bunch_tridiagonal_pivot_choice_two_threshold σ (A 0 0)
      (A (oneIdx (m + 1)) 0) hchoice)
  obtain ⟨δ0, hδ0, hm0⟩ := fp.model_mul (A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1)))
    (-A (oneIdx (m + 1)) 0 / mixedDet2 (m + 1) A)
  obtain ⟨δ1, hδ1, hm1⟩ := fp.model_mul (A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1)))
    (A 0 0 / mixedDet2 (m + 1) A)
  have hw0val : flMixedMult2 (m + 1) fp A 0 0
      = A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))
          * (-A (oneIdx (m + 1)) 0 / mixedDet2 (m + 1) A) * (1 + δ0) := by
    rw [flMixedMult2_corner0 fp A hA]; exact hm0
  have hw1val : flMixedMult2 (m + 1) fp A 0 1
      = A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))
          * (A 0 0 / mixedDet2 (m + 1) A) * (1 + δ1) := by
    rw [flMixedMult2_corner1 fp A hA]; exact hm1
  have hcancel0 : |(-A (oneIdx (m + 1)) 0) / mixedDet2 (m + 1) A| * |mixedDet2 (m + 1) A|
      = |A (oneIdx (m + 1)) 0| := by
    rw [abs_div, abs_neg, div_mul_cancel₀ _ hDgt.ne']
  have hcancel1 : |A 0 0 / mixedDet2 (m + 1) A| * |mixedDet2 (m + 1) A| = |A 0 0| := by
    rw [abs_div, div_mul_cancel₀ _ hDgt.ne']
  have hw0D : |flMixedMult2 (m + 1) fp A 0 0| * |mixedDet2 (m + 1) A|
      ≤ (1 + fp.u) * |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
          * |A (oneIdx (m + 1)) 0| := by
    rw [hw0val, abs_mul, abs_mul]
    have hrw : |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
          * |(-A (oneIdx (m + 1)) 0) / mixedDet2 (m + 1) A| * |1 + δ0|
          * |mixedDet2 (m + 1) A|
        = |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
          * (|(-A (oneIdx (m + 1)) 0) / mixedDet2 (m + 1) A| * |mixedDet2 (m + 1) A|)
          * |1 + δ0| := by ring
    rw [hrw, hcancel0]
    calc |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| * |A (oneIdx (m + 1)) 0| * |1 + δ0|
        ≤ |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| * |A (oneIdx (m + 1)) 0|
            * (1 + fp.u) :=
          mul_le_mul_of_nonneg_left (abs_one_add_le fp hδ0)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = (1 + fp.u) * |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
            * |A (oneIdx (m + 1)) 0| := by ring
  have hw1D : |flMixedMult2 (m + 1) fp A 0 1| * |mixedDet2 (m + 1) A|
      ≤ (1 + fp.u) * |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| * |A 0 0| := by
    rw [hw1val, abs_mul, abs_mul]
    have hrw : |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
          * |A 0 0 / mixedDet2 (m + 1) A| * |1 + δ1| * |mixedDet2 (m + 1) A|
        = |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
          * (|A 0 0 / mixedDet2 (m + 1) A| * |mixedDet2 (m + 1) A|) * |1 + δ1| := by ring
    rw [hrw, hcancel1]
    calc |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| * |A 0 0| * |1 + δ1|
        ≤ |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| * |A 0 0| * (1 + fp.u) :=
          mul_le_mul_of_nonneg_left (abs_one_add_le fp hδ1)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = (1 + fp.u) * |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| * |A 0 0| := by ring
  obtain ⟨hrow0, hrow1⟩ := corner_rowcol_le_core_decoupled fp.u σ τ |A 0 0|
    |A (oneIdx (m + 1)) 0|
    |A (oneIdx (m + 1)) (oneIdx (m + 1))|
    |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
    |flMixedMult2 (m + 1) fp A 0 0| |flMixedMult2 (m + 1) fp A 0 1|
    |mixedDet2 (m + 1) A|
    hu0 hσpos (abs_nonneg _) (abs_pos.mpr ha21ne) (abs_nonneg _) (abs_nonneg _)
    hDgt hslack hDlow htest hτa21 hτa22 hτanext hw0D hw1D
  have hexpRow0 : pivotRowPathAbs (m + 1) fp A 0 0
      = |A 0 0| * |flMixedMult2 (m + 1) fp A 0 0|
        + |A (oneIdx (m + 1)) 0| * |flMixedMult2 (m + 1) fp A 0 1| := by
    rw [pivotRowPathAbs, Fin.sum_univ_two]
    simp only [leadingTwoBlock_apply, embedTwo_zero, embedTwo_one_eq]
    rw [hsym]
  have hexpRow1 : pivotRowPathAbs (m + 1) fp A 1 0
      = |A (oneIdx (m + 1)) 0| * |flMixedMult2 (m + 1) fp A 0 0|
        + |A (oneIdx (m + 1)) (oneIdx (m + 1))| * |flMixedMult2 (m + 1) fp A 0 1| := by
    rw [pivotRowPathAbs, Fin.sum_univ_two]
    simp only [leadingTwoBlock_apply, embedTwo_zero, embedTwo_one_eq]
  have hexpCol0 : pivotColPathAbs (m + 1) fp A 0 0
      = |A 0 0| * |flMixedMult2 (m + 1) fp A 0 0|
        + |A (oneIdx (m + 1)) 0| * |flMixedMult2 (m + 1) fp A 0 1| := by
    rw [pivotColPathAbs, Fin.sum_univ_two]
    simp only [leadingTwoBlock_apply, embedTwo_zero, embedTwo_one_eq]
    ring
  have hexpCol1 : pivotColPathAbs (m + 1) fp A 0 1
      = |A (oneIdx (m + 1)) 0| * |flMixedMult2 (m + 1) fp A 0 0|
        + |A (oneIdx (m + 1)) (oneIdx (m + 1))| * |flMixedMult2 (m + 1) fp A 0 1| := by
    rw [pivotColPathAbs, Fin.sum_univ_two]
    simp only [leadingTwoBlock_apply, embedTwo_zero, embedTwo_one_eq]
    rw [show A 0 (oneIdx (m + 1)) = A (oneIdx (m + 1)) 0 from hsym]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hexpRow0]; exact hrow0
  · rw [hexpRow1]; exact hrow1
  · rw [hexpCol0]; exact hrow0
  · rw [hexpCol1]; exact hrow1

/-! ## Session 6 — uniform decoupled pivot-path bounds -/

/-- The uniform 2×2 pivot-path constant. -/
noncomputable def pathConst2 (u σ τ : ℝ) : ℝ :=
  (1 + u) ^ 2 * bunchTridiagonalAlpha * τ ^ 2
    * (3 * σ + bunchTridiagonalAlpha * τ) / (σ - bunchTridiagonalAlpha * τ) ^ 2

/-- The uniform pivot-row/column constant. -/
noncomputable def pathConstRC (u σ τ : ℝ) : ℝ :=
  2 * (1 + u) * σ * τ / (σ - bunchTridiagonalAlpha * τ)

theorem pathConst2_nonneg (u σ τ : ℝ) (hu : 0 ≤ u) (hσ : 0 < σ) (hτ : 0 ≤ τ)
    (hslack : bunchTridiagonalAlpha * τ < σ) : 0 ≤ pathConst2 u σ τ := by
  have hα := bunch_tridiagonal_alpha_pos
  have hd : 0 < σ - bunchTridiagonalAlpha * τ := by linarith
  unfold pathConst2
  apply div_nonneg _ (by positivity)
  have hnn : 0 ≤ 3 * σ + bunchTridiagonalAlpha * τ := by nlinarith [mul_nonneg hα.le hτ]
  have : 0 ≤ (1 + u) ^ 2 * bunchTridiagonalAlpha * τ ^ 2 := by positivity
  exact mul_nonneg this hnn

theorem pathConstRC_nonneg (u σ τ : ℝ) (hu : 0 ≤ u) (hσ : 0 < σ) (hτ : 0 ≤ τ)
    (hslack : bunchTridiagonalAlpha * τ < σ) : 0 ≤ pathConstRC u σ τ := by
  have hd : 0 < σ - bunchTridiagonalAlpha * τ := by linarith
  unfold pathConstRC
  apply div_nonneg _ (le_of_lt hd); positivity

/-- Uniform decoupled 2×2 pivot-path bound. -/
theorem pivotPath2Abs_le_decoupled (fp : FPModel) (σ τ : ℝ) (hσpos : 0 < σ)
    (hslack : bunchTridiagonalAlpha * τ < σ) :
    ∀ {m : ℕ} (A : Fin (m + 2) → Fin (m + 2) → ℝ), IsSymTridiagonal (m + 2) A →
      (∀ i j : Fin (m + 2), i.val ≠ 0 ∨ j.val ≠ 0 → |A i j| ≤ τ) →
      BunchTridiagonalPivotChoice σ (A 0 0) (A (oneIdx m) 0) PivotSize.two →
      ∀ i j : Fin m, pivotPath2Abs m fp A i j ≤ pathConst2 fp.u σ τ := by
  intro m
  cases m with
  | zero => intro A _ _ _ i; exact Fin.elim0 i
  | succ m' =>
      intro A hA hoff hchoice i j
      have hτ0 : 0 ≤ τ :=
        le_trans (abs_nonneg _) (hoff (oneIdx (m' + 1)) 0 (Or.inl (by simp [oneIdx])))
      have hRHS0 : 0 ≤ pathConst2 fp.u σ τ :=
        pathConst2_nonneg fp.u σ τ fp.u_nonneg hσpos hτ0 hslack
      by_cases hc : i.val = 0 ∧ j.val = 0
      · have hi : i = 0 := Fin.ext hc.1
        have hj : j = 0 := Fin.ext hc.2
        subst hi; subst hj
        exact pivotPath2Abs_corner_le_decoupled fp A hA σ τ hσpos hslack hchoice
          (hoff _ _ (Or.inl (by simp [oneIdx]))) (hoff _ _ (Or.inl (by simp only [Fin.val_succ, Fin.val_zero]; omega)))
      · have hne : i.val ≠ 0 ∨ j.val ≠ 0 := by
          by_contra h; push_neg at h; exact hc ⟨h.1, h.2⟩
        rw [pivotPath2Abs_eq_zero_of_ne_corner fp A hA i j hne]; exact hRHS0

/-- Uniform decoupled pivot-row bound. -/
theorem pivotRowPathAbs_le_decoupled (fp : FPModel) (σ τ : ℝ) (hσpos : 0 < σ)
    (hslack : bunchTridiagonalAlpha * τ < σ) :
    ∀ {m : ℕ} (A : Fin (m + 2) → Fin (m + 2) → ℝ), IsSymTridiagonal (m + 2) A →
      (∀ i j : Fin (m + 2), i.val ≠ 0 ∨ j.val ≠ 0 → |A i j| ≤ τ) →
      BunchTridiagonalPivotChoice σ (A 0 0) (A (oneIdx m) 0) PivotSize.two →
      ∀ (p : Fin 2) (j : Fin m), pivotRowPathAbs m fp A p j ≤ pathConstRC fp.u σ τ := by
  intro m
  cases m with
  | zero => intro A _ _ _ _ j; exact Fin.elim0 j
  | succ m' =>
      intro A hA hoff hchoice p j
      have hα := bunch_tridiagonal_alpha_pos
      have hd : 0 < σ - bunchTridiagonalAlpha * τ := by linarith
      have hτ0 : 0 ≤ τ :=
        le_trans (abs_nonneg _) (hoff (oneIdx (m' + 1)) 0 (Or.inl (by simp [oneIdx])))
      have hRC0 : 0 ≤ pathConstRC fp.u σ τ :=
        pathConstRC_nonneg fp.u σ τ fp.u_nonneg hσpos hτ0 hslack
      obtain ⟨hr0, hr1, _, _⟩ := pivotRowColPathAbs_corner_le_decoupled fp A hA σ τ hσpos hslack
        hchoice (hoff _ _ (Or.inl (by simp [oneIdx])))
        (hoff _ _ (Or.inl (by simp [oneIdx]))) (hoff _ _ (Or.inl (by simp only [Fin.val_succ, Fin.val_zero]; omega)))
      have hrelax : 2 * (1 + fp.u) * bunchTridiagonalAlpha * τ ^ 2 / (σ - bunchTridiagonalAlpha * τ)
          ≤ pathConstRC fp.u σ τ := by
        unfold pathConstRC
        have hnum : 2 * (1 + fp.u) * bunchTridiagonalAlpha * τ ^ 2 ≤ 2 * (1 + fp.u) * σ * τ := by
          nlinarith [mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 2 * (1 + fp.u) by
            have := fp.u_nonneg; linarith) (le_of_lt hd)) hτ0, fp.u_nonneg, hτ0, hslack]
        exact div_le_div_of_nonneg_right hnum (le_of_lt hd)
      by_cases hj : j.val = 0
      · have hj0 : j = 0 := Fin.ext hj
        subst hj0
        match p with
        | 0 => exact le_trans hr0 hrelax
        | 1 => exact hr1
      · rw [pivotRowPathAbs_eq_zero_of_ne_corner fp A hA p j hj]; exact hRC0

/-- Uniform decoupled pivot-column bound. -/
theorem pivotColPathAbs_le_decoupled (fp : FPModel) (σ τ : ℝ) (hσpos : 0 < σ)
    (hslack : bunchTridiagonalAlpha * τ < σ) :
    ∀ {m : ℕ} (A : Fin (m + 2) → Fin (m + 2) → ℝ), IsSymTridiagonal (m + 2) A →
      (∀ i j : Fin (m + 2), i.val ≠ 0 ∨ j.val ≠ 0 → |A i j| ≤ τ) →
      BunchTridiagonalPivotChoice σ (A 0 0) (A (oneIdx m) 0) PivotSize.two →
      ∀ (i : Fin m) (q : Fin 2), pivotColPathAbs m fp A i q ≤ pathConstRC fp.u σ τ := by
  intro m
  cases m with
  | zero => intro A _ _ _ i _; exact Fin.elim0 i
  | succ m' =>
      intro A hA hoff hchoice i q
      have hα := bunch_tridiagonal_alpha_pos
      have hd : 0 < σ - bunchTridiagonalAlpha * τ := by linarith
      have hτ0 : 0 ≤ τ :=
        le_trans (abs_nonneg _) (hoff (oneIdx (m' + 1)) 0 (Or.inl (by simp [oneIdx])))
      have hRC0 : 0 ≤ pathConstRC fp.u σ τ :=
        pathConstRC_nonneg fp.u σ τ fp.u_nonneg hσpos hτ0 hslack
      obtain ⟨_, _, hc0, hc1⟩ := pivotRowColPathAbs_corner_le_decoupled fp A hA σ τ hσpos hslack
        hchoice (hoff _ _ (Or.inl (by simp [oneIdx])))
        (hoff _ _ (Or.inl (by simp [oneIdx]))) (hoff _ _ (Or.inl (by simp only [Fin.val_succ, Fin.val_zero]; omega)))
      have hrelax : 2 * (1 + fp.u) * bunchTridiagonalAlpha * τ ^ 2 / (σ - bunchTridiagonalAlpha * τ)
          ≤ pathConstRC fp.u σ τ := by
        unfold pathConstRC
        have hnum : 2 * (1 + fp.u) * bunchTridiagonalAlpha * τ ^ 2 ≤ 2 * (1 + fp.u) * σ * τ := by
          nlinarith [mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 2 * (1 + fp.u) by
            have := fp.u_nonneg; linarith) (le_of_lt hd)) hτ0, fp.u_nonneg, hτ0, hslack]
        exact div_le_div_of_nonneg_right hnum (le_of_lt hd)
      by_cases hi : i.val = 0
      · have hi0 : i = 0 := Fin.ext hi
        subst hi0
        match q with
        | 0 => exact le_trans hc0 hrelax
        | 1 => exact hc1
      · rw [pivotColPathAbs_eq_zero_of_ne_corner fp A hA i q hi]; exact hRC0

/-! ## Session 7 — the growth invariant (off-corner entries stay ≤ τmax) -/

/-- Number of pivot stages (constructors) in a schedule. -/
def stages : {k : ℕ} → PivotSchedule k → ℕ
  | _, .nil => 0
  | _, .consOne s => stages s + 1
  | _, .consTwo s => stages s + 1

@[simp] theorem stages_consOne {n : ℕ} (s : PivotSchedule n) :
    stages s.consOne = stages s + 1 := rfl
@[simp] theorem stages_consTwo {n : ℕ} (s : PivotSchedule n) :
    stages s.consTwo = stages s + 1 := rfl

/-- Fixed-`M₀` Bunch run with the derived uniform off-corner entry bound `τmax`. -/
def TriGrowthBounded (fp : FPModel) (M0 τmax : ℝ) :
    {k : ℕ} → PivotSchedule k → (Fin k → Fin k → ℝ) → Prop
  | 0, .nil, _ => True
  | n + 1, .consOne s, A =>
      IsSymTridiagonal (n + 1) A ∧ A 0 0 ≠ 0 ∧
      (∀ i : Fin n, BunchTridiagonalPivotChoice M0 (A 0 0) (A i.succ 0) PivotSize.one) ∧
      (∀ i j : Fin (n + 1), i.val ≠ 0 ∨ j.val ≠ 0 → |A i j| ≤ τmax) ∧
      TriGrowthBounded fp M0 τmax s (flSchurCompl n fp A)
  | n + 2, .consTwo s, A =>
      IsSymTridiagonal (n + 2) A ∧
      BunchTridiagonalPivotChoice M0 (A 0 0) (A (oneIdx n) 0) PivotSize.two ∧
      (∀ i j : Fin (n + 2), i.val ≠ 0 ∨ j.val ≠ 0 → |A i j| ≤ τmax) ∧
      TriGrowthBounded fp M0 τmax s (flSchurCompl2 n fp A)

/-- **Growth invariant.**  A fixed-`M₀` Bunch run whose off-corner entries start
`≤ B`, with the budget `(1+u)^(#stages)·B ≤ τmax`, has all off-corner entries of
every reduced matrix `≤ τmax`.  Off-corner entries grow by exactly one `(1+u)` per
stage (`flSchurCompl(2)_offcorner_bound`), which the budget absorbs. -/
theorem growth_offcorner (fp : FPModel) (M0 τmax : ℝ) :
    ∀ {k : ℕ} (s : PivotSchedule k) (A : Fin k → Fin k → ℝ) (B : ℝ),
      TriGrowthData fp M0 s A →
      (∀ i j : Fin k, i.val ≠ 0 ∨ j.val ≠ 0 → |A i j| ≤ B) → 0 ≤ B →
      (1 + fp.u) ^ stages s * B ≤ τmax →
      TriGrowthBounded fp M0 τmax s A := by
  intro k s
  induction s with
  | nil => intro A B _ _ _ _; exact True.intro
  | @consOne n s ih =>
      intro A B hdata hoff hB0 hbud
      rw [TriGrowthData_consOne] at hdata
      obtain ⟨hA, hA00, hchoices, hrec⟩ := hdata
      have hupos : (0 : ℝ) ≤ 1 + fp.u := by have := fp.u_nonneg; linarith
      have hu1 : (1 : ℝ) ≤ 1 + fp.u := by have := fp.u_nonneg; linarith
      have hpow1 : (1 : ℝ) ≤ (1 + fp.u) ^ stages s.consOne := one_le_pow₀ hu1
      have hBle : B ≤ τmax := le_trans (le_mul_of_one_le_left hB0 hpow1) hbud
      have hoff' : ∀ i j : Fin (n + 1), i.val ≠ 0 ∨ j.val ≠ 0 → |A i j| ≤ τmax :=
        fun i j h => le_trans (hoff i j h) hBle
      -- off-corner preservation for the Schur complement
      have hoffS : ∀ i j : Fin n, i.val ≠ 0 ∨ j.val ≠ 0 →
          |flSchurCompl n fp A i j| ≤ (1 + fp.u) * B := by
        intro i j hne
        refine le_trans (flSchurCompl_offcorner_bound fp A hA hA00 i j hne) ?_
        have : |A i.succ j.succ| ≤ B := hoff i.succ j.succ (Or.inl (by simp [Fin.val_succ]))
        exact mul_le_mul_of_nonneg_left this hupos
      have hbud' : (1 + fp.u) ^ stages s * ((1 + fp.u) * B) ≤ τmax := by
        have : (1 + fp.u) ^ stages s * ((1 + fp.u) * B)
            = (1 + fp.u) ^ stages s.consOne * B := by
          rw [stages_consOne, pow_succ]; ring
        rw [this]; exact hbud
      have hB0' : 0 ≤ (1 + fp.u) * B := mul_nonneg hupos hB0
      refine ⟨hA, hA00, hchoices, hoff', ?_⟩
      exact ih (flSchurCompl n fp A) ((1 + fp.u) * B) hrec hoffS hB0' hbud'
  | @consTwo n s ih =>
      intro A B hdata hoff hB0 hbud
      rw [TriGrowthData_consTwo] at hdata
      obtain ⟨hA, hchoice, hrec⟩ := hdata
      have hupos : (0 : ℝ) ≤ 1 + fp.u := by have := fp.u_nonneg; linarith
      have hu1 : (1 : ℝ) ≤ 1 + fp.u := by have := fp.u_nonneg; linarith
      have hpow1 : (1 : ℝ) ≤ (1 + fp.u) ^ stages s.consTwo := one_le_pow₀ hu1
      have hBle : B ≤ τmax := le_trans (le_mul_of_one_le_left hB0 hpow1) hbud
      have hoff' : ∀ i j : Fin (n + 2), i.val ≠ 0 ∨ j.val ≠ 0 → |A i j| ≤ τmax :=
        fun i j h => le_trans (hoff i j h) hBle
      have hoffS : ∀ i j : Fin n, i.val ≠ 0 ∨ j.val ≠ 0 →
          |flSchurCompl2 n fp A i j| ≤ (1 + fp.u) * B := by
        intro i j hne
        refine le_trans (flSchurCompl2_offcorner_bound fp A hA i j hne) ?_
        have : |A i.succ.succ j.succ.succ| ≤ B :=
          hoff i.succ.succ j.succ.succ (Or.inl (by simp only [Fin.val_succ, Fin.val_zero]; omega))
        exact mul_le_mul_of_nonneg_left this hupos
      have hbud' : (1 + fp.u) ^ stages s * ((1 + fp.u) * B) ≤ τmax := by
        have : (1 + fp.u) ^ stages s * ((1 + fp.u) * B)
            = (1 + fp.u) ^ stages s.consTwo * B := by
          rw [stages_consTwo, pow_succ]; ring
        rw [this]; exact hbud
      have hB0' : 0 ≤ (1 + fp.u) * B := mul_nonneg hupos hB0
      refine ⟨hA, hchoice, hoff', ?_⟩
      exact ih (flSchurCompl2 n fp A) ((1 + fp.u) * B) hrec hoffS hB0' hbud'

/-! ## Session 8 — the decoupled hfactor_bound and hfactor_derived (crux assembly) -/

/-! ### Re-proved product-entry equalities (originally HFactor-local) -/

theorem productEntry_consTwo_00 (fp : FPModel) {m : ℕ}
    (s : PivotSchedule m) (A : Fin (m + 2) → Fin (m + 2) → ℝ) :
    higham11_4_bunchKaufmanProductEntry (m + 2) (flMixedL fp (s.consTwo) A)
        (flMixedD fp (s.consTwo) A) 0 0 = |A 0 0| := by
  unfold higham11_4_bunchKaufmanProductEntry
  simp only [sum_fin_add_two, flMixedL_consTwo_00, flMixedL_consTwo_01, flMixedL_consTwo_0t,
    flMixedD_consTwo_00,
    abs_zero, abs_one, zero_mul, mul_zero, one_mul, mul_one, add_zero,
    Finset.sum_const_zero]

theorem productEntry_consTwo_01 (fp : FPModel) {m : ℕ}
    (s : PivotSchedule m) (A : Fin (m + 2) → Fin (m + 2) → ℝ) :
    higham11_4_bunchKaufmanProductEntry (m + 2) (flMixedL fp (s.consTwo) A)
        (flMixedD fp (s.consTwo) A) 0 (Fin.succ 0) = |A 0 (oneIdx m)| := by
  unfold higham11_4_bunchKaufmanProductEntry
  simp only [sum_fin_add_two, flMixedL_consTwo_00, flMixedL_consTwo_01, flMixedL_consTwo_0t,
    flMixedL_consTwo_10, flMixedL_consTwo_11, flMixedL_consTwo_1t,
    flMixedD_consTwo_01,
    abs_zero, abs_one, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add,
    Finset.sum_const_zero]

theorem productEntry_consTwo_10 (fp : FPModel) {m : ℕ}
    (s : PivotSchedule m) (A : Fin (m + 2) → Fin (m + 2) → ℝ) :
    higham11_4_bunchKaufmanProductEntry (m + 2) (flMixedL fp (s.consTwo) A)
        (flMixedD fp (s.consTwo) A) (Fin.succ 0) 0 = |A (oneIdx m) 0| := by
  unfold higham11_4_bunchKaufmanProductEntry
  simp only [sum_fin_add_two, flMixedL_consTwo_00, flMixedL_consTwo_01, flMixedL_consTwo_0t,
    flMixedL_consTwo_10, flMixedL_consTwo_11, flMixedL_consTwo_1t,
    flMixedD_consTwo_10,
    abs_zero, abs_one, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add,
    Finset.sum_const_zero]

theorem productEntry_consTwo_11 (fp : FPModel) {m : ℕ}
    (s : PivotSchedule m) (A : Fin (m + 2) → Fin (m + 2) → ℝ) :
    higham11_4_bunchKaufmanProductEntry (m + 2) (flMixedL fp (s.consTwo) A)
        (flMixedD fp (s.consTwo) A) (Fin.succ 0) (Fin.succ 0) = |A (oneIdx m) (oneIdx m)| := by
  unfold higham11_4_bunchKaufmanProductEntry
  simp only [sum_fin_add_two, flMixedL_consTwo_10, flMixedL_consTwo_11, flMixedL_consTwo_1t,
    flMixedD_consTwo_11,
    abs_zero, abs_one, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add,
    Finset.sum_const_zero]

theorem productEntry_head00 (fp : FPModel) {n : ℕ}
    (s : PivotSchedule (n + 1)) (A : Fin (n + 1) → Fin (n + 1) → ℝ) :
    higham11_4_bunchKaufmanProductEntry (n + 1) (flMixedL fp s A) (flMixedD fp s A) 0 0
      = |A 0 0| := by
  cases s with
  | consOne s' =>
      unfold higham11_4_bunchKaufmanProductEntry
      simp only [Fin.sum_univ_succ, flMixedL_consOne_00, flMixedL_consOne_0s,
        flMixedD_consOne_00,
        abs_zero, abs_one, zero_mul, mul_zero, one_mul, mul_one, add_zero,
        Finset.sum_const_zero]
  | consTwo s' =>
      exact productEntry_consTwo_00 fp s' A

theorem productEntry_consOne_0s (fp : FPModel) {n : ℕ}
    (s : PivotSchedule n) (A : Fin (n + 1) → Fin (n + 1) → ℝ) (j : Fin n) :
    higham11_4_bunchKaufmanProductEntry (n + 1) (flMixedL fp (s.consOne) A)
        (flMixedD fp (s.consOne) A) 0 j.succ
      = |A 0 0| * |fp.fl_div (A j.succ 0) (A 0 0)| := by
  unfold higham11_4_bunchKaufmanProductEntry
  rw [Fin.sum_univ_succ]
  rw [show (∑ k₁ : Fin n, ∑ k₂, |flMixedL fp (s.consOne) A 0 k₁.succ|
        * |flMixedD fp (s.consOne) A k₁.succ k₂| * |flMixedL fp (s.consOne) A j.succ k₂|) = 0 from by
    apply Finset.sum_eq_zero; intro k₁ _; apply Finset.sum_eq_zero; intro k₂ _; simp]
  rw [add_zero, Fin.sum_univ_succ]
  rw [show (∑ k₂ : Fin n, |flMixedL fp (s.consOne) A 0 0|
        * |flMixedD fp (s.consOne) A 0 k₂.succ| * |flMixedL fp (s.consOne) A j.succ k₂.succ|) = 0 from by
    apply Finset.sum_eq_zero; intro k₂ _; simp]
  rw [add_zero]
  simp only [flMixedL_consOne_00, flMixedD_consOne_00, flMixedL_consOne_s0, abs_one, one_mul]

theorem productEntry_consOne_s0 (fp : FPModel) {n : ℕ}
    (s : PivotSchedule n) (A : Fin (n + 1) → Fin (n + 1) → ℝ) (i : Fin n) :
    higham11_4_bunchKaufmanProductEntry (n + 1) (flMixedL fp (s.consOne) A)
        (flMixedD fp (s.consOne) A) i.succ 0
      = |fp.fl_div (A i.succ 0) (A 0 0)| * |A 0 0| := by
  unfold higham11_4_bunchKaufmanProductEntry
  have hinner : ∀ k₁ : Fin (n + 1),
      (∑ k₂, |flMixedL fp (s.consOne) A i.succ k₁| * |flMixedD fp (s.consOne) A k₁ k₂|
          * |flMixedL fp (s.consOne) A 0 k₂|)
        = |flMixedL fp (s.consOne) A i.succ k₁| * |flMixedD fp (s.consOne) A k₁ 0|
          * |flMixedL fp (s.consOne) A 0 0| := by
    intro k₁
    rw [Fin.sum_univ_succ]
    rw [show (∑ k₂ : Fin n, |flMixedL fp (s.consOne) A i.succ k₁|
          * |flMixedD fp (s.consOne) A k₁ k₂.succ| * |flMixedL fp (s.consOne) A 0 k₂.succ|) = 0 from by
      apply Finset.sum_eq_zero; intro k₂ _; simp]
    rw [add_zero]
  simp_rw [hinner]
  rw [Fin.sum_univ_succ]
  rw [show (∑ k₁ : Fin n, |flMixedL fp (s.consOne) A i.succ k₁.succ|
        * |flMixedD fp (s.consOne) A k₁.succ 0| * |flMixedL fp (s.consOne) A 0 0|) = 0 from by
    apply Finset.sum_eq_zero; intro k₁ _; simp]
  rw [add_zero]
  simp only [flMixedL_consOne_s0, flMixedD_consOne_00, flMixedL_consOne_00, abs_one, mul_one]

/-! ### Re-proved rounding helpers (originally HFactor-local) -/

theorem fl_div_mul_abs_le (fp : FPModel) (a e : ℝ) (he : e ≠ 0) :
    |e| * |fp.fl_div a e| ≤ (1 + fp.u) * |a| := by
  obtain ⟨δ, hδ, h⟩ := fp.model_div a e he
  rw [h, abs_mul, abs_div]
  have he0 : (|e| : ℝ) ≠ 0 := abs_ne_zero.mpr he
  have hrw : |e| * (|a| / |e| * |1 + δ|) = |a| * |1 + δ| := by
    field_simp
  rw [hrw]
  calc |a| * |1 + δ| ≤ |a| * (1 + fp.u) :=
        mul_le_mul_of_nonneg_left (abs_one_add_le fp hδ) (abs_nonneg _)
    _ = (1 + fp.u) * |a| := by ring

theorem oneByOne_corner_mult_le (fp : FPModel) (σ a11 a21 Amax : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.one)
    (ha11 : a11 ≠ 0) (hσA : σ ≤ Amax) :
    |fp.fl_div a21 a11| ^ 2 * |a11|
      ≤ (1 + fp.u) ^ 2 * (Amax / bunchTridiagonalAlpha) := by
  obtain ⟨δ, hδ, h⟩ := fp.model_div a21 a11 ha11
  have hcorr : |a21 * a21 / a11| ≤ Amax / bunchTridiagonalAlpha :=
    higham11_7_tridiagonal_oneByOne_correction_le_of_choice σ a11 a21 Amax hchoice ha11 hσA
  have ha11' : (|a11| : ℝ) ≠ 0 := abs_ne_zero.mpr ha11
  have hbase : |a21 / a11| ^ 2 * |a11| = |a21 * a21 / a11| := by
    rw [abs_div, div_pow, abs_div, abs_mul]
    field_simp
  have hkey : |fp.fl_div a21 a11| ^ 2 * |a11| = |a21 * a21 / a11| * |1 + δ| ^ 2 := by
    rw [h, abs_mul, mul_pow]
    rw [show |a21 / a11| ^ 2 * |1 + δ| ^ 2 * |a11|
          = (|a21 / a11| ^ 2 * |a11|) * |1 + δ| ^ 2 from by ring, hbase]
  rw [hkey]
  have hδsq : |1 + δ| ^ 2 ≤ (1 + fp.u) ^ 2 := by
    have h1 := abs_one_add_le fp hδ
    have h2 := abs_nonneg (1 + δ)
    nlinarith [h1, h2, fp.u_nonneg]
  have hAmaxα : 0 ≤ Amax / bunchTridiagonalAlpha := le_trans (abs_nonneg _) hcorr
  calc |a21 * a21 / a11| * |1 + δ| ^ 2
      ≤ (Amax / bunchTridiagonalAlpha) * (1 + fp.u) ^ 2 :=
        mul_le_mul hcorr hδsq (by positivity) hAmaxα
    _ = (1 + fp.u) ^ 2 * (Amax / bunchTridiagonalAlpha) := by ring

/-! ### The decoupled factor-norm constant and its domination lemmas -/

noncomputable def growthFactorConst (fp : FPModel) (M0 tau Bcorner : ℝ) : ℝ :=
  Bcorner / M0
  + (1 + fp.u) * tau / M0
  + pathConstRC fp.u M0 tau / M0
  + pathConst2 fp.u M0 tau / M0
  + (1 + fp.u) ^ 2 / bunchTridiagonalAlpha

theorem growthFactorConst_mul_M0 (fp : FPModel) (M0 tau Bcorner : ℝ) (hM0 : 0 < M0) :
    growthFactorConst fp M0 tau Bcorner * M0
      = Bcorner + (1 + fp.u) * tau + pathConstRC fp.u M0 tau + pathConst2 fp.u M0 tau
        + (1 + fp.u) ^ 2 / bunchTridiagonalAlpha * M0 := by
  unfold growthFactorConst
  field_simp

theorem growth_summands_nonneg (fp : FPModel) (M0 tau : ℝ)
    (hM0 : 0 < M0) (hMtau : M0 ≤ tau) (hslack : bunchTridiagonalAlpha * tau < M0) :
    0 ≤ (1 + fp.u) * tau ∧ 0 ≤ pathConstRC fp.u M0 tau ∧ 0 ≤ pathConst2 fp.u M0 tau
      ∧ 0 ≤ (1 + fp.u) ^ 2 / bunchTridiagonalAlpha * M0 ∧ 0 ≤ tau := by
  have hα := bunch_tridiagonal_alpha_pos
  have hu := fp.u_nonneg
  have hτ0 : 0 ≤ tau := le_trans hM0.le hMtau
  refine ⟨by positivity, ?_, ?_, by positivity, hτ0⟩
  · exact pathConstRC_nonneg fp.u M0 tau hu hM0 hτ0 hslack
  · exact pathConst2_nonneg fp.u M0 tau hu hM0 hτ0 hslack

theorem dom_corner (fp : FPModel) (M0 tau Bcorner : ℝ)
    (hM0 : 0 < M0) (hMtau : M0 ≤ tau) (hslack : bunchTridiagonalAlpha * tau < M0)
    (_hBc0 : 0 ≤ Bcorner) :
    Bcorner ≤ growthFactorConst fp M0 tau Bcorner * M0 := by
  rw [growthFactorConst_mul_M0 fp M0 tau Bcorner hM0]
  obtain ⟨h1, h2, h3, h4, h5⟩ := growth_summands_nonneg fp M0 tau hM0 hMtau hslack
  linarith

theorem dom_off (fp : FPModel) (M0 tau Bcorner : ℝ)
    (hM0 : 0 < M0) (hMtau : M0 ≤ tau) (hslack : bunchTridiagonalAlpha * tau < M0)
    (hBc0 : 0 ≤ Bcorner) :
    tau ≤ growthFactorConst fp M0 tau Bcorner * M0 := by
  rw [growthFactorConst_mul_M0 fp M0 tau Bcorner hM0]
  obtain ⟨h1, h2, h3, h4, h5⟩ := growth_summands_nonneg fp M0 tau hM0 hMtau hslack
  have hu := fp.u_nonneg
  nlinarith [h5]

theorem dom_row1 (fp : FPModel) (M0 tau Bcorner : ℝ)
    (hM0 : 0 < M0) (hMtau : M0 ≤ tau) (hslack : bunchTridiagonalAlpha * tau < M0)
    (hBc0 : 0 ≤ Bcorner) :
    (1 + fp.u) * tau ≤ growthFactorConst fp M0 tau Bcorner * M0 := by
  rw [growthFactorConst_mul_M0 fp M0 tau Bcorner hM0]
  obtain ⟨h1, h2, h3, h4, h5⟩ := growth_summands_nonneg fp M0 tau hM0 hMtau hslack
  linarith

theorem dom_rc (fp : FPModel) (M0 tau Bcorner : ℝ)
    (hM0 : 0 < M0) (hMtau : M0 ≤ tau) (hslack : bunchTridiagonalAlpha * tau < M0)
    (hBc0 : 0 ≤ Bcorner) :
    pathConstRC fp.u M0 tau ≤ growthFactorConst fp M0 tau Bcorner * M0 := by
  rw [growthFactorConst_mul_M0 fp M0 tau Bcorner hM0]
  obtain ⟨h1, h2, h3, h4, h5⟩ := growth_summands_nonneg fp M0 tau hM0 hMtau hslack
  linarith

theorem dom_two (fp : FPModel) (M0 tau Bcorner : ℝ)
    (hM0 : 0 < M0) (hMtau : M0 ≤ tau) (hslack : bunchTridiagonalAlpha * tau < M0)
    (_hBc0 : 0 ≤ Bcorner) :
    pathConst2 fp.u M0 tau + Bcorner ≤ growthFactorConst fp M0 tau Bcorner * M0 := by
  rw [growthFactorConst_mul_M0 fp M0 tau Bcorner hM0]
  obtain ⟨h1, h2, h3, h4, h5⟩ := growth_summands_nonneg fp M0 tau hM0 hMtau hslack
  linarith

theorem dom_one (fp : FPModel) (M0 tau Bcorner : ℝ)
    (hM0 : 0 < M0) (hMtau : M0 ≤ tau) (hslack : bunchTridiagonalAlpha * tau < M0)
    (_hBc0 : 0 ≤ Bcorner) :
    (1 + fp.u) ^ 2 / bunchTridiagonalAlpha * M0 + Bcorner
      ≤ growthFactorConst fp M0 tau Bcorner * M0 := by
  rw [growthFactorConst_mul_M0 fp M0 tau Bcorner hM0]
  obtain ⟨h1, h2, h3, h4, h5⟩ := growth_summands_nonneg fp M0 tau hM0 hMtau hslack
  linarith

/-! ### Reduced-corner refresh: both pivot sizes give a reduced corner ≤ Bcorner -/

theorem schur2Corner_le_Bcorner (fp : FPModel) (hval : gammaValid fp 3) {m : ℕ}
    (A : Fin (m + 3) → Fin (m + 3) → ℝ) (hA : IsSymTridiagonal (m + 3) A)
    (M0 tau Bcorner : ℝ) (hM0 : 0 < M0) (hslack : bunchTridiagonalAlpha * tau < M0)
    (hchoice : BunchTridiagonalPivotChoice M0 (A 0 0) (A (oneIdx (m + 1)) 0) PivotSize.two)
    (hoff : ∀ i j : Fin (m + 3), i.val ≠ 0 ∨ j.val ≠ 0 → |A i j| ≤ tau)
    (hBc2 : (1 + gamma fp 3) *
        (tau + tau ^ 2 * bunchTridiagonalAlpha / (M0 - bunchTridiagonalAlpha * tau))
      ≤ Bcorner) :
    |flSchurCompl2 (m + 1) fp A 0 0| ≤ Bcorner := by
  have hα := bunch_tridiagonal_alpha_pos
  have hd : 0 < M0 - bunchTridiagonalAlpha * tau := by linarith
  have hγ0 : 0 ≤ 1 + gamma fp 3 := by have := gamma_nonneg fp hval; linarith
  have hτa22 : |A (oneIdx (m + 1)) (oneIdx (m + 1))| ≤ tau :=
    hoff _ _ (Or.inl (by simp [oneIdx]))
  have hbound := flSchurCompl2_corner_bound_decoupled fp hval A hA M0 tau hM0 hchoice hτa22 hslack
  have hA22 : |A ((0 : Fin (m + 1)).succ.succ) ((0 : Fin (m + 1)).succ.succ)| ≤ tau :=
    hoff _ _ (Or.inl (by simp only [Fin.val_succ, Fin.val_zero]; omega))
  have hanextabs : |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| ≤ tau :=
    hoff _ _ (Or.inl (by simp only [Fin.val_succ, Fin.val_zero]; omega))
  have hτ0 : 0 ≤ tau := le_trans (abs_nonneg _) hanextabs
  have hanextsq : (A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))) ^ 2 ≤ tau ^ 2 := by
    nlinarith [hanextabs, abs_nonneg (A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))),
      sq_abs (A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1)))]
  have hnum2 : (A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))) ^ 2 * bunchTridiagonalAlpha
      ≤ tau ^ 2 * bunchTridiagonalAlpha := mul_le_mul_of_nonneg_right hanextsq hα.le
  have hcorr : (A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))) ^ 2 * bunchTridiagonalAlpha
        / (M0 - bunchTridiagonalAlpha * tau)
      ≤ tau ^ 2 * bunchTridiagonalAlpha / (M0 - bunchTridiagonalAlpha * tau) :=
    div_le_div_of_nonneg_right hnum2 (le_of_lt hd)
  calc |flSchurCompl2 (m + 1) fp A 0 0|
      ≤ (1 + gamma fp 3) *
          (|A ((0 : Fin (m + 1)).succ.succ) ((0 : Fin (m + 1)).succ.succ)|
            + (A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))) ^ 2
                * bunchTridiagonalAlpha / (M0 - bunchTridiagonalAlpha * tau)) := hbound
    _ ≤ (1 + gamma fp 3) *
          (tau + tau ^ 2 * bunchTridiagonalAlpha / (M0 - bunchTridiagonalAlpha * tau)) :=
        mul_le_mul_of_nonneg_left (add_le_add hA22 hcorr) hγ0
    _ ≤ Bcorner := hBc2

theorem schur1Corner_le_Bcorner (fp : FPModel) (hval : gammaValid fp 3) {n : ℕ}
    (A : Fin (n + 2) → Fin (n + 2) → ℝ) (hA : IsSymTridiagonal (n + 2) A)
    (M0 tau Bcorner : ℝ) (_hM0 : 0 < M0)
    (hchoice : BunchTridiagonalPivotChoice M0 (A 0 0) (A ((0 : Fin (n + 1)).succ) 0) PivotSize.one)
    (hA00 : A 0 0 ≠ 0)
    (hoff : ∀ i j : Fin (n + 2), i.val ≠ 0 ∨ j.val ≠ 0 → |A i j| ≤ tau)
    (hBc1 : (1 + gamma fp 3) * (tau + M0 / bunchTridiagonalAlpha) ≤ Bcorner) :
    |flSchurCompl (n + 1) fp A 0 0| ≤ Bcorner := by
  have hγ0 : 0 ≤ 1 + gamma fp 3 := by have := gamma_nonneg fp hval; linarith
  have hbound := flSchurCompl_corner_bound fp hval A hA M0 M0 (le_refl M0) hchoice hA00
  have hA11 : |A ((0 : Fin (n + 1)).succ) ((0 : Fin (n + 1)).succ)| ≤ tau :=
    hoff _ _ (Or.inl (by simp only [Fin.val_succ, Fin.val_zero]; omega))
  calc |flSchurCompl (n + 1) fp A 0 0|
      ≤ (1 + gamma fp 3) *
          (|A ((0 : Fin (n + 1)).succ) ((0 : Fin (n + 1)).succ)|
            + M0 / bunchTridiagonalAlpha) := hbound
    _ ≤ (1 + gamma fp 3) * (tau + M0 / bunchTridiagonalAlpha) :=
        mul_le_mul_of_nonneg_left (add_le_add hA11 le_rfl) hγ0
    _ ≤ Bcorner := hBc1

/-! ### Decoupled trailing terms -/

theorem trailingTwo_le_decoupled (fp : FPModel) (hval : gammaValid fp 3)
    (M0 tau Bcorner : ℝ) (hM0 : 0 < M0) (hMtau : M0 ≤ tau)
    (hslack : bunchTridiagonalAlpha * tau < M0) (hBc0 : 0 ≤ Bcorner)
    (hBc2 : (1 + gamma fp 3) *
        (tau + tau ^ 2 * bunchTridiagonalAlpha / (M0 - bunchTridiagonalAlpha * tau))
      ≤ Bcorner) :
    ∀ {n : ℕ} (s : PivotSchedule n) (A : Fin (n + 2) → Fin (n + 2) → ℝ),
      IsSymTridiagonal (n + 2) A →
      BunchTridiagonalPivotChoice M0 (A 0 0) (A (oneIdx n) 0) PivotSize.two →
      (∀ i j : Fin (n + 2), i.val ≠ 0 ∨ j.val ≠ 0 → |A i j| ≤ tau) →
      (∀ i' j', higham11_4_bunchKaufmanProductEntry n
          (flMixedL fp s (flSchurCompl2 n fp A)) (flMixedD fp s (flSchurCompl2 n fp A)) i' j'
          ≤ growthFactorConst fp M0 tau Bcorner * M0) →
      ∀ i j : Fin n,
        pivotPath2Abs n fp A i j
          + higham11_4_bunchKaufmanProductEntry n
              (flMixedL fp s (flSchurCompl2 n fp A)) (flMixedD fp s (flSchurCompl2 n fp A)) i j
          ≤ growthFactorConst fp M0 tau Bcorner * M0 := by
  intro n
  cases n with
  | zero => intro s A _ _ _ _ i; exact Fin.elim0 i
  | succ n' =>
      intro s A hA hchoice hoff hIH i j
      by_cases hc : i.val = 0 ∧ j.val = 0
      · have hi : i = 0 := Fin.ext hc.1
        have hj : j = 0 := Fin.ext hc.2
        subst hi; subst hj
        rw [productEntry_head00 fp s (flSchurCompl2 (n' + 1) fp A)]
        have hpp : pivotPath2Abs (n' + 1) fp A 0 0 ≤ pathConst2 fp.u M0 tau :=
          pivotPath2Abs_le_decoupled fp M0 tau hM0 hslack A hA hoff hchoice 0 0
        have hKbound : |flSchurCompl2 (n' + 1) fp A 0 0| ≤ Bcorner :=
          schur2Corner_le_Bcorner fp hval A hA M0 tau Bcorner hM0 hslack hchoice hoff hBc2
        calc pivotPath2Abs (n' + 1) fp A 0 0 + |flSchurCompl2 (n' + 1) fp A 0 0|
            ≤ pathConst2 fp.u M0 tau + Bcorner := add_le_add hpp hKbound
          _ ≤ growthFactorConst fp M0 tau Bcorner * M0 :=
              dom_two fp M0 tau Bcorner hM0 hMtau hslack hBc0
      · have hne : i.val ≠ 0 ∨ j.val ≠ 0 := by
          by_contra h; push_neg at h; exact hc ⟨h.1, h.2⟩
        rw [pivotPath2Abs_eq_zero_of_ne_corner fp A hA i j hne, zero_add]
        exact hIH i j

theorem trailingOne_le_decoupled (fp : FPModel) (hval : gammaValid fp 3)
    (M0 tau Bcorner : ℝ) (hM0 : 0 < M0) (hMtau : M0 ≤ tau)
    (hslack : bunchTridiagonalAlpha * tau < M0) (hBc0 : 0 ≤ Bcorner)
    (hBc1 : (1 + gamma fp 3) * (tau + M0 / bunchTridiagonalAlpha) ≤ Bcorner) :
    ∀ {n : ℕ} (s : PivotSchedule n) (A : Fin (n + 1) → Fin (n + 1) → ℝ),
      IsSymTridiagonal (n + 1) A → A 0 0 ≠ 0 →
      (∀ i : Fin n, BunchTridiagonalPivotChoice M0 (A 0 0) (A i.succ 0) PivotSize.one) →
      (∀ i j : Fin (n + 1), i.val ≠ 0 ∨ j.val ≠ 0 → |A i j| ≤ tau) →
      (∀ i' j', higham11_4_bunchKaufmanProductEntry n
          (flMixedL fp s (flSchurCompl n fp A)) (flMixedD fp s (flSchurCompl n fp A)) i' j'
          ≤ growthFactorConst fp M0 tau Bcorner * M0) →
      ∀ i j : Fin n,
        |fp.fl_div (A i.succ 0) (A 0 0)| * |A 0 0| * |fp.fl_div (A j.succ 0) (A 0 0)|
          + higham11_4_bunchKaufmanProductEntry n
              (flMixedL fp s (flSchurCompl n fp A)) (flMixedD fp s (flSchurCompl n fp A)) i j
          ≤ growthFactorConst fp M0 tau Bcorner * M0 := by
  intro n
  cases n with
  | zero => intro s A _ _ _ _ _ i; exact Fin.elim0 i
  | succ n' =>
      intro s A hA hA00 hchoice hoff hIH i j
      have hα := bunch_tridiagonal_alpha_pos
      by_cases hc : i.val = 0 ∧ j.val = 0
      · have hi : i = 0 := Fin.ext hc.1
        have hj : j = 0 := Fin.ext hc.2
        subst hi; subst hj
        rw [productEntry_head00 fp s (flSchurCompl (n' + 1) fp A)]
        have hrw : |fp.fl_div (A (0 : Fin (n' + 1)).succ 0) (A 0 0)| * |A 0 0|
              * |fp.fl_div (A (0 : Fin (n' + 1)).succ 0) (A 0 0)|
            = |fp.fl_div (A (0 : Fin (n' + 1)).succ 0) (A 0 0)| ^ 2 * |A 0 0| := by ring
        rw [hrw]
        have hmult : |fp.fl_div (A (0 : Fin (n' + 1)).succ 0) (A 0 0)| ^ 2 * |A 0 0|
            ≤ (1 + fp.u) ^ 2 / bunchTridiagonalAlpha * M0 := by
          have h := oneByOne_corner_mult_le fp M0 (A 0 0) (A (0 : Fin (n' + 1)).succ 0) M0
            (hchoice 0) hA00 (le_refl M0)
          calc |fp.fl_div (A (0 : Fin (n' + 1)).succ 0) (A 0 0)| ^ 2 * |A 0 0|
              ≤ (1 + fp.u) ^ 2 * (M0 / bunchTridiagonalAlpha) := h
            _ = (1 + fp.u) ^ 2 / bunchTridiagonalAlpha * M0 := by ring
        have hKbound : |flSchurCompl (n' + 1) fp A 0 0| ≤ Bcorner :=
          schur1Corner_le_Bcorner fp hval A hA M0 tau Bcorner hM0 (hchoice 0) hA00 hoff hBc1
        calc |fp.fl_div (A (0 : Fin (n' + 1)).succ 0) (A 0 0)| ^ 2 * |A 0 0|
              + |flSchurCompl (n' + 1) fp A 0 0|
            ≤ (1 + fp.u) ^ 2 / bunchTridiagonalAlpha * M0 + Bcorner := add_le_add hmult hKbound
          _ ≤ growthFactorConst fp M0 tau Bcorner * M0 :=
              dom_one fp M0 tau Bcorner hM0 hMtau hslack hBc0
      · have hzero : |fp.fl_div (A i.succ 0) (A 0 0)| * |A 0 0|
              * |fp.fl_div (A j.succ 0) (A 0 0)| = 0 := by
          rcases not_and_or.mp hc with hi | hj
          · have h0 : A i.succ 0 = 0 := by
              apply hA.2; right; simp only [Fin.val_succ, Fin.val_zero]; omega
            simp only [h0, fl_div_zero_left fp (A 0 0) hA00, abs_zero, zero_mul]
          · have h0 : A j.succ 0 = 0 := by
              apply hA.2; right; simp only [Fin.val_succ, Fin.val_zero]; omega
            simp only [h0, fl_div_zero_left fp (A 0 0) hA00, abs_zero, mul_zero]
        rw [hzero, zero_add]
        exact hIH i j

/-! ### Unfolding lemmas for `TriGrowthBounded` -/

@[simp] theorem TriGrowthBounded_consOne (fp : FPModel) (M0 τmax : ℝ) {n : ℕ}
    (s : PivotSchedule n) (A : Fin (n + 1) → Fin (n + 1) → ℝ) :
    TriGrowthBounded fp M0 τmax s.consOne A ↔
      (IsSymTridiagonal (n + 1) A ∧ A 0 0 ≠ 0 ∧
        (∀ i : Fin n, BunchTridiagonalPivotChoice M0 (A 0 0) (A i.succ 0) PivotSize.one) ∧
        (∀ i j : Fin (n + 1), i.val ≠ 0 ∨ j.val ≠ 0 → |A i j| ≤ τmax) ∧
        TriGrowthBounded fp M0 τmax s (flSchurCompl n fp A)) := Iff.rfl

@[simp] theorem TriGrowthBounded_consTwo (fp : FPModel) (M0 τmax : ℝ) {n : ℕ}
    (s : PivotSchedule n) (A : Fin (n + 2) → Fin (n + 2) → ℝ) :
    TriGrowthBounded fp M0 τmax s.consTwo A ↔
      (IsSymTridiagonal (n + 2) A ∧
        BunchTridiagonalPivotChoice M0 (A 0 0) (A (oneIdx n) 0) PivotSize.two ∧
        (∀ i j : Fin (n + 2), i.val ≠ 0 ∨ j.val ≠ 0 → |A i j| ≤ τmax) ∧
        TriGrowthBounded fp M0 τmax s (flSchurCompl2 n fp A)) := Iff.rfl

/-! ### Step F (decoupled) — the factor-norm entry bound by structural induction -/

theorem hfactor_bound_decoupled (fp : FPModel) (hval : gammaValid fp 3)
    (M0 tau Bcorner : ℝ) (hM0 : 0 < M0) (hMtau : M0 ≤ tau)
    (hslack : bunchTridiagonalAlpha * tau < M0) (hBc0 : 0 ≤ Bcorner)
    (hBc1 : (1 + gamma fp 3) * (tau + M0 / bunchTridiagonalAlpha) ≤ Bcorner)
    (hBc2 : (1 + gamma fp 3) *
        (tau + tau ^ 2 * bunchTridiagonalAlpha / (M0 - bunchTridiagonalAlpha * tau)) ≤ Bcorner) :
    ∀ {k : ℕ} (s : PivotSchedule k) (A : Fin k → Fin k → ℝ),
      TriGrowthBounded fp M0 tau s A →
      (∀ i j : Fin k, i.val = 0 → j.val = 0 → |A i j| ≤ Bcorner) →
      ∀ I J : Fin k,
        higham11_4_bunchKaufmanProductEntry k (flMixedL fp s A) (flMixedD fp s A) I J
          ≤ growthFactorConst fp M0 tau Bcorner * M0 := by
  intro k s
  induction s with
  | nil => intro A _ _ I; exact Fin.elim0 I
  | @consOne n s ih =>
      intro A hdata hcorner I J
      rw [TriGrowthBounded_consOne] at hdata
      obtain ⟨hA, hA00, hchoice, hoff, hrec⟩ := hdata
      have hcornerS : ∀ i j : Fin n, i.val = 0 → j.val = 0 →
          |flSchurCompl n fp A i j| ≤ Bcorner := by
        intro i j hi hj
        have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.2
        obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
        have hi0 : i = 0 := Fin.ext hi
        have hj0 : j = 0 := Fin.ext hj
        subst hi0; subst hj0
        exact schur1Corner_le_Bcorner fp hval A hA M0 tau Bcorner hM0 (hchoice 0) hA00 hoff hBc1
      have hIH := ih (flSchurCompl n fp A) hrec hcornerS
      have hrowbound : ∀ j : Fin n, |A 0 0| * |fp.fl_div (A j.succ 0) (A 0 0)|
          ≤ growthFactorConst fp M0 tau Bcorner * M0 := by
        intro j
        refine le_trans (fl_div_mul_abs_le fp (A j.succ 0) (A 0 0) hA00) ?_
        have hoffval : |A j.succ 0| ≤ tau := hoff j.succ 0 (Or.inl (by simp only [Fin.val_succ]; omega))
        refine le_trans (mul_le_mul_of_nonneg_left hoffval (by have := fp.u_nonneg; linarith)) ?_
        exact dom_row1 fp M0 tau Bcorner hM0 hMtau hslack hBc0
      rcases Fin.eq_zero_or_eq_succ I with rfl | ⟨i, rfl⟩
      · rcases Fin.eq_zero_or_eq_succ J with rfl | ⟨j, rfl⟩
        · rw [productEntry_head00 fp (s.consOne) A]
          exact le_trans (hcorner 0 0 rfl rfl) (dom_corner fp M0 tau Bcorner hM0 hMtau hslack hBc0)
        · rw [productEntry_consOne_0s]; exact hrowbound j
      · rcases Fin.eq_zero_or_eq_succ J with rfl | ⟨j, rfl⟩
        · rw [productEntry_consOne_s0, mul_comm]; exact hrowbound i
        · rw [productEntry_consOne_split fp s A i j]
          exact trailingOne_le_decoupled fp hval M0 tau Bcorner hM0 hMtau hslack hBc0 hBc1
            s A hA hA00 hchoice hoff hIH i j
  | @consTwo m s ih =>
      intro A hdata hcorner I J
      rw [TriGrowthBounded_consTwo] at hdata
      obtain ⟨hA, hchoice, hoff, hrec⟩ := hdata
      have hcornerS : ∀ i j : Fin m, i.val = 0 → j.val = 0 →
          |flSchurCompl2 m fp A i j| ≤ Bcorner := by
        intro i j hi hj
        have hn : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.2
        obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
        have hi0 : i = 0 := Fin.ext hi
        have hj0 : j = 0 := Fin.ext hj
        subst hi0; subst hj0
        exact schur2Corner_le_Bcorner fp hval A hA M0 tau Bcorner hM0 hslack hchoice hoff hBc2
      have hIH := ih (flSchurCompl2 m fp A) hrec hcornerS
      have hoffle : ∀ z : ℝ, z ≤ tau → z ≤ growthFactorConst fp M0 tau Bcorner * M0 := fun z hz =>
        le_trans hz (dom_off fp M0 tau Bcorner hM0 hMtau hslack hBc0)
      have hrc : ∀ z : ℝ, z ≤ pathConstRC fp.u M0 tau →
          z ≤ growthFactorConst fp M0 tau Bcorner * M0 := fun z hz =>
        le_trans hz (dom_rc fp M0 tau Bcorner hM0 hMtau hslack hBc0)
      rcases Fin.eq_zero_or_eq_succ I with rfl | ⟨I', rfl⟩
      · rcases Fin.eq_zero_or_eq_succ J with rfl | ⟨J', rfl⟩
        · rw [productEntry_consTwo_00]
          exact le_trans (hcorner 0 0 rfl rfl) (dom_corner fp M0 tau Bcorner hM0 hMtau hslack hBc0)
        · rcases Fin.eq_zero_or_eq_succ J' with rfl | ⟨j, rfl⟩
          · rw [productEntry_consTwo_01]
            exact hoffle _ (hoff 0 (oneIdx m) (Or.inr (by simp [oneIdx])))
          · rw [productEntry_consTwo_0t]
            exact hrc _ (pivotRowPathAbs_le_decoupled fp M0 tau hM0 hslack A hA hoff hchoice 0 j)
      · rcases Fin.eq_zero_or_eq_succ I' with rfl | ⟨i, rfl⟩
        · rcases Fin.eq_zero_or_eq_succ J with rfl | ⟨J', rfl⟩
          · rw [productEntry_consTwo_10]
            exact hoffle _ (hoff (oneIdx m) 0 (Or.inl (by simp [oneIdx])))
          · rcases Fin.eq_zero_or_eq_succ J' with rfl | ⟨j, rfl⟩
            · rw [productEntry_consTwo_11]
              exact hoffle _ (hoff (oneIdx m) (oneIdx m) (Or.inl (by simp [oneIdx])))
            · rw [productEntry_consTwo_1t]
              exact hrc _ (pivotRowPathAbs_le_decoupled fp M0 tau hM0 hslack A hA hoff hchoice 1 j)
        · rcases Fin.eq_zero_or_eq_succ J with rfl | ⟨J', rfl⟩
          · rw [productEntry_consTwo_t0]
            exact hrc _ (pivotColPathAbs_le_decoupled fp M0 tau hM0 hslack A hA hoff hchoice i 0)
          · rcases Fin.eq_zero_or_eq_succ J' with rfl | ⟨j, rfl⟩
            · rw [productEntry_consTwo_t1]
              exact hrc _ (pivotColPathAbs_le_decoupled fp M0 tau hM0 hslack A hA hoff hchoice i 1)
            · rw [productEntry_consTwo_trailing]
              exact trailingTwo_le_decoupled fp hval M0 tau Bcorner hM0 hMtau hslack hBc0 hBc2
                s A hA hchoice hoff hIH i j

/-! ### Step F wrapper (decoupled): discharge the entry bound from `TriGrowthData` -/

noncomputable def growthBcorner (fp : FPModel) (M0 tau : ℝ) : ℝ :=
  (1 + gamma fp 3) * (tau + M0 / bunchTridiagonalAlpha
    + tau ^ 2 * bunchTridiagonalAlpha / (M0 - bunchTridiagonalAlpha * tau))

theorem hfactor_derived (fp : FPModel) (hval : gammaValid fp 3)
    {k : ℕ} (s : PivotSchedule k) (A : Fin k → Fin k → ℝ) (M0 : ℝ)
    (hM0 : 0 < M0)
    (hvalstages : gammaValid fp (stages s)) (hval1 : gammaValid fp 1)
    (hγα : gamma fp (stages s) < bunchTridiagonalAlpha)
    (hdata : TriGrowthData fp M0 s A)
    (hoff : ∀ i j : Fin k, i.val ≠ 0 ∨ j.val ≠ 0 → |A i j| ≤ M0)
    (hcorner : ∀ i j : Fin k, i.val = 0 → j.val = 0 → |A i j| ≤ M0) :
    ∀ I J : Fin k,
      higham11_4_bunchKaufmanProductEntry k (flMixedL fp s A) (flMixedD fp s A) I J
        ≤ growthFactorConst fp M0 ((1 + gamma fp (stages s)) * M0)
            (growthBcorner fp M0 ((1 + gamma fp (stages s)) * M0)) * M0 := by
  set g := gamma fp (stages s) with hg
  set τ := (1 + g) * M0 with hτdef
  set Bcorner := growthBcorner fp M0 τ with hBcdef
  have hα := bunch_tridiagonal_alpha_pos
  have hαsq := bunch_tridiagonal_alpha_sq
  have hg0 : 0 ≤ g := gamma_nonneg fp hvalstages
  have hγ30 : 0 ≤ 1 + gamma fp 3 := by have := gamma_nonneg fp hval; linarith
  have hMtau : M0 ≤ τ := by rw [hτdef]; nlinarith [hg0, hM0]
  have hτ0 : 0 ≤ τ := le_trans hM0.le hMtau
  have hslack : bunchTridiagonalAlpha * τ < M0 := by
    rw [hτdef]
    nlinarith [mul_lt_mul_of_pos_left hγα hα, hαsq, hM0, mul_pos hα hM0]
  have hd : 0 < M0 - bunchTridiagonalAlpha * τ := by linarith [hslack]
  have hcorr1 : 0 ≤ M0 / bunchTridiagonalAlpha := div_nonneg hM0.le hα.le
  have hcorr2 : 0 ≤ τ ^ 2 * bunchTridiagonalAlpha / (M0 - bunchTridiagonalAlpha * τ) :=
    div_nonneg (by positivity) hd.le
  have hBc0 : 0 ≤ Bcorner := by
    rw [hBcdef, growthBcorner]
    have : 0 ≤ τ + M0 / bunchTridiagonalAlpha
        + τ ^ 2 * bunchTridiagonalAlpha / (M0 - bunchTridiagonalAlpha * τ) := by
      linarith [hτ0, hcorr1, hcorr2]
    exact mul_nonneg hγ30 this
  have hBc1 : (1 + gamma fp 3) * (τ + M0 / bunchTridiagonalAlpha) ≤ Bcorner := by
    rw [hBcdef, growthBcorner]
    exact mul_le_mul_of_nonneg_left (by linarith [hcorr2]) hγ30
  have hBc2 : (1 + gamma fp 3) *
      (τ + τ ^ 2 * bunchTridiagonalAlpha / (M0 - bunchTridiagonalAlpha * τ)) ≤ Bcorner := by
    rw [hBcdef, growthBcorner]
    exact mul_le_mul_of_nonneg_left (by linarith [hcorr1]) hγ30
  have hM0Bc : M0 ≤ Bcorner := by
    rw [hBcdef, growthBcorner]
    have hX : M0 ≤ τ + M0 / bunchTridiagonalAlpha
        + τ ^ 2 * bunchTridiagonalAlpha / (M0 - bunchTridiagonalAlpha * τ) := by
      linarith [hMtau, hcorr1, hcorr2]
    have hX0 : 0 ≤ τ + M0 / bunchTridiagonalAlpha
        + τ ^ 2 * bunchTridiagonalAlpha / (M0 - bunchTridiagonalAlpha * τ) :=
      le_trans hM0.le hX
    exact le_trans hX (le_mul_of_one_le_left hX0 (by linarith [gamma_nonneg fp hval]))
  have hpow : (1 + fp.u) ^ stages s ≤ 1 + g :=
    one_add_u_pow_le fp (le_refl (stages s)) hvalstages hval1
  have hbudget : (1 + fp.u) ^ stages s * M0 ≤ τ := by
    rw [hτdef]; exact mul_le_mul_of_nonneg_right hpow hM0.le
  have hTGB : TriGrowthBounded fp M0 τ s A :=
    growth_offcorner fp M0 τ s A M0 hdata hoff hM0.le hbudget
  have hcornerB : ∀ i j : Fin k, i.val = 0 → j.val = 0 → |A i j| ≤ Bcorner :=
    fun i j hi hj => le_trans (hcorner i j hi hj) hM0Bc
  exact hfactor_bound_decoupled fp hval M0 τ Bcorner hM0 hMtau hslack hBc0 hBc1 hBc2 s A hTGB hcornerB

end NumStability.Ch11Closure.TriGrowthInv
