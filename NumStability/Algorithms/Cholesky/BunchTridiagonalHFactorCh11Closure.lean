/-
Chapter 11 closure: **discharging `hfactor` and producing the unconditional
Theorem 11.7** (Bunch's symmetric-tridiagonal pivoting, Algorithm 11.6).

The module `BlockLDLTBunchTridiagonalCh11Closure` derives Theorem 11.7 modulo the
"constant growth" factor-norm hypothesis

  `hfactor : |L̂||D̂||L̂ᵀ| i j ≤ c₀·Amax`.

The sibling modules proved every hard ingredient:
  * `BunchTridiagonalGrowthCh11Closure`: the per-step corner constant-growth
    bounds `flSchurCompl2_corner_bound` / `flSchurCompl_corner_bound` (the reduced
    corner does not compound), and the corner reductions;
  * `BunchTridiagonalFactorBoundCh11Closure`: the corner cancellation cores
    `corner_quadform_core` / `corner_rowcol_le_core`, the corner instantiation
    `pivotPath2Abs_corner_le`, and the banding lemmas
    `pivotPath2Abs_eq_zero_of_ne_corner` etc.

This file performs the remaining **structural assembly**:
  * (Step G' ingredients) the mechanical instantiation of `corner_rowcol_le_core`
    into `pivotRowPathAbs`/`pivotColPathAbs` at the corner, and the analogous
    1×1 multiplier bounds;
  * (Step F) a structural induction over `PivotSchedule` proving

      `higham11_4_bunchKaufmanProductEntry n (flMixedL fp s A) (flMixedD fp s A) i j
          ≤ c₀·Amax`

    from a per-stage `TriPivotData` record of the Algorithm-11.6 pivot choices and
    local `σ`-scales.  The banding lemmas make each product entry collect only
    `O(1)` nonzero contributions, so `c₀` is dimension-independent.
  * (Wrapper) `higham11_7_bunch_tridiagonal_backward_error_unconditional`, which
    supplies `hfactor` from Step F, so its hypotheses are only
    `FlMixedPivots`/(11.5) + `TriPivotData` (tridiagonal structure + per-stage
    pivot data) + the solve-side (11.5), NOT `hfactor`.

No `sorry`/`admit`/`axiom`/`native_decide`.
-/
import NumStability.Algorithms.Cholesky.BunchTridiagonalFactorBoundCh11Closure

open scoped BigOperators

namespace NumStability.Ch11Closure.HFactor

open NumStability
open NumStability.Ch11Closure
open NumStability.Ch11Closure.Mixed
open NumStability.Ch11Closure.BunchTri
open NumStability.Ch11Closure.BunchTriGrowth
open NumStability.Ch11Closure.BunchTriFactor

/-! ## Part 1 — product-entry equalities at pivot-block indices

`higham11_4_bunchKaufmanProductEntry` at the four leading indices of a 2×2 stage,
and at the leading `(0,0)` of any stage, reproduces the (absolute) leading block
entries exactly.  Proved by the same `sum_fin_add_two` reductions used for the
pivot-row/column split lemmas. -/

theorem productEntry_consTwo_00 (fp : FPModel) {m : ℕ}
    (s : PivotSchedule m) (A : Fin (m + 2) → Fin (m + 2) → ℝ) :
    higham11_4_bunchKaufmanProductEntry (m + 2) (flMixedL fp (s.consTwo) A)
        (flMixedD fp (s.consTwo) A) 0 0 = |A 0 0| := by
  unfold higham11_4_bunchKaufmanProductEntry
  simp only [sum_fin_add_two, flMixedL_consTwo_00, flMixedL_consTwo_01, flMixedL_consTwo_0t,
    flMixedD_consTwo_00, flMixedD_consTwo_01, flMixedD_consTwo_0t,
    abs_zero, abs_one, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add,
    Finset.sum_const_zero]

theorem productEntry_consTwo_01 (fp : FPModel) {m : ℕ}
    (s : PivotSchedule m) (A : Fin (m + 2) → Fin (m + 2) → ℝ) :
    higham11_4_bunchKaufmanProductEntry (m + 2) (flMixedL fp (s.consTwo) A)
        (flMixedD fp (s.consTwo) A) 0 (Fin.succ 0) = |A 0 (oneIdx m)| := by
  unfold higham11_4_bunchKaufmanProductEntry
  simp only [sum_fin_add_two, flMixedL_consTwo_00, flMixedL_consTwo_01, flMixedL_consTwo_0t,
    flMixedL_consTwo_10, flMixedL_consTwo_11, flMixedL_consTwo_1t,
    flMixedD_consTwo_00, flMixedD_consTwo_01, flMixedD_consTwo_0t,
    abs_zero, abs_one, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add,
    Finset.sum_const_zero]

theorem productEntry_consTwo_10 (fp : FPModel) {m : ℕ}
    (s : PivotSchedule m) (A : Fin (m + 2) → Fin (m + 2) → ℝ) :
    higham11_4_bunchKaufmanProductEntry (m + 2) (flMixedL fp (s.consTwo) A)
        (flMixedD fp (s.consTwo) A) (Fin.succ 0) 0 = |A (oneIdx m) 0| := by
  unfold higham11_4_bunchKaufmanProductEntry
  simp only [sum_fin_add_two, flMixedL_consTwo_00, flMixedL_consTwo_01, flMixedL_consTwo_0t,
    flMixedL_consTwo_10, flMixedL_consTwo_11, flMixedL_consTwo_1t,
    flMixedD_consTwo_10, flMixedD_consTwo_11, flMixedD_consTwo_1t,
    abs_zero, abs_one, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add,
    Finset.sum_const_zero]

theorem productEntry_consTwo_11 (fp : FPModel) {m : ℕ}
    (s : PivotSchedule m) (A : Fin (m + 2) → Fin (m + 2) → ℝ) :
    higham11_4_bunchKaufmanProductEntry (m + 2) (flMixedL fp (s.consTwo) A)
        (flMixedD fp (s.consTwo) A) (Fin.succ 0) (Fin.succ 0) = |A (oneIdx m) (oneIdx m)| := by
  unfold higham11_4_bunchKaufmanProductEntry
  simp only [sum_fin_add_two, flMixedL_consTwo_10, flMixedL_consTwo_11, flMixedL_consTwo_1t,
    flMixedD_consTwo_10, flMixedD_consTwo_11, flMixedD_consTwo_1t,
    abs_zero, abs_one, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add,
    Finset.sum_const_zero]

/-- The leading `(0,0)` product entry of ANY stage is the absolute leading pivot
    entry `|A 0 0|`. -/
theorem productEntry_head00 (fp : FPModel) {n : ℕ}
    (s : PivotSchedule (n + 1)) (A : Fin (n + 1) → Fin (n + 1) → ℝ) :
    higham11_4_bunchKaufmanProductEntry (n + 1) (flMixedL fp s A) (flMixedD fp s A) 0 0
      = |A 0 0| := by
  cases s with
  | consOne s' =>
      unfold higham11_4_bunchKaufmanProductEntry
      simp only [Fin.sum_univ_succ, flMixedL_consOne_00, flMixedL_consOne_0s,
        flMixedD_consOne_00, flMixedD_consOne_0s,
        abs_zero, abs_one, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add,
        Finset.sum_const_zero]
  | consTwo s' =>
      exact productEntry_consTwo_00 fp s' A

/-! ## Part 2 — corner pivot-row / pivot-column bounds

Instantiating `corner_rowcol_le_core` with the genuine `flMixedMult2` corner
multipliers (the identical setup used in `pivotPath2Abs_corner_le`) bounds the
four corner pivot-row / pivot-column abs paths by a constant multiple of `σ`. -/

theorem pivotRowColPathAbs_corner_le (fp : FPModel) {m : ℕ}
    (A : Fin (m + 3) → Fin (m + 3) → ℝ) (hA : IsSymTridiagonal (m + 3) A)
    (σ : ℝ) (hσpos : 0 < σ)
    (hchoice : BunchTridiagonalPivotChoice σ (A 0 0) (A (oneIdx (m + 1)) 0) PivotSize.two)
    (hσa21 : |A (oneIdx (m + 1)) 0| ≤ σ)
    (hσa22 : |A (oneIdx (m + 1)) (oneIdx (m + 1))| ≤ σ)
    (hσanext : |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| ≤ σ) :
    pivotRowPathAbs (m + 1) fp A 0 0
        ≤ 2 * (1 + fp.u) * σ / bunchTridiagonalAlpha
      ∧ pivotRowPathAbs (m + 1) fp A 1 0
        ≤ 2 * (1 + fp.u) * σ / bunchTridiagonalAlpha ^ 2
      ∧ pivotColPathAbs (m + 1) fp A 0 0
        ≤ 2 * (1 + fp.u) * σ / bunchTridiagonalAlpha
      ∧ pivotColPathAbs (m + 1) fp A 0 1
        ≤ 2 * (1 + fp.u) * σ / bunchTridiagonalAlpha ^ 2 := by
  have hu0 := fp.u_nonneg
  have hα1 : bunchTridiagonalAlpha < 1 := bunch_tridiagonal_alpha_lt_one
  have hgap : 0 < 1 - bunchTridiagonalAlpha := by linarith
  have hsym : A 0 (oneIdx (m + 1)) = A (oneIdx (m + 1)) 0 := hA.1 0 (oneIdx (m + 1))
  have ha21ne : A (oneIdx (m + 1)) 0 ≠ 0 :=
    bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_sigma_nonneg σ (A 0 0)
      (A (oneIdx (m + 1)) 0) hchoice hσpos.le
  have ha21sq : 0 < A (oneIdx (m + 1)) 0 ^ 2 := sq_pos_of_ne_zero ha21ne
  have hdeteq : mixedDet2 (m + 1) A
      = A 0 0 * A (oneIdx (m + 1)) (oneIdx (m + 1)) - A (oneIdx (m + 1)) 0 ^ 2 := by
    unfold mixedDet2; rw [hsym]; ring
  have habsdet := bunch_tridiagonal_twoByTwo_absdet_lower_of_sigma_bound σ (A 0 0)
    (A (oneIdx (m + 1)) 0) (A (oneIdx (m + 1)) (oneIdx (m + 1))) hchoice hσa22
  have hDgt : 0 < |mixedDet2 (m + 1) A| := by
    rw [hdeteq]; exact lt_of_lt_of_le (mul_pos hgap ha21sq) habsdet
  have hDlow : bunchTridiagonalAlpha ^ 2 * |A (oneIdx (m + 1)) 0| ^ 2
      ≤ |mixedDet2 (m + 1) A| := by
    rw [hdeteq, sq_abs, bunch_tridiagonal_alpha_sq]; exact habsdet
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
  -- the core inequality
  obtain ⟨hrow0, hrow1⟩ := corner_rowcol_le_core fp.u σ |A 0 0| |A (oneIdx (m + 1)) 0|
    |A (oneIdx (m + 1)) (oneIdx (m + 1))|
    |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
    |flMixedMult2 (m + 1) fp A 0 0| |flMixedMult2 (m + 1) fp A 0 1|
    |mixedDet2 (m + 1) A|
    hu0 hσpos (abs_nonneg _) (abs_pos.mpr ha21ne) (abs_nonneg _) (abs_nonneg _)
    hDgt hDlow htest hσa21 hσa22 hσanext hw0D hw1D
  -- expansions
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

/-! ## Part 3 — the 1×1 multiplier bounds

The two floating-point multiplier products appearing in a 1×1 tridiagonal Bunch
stage: the pivot-row / pivot-column entry `|A₀₀|·|fl(a/A₀₀)|` (linear) and the
`(0,0)` trailing multiplier square `|fl(a₂₁/a₁₁)|²·|a₁₁|` (the 1×1 corner path).
The latter uses the 1×1 acceptance test to cancel the `a₂₁²/a₁₁` ratio. -/

/-- `|e|·|fl(a/e)| ≤ (1+u)·|a|` for `e ≠ 0`: one rounding of a division whose exact
    value is `a/e`, remultiplied by `|e|`. -/
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

/-- **1×1 corner multiplier square.**  Using the Algorithm-11.6 1×1 acceptance test
    (via `higham11_7_tridiagonal_oneByOne_correction_le_of_choice`, which cancels
    the `a₂₁²/a₁₁` ratio), the corner trailing multiplier square is a constant
    multiple of `Amax`:

      `|fl(a₂₁/a₁₁)|²·|a₁₁| ≤ (1+u)²·Amax/α`. -/
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

/-! ## Part 4 — uniform abs pivot-path bounds along a stage

For a symmetric tridiagonal 2×2 stage with an accepted pivot and local scale
`σ ≤ Amax`, every abs pivot path is bounded by a dimension-independent constant
multiple of `Amax` — either by the corner cancellation (leading corner) or by the
banding lemmas (everywhere else).  The dimension `cases m` is discharged here so
the main induction never needs it. -/

/-- Local nonnegativity helper for the constant `bunchTridiagonalAlpha`. -/
private theorem alpha_sq_pos : 0 < bunchTridiagonalAlpha ^ 2 := by
  have := bunch_tridiagonal_alpha_pos; positivity

private theorem alpha_cube_pos : 0 < bunchTridiagonalAlpha ^ 3 := by
  have := bunch_tridiagonal_alpha_pos; positivity

/-- **Uniform corner-path bound.**  `pivotPath2Abs m fp A i j ≤ Cpath·Amax` for all
    trailing `i j`, with `Cpath = (1+u)²(3+α)/α³`. -/
theorem pivotPath2Abs_le (fp : FPModel) (Amax : ℝ) (hAmax : 0 ≤ Amax) :
    ∀ {m : ℕ} (A : Fin (m + 2) → Fin (m + 2) → ℝ), IsSymTridiagonal (m + 2) A →
      ∀ σ : ℝ, 0 < σ → σ ≤ Amax → (∀ i j, |A i j| ≤ σ) →
        BunchTridiagonalPivotChoice σ (A 0 0) (A (oneIdx m) 0) PivotSize.two →
        ∀ i j : Fin m, pivotPath2Abs m fp A i j
          ≤ (1 + fp.u) ^ 2 * (3 + bunchTridiagonalAlpha) / bunchTridiagonalAlpha ^ 3 * Amax := by
  intro m
  cases m with
  | zero => intro A _ σ _ _ _ _ i; exact Fin.elim0 i
  | succ m' =>
      intro A hA σ hσpos hσA hσ hchoice i j
      have hCpath0 : 0 ≤ (1 + fp.u) ^ 2 * (3 + bunchTridiagonalAlpha) / bunchTridiagonalAlpha ^ 3 := by
        have hα := bunch_tridiagonal_alpha_pos
        have hu := fp.u_nonneg
        positivity
      by_cases hc : i.val = 0 ∧ j.val = 0
      · obtain ⟨hi0, hj0⟩ := hc
        have hi : i = 0 := by rw [Fin.ext_iff, Fin.val_zero]; exact hi0
        have hj : j = 0 := by rw [Fin.ext_iff, Fin.val_zero]; exact hj0
        subst hi; subst hj
        refine (pivotPath2Abs_corner_le fp A hA σ hσpos hchoice (hσ _ _) (hσ _ _)).trans ?_
        have heq : (1 + fp.u) ^ 2 * (3 + bunchTridiagonalAlpha) * σ / bunchTridiagonalAlpha ^ 3
            = ((1 + fp.u) ^ 2 * (3 + bunchTridiagonalAlpha) / bunchTridiagonalAlpha ^ 3) * σ := by
          ring
        rw [heq]
        exact mul_le_mul_of_nonneg_left hσA hCpath0
      · have hne : i.val ≠ 0 ∨ j.val ≠ 0 := by
          by_contra h; push_neg at h; exact hc ⟨h.1, h.2⟩
        rw [pivotPath2Abs_eq_zero_of_ne_corner fp A hA i j hne]
        exact mul_nonneg hCpath0 hAmax

/-- **Uniform corner pivot-row bound.**  `pivotRowPathAbs m fp A p j ≤ Crc·Amax` for
    all `p j`, with `Crc = 2(1+u)/α²`. -/
theorem pivotRowPathAbs_le (fp : FPModel) (Amax : ℝ) (hAmax : 0 ≤ Amax) :
    ∀ {m : ℕ} (A : Fin (m + 2) → Fin (m + 2) → ℝ), IsSymTridiagonal (m + 2) A →
      ∀ σ : ℝ, 0 < σ → σ ≤ Amax → (∀ i j, |A i j| ≤ σ) →
        BunchTridiagonalPivotChoice σ (A 0 0) (A (oneIdx m) 0) PivotSize.two →
        ∀ (p : Fin 2) (j : Fin m), pivotRowPathAbs m fp A p j
          ≤ 2 * (1 + fp.u) / bunchTridiagonalAlpha ^ 2 * Amax := by
  intro m
  cases m with
  | zero => intro A _ σ _ _ _ _ _ j; exact Fin.elim0 j
  | succ m' =>
      intro A hA σ hσpos hσA hσ hchoice p j
      have hα := bunch_tridiagonal_alpha_pos
      have hα1 := bunch_tridiagonal_alpha_lt_one
      have hCrc0 : 0 ≤ 2 * (1 + fp.u) / bunchTridiagonalAlpha ^ 2 := by
        have hu := fp.u_nonneg; positivity
      have hα2le : bunchTridiagonalAlpha ^ 2 ≤ bunchTridiagonalAlpha := by nlinarith [hα, hα1]
      -- the two corner bounds (both ≤ Crc·Amax)
      obtain ⟨hr0, hr1, _, _⟩ := pivotRowColPathAbs_corner_le fp A hA σ hσpos hchoice
        (hσ _ _) (hσ _ _) (hσ _ _)
      -- relaxation to Crc·Amax
      have hrelaxα2 : 2 * (1 + fp.u) * σ / bunchTridiagonalAlpha ^ 2
          ≤ 2 * (1 + fp.u) / bunchTridiagonalAlpha ^ 2 * Amax := by
        have heq : 2 * (1 + fp.u) * σ / bunchTridiagonalAlpha ^ 2
            = (2 * (1 + fp.u) / bunchTridiagonalAlpha ^ 2) * σ := by ring
        rw [heq]; exact mul_le_mul_of_nonneg_left hσA hCrc0
      have hrelaxα : 2 * (1 + fp.u) * σ / bunchTridiagonalAlpha
          ≤ 2 * (1 + fp.u) / bunchTridiagonalAlpha ^ 2 * Amax := by
        refine le_trans ?_ hrelaxα2
        apply div_le_div_of_nonneg_left _ (alpha_sq_pos) hα2le
        have hu := fp.u_nonneg
        have := hσpos.le
        positivity
      have hCrc0' : 0 ≤ 2 * (1 + fp.u) / bunchTridiagonalAlpha ^ 2 * Amax :=
        mul_nonneg hCrc0 hAmax
      by_cases hj : j.val = 0
      · have hj0 : j = 0 := by rw [Fin.ext_iff, Fin.val_zero]; exact hj
        subst hj0
        match p with
        | 0 => exact le_trans hr0 hrelaxα
        | 1 => exact le_trans hr1 hrelaxα2
      · rw [pivotRowPathAbs_eq_zero_of_ne_corner fp A hA p j hj]
        exact hCrc0'

/-- **Uniform corner pivot-column bound.**  `pivotColPathAbs m fp A i q ≤ Crc·Amax`
    for all `i q`, with `Crc = 2(1+u)/α²`. -/
theorem pivotColPathAbs_le (fp : FPModel) (Amax : ℝ) (hAmax : 0 ≤ Amax) :
    ∀ {m : ℕ} (A : Fin (m + 2) → Fin (m + 2) → ℝ), IsSymTridiagonal (m + 2) A →
      ∀ σ : ℝ, 0 < σ → σ ≤ Amax → (∀ i j, |A i j| ≤ σ) →
        BunchTridiagonalPivotChoice σ (A 0 0) (A (oneIdx m) 0) PivotSize.two →
        ∀ (i : Fin m) (q : Fin 2), pivotColPathAbs m fp A i q
          ≤ 2 * (1 + fp.u) / bunchTridiagonalAlpha ^ 2 * Amax := by
  intro m
  cases m with
  | zero => intro A _ σ _ _ _ _ i _; exact Fin.elim0 i
  | succ m' =>
      intro A hA σ hσpos hσA hσ hchoice i q
      have hα := bunch_tridiagonal_alpha_pos
      have hα1 := bunch_tridiagonal_alpha_lt_one
      have hCrc0 : 0 ≤ 2 * (1 + fp.u) / bunchTridiagonalAlpha ^ 2 := by
        have hu := fp.u_nonneg; positivity
      have hα2le : bunchTridiagonalAlpha ^ 2 ≤ bunchTridiagonalAlpha := by nlinarith [hα, hα1]
      obtain ⟨_, _, hc0, hc1⟩ := pivotRowColPathAbs_corner_le fp A hA σ hσpos hchoice
        (hσ _ _) (hσ _ _) (hσ _ _)
      have hrelaxα2 : 2 * (1 + fp.u) * σ / bunchTridiagonalAlpha ^ 2
          ≤ 2 * (1 + fp.u) / bunchTridiagonalAlpha ^ 2 * Amax := by
        have heq : 2 * (1 + fp.u) * σ / bunchTridiagonalAlpha ^ 2
            = (2 * (1 + fp.u) / bunchTridiagonalAlpha ^ 2) * σ := by ring
        rw [heq]; exact mul_le_mul_of_nonneg_left hσA hCrc0
      have hrelaxα : 2 * (1 + fp.u) * σ / bunchTridiagonalAlpha
          ≤ 2 * (1 + fp.u) / bunchTridiagonalAlpha ^ 2 * Amax := by
        refine le_trans ?_ hrelaxα2
        apply div_le_div_of_nonneg_left _ (alpha_sq_pos) hα2le
        have hu := fp.u_nonneg
        have := hσpos.le
        positivity
      by_cases hi : i.val = 0
      · have hi0 : i = 0 := by rw [Fin.ext_iff, Fin.val_zero]; exact hi
        subst hi0
        match q with
        | 0 => exact le_trans hc0 hrelaxα
        | 1 => exact le_trans hc1 hrelaxα2
      · rw [pivotColPathAbs_eq_zero_of_ne_corner fp A hA i q hi]
        exact mul_nonneg hCrc0 hAmax

/-! ## Part 5 — the per-stage data, the constant `c₀`, and Step F

`TriPivotData` records, along the schedule, the tridiagonal structure and the
Algorithm-11.6 per-stage pivot choices with a local scale `σ ≤ Amax` bounding
every entry of the stage matrix (the algorithm sets `σ = ‖A^ℓ‖_M`).  It is the
sanctioned per-stage hypothesis family of the Step-G plan. -/

/-- Per-stage pivot-choice / scale data threaded along the pivot schedule.  Each
    1×1 stage records a nonzero pivot and a local scale `σ ≤ Amax` bounding every
    entry, with the Algorithm-11.6 1×1 acceptance test for every subdiagonal (only
    the leading one is nontrivial for a tridiagonal matrix).  Each 2×2 stage
    records a scale and the 2×2 acceptance test. -/
noncomputable def TriPivotData (fp : FPModel) (Amax : ℝ) :
    {n : ℕ} → PivotSchedule n → (Fin n → Fin n → ℝ) → Prop
  | 0, .nil, _ => True
  | n + 1, .consOne s, A =>
      IsSymTridiagonal (n + 1) A ∧ A 0 0 ≠ 0 ∧
      (∃ σ : ℝ, 0 < σ ∧ σ ≤ Amax ∧ (∀ i j, |A i j| ≤ σ) ∧
        ∀ i : Fin n, BunchTridiagonalPivotChoice σ (A 0 0) (A i.succ 0) PivotSize.one) ∧
      TriPivotData fp Amax s (flSchurCompl n fp A)
  | m + 2, .consTwo s, A =>
      IsSymTridiagonal (m + 2) A ∧
      (∃ σ : ℝ, 0 < σ ∧ σ ≤ Amax ∧ (∀ i j, |A i j| ≤ σ) ∧
        BunchTridiagonalPivotChoice σ (A 0 0) (A (oneIdx m) 0) PivotSize.two) ∧
      TriPivotData fp Amax s (flSchurCompl2 m fp A)

@[simp] theorem TriPivotData_consOne (fp : FPModel) (Amax : ℝ) {n : ℕ}
    (s : PivotSchedule n) (A : Fin (n + 1) → Fin (n + 1) → ℝ) :
    TriPivotData fp Amax (s.consOne) A ↔
      (IsSymTridiagonal (n + 1) A ∧ A 0 0 ≠ 0 ∧
        (∃ σ : ℝ, 0 < σ ∧ σ ≤ Amax ∧ (∀ i j, |A i j| ≤ σ) ∧
          ∀ i : Fin n, BunchTridiagonalPivotChoice σ (A 0 0) (A i.succ 0) PivotSize.one) ∧
        TriPivotData fp Amax s (flSchurCompl n fp A)) := Iff.rfl

@[simp] theorem TriPivotData_consTwo (fp : FPModel) (Amax : ℝ) {m : ℕ}
    (s : PivotSchedule m) (A : Fin (m + 2) → Fin (m + 2) → ℝ) :
    TriPivotData fp Amax (s.consTwo) A ↔
      (IsSymTridiagonal (m + 2) A ∧
        (∃ σ : ℝ, 0 < σ ∧ σ ≤ Amax ∧ (∀ i j, |A i j| ≤ σ) ∧
          BunchTridiagonalPivotChoice σ (A 0 0) (A (oneIdx m) 0) PivotSize.two) ∧
        TriPivotData fp Amax s (flSchurCompl2 m fp A)) := Iff.rfl

/-- The dimension-independent factor-norm constant `c₀`: the sum of every per-entry
    contribution coefficient (corner quad path, refreshed corner growth `K`, corner
    row/col path, 1×1 corner path, 1×1 row/col, pivot block). -/
noncomputable def hfactorConst (fp : FPModel) : ℝ :=
  (1 + fp.u) ^ 2 * (3 + bunchTridiagonalAlpha) / bunchTridiagonalAlpha ^ 3
  + (1 + gamma fp 3) * (1 + 1 / bunchTridiagonalAlpha)
  + 2 * (1 + fp.u) / bunchTridiagonalAlpha ^ 2
  + (1 + fp.u) ^ 2 / bunchTridiagonalAlpha
  + (1 + fp.u)
  + 1

/-- The six summands of `hfactorConst` are all nonnegative. -/
private theorem hfc_summands_nonneg (fp : FPModel) (hval : gammaValid fp 3) :
    0 ≤ (1 + fp.u) ^ 2 * (3 + bunchTridiagonalAlpha) / bunchTridiagonalAlpha ^ 3
    ∧ 0 ≤ (1 + gamma fp 3) * (1 + 1 / bunchTridiagonalAlpha)
    ∧ 0 ≤ 2 * (1 + fp.u) / bunchTridiagonalAlpha ^ 2
    ∧ 0 ≤ (1 + fp.u) ^ 2 / bunchTridiagonalAlpha
    ∧ 0 ≤ (1 + fp.u) := by
  have hα := bunch_tridiagonal_alpha_pos
  have hu := fp.u_nonneg
  have hγ := gamma_nonneg fp hval
  have honeα : (0 : ℝ) < 1 / bunchTridiagonalAlpha := one_div_pos.mpr hα
  refine ⟨?_, ?_, ?_, ?_, by linarith⟩
  · exact div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) alpha_cube_pos.le
  · exact mul_nonneg (by linarith) (by linarith)
  · exact div_nonneg (by linarith) alpha_sq_pos.le
  · exact div_nonneg (sq_nonneg _) hα.le

theorem hfactorConst_nonneg (fp : FPModel) (hval : gammaValid fp 3) :
    0 ≤ hfactorConst fp := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hfc_summands_nonneg fp hval
  unfold hfactorConst; linarith

/-- Domination: the 2×2 trailing coefficient (`Cpath + K`) is `≤ c₀`. -/
theorem dom_two (fp : FPModel) (hval : gammaValid fp 3) :
    (1 + fp.u) ^ 2 * (3 + bunchTridiagonalAlpha) / bunchTridiagonalAlpha ^ 3
      + (1 + gamma fp 3) * (1 + 1 / bunchTridiagonalAlpha) ≤ hfactorConst fp := by
  obtain ⟨_, _, h3, h4, h5⟩ := hfc_summands_nonneg fp hval
  unfold hfactorConst; linarith

/-- Domination: the corner row/column coefficient (`Crc`) is `≤ c₀`. -/
theorem dom_rc (fp : FPModel) (hval : gammaValid fp 3) :
    2 * (1 + fp.u) / bunchTridiagonalAlpha ^ 2 ≤ hfactorConst fp := by
  obtain ⟨h1, h2, _, h4, h5⟩ := hfc_summands_nonneg fp hval
  unfold hfactorConst; linarith

/-- Domination: the 1×1 trailing coefficient (`C1x1 + K`) is `≤ c₀`. -/
theorem dom_one (fp : FPModel) (hval : gammaValid fp 3) :
    (1 + fp.u) ^ 2 / bunchTridiagonalAlpha
      + (1 + gamma fp 3) * (1 + 1 / bunchTridiagonalAlpha) ≤ hfactorConst fp := by
  obtain ⟨h1, _, h3, _, h5⟩ := hfc_summands_nonneg fp hval
  unfold hfactorConst; linarith

/-- Domination: the 1×1 pivot-row/column coefficient (`1+u`) is `≤ c₀`. -/
theorem dom_row1 (fp : FPModel) (hval : gammaValid fp 3) :
    (1 + fp.u) ≤ hfactorConst fp := by
  obtain ⟨h1, h2, h3, h4, _⟩ := hfc_summands_nonneg fp hval
  unfold hfactorConst; linarith

/-- Domination: the pivot-block coefficient (`1`) is `≤ c₀`. -/
theorem dom_block (fp : FPModel) (hval : gammaValid fp 3) :
    (1 : ℝ) ≤ hfactorConst fp := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hfc_summands_nonneg fp hval
  unfold hfactorConst; linarith

/-- **2×2 trailing term.**  The leading corner pivot-path plus the recursive Schur
    product entry (via `productEntry_consTwo_trailing`) is `≤ c₀·Amax`: at the
    corner the pivot path (`≤ Cpath·Amax`) adds the *refreshed* reduced corner
    (`≤ K·Amax`, not the induction hypothesis — no compounding); everywhere else the
    pivot path vanishes and the induction hypothesis finishes. -/
theorem trailingTwo_le (fp : FPModel) (hval : gammaValid fp 3) (Amax : ℝ) (hAmax : 0 ≤ Amax) :
    ∀ {m : ℕ} (s : PivotSchedule m) (A : Fin (m + 2) → Fin (m + 2) → ℝ),
      IsSymTridiagonal (m + 2) A →
      (∃ σ : ℝ, 0 < σ ∧ σ ≤ Amax ∧ (∀ i j, |A i j| ≤ σ) ∧
        BunchTridiagonalPivotChoice σ (A 0 0) (A (oneIdx m) 0) PivotSize.two) →
      (∀ i' j', higham11_4_bunchKaufmanProductEntry m
          (flMixedL fp s (flSchurCompl2 m fp A)) (flMixedD fp s (flSchurCompl2 m fp A)) i' j'
          ≤ hfactorConst fp * Amax) →
      ∀ i j : Fin m,
        pivotPath2Abs m fp A i j
          + higham11_4_bunchKaufmanProductEntry m
              (flMixedL fp s (flSchurCompl2 m fp A)) (flMixedD fp s (flSchurCompl2 m fp A)) i j
          ≤ hfactorConst fp * Amax := by
  intro m
  cases m with
  | zero => intro s A _ _ _ i; exact Fin.elim0 i
  | succ m' =>
      intro s A hA hdata hIH i j
      obtain ⟨σ, hσpos, hσA, hσ, hchoice⟩ := hdata
      have hα := bunch_tridiagonal_alpha_pos
      by_cases hc : i.val = 0 ∧ j.val = 0
      · obtain ⟨hi0, hj0⟩ := hc
        have hi : i = 0 := by rw [Fin.ext_iff, Fin.val_zero]; exact hi0
        have hj : j = 0 := by rw [Fin.ext_iff, Fin.val_zero]; exact hj0
        subst hi; subst hj
        rw [productEntry_head00 fp s (flSchurCompl2 (m' + 1) fp A)]
        have hpp : pivotPath2Abs (m' + 1) fp A 0 0
            ≤ (1 + fp.u) ^ 2 * (3 + bunchTridiagonalAlpha) / bunchTridiagonalAlpha ^ 3 * Amax :=
          pivotPath2Abs_le fp Amax hAmax A hA σ hσpos hσA hσ hchoice 0 0
        have hcorner := flSchurCompl2_corner_bound fp hval A hA σ hσpos hchoice (hσ _ _)
        set anext := A ((0 : Fin (m' + 1)).succ.succ) (oneIdx (m' + 1)) with hanextdef
        have hanextabs : |anext| ≤ σ := hσ _ _
        have hanext2 : anext ^ 2 ≤ σ * Amax := by
          nlinarith [hanextabs, abs_nonneg anext, sq_abs anext, hσA, hσpos.le,
            mul_nonneg hσpos.le (sub_nonneg.mpr hσA)]
        have hstep : anext ^ 2 / (σ * bunchTridiagonalAlpha) ≤ Amax / bunchTridiagonalAlpha := by
          rw [div_le_div_iff₀ (mul_pos hσpos hα) hα]
          nlinarith [mul_le_mul_of_nonneg_right hanext2 hα.le]
        have hA22 : |A ((0 : Fin (m' + 1)).succ.succ) ((0 : Fin (m' + 1)).succ.succ)| ≤ Amax :=
          le_trans (hσ _ _) hσA
        have hKbound : |flSchurCompl2 (m' + 1) fp A 0 0|
            ≤ (1 + gamma fp 3) * (1 + 1 / bunchTridiagonalAlpha) * Amax := by
          have hγ0 : 0 ≤ 1 + gamma fp 3 := by have := gamma_nonneg fp hval; linarith
          calc |flSchurCompl2 (m' + 1) fp A 0 0|
              ≤ (1 + gamma fp 3) *
                  (|A ((0 : Fin (m' + 1)).succ.succ) ((0 : Fin (m' + 1)).succ.succ)|
                    + anext ^ 2 / (σ * bunchTridiagonalAlpha)) := hcorner
            _ ≤ (1 + gamma fp 3) * (Amax + Amax / bunchTridiagonalAlpha) :=
                mul_le_mul_of_nonneg_left (add_le_add hA22 hstep) hγ0
            _ = (1 + gamma fp 3) * (1 + 1 / bunchTridiagonalAlpha) * Amax := by ring
        calc pivotPath2Abs (m' + 1) fp A 0 0 + |flSchurCompl2 (m' + 1) fp A 0 0|
            ≤ (1 + fp.u) ^ 2 * (3 + bunchTridiagonalAlpha) / bunchTridiagonalAlpha ^ 3 * Amax
              + (1 + gamma fp 3) * (1 + 1 / bunchTridiagonalAlpha) * Amax := add_le_add hpp hKbound
          _ = ((1 + fp.u) ^ 2 * (3 + bunchTridiagonalAlpha) / bunchTridiagonalAlpha ^ 3
                + (1 + gamma fp 3) * (1 + 1 / bunchTridiagonalAlpha)) * Amax := by ring
          _ ≤ hfactorConst fp * Amax := mul_le_mul_of_nonneg_right (dom_two fp hval) hAmax
      · have hne : i.val ≠ 0 ∨ j.val ≠ 0 := by
          by_contra h; push_neg at h; exact hc ⟨h.1, h.2⟩
        rw [pivotPath2Abs_eq_zero_of_ne_corner fp A hA i j hne, zero_add]
        exact hIH i j

/-- **1×1 trailing term.**  The leading multiplier square plus the recursive Schur
    product entry (via `productEntry_consOne_split`) is `≤ c₀·Amax`: at the corner
    the multiplier square (`≤ C1x1·Amax`) adds the refreshed reduced corner
    (`≤ K·Amax`); everywhere else the multiplier vanishes by banding. -/
theorem trailingOne_le (fp : FPModel) (hval : gammaValid fp 3) (Amax : ℝ) (hAmax : 0 ≤ Amax) :
    ∀ {n : ℕ} (s : PivotSchedule n) (A : Fin (n + 1) → Fin (n + 1) → ℝ),
      IsSymTridiagonal (n + 1) A → A 0 0 ≠ 0 →
      (∃ σ : ℝ, 0 < σ ∧ σ ≤ Amax ∧ (∀ i j, |A i j| ≤ σ) ∧
        ∀ i : Fin n, BunchTridiagonalPivotChoice σ (A 0 0) (A i.succ 0) PivotSize.one) →
      (∀ i' j', higham11_4_bunchKaufmanProductEntry n
          (flMixedL fp s (flSchurCompl n fp A)) (flMixedD fp s (flSchurCompl n fp A)) i' j'
          ≤ hfactorConst fp * Amax) →
      ∀ i j : Fin n,
        |fp.fl_div (A i.succ 0) (A 0 0)| * |A 0 0| * |fp.fl_div (A j.succ 0) (A 0 0)|
          + higham11_4_bunchKaufmanProductEntry n
              (flMixedL fp s (flSchurCompl n fp A)) (flMixedD fp s (flSchurCompl n fp A)) i j
          ≤ hfactorConst fp * Amax := by
  intro n
  cases n with
  | zero => intro s A _ _ _ _ i; exact Fin.elim0 i
  | succ n' =>
      intro s A hA hA00 hdata hIH i j
      obtain ⟨σ, hσpos, hσA, hσ, hchoice⟩ := hdata
      have hα := bunch_tridiagonal_alpha_pos
      by_cases hc : i.val = 0 ∧ j.val = 0
      · obtain ⟨hi0, hj0⟩ := hc
        have hi : i = 0 := by rw [Fin.ext_iff, Fin.val_zero]; exact hi0
        have hj : j = 0 := by rw [Fin.ext_iff, Fin.val_zero]; exact hj0
        subst hi; subst hj
        rw [productEntry_head00 fp s (flSchurCompl (n' + 1) fp A)]
        have hrw : |fp.fl_div (A (0 : Fin (n' + 1)).succ 0) (A 0 0)| * |A 0 0|
              * |fp.fl_div (A (0 : Fin (n' + 1)).succ 0) (A 0 0)|
            = |fp.fl_div (A (0 : Fin (n' + 1)).succ 0) (A 0 0)| ^ 2 * |A 0 0| := by ring
        rw [hrw]
        have hmult : |fp.fl_div (A (0 : Fin (n' + 1)).succ 0) (A 0 0)| ^ 2 * |A 0 0|
            ≤ (1 + fp.u) ^ 2 / bunchTridiagonalAlpha * Amax := by
          have h := oneByOne_corner_mult_le fp σ (A 0 0) (A (0 : Fin (n' + 1)).succ 0) Amax
            (hchoice 0) hA00 hσA
          calc |fp.fl_div (A (0 : Fin (n' + 1)).succ 0) (A 0 0)| ^ 2 * |A 0 0|
              ≤ (1 + fp.u) ^ 2 * (Amax / bunchTridiagonalAlpha) := h
            _ = (1 + fp.u) ^ 2 / bunchTridiagonalAlpha * Amax := by ring
        have hKbound : |flSchurCompl (n' + 1) fp A 0 0|
            ≤ (1 + gamma fp 3) * (1 + 1 / bunchTridiagonalAlpha) * Amax := by
          have hγ0 : 0 ≤ 1 + gamma fp 3 := by have := gamma_nonneg fp hval; linarith
          have hcorner := flSchurCompl_corner_bound fp hval A hA σ Amax hσA (hchoice 0) hA00
          have hA11 : |A ((0 : Fin (n' + 1)).succ) ((0 : Fin (n' + 1)).succ)| ≤ Amax :=
            le_trans (hσ _ _) hσA
          calc |flSchurCompl (n' + 1) fp A 0 0|
              ≤ (1 + gamma fp 3) *
                  (|A ((0 : Fin (n' + 1)).succ) ((0 : Fin (n' + 1)).succ)|
                    + Amax / bunchTridiagonalAlpha) := hcorner
            _ ≤ (1 + gamma fp 3) * (Amax + Amax / bunchTridiagonalAlpha) :=
                mul_le_mul_of_nonneg_left (add_le_add hA11 le_rfl) hγ0
            _ = (1 + gamma fp 3) * (1 + 1 / bunchTridiagonalAlpha) * Amax := by ring
        calc |fp.fl_div (A (0 : Fin (n' + 1)).succ 0) (A 0 0)| ^ 2 * |A 0 0|
              + |flSchurCompl (n' + 1) fp A 0 0|
            ≤ (1 + fp.u) ^ 2 / bunchTridiagonalAlpha * Amax
              + (1 + gamma fp 3) * (1 + 1 / bunchTridiagonalAlpha) * Amax := add_le_add hmult hKbound
          _ = ((1 + fp.u) ^ 2 / bunchTridiagonalAlpha
                + (1 + gamma fp 3) * (1 + 1 / bunchTridiagonalAlpha)) * Amax := by ring
          _ ≤ hfactorConst fp * Amax := mul_le_mul_of_nonneg_right (dom_one fp hval) hAmax
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

/-- 1×1 pivot-row product entry `(0, j+1)` = `|A₀₀|·|fl(A_{j+1,0}/A₀₀)|`. -/
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

/-- 1×1 pivot-column product entry `(i+1, 0)` = `|fl(A_{i+1,0}/A₀₀)|·|A₀₀|`. -/
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

/-! ## Step F — the factor-norm entry bound by structural induction

Each product entry collects only `O(1)` nonzero contributions (banding), so the
dimension-independent `c₀ = hfactorConst fp` bounds them all. -/

theorem hfactor_bound (fp : FPModel) (hval : gammaValid fp 3) (Amax : ℝ) (hAmax : 0 ≤ Amax) :
    ∀ {n : ℕ} (s : PivotSchedule n) (A : Fin n → Fin n → ℝ),
      TriPivotData fp Amax s A →
      ∀ I J : Fin n,
        higham11_4_bunchKaufmanProductEntry n (flMixedL fp s A) (flMixedD fp s A) I J
          ≤ hfactorConst fp * Amax := by
  intro n s
  induction s with
  | nil => intro A _ I; exact Fin.elim0 I
  | @consOne n s ih =>
      intro A hdata I J
      rw [TriPivotData_consOne] at hdata
      obtain ⟨hA, hA00, ⟨σ, hσpos, hσA, hσ, hchoice⟩, hrec⟩ := hdata
      have hIH := ih (flSchurCompl n fp A) hrec
      have hblock : ∀ x : ℝ, |x| ≤ σ → |x| ≤ hfactorConst fp * Amax := fun x hx =>
        le_trans (le_trans hx hσA) (le_mul_of_one_le_left hAmax (dom_block fp hval))
      have hrowbound : ∀ j : Fin n, |A 0 0| * |fp.fl_div (A j.succ 0) (A 0 0)|
          ≤ hfactorConst fp * Amax := by
        intro j
        refine le_trans (fl_div_mul_abs_le fp (A j.succ 0) (A 0 0) hA00) ?_
        refine le_trans (mul_le_mul_of_nonneg_left (le_trans (hσ j.succ 0) hσA)
          (by have := fp.u_nonneg; linarith)) ?_
        exact mul_le_mul_of_nonneg_right (dom_row1 fp hval) hAmax
      rcases Fin.eq_zero_or_eq_succ I with rfl | ⟨i, rfl⟩
      · rcases Fin.eq_zero_or_eq_succ J with rfl | ⟨j, rfl⟩
        · rw [productEntry_head00 fp (s.consOne) A]; exact hblock _ (hσ 0 0)
        · rw [productEntry_consOne_0s]; exact hrowbound j
      · rcases Fin.eq_zero_or_eq_succ J with rfl | ⟨j, rfl⟩
        · rw [productEntry_consOne_s0, mul_comm]; exact hrowbound i
        · rw [productEntry_consOne_split fp s A i j]
          exact trailingOne_le fp hval Amax hAmax s A hA hA00
            ⟨σ, hσpos, hσA, hσ, hchoice⟩ hIH i j
  | @consTwo m s ih =>
      intro A hdata I J
      rw [TriPivotData_consTwo] at hdata
      obtain ⟨hA, ⟨σ, hσpos, hσA, hσ, hchoice⟩, hrec⟩ := hdata
      have hIH := ih (flSchurCompl2 m fp A) hrec
      have hblock : ∀ x : ℝ, |x| ≤ σ → |x| ≤ hfactorConst fp * Amax := fun x hx =>
        le_trans (le_trans hx hσA) (le_mul_of_one_le_left hAmax (dom_block fp hval))
      have hrc : ∀ z : ℝ, z ≤ 2 * (1 + fp.u) / bunchTridiagonalAlpha ^ 2 * Amax →
          z ≤ hfactorConst fp * Amax := fun z hz =>
        le_trans hz (mul_le_mul_of_nonneg_right (dom_rc fp hval) hAmax)
      rcases Fin.eq_zero_or_eq_succ I with rfl | ⟨I', rfl⟩
      · rcases Fin.eq_zero_or_eq_succ J with rfl | ⟨J', rfl⟩
        · rw [productEntry_consTwo_00]; exact hblock _ (hσ 0 0)
        · rcases Fin.eq_zero_or_eq_succ J' with rfl | ⟨j, rfl⟩
          · rw [productEntry_consTwo_01]; exact hblock _ (hσ 0 (oneIdx m))
          · rw [productEntry_consTwo_0t]
            exact hrc _ (pivotRowPathAbs_le fp Amax hAmax A hA σ hσpos hσA hσ hchoice 0 j)
      · rcases Fin.eq_zero_or_eq_succ I' with rfl | ⟨i, rfl⟩
        · rcases Fin.eq_zero_or_eq_succ J with rfl | ⟨J', rfl⟩
          · rw [productEntry_consTwo_10]; exact hblock _ (hσ (oneIdx m) 0)
          · rcases Fin.eq_zero_or_eq_succ J' with rfl | ⟨j, rfl⟩
            · rw [productEntry_consTwo_11]; exact hblock _ (hσ (oneIdx m) (oneIdx m))
            · rw [productEntry_consTwo_1t]
              exact hrc _ (pivotRowPathAbs_le fp Amax hAmax A hA σ hσpos hσA hσ hchoice 1 j)
        · rcases Fin.eq_zero_or_eq_succ J with rfl | ⟨J', rfl⟩
          · rw [productEntry_consTwo_t0]
            exact hrc _ (pivotColPathAbs_le fp Amax hAmax A hA σ hσpos hσA hσ hchoice i 0)
          · rcases Fin.eq_zero_or_eq_succ J' with rfl | ⟨j, rfl⟩
            · rw [productEntry_consTwo_t1]
              exact hrc _ (pivotColPathAbs_le fp Amax hAmax A hA σ hσpos hσA hσ hchoice i 1)
            · rw [productEntry_consTwo_trailing]
              exact trailingTwo_le fp hval Amax hAmax s A hA
                ⟨σ, hσpos, hσA, hσ, hchoice⟩ hIH i j

/-! ## Step Wrapper — the unconditional Theorem 11.7

Supplying `hfactor` from Step F (`hfactor_bound`) with `c₀ = hfactorConst fp`, the
factor-norm hypothesis of `higham11_7_bunch_tridiagonal_backward_error` is
discharged.  The remaining hypotheses are only the (11.5) `FlMixedPivots`/solve
data and the tridiagonal per-stage pivot data `TriPivotData` — no `hfactor`. -/

/-- **Theorem 11.7 (Bunch, symmetric tridiagonal), unconditional in `hfactor`.**
    For a symmetric tridiagonal `A` whose Algorithm-11.6 mixed-pivot run is recorded
    by the schedule `s` with per-stage pivot data `TriPivotData` (tridiagonal
    structure, accepted pivots, local scales `σ_ℓ ≤ Amax`), whose rounded path
    satisfies the (11.5) `FlMixedPivots` conditions, and whose solve step admits the
    (11.5) backward perturbation, Bunch's method produces

      `L̂D̂L̂ᵀ = A + ΔA₁`,  `(A + ΔA₂)x̂ = b`,  `|ΔAₖ i j| ≤ 20 n (1+c₀)·u·Amax`,

    with the dimension-independent factor-norm constant `c₀ = hfactorConst fp` and
    the linear-in-`n` coefficient `c = 20 n (1+c₀)` (Higham's `c·u·‖A‖_M`,
    Option A).  The tridiagonal factor-norm hypothesis `hfactor` of
    `higham11_7_bunch_tridiagonal_backward_error` is discharged here by Step F
    (`hfactor_bound`); it is no longer an assumption. -/
theorem higham11_7_bunch_tridiagonal_backward_error_unconditional
    (fp : FPModel) (hval : gammaValid fp 3)
    {n : ℕ} (A : Fin n → Fin n → ℝ) (b x_hat : Fin n → ℝ)
    (s : PivotSchedule n) (Amax cSolve cStage : ℝ)
    (hAmax : ∀ i j : Fin n, |A i j| ≤ Amax) (hAmax0 : 0 ≤ Amax)
    (hcS0 : 0 ≤ cSolve) (hcS40 : cSolve ≤ 40)
    (hcSt0 : 0 ≤ cStage) (hcSt5 : cStage ≤ 5)
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 100)
    (hpiv : FlMixedPivots fp cSolve cStage s A)
    (hdata : TriPivotData fp Amax s A)
    (hsolve : ∃ ΔA2 : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |ΔA2 i j| ≤ 20 * (n : ℝ) * (1 + hfactorConst fp) * fp.u * Amax) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + ΔA2 i j) * x_hat j = b i)) :
    ∃ ΔA1 ΔA2 : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |ΔA1 i j| ≤ 20 * (n : ℝ) * (1 + hfactorConst fp) * fp.u * Amax) ∧
      (∀ i j : Fin n, |ΔA2 i j| ≤ 20 * (n : ℝ) * (1 + hfactorConst fp) * fp.u * Amax) ∧
      (∀ i j : Fin n,
        (∑ k₁, ∑ k₂, flMixedL fp s A i k₁ * flMixedD fp s A k₁ k₂ * flMixedL fp s A j k₂)
          = A i j + ΔA1 i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + ΔA2 i j) * x_hat j = b i) :=
  higham11_7_bunch_tridiagonal_backward_error fp hval A b x_hat s Amax (hfactorConst fp)
    cSolve cStage hAmax hAmax0 (hfactorConst_nonneg fp hval) hcS0 hcS40 hcSt0 hcSt5 hsmall hpiv
    (hfactor_bound fp hval Amax hAmax0 s A hdata) hsolve

/-! ## Precise honesty status

**Fully derived here (no `sorry`/`admit`/`axiom`/`native_decide`; axioms
`[propext, Classical.choice, Quot.sound]` only):**
  * **Step F** (`hfactor_bound`): by structural induction on the `PivotSchedule`,
    every `|L̂||D̂||L̂ᵀ|` entry is `≤ c₀·Amax` with the dimension-independent
    `c₀ = hfactorConst fp`.  Each product entry collects only `O(1)` nonzero
    contributions — the banding lemmas kill every off-corner pivot path, and the
    product-entry recursion adds a corner path at most once, refreshing (not
    compounding) the reduced corner via `flSchurCompl2_corner_bound` /
    `flSchurCompl_corner_bound`.  The corner cancellations are the previously
    proven `pivotPath2Abs_corner_le`, `pivotRowColPathAbs_corner_le` (this file,
    via `corner_rowcol_le_core`), and `oneByOne_corner_mult_le` (via the 1×1
    acceptance test).
  * **Step Wrapper** (`higham11_7_bunch_tridiagonal_backward_error_unconditional`):
    `hfactor` is discharged by Step F, so Theorem 11.7 holds unconditionally in the
    factor-norm hypothesis, modulo only the (11.5) `FlMixedPivots`/solve data and
    the per-stage `TriPivotData` (tridiagonal structure + Algorithm-11.6 pivot
    choices + local scales `σ_ℓ ≤ Amax`, the sanctioned Step-G hypothesis family).

**Strength.**  `c₀ = hfactorConst fp` is a fixed constant (function of `u`, `α`,
`γ₃`); the coefficient `c = 20 n (1+c₀)` is Higham's `c·u·‖A‖_M`, the linear-in-`n`
Option-A landing. -/

end NumStability.Ch11Closure.HFactor
