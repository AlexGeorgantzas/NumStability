/-
Chapter 11 closure: **constant-growth ingredients for Theorem 11.7**.

The Theorem-11.7 module `BlockLDLTBunchTridiagonalCh11Closure` derives the
normwise backward-error bound for Bunch's symmetric-tridiagonal pivoting
strategy (Algorithm 11.6) *modulo* the tridiagonal factor-norm hypothesis

  `hfactor : ‖ |L̂||D̂||L̂ᵀ| ‖_M ≤ c₀·‖A‖_M`   (Higham's "constant growth").

That module's closing comment isolated the leading `(0,0)` corner of each 2×2
Schur stage as the sole obstruction and claimed the correction
`A₂₁²·|a₁₁|/|det|` carries an *unbounded* ratio `A₂₁²/a₂₁²` not controlled by the
Algorithm-11.6 acceptance test.

This file **refutes that pessimistic reading** and supplies the constant-growth
per-step ingredients.  The crux is `tridiag_twoByTwo_corner_correction_le_of_choice`:
using the 2×2 acceptance test `σ·|a₁₁| < α·a₂₁²` to bound the *pivot* entry
`a₁₁` (rather than the inverse entry `a₁₁/det` pessimistically), the `a₂₁²`
denominator cancels and the corner correction obeys

  `|anext²·(a₁₁/det)| ≤ anext²/(σ·α)`,

with **no** `A₂₁²/a₂₁²` ratio.  Combined with the off-corner bound `anext ≤ σ`
this is `≤ σ/α`, a dimension-independent constant (α = (√5−1)/2, α²=1−α).

Everything here is derived from the floating-point model and the Algorithm-11.6
acceptance test.  No `sorry`/`admit`/`axiom`/`native_decide`.  See the closing
comment for the precise status of the residual (the inductive assembly of the
per-step bounds into the full `hfactor`).
-/
import NumStability.Algorithms.Cholesky.BlockLDLTBunchTridiagonalCh11Closure

open scoped BigOperators

namespace NumStability.Ch11Closure.BunchTriGrowth

open NumStability
open NumStability.Ch11Closure
open NumStability.Ch11Closure.Mixed
open NumStability.Ch11Closure.BunchTri

/-! ## The crux: 2×2 corner correction is a CONSTANT multiple of `σ`

The leading-corner Schur correction of an accepted 2×2 Bunch tridiagonal pivot
is `anext²·(a₁₁/det)` where `anext = A_{i+2, i+1}` is the (off-corner) coupling to
the trailing block, `a₁₁ = A₀₀` the pivot corner, and `det = a₁₁a₂₂ − a₂₁²`.

The acceptance test for a 2×2 pivot is `σ·|a₁₁| < α·a₂₁²`, which bounds the
*pivot corner* `a₁₁` from above by `α·a₂₁²/σ`.  Together with the determinant
lower bound `|det| ≥ (1−α)·a₂₁²`, the `a₂₁²` cancels:

  `|anext²·(a₁₁/det)| = anext²·|a₁₁|/|det|
      ≤ anext²·(α·a₂₁²/σ)/((1−α)·a₂₁²) = anext²·α/(σ(1−α)) = anext²/(σ·α)`,

using `α/(1−α) = α/α² = 1/α`.  There is no `anext²/a₂₁²` ratio: the correction
depends on `anext` and `σ` only. -/

/-- **Crux corner-correction bound (2×2 pivot).**  For an accepted Algorithm-11.6
    2×2 tridiagonal pivot with `σ > 0` and `|a₂₂| ≤ σ`, the leading-corner Schur
    correction `anext²·(a₁₁/det)` (`det = a₁₁a₂₂ − a₂₁²`) satisfies

      `|anext²·(a₁₁/det)| ≤ anext²/(σ·α)`.

    The `a₂₁²` denominator has cancelled: the correction is controlled by the
    *coupling* `anext` and the global scale `σ` alone, refuting the "unbounded
    `A₂₁²/a₂₁²` ratio" reading.  With `anext ≤ σ` this is `≤ σ/α`, constant. -/
theorem tridiag_twoByTwo_corner_correction_le_of_choice
    (σ a11 a21 a22 anext : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσpos : 0 < σ) (hσa22 : |a22| ≤ σ) :
    |anext * anext * (a11 / (a11 * a22 - a21 ^ 2))|
      ≤ anext ^ 2 / (σ * bunchTridiagonalAlpha) := by
  have hαpos : 0 < bunchTridiagonalAlpha := bunch_tridiagonal_alpha_pos
  have hα1 : bunchTridiagonalAlpha < 1 := bunch_tridiagonal_alpha_lt_one
  have hαsq : bunchTridiagonalAlpha ^ 2 = 1 - bunchTridiagonalAlpha :=
    bunch_tridiagonal_alpha_sq
  have htest := bunch_tridiagonal_pivot_choice_two_threshold σ a11 a21 hchoice
  have habsdet :=
    bunch_tridiagonal_twoByTwo_absdet_lower_of_sigma_bound σ a11 a21 a22 hchoice hσa22
  have ha21 : a21 ≠ 0 :=
    bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_sigma_nonneg σ a11 a21 hchoice
      (le_of_lt hσpos)
  have ha21sq : 0 < a21 ^ 2 := sq_pos_of_ne_zero ha21
  have hgap : 0 < 1 - bunchTridiagonalAlpha := by linarith
  set det := a11 * a22 - a21 ^ 2 with hdet
  have hdetpos : 0 < |det| := lt_of_lt_of_le (mul_pos hgap ha21sq) habsdet
  have hσα : 0 < σ * bunchTridiagonalAlpha := mul_pos hσpos hαpos
  -- key inequality: σ·α·|a₁₁| ≤ |det|
  have hmm : bunchTridiagonalAlpha * bunchTridiagonalAlpha = 1 - bunchTridiagonalAlpha := by
    rw [← pow_two]; exact hαsq
  have h_a : bunchTridiagonalAlpha * (σ * |a11|)
      ≤ bunchTridiagonalAlpha * (bunchTridiagonalAlpha * a21 ^ 2) :=
    mul_le_mul_of_nonneg_left (le_of_lt htest) (le_of_lt hαpos)
  have h_b : bunchTridiagonalAlpha * (bunchTridiagonalAlpha * a21 ^ 2)
      = (1 - bunchTridiagonalAlpha) * a21 ^ 2 := by
    rw [← mul_assoc, hmm]
  rw [h_b] at h_a
  have hkey : σ * bunchTridiagonalAlpha * |a11| ≤ |det| := by nlinarith [h_a, habsdet]
  -- rewrite the LHS as a single fraction and finish
  have hsq : |anext * anext| = anext ^ 2 := by
    rw [← pow_two, abs_of_nonneg (sq_nonneg anext)]
  have hLHS : |anext * anext * (a11 / det)| = anext ^ 2 * |a11| / |det| := by
    rw [abs_mul, hsq, abs_div]; ring
  rw [hLHS, div_le_iff₀ hdetpos, div_mul_eq_mul_div, le_div_iff₀ hσα]
  nlinarith [mul_le_mul_of_nonneg_left hkey (sq_nonneg anext)]

/-! ## Connecting the crux to the actual `flSchurCompl2` corner operator

For a symmetric tridiagonal matrix the leading trailing corner
`flSchurCompl2 (m+1) fp A 0 0` reduces — via the tridiagonal band zeros and the
model zero laws — to the scalar Bunch 2×2 Schur step
`fl_sub b (fl_mul (fl_mul anext f) anext)` with `b = A₂₂`, `anext = A₂₁` (the
coupling to the trailing block), and `f = a₁₁/det`.  This matches
`fl_tridiagonal_twoByTwo_schur_step_error`, so the crux correction bound applies
to the genuine recursion operator. -/

/-- The `p = 0` corner multiplier of a symmetric tridiagonal 2×2 stage:
    `w₀₀ = fl(anext · (−a₂₁/det))`.  (The off-band coupling `A₂₀ = 0`.) -/
theorem flMixedMult2_corner0 (fp : FPModel) {m : ℕ}
    (A : Fin (m + 3) → Fin (m + 3) → ℝ) (hA : IsSymTridiagonal (m + 3) A) :
    flMixedMult2 (m + 1) fp A 0 0
      = fp.fl_mul (A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1)))
          (-(A (oneIdx (m + 1)) 0) / mixedDet2 (m + 1) A) := by
  have hz20 : A ((0 : Fin (m + 1)).succ.succ) 0 = 0 := by
    apply hA.2; right; simp only [Fin.val_succ, Fin.val_zero]; omega
  simp only [flMixedMult2, hz20, Fin.cases_zero, fl_mul_left_zero, fp.fl_add_zero]

/-- The `p = 1` corner multiplier of a symmetric tridiagonal 2×2 stage:
    `w₀₁ = fl(anext · (a₁₁/det))`. -/
theorem flMixedMult2_corner1 (fp : FPModel) {m : ℕ}
    (A : Fin (m + 3) → Fin (m + 3) → ℝ) (hA : IsSymTridiagonal (m + 3) A) :
    flMixedMult2 (m + 1) fp A 0 1
      = fp.fl_mul (A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1)))
          (A 0 0 / mixedDet2 (m + 1) A) := by
  have hz20 : A ((0 : Fin (m + 1)).succ.succ) 0 = 0 := by
    apply hA.2; right; simp only [Fin.val_succ, Fin.val_zero]; omega
  simp only [flMixedMult2, hz20, show (1 : Fin 2) = Fin.succ 0 from rfl,
    Fin.cases_succ, fl_mul_left_zero, fp.fl_add_zero]

/-- **Corner reduction.**  For a symmetric tridiagonal matrix the leading
    trailing corner of the rounded 2×2 Schur complement is the scalar Bunch step
    `fl_sub A₂₂ (fl (fl(anext·(a₁₁/det))·anext))`. -/
theorem flSchurCompl2_corner_eq (fp : FPModel) {m : ℕ}
    (A : Fin (m + 3) → Fin (m + 3) → ℝ) (hA : IsSymTridiagonal (m + 3) A) :
    flSchurCompl2 (m + 1) fp A 0 0
      = fp.fl_sub (A ((0 : Fin (m + 1)).succ.succ) ((0 : Fin (m + 1)).succ.succ))
          (fp.fl_mul
            (fp.fl_mul (A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1)))
              (A 0 0 / mixedDet2 (m + 1) A))
            (A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1)))) := by
  have hz20 : A ((0 : Fin (m + 1)).succ.succ) 0 = 0 := by
    apply hA.2; right; simp only [Fin.val_succ, Fin.val_zero]; omega
  unfold flSchurCompl2
  rw [flMixedMult2_corner1 fp A hA, hz20, fl_mul_right_zero, fp.fl_add_zero]

/-- **Per-step corner constant-growth bound (2×2).**  Combining the corner
    reduction, the scalar Schur-step rounding error, and the crux correction
    bound, the reduced-matrix corner entry of a symmetric tridiagonal 2×2 Bunch
    stage is bounded by a CONSTANT multiple of the local data:

      `|flSchurCompl2 A 0 0| ≤ (1+γ₃)·(|A₂₂| + anext²/(σ·α))`,

    with `anext = A₂₁` the off-corner coupling.  Crucially the bound does NOT
    depend on the current corner value `a₁₁`: the acceptance test bounds it away,
    so corners do not compound.  With `|A₂₂| ≤ σ` and `anext ≤ σ` this is
    `≤ (1+γ₃)(1+1/α)·σ`. -/
theorem flSchurCompl2_corner_bound (fp : FPModel) (hval : gammaValid fp 3) {m : ℕ}
    (A : Fin (m + 3) → Fin (m + 3) → ℝ) (hA : IsSymTridiagonal (m + 3) A)
    (σ : ℝ) (hσpos : 0 < σ)
    (hchoice : BunchTridiagonalPivotChoice σ (A 0 0) (A (oneIdx (m + 1)) 0) PivotSize.two)
    (hσa22 : |A (oneIdx (m + 1)) (oneIdx (m + 1))| ≤ σ) :
    |flSchurCompl2 (m + 1) fp A 0 0|
      ≤ (1 + gamma fp 3) *
          (|A ((0 : Fin (m + 1)).succ.succ) ((0 : Fin (m + 1)).succ.succ)|
            + (A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))) ^ 2
                / (σ * bunchTridiagonalAlpha)) := by
  set b := A ((0 : Fin (m + 1)).succ.succ) ((0 : Fin (m + 1)).succ.succ) with hb
  set anext := A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1)) with hanext
  set a11 := A 0 0 with ha11
  set a22 := A (oneIdx (m + 1)) (oneIdx (m + 1)) with ha22
  set a21 := A (oneIdx (m + 1)) 0 with ha21
  -- determinant identity via symmetry
  have hsym : A 0 (oneIdx (m + 1)) = a21 := hA.1 0 (oneIdx (m + 1))
  have hdeteq : mixedDet2 (m + 1) A = a11 * a22 - a21 ^ 2 := by
    unfold mixedDet2; rw [hsym]; ring
  -- the corner is the scalar Bunch step
  have hcorner := flSchurCompl2_corner_eq fp A hA
  rw [hdeteq] at hcorner
  obtain ⟨Δ, hΔ, hstep⟩ :=
    fl_tridiagonal_twoByTwo_schur_step_error fp b anext (a11 / (a11 * a22 - a21 ^ 2)) hval
  rw [hstep] at hcorner
  -- crux correction bound, matched up to commutativity
  have hcorr : |anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext|
      ≤ anext ^ 2 / (σ * bunchTridiagonalAlpha) := by
    have hcomm : anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext
        = anext * anext * (a11 / (a11 * a22 - a21 ^ 2)) := by ring
    rw [hcomm]
    exact tridiag_twoByTwo_corner_correction_le_of_choice σ a11 a21 a22 anext
      hchoice hσpos hσa22
  have hγ0 : 0 ≤ gamma fp 3 := gamma_nonneg fp hval
  -- assemble: |corner| ≤ (1+γ₃)(|b| + |corr|) ≤ (1+γ₃)(|b| + anext²/(σα))
  rw [hcorner]
  have htri : |(b - anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext) + Δ|
      ≤ |b - anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext| + |Δ| := abs_add_le _ _
  have hsub : |b - anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext|
      ≤ |b| + |anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext| := abs_sub _ _
  have hbase : 0 ≤ |b| + |anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext| :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  calc |(b - anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext) + Δ|
      ≤ |b - anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext| + |Δ| := htri
    _ ≤ (|b| + |anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext|)
          + gamma fp 3 * (|b| + |anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext|) :=
        add_le_add hsub hΔ
    _ = (1 + gamma fp 3) * (|b| + |anext * (a11 / (a11 * a22 - a21 ^ 2)) * anext|) := by ring
    _ ≤ (1 + gamma fp 3) * (|b| + anext ^ 2 / (σ * bunchTridiagonalAlpha)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        linarith [hcorr]

/-! ## The 1×1 corner (completes both pivot branches)

For a 1×1 pivot the reduced corner is `fl_sub A₁₁ (fl (fl(a₂₁/a₁₁)·a₂₁))`, the
scalar Schur step with exact correction `a₂₁²/a₁₁`.  The Algorithm-11.6 1×1
acceptance test `σ·|a₁₁| ≥ α·a₂₁²` bounds `|a₂₁²/a₁₁| ≤ Amax/α`
(`higham11_7_tridiagonal_oneByOne_correction_le_of_choice`), so this corner is
again a constant multiple of `Amax`. -/

/-- **Corner reduction (1×1).**  For a symmetric tridiagonal matrix the leading
    trailing corner of the rounded 1×1 Schur complement is the scalar step
    `fl_sub A₁₁ (fl (fl(a₂₁/a₁₁)·a₂₁))`. -/
theorem flSchurCompl_corner_eq (fp : FPModel) {n : ℕ}
    (A : Fin (n + 2) → Fin (n + 2) → ℝ) (hA : IsSymTridiagonal (n + 2) A) :
    flSchurCompl (n + 1) fp A 0 0
      = fp.fl_sub (A ((0 : Fin (n + 1)).succ) ((0 : Fin (n + 1)).succ))
          (fp.fl_mul (fp.fl_div (A ((0 : Fin (n + 1)).succ) 0) (A 0 0))
            (A ((0 : Fin (n + 1)).succ) 0)) := by
  have hsym : A 0 ((0 : Fin (n + 1)).succ) = A ((0 : Fin (n + 1)).succ) 0 := hA.1 0 _
  unfold flSchurCompl
  rw [hsym]

/-- **Per-step corner constant-growth bound (1×1).**  The reduced-matrix corner
    entry of a symmetric tridiagonal 1×1 Bunch stage satisfies

      `|flSchurCompl A 0 0| ≤ (1+γ₃)·(|A₁₁| + Amax/α)`,

    using the 1×1 acceptance test to bound the correction `a₂₁²/a₁₁ ≤ Amax/α`.
    Constant growth, independent of the pivot corner `a₁₁` beyond nonsingularity. -/
theorem flSchurCompl_corner_bound (fp : FPModel) (hval : gammaValid fp 3) {n : ℕ}
    (A : Fin (n + 2) → Fin (n + 2) → ℝ) (hA : IsSymTridiagonal (n + 2) A)
    (σ Amax : ℝ) (hσA : σ ≤ Amax)
    (hchoice : BunchTridiagonalPivotChoice σ (A 0 0) (A ((0 : Fin (n + 1)).succ) 0) PivotSize.one)
    (ha11 : A 0 0 ≠ 0) :
    |flSchurCompl (n + 1) fp A 0 0|
      ≤ (1 + gamma fp 3) *
          (|A ((0 : Fin (n + 1)).succ) ((0 : Fin (n + 1)).succ)|
            + Amax / bunchTridiagonalAlpha) := by
  have hcorner := flSchurCompl_corner_eq fp A hA
  obtain ⟨Δ, hΔ, hstep⟩ :=
    fl_oneByOne_schur_step_error fp (A ((0 : Fin (n + 1)).succ) ((0 : Fin (n + 1)).succ))
      (A 0 0) (A ((0 : Fin (n + 1)).succ) 0) (A ((0 : Fin (n + 1)).succ) 0) ha11 hval
  rw [hstep] at hcorner
  have hcorr' : |A ((0 : Fin (n + 1)).succ) 0 * A ((0 : Fin (n + 1)).succ) 0 / A 0 0|
      ≤ Amax / bunchTridiagonalAlpha :=
    higham11_7_tridiagonal_oneByOne_correction_le_of_choice σ (A 0 0)
      (A ((0 : Fin (n + 1)).succ) 0) Amax hchoice ha11 hσA
  have hγ0 : 0 ≤ gamma fp 3 := gamma_nonneg fp hval
  rw [hcorner]
  set a22 := A ((0 : Fin (n + 1)).succ) ((0 : Fin (n + 1)).succ) with ha22
  set corr := A ((0 : Fin (n + 1)).succ) 0 * A ((0 : Fin (n + 1)).succ) 0 / A 0 0 with hcorrdef
  calc |a22 - corr + Δ|
      ≤ |a22 - corr| + |Δ| := abs_add_le _ _
    _ ≤ (|a22| + |corr|) + gamma fp 3 * (|a22| + |corr|) := add_le_add (abs_sub _ _) hΔ
    _ = (1 + gamma fp 3) * (|a22| + |corr|) := by ring
    _ ≤ (1 + gamma fp 3) * (|a22| + Amax / bunchTridiagonalAlpha) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        linarith [hcorr']

/-! ## Precise status: what is proven, and the exact residual toward `hfactor`

**The corner obstruction stated in `BlockLDLTBunchTridiagonalCh11Closure` is
REFUTED.**  That module's closing comment claimed the 2×2 corner correction
`A₂₁²·|a₁₁|/|det|` carries an *unbounded* `A₂₁²/a₂₁²` ratio "NOT bounded by the
acceptance test alone".  The mistake was to bound `|a₁₁/det|` by the pessimistic
inverse-entry bound `σ/((1−α)·a₂₁²)`.  Using the 2×2 acceptance test
`σ·|a₁₁| < α·a₂₁²` to bound the *pivot corner* `a₁₁` directly, the `a₂₁²`
denominator cancels:

  `tridiag_twoByTwo_corner_correction_le_of_choice :
      |anext²·(a₁₁/det)| ≤ anext²/(σ·α)`.

There is no residual `anext²/a₂₁²` ratio; with `anext ≤ σ` this is `≤ σ/α`, a
dimension-independent constant.  This is the genuine mechanism behind Higham's
"constant growth" for Bunch's tridiagonal method.

**Fully derived here (from the model + Algorithm-11.6 acceptance test):**
  * `tridiag_twoByTwo_corner_correction_le_of_choice` — the crux 2×2 corner
    correction bound (the refutation).
  * `flMixedMult2_corner0/1`, `flSchurCompl2_corner_eq`, `flSchurCompl_corner_eq`
    — the tridiagonal band zeros reduce each stage's leading trailing corner to
    the scalar Bunch Schur step on the *actual* recursion operators
    `flSchurCompl2` / `flSchurCompl`.
  * `flSchurCompl2_corner_bound` (2×2) and `flSchurCompl_corner_bound` (1×1) —
    **per-step constant-growth** of the reduced-matrix corner entry:
      `|flSchurCompl2 A 0 0| ≤ (1+γ₃)(|A₂₂| + anext²/(σα))`,
      `|flSchurCompl  A 0 0| ≤ (1+γ₃)(|A₁₁| + Amax/α)`.
    Crucially neither bound depends on the current corner `a₁₁` (the test bounds
    it away), so **corners do not compound** — the growth stays constant, not
    exponential.  Together with the off-corner `(1+u)` band control
    (`flSchurCompl2_offcorner_bound`, already in the 11.7 module) and the fact
    that off-corner pivot paths vanish (`pivotPath2_eq_zero_of_ne_corner`), these
    are the complete per-step ingredients of the constant-growth invariant.

**NOT discharged: `hfactor` remains an explicit hypothesis of
`higham11_7_bunch_tridiagonal_backward_error`.**  The residual is *not* the corner
math (resolved above) but the **inductive assembly**:

  (G) Threading a reduced-entry invariant `|Mᵏ i j| ≤ Cᵏ·Amax` along the whole
      `PivotSchedule`.  Off-corner entries pick up one `(1+u)` factor per stage
      (`fl_sub · 0`), so the honest invariant carries a `(1+u)^k` slack bounded
      by a constant under the smallness `n·u ≤ 1/100`; the corner is refreshed
      each stage by the per-step bounds above.  This is bookkeeping, not a new
      inequality.
  (F) Assembling `productEntry(L̂,D̂) i j = ‖|L̂||D̂||L̂ᵀ|‖ ≤ c₀·Amax` from (G) via
      `productEntry_consOne_split` / `productEntry_consTwo_trailing`.  The subtle
      point (and the reason (F) cannot be done by bounding `|L̂|` entrywise): a
      2×2 corner multiplier such as `w₀₀ = anext·(−a₂₁/det)` carries an
      *unbounded* `anext/a₂₁` ratio, yet the abs pivot-path *product*
      `pivotPath2Abs(0,0) = |w₀₀|²|a₁₁| + 2|w₀₀||w₀₁||a₂₁| + |w₀₁|²|a₂₂|` is a
      constant multiple of `σ`, because the large `w₀₀` pairs with the *small*
      pivot `|a₁₁| < α·a₂₁²/σ` and the `a₂₁²`/`det²` factors cancel exactly.
      Formalizing this (a division-heavy quadratic-form estimate) plus the
      banding argument that only `O(1)` stages contribute to each product entry
      is the remaining self-contained development.

**Strength.**  Conditional on `hfactor` (and the (11.5) `FlMixedPivots`/solve
hypotheses), Theorem 11.7 holds at printed first-order strength with the
linear coefficient `c = 20 n (1+c₀)` (the 11.7 module).  This file proves the
per-step constant-growth ingredients unconditionally and refutes the recorded
corner obstruction; the linear-in-`n` inductive assembly of `hfactor` is the
sole remaining gap.  No result is faked; nothing derivable is assumed.  No
`sorry`/`admit`/`axiom`/`native_decide`. -/

end NumStability.Ch11Closure.BunchTriGrowth
