/-
Chapter 11 closure: **discharging the tridiagonal factor-norm hypothesis
`hfactor` of Theorem 11.7** (Bunch's symmetric-tridiagonal pivoting strategy,
Algorithm 11.6).

The Theorem-11.7 module `BlockLDLTBunchTridiagonalCh11Closure` derives the
normwise backward error *modulo* the "constant growth" hypothesis

  `hfactor : |L̂||D̂||L̂ᵀ| i j ≤ c₀·Amax`

and the sibling module `BunchTridiagonalGrowthCh11Closure` proved the crux
per-step corner ingredients (refuting the earlier "unbounded `A₂₁²/a₂₁²`
obstruction").  This file builds the remaining assembly:

  * the **corner quadratic-form bound** — the abs pivot-path product
    `pivotPath2Abs 0 0 = |w₀|²|a₁₁| + 2|w₀||w₁||a₂₁| + |w₁|²|a₂₂|` is a *constant*
    multiple of the local scale `σ`, even though the multiplier `w₀` can be large,
    because the large `w₀` pairs with the *small* accepted pivot `a₁₁` and the
    `a₂₁²/det²` factors cancel (Task F crux);
  * the **banding structure** — for a symmetric tridiagonal matrix only the first
    trailing block couples to the leading pivot block, so `pivotPath2Abs`,
    `pivotRowPathAbs`, `pivotColPathAbs` all vanish off the leading corner;

No `sorry`/`admit`/`axiom`/`native_decide`.  Everything is derived from the
floating-point model, the Algorithm-11.6 acceptance test, and the proven
ingredients of the growth module.
-/
import NumStability.Algorithms.Cholesky.BunchTridiagonalGrowthCh11Closure

open scoped BigOperators

namespace NumStability.Ch11Closure.BunchTriFactor

open NumStability
open NumStability.Ch11Closure
open NumStability.Ch11Closure.Mixed
open NumStability.Ch11Closure.BunchTri
open NumStability.Ch11Closure.BunchTriGrowth

/-! ## Warm-up: the Bunch tridiagonal parameter `α`

We reuse `bunchTridiagonalAlpha` (`= (√5−1)/2`) with `0 < α < 1` and `α² = 1−α`. -/

theorem alpha_pos : 0 < bunchTridiagonalAlpha := bunch_tridiagonal_alpha_pos
theorem alpha_lt_one : bunchTridiagonalAlpha < 1 := bunch_tridiagonal_alpha_lt_one

/-! ## The corner quadratic-form bound (crux of Task F)

The abs pivot-path product at the leading corner of a 2×2 stage is

  `Q = |w₀|²·|a₁₁| + 2·|w₀|·|w₁|·|a₂₁| + |w₁|²·|a₂₂|`,

with multipliers obeying the (rounding) bounds `|w₀|·|det| ≤ (1+u)·|anext|·|a₂₁|`
and `|w₁|·|det| ≤ (1+u)·|anext|·|a₁₁|`.  Although `|w₀|` and `|w₁|` are individually
*unbounded* (`|det|` can be tiny), the *product* `Q` is a constant multiple of the
local scale `σ`, because:

  * the large `|w₀|` (carrying `|a₂₁|/|det|`) pairs with the *small* accepted pivot
    `|a₁₁| ≤ α·a₂₁²/σ` and the `a₂₁²/det²` factors cancel;
  * `|det| ≥ (1−α)·a₂₁² = α²·a₂₁²` (accepted-2×2 determinant lower bound).

The clean output is `Q ≤ (1+u)²·(3+α)·σ / α³`.  This is a pure real-arithmetic
fact; the floating-point content lives entirely in the `hw0D`/`hw1D` multiplier
bounds and the acceptance test `htest`, both supplied at the call site. -/

/-- Monotonicity of squaring on the nonnegatives (local helper). -/
private theorem sq_le_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  rw [pow_two, pow_two]; exact mul_self_le_mul_self ha hab

/-- **Corner quadratic-form core.**  A division-free real-arithmetic statement:
    from the accepted-pivot data and the two multiplier bounds, the abs pivot-path
    quadratic form is `≤ (1+u)²·(3+α)·σ/α³` — a constant multiple of `σ` with no
    residual `a₂₁²/det²` ratio. -/
theorem corner_quadform_core
    (u σ a11abs a21abs a22abs anextabs w0 w1 D : ℝ)
    (hu : 0 ≤ u) (hσ : 0 < σ)
    (ha11abs : 0 ≤ a11abs) (ha21abs : 0 < a21abs)
    (ha22abs : 0 ≤ a22abs) (hanextabs : 0 ≤ anextabs)
    (hw0 : 0 ≤ w0) (hw1 : 0 ≤ w1)
    (hDpos : 0 < D)
    (hDlow : bunchTridiagonalAlpha ^ 2 * a21abs ^ 2 ≤ D)
    (htest : σ * a11abs ≤ bunchTridiagonalAlpha * a21abs ^ 2)
    (ha22 : a22abs ≤ σ) (hanext : anextabs ≤ σ)
    (hw0D : w0 * D ≤ (1 + u) * anextabs * a21abs)
    (hw1D : w1 * D ≤ (1 + u) * anextabs * a11abs) :
    w0 ^ 2 * a11abs + 2 * w0 * w1 * a21abs + w1 ^ 2 * a22abs
      ≤ (1 + u) ^ 2 * (3 + bunchTridiagonalAlpha) * σ / bunchTridiagonalAlpha ^ 3 := by
  have hα : 0 < bunchTridiagonalAlpha := bunch_tridiagonal_alpha_pos
  have hα1 : bunchTridiagonalAlpha < 1 := bunch_tridiagonal_alpha_lt_one
  set α := bunchTridiagonalAlpha with hαdef
  have h1u : (0 : ℝ) ≤ 1 + u := by linarith
  have hσ0 : 0 ≤ σ := le_of_lt hσ
  have hw0Dnn : 0 ≤ w0 * D := mul_nonneg hw0 hDpos.le
  have hw1Dnn : 0 ≤ w1 * D := mul_nonneg hw1 hDpos.le
  have hP0nn : 0 ≤ (1 + u) * anextabs * a21abs :=
    mul_nonneg (mul_nonneg h1u hanextabs) ha21abs.le
  have hR0nn : 0 ≤ (1 + u) * anextabs * a11abs :=
    mul_nonneg (mul_nonneg h1u hanextabs) ha11abs
  -- squared / cross multiplier bounds (clearing `D`)
  have e0 : (w0 * D) ^ 2 ≤ ((1 + u) * anextabs * a21abs) ^ 2 := sq_le_sq_of_nonneg hw0Dnn hw0D
  have e1 : (w1 * D) ^ 2 ≤ ((1 + u) * anextabs * a11abs) ^ 2 := sq_le_sq_of_nonneg hw1Dnn hw1D
  have ecross : (w0 * D) * (w1 * D)
      ≤ ((1 + u) * anextabs * a21abs) * ((1 + u) * anextabs * a11abs) :=
    mul_le_mul hw0D hw1D hw1Dnn hP0nn
  -- STEP (i): `Q · D² ≤ N` (via three per-term products; no heavy nlinarith)
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
  -- reduced polynomial (after cancelling the common `a₂₁²/det²`) — explicit, no nlinarith
  have hanextsq : anextabs ^ 2 ≤ σ ^ 2 := sq_le_sq_of_nonneg hanextabs hanext
  have hlhs : 0 ≤ σ * a11abs := mul_nonneg hσ0 ha11abs
  have htestsq : (σ * a11abs) ^ 2 ≤ (α * a21abs ^ 2) ^ 2 := sq_le_sq_of_nonneg hlhs htest
  -- term 1: `|w₀|²|a₁₁|` after cancellation
  have t1 : anextabs ^ 2 * (3 * a21abs ^ 2 * a11abs) ≤ 3 * σ * α * a21abs ^ 4 := by
    have hXnn : 0 ≤ 3 * a21abs ^ 2 * a11abs :=
      mul_nonneg (by positivity : (0:ℝ) ≤ 3 * a21abs ^ 2) ha11abs
    have stepA : anextabs ^ 2 * (3 * a21abs ^ 2 * a11abs)
        ≤ σ ^ 2 * (3 * a21abs ^ 2 * a11abs) := mul_le_mul_of_nonneg_right hanextsq hXnn
    have hσa : 3 * a21abs ^ 2 * (σ * (σ * a11abs)) ≤ 3 * a21abs ^ 2 * (σ * (α * a21abs ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htest hσ0)
        (by positivity : (0:ℝ) ≤ 3 * a21abs ^ 2)
    calc anextabs ^ 2 * (3 * a21abs ^ 2 * a11abs)
        ≤ σ ^ 2 * (3 * a21abs ^ 2 * a11abs) := stepA
      _ = 3 * a21abs ^ 2 * (σ * (σ * a11abs)) := by ring
      _ ≤ 3 * a21abs ^ 2 * (σ * (α * a21abs ^ 2)) := hσa
      _ = 3 * σ * α * a21abs ^ 4 := by ring
  -- term 3: `|w₁|²|a₂₂|` after cancellation
  have t2 : anextabs ^ 2 * (a11abs ^ 2 * a22abs) ≤ α ^ 2 * σ * a21abs ^ 4 := by
    have hYnn : 0 ≤ a11abs ^ 2 * a22abs := mul_nonneg (sq_nonneg _) ha22abs
    have stepA' : anextabs ^ 2 * (a11abs ^ 2 * a22abs)
        ≤ σ ^ 2 * (a11abs ^ 2 * a22abs) := mul_le_mul_of_nonneg_right hanextsq hYnn
    have hstep1 : a22abs * (σ * a11abs) ^ 2 ≤ a22abs * (α * a21abs ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_left htestsq ha22abs
    have hstep2 : a22abs * (α ^ 2 * a21abs ^ 4) ≤ σ * (α ^ 2 * a21abs ^ 4) :=
      mul_le_mul_of_nonneg_right ha22 (by positivity : (0:ℝ) ≤ α ^ 2 * a21abs ^ 4)
    calc anextabs ^ 2 * (a11abs ^ 2 * a22abs)
        ≤ σ ^ 2 * (a11abs ^ 2 * a22abs) := stepA'
      _ = a22abs * (σ * a11abs) ^ 2 := by ring
      _ ≤ a22abs * (α * a21abs ^ 2) ^ 2 := hstep1
      _ = a22abs * (α ^ 2 * a21abs ^ 4) := by ring
      _ ≤ σ * (α ^ 2 * a21abs ^ 4) := hstep2
      _ = α ^ 2 * σ * a21abs ^ 4 := by ring
  have hred :
      anextabs ^ 2 * (3 * a21abs ^ 2 * a11abs + a11abs ^ 2 * a22abs)
        ≤ (3 + α) * σ * α * a21abs ^ 4 := by
    have hdist : anextabs ^ 2 * (3 * a21abs ^ 2 * a11abs + a11abs ^ 2 * a22abs)
        = anextabs ^ 2 * (3 * a21abs ^ 2 * a11abs) + anextabs ^ 2 * (a11abs ^ 2 * a22abs) := by
      ring
    have hrhs : (3 + α) * σ * α * a21abs ^ 4
        = 3 * σ * α * a21abs ^ 4 + α ^ 2 * σ * a21abs ^ 4 := by ring
    rw [hdist, hrhs]; exact add_le_add t1 t2
  -- STEP (iii): assemble `N/D² ≤ (1+u)²(3+α)σ/α³`
  have hfac : (0 : ℝ) ≤ (1 + u) ^ 2 * α ^ 3 := by positivity
  have hpoly : N * α ^ 3 ≤ (1 + u) ^ 2 * (3 + α) * σ * (α ^ 2 * a21abs ^ 2) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hred hfac
    have eqL : (1 + u) ^ 2 * α ^ 3
          * (anextabs ^ 2 * (3 * a21abs ^ 2 * a11abs + a11abs ^ 2 * a22abs))
        = N * α ^ 3 := by rw [hN]; ring
    have eqR : (1 + u) ^ 2 * α ^ 3 * ((3 + α) * σ * α * a21abs ^ 4)
        = (1 + u) ^ 2 * (3 + α) * σ * (α ^ 2 * a21abs ^ 2) ^ 2 := by ring
    rw [eqL, eqR] at h; exact h
  have hBnn : 0 ≤ (1 + u) ^ 2 * (3 + α) * σ := by positivity
  have hsqle : (α ^ 2 * a21abs ^ 2) ^ 2 ≤ D ^ 2 :=
    sq_le_sq_of_nonneg (by positivity : (0:ℝ) ≤ α ^ 2 * a21abs ^ 2) hDlow
  have hBD : (1 + u) ^ 2 * (3 + α) * σ * (α ^ 2 * a21abs ^ 2) ^ 2
      ≤ (1 + u) ^ 2 * (3 + α) * σ * D ^ 2 :=
    mul_le_mul_of_nonneg_left hsqle hBnn
  have hNα : N * α ^ 3 ≤ (1 + u) ^ 2 * (3 + α) * σ * D ^ 2 := le_trans hpoly hBD
  have hα3pos : (0 : ℝ) < α ^ 3 := by positivity
  refine (le_div_iff₀ hα3pos).mpr ?_
  calc (w0 ^ 2 * a11abs + 2 * w0 * w1 * a21abs + w1 ^ 2 * a22abs) * α ^ 3
      ≤ (N / D ^ 2) * α ^ 3 := mul_le_mul_of_nonneg_right stepii (by positivity)
    _ = N * α ^ 3 / D ^ 2 := by ring
    _ ≤ (1 + u) ^ 2 * (3 + α) * σ := (div_le_iff₀ hD2pos).mpr hNα

/-! ## Corner pivot-row / pivot-column bounds (linear cancellation)

The corner pivot-*row* and pivot-*column* abs paths are *linear* in the
multipliers (one factor of `w`), yet use the identical acceptance-test
cancellation as the quadratic corner form: a large multiplier (carrying `1/det`)
is tamed by the small accepted pivot `|a₁₁| ≤ α a₂₁²/σ` against `|det| ≥ α² a₂₁²`.
Both are constant multiples of `σ`. -/

/-- From `p·β·D ≤ (1+u)σ·D` (`β, D > 0`) conclude `p ≤ (1+u)σ/β`. -/
private theorem le_div_of_mul_D_le {p β D u σ : ℝ} (hβ : 0 < β) (hD : 0 < D)
    (h : p * β * D ≤ (1 + u) * σ * D) : p ≤ (1 + u) * σ / β := by
  rw [le_div_iff₀ hβ]; exact le_of_mul_le_mul_right h hD

/-- **Corner pivot-row / pivot-column core.**  With the same accepted-pivot data as
    `corner_quadform_core` (plus the off-corner bound `|a₂₁| ≤ σ`), the two linear
    corner paths are constant multiples of `σ`:

      `|a₁₁||w₀| + |a₂₁||w₁| ≤ 2(1+u)σ/α`,   `|a₂₁||w₀| + |a₂₂||w₁| ≤ 2(1+u)σ/α²`.

    These are the pivot-row (`pivotRowPathAbs p 0`) and pivot-column
    (`pivotColPathAbs 0 q`) contributions at the leading corner. -/
theorem corner_rowcol_le_core
    (u σ a11abs a21abs a22abs anextabs w0 w1 D : ℝ)
    (hu : 0 ≤ u) (hσ : 0 < σ)
    (ha11abs : 0 ≤ a11abs) (ha21abs : 0 < a21abs)
    (ha22abs : 0 ≤ a22abs) (hanextabs : 0 ≤ anextabs)
    (hDpos : 0 < D)
    (hDlow : bunchTridiagonalAlpha ^ 2 * a21abs ^ 2 ≤ D)
    (htest : σ * a11abs ≤ bunchTridiagonalAlpha * a21abs ^ 2)
    (ha21 : a21abs ≤ σ) (ha22 : a22abs ≤ σ) (hanext : anextabs ≤ σ)
    (hw0D : w0 * D ≤ (1 + u) * anextabs * a21abs)
    (hw1D : w1 * D ≤ (1 + u) * anextabs * a11abs) :
    a11abs * w0 + a21abs * w1 ≤ 2 * (1 + u) * σ / bunchTridiagonalAlpha
      ∧ a21abs * w0 + a22abs * w1 ≤ 2 * (1 + u) * σ / bunchTridiagonalAlpha ^ 2 := by
  have hα : 0 < bunchTridiagonalAlpha := bunch_tridiagonal_alpha_pos
  have hα1 : bunchTridiagonalAlpha < 1 := bunch_tridiagonal_alpha_lt_one
  set α := bunchTridiagonalAlpha with hαdef
  have hα2 : 0 < α ^ 2 := by positivity
  have h1u : (0 : ℝ) ≤ 1 + u := by linarith
  have hσ0 : 0 ≤ σ := hσ.le
  have hαa11 : 0 ≤ α * a11abs := mul_nonneg hα.le ha11abs
  have hαa21 : 0 ≤ α * a21abs := mul_nonneg hα.le ha21abs.le
  have hαa22 : 0 ≤ α * a22abs := mul_nonneg hα.le ha22abs
  -- three "need" inequalities (after clearing `D`), all instances of the cancellation
  have need_ab : (1 + u) * α * a11abs * anextabs * a21abs ≤ (1 + u) * σ * D := by
    have c1 : a11abs * anextabs ≤ α * a21abs ^ 2 :=
      le_trans (mul_le_mul_of_nonneg_left hanext ha11abs) (by rw [mul_comm]; exact htest)
    have c2 : (1 + u) * α * a11abs * anextabs * a21abs
        ≤ (1 + u) * α * a21abs * (α * a21abs ^ 2) := by
      calc (1 + u) * α * a11abs * anextabs * a21abs
          = ((1 + u) * α * a21abs) * (a11abs * anextabs) := by ring
        _ ≤ ((1 + u) * α * a21abs) * (α * a21abs ^ 2) :=
            mul_le_mul_of_nonneg_left c1 (mul_nonneg (mul_nonneg h1u hα.le) ha21abs.le)
        _ = (1 + u) * α * a21abs * (α * a21abs ^ 2) := by ring
    have c3 : (1 + u) * α * a21abs * (α * a21abs ^ 2) ≤ (1 + u) * σ * (α ^ 2 * a21abs ^ 2) := by
      calc (1 + u) * α * a21abs * (α * a21abs ^ 2)
          = ((1 + u) * α ^ 2 * a21abs ^ 2) * a21abs := by ring
        _ ≤ ((1 + u) * α ^ 2 * a21abs ^ 2) * σ :=
            mul_le_mul_of_nonneg_left ha21
              (mul_nonneg (mul_nonneg h1u hα2.le) (sq_nonneg _))
        _ = (1 + u) * σ * (α ^ 2 * a21abs ^ 2) := by ring
    have c4 : (1 + u) * σ * (α ^ 2 * a21abs ^ 2) ≤ (1 + u) * σ * D :=
      mul_le_mul_of_nonneg_left hDlow (mul_nonneg h1u hσ0)
    exact le_trans (le_trans c2 c3) c4
  have need_c : (1 + u) * α ^ 2 * anextabs * a21abs ^ 2 ≤ (1 + u) * σ * D := by
    have c1 : (1 + u) * α ^ 2 * anextabs * a21abs ^ 2 ≤ (1 + u) * α ^ 2 * σ * a21abs ^ 2 := by
      calc (1 + u) * α ^ 2 * anextabs * a21abs ^ 2
          = ((1 + u) * α ^ 2 * a21abs ^ 2) * anextabs := by ring
        _ ≤ ((1 + u) * α ^ 2 * a21abs ^ 2) * σ :=
            mul_le_mul_of_nonneg_left hanext
              (mul_nonneg (mul_nonneg h1u hα2.le) (sq_nonneg _))
        _ = (1 + u) * α ^ 2 * σ * a21abs ^ 2 := by ring
    have c2 : (1 + u) * α ^ 2 * σ * a21abs ^ 2 ≤ (1 + u) * σ * D := by
      calc (1 + u) * α ^ 2 * σ * a21abs ^ 2 = ((1 + u) * σ) * (α ^ 2 * a21abs ^ 2) := by ring
        _ ≤ ((1 + u) * σ) * D := mul_le_mul_of_nonneg_left hDlow (mul_nonneg h1u hσ0)
        _ = (1 + u) * σ * D := by ring
    exact le_trans c1 c2
  have need_d : (1 + u) * α * a22abs * anextabs * a11abs ≤ (1 + u) * σ * D := by
    have c1 : (1 + u) * α * a22abs * anextabs * a11abs ≤ (1 + u) * α * a11abs * (σ * σ) := by
      calc (1 + u) * α * a22abs * anextabs * a11abs
          = ((1 + u) * α * a11abs) * (a22abs * anextabs) := by ring
        _ ≤ ((1 + u) * α * a11abs) * (σ * σ) :=
            mul_le_mul_of_nonneg_left (mul_le_mul ha22 hanext hanextabs hσ0)
              (mul_nonneg (mul_nonneg h1u hα.le) ha11abs)
    have c2 : (1 + u) * α * a11abs * (σ * σ) ≤ (1 + u) * σ * D := by
      calc (1 + u) * α * a11abs * (σ * σ) = ((1 + u) * α * σ) * (σ * a11abs) := by ring
        _ ≤ ((1 + u) * α * σ) * (α * a21abs ^ 2) :=
            mul_le_mul_of_nonneg_left htest (mul_nonneg (mul_nonneg h1u hα.le) hσ0)
        _ = ((1 + u) * σ) * (α ^ 2 * a21abs ^ 2) := by ring
        _ ≤ ((1 + u) * σ) * D := mul_le_mul_of_nonneg_left hDlow (mul_nonneg h1u hσ0)
        _ = (1 + u) * σ * D := by ring
    exact le_trans c1 c2
  -- the four term bounds
  have ta : a11abs * w0 ≤ (1 + u) * σ / α := by
    refine le_div_of_mul_D_le (D := D) hα hDpos ?_
    calc a11abs * w0 * α * D = α * a11abs * (w0 * D) := by ring
      _ ≤ α * a11abs * ((1 + u) * anextabs * a21abs) :=
          mul_le_mul_of_nonneg_left hw0D hαa11
      _ = (1 + u) * α * a11abs * anextabs * a21abs := by ring
      _ ≤ (1 + u) * σ * D := need_ab
  have tb : a21abs * w1 ≤ (1 + u) * σ / α := by
    refine le_div_of_mul_D_le (D := D) hα hDpos ?_
    calc a21abs * w1 * α * D = α * a21abs * (w1 * D) := by ring
      _ ≤ α * a21abs * ((1 + u) * anextabs * a11abs) :=
          mul_le_mul_of_nonneg_left hw1D hαa21
      _ = (1 + u) * α * a11abs * anextabs * a21abs := by ring
      _ ≤ (1 + u) * σ * D := need_ab
  have tc : a21abs * w0 ≤ (1 + u) * σ / α ^ 2 := by
    refine le_div_of_mul_D_le (D := D) hα2 hDpos ?_
    calc a21abs * w0 * α ^ 2 * D = α ^ 2 * a21abs * (w0 * D) := by ring
      _ ≤ α ^ 2 * a21abs * ((1 + u) * anextabs * a21abs) :=
          mul_le_mul_of_nonneg_left hw0D (mul_nonneg hα2.le ha21abs.le)
      _ = (1 + u) * α ^ 2 * anextabs * a21abs ^ 2 := by ring
      _ ≤ (1 + u) * σ * D := need_c
  have td : a22abs * w1 ≤ (1 + u) * σ / α := by
    refine le_div_of_mul_D_le (D := D) hα hDpos ?_
    calc a22abs * w1 * α * D = α * a22abs * (w1 * D) := by ring
      _ ≤ α * a22abs * ((1 + u) * anextabs * a11abs) :=
          mul_le_mul_of_nonneg_left hw1D hαa22
      _ = (1 + u) * α * a22abs * anextabs * a11abs := by ring
      _ ≤ (1 + u) * σ * D := need_d
  have relax : (1 + u) * σ / α ≤ (1 + u) * σ / α ^ 2 := by
    have h1uσ : 0 < (1 + u) * σ := mul_pos (by linarith) hσ
    have hα2le : α ^ 2 ≤ α := by nlinarith [hα, hα1]
    exact (div_le_div_iff_of_pos_left h1uσ hα hα2).mpr hα2le
  refine ⟨?_, ?_⟩
  · calc a11abs * w0 + a21abs * w1 ≤ (1 + u) * σ / α + (1 + u) * σ / α := add_le_add ta tb
      _ = 2 * (1 + u) * σ / α := by ring
  · calc a21abs * w0 + a22abs * w1 ≤ (1 + u) * σ / α ^ 2 + (1 + u) * σ / α ^ 2 :=
          add_le_add tc (le_trans td relax)
      _ = 2 * (1 + u) * σ / α ^ 2 := by ring

/-! ## Banding: the abs pivot paths vanish off the leading corner

For a symmetric tridiagonal matrix only the *first* trailing block couples to the
leading pivot block (`flMixedMult2_eq_zero_of_tridiag`), so every abs pivot path
`pivotPath2Abs`, `pivotRowPathAbs`, `pivotColPathAbs` vanishes away from the
leading corner.  This is the structural reason each `|L̂||D̂||L̂ᵀ|` entry collects
only `O(1)` per-stage contributions (dimension-independent `c₀`). -/

/-- The abs 2×2 pivot path vanishes unless both trailing indices are the corner. -/
theorem pivotPath2Abs_eq_zero_of_ne_corner (fp : FPModel) {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) (hA : IsSymTridiagonal (m + 2) A)
    (i j : Fin m) (hne : i.val ≠ 0 ∨ j.val ≠ 0) :
    pivotPath2Abs m fp A i j = 0 := by
  rw [pivotPath2Abs]
  rcases hne with hi | hj
  · have h0 := flMixedMult2_eq_zero_of_tridiag fp A hA i (by omega)
    simp only [Fin.sum_univ_two, h0.1, h0.2, abs_zero, zero_mul, add_zero]
  · have h0 := flMixedMult2_eq_zero_of_tridiag fp A hA j (by omega)
    simp only [Fin.sum_univ_two, h0.1, h0.2, abs_zero, mul_zero, add_zero]

/-- The abs pivot-row path vanishes unless the trailing index is the corner. -/
theorem pivotRowPathAbs_eq_zero_of_ne_corner (fp : FPModel) {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) (hA : IsSymTridiagonal (m + 2) A)
    (p : Fin 2) (j : Fin m) (hj : j.val ≠ 0) :
    pivotRowPathAbs m fp A p j = 0 := by
  rw [pivotRowPathAbs]
  have h0 := flMixedMult2_eq_zero_of_tridiag fp A hA j (by omega)
  simp only [Fin.sum_univ_two, h0.1, h0.2, abs_zero, mul_zero, add_zero]

/-- The abs pivot-column path vanishes unless the trailing index is the corner. -/
theorem pivotColPathAbs_eq_zero_of_ne_corner (fp : FPModel) {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) (hA : IsSymTridiagonal (m + 2) A)
    (i : Fin m) (q : Fin 2) (hi : i.val ≠ 0) :
    pivotColPathAbs m fp A i q = 0 := by
  rw [pivotColPathAbs]
  have h0 := flMixedMult2_eq_zero_of_tridiag fp A hA i (by omega)
  simp only [Fin.sum_univ_two, h0.1, h0.2, abs_zero, zero_mul, add_zero]

/-! ## The corner instantiation: `pivotPath2Abs 0 0 ≤ const·σ`

Feeding the actual `flMixedMult2` corner multipliers and the Algorithm-11.6
determinant/threshold facts into `corner_quadform_core`, the leading corner of a
symmetric tridiagonal 2×2 stage obeys the constant-growth pivot-path bound. -/

/-- **Corner abs pivot-path bound.**  For a symmetric tridiagonal `A` with an
    accepted 2×2 Algorithm-11.6 pivot at the leading corner and local scale `σ`
    (`|a₂₂| ≤ σ`, `|anext| ≤ σ`), the leading-corner abs pivot path is bounded by a
    *constant* multiple of `σ`:

      `pivotPath2Abs 0 0 ≤ (1+u)²·(3+α)·σ / α³`.

    The individually-unbounded corner multipliers `w₀, w₁` do not appear on the
    right: the acceptance test and the determinant lower bound cancel the
    `a₂₁²/det²` ratios exactly (see `corner_quadform_core`). -/
theorem pivotPath2Abs_corner_le (fp : FPModel) {m : ℕ}
    (A : Fin (m + 3) → Fin (m + 3) → ℝ) (hA : IsSymTridiagonal (m + 3) A)
    (σ : ℝ) (hσpos : 0 < σ)
    (hchoice : BunchTridiagonalPivotChoice σ (A 0 0) (A (oneIdx (m + 1)) 0) PivotSize.two)
    (hσa22 : |A (oneIdx (m + 1)) (oneIdx (m + 1))| ≤ σ)
    (hσanext : |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))| ≤ σ) :
    pivotPath2Abs (m + 1) fp A 0 0
      ≤ (1 + fp.u) ^ 2 * (3 + bunchTridiagonalAlpha) * σ / bunchTridiagonalAlpha ^ 3 := by
  have hu0 := fp.u_nonneg
  have hα1 : bunchTridiagonalAlpha < 1 := bunch_tridiagonal_alpha_lt_one
  have hgap : 0 < 1 - bunchTridiagonalAlpha := by linarith
  have hsym : A 0 (oneIdx (m + 1)) = A (oneIdx (m + 1)) 0 := hA.1 0 (oneIdx (m + 1))
  have ha21ne : A (oneIdx (m + 1)) 0 ≠ 0 :=
    bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_sigma_nonneg σ (A 0 0)
      (A (oneIdx (m + 1)) 0) hchoice hσpos.le
  have ha21sq : 0 < A (oneIdx (m + 1)) 0 ^ 2 := sq_pos_of_ne_zero ha21ne
  -- determinant identity and lower bound
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
  -- multiplier rounding bounds (clearing `det`)
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
  -- expand `pivotPath2Abs` at the corner
  have hexpand : pivotPath2Abs (m + 1) fp A 0 0
      = |flMixedMult2 (m + 1) fp A 0 0| ^ 2 * |A 0 0|
        + 2 * |flMixedMult2 (m + 1) fp A 0 0| * |flMixedMult2 (m + 1) fp A 0 1|
            * |A (oneIdx (m + 1)) 0|
        + |flMixedMult2 (m + 1) fp A 0 1| ^ 2 * |A (oneIdx (m + 1)) (oneIdx (m + 1))| := by
    rw [pivotPath2Abs, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [leadingTwoBlock_apply, embedTwo_zero, embedTwo_one_eq]
    rw [hsym]; ring
  rw [hexpand]
  exact corner_quadform_core fp.u σ |A 0 0| |A (oneIdx (m + 1)) 0|
    |A (oneIdx (m + 1)) (oneIdx (m + 1))|
    |A ((0 : Fin (m + 1)).succ.succ) (oneIdx (m + 1))|
    |flMixedMult2 (m + 1) fp A 0 0| |flMixedMult2 (m + 1) fp A 0 1|
    |mixedDet2 (m + 1) A|
    hu0 hσpos (abs_nonneg _) (abs_pos.mpr ha21ne) (abs_nonneg _) (abs_nonneg _)
    (abs_nonneg _) (abs_nonneg _) hDgt hDlow htest hσa22 hσanext hw0D hw1D

/-! ## Precise status: proven cancellation/banding content and the remaining gap

**Fully derived here (no `sorry`/`admit`/`axiom`/`native_decide`; only
`propext`/`Classical.choice`/`Quot.sound`):**

  * `corner_quadform_core` — the crux of Task F as a *division-free* real-arithmetic
    fact.  The abs pivot-path quadratic form
    `|w₀|²|a₁₁| + 2|w₀||w₁||a₂₁| + |w₁|²|a₂₂|` is bounded by `(1+u)²(3+α)σ/α³`, a
    *constant* multiple of the local scale `σ`, even though the corner multipliers
    `w₀, w₁` are individually unbounded.  The mechanism is exactly Higham's: the
    large `w₀` (carrying `|a₂₁|/|det|`) pairs with the accepted-small pivot
    `|a₁₁| ≤ α a₂₁²/σ`, and the determinant lower bound `|det| ≥ α² a₂₁²` cancels
    the `a₂₁²/det²` ratios.  This is the quantitative heart of the constant-growth
    factor-norm bound.

  * `pivotPath2Abs_corner_le` — the corner instantiation: feeding the genuine
    `flMixedMult2` corner multiplier forms (`flMixedMult2_corner0/1` from the growth
    module) and the Algorithm-11.6 determinant/threshold facts into the core gives

      `pivotPath2Abs 0 0 ≤ (1+u)²(3+α)σ/α³`.

  * `corner_rowcol_le_core` — the *linear* cancellation for the corner pivot-row
    and pivot-column paths (one factor of `w`), via the identical acceptance-test
    mechanism:

      `|a₁₁||w₀| + |a₂₁||w₁| ≤ 2(1+u)σ/α`,   `|a₂₁||w₀| + |a₂₂||w₁| ≤ 2(1+u)σ/α²`.

    These bound `pivotRowPathAbs p 0` and `pivotColPathAbs 0 q` at the leading
    corner once instantiated with the genuine multipliers (the instantiation is
    mechanical, identical in shape to `pivotPath2Abs_corner_le`).

  * `pivotPath2Abs_eq_zero_of_ne_corner`, `pivotRowPathAbs_eq_zero_of_ne_corner`,
    `pivotColPathAbs_eq_zero_of_ne_corner` — the **banding** structure: for a
    symmetric tridiagonal matrix every abs pivot path vanishes off the leading
    corner, because only the first trailing block couples to the leading pivot
    (`flMixedMult2_eq_zero_of_tridiag`).  This is the structural reason each
    `|L̂||D̂||L̂ᵀ|` entry collects only `O(1)` per-stage contributions, so the final
    `c₀` is dimension-independent.

**`hfactor` remains an explicit hypothesis of
`higham11_7_bunch_tridiagonal_backward_error` (this file adds no unconditional
discharge).**  The two remaining self-contained developments are:

  (G) *Constant-growth invariant.*  Along the pivot schedule, thread the bound on
      the *off-corner* band entries `Boff_ℓ ≤ (1+u)^ℓ·Amax` (each stage multiplies
      by `(1+u)` via `flSchurCompl2_offcorner_bound` / `fl_sub_zero_right`; the
      1×1 analogue needs the off-corner-diagonal reduction, provable exactly like
      `flSchurCompl_offdiag`).  The corner is *refreshed* each stage from off-corner
      data alone (`flSchurCompl2_corner_bound` / `flSchurCompl_corner_bound`), so it
      never compounds: `|A^ℓ 0 0| ≤ (1+γ₃)(1+1/α)·Boff_ℓ`.  Under `n·u ≤ 1/100`,
      `(1+u)^ℓ ≤ (1+u)^n ≤ 2`, so every reduced entry — hence every `D̂` block
      entry — is `≤ K·Amax` with `K = 2(1+γ₃)(1+1/α)`.  This is bookkeeping over the
      schedule (the `(1+u)^ℓ` slack, as in `flMixed_envelope_le_printed`'s
      `trailing_arith`/`trailing_arith_two`), not a new inequality; it additionally
      needs a per-stage hypothesis recording the Algorithm-11.6 pivot choices with
      `0 < σ_ℓ`, `|a₂₂|,|a₂₁|,|anext| ≤ σ_ℓ`, `σ_ℓ ≤ Amax` (the algorithm sets
      `σ_ℓ = ‖A^ℓ‖_M`).

  (F) *Product-entry assembly.*  Using `productEntry_consTwo_trailing` /
      `productEntry_consTwo_0t/1t/t0/t1` (and the trivial pivot-block entries
      `productEntry 0 0 = |A₀₀|`, etc.) plus the banding lemmas above, each
      `higham11_4_bunchKaufmanProductEntry (flMixedL s A) (flMixedD s A) I J` reduces
      to `O(1)` nonzero contributions: the corner pivot path `pivotPath2Abs 0 0`
      (bounded by `pivotPath2Abs_corner_le`), the corner pivot-row / pivot-column
      paths (bounded by `corner_rowcol_le_core` once instantiated — mechanical), the
      trivial pivot-block entries, and the recursive Schur-complement product entry
      (the induction hypothesis).  All the *cancellation* inequalities are proved
      above; what remains is (i) the mechanical instantiation of `corner_rowcol_le_core`
      into `pivotRowPathAbs`/`pivotColPathAbs` and the trivial pivot-block equalities,
      and (ii) the structural induction over the schedule assembling these into the
      full product entry via the `productEntry_consOne_split` /
      `productEntry_consTwo_*` reductions.  With every contribution `≤ const·(K·Amax)`
      from (G) and only `O(1)` of them, `hfactor` holds with a dimension-independent
      `c₀` (`c₀ = O(K/α³)`).

**Suggested `c₀`.**  Combining (G)'s `K = 2(1+γ₃)(1+1/α)` with the corner
constant `(1+u)²(3+α)/α³` and the `O(1)` banding multiplicity, a safe closed
value is `c₀ = 8(1+γ₃)(3+α)/α³` (any fixed constant of this shape works; the
point is dimension-independence).  Because the outer `p(n) = 20n` from Theorem
11.3 is still linear in `n`, the resulting `c = 20n(1+c₀)` is the plan's
Option-A landing; a constant-`c` Option B is not attempted. -/

end NumStability.Ch11Closure.BunchTriFactor
