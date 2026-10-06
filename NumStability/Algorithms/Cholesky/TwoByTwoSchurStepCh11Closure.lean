/-
Chapter 11 closure: DERIVING the per-2×2-stage trailing Schur backward error
("item b") of the mixed-pivot block-LDLᵀ factorization from the floating-point
model.

The mixed-pivot module `BlockLDLTMixedPivotCh11Closure` carries, inside the
per-stage side condition `FlMixedPivots`, a trailing 2×2 Schur backward-error
hypothesis ("item b"):

  `|pivotPath2 + flSchurCompl2 − A_trailing| ≤ cStage·γ₃·(|A_trailing| + pivotPath2Abs)`.

That module documented this as an *assumed* per-stage fact.  This file removes the
assumption: item b is DERIVED here from the standard floating-point model
(`model_mul/model_add/model_sub`) together with the genuinely source-legitimate
(11.5) 2×2-solve coupling.  Concretely:

  * `round_residual_bound` — a self-contained real-number identity/bound: the
    accumulated rounding error of the three-operation Schur update
    `fl(b − fl(fl(x·c₀)+fl(y·c₁)))` is at most `((1+u)³−1)·(|b|+|x c₀|+|y c₁|)`.
    (Pure floating-point-model content; nothing assumed.)
  * `schur2_dot_residual` — instantiates that at the actual computed multipliers
    and rounded Schur entry `flSchurCompl2`; FULLY derived from the model.
  * `cube_sub_one_le_two_gamma3` — `(1+u)³−1 ≤ 2·γ₃` under `gammaValid fp 3`.
  * `fl_twoByTwo_stage_trailing_bound` — the PRIMARY deliverable: item b, derived
    from the model (the "+2" of the constant) plus the assumed (11.5) signed
    solve coupling `hsolve` (the `+cCouple` of the constant).  With `cCouple = 3`
    this gives item b with `cStage = 5`, matching the mixed-pivot wrapper's cap.

Honesty note.  The residual `pivotPath2 + flSchurCompl2 − A_trailing` splits as

    (pivotPath2 − w_i·c_j)  +  (w_i·c_j + flSchurCompl2 − A_trailing),

where `w_i·c_j = w_{i0}·A_{j+2,0} + w_{i1}·A_{j+2,·}` is the *exact* dot product
that the Schur update rounds.  The second summand is PURE ROUNDING of the three
Schur-update operations and is fully derived here (`schur2_dot_residual`).  The
first summand is the signed (11.5) solve residual `w_i·(E·w_j − c_j)`: this
genuinely depends on the accuracy of the computed 2×2 multipliers and is NOT a
consequence of the model alone, so it is carried as the legitimate assumed
(11.5) coupling `hsolve` (analogous to, and in the same family as, the row/column
solve bounds and the abs coupling `hbridge` already present in `FlMixedPivots`).
Thus after this file the ONLY thing item b rests on is the (11.5) 2×2 solve
bound — exactly the intended source-faithful end state.

No `sorry`/`admit`/`axiom`/`unsafe`/`opaque`/`native_decide`.
-/
import NumStability.Algorithms.Cholesky.BlockLDLTMixedPivotCh11Closure

open scoped BigOperators

namespace NumStability.Ch11Closure.TwoStep

open NumStability
open NumStability.Ch11Closure
open NumStability.Ch11Closure.Mixed

/-! ## Pure-rounding core of the Schur update

The Schur update computes `fl(b − fl(fl(x)+fl(y)))` with three rounded
operations after the two products `x`, `y` are formed.  The following lemma is a
self-contained real-number statement: the difference between the ideal value
`(x + y) + [b − (x+y)] = b` and the computed `(x+y) + Ŝ` is a pure accumulation
of the four relative-error factors, bounded by `((1+u)³−1)·(|b|+|x|+|y|)`.

Here `x`, `y` play the role of the two exact products `w_{i0}·c_{j0}` and
`w_{i1}·c_{j1}`; `μ₀, μ₁` are the product rounding errors, `α` the add rounding
error, `σ` the subtract rounding error. -/
theorem round_residual_bound (u x y b μ0 μ1 α σ : ℝ)
    (hu : 0 ≤ u)
    (hμ0 : |μ0| ≤ u) (hμ1 : |μ1| ≤ u) (hα : |α| ≤ u) (hσ : |σ| ≤ u) :
    |(x + y) + (b - (x * (1 + μ0) + y * (1 + μ1)) * (1 + α)) * (1 + σ) - b|
      ≤ ((1 + u) ^ 3 - 1) * (|b| + |x| + |y|) := by
  have h1u : (0 : ℝ) ≤ 1 + u := by linarith
  -- elementary `|1 + δ|` bounds
  have habs0 : |1 + μ0| ≤ 1 + u := by
    calc |1 + μ0| ≤ |(1 : ℝ)| + |μ0| := abs_add_le _ _
      _ = 1 + |μ0| := by rw [abs_one]
      _ ≤ 1 + u := by linarith
  have habs1 : |1 + μ1| ≤ 1 + u := by
    calc |1 + μ1| ≤ |(1 : ℝ)| + |μ1| := abs_add_le _ _
      _ = 1 + |μ1| := by rw [abs_one]
      _ ≤ 1 + u := by linarith
  have habsα : |1 + α| ≤ 1 + u := by
    calc |1 + α| ≤ |(1 : ℝ)| + |α| := abs_add_le _ _
      _ = 1 + |α| := by rw [abs_one]
      _ ≤ 1 + u := by linarith
  -- two-factor bounds
  have hf0 : |(1 + μ0) * (1 + α)| ≤ (1 + u) ^ 2 := by
    rw [abs_mul]
    calc |1 + μ0| * |1 + α| ≤ (1 + u) * (1 + u) :=
          mul_le_mul habs0 habsα (abs_nonneg _) h1u
      _ = (1 + u) ^ 2 := by ring
  have hf1 : |(1 + μ1) * (1 + α)| ≤ (1 + u) ^ 2 := by
    rw [abs_mul]
    calc |1 + μ1| * |1 + α| ≤ (1 + u) * (1 + u) :=
          mul_le_mul habs1 habsα (abs_nonneg _) h1u
      _ = (1 + u) ^ 2 := by ring
  have he0 : |(1 + μ0) * (1 + α) - 1| ≤ (1 + u) ^ 2 - 1 := by
    have hrw : (1 + μ0) * (1 + α) - 1 = μ0 + α + μ0 * α := by ring
    rw [hrw]
    calc |μ0 + α + μ0 * α| ≤ |μ0 + α| + |μ0 * α| := abs_add_le _ _
      _ ≤ (|μ0| + |α|) + |μ0| * |α| := by rw [abs_mul]; linarith [abs_add_le μ0 α]
      _ ≤ (u + u) + u * u := by
          refine add_le_add (add_le_add hμ0 hα) ?_
          exact mul_le_mul hμ0 hα (abs_nonneg _) hu
      _ = (1 + u) ^ 2 - 1 := by ring
  have he1 : |(1 + μ1) * (1 + α) - 1| ≤ (1 + u) ^ 2 - 1 := by
    have hrw : (1 + μ1) * (1 + α) - 1 = μ1 + α + μ1 * α := by ring
    rw [hrw]
    calc |μ1 + α + μ1 * α| ≤ |μ1 + α| + |μ1 * α| := abs_add_le _ _
      _ ≤ (|μ1| + |α|) + |μ1| * |α| := by rw [abs_mul]; linarith [abs_add_le μ1 α]
      _ ≤ (u + u) + u * u := by
          refine add_le_add (add_le_add hμ1 hα) ?_
          exact mul_le_mul hμ1 hα (abs_nonneg _) hu
      _ = (1 + u) ^ 2 - 1 := by ring
  -- expose the cancellation
  have key : (x + y) + (b - (x * (1 + μ0) + y * (1 + μ1)) * (1 + α)) * (1 + σ) - b
      = -(x * ((1 + μ0) * (1 + α) - 1)) + -(y * ((1 + μ1) * (1 + α) - 1))
        + σ * (b - (x * ((1 + μ0) * (1 + α)) + y * ((1 + μ1) * (1 + α)))) := by ring
  rw [key]
  set f0 := (1 + μ0) * (1 + α) with hf0def
  set f1 := (1 + μ1) * (1 + α) with hf1def
  -- three-piece bounds
  have hpiece0 : |x * (f0 - 1)| ≤ |x| * ((1 + u) ^ 2 - 1) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left he0 (abs_nonneg _)
  have hpiece1 : |y * (f1 - 1)| ≤ |y| * ((1 + u) ^ 2 - 1) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left he1 (abs_nonneg _)
  have hinner : |b - (x * f0 + y * f1)| ≤ |b| + |x| * (1 + u) ^ 2 + |y| * (1 + u) ^ 2 := by
    calc |b - (x * f0 + y * f1)|
        ≤ |b| + |x * f0 + y * f1| := abs_sub _ _
      _ ≤ |b| + (|x * f0| + |y * f1|) := by linarith [abs_add_le (x * f0) (y * f1)]
      _ ≤ |b| + (|x| * (1 + u) ^ 2 + |y| * (1 + u) ^ 2) := by
          rw [abs_mul x f0, abs_mul y f1]
          have hx0 : |x| * |f0| ≤ |x| * (1 + u) ^ 2 :=
            mul_le_mul_of_nonneg_left hf0 (abs_nonneg _)
          have hy0 : |y| * |f1| ≤ |y| * (1 + u) ^ 2 :=
            mul_le_mul_of_nonneg_left hf1 (abs_nonneg _)
          linarith
      _ = |b| + |x| * (1 + u) ^ 2 + |y| * (1 + u) ^ 2 := by ring
  have hpiece2 : |σ * (b - (x * f0 + y * f1))|
      ≤ u * (|b| + |x| * (1 + u) ^ 2 + |y| * (1 + u) ^ 2) := by
    rw [abs_mul]
    calc |σ| * |b - (x * f0 + y * f1)|
        ≤ u * |b - (x * f0 + y * f1)| := mul_le_mul_of_nonneg_right hσ (abs_nonneg _)
      _ ≤ u * (|b| + |x| * (1 + u) ^ 2 + |y| * (1 + u) ^ 2) :=
          mul_le_mul_of_nonneg_left hinner hu
  -- triangle inequality on the three pieces
  have htri :
      |(-(x * (f0 - 1))) + (-(y * (f1 - 1))) + σ * (b - (x * f0 + y * f1))|
        ≤ |x * (f0 - 1)| + |y * (f1 - 1)| + |σ * (b - (x * f0 + y * f1))| := by
    calc |(-(x * (f0 - 1))) + (-(y * (f1 - 1))) + σ * (b - (x * f0 + y * f1))|
        ≤ |(-(x * (f0 - 1))) + (-(y * (f1 - 1)))| + |σ * (b - (x * f0 + y * f1))| :=
          abs_add_le _ _
      _ ≤ |x * (f0 - 1)| + |y * (f1 - 1)| + |σ * (b - (x * f0 + y * f1))| := by
          have h := abs_add_le (-(x * (f0 - 1))) (-(y * (f1 - 1)))
          rw [abs_neg, abs_neg] at h
          linarith
  refine htri.trans ?_
  -- fold the three piece-bounds into `((1+u)³−1)·(|b|+|x|+|y|)`
  have hfinal :
      |x| * ((1 + u) ^ 2 - 1) + |y| * ((1 + u) ^ 2 - 1)
        + u * (|b| + |x| * (1 + u) ^ 2 + |y| * (1 + u) ^ 2)
      ≤ ((1 + u) ^ 3 - 1) * (|b| + |x| + |y|) := by
    have hbnn := abs_nonneg b
    have hdiff :
        ((1 + u) ^ 3 - 1) * (|b| + |x| + |y|)
          - (|x| * ((1 + u) ^ 2 - 1) + |y| * ((1 + u) ^ 2 - 1)
             + u * (|b| + |x| * (1 + u) ^ 2 + |y| * (1 + u) ^ 2))
          = (2 * u + 3 * u ^ 2 + u ^ 3) * |b| := by ring
    have hpos : 0 ≤ (2 * u + 3 * u ^ 2 + u ^ 3) * |b| :=
      mul_nonneg (by nlinarith [hu, mul_nonneg hu hu, mul_nonneg (mul_nonneg hu hu) hu]) hbnn
    linarith [hdiff, hpos]
  linarith [hpiece0, hpiece1, hpiece2, hfinal]

/-! ## `(1+u)³ − 1 ≤ 2·γ₃` -/

theorem cube_sub_one_le_two_gamma3 (fp : FPModel) (hval : gammaValid fp 3) :
    (1 + fp.u) ^ 3 - 1 ≤ 2 * gamma fp 3 := by
  have hu := fp.u_nonneg
  have hval' : (3 : ℝ) * fp.u < 1 := by
    unfold gammaValid at hval; push_cast at hval; linarith
  have hden : 0 < 1 - (3 : ℝ) * fp.u := by linarith
  have hgamma : gamma fp 3 = ((3 : ℝ) * fp.u) / (1 - (3 : ℝ) * fp.u) := by
    unfold gamma; push_cast; ring
  have key : ((1 + fp.u) ^ 3 - 1) * (1 - (3 : ℝ) * fp.u) ≤ 6 * fp.u := by
    nlinarith [hu, mul_nonneg hu hu, mul_nonneg (mul_nonneg hu hu) hu,
      mul_nonneg (mul_nonneg (mul_nonneg hu hu) hu) hu]
  rw [hgamma,
    show (2 : ℝ) * (((3 : ℝ) * fp.u) / (1 - (3 : ℝ) * fp.u))
        = (6 * fp.u) / (1 - (3 : ℝ) * fp.u) from by ring,
    le_div_iff₀ hden]
  linarith [key]

/-! ## The fully-derived pure-rounding Schur bound

`schur2_dot_residual` compares the *computed* rounded Schur entry `flSchurCompl2`
against the *exact* dot product `w_{i0}·c_{j0} + w_{i1}·c_{j1}` that it rounds.
It is derived purely from the floating-point model — no solve/coupling
hypotheses. -/
theorem schur2_dot_residual (fp : FPModel) {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) (i j : Fin m) :
    |(flMixedMult2 m fp A i 0 * A j.succ.succ 0
        + flMixedMult2 m fp A i 1 * A j.succ.succ (oneIdx m))
      + flSchurCompl2 m fp A i j - A i.succ.succ j.succ.succ|
      ≤ ((1 + fp.u) ^ 3 - 1)
          * (|A i.succ.succ j.succ.succ|
              + |flMixedMult2 m fp A i 0| * |A j.succ.succ 0|
              + |flMixedMult2 m fp A i 1| * |A j.succ.succ (oneIdx m)|) := by
  unfold flSchurCompl2
  set b := A i.succ.succ j.succ.succ with hb
  set w0 := flMixedMult2 m fp A i 0 with hw0
  set w1 := flMixedMult2 m fp A i 1 with hw1
  set c0 := A j.succ.succ 0 with hc0
  set c1 := A j.succ.succ (oneIdx m) with hc1
  obtain ⟨σ, hσ, hs⟩ := fp.model_sub b (fp.fl_add (fp.fl_mul w0 c0) (fp.fl_mul w1 c1))
  obtain ⟨α, hα, ha⟩ := fp.model_add (fp.fl_mul w0 c0) (fp.fl_mul w1 c1)
  obtain ⟨μ0, hμ0, hm0⟩ := fp.model_mul w0 c0
  obtain ⟨μ1, hμ1, hm1⟩ := fp.model_mul w1 c1
  rw [hs, ha, hm0, hm1]
  have h := round_residual_bound fp.u (w0 * c0) (w1 * c1) b μ0 μ1 α σ
    fp.u_nonneg hμ0 hμ1 hα hσ
  rw [abs_mul w0 c0, abs_mul w1 c1] at h
  exact h

/-! ## PRIMARY DELIVERABLE — item b, derived

The trailing 2×2 Schur backward error ("item b" of `FlMixedPivots`), derived from
the floating-point model plus the source-legitimate (11.5) 2×2-solve coupling.

`hbridge` is the abs coupling `|w_{i0}||c_{j0}| + |w_{i1}||c_{j1}| ≤ pivotPath2Abs`
already present in `FlMixedPivots` (Higham (11.5), abs form).

`hsolve` is the signed (11.5) solve coupling — the residual of the computed 2×2
solve `pivotPath2 − w_i·c_j = w_i·(E·w_j − c_j)`.  It genuinely depends on the
computed-multiplier accuracy and is not a consequence of the model alone, so it
is carried as the legitimate assumed (11.5) bound.

The `+2` of the resulting constant is FULLY DERIVED (the Schur-update rounding);
the `+cCouple` is the assumed (11.5) coupling.  Taking `cCouple = 3` yields item
b with `cStage = 5`, matching the mixed-pivot wrapper cap `cStage ≤ 5`. -/
theorem fl_twoByTwo_stage_trailing_bound (fp : FPModel) (hval : gammaValid fp 3) {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) (i j : Fin m) (cCouple : ℝ)
    (hbridge : |flMixedMult2 m fp A i 0| * |A j.succ.succ 0|
                 + |flMixedMult2 m fp A i 1| * |A j.succ.succ (oneIdx m)|
               ≤ pivotPath2Abs m fp A i j)
    (hsolve : |pivotPath2 m fp A i j
                 - (flMixedMult2 m fp A i 0 * A j.succ.succ 0
                    + flMixedMult2 m fp A i 1 * A j.succ.succ (oneIdx m))|
               ≤ cCouple * gamma fp 3
                   * (|A i.succ.succ j.succ.succ| + pivotPath2Abs m fp A i j)) :
    |pivotPath2 m fp A i j + flSchurCompl2 m fp A i j - A i.succ.succ j.succ.succ|
      ≤ (cCouple + 2) * gamma fp 3
          * (|A i.succ.succ j.succ.succ| + pivotPath2Abs m fp A i j) := by
  have hu0 := fp.u_nonneg
  have hPPA : 0 ≤ pivotPath2Abs m fp A i j := by
    rw [pivotPath2Abs]
    exact Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ =>
      mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
  have hBP : 0 ≤ |A i.succ.succ j.succ.succ| + pivotPath2Abs m fp A i j :=
    add_nonneg (abs_nonneg _) hPPA
  -- fully-derived rounding part → `2·γ₃·(|A|+pivotPath2Abs)`
  have hround :
      |(flMixedMult2 m fp A i 0 * A j.succ.succ 0
          + flMixedMult2 m fp A i 1 * A j.succ.succ (oneIdx m))
        + flSchurCompl2 m fp A i j - A i.succ.succ j.succ.succ|
        ≤ 2 * gamma fp 3 * (|A i.succ.succ j.succ.succ| + pivotPath2Abs m fp A i j) := by
    have h1 := schur2_dot_residual fp A i j
    have h2 :
        |A i.succ.succ j.succ.succ|
            + |flMixedMult2 m fp A i 0| * |A j.succ.succ 0|
            + |flMixedMult2 m fp A i 1| * |A j.succ.succ (oneIdx m)|
          ≤ |A i.succ.succ j.succ.succ| + pivotPath2Abs m fp A i j := by
      linarith [hbridge]
    have hcubenn : 0 ≤ (1 + fp.u) ^ 3 - 1 := by
      nlinarith [hu0, mul_nonneg hu0 hu0, mul_nonneg (mul_nonneg hu0 hu0) hu0]
    have hcube := cube_sub_one_le_two_gamma3 fp hval
    have hstep :
        ((1 + fp.u) ^ 3 - 1)
            * (|A i.succ.succ j.succ.succ|
                + |flMixedMult2 m fp A i 0| * |A j.succ.succ 0|
                + |flMixedMult2 m fp A i 1| * |A j.succ.succ (oneIdx m)|)
          ≤ 2 * gamma fp 3 * (|A i.succ.succ j.succ.succ| + pivotPath2Abs m fp A i j) := by
      calc ((1 + fp.u) ^ 3 - 1)
              * (|A i.succ.succ j.succ.succ|
                  + |flMixedMult2 m fp A i 0| * |A j.succ.succ 0|
                  + |flMixedMult2 m fp A i 1| * |A j.succ.succ (oneIdx m)|)
          ≤ ((1 + fp.u) ^ 3 - 1)
              * (|A i.succ.succ j.succ.succ| + pivotPath2Abs m fp A i j) :=
            mul_le_mul_of_nonneg_left h2 hcubenn
        _ ≤ 2 * gamma fp 3 * (|A i.succ.succ j.succ.succ| + pivotPath2Abs m fp A i j) :=
            mul_le_mul_of_nonneg_right hcube hBP
    exact h1.trans hstep
  -- split the signed residual: (11.5) coupling + derived rounding
  have hsplit :
      pivotPath2 m fp A i j + flSchurCompl2 m fp A i j - A i.succ.succ j.succ.succ
        = (pivotPath2 m fp A i j
            - (flMixedMult2 m fp A i 0 * A j.succ.succ 0
               + flMixedMult2 m fp A i 1 * A j.succ.succ (oneIdx m)))
          + ((flMixedMult2 m fp A i 0 * A j.succ.succ 0
               + flMixedMult2 m fp A i 1 * A j.succ.succ (oneIdx m))
              + flSchurCompl2 m fp A i j - A i.succ.succ j.succ.succ) := by ring
  rw [hsplit]
  calc |(pivotPath2 m fp A i j
          - (flMixedMult2 m fp A i 0 * A j.succ.succ 0
             + flMixedMult2 m fp A i 1 * A j.succ.succ (oneIdx m)))
        + ((flMixedMult2 m fp A i 0 * A j.succ.succ 0
             + flMixedMult2 m fp A i 1 * A j.succ.succ (oneIdx m))
            + flSchurCompl2 m fp A i j - A i.succ.succ j.succ.succ)|
      ≤ |pivotPath2 m fp A i j
            - (flMixedMult2 m fp A i 0 * A j.succ.succ 0
               + flMixedMult2 m fp A i 1 * A j.succ.succ (oneIdx m))|
          + |(flMixedMult2 m fp A i 0 * A j.succ.succ 0
               + flMixedMult2 m fp A i 1 * A j.succ.succ (oneIdx m))
              + flSchurCompl2 m fp A i j - A i.succ.succ j.succ.succ| := abs_add_le _ _
    _ ≤ cCouple * gamma fp 3 * (|A i.succ.succ j.succ.succ| + pivotPath2Abs m fp A i j)
          + 2 * gamma fp 3 * (|A i.succ.succ j.succ.succ| + pivotPath2Abs m fp A i j) :=
        add_le_add hsolve hround
    _ = (cCouple + 2) * gamma fp 3
          * (|A i.succ.succ j.succ.succ| + pivotPath2Abs m fp A i j) := by ring

/-- Concrete instance with `cCouple = 3`, giving item b at the wrapper's cap
    `cStage = 5`.  This is exactly the shape of the `htrail` field of
    `FlMixedPivots` (`consTwo` case) with `cStage = 5`. -/
theorem fl_twoByTwo_stage_trailing_bound_five (fp : FPModel) (hval : gammaValid fp 3) {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) (i j : Fin m)
    (hbridge : |flMixedMult2 m fp A i 0| * |A j.succ.succ 0|
                 + |flMixedMult2 m fp A i 1| * |A j.succ.succ (oneIdx m)|
               ≤ pivotPath2Abs m fp A i j)
    (hsolve : |pivotPath2 m fp A i j
                 - (flMixedMult2 m fp A i 0 * A j.succ.succ 0
                    + flMixedMult2 m fp A i 1 * A j.succ.succ (oneIdx m))|
               ≤ 3 * gamma fp 3
                   * (|A i.succ.succ j.succ.succ| + pivotPath2Abs m fp A i j)) :
    |pivotPath2 m fp A i j + flSchurCompl2 m fp A i j - A i.succ.succ j.succ.succ|
      ≤ 5 * gamma fp 3
          * (|A i.succ.succ j.succ.succ| + pivotPath2Abs m fp A i j) := by
  have h := fl_twoByTwo_stage_trailing_bound fp hval A i j 3 hbridge hsolve
  norm_num at h
  exact h

/-! ## STRETCH — recursive discharge and a fully-derived general 11.3 wrapper

`DenseAcceptance` is the per-stage side condition for the GENERAL (dense)
mixed-pivot path with item b REMOVED: each 2×2 stage carries only the genuinely
source-legitimate (11.5) data — the four solve bounds (`cSolve`), the abs
coupling (`hbridge`), and the signed solve coupling (`hsolve`) — plus the derived
1×1 conditions.  It does NOT carry the trailing 2×2 Schur backward error, which
is now discharged for free by `fl_twoByTwo_stage_trailing_bound_five`. -/
noncomputable def DenseAcceptance (fp : FPModel) (cSolve : ℝ) :
    {n : ℕ} → PivotSchedule n → (Fin n → Fin n → ℝ) → Prop
  | 0, .nil, _ => True
  | _ + 1, .consOne s, A =>
      A 0 0 ≠ 0 ∧ (∀ i : Fin _, A 0 i.succ = A i.succ 0) ∧
      DenseAcceptance fp cSolve s (flSchurCompl _ fp A)
  | m + 2, .consTwo s, A =>
      -- pivot-row (11.5) solve bound, embed 0 and embed 1
      (∀ j : Fin m,
        |A 0 0 * flMixedMult2 m fp A j 0 + A 0 (oneIdx m) * flMixedMult2 m fp A j 1
          - A 0 j.succ.succ| ≤ cSolve * fp.u * pivotRowPathAbs m fp A 0 j) ∧
      (∀ j : Fin m,
        |A (oneIdx m) 0 * flMixedMult2 m fp A j 0
            + A (oneIdx m) (oneIdx m) * flMixedMult2 m fp A j 1
          - A (oneIdx m) j.succ.succ| ≤ cSolve * fp.u * pivotRowPathAbs m fp A 1 j) ∧
      -- pivot-column (11.5) solve bound, embed 0 and embed 1
      (∀ i : Fin m,
        |flMixedMult2 m fp A i 0 * A 0 0 + flMixedMult2 m fp A i 1 * A (oneIdx m) 0
          - A i.succ.succ 0| ≤ cSolve * fp.u * pivotColPathAbs m fp A i 0) ∧
      (∀ i : Fin m,
        |flMixedMult2 m fp A i 0 * A 0 (oneIdx m)
            + flMixedMult2 m fp A i 1 * A (oneIdx m) (oneIdx m)
          - A i.succ.succ (oneIdx m)| ≤ cSolve * fp.u * pivotColPathAbs m fp A i 1) ∧
      -- abs coupling (11.5, abs form)
      (∀ i j : Fin m,
        |flMixedMult2 m fp A i 0| * |A j.succ.succ 0|
            + |flMixedMult2 m fp A i 1| * |A j.succ.succ (oneIdx m)|
          ≤ pivotPath2Abs m fp A i j) ∧
      -- signed (11.5) solve coupling (the ONLY 2×2 residual still assumed)
      (∀ i j : Fin m,
        |pivotPath2 m fp A i j
            - (flMixedMult2 m fp A i 0 * A j.succ.succ 0
               + flMixedMult2 m fp A i 1 * A j.succ.succ (oneIdx m))|
          ≤ 3 * gamma fp 3
              * (|A i.succ.succ j.succ.succ| + pivotPath2Abs m fp A i j)) ∧
      DenseAcceptance fp cSolve s (flSchurCompl2 m fp A)

/-- **Recursive discharge of item b.**  From `DenseAcceptance` (which carries no
    trailing Schur backward error), the full mixed-pivot side condition
    `FlMixedPivots` with `cStage = 5` holds: at every 2×2 stage the trailing
    bound (item b) is produced by `fl_twoByTwo_stage_trailing_bound_five` from the
    per-stage abs coupling and signed solve coupling. -/
theorem FlMixedPivots_of_denseAcceptance (fp : FPModel) (hval : gammaValid fp 3)
    (cSolve : ℝ) :
    ∀ {n : ℕ} (s : PivotSchedule n) (A : Fin n → Fin n → ℝ),
      DenseAcceptance fp cSolve s A → FlMixedPivots fp cSolve 5 s A := by
  intro n s
  induction s with
  | nil => intro A _; exact trivial
  | consOne s ih =>
      intro A hacc
      obtain ⟨ha, hsym, hrec⟩ := hacc
      exact ⟨ha, hsym, ih (flSchurCompl _ fp A) hrec⟩
  | consTwo s ih =>
      intro A hacc
      obtain ⟨hr0, hr1, hc0, hc1, hbr, hsol, hrec⟩ := hacc
      exact ⟨hr0, hr1, hc0, hc1,
        (fun i j => fl_twoByTwo_stage_trailing_bound_five fp hval A i j (hbr i j) (hsol i j)),
        hbr, ih (flSchurCompl2 _ fp A) hrec⟩

/-- **Fully-derived general (dense) Theorem 11.3 wrapper.**  Identical conclusion
    to `higham11_3_block_ldlt_mixed_printed`, but the per-stage side condition is
    `DenseAcceptance` — i.e. item b (the trailing 2×2 Schur backward error) is no
    longer assumed; it is discharged from the floating-point model plus the
    (11.5) solve data.  `cStage` is fixed to the derived value `5`. -/
theorem higham11_3_block_ldlt_mixed_printed_of_acceptance (fp : FPModel)
    (hval : gammaValid fp 3) (cSolve : ℝ) (hcS0 : 0 ≤ cSolve) (hcS40 : cSolve ≤ 40)
    {n : ℕ} (s : PivotSchedule n) (A : Fin n → Fin n → ℝ)
    (hsmall : (n : ℝ) * fp.u ≤ 1 / 100)
    (hacc : DenseAcceptance fp cSolve s A) :
    ∃ L D ΔA1 ΔA2 : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA1 i j|
          ≤ higham11_3_printedFirstOrderBound n A L D id (pPoly n) fp.u i j) ∧
      (∀ i j, |ΔA2 i j|
          ≤ higham11_3_printedFirstOrderBound n A L D id (pPoly n) fp.u i j) ∧
      (∀ i j, (∑ k₁, ∑ k₂, L i k₁ * D k₁ k₂ * L j k₂) = A i j + ΔA1 i j) :=
  higham11_3_block_ldlt_mixed_printed fp hval cSolve 5 hcS0 hcS40
    (by norm_num) (by norm_num) s A hsmall
    (FlMixedPivots_of_denseAcceptance fp hval cSolve s A hacc)

end NumStability.Ch11Closure.TwoStep
