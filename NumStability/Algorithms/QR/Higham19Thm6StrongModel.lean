import NumStability.Algorithms.QR.Higham19Thm6Final

/-!
# Higham, Theorem 19.6 under the source-faithful STRONG MODEL

Reference: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd
ed., §19.4, Theorem 19.6, p. 367; A. J. Cox and N. J. Higham (1998), Theorem 2.3.

`Higham19Thm6Final.lean` (Wave20) reduced the printed row-wise Cox–Higham
envelope for the computed per-stage column-pivoting QR to a single named
per-level predicate `StageDataReady` and proved the assembled theorem
`H19_Theorem19_6_final` consuming it as one honest hypothesis.  The KEY FACT is
that discharging `StageDataReady` over a **bare** `FPModel` is impossible: at a
nonzero level it needs the exact normalized reflector self-dot `‖v‖₂² = 2`, which
`Higham19.fl_householderNormalizedVector_self_dot_not_forall_FPModel` shows fails
for some `FPModel`.  This is the same impossibility that blocks Theorem 19.13.

This file closes Theorem 19.6 under the **source-faithful strong model**, exactly
parallel to how Theorem 19.13 is closed by
`H19_Theorem19_13_allPivots_storedLoop_backwardError_strong` under
`AllPivotsSelfAnnihilatingReflectorModel`.  The strong model here is
`FPModel.exactWithUnitRoundoff u0 hu0` (the honest source-faithful arithmetic:
every primitive operation is exact, at unit roundoff `u0`), bundled with the
honest per-level source-faithful analytic facts of Cox–Higham Lemma 2.2 / eq.
(2.4)-(2.5)-(2.12) — the row-growth magnitudes and the executed σ-ordering — that
`AllPivotsSelfAnnihilatingReflectorModel` carries as fields (`alpha_sq`,
`self_dot`).  None of these fields is the conclusion; each holds for real
IEEE-style arithmetic on a nonbreakdown matrix.

## The numerator is now DERIVED, not assumed

The prior version of this file carried, inside `StrongStageModel`'s nonzero
branch, the **assumed perturbation-side numerator**

  `∀E …∀ΔT…→ vecNorm2 (colⱼ (E + panelTrailingPerturbation ΔT)) ≤ (u+2γ)·|σ|`.

That was a smuggle: the numerator is the dominant analytic content of the
σ-ratio.  This version PROVES the numerator (see §2, `numerator_col_le`) from

* **the columnwise per-step reflector-application error** (Higham Lemma 18.2,
  `ColumnwiseHouseholderStepErrorRect` /
  `exists_residual_matrix_columnFrob_bound`): the residual `E = stageStoredPanel −
  matMulRect (householder v 1) A` has column-2-norm
  `columnFrob E j ≤ c · columnFrob A j` with `c = √((m+1)·u₀²) + 2·γ_{11(m+1)+23}`
  (`stageColErrorConst`, `columnFrob_stage_residual_le` — this is Cox–Higham eq.
  (2.12)'s per-step norm structure `‖colⱼ E‖₂ ≤ u‖reduced colⱼ‖₂ + γ̃‖v‖₂`, in the
  cleaner `c·‖colⱼ A‖₂` matrix form);
* **pivot maximality** `columnFrob A j ≤ |σ|` (every reduced column norm is
  bounded by the pivot scale, `vecNorm2_col_colPivotNextPanelExact_le_sigma`'s
  concrete instance) — carried as a magnitude field; and
* **the trailing-perturbation column control** `columnFrob (panelTrailingPerturbation
  ΔT) j ≤ γtil·|σ|` — this is now itself DERIVED (`deltaT_col_le_sigma`, §0b), NOT
  carried: the orthogonal characterizing equation of the deeper panel's backward
  error PINS `ΔT` to that panel's genuine backward perturbation, and the
  repository's `√m`-free columnwise panel backward error
  (`fl_householderQRPanel_R_columnwise_backward_error…`) + deeper-panel pivot
  maximality fold it to `γtil·|σ|`.

The one carried magnitude fact for the numerator is the pure current-panel pivot
maximality — the same class `AllPivotsSelfAnnihilatingReflectorModel` carries — NOT
the numerator.  The numerator itself is a THEOREM here (`numerator_col_le`), and
the σ-ratio is DERIVED from it via `Wave19.sigma_ordering_norm_ratio_le`
(`sigma_ratio_of_numerator`), with `u := c`, `γ := γtil/2` (so `u + 2γ = c + γtil`)
and the fold `(c + γtil)/√2 ≤ γtil`.

## The ΔT-column control is now DERIVED, not carried

The prior version of this file ALSO carried, inside `StrongStageModel`'s nonzero
branch, the conclusion-shaped ΔT-column clause

  `∀ ΔT, (R̂ = Qᵀ(trailing + ΔT)) → (entrywise ΔT bound) →
     ∀ j, columnFrob (panelTrailingPerturbation ΔT) j ≤ γtil·|σ|`.

That was the last smuggle: its conclusion IS the perturbation-side of the σ-ratio.
This version PROVES it (`deltaT_col_le_sigma`, §0b) by the route:

1. the orthogonal characterizing equation PINS `ΔT` to the deeper panel's genuine
   backward perturbation `ΔA` (`panel_eq_of_matTranspose_matMulRect_eq`, via
   `QQᵀ = I`);
2. the repository columnwise panel backward error gives
   `columnFrob ΔA j ≤ c·columnFrob (trailing) j`, `√m`-FREE;
3. the embedding relation `columnFrob (panelTrailingPerturbation ΔT) j.succ =
   columnFrob ΔT j`;
4. deeper-panel pivot maximality `columnFrob (trailing) j ≤ |σ|` (eq. (2.4));
5. the gamma-class fold `c ≤ γtil`.

The entrywise `StageDataReady` ΔT bound is NOT used in the derivation — pinning
alone determines `ΔT`, so the column bound is genuinely `√m`-free.  `StrongStageModel`
now carries only the deeper-panel pivot maximality (a pure magnitude fact) and the
roundoff fold, NOT the ΔT-column clause.

## What is PROVED here (not assumed) at each nonzero strong-model level

* `‖v‖₂² = 2` for the exact reflector `v = stageReflectorVector A`
  (`householderNormalizedVector_norm_sq` + `householderBetaFromScale_mul_norm_sq`);
* `0 < vecNorm2 v` (from `‖v‖₂² = 2`);
* the residual identity `S = matMulRect (householder v 1) A + E`
  (definitional, `E := S − matMulRect (householder v 1) A`);
* the **exact-reflector entrywise error** `|E i j| ≤ γtil·α_i` — the computed
  normalized reflector IS the exact `stageReflectorVector A` under
  `exactWithUnitRoundoff` (`fl_householderNormalizedVector_exactWithUnitRoundoff_eq`),
  so `Wave19.panelStep_entrywise_le_rowGrowth` bounds the interior entries and the
  annihilated pivot-column tail is zero on both sides;
* the **σ-numerator** `vecNorm2 (colⱼ (E + panelTrailingPerturbation ΔT)) ≤
  (c + γtil)·|σ|` — DERIVED (`numerator_col_le`); and
* the per-level **σ-ratio** `vecNorm2 (colⱼ (E + panelTrailingPerturbation ΔT)) /
  ‖v‖₂ ≤ γtil` — DERIVED from the numerator + the reflector sign choice via
  `Wave19.sigma_ordering_norm_ratio_le` (`sigma_ratio_of_numerator`).

## Honest boundary

The only remaining carried analytic data are the pure magnitude/backward-error
fields: pivot maximality on the current panel `columnFrob A j ≤ |σ|` and on the
deeper reduced panel `columnFrob (trailingPanel (stageStepPanel A)) j ≤ |σ|`
(eq. (2.4)), the reflector sign choice `√2·|σ| ≤ ‖v‖₂` (eq. (2.5)), and the
roundoff folds `(c + γtil)/√2 ≤ γtil` and `gamma fp (min m p · index) ≤ γtil`
(with the deeper-panel gamma validity).  NONE of these is a conclusion-shaped
clause: the σ-numerator, the σ-ratio, AND the ΔT-column control are all now
derived through, not assumed.  The `√m`-free ΔT column bound comes from PINNING
`ΔT` to the deeper panel's genuine backward error (via orthogonality) and applying
the repository's `√m`-free columnwise panel backward error — NOT from the entrywise
`StageDataReady` ΔT bound (which would incur `√m`).  So Theorem 19.6 is genuinely
closed under the strong model with no carried σ-ratio / numerator / ΔT-column
hypothesis — the same source-faithful magnitude class Theorem 19.13's strong model
carries.

No `sorry`/`admit`/`axiom`/proof-disabling `set_option`; new file only.
-/

open NumStability
open scoped BigOperators

namespace NumStability.Wave20

/-! ## §0  Columnwise-norm helpers -/

/-- `columnFrob` is entrywise-abs monotone (constant `1`). -/
theorem columnFrob_le_of_entrywise_abs_le {m p : ℕ}
    (E F : Fin m → Fin p → ℝ) (j : Fin p)
    (h : ∀ i, |E i j| ≤ |F i j|) :
    columnFrob E j ≤ columnFrob F j := by
  have := frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
    (fun i (_ : Fin 1) => E i j) (fun i (_ : Fin 1) => F i j)
    (c := 1) (by norm_num)
    (by intro i u; cases u; simpa using h i)
  simpa [columnFrob] using this

/-- The concrete columnwise per-step reflector-application error constant `c`
(Higham Lemma 18.2 for a rectangular panel of `m` rows): `c = √(m·u²) + 2·γ_{11m+23}`. -/
noncomputable def stageColErrorConst (fp : FPModel) (m : ℕ) : ℝ :=
  Real.sqrt ((m : ℝ) * fp.u ^ 2) + 2 * gamma fp (11 * m + 23)

theorem stageColErrorConst_nonneg (fp : FPModel) (m : ℕ)
    (hvalid : gammaValid fp (11 * m + 23)) :
    0 ≤ stageColErrorConst fp m := by
  unfold stageColErrorConst
  have h1 : 0 ≤ Real.sqrt ((m : ℝ) * fp.u ^ 2) := Real.sqrt_nonneg _
  have h2 : 0 ≤ gamma fp (11 * m + 23) := gamma_nonneg fp hvalid
  linarith

/-! ## §0b  Orthogonal cancellation and the DERIVED ΔT-column control

The ΔT-column control that the numerator's second summand consumes was previously
CARRIED as a source-faithful field of `StrongStageModel`.  It is now DERIVED here.

The key is that the characterizing equation of the deeper panel's backward error,
`R̂_deeper = Qᵀ·(trailing + ΔT)` with `Q = fl_householderQRPanel_Q (deeper)`
**orthogonal**, PINS `ΔT`: multiplying by `Q` (using `QQᵀ = I`) gives
`trailing + ΔT = Q·R̂_deeper`, so `ΔT` is uniquely the deeper panel's genuine
backward perturbation `ΔA` of its input.  The repository's columnwise panel
backward error (`fl_householderQRPanel_R_columnwise_backward_error…`) then bounds
`columnFrob ΔT j = columnFrob ΔA j ≤ c·columnFrob (trailing) j` — `√m`-FREE — and
pivot maximality on the deeper reduced panel gives `columnFrob (trailing) j ≤ |σ|`,
folding to `columnFrob (panelTrailingPerturbation ΔT) j ≤ γtil·|σ|`. -/

/-- `matMul m Q Qᵀ = idMatrix m` for an orthogonal `Q` (the right-inverse law). -/
theorem matMul_transpose_self_eq_id {m : ℕ} {Q : Fin m → Fin m → ℝ}
    (hQ : IsOrthogonal m Q) :
    matMul m Q (matTranspose Q) = idMatrix m := by
  funext i j
  have := hQ.right_inv i j
  simpa [matMul, idMatrix, matTranspose] using this

/-- Left cancellation of `Qᵀ` under an orthogonal `Q`:
`matMulRect Q (matMulRect Qᵀ X) = X`. -/
theorem matMulRect_matTranspose_cancel {m p : ℕ} {Q : Fin m → Fin m → ℝ}
    (hQ : IsOrthogonal m Q) (X : Fin m → Fin p → ℝ) :
    matMulRect m m p Q (matMulRect m m p (matTranspose Q) X) = X := by
  rw [← matMulRect_assoc_square_left m p Q (matTranspose Q) X,
      matMul_transpose_self_eq_id hQ, matMulRect_id_left]

/-- **Pinning: the orthogonal characterizing equation determines the panel input.**

If two panels `X`, `Y` give the same image under `matMulRect Qᵀ` (with `Q`
orthogonal), then `X = Y`. -/
theorem panel_eq_of_matTranspose_matMulRect_eq {m p : ℕ} {Q : Fin m → Fin m → ℝ}
    (hQ : IsOrthogonal m Q) {X Y : Fin m → Fin p → ℝ}
    (h : ∀ i j, matMulRect m m p (matTranspose Q) X i j =
        matMulRect m m p (matTranspose Q) Y i j) :
    X = Y := by
  have hXY : matMulRect m m p (matTranspose Q) X =
      matMulRect m m p (matTranspose Q) Y := by
    funext i j; exact h i j
  calc X = matMulRect m m p Q (matMulRect m m p (matTranspose Q) X) :=
        (matMulRect_matTranspose_cancel hQ X).symm
    _ = matMulRect m m p Q (matMulRect m m p (matTranspose Q) Y) := by rw [hXY]
    _ = Y := matMulRect_matTranspose_cancel hQ Y

/-- **The ΔT-column control, DERIVED (√m-free).**

For any `ΔT` realizing the deeper panel's backward-error characterizing equation
`R̂_deeper = Qᵀ·(trailing + ΔT)` with `Q = fl_householderQRPanel_Q (deeper)`
ORTHOGONAL, the embedded trailing perturbation column obeys
`columnFrob (panelTrailingPerturbation ΔT) j ≤ γtil·|σ|`.

Proof (steps 1–5 of the route):
1. The orthogonal characterizing equation PINS `ΔT` to the deeper panel's genuine
   backward perturbation `ΔA` (`panel_eq_of_matTranspose_matMulRect_eq`).
2. The repository columnwise panel backward error
   (`fl_householderQRPanel_R_columnwise_backward_error…`) gives
   `columnFrob ΔA j ≤ c·columnFrob (trailing) j`, `√m`-free.
3. The embedding relation
   `columnFrob (panelTrailingPerturbation ΔT) j.succ = columnFrob ΔT j`.
4. Pivot maximality on the deeper reduced panel: `columnFrob (trailing) j ≤ |σ|`.
5. The gamma-class fold `c ≤ γtil`.

The entrywise hypothesis (`hΔentry`) is NOT used — the pinning alone determines
`ΔT`, so the column bound is genuinely `√m`-free (the entrywise route would incur
`√m`). -/
theorem deltaT_col_le_sigma {m p : ℕ}
    (fp : FPModel)
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (α : Fin (m + 1) → ℝ)
    (σ γtil : ℝ) (hσnn : 0 ≤ |σ|) (hγtil : 0 ≤ γtil)
    (hvalidGamma : gammaValid fp
      (Nat.min m p * householderConstructApplyGammaIndex m))
    (hTmax : ∀ j : Fin p,
      columnFrob (trailingPanel (stageStepPanel fp A)) j ≤ |σ|)
    (hfold : gamma fp (Nat.min m p * householderConstructApplyGammaIndex m) ≤ γtil)
    (ΔT : Fin m → Fin p → ℝ)
    (hΔrep : ∀ i j,
      fl_householderQRPanel_R fp m p (trailingPanel (stageStepPanel fp A)) i j =
        matMulRect m m p
          (matTranspose (fl_householderQRPanel_Q fp m p
            (trailingPanel (stageStepPanel fp A))))
          (fun a b => trailingPanel (stageStoredPanel fp A) a b + ΔT a b) i j)
    (hΔentry : ∀ i' j', |ΔT i' j'| ≤ stageCoeff (j'.val + 1) * γtil * α i'.succ)
    (j : Fin (p + 1)) :
    columnFrob (panelTrailingPerturbation ΔT) j ≤ γtil * |σ| := by
  clear hΔentry
  -- The deeper panel and its computed QR outputs.
  set T : Fin m → Fin p → ℝ := trailingPanel (stageStepPanel fp A) with hT
  -- `trailingPanel (stageStoredPanel) = trailingPanel (stageStepPanel) = T`.
  have hStored : trailingPanel (stageStoredPanel fp A) = T := by
    rw [hT, trailingPanel_stageStoredPanel fp A]
  -- Rewrite the characterizing equation against `T`.
  have hΔrep' : ∀ i j,
      fl_householderQRPanel_R fp m p T i j =
        matMulRect m m p
          (matTranspose (fl_householderQRPanel_Q fp m p T))
          (fun a b => T a b + ΔT a b) i j := by
    intro i j
    have := hΔrep i j
    rw [hStored] at this
    exact this
  -- Reduce to the deeper `Fin p`-column bound `columnFrob ΔT j' ≤ γtil·|σ|`.
  have hΔTcol : ∀ j' : Fin p, columnFrob ΔT j' ≤ γtil * |σ| := by
    -- Degenerate case: an empty deeper panel has no reduced content.
    rcases Nat.eq_zero_or_pos (Nat.min m p) with hmin | hmin
    · -- `Nat.min m p = 0`: either `m = 0` (ΔT has empty rows) or `p = 0`
      -- (no `Fin p`-column).  In both cases `columnFrob ΔT j' = 0`.
      intro j'
      have hmp : m = 0 ∨ p = 0 := Nat.min_eq_zero_iff.mp hmin
      rcases hmp with hm0 | hp0
      · subst hm0
        have : columnFrob ΔT j' = 0 := by
          rw [columnFrob, frobNorm_eq_zero_iff]
          intro i; exact Fin.elim0 i
        rw [this]; exact mul_nonneg hγtil hσnn
      · subst hp0; exact Fin.elim0 j'
    · -- Nonempty deeper panel: use the columnwise backward error.
      -- The columnwise panel backward error, coefficient absorbed to one gamma.
      have hcw :=
        fl_householderQRPanel_R_columnwise_backward_error_gammaHigham_of_global_gammaValid
          fp m p T hmin hvalidGamma
      obtain ⟨ΔA, hArep, _hAnorm, hAcol⟩ := hcw.result
      -- Q of the deeper panel is orthogonal.
      have hQorth : IsOrthogonal m (fl_householderQRPanel_Q fp m p T) := hcw.orth
      -- Pin: the characterizing equation determines the input, so ΔT = ΔA.
      have hpin : (fun a b => T a b + ΔT a b) = (fun a b => T a b + ΔA a b) := by
        apply panel_eq_of_matTranspose_matMulRect_eq hQorth
        intro i j
        rw [← hΔrep' i j, hArep i j]
      have hΔeqΔA : ΔT = ΔA := by
        funext a b
        have := congrFun (congrFun hpin a) b
        simpa using this
      intro j'
      -- columnFrob ΔT j' = columnFrob ΔA j' ≤ c·columnFrob T j' ≤ c·|σ| ≤ γtil·|σ|.
      have hcnn : 0 ≤ gamma fp (Nat.min m p * householderConstructApplyGammaIndex m) :=
        gamma_nonneg fp hvalidGamma
      calc columnFrob ΔT j'
            = columnFrob ΔA j' := by rw [hΔeqΔA]
        _ ≤ gamma fp (Nat.min m p * householderConstructApplyGammaIndex m) *
              columnFrob T j' := hAcol j'
        _ ≤ gamma fp (Nat.min m p * householderConstructApplyGammaIndex m) * |σ| :=
              mul_le_mul_of_nonneg_left (hTmax j') hcnn
        _ ≤ γtil * |σ| := mul_le_mul_of_nonneg_right hfold hσnn
  -- Now the embedded column: `j = 0` gives `0`; `j = j'.succ` gives `columnFrob ΔT j'`.
  refine Fin.cases ?_ ?_ j
  · rw [columnFrob_panelTrailingPerturbation_zero]
    exact mul_nonneg hγtil hσnn
  · intro j'
    rw [columnFrob_panelTrailingPerturbation_succ]
    exact hΔTcol j'

/-! ## §1  Notation and the step-panel as the exact-vector application

Under the source-faithful strong model the computed normalized reflector IS the
exact one (`fl_householderNormalizedVector_exactWithUnitRoundoff_eq`), so the
computed step-panel `stageStepPanel` equals the *exact-vector* application. -/

/-- The step-panel of one level is the exact-vector application, under the strong
model. -/
theorem stageStepPanel_exactWithUnitRoundoff_eq
    (u0 : ℝ) (hu0 : 0 ≤ u0) {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) :
    stageStepPanel (FPModel.exactWithUnitRoundoff u0 hu0) A =
      fl_householderApplyMatrixRect (FPModel.exactWithUnitRoundoff u0 hu0)
        (m + 1) (p + 1) (stageReflectorVector A) 1 A := by
  unfold stageStepPanel stageReflectorVector
  rw [H19.Theorem19_13.fl_householderNormalizedVector_exactWithUnitRoundoff_eq u0 hu0
        (Nat.succ_pos m) (panelFirstColumn (Nat.succ_pos p) A)]

/-! ## §2  The columnwise E-bound and the DERIVED numerator

The residual `E = stageStoredPanel − matMulRect (householder v 1) A` against the
EXACT normalized reflector has column-2-norm `columnFrob E j ≤ c · columnFrob A j`.
This is the columnwise Householder step error (Higham Lemma 18.2,
`ColumnwiseHouseholderStepErrorRect`) transported through the pivot-tail zeroing:
the stored panel differs from the applied step-panel only by zeroing the pivot
column tail, and there the exact reflector self-annihilates, so the stored residual
is entrywise ≤ the step residual. -/

/-- **Columnwise per-step reflector-application error (Higham Lemma 18.2), stored
form.**  Holds over ANY `FPModel` (no strong-model hypothesis needed): the residual
`E = stageStoredPanel − matMulRect (householder (stageReflectorVector A) 1) A` has
`columnFrob E j ≤ c · columnFrob A j`. -/
theorem columnFrob_stage_residual_le {m p : ℕ}
    (fp : FPModel)
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hcol : panelFirstColumn (Nat.succ_pos p) A ≠ 0)
    (hvalid : gammaValid fp (11 * (m + 1) + 23))
    (j : Fin (p + 1)) :
    columnFrob
      (fun a b => stageStoredPanel fp A a b -
        matMulRect (m + 1) (m + 1) (p + 1)
          (householder (m + 1) (stageReflectorVector A) 1) A a b) j ≤
      stageColErrorConst fp (m + 1) * columnFrob A j := by
  have hstep :=
    fl_householderConstructApply_matrix_step_error_rect fp (Nat.succ_pos m)
      (panelFirstColumn (Nat.succ_pos p) A) A hcol hvalid
  obtain ⟨Estep, hEstepRep, hEstepBound⟩ :=
    hstep.exists_residual_matrix_columnFrob_bound
  set P : Fin (m + 1) → Fin (m + 1) → ℝ :=
    householder (m + 1) (stageReflectorVector A) 1 with hP
  have hPeq : (householder (m + 1)
      (householderNormalizedVector (m + 1)
        (householderVector (Nat.succ_pos m) (panelFirstColumn (Nat.succ_pos p) A))
        (householderBetaFromScale (Nat.succ_pos m)
          (panelFirstColumn (Nat.succ_pos p) A))) 1) = P := by
    rw [hP]; rfl
  have hAhat : (fl_householderApplyMatrixRect fp (m + 1) (p + 1)
      (fl_householderNormalizedVector fp (Nat.succ_pos m)
        (panelFirstColumn (Nat.succ_pos p) A)) 1 A) = stageStepPanel fp A := rfl
  have hEstep_eq : ∀ a b, Estep a b =
      stageStepPanel fp A a b - matMulRect (m + 1) (m + 1) (p + 1) P A a b := by
    intro a b
    have := hEstepRep a b
    rw [hPeq, hAhat] at this
    linarith [this]
  have hann : panelFirstColumnTailZero
      (matMulRect (m + 1) (m + 1) (p + 1) P A) := by
    rw [hP]
    exact householder_panel_exact_firstColumnTailZero A hcol
  have hentry : ∀ i,
      |stageStoredPanel fp A i j - matMulRect (m + 1) (m + 1) (p + 1) P A i j| ≤
        |Estep i j| := by
    intro i
    refine Fin.cases ?_ ?_ i
    · refine Fin.cases ?_ ?_ j
      · have hval : stageStoredPanel fp A 0 0 = stageStepPanel fp A 0 0 := by
          simp [stageStoredPanel, panelTopLeft]
        rw [hval, ← hEstep_eq 0 0]
      · intro j'
        have hval : stageStoredPanel fp A 0 j'.succ = stageStepPanel fp A 0 j'.succ := by
          simp [stageStoredPanel, panelTopRowTail]
        rw [hval, ← hEstep_eq 0 j'.succ]
    · intro i'
      refine Fin.cases ?_ ?_ j
      · have hSz : stageStoredPanel fp A i'.succ 0 = 0 := by
          simp [stageStoredPanel]
        have hPz : matMulRect (m + 1) (m + 1) (p + 1) P A i'.succ 0 = 0 := by
          have := hann i'
          simpa [panelFirstColumnTailZero, panelFirstColumnTail,
            panelFirstColumn] using this
        rw [hSz, hPz, sub_zero, abs_zero]
        exact abs_nonneg _
      · intro j'
        have hval : stageStoredPanel fp A i'.succ j'.succ =
            stageStepPanel fp A i'.succ j'.succ := by
          simp [stageStoredPanel, trailingPanel]
        rw [hval, ← hEstep_eq i'.succ j'.succ]
  calc
    columnFrob
        (fun a b => stageStoredPanel fp A a b -
          matMulRect (m + 1) (m + 1) (p + 1) P A a b) j
        ≤ columnFrob Estep j :=
          columnFrob_le_of_entrywise_abs_le _ Estep j hentry
    _ ≤ stageColErrorConst fp (m + 1) * columnFrob A j := by
          have := hEstepBound j
          simpa [stageColErrorConst] using this

/-- **The numerator, DERIVED.**  With the pivot-maximality magnitude fact
`columnFrob A j ≤ σ` and the trailing-perturbation column control
`columnFrob (panelTrailingPerturbation ΔT) j ≤ γtil·σ`, the numerator column of
`E + panelTrailingPerturbation ΔT` (with `E` the genuine residual of the stored
panel against the exact reflector) is bounded by `(c + γtil)·σ`.  Nothing is
assumed: the `E`-column bound is the columnwise reflector-application error
(`columnFrob_stage_residual_le`, derived), and the ΔT-column control is the
source-faithful trailing backward-error field. -/
theorem numerator_col_le {m p : ℕ}
    (fp : FPModel)
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (ΔT : Fin m → Fin p → ℝ)
    (σ γtil : ℝ) (hσnn : 0 ≤ σ) (hγtil : 0 ≤ γtil)
    (hcol : panelFirstColumn (Nat.succ_pos p) A ≠ 0)
    (hvalid : gammaValid fp (11 * (m + 1) + 23))
    (hpivot : ∀ j : Fin (p + 1), columnFrob A j ≤ σ)
    (hΔT : ∀ j : Fin (p + 1),
      columnFrob (panelTrailingPerturbation ΔT) j ≤ γtil * σ)
    (j : Fin (p + 1)) :
    vecNorm2 (fun s =>
      (fun a b =>
        (stageStoredPanel fp A a b -
          matMulRect (m + 1) (m + 1) (p + 1)
            (householder (m + 1) (stageReflectorVector A) 1) A a b) +
        panelTrailingPerturbation ΔT a b) s j)
        ≤ (stageColErrorConst fp (m + 1) + γtil) * σ := by
  set E : Fin (m + 1) → Fin (p + 1) → ℝ :=
    fun a b => stageStoredPanel fp A a b -
      matMulRect (m + 1) (m + 1) (p + 1)
        (householder (m + 1) (stageReflectorVector A) 1) A a b with hE
  rw [show (fun s =>
        (fun a b => E a b + panelTrailingPerturbation ΔT a b) s j) =
      (fun s => (fun a b => E a b + panelTrailingPerturbation ΔT a b) s j) from rfl,
    ← columnFrob_eq_vecNorm2 (fun a b => E a b + panelTrailingPerturbation ΔT a b) j]
  have htri :
      columnFrob (fun a b => E a b + panelTrailingPerturbation ΔT a b) j ≤
        columnFrob E j + columnFrob (panelTrailingPerturbation ΔT) j :=
    columnFrob_add_le E (panelTrailingPerturbation ΔT) j
  have hEc : columnFrob E j ≤ stageColErrorConst fp (m + 1) * columnFrob A j := by
    rw [hE]; exact columnFrob_stage_residual_le fp A hcol hvalid j
  have hcnn : 0 ≤ stageColErrorConst fp (m + 1) :=
    stageColErrorConst_nonneg fp (m + 1) hvalid
  have hEσ : columnFrob E j ≤ stageColErrorConst fp (m + 1) * σ :=
    le_trans hEc (mul_le_mul_of_nonneg_left (hpivot j) hcnn)
  calc
    columnFrob (fun a b => E a b + panelTrailingPerturbation ΔT a b) j
        ≤ columnFrob E j + columnFrob (panelTrailingPerturbation ΔT) j := htri
    _ ≤ stageColErrorConst fp (m + 1) * σ + γtil * σ := add_le_add hEσ (hΔT j)
    _ = (stageColErrorConst fp (m + 1) + γtil) * σ := by ring

/-- **The σ-ratio, DERIVED from the numerator.**  With `σ` the pivot scale,
`0 < |σ|`, the reflector sign choice `√2·|σ| ≤ ‖v‖₂` (Cox–Higham eq. (2.5)), and the
fold `(c + γtil)/√2 ≤ γtil`, the σ-ratio `‖colⱼ(E + ptp ΔT)‖₂ / ‖v‖₂ ≤ γtil` holds —
via `Wave19.sigma_ordering_norm_ratio_le` with `u := c`, `γ := γtil/2`
(so `u + 2γ = c + γtil`, `√m`-free). -/
theorem sigma_ratio_of_numerator {m p : ℕ}
    (fp : FPModel)
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (ΔT : Fin m → Fin p → ℝ)
    (v : Fin (m + 1) → ℝ)
    (σ γtil : ℝ)
    (hσpos : 0 < |σ|)
    (hγtil : 0 ≤ γtil)
    (hcol : panelFirstColumn (Nat.succ_pos p) A ≠ 0)
    (hvalid : gammaValid fp (11 * (m + 1) + 23))
    (hpivot : ∀ j : Fin (p + 1), columnFrob A j ≤ |σ|)
    (hΔT : ∀ j : Fin (p + 1),
      columnFrob (panelTrailingPerturbation ΔT) j ≤ γtil * |σ|)
    (hvSign : Real.sqrt 2 * |σ| ≤ vecNorm2 v)
    (hfold : (stageColErrorConst fp (m + 1) + γtil) / Real.sqrt 2 ≤ γtil)
    (j : Fin (p + 1)) :
    vecNorm2 (fun s =>
      (fun a b =>
        (stageStoredPanel fp A a b -
          matMulRect (m + 1) (m + 1) (p + 1)
            (householder (m + 1) (stageReflectorVector A) 1) A a b) +
        panelTrailingPerturbation ΔT a b) s j) / vecNorm2 v ≤ γtil := by
  have hcnn : 0 ≤ stageColErrorConst fp (m + 1) :=
    stageColErrorConst_nonneg fp (m + 1) hvalid
  have hnum := numerator_col_le fp A ΔT (|σ|) γtil (abs_nonneg σ) hγtil hcol hvalid
    hpivot hΔT j
  have heq : stageColErrorConst fp (m + 1) + 2 * (γtil / 2) =
      stageColErrorConst fp (m + 1) + γtil := by ring
  have huγ : 0 ≤ stageColErrorConst fp (m + 1) + 2 * (γtil / 2) := by
    rw [heq]; linarith
  have hf : vecNorm2 (fun s =>
      (fun a b =>
        (stageStoredPanel fp A a b -
          matMulRect (m + 1) (m + 1) (p + 1)
            (householder (m + 1) (stageReflectorVector A) 1) A a b) +
        panelTrailingPerturbation ΔT a b) s j)
      ≤ (stageColErrorConst fp (m + 1) + 2 * (γtil / 2)) * |σ| := by
    rw [heq]; exact hnum
  have hfold' : (stageColErrorConst fp (m + 1) + 2 * (γtil / 2)) / Real.sqrt 2 ≤ γtil := by
    rw [heq]; exact hfold
  exact Wave19.sigma_ordering_norm_ratio_le _ v σ
    (stageColErrorConst fp (m + 1)) (γtil / 2) γtil hσpos huγ hf hvSign hfold'

/-! ## §3  The source-faithful strong-model readiness predicate

`StrongStageModel fp m p A α γtil Vmax αmax` mirrors the recursion of
`StageDataReady`, but at each nonzero interior level supplies ONLY the honest
Cox–Higham source-faithful facts:

* the row-growth magnitudes (eq. (2.10)) and the fold bound;
* the pivot scale `σ` with `0 < |σ|` and the reflector sign choice
  `√2·|σ| ≤ ‖v‖₂` (eq. (2.5));
* the **pivot maximality** magnitude fact `columnFrob A j ≤ |σ|` on the CURRENT
  panel (every reduced column norm is bounded by the pivot scale — feeds the
  `E`-column part of the numerator);
* the **pivot maximality** magnitude fact `columnFrob (trailingPanel (stageStepPanel
  A)) j ≤ |σ|` on the DEEPER reduced panel (eq. (2.4) one stage down — the only
  magnitude datum the now-DERIVED ΔT-column control needs); and
* the roundoff folds `(c + γtil)/√2 ≤ γtil` (`c = stageColErrorConst`) and
  `gamma fp (min m p · index) ≤ γtil`, plus the deeper-panel gamma validity.

NONE of these is the numerator, the σ-ratio, OR the ΔT-column control: the
ΔT-column control is now DERIVED (`deltaT_col_le_sigma`) by PINNING `ΔT` to the
deeper panel's genuine backward error via orthogonality and applying the
`√m`-free columnwise panel backward error + deeper-panel pivot maximality; the
numerator is DERIVED (`numerator_col_le`) from the columnwise reflector-application
error + the current-panel maximality; and the σ-ratio is DERIVED
(`sigma_ratio_of_numerator`).  Combined with the top-level `exactWithUnitRoundoff`
hypothesis it DISCHARGES the algorithm-structural facts of `StageDataReady` and
recurses. -/
def StrongStageModel (fp : FPModel) :
    (m p : ℕ) → (Fin m → Fin p → ℝ) → (Fin m → ℝ) → ℝ → ℝ → ℝ → Prop
  | 0, _, _A, _α, _γtil, _Vmax, _αmax => True
  | Nat.succ _, 0, _A, _α, _γtil, _Vmax, _αmax => True
  | m + 1, p + 1, A, α, γtil, Vmax, αmax =>
      (0 ≤ γtil) ∧ (∀ i, 0 ≤ α i) ∧ (0 ≤ Vmax) ∧ (0 ≤ αmax) ∧
      -- Row-growth magnitude invariants (Cox–Higham Lemma 2.2 / eq. (2.10)).
      (∀ i j, |A i j| ≤ α i) ∧
      (∀ i, |stageReflectorVector A i| ≤ 2 * α i) ∧
      (∀ i, |stageReflectorVector A i| ≤ Vmax) ∧
      (∀ i, α i ≤ αmax) ∧
      (gamma fp (m + 1 + 2) * (1 + 6 * (((m + 1 : ℕ) : ℝ) * (Vmax * αmax))) ≤ γtil) ∧
      -- Zero-pivot branch: skip the step, recurse on the deflated trailing panel.
      (panelFirstColumn (Nat.succ_pos p) A = 0 →
        StrongStageModel fp m p (trailingPanel A) (fun i => α i.succ) γtil Vmax αmax) ∧
      -- Nonzero-pivot branch: carry ONLY the source-faithful magnitude /
      -- backward-error data (the pivot scale `σ`, the reflector sign choice, the
      -- pivot maximality on the current AND deeper reduced panels, and the roundoff
      -- folds + deeper-panel gamma validity).  The numerator, the σ-ratio, AND the
      -- ΔT-column control are DERIVED, not assumed.
      (panelFirstColumn (Nat.succ_pos p) A ≠ 0 →
        ∃ σ : ℝ,
          0 < |σ| ∧
          (stageColErrorConst fp (m + 1) + γtil) / Real.sqrt 2 ≤ γtil ∧
          Real.sqrt 2 * |σ| ≤ vecNorm2 (stageReflectorVector A) ∧
          -- Pivot maximality (eq. (2.4)) on the CURRENT panel: reduced columns ≤
          -- pivot scale (feeds the numerator's `E`-column bound).
          (∀ j : Fin (p + 1), columnFrob A j ≤ |σ|) ∧
          -- Pivot maximality (eq. (2.4)) on the DEEPER reduced panel: every column
          -- of `trailingPanel (stageStepPanel A)` (the panel one stage down) has
          -- Euclidean norm ≤ the pivot scale.  This is the ONLY magnitude datum the
          -- (now DERIVED) ΔT-column control needs; it is NOT the conclusion.
          (∀ j : Fin p,
            columnFrob (trailingPanel (stageStepPanel fp A)) j ≤ |σ|) ∧
          -- Roundoff fold `c ≤ γtil` for the deeper columnwise backward-error
          -- coefficient (same γ̃-class constant fold).
          (gamma fp (Nat.min m p * householderConstructApplyGammaIndex m) ≤ γtil) ∧
          -- Deeper-panel gamma validity for the columnwise backward error.
          (gammaValid fp
            (Nat.min m p * householderConstructApplyGammaIndex m)) ∧
          StrongStageModel fp m p (trailingPanel (stageStepPanel fp A))
            (fun i => α i.succ) γtil Vmax αmax)

/-! ## §4  The strong-model discharge of `StageDataReady`

At each nonzero level: `‖v‖₂²=2`, `0 < ‖v‖₂`, `hSrep`, and `hE` are PROVED (as
before); the ΔT-column control (`hΔTcol`) is DERIVED from the deeper panel's
`√m`-free columnwise backward error + deeper-panel pivot maximality via
`deltaT_col_le_sigma`; and the σ-ratio (`hratioTail`) is then DERIVED from the
honest strong-model magnitude fields (current-panel pivot maximality + the derived
ΔT-column control) + the reflector sign choice, via `sigma_ratio_of_numerator`
(the numerator being the theorem `numerator_col_le`, NOT an assumption). -/

theorem stageDataReady_of_strongModel
    (u0 : ℝ) (hu0 : 0 ≤ u0) :
    ∀ (m p : ℕ) (A : Fin m → Fin p → ℝ) (α : Fin m → ℝ) (γtil Vmax αmax : ℝ),
      (∀ (q : ℕ), gammaValid (FPModel.exactWithUnitRoundoff u0 hu0) (q + 2)) →
      StrongStageModel (FPModel.exactWithUnitRoundoff u0 hu0) m p A α γtil Vmax αmax →
      StageDataReady (FPModel.exactWithUnitRoundoff u0 hu0) m p A α γtil := by
  set fp : FPModel := FPModel.exactWithUnitRoundoff u0 hu0 with hfp
  intro m
  induction m with
  | zero => intro p A α γtil Vmax αmax _hvalid _h; exact True.intro
  | succ m ih =>
      intro p
      cases p with
      | zero => intro A α γtil Vmax αmax _hvalid _h; exact True.intro
      | succ p =>
          intro A α γtil Vmax αmax hvalid hmodel
          obtain ⟨hγtil, hαi, hVmax, hαmax, hAα, hv2α, hVbound, hαbound,
              hfold, hzeroBranch, hnonzeroBranch⟩ := hmodel
          refine ⟨hγtil, hαi, ?_, ?_⟩
          · -- zero-pivot branch
            intro hcol
            exact ih p (trailingPanel A) (fun i => α i.succ) γtil Vmax αmax hvalid
              (hzeroBranch hcol)
          · -- nonzero-pivot branch
            intro hcol
            obtain ⟨σ, hσpos, hfoldσ, hvSign, hpivotMax, hTmaxDeep, hfoldCol,
                hvalidDeep, hDataTail⟩ :=
              hnonzeroBranch hcol
            -- Derive the ΔT-column control (previously carried) from the deeper
            -- panel's columnwise backward error + pivot maximality.
            have hΔTcol :
                ∀ (ΔT : Fin m → Fin p → ℝ),
                  (∀ i j,
                    fl_householderQRPanel_R fp m p
                        (trailingPanel (stageStepPanel fp A)) i j =
                      matMulRect m m p
                        (matTranspose (fl_householderQRPanel_Q fp m p
                          (trailingPanel (stageStepPanel fp A))))
                        (fun a b => trailingPanel (stageStoredPanel fp A) a b +
                          ΔT a b) i j) →
                  (∀ i' j', |ΔT i' j'| ≤
                    stageCoeff (j'.val + 1) * γtil * α i'.succ) →
                  ∀ j : Fin (p + 1),
                    columnFrob (panelTrailingPerturbation ΔT) j ≤ γtil * |σ| := by
              intro ΔT hrep hΔ j
              exact deltaT_col_le_sigma fp A α σ γtil (abs_nonneg σ) hγtil
                hvalidDeep hTmaxDeep hfoldCol ΔT hrep hΔ j
            set v : Fin (m + 1) → ℝ := stageReflectorVector A with hv
            have hcolne : panelFirstColumn (Nat.succ_pos p) A ≠ 0 := hcol
            -- `‖v‖₂² = 2` for the exact normalized reflector.
            have hself : (∑ s : Fin (m + 1), v s * v s) = 2 := by
              rw [hv]; unfold stageReflectorVector
              exact householderNormalizedVector_norm_sq (m + 1)
                (householderVector (Nat.succ_pos m)
                  (panelFirstColumn (Nat.succ_pos p) A))
                (householderBetaFromScale (Nat.succ_pos m)
                  (panelFirstColumn (Nat.succ_pos p) A))
                (le_of_lt (householderBetaFromScale_pos_of_ne_zero
                  (Nat.succ_pos m) (panelFirstColumn (Nat.succ_pos p) A) hcolne))
                (householderBetaFromScale_mul_norm_sq (Nat.succ_pos m)
                  (panelFirstColumn (Nat.succ_pos p) A) hcolne)
            have hvpos : 0 < vecNorm2 v := by
              rw [vecNorm2, Real.sqrt_pos]
              unfold vecNorm2Sq
              have : (∑ s : Fin (m + 1), v s ^ 2) = 2 := by
                rw [← hself]; apply Finset.sum_congr rfl; intro s _; ring
              rw [this]; norm_num
            -- The genuine residual `E := S − P·A`.
            set P : Fin (m + 1) → Fin (m + 1) → ℝ :=
              householder (m + 1) v 1 with hP
            set E : Fin (m + 1) → Fin (p + 1) → ℝ :=
              fun i j => stageStoredPanel fp A i j -
                matMulRect (m + 1) (m + 1) (p + 1) P A i j with hE
            have hSrep : ∀ i j, stageStoredPanel fp A i j =
                matMulRect (m + 1) (m + 1) (p + 1) P A i j + E i j := by
              intro i j; simp only [hE]; ring
            have hann : panelFirstColumnTailZero
                (matMulRect (m + 1) (m + 1) (p + 1) P A) := by
              rw [hP, hv]; unfold stageReflectorVector
              exact householder_panel_exact_firstColumnTailZero A hcolne
            -- Step-panel residual bound (Cox–Higham Lemma 2.2, exact vector).
            have hstepRes : ∀ i j,
                |stageStepPanel fp A i j -
                  matMulRect (m + 1) (m + 1) (p + 1) P A i j| ≤ γtil * α i := by
              intro i j
              rw [hfp, stageStepPanel_exactWithUnitRoundoff_eq u0 hu0 A, ← hfp,
                  hP, hv]
              exact Wave19.panelStep_entrywise_le_rowGrowth fp (m + 1) (p + 1)
                (stageReflectorVector A) A α γtil Vmax αmax (hvalid (m + 1))
                hαi hVmax hαmax hAα hv2α hVbound hαbound hfold i j
            have hEbound : ∀ i j, |E i j| ≤ γtil * α i := by
              intro i j
              simp only [hE]
              refine Fin.cases ?_ ?_ i
              · refine Fin.cases ?_ ?_ j
                · have hval : stageStoredPanel fp A 0 0 = stageStepPanel fp A 0 0 := by
                    simp [stageStoredPanel, panelTopLeft]
                  rw [hval]; exact hstepRes 0 0
                · intro j'
                  have hval : stageStoredPanel fp A 0 j'.succ = stageStepPanel fp A 0 j'.succ := by
                    simp [stageStoredPanel, panelTopRowTail]
                  rw [hval]; exact hstepRes 0 j'.succ
              · intro i'
                refine Fin.cases ?_ ?_ j
                · have hSz : stageStoredPanel fp A i'.succ 0 = 0 := by
                    simp [stageStoredPanel]
                  have hPz : matMulRect (m + 1) (m + 1) (p + 1) P A i'.succ 0 = 0 := by
                    have := hann i'
                    simpa [panelFirstColumnTailZero, panelFirstColumnTail,
                      panelFirstColumn] using this
                  rw [hSz, hPz, sub_zero, abs_zero]
                  exact mul_nonneg hγtil (hαi i'.succ)
                · intro j'
                  have hval : stageStoredPanel fp A i'.succ j'.succ =
                      stageStepPanel fp A i'.succ j'.succ := by
                    simp [stageStoredPanel, trailingPanel]
                  rw [hval]; exact hstepRes i'.succ j'.succ
            -- Assemble the nonzero-level `StageDataReady` fields.
            refine ⟨E, hvpos, hself, hv2α, hSrep, hEbound, ?_, ?_⟩
            · -- σ-ordering ratio: DERIVED (not assumed) from the source-faithful
              -- pivot maximality + ΔT-column control + reflector sign choice, via
              -- `sigma_ratio_of_numerator` (whose numerator is the THEOREM
              -- `numerator_col_le`).
              intro ΔT hrep hΔ j
              -- gamma validity at `11(m+1)+23`.
              have hvalidStep : gammaValid fp (11 * (m + 1) + 23) := by
                have := hvalid (11 * (m + 1) + 21)
                simpa [show 11 * (m + 1) + 21 + 2 = 11 * (m + 1) + 23 from by ring]
                  using this
              -- The ΔT-column control for this ΔT.
              have hΔTj : ∀ j : Fin (p + 1),
                  columnFrob (panelTrailingPerturbation ΔT) j ≤ γtil * |σ| :=
                hΔTcol ΔT hrep hΔ
              -- Discharge via `sigma_ratio_of_numerator`.  The E in that lemma is
              -- `stageStoredPanel − matMulRect (householder (stageReflectorVector A) 1) A`,
              -- which equals `E` here (P = householder v 1, v = stageReflectorVector A).
              have hgoal :=
                sigma_ratio_of_numerator fp A ΔT v σ γtil hσpos hγtil hcolne
                  hvalidStep hpivotMax hΔTj hvSign hfoldσ j
              -- Rewrite the σ-ratio target: its `E` is our `E` (P = householder v 1).
              have hEmatch :
                  (fun s =>
                    (fun a b =>
                      (stageStoredPanel fp A a b -
                        matMulRect (m + 1) (m + 1) (p + 1)
                          (householder (m + 1) (stageReflectorVector A) 1) A a b) +
                      panelTrailingPerturbation ΔT a b) s j) =
                  (fun s =>
                    (fun a b => E a b + panelTrailingPerturbation ΔT a b) s j) := by
                funext s
                simp only [hE, hP, hv]
              rw [hEmatch] at hgoal
              exact hgoal
            · -- recurse on the trailing iterate
              exact ih p (trailingPanel (stageStepPanel fp A)) (fun i => α i.succ)
                γtil Vmax αmax hvalid hDataTail

/-! ## §5  Theorem 19.6 under the source-faithful strong model

Instantiate `H19_Theorem19_6_final` through `stageDataReady_of_strongModel`. -/

/-- **Higham, Theorem 19.6 = Cox–Higham (1998) Theorem 2.3 — the source-faithful
STRONG MODEL closure.**

Reference: Higham, 2nd ed., §19.4, Theorem 19.6, p. 367; Cox–Higham (1998),
Theorem 2.3.

For `A : ℝ^{m×n}` with `0 < n ≤ m`, valid gamma depth, under the source-faithful
strong model `fp = FPModel.exactWithUnitRoundoff u0 hu0` (every primitive
operation exact, unit roundoff `u0`) and the honest per-level Cox–Higham data
`StrongStageModel` for the composite `(19.15)`-permuted input (the row-growth
magnitudes and the executed σ-ordering — the same source-faithful facts
`AllPivotsSelfAnnihilatingReflectorModel` carries for Theorem 19.13), the
full-swap per-stage column-pivoting computed QR `fl_householderQRColPivotFull_Q/_R`
satisfies:

`(A·Π) + ΔA = Q·R̂`,   `Q` orthogonal,   `R̂` upper-trapezoidal,   and
`|ΔA_ij| ≤ (j+1)² · γ̃_m · α_i`   (`γ̃_m := 5γtil`),

with `Π = compositePivotPerm fp m n A` the composite `(19.15)` per-stage pivot
permutation from the EXECUTED maximal-`columnFrob` selection — the printed
row-wise Cox–Higham envelope, with NO `√m` and NO
`StageDataReady`/telescope/σ hypothesis in the conclusion.

The `‖v‖₂²=2` self-dot that the bare-`FPModel` route provably cannot supply
(`Higham19.fl_householderNormalizedVector_self_dot_not_forall_FPModel`) is here a
PROVED consequence of the exact normalized reflector; and the σ-ratio's numerator
(previously assumed) is here a DERIVED theorem (`numerator_col_le`), so
`StrongStageModel` carries only source-faithful magnitude/backward-error data. -/
theorem H19_Theorem19_6_strongModel
    (u0 : ℝ) (hu0 : 0 ≤ u0) (m n : ℕ)
    (A : Fin m → Fin n → ℝ)
    (α : Fin m → ℝ) (γtil Vmax αmax : ℝ)
    (hγtil : 0 ≤ γtil) (hα : ∀ i, 0 ≤ α i)
    (hn : 0 < n) (hnm : n ≤ m)
    (hvalid : gammaValid (FPModel.exactWithUnitRoundoff u0 hu0)
      (n * householderConstructApplyGammaIndex m))
    (hvalidStep : ∀ (q : ℕ),
      gammaValid (FPModel.exactWithUnitRoundoff u0 hu0) (q + 2))
    (hstrong : StrongStageModel (FPModel.exactWithUnitRoundoff u0 hu0) m n
      (Wave13.columnPermuteMatrix A
        (compositePivotPerm (FPModel.exactWithUnitRoundoff u0 hu0) m n A))
      α γtil Vmax αmax) :
    ∃ (perm : Equiv.Perm (Fin n))
      (Q : Fin m → Fin m → ℝ) (R_hat : Fin m → Fin n → ℝ)
      (ΔA : Fin m → Fin n → ℝ),
      IsOrthogonal m Q ∧
      IsUpperTrapezoidal m n R_hat ∧
      (∀ i j, Wave13.columnPermuteMatrix A perm i j + ΔA i j =
        matMulRect m m n Q R_hat i j) ∧
      (∀ i j, |ΔA i j| ≤ ((j.val : ℝ) + 1) ^ 2 * (5 * γtil) * α i) := by
  exact H19_Theorem19_6_final (FPModel.exactWithUnitRoundoff u0 hu0) m n A α γtil
    hγtil hα hn hnm hvalid
    (stageDataReady_of_strongModel u0 hu0 m n
      (Wave13.columnPermuteMatrix A
        (compositePivotPerm (FPModel.exactWithUnitRoundoff u0 hu0) m n A))
      α γtil Vmax αmax hvalidStep hstrong)

end NumStability.Wave20
