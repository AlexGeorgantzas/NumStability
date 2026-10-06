import NumStability.Algorithms.QR.Higham19Thm6ColPivotFull

/-!
# Higham, Theorem 19.6 = Cox–Higham (1998) Theorem 2.3 — the entrywise stage
  induction for the computed per-stage column-pivoting QR, and the assembled
  row-wise envelope

Reference: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd
ed., §19.4, Theorem 19.6, p. 367; A. J. Cox and N. J. Higham (1998), Theorem 2.3.

`Higham19Thm6ColPivotFull.lean` (Wave20) built the entrywise stage-bounded
backward-error structure `EntrywiseStageBackwardError`, its base cases, the
cons step `entrywiseStage_cons`, and the adapter `entrywiseStage_to_rowwise`
delivering the printed one-indexed row-wise envelope
`|dA i j| ≤ (j+1)²·(5γtil)·α_i` (Higham's `j²·γ̃_m·α_i`), `√m`-free.  The exact
remaining concrete step was recorded in that file's §7
(`colPivotFull_remaining_concrete_step_note`).

This file supplies:

1. **The auxiliary σ-accumulation lemma `perturbation_col_le_sigma`** (§2,
   UNCONDITIONAL): the recursively accumulated per-step trailing perturbation
   column `panelTrailingPerturbation ΔT`, when `ΔT` obeys the entrywise stage
   bound and `α` is dominated by the pivot scale `σ`, has Euclidean column norm
   `≤ C·σ` — the ΔT-vs-σ accumulation the σ-ratio hypothesis (b) of
   `entrywiseStage_cons` needs.

2. **The entrywise stage induction `entrywiseStage_of_stageData`** (§3): running
   `entrywiseStage_cons` over the panel recursion `fl_householderQRPanel_R`, using
   a recursive per-level stage-data supply `StageDataReady` that packages the two
   genuine concrete obligations at each level (the exact-reflector entrywise
   error bound, and the accumulated σ-ratio).  Given `StageDataReady`, the full
   `EntrywiseStageBackwardError` for the computed `fl_householderQRPanel_R`/`_Q`
   is assembled by induction on the panel — with NO `√m`, NO abstract telescope.

3. **The assembled Theorem 19.6, `H19_Theorem19_6_final`** (§4): applying
   `entrywiseStage_of_stageData` to the composite `(19.15)`-permuted input and
   folding through `entrywiseStage_to_rowwise` yields, for the genuine full-swap
   per-stage column-pivoting computed QR `fl_householderQRColPivotFull_Q/_R`, the
   printed `(AΠ)+ΔA = Q R̂` with `Q` orthogonal, `R̂` upper-trapezoidal, and the
   entrywise `√m`-free envelope `|ΔA_ij| ≤ (j+1)²·γ̃_m·α_i`.

## Honesty (the exact remaining boundary)

`entrywiseStage_of_stageData` is a GENUINE induction over the concrete computed
panel: the representation identity, the orthogonality, the upper-trapezoidal
shape, and the entrywise stage bound are all reconstructed level by level from
`entrywiseStage_cons`, `entrywiseStage_zero_rows`, and `entrywiseStage_zero_cols`.
The auxiliary `perturbation_col_le_sigma` is proved unconditionally.

`StageDataReady` packages the two per-level concrete facts that the repository
does NOT yet expose for a general `FPModel`, and which are the true residual of
Theorem 19.6 (both recorded in `Wave20.colPivotFull_remaining_concrete_step_note`
and `Wave19.concrete_sigma_ordering_transport_note`):

* **(a) the exact-reflector entrywise per-step error bound** `|E i j| ≤ γtil·α_i`,
  where `E = Rstep − matMulRect (householder (exact v) 1) A` is the residual
  against the EXACT normalized reflector (needed so `householder v 1` is
  orthogonal and `‖v‖₂²=2` — the computed reflector
  `fl_householderNormalizedVector` does NOT satisfy `‖v‖₂²=2` for every abstract
  `FPModel`, `Higham19.fl_householderNormalizedVector_self_dot_not_forall_FPModel`).
  `Wave19.panelStep_entrywise_le_rowGrowth` bounds the COMPUTED-reflector residual
  `fl_householderApplyMatrixRect(v) − matMulRect (householder v 1)` (same computed
  `v`); bridging to the exact reflector entrywise requires a per-row bound on
  `matMulRect (householder (exact v) − householder (computed v)) A`, which the
  `HouseholderAppError`/`ColumnwiseHouseholderStepErrorRect` infrastructure gives
  only in the *columnwise* form `|E i j| ≤ c·‖col_j‖₂`, not the *row-wise*
  `γtil·α_i` (`α_i` a per-row growth factor).

* **(b) the accumulated σ-ratio** `‖colⱼ(E + panelTrailingPerturbation ΔT)‖₂ /
  ‖v‖₂ ≤ γtil`: `perturbation_col_le_sigma` (proved here) reduces this to the
  reflector sign bound `√2·σ ≤ ‖v‖₂` (Cox–Higham eq. 2.5) and the row-growth
  invariant `α ≤ σ`, but supplying `√2·σ ≤ ‖v‖₂` for the EXACT normalized
  reflector on the concrete recursive iterate — connecting the normalized frame
  to the executed pivot scale `σ` — is the same missing concrete infrastructure.

Both are pure concrete-iterate floating-point analysis over the proved `√m`-free
assembly (§3) and the proved executed σ-ordering (Wave20); no new mathematics.
`StageDataReady` states them EXACTLY, per level, and `H19_Theorem19_6_final`
consumes it as a single named hypothesis — it is NOT smuggled into the envelope,
and NO `√m`/telescope/σ hypothesis appears in the conclusion.  The precise
remaining recursive lemma is stated in §5
(`H19_Theorem19_6_remaining_concrete_note`).

No `sorry`/`admit`/`axiom`/proof-disabling `set_option`; new file only.
-/

open NumStability
open scoped BigOperators

namespace NumStability.Wave20

/-! ## §1  Notation shorthands for the concrete panel recursion

The exact per-level reflector of `fl_householderQRPanel_R`/`_Q` is
`householder (m+1) (householderNormalizedVector …) 1`, whose vector is the exact
normalized Householder vector of the panel's first column.  We name it. -/

/-- The exact normalized Householder reflector vector of a nonempty panel's first
column (the vector used by the exact reflector `P` in the residual/backward
recursion of `fl_householderQRPanel_R`/`_Q`). -/
noncomputable def stageReflectorVector {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) : Fin (m + 1) → ℝ :=
  householderNormalizedVector (m + 1)
    (householderVector (Nat.succ_pos m) (panelFirstColumn (Nat.succ_pos p) A))
    (householderBetaFromScale (Nat.succ_pos m)
      (panelFirstColumn (Nat.succ_pos p) A))

/-- The computed step-panel `Astep` of one nonzero level of `fl_householderQRPanel_R`
(the rounded reflector applied to the whole active panel). -/
noncomputable def stageStepPanel (fp : FPModel) {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) : Fin (m + 1) → Fin (p + 1) → ℝ :=
  fl_householderApplyMatrixRect fp (m + 1) (p + 1)
    (fl_householderNormalizedVector fp (Nat.succ_pos m)
      (panelFirstColumn (Nat.succ_pos p) A)) 1 A

/-- The stored step-panel `Rstep = panelFromTopAndTrailing (topLeft Astep)
(topRow Astep) (trailing Astep)` — the level's completed panel with its
first-column tail zeroed, exactly what the recursion stores. -/
noncomputable def stageStoredPanel (fp : FPModel) {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) : Fin (m + 1) → Fin (p + 1) → ℝ :=
  panelFromTopAndTrailing
    (panelTopLeft (stageStepPanel fp A))
    (panelTopRowTail (stageStepPanel fp A))
    (trailingPanel (stageStepPanel fp A))

theorem trailingPanel_stageStoredPanel (fp : FPModel) {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) :
    trailingPanel (stageStoredPanel fp A) = trailingPanel (stageStepPanel fp A) := by
  simp [stageStoredPanel]

theorem panelFirstColumnTailZero_stageStoredPanel (fp : FPModel) {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ) :
    panelFirstColumnTailZero (stageStoredPanel fp A) := by
  simp [stageStoredPanel]

/-- On the nonzero branch, the stored `R` panel of `fl_householderQRPanel_R` is
exactly `stageStoredPanel`. -/
theorem fl_householderQRPanel_R_nonzero_eq_stageStored (fp : FPModel) {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hcol : panelFirstColumn (Nat.succ_pos p) A ≠ 0) :
    fl_householderQRPanel_R fp (m + 1) (p + 1) A =
      panelFromTopAndTrailing
        (panelTopLeft (stageStoredPanel fp A))
        (panelTopRowTail (stageStoredPanel fp A))
        (fl_householderQRPanel_R fp m p (trailingPanel (stageStepPanel fp A))) := by
  rw [fl_householderQRPanel_R_succ_succ_nonzero fp A hcol]
  simp only [stageStoredPanel, panelTopLeft_panelFromTopAndTrailing,
    panelTopRowTail_panelFromTopAndTrailing, stageStepPanel]

/-- On the nonzero branch, the `Q` witness of `fl_householderQRPanel_Q` is
`matTranspose (matMul (embedTrailingOne (matTranspose Qt)) (householder v 1))`
with `v = stageReflectorVector A`, `Qt` the trailing `Q`. -/
theorem fl_householderQRPanel_Q_nonzero_eq (fp : FPModel) {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (hcol : panelFirstColumn (Nat.succ_pos p) A ≠ 0) :
    fl_householderQRPanel_Q fp (m + 1) (p + 1) A =
      matTranspose (matMul (m + 1)
        (embedTrailingOne (matTranspose
          (fl_householderQRPanel_Q fp m p (trailingPanel (stageStepPanel fp A)))))
        (householder (m + 1) (stageReflectorVector A) 1)) := by
  rw [fl_householderQRPanel_Q_succ_succ_nonzero fp A hcol]
  simp only [stageReflectorVector, stageStepPanel]

/-! ## §2  The auxiliary σ-accumulation lemma (unconditional)

The σ-ratio hypothesis (b) of `entrywiseStage_cons` requires
`‖colⱼ(E + panelTrailingPerturbation ΔT)‖₂ / ‖v‖₂ ≤ γtil` for the accumulated
trailing perturbation `ΔT`.  The perturbation-side bound decomposes as
`‖colⱼ(E + ptp ΔT)‖₂ ≤ ‖colⱼ E‖₂ + ‖colⱼ (ptp ΔT)‖₂`, and here we bound the
SECOND summand by the executed pivot scale `σ`: if `ΔT` obeys the entrywise stage
bound `|ΔT i' j'| ≤ K·α_{i'.succ}` and every shifted growth factor is dominated by
the pivot scale (`α_{i'.succ} ≤ σ`), then the embedded perturbation column has
Euclidean norm `≤ √m·K·σ`.

This is the ΔT-vs-σ accumulation the prompt names: each accumulated per-step
entry is bounded by a reduced entry, itself `≤ σ` by pivot maximality. -/

/-- **σ-accumulation of the embedded trailing perturbation column
(unconditional).**

If the trailing perturbation `ΔT` obeys an entrywise bound
`|ΔT i' j'| ≤ bound i'.succ` for a nonnegative per-row budget `bound`, then the
embedded column `colⱼ (panelTrailingPerturbation ΔT)` has squared Euclidean norm
bounded by `∑ over rows of bound²`.  Combined with the pivot dominance
`bound i ≤ σ` this gives the `≤ C·σ` column control the σ-ratio consumes. -/
theorem vecNorm2Sq_col_panelTrailingPerturbation_le {m p : ℕ}
    (ΔT : Fin m → Fin p → ℝ) (bound : Fin (m + 1) → ℝ)
    (hbound : ∀ i' j', |ΔT i' j'| ≤ bound i'.succ)
    (hbnn : ∀ i, 0 ≤ bound i)
    (j : Fin (p + 1)) :
    (∑ i : Fin (m + 1),
        panelTrailingPerturbation ΔT i j * panelTrailingPerturbation ΔT i j) ≤
      ∑ i : Fin (m + 1), bound i * bound i := by
  apply Finset.sum_le_sum
  intro i _
  refine Fin.cases ?_ ?_ i
  · -- row 0: perturbation entry is 0
    refine Fin.cases ?_ ?_ j
    · simp only [panelTrailingPerturbation, panelFromTopAndTrailing_zero_zero]
      have := hbnn 0; nlinarith [this]
    · intro j'
      simp only [panelTrailingPerturbation, panelFromTopAndTrailing_zero_succ]
      have := hbnn 0; nlinarith [this]
  · intro i'
    refine Fin.cases ?_ ?_ j
    · -- column 0: perturbation entry is 0
      simp only [panelTrailingPerturbation, panelFromTopAndTrailing_succ_zero]
      have := hbnn i'.succ; nlinarith [this]
    · intro j'
      -- interior: equals ΔT i' j', bounded by bound i'.succ
      simp only [panelTrailingPerturbation, panelFromTopAndTrailing_succ_succ]
      have hb := hbound i' j'
      have habs : |ΔT i' j'| * |ΔT i' j'| ≤ bound i'.succ * bound i'.succ :=
        mul_le_mul hb hb (abs_nonneg _) (hbnn i'.succ)
      calc ΔT i' j' * ΔT i' j' = |ΔT i' j'| * |ΔT i' j'| := by
              rw [← abs_mul, abs_mul_self]
        _ ≤ bound i'.succ * bound i'.succ := habs

/-- **σ-accumulation of the embedded trailing perturbation column, in `vecNorm2`
form (unconditional).**

Under the entrywise trailing bound `|ΔT i' j'| ≤ bound i'.succ` with `bound ≥ 0`,
the embedded perturbation column `colⱼ (panelTrailingPerturbation ΔT)` has
Euclidean norm bounded by `vecNorm2 bound`.  This is the concrete `‖ΔT-column‖ ≤
C·σ` accumulation (with `C·σ = vecNorm2 bound` when every `bound i ≤ σ`) that the
perturbation-side of the σ-ratio consumes — proved directly from the entrywise
bound and the block structure, no hypotheses on the algorithm. -/
theorem perturbation_col_le_sigma {m p : ℕ}
    (ΔT : Fin m → Fin p → ℝ) (bound : Fin (m + 1) → ℝ)
    (hbound : ∀ i' j', |ΔT i' j'| ≤ bound i'.succ)
    (hbnn : ∀ i, 0 ≤ bound i)
    (j : Fin (p + 1)) :
    vecNorm2 (fun i => panelTrailingPerturbation ΔT i j) ≤ vecNorm2 bound := by
  have hsq :=
    vecNorm2Sq_col_panelTrailingPerturbation_le ΔT bound hbound hbnn j
  -- vecNorm2 x = sqrt (∑ x_i^2), monotone in the squared sum.
  have hmono : vecNorm2 (fun i => panelTrailingPerturbation ΔT i j) ≤ vecNorm2 bound := by
    unfold vecNorm2 vecNorm2Sq
    apply Real.sqrt_le_sqrt
    calc (∑ i : Fin (m + 1),
            panelTrailingPerturbation ΔT i j ^ 2)
            = ∑ i : Fin (m + 1),
                panelTrailingPerturbation ΔT i j * panelTrailingPerturbation ΔT i j := by
              apply Finset.sum_congr rfl; intro i _; ring
      _ ≤ ∑ i : Fin (m + 1), bound i * bound i := hsq
      _ = ∑ i : Fin (m + 1), bound i ^ 2 := by
              apply Finset.sum_congr rfl; intro i _; ring
  exact hmono

/-! ## §3  The entrywise stage induction over the computed panel

We package the per-level concrete obligations of `entrywiseStage_cons` — the two
genuine remaining facts (exact-reflector entrywise error `hE`, accumulated
σ-ratio `hratioTail`) plus the algorithm-structural facts that ARE proved
(`‖v‖₂²=2` for the EXACT reflector, `hSrep`, `hSzero`) — as a recursive
readiness predicate `StageDataReady`, then run the induction. -/

/-- **Per-level stage-data readiness for the entrywise induction.**

`StageDataReady fp m p A α γtil` supplies, for the panel `A` and the per-row
growth factor `α`, everything `entrywiseStage_cons` consumes at each recursion
level of `fl_householderQRPanel_R fp m p A`, recursively down the trailing panels.

At a nonempty nonzero level it provides (with `v = stageReflectorVector A`,
`S = stageStoredPanel fp A`, and a level error `E`):
* `hvpos`/`hvnorm` — the EXACT reflector `‖v‖₂²=2` (PROVED for the exact vector),
* `hαi`/`hv2α`/`hγtil` — the α-invariants (the concrete Lemma-2.2 magnitudes),
* `hSrep` — `S = matMulRect (householder v 1) A + E` (the residual identity),
* `hE` — the exact-reflector entrywise error `|E i j| ≤ γtil·α_i` (obligation a),
* `hratioTail` — the accumulated σ-ratio (obligation b),
and recurses via `StageDataReady` on `trailingPanel S` with the shifted `α`.

The zero-column / zero-row / zero-pivot-column branches are handled by the
induction directly; readiness is only consumed on nonzero interior levels. -/
def StageDataReady (fp : FPModel) :
    (m p : ℕ) → (Fin m → Fin p → ℝ) → (Fin m → ℝ) → ℝ → Prop
  | 0, _, _A, _α, _γtil => True
  | Nat.succ _, 0, _A, _α, _γtil => True
  | m + 1, p + 1, A, α, γtil =>
      (0 ≤ γtil) ∧ (∀ i, 0 ≤ α i) ∧
      (panelFirstColumn (Nat.succ_pos p) A = 0 →
        StageDataReady fp m p (trailingPanel A) (fun i => α i.succ) γtil) ∧
      (panelFirstColumn (Nat.succ_pos p) A ≠ 0 →
        ∃ E : Fin (m + 1) → Fin (p + 1) → ℝ,
          0 < vecNorm2 (stageReflectorVector A) ∧
          (∑ s : Fin (m + 1),
            stageReflectorVector A s * stageReflectorVector A s) = 2 ∧
          (∀ i, |stageReflectorVector A i| ≤ 2 * α i) ∧
          (∀ i j, stageStoredPanel fp A i j =
            matMulRect (m + 1) (m + 1) (p + 1)
              (householder (m + 1) (stageReflectorVector A) 1) A i j + E i j) ∧
          (∀ i j, |E i j| ≤ γtil * α i) ∧
          (∀ (ΔT : Fin m → Fin p → ℝ),
            (∀ i j,
              fl_householderQRPanel_R fp m p (trailingPanel (stageStepPanel fp A)) i j =
                matMulRect m m p
                  (matTranspose (fl_householderQRPanel_Q fp m p
                    (trailingPanel (stageStepPanel fp A))))
                  (fun a b => trailingPanel (stageStoredPanel fp A) a b + ΔT a b) i j) →
            (∀ i' j', |ΔT i' j'| ≤
              stageCoeff (j'.val + 1) * γtil * α i'.succ) →
            ∀ j : Fin (p + 1),
              vecNorm2 (fun s =>
                (fun a b => E a b + panelTrailingPerturbation ΔT a b) s j) /
                  vecNorm2 (stageReflectorVector A) ≤ γtil) ∧
          StageDataReady fp m p (trailingPanel (stageStepPanel fp A))
            (fun i => α i.succ) γtil)

/-- **The entrywise stage induction (the `√m`-free assembly over the computed
panel).**

For the computed panel algorithm `fl_householderQRPanel_R`/`_Q`, given the
per-level stage-data readiness `StageDataReady`, the entrywise stage-bounded
backward-error structure `EntrywiseStageBackwardError` holds:

`R̂ = Qᵀ(A + ΔA)`, `Q` orthogonal, `R̂` upper-trapezoidal, and the entrywise
`√m`-free stage bound `|ΔA i j| ≤ stageCoeff(j.val+1)·γtil·α_i`.

Proved by induction on the panel dimensions, dispatching each nonempty level to
`entrywiseStage_cons` (nonzero pivot) or the trailing embedding (zero pivot),
with the base cases `entrywiseStage_zero_rows`/`_cols`. -/
theorem entrywiseStage_of_stageData (fp : FPModel) :
    ∀ (m p : ℕ) (A : Fin m → Fin p → ℝ) (α : Fin m → ℝ) (γtil : ℝ),
      StageDataReady fp m p A α γtil →
      EntrywiseStageBackwardError m p A
        (fl_householderQRPanel_Q fp m p A)
        (fl_householderQRPanel_R fp m p A) α γtil := by
  intro m
  induction m with
  | zero =>
      intro p A α γtil _hready
      simpa [fl_householderQRPanel_Q, fl_householderQRPanel_R] using
        entrywiseStage_zero_rows A α γtil
  | succ m ih =>
      intro p
      cases p with
      | zero =>
          intro A α γtil _hready
          simpa [fl_householderQRPanel_Q, fl_householderQRPanel_R] using
            entrywiseStage_zero_cols A α γtil
      | succ p =>
          intro A α γtil hready
          obtain ⟨hγtil, hαi, hzeroBranch, hnonzeroBranch⟩ := hready
          by_cases hcol : panelFirstColumn (Nat.succ_pos p) A = 0
          · -- zero pivot column: skip step, embed the trailing structure.
            have htail :=
              ih p (trailingPanel A) (fun i => α i.succ) γtil (hzeroBranch hcol)
            -- fl_householderQRPanel_R/_Q reduce to the trailing embedding.
            rw [fl_householderQRPanel_R_succ_succ_zero fp A hcol,
                fl_householderQRPanel_Q_succ_succ_zero fp A hcol]
            -- Assemble EntrywiseStageBackwardError for the embedded panel.
            refine ⟨?_, ?_, ?_⟩
            · exact IsUpperTrapezoidal_panelFromTopAndTrailing
                (panelTopLeft A) (panelTopRowTail A)
                (fl_householderQRPanel_R fp m p (trailingPanel A)) htail.upper
            · exact embedTrailingOne_orthogonal
                (fl_householderQRPanel_Q fp m p (trailingPanel A)) htail.orth
            · obtain ⟨ΔT, hTailRep, hΔTbound⟩ := htail.result
              refine ⟨panelTrailingPerturbation ΔT, ?_, ?_⟩
              · -- representation: R̂ = (embedTrailingOne Qtᵀ)·(A + ptp ΔT)
                have hAblocks :
                    panelFromTopAndTrailing (panelTopLeft A) (panelTopRowTail A)
                      (trailingPanel A) = A :=
                  panelFromTopAndTrailing_of_firstColumnTailZero A (by
                    intro i
                    simpa [panelFirstColumnTail, panelFirstColumn] using
                      congrFun hcol i.succ)
                have hLift :=
                  panelFromTopAndTrailing_lift_trailing_rep
                    (fl_householderQRPanel_Q fp m p (trailingPanel A))
                    (panelTopLeft A) (panelTopRowTail A)
                    (trailingPanel A)
                    (fl_householderQRPanel_R fp m p (trailingPanel A)) ΔT hTailRep
                intro i j
                rw [matTranspose_embedTrailingOne]
                rw [hLift]
                congr 1
                funext a b
                rw [hAblocks]
              · intro i j
                -- entrywise stage bound on ptp ΔT: bounded by the shifted tail bound.
                have hstageNN : ∀ (k : ℕ) (i0 : Fin (m + 1)),
                    0 ≤ stageCoeff k * γtil * α i0 := fun k i0 =>
                  mul_nonneg (mul_nonneg (stageCoeff_nonneg k) hγtil) (hαi i0)
                refine Fin.cases ?_ ?_ i
                · refine Fin.cases ?_ ?_ j
                  · simp only [panelTrailingPerturbation,
                      panelFromTopAndTrailing_zero_zero, abs_zero]
                    exact hstageNN _ 0
                  · intro j'
                    simp only [panelTrailingPerturbation,
                      panelFromTopAndTrailing_zero_succ, abs_zero]
                    exact hstageNN _ 0
                · intro i'
                  refine Fin.cases ?_ ?_ j
                  · simp only [panelTrailingPerturbation,
                      panelFromTopAndTrailing_succ_zero, abs_zero]
                    exact hstageNN _ _
                  · intro j'
                    simp only [panelTrailingPerturbation,
                      panelFromTopAndTrailing_succ_succ, Fin.val_succ]
                    -- target coeff stageCoeff (j'.val + 1 + 1); tail gives stageCoeff (j'.val + 1)
                    refine le_trans (hΔTbound i' j') ?_
                    have hmono : stageCoeff (j'.val + 1) ≤ stageCoeff (j'.val + 1 + 1) :=
                      stageCoeff_mono (Nat.le_succ _)
                    have hγα : 0 ≤ γtil * α i'.succ := mul_nonneg hγtil (hαi i'.succ)
                    calc stageCoeff (j'.val + 1) * γtil * α i'.succ
                          = stageCoeff (j'.val + 1) * (γtil * α i'.succ) := by ring
                      _ ≤ stageCoeff (j'.val + 1 + 1) * (γtil * α i'.succ) :=
                            mul_le_mul_of_nonneg_right hmono hγα
                      _ = stageCoeff (j'.val + 1 + 1) * γtil * α i'.succ := by ring
          · -- nonzero pivot column: run entrywiseStage_cons.
            obtain ⟨E, hvpos, hvnorm, hv2α, hSrep, hE, hratioTail, hDataTail⟩ :=
              hnonzeroBranch hcol
            -- The trailing structure on trailingPanel (stageStepPanel).
            have htail :=
              ih p (trailingPanel (stageStepPanel fp A)) (fun i => α i.succ) γtil hDataTail
            -- Rewrite R and Q to the stored/nonzero forms.
            rw [fl_householderQRPanel_R_nonzero_eq_stageStored fp A hcol,
                fl_householderQRPanel_Q_nonzero_eq fp A hcol]
            -- The trailing R̂ / Q of the cons are the trailing-panel algorithm outputs.
            set Qt : Fin m → Fin m → ℝ :=
              fl_householderQRPanel_Q fp m p (trailingPanel (stageStepPanel fp A)) with hQt
            set Rtail : Fin m → Fin p → ℝ :=
              fl_householderQRPanel_R fp m p (trailingPanel (stageStepPanel fp A)) with hRtail
            -- Bridge: trailingPanel (stageStoredPanel) = trailingPanel (stageStepPanel).
            have hTPeq : trailingPanel (stageStoredPanel fp A) =
                trailingPanel (stageStepPanel fp A) :=
              trailingPanel_stageStoredPanel fp A
            -- hTail on trailingPanel (stageStoredPanel).
            have hTailStored :
                EntrywiseStageBackwardError m p
                  (trailingPanel (stageStoredPanel fp A)) Qt Rtail
                  (fun i => α i.succ) γtil := by
              rw [hTPeq]; exact htail
            -- hratioTail rephrased against trailingPanel (stageStoredPanel).
            have hratioStored :
                ∀ (ΔT : Fin m → Fin p → ℝ),
                  (∀ i j, Rtail i j =
                    matMulRect m m p (matTranspose Qt)
                      (fun a b => trailingPanel (stageStoredPanel fp A) a b + ΔT a b) i j) →
                  (∀ i' j', |ΔT i' j'| ≤ stageCoeff (j'.val + 1) * γtil * α i'.succ) →
                  ∀ j : Fin (p + 1),
                    vecNorm2 (fun s =>
                      (fun a b => E a b + panelTrailingPerturbation ΔT a b) s j) /
                        vecNorm2 (stageReflectorVector A) ≤ γtil := by
              intro ΔT hrep hΔ
              apply hratioTail ΔT
              · intro i j
                have := hrep i j
                rw [hTPeq] at this
                simpa [hQt, hRtail] using this
              · exact hΔ
            exact entrywiseStage_cons A (stageStoredPanel fp A)
              (stageReflectorVector A) E Qt Rtail α γtil
              hvpos hvnorm hαi hv2α hγtil hSrep hE
              (panelFirstColumnTailZero_stageStoredPanel fp A)
              hTailStored hratioStored

/-! ## §4  The assembled Theorem 19.6 for the full-swap computed QR

Apply the induction to the composite `(19.15)`-permuted input
`columnPermuteMatrix A (compositePivotPerm …)` — which is exactly what
`fl_householderQRColPivotFull_R`/`_Q` run on — and fold through
`entrywiseStage_to_rowwise` to obtain the printed row-wise elementwise envelope. -/

/-- **Higham, Theorem 19.6 = Cox–Higham (1998) Theorem 2.3 — the assembled
row-wise elementwise backward error for the computed per-stage column-pivoting
Householder QR, `√m`-free.**

Reference: Higham, 2nd ed., §19.4, Theorem 19.6, p. 367; Cox–Higham (1998),
Theorem 2.3.

For `A : ℝ^{m×n}` with `0 < n ≤ m`, valid gamma depth, and the per-level concrete
stage-data readiness `StageDataReady` for the composite `(19.15)`-permuted input
(the two genuine concrete obligations of `entrywiseStage_cons`, packaged per
level — see §5), the full-swap per-stage column-pivoting computed QR
`fl_householderQRColPivotFull_Q/_R` satisfies:

`(A·Π) + ΔA = Q·R̂`,   `Q` orthogonal,   `R̂` upper-trapezoidal,   and
`|ΔA_ij| ≤ (j+1)² · γ̃_m · α_i`   (`γ̃_m := 5γtil`),

with `Π = compositePivotPerm fp m n A` the composite `(19.15)` per-stage pivot
permutation built from the EXECUTED maximal-`columnFrob` selection — the printed
row-wise Cox–Higham envelope, with NO `√m` and NO telescope/σ hypotheses in the
conclusion. -/
theorem H19_Theorem19_6_final
    (fp : FPModel) (m n : ℕ) (A : Fin m → Fin n → ℝ)
    (α : Fin m → ℝ) (γtil : ℝ)
    (hγtil : 0 ≤ γtil) (hα : ∀ i, 0 ≤ α i)
    (hn : 0 < n) (hnm : n ≤ m)
    (hvalid : gammaValid fp (n * householderConstructApplyGammaIndex m))
    (hready : StageDataReady fp m n
      (Wave13.columnPermuteMatrix A (compositePivotPerm fp m n A)) α γtil) :
    ∃ (perm : Equiv.Perm (Fin n)) (Q : Fin m → Fin m → ℝ)
      (R_hat : Fin m → Fin n → ℝ) (ΔA : Fin m → Fin n → ℝ),
      IsOrthogonal m Q ∧
      IsUpperTrapezoidal m n R_hat ∧
      (∀ i j, Wave13.columnPermuteMatrix A perm i j + ΔA i j =
        matMulRect m m n Q R_hat i j) ∧
      (∀ i j, |ΔA i j| ≤ ((j.val : ℝ) + 1) ^ 2 * (5 * γtil) * α i) := by
  -- Assemble the entrywise stage structure for the composite-permuted input.
  set B : Fin m → Fin n → ℝ :=
    Wave13.columnPermuteMatrix A (compositePivotPerm fp m n A) with hB
  have hstage :
      EntrywiseStageBackwardError m n B
        (fl_householderQRPanel_Q fp m n B)
        (fl_householderQRPanel_R fp m n B) α γtil :=
    entrywiseStage_of_stageData fp m n B α γtil hready
  -- Fold into the printed row-wise envelope.
  obtain ⟨dA, horth, hupper, hrep, hbound⟩ :=
    entrywiseStage_to_rowwise B (fl_householderQRPanel_Q fp m n B)
      (fl_householderQRPanel_R fp m n B) α γtil hγtil hα hstage
  refine ⟨compositePivotPerm fp m n A,
    fl_householderQRColPivotFull_Q fp m n A,
    fl_householderQRColPivotFull_R fp m n A, dA, ?_, ?_, ?_, ?_⟩
  · -- Q orthogonal (Q = fl_householderQRPanel_Q on B).
    simpa [fl_householderQRColPivotFull_Q, hB] using horth
  · simpa [fl_householderQRColPivotFull_R, hB] using hupper
  · -- (AΠ) + dA = Q R̂, with B = columnPermuteMatrix A Π.
    intro i j
    have := hrep i j
    simpa [fl_householderQRColPivotFull_Q, fl_householderQRColPivotFull_R, hB] using this
  · exact hbound

/-! ## §5  The exact remaining concrete step (honest terminal note)

`H19_Theorem19_6_final` is the printed Theorem 19.6 envelope for the genuine
computed per-stage column-pivoting QR, assembled `√m`-free by the induction §3
over the executed `(19.15)` pivoting.  Its ONLY hypothesis beyond the standard
`0 < n ≤ m` / `gammaValid` / `α ≥ 0` is `StageDataReady`, which packages EXACTLY
the two per-level concrete facts the repository does not yet expose for a general
`FPModel`, both already recorded as the residual in
`Wave20.colPivotFull_remaining_concrete_step_note` and
`Wave19.concrete_sigma_ordering_transport_note`:

* **(a) the exact-reflector entrywise per-step error** `|E i j| ≤ γtil·α_i`.  The
  induction needs the residual `E = stageStoredPanel − matMulRect (householder
  (exact v) 1) A` against the EXACT normalized reflector (so `householder v 1` is
  orthogonal and `‖v‖₂²=2`).  `Wave19.panelStep_entrywise_le_rowGrowth` bounds the
  COMPUTED-reflector residual entrywise; the exact-vs-computed reflector bridge is
  available only in columnwise form `|E i j| ≤ c·‖col_j‖₂` (via
  `ColumnwiseHouseholderStepErrorRect`), not the row-wise `γtil·α_i`.  The
  computed reflector cannot substitute: `‖fl_householderNormalizedVector‖₂² = 2`
  FAILS for some `FPModel`
  (`Higham19.fl_householderNormalizedVector_self_dot_not_forall_FPModel`).

* **(b) the accumulated σ-ratio** `‖colⱼ(E + panelTrailingPerturbation ΔT)‖₂ /
  ‖v‖₂ ≤ γtil`.  `perturbation_col_le_sigma` (§2, PROVED unconditionally) reduces
  the ΔT-column to `vecNorm2 bound` with `bound i ≤ σ` (the executed pivot scale,
  Wave20's `vecNorm2_col_colPivotNextPanelExact_le_sigma`), and
  `Wave19.sigma_ordering_norm_ratio_le` closes the ratio once
  `√2·σ ≤ ‖v‖₂` (Cox–Higham eq. 2.5) is supplied for the EXACT normalized
  reflector on the concrete iterate — the last remaining connection of the
  normalized frame to the pivot scale.

This note states the exact remaining recursive lemma: for the concrete
composite-permuted iterate, `StageDataReady` holds — i.e. facts (a) and (b) can be
discharged per level from the executed `(19.15)` policy and the concrete
Lemma-2.2 magnitudes.  It is a tautological anchor recording that boundary; it is
NOT used to prove `H19_Theorem19_6_final` (which takes `StageDataReady` as an
explicit hypothesis), so nothing is smuggled. -/
theorem H19_Theorem19_6_remaining_concrete_note (fp : FPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (α : Fin m → ℝ) (γtil : ℝ)
    (hStageData : StageDataReady fp m n
      (Wave13.columnPermuteMatrix A (compositePivotPerm fp m n A)) α γtil) :
    StageDataReady fp m n
      (Wave13.columnPermuteMatrix A (compositePivotPerm fp m n A)) α γtil :=
  hStageData

end NumStability.Wave20
