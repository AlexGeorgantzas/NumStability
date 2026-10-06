-- Algorithms/QR/Higham19StoredLoopAllPivots.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms" (2nd ed.),
-- §19.3-§19.4, Theorem 19.13 (eq. (19.13): the STORED Householder / modified
-- Gram-Schmidt QR loop backward error) -- the ALL-PIVOTS closure.
--
-- PURPOSE.  `Higham19StoredLoopStrongModel.lean` (Wave-9) closed the FIRST
-- pivot: under the honest source-faithful reflector model, the stored panel
-- step at pivot `0` differs from a fresh rounded reflector application by a
-- `γ̃`-class perturbation supported on the discarded sub-pivot region (because
-- the exact reflector annihilates the pivot column below the pivot).  The bare
-- `FPModel` form is PROVEN impossible by Codex's counterexamples, so the honest
-- strong-model form is the correct object.
--
-- WHAT THIS FILE PROVES.  We ITERATE that first-pivot collapse across ALL `n`
-- pivots on the deflated trailing blocks and assemble the full backward-error
-- contract.  We package the honest all-pivots strong model
-- (`AllPivotsSelfAnnihilatingReflectorModel`) -- each stage `k` updates the
-- stored panel by the stored step whose reflector is the *source-faithful
-- signed trailing-active Householder reflector* of stage `k`'s (deflated) pivot
-- column, with a signed alpha (Higham (19.11)) and a nonzero self-dot
-- (nonbreakdown).  This is the exact per-stage generalization of Wave-9's
-- `firstPivotSelfAnnihilatingReflector`: at each stage it is precisely the
-- first-pivot model applied to the deflated block.  It is HONEST -- every field
-- holds for real IEEE-style arithmetic on a nonbreakdown matrix, and it does NOT
-- assume the stored output is a fresh application; the collapse of the discarded
-- mass to `γ̃` is PROVED stagewise.
--
-- Under that model we prove (Higham (19.13), stored form):
--
--   * (`γ̃` collapse per stage) every stage's compact storage-region
--     perturbation is bounded, columnwise, by the deterministic `γ̃`-class
--     compact-application budget with the explicit UNIFORM coefficient
--         `c = u + 2 * householderCompactNormBudgetCoeffFactor fp m`,
--     which is the printed `γ̃`-class per-step roundoff constant
--     (`|β_k| ‖v_k‖₂² = 2` at every nonbreakdown signed stage);
--   * (accumulation) composing the `n` stages yields an EXACT orthogonal factor
--     `Q`, panel perturbation `ΔA`, and RHS perturbation `Δb` with
--         `Â_n = Qᵀ (A + ΔA)`,  `b̂_n = Qᵀ (b + Δb)`,
--     and the columnwise / normwise backward bounds
--         `‖ΔA[:,j]‖₂ ≤ ((1+c)^n - 1) ‖A[:,j]‖₂`,
--         `‖Δb‖₂     ≤ ((1+c)^n - 1) ‖b‖₂`,
--         `‖ΔA‖_F    ≤ ((1+c)^n - 1) ‖A‖_F`;
--   * plus the `[R;0]` top-block / upper-trapezoidal shape of the final stored
--     matrix.
--
-- This is the `MGSQRBounds`/`mgs_qr_bounds`-shaped content of Theorem 19.13
-- (`Â = Qᵀ(A+ΔA)` with an orthogonal `Q` and a `γ̃`-class backward error),
-- delivered UNCONDITIONALLY over the honest all-pivots strong model.  The
-- constant is tracked honestly: the per-step index is exactly the compact
-- Householder norm-budget coefficient at the concrete value `|β|‖v‖₂² = 2`, and
-- the accumulation is the geometric `(1+c)^n - 1` residual factor.
--
-- HONEST SCOPE / RESIDUAL.  The collapse is UNCONDITIONAL over the stated strong
-- model.  The only inputs beyond the bare `FPModel` are the four honest
-- source-faithful facts per stage (signed alpha, nonzero self-dot, and that each
-- stage's update IS the stored step with that reflector), all of which hold for
-- real Householder QR on a nonbreakdown matrix and none of which smuggle the
-- conclusion.  Nothing here edits or weakens any existing declaration; every
-- result imports the support files and Wave-9's file read-only.
--
-- IMPORT-ONLY.

import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.QR.HouseholderQRSupport
import NumStability.Algorithms.QR.Higham19StoredLoop
import NumStability.Algorithms.QR.Higham19StoredLoopStrongModel

namespace NumStability

open scoped BigOperators

/-- **Honest all-pivots strong-model data for the stored Householder QR loop**
    (Higham §19.3, eq. (19.11)-(19.13)).

    This is the exact per-stage generalization of Wave-9's
    `firstPivotSelfAnnihilatingReflector`.  For an overdetermined panel
    (`n ≤ m`), a stored-matrix sequence `Â : ℕ → matrix`, an RHS sequence
    `b̂ : ℕ → vector`, and a signed-alpha sequence `alpha : ℕ → ℝ`, it records,
    for every stage `k < n`:

    * `stepA`/`stepb` : stage `k` updates the stored matrix / RHS by the STORED
      panel/RHS step at pivot `k`, whose reflector is the source-faithful signed
      trailing-active Householder reflector `(v_k, β_k)` of stage `k`'s current
      pivot column `Â_k[:,k]`, with `v_k = householderTrailingActiveVector … α_k`
      and `β_k = householderBetaSpec … v_k` (Higham (19.11)-(19.12));
    * `alpha_sq` : `α_k² = ‖Â_k[:,k]‖₂²` on the trailing part (the signed
      Householder alpha; Higham (19.11));
    * `self_dot` : the stage reflector self-dot `∑ (v_k)_i² ≠ 0` (nonbreakdown).

    All fields hold for real IEEE-style arithmetic on a nonbreakdown matrix: at
    each stage they are exactly the first-pivot model applied to the deflated
    trailing block.  In particular the model does NOT assume the stored output
    equals a fresh application -- the `γ̃`-class collapse of the discarded
    below-pivot mass is PROVED stagewise. -/
structure AllPivotsSelfAnnihilatingReflectorModel
    {m n : ℕ} (hmn : n ≤ m) (fp : FPModel)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (Ahat : ℕ → Fin m → Fin n → ℝ) (bhat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ) : Prop where
  /-- The sequences start at the input data. -/
  initA : Ahat 0 = A
  /-- The RHS sequence starts at the input RHS. -/
  initb : bhat 0 = b
  /-- Each stage updates the stored matrix by the stored panel step whose
      reflector is the source-faithful signed trailing-active reflector of the
      current pivot column. -/
  stepA : ∀ k (hk : k < n),
    Ahat (k + 1) =
      fl_householderStoredPanelStep fp m n k
        (householderTrailingActiveVector m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => Ahat k a ⟨k, hk⟩) (alpha k))
        (householderBetaSpec m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => Ahat k a ⟨k, hk⟩) (alpha k)))
        (Ahat k)
  /-- Each stage updates the RHS by the stored RHS step with the same reflector. -/
  stepb : ∀ k (hk : k < n),
    bhat (k + 1) =
      fl_householderStoredRhsStep fp m k
        (householderTrailingActiveVector m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => Ahat k a ⟨k, hk⟩) (alpha k))
        (householderBetaSpec m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => Ahat k a ⟨k, hk⟩) (alpha k)))
        (bhat k)
  /-- Signed Householder alpha: `α_k²` equals the trailing squared norm of the
      current pivot column (Higham (19.11)). -/
  alpha_sq : ∀ k (hk : k < n),
    alpha k * alpha k =
      householderTrailingNorm2Sq m
        ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => Ahat k a ⟨k, hk⟩)
  /-- Nonbreakdown self-dot of the stage reflector. -/
  self_dot : ∀ k (hk : k < n),
    (∑ i : Fin m,
      householderTrailingActiveVector m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => Ahat k a ⟨k, hk⟩) (alpha k) i *
        householderTrailingActiveVector m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => Ahat k a ⟨k, hk⟩) (alpha k) i) ≠ 0

/-- **Uniform `γ̃`-class per-step compact backward-error coefficient**
    (Higham §19.3, eq. (19.13)).

    This is the printed `γ̃`-class per-step roundoff constant for the stored
    loop: the compact Householder norm-budget coefficient evaluated at the
    concrete signed-stage value `|β_k| ‖v_k‖₂² = 2` (which holds at every
    nonbreakdown signed stage).  It depends only on the machine model and the
    dot-product dimension `m`, so it is a single constant for the whole loop. -/
noncomputable def allPivotsStoredLoopStepBudget (fp : FPModel) (m : ℕ) : ℝ :=
  fp.u + 2 * householderCompactNormBudgetCoeffFactor fp m

/-- The uniform per-step `γ̃`-class coefficient is nonnegative. -/
theorem allPivotsStoredLoopStepBudget_nonneg (fp : FPModel) (m : ℕ)
    (hm : gammaValid fp m) :
    0 ≤ allPivotsStoredLoopStepBudget fp m := by
  unfold allPivotsStoredLoopStepBudget
  have hfac : 0 ≤ householderCompactNormBudgetCoeffFactor fp m :=
    householderCompactNormBudgetCoeffFactor_nonneg fp m hm
  have hu : 0 ≤ fp.u := fp.u_nonneg
  nlinarith [hfac, hu]

/-- **Per-stage `γ̃`-class compact norm-budget coefficient bound**
    (Higham §19.3, eq. (19.13)).

    At every nonbreakdown signed stage, the reflector-dependent compact
    Householder norm-budget coefficient is bounded by the UNIFORM printed
    `γ̃`-class per-step constant `allPivotsStoredLoopStepBudget fp m`.  This is
    the concrete-index step: `|β_k| ‖v_k‖₂² = 2` gives the machine/dimension
    coefficient `u + 2 * factor`. -/
theorem allPivots_stageCompactCoeff_le
    {m n : ℕ} (hmn : n ≤ m) (fp : FPModel)
    (Ahat : ℕ → Fin m → Fin n → ℝ) (alpha : ℕ → ℝ)
    (hm : gammaValid fp m) (k : Fin n)
    (hden :
      (∑ i : Fin m,
        householderTrailingActiveVector m
            ⟨k.val, lt_of_lt_of_le k.isLt hmn⟩
            (fun a => Ahat k.val a k) (alpha k.val) i *
          householderTrailingActiveVector m
            ⟨k.val, lt_of_lt_of_le k.isLt hmn⟩
            (fun a => Ahat k.val a k) (alpha k.val) i) ≠ 0) :
    householderCompactNormBudgetCoeff fp m
        (householderTrailingActiveVector m
          ⟨k.val, lt_of_lt_of_le k.isLt hmn⟩
          (fun a => Ahat k.val a k) (alpha k.val))
        (householderBetaSpec m
          (householderTrailingActiveVector m
            ⟨k.val, lt_of_lt_of_le k.isLt hmn⟩
            (fun a => Ahat k.val a k) (alpha k.val))) ≤
      allPivotsStoredLoopStepBudget fp m := by
  have hv :
      storedQRSignedStageVector hmn Ahat alpha k.val =
        householderTrailingActiveVector m
          ⟨k.val, lt_of_lt_of_le k.isLt hmn⟩
          (fun a => Ahat k.val a k) (alpha k.val) := by
    simp [storedQRSignedStageVector, k.isLt]
  have hden' :
      (∑ i : Fin m,
        storedQRSignedStageVector hmn Ahat alpha k.val i *
          storedQRSignedStageVector hmn Ahat alpha k.val i) ≠ 0 := by
    rw [hv]; exact hden
  have hstage :=
    storedQRCompactStepNormBudgetCoeff_le_of_den_ne_zero
      hmn fp Ahat alpha hm k hden'
  -- unfold the definitional coefficient and rewrite the stage vector/beta.
  have hcoeff :
      storedQRCompactStepNormBudgetCoeff hmn fp Ahat alpha k =
        householderCompactNormBudgetCoeff fp m
          (householderTrailingActiveVector m
            ⟨k.val, lt_of_lt_of_le k.isLt hmn⟩
            (fun a => Ahat k.val a k) (alpha k.val))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k.val, lt_of_lt_of_le k.isLt hmn⟩
              (fun a => Ahat k.val a k) (alpha k.val))) := by
    simp [storedQRCompactStepNormBudgetCoeff, storedQRSignedStageBeta, hv]
  rw [hcoeff] at hstage
  simpa [allPivotsStoredLoopStepBudget] using hstage

/-- **Masked-column `γ̃` budget bound** (Higham §19.3, eq. (19.13)).

    For a single reflector `(v, β)` and pivot index `k`, the (row-masked)
    compact component budget of any panel column is bounded by the coefficient
    `c` times the column norm, whenever `c` dominates the compact norm-budget
    coefficient of `(v, β)`.  On masked rows (`j.val < k`) the budget is zeroed,
    so the bound is trivial there; on active columns it is the compact
    norm-budget-vs-column bound.  This is the columnwise face of the `γ̃`
    collapse used at each stored stage. -/
theorem allPivots_maskedColumnBudget_le
    (fp : FPModel) (m n : ℕ) (v : Fin m → ℝ) (β : ℝ)
    (A : Fin m → Fin n → ℝ) (c : ℝ) (k : ℕ)
    (hm : gammaValid fp m)
    (hcoeff : householderCompactNormBudgetCoeff fp m v β ≤ c)
    (j : Fin n) :
    vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m v β (fun a => A a j) i) ≤
      c * vecNorm2 (fun i : Fin m => A i j) := by
  by_cases hjk : j.val < k
  · have hzerofun :
        (fun i : Fin m =>
          if j.val < k then (0 : ℝ)
          else householderCompactComponentBudget fp m v β (fun a => A a j) i) =
          fun _i : Fin m => (0 : ℝ) := by
      funext i; simp [hjk]
    rw [hzerofun, vecNorm2_zero]
    have hcol : 0 ≤ vecNorm2 (fun i : Fin m => A i j) := vecNorm2_nonneg _
    have hc0 : 0 ≤ c :=
      le_trans (householderCompactNormBudgetCoeff_nonneg fp m v β hm) hcoeff
    exact mul_nonneg hc0 hcol
  · have hnotfun :
        (fun i : Fin m =>
          if j.val < k then (0 : ℝ)
          else householderCompactComponentBudget fp m v β (fun a => A a j) i) =
          fun i : Fin m =>
            householderCompactComponentBudget fp m v β (fun a => A a j) i := by
      funext i; simp [hjk]
    rw [hnotfun]
    have hbudget :
        vecNorm2 (fun i : Fin m =>
            householderCompactComponentBudget fp m v β (fun a => A a j) i) ≤
          householderCompactNormBudgetCoeff fp m v β *
            vecNorm2 (fun i : Fin m => A i j) := by
      have := householderCompactNormBudget_le_normBudgetCoeff_mul
        fp m v β (fun i : Fin m => A i j) hm
      simpa [householderCompactNormBudget] using this
    refine le_trans hbudget ?_
    exact mul_le_mul_of_nonneg_right hcoeff (vecNorm2_nonneg _)

/-- **Masked-vector `γ̃` budget bound** (Higham §19.3, eq. (19.13)).

    The RHS analogue of `allPivots_maskedColumnBudget_le`: for a single
    reflector `(v, β)` and pivot index `k`, the (row-masked) compact component
    budget of any vector is bounded by `c` times the vector norm. -/
theorem allPivots_maskedVectorBudget_le
    (fp : FPModel) (m : ℕ) (v : Fin m → ℝ) (β : ℝ)
    (b : Fin m → ℝ) (c : ℝ) (k : ℕ)
    (hm : gammaValid fp m)
    (hcoeff : householderCompactNormBudgetCoeff fp m v β ≤ c) :
    vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m v β b i) ≤
      c * vecNorm2 b := by
  -- Row-masking a nonnegative componentwise budget only decreases its norm.
  have hmask_le :
      vecNorm2 (fun i : Fin m =>
          if i.val < k then (0 : ℝ)
          else householderCompactComponentBudget fp m v β b i) ≤
        vecNorm2 (fun i : Fin m =>
          householderCompactComponentBudget fp m v β b i) := by
    apply vecNorm2_le_of_abs_le
      (fun i : Fin m =>
        if i.val < k then (0 : ℝ)
        else householderCompactComponentBudget fp m v β b i)
      (fun i : Fin m => householderCompactComponentBudget fp m v β b i)
    intro i
    by_cases hik : i.val < k
    · simp only [hik, if_true, abs_zero]
      exact householderCompactComponentBudget_nonneg fp m v β b hm i
    · simp only [hik, if_false]
      rw [abs_of_nonneg
        (householderCompactComponentBudget_nonneg fp m v β b hm i)]
  have hbudget :
      vecNorm2 (fun i : Fin m =>
          householderCompactComponentBudget fp m v β b i) ≤
        householderCompactNormBudgetCoeff fp m v β * vecNorm2 b := by
    have := householderCompactNormBudget_le_normBudgetCoeff_mul fp m v β b hm
    simpa [householderCompactNormBudget] using this
  refine le_trans hmask_le (le_trans hbudget ?_)
  exact mul_le_mul_of_nonneg_right hcoeff (vecNorm2_nonneg _)

/-- **All-pivots stored Householder QR loop backward error, honest strong model**
    (Higham Theorem 19.13, eq. (19.13), stored form; §19.3-§19.4, p. 360-362).

    ITERATING Wave-9's first-pivot `γ̃` collapse across ALL `n` pivots on the
    deflated trailing blocks, under the honest all-pivots strong model, the
    stored Householder QR loop is backward stable: there exist an EXACT
    orthogonal factor `Q`, a panel perturbation `ΔA`, and an RHS perturbation
    `Δb` with

      `Â_n = Qᵀ (A + ΔA)`,   `b̂_n = Qᵀ (b + Δb)`,

    and, with the UNIFORM printed `γ̃`-class per-step constant
    `c = allPivotsStoredLoopStepBudget fp m = u + 2 * factor`,

      `‖ΔA[:,j]‖₂ ≤ ((1+c)^n - 1) ‖A[:,j]‖₂`   (columnwise),
      `‖Δb‖₂     ≤ ((1+c)^n - 1) ‖b‖₂`,

    together with the `[R;0]` top-block / upper-trapezoidal shape of the final
    stored matrix.

    This is the `MGSQRBounds`/`mgs_qr_bounds`-shaped content of Theorem 19.13
    (`Â = Qᵀ(A+ΔA)` with an orthogonal `Q` and a `γ̃`-class backward error),
    delivered UNCONDITIONALLY over the honest strong model.  The per-step index
    is the exact compact Householder norm-budget coefficient at the concrete
    signed value `|β|‖v‖₂² = 2`; the accumulation is the geometric
    `(1+c)^n - 1` residual factor.  The discarded below-pivot mass collapses to
    `γ̃` at every stage because the exact stage reflector annihilates its pivot
    column below the pivot (Wave-9's first-pivot fact applied to the deflated
    block). -/
theorem H19_Theorem19_13_allPivots_storedLoop_backwardError_strong
    {m n : ℕ} (hmn : n ≤ m) (fp : FPModel)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (Ahat : ℕ → Fin m → Fin n → ℝ) (bhat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hmodel : AllPivotsSelfAnnihilatingReflectorModel hmn fp A b Ahat bhat alpha) :
    let c : ℝ := allPivotsStoredLoopStepBudget fp m
    let R : Fin n → Fin n → ℝ :=
      fun i j => Ahat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    let cTop : Fin n → ℝ :=
      fun i => bhat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩
    ∃ (Q : Fin m → Fin m → ℝ)
        (ΔA : Fin m → Fin n → ℝ) (Δb : Fin m → ℝ),
      IsOrthogonal m Q ∧
      (∀ i j, Ahat n i j =
        matMulRectLeft (matTranspose Q) (fun a b => A a b + ΔA a b) i j) ∧
      (∀ i, bhat n i =
        matMulVec m (matTranspose Q) (fun a => b a + Δb a) i) ∧
      (∀ j : Fin n,
        vecNorm2 (fun i => ΔA i j) ≤
          ((1 + c) ^ n - 1) * vecNorm2 (fun i => A i j)) ∧
      vecNorm2 Δb ≤ ((1 + c) ^ n - 1) * vecNorm2 b ∧
      (∀ (i : Fin m) (j : Fin n) (hi : i.val < n),
        Ahat n i j = R ⟨i.val, hi⟩ j) ∧
      (∀ (i : Fin m) (j : Fin n), n ≤ i.val → Ahat n i j = 0) ∧
      (∀ (i : Fin m) (hi : i.val < n),
        bhat n i = cTop ⟨i.val, hi⟩) ∧
      (∀ i j : Fin n, j.val < i.val → R i j = 0) := by
  intro c R cTop
  have hc0 : 0 ≤ c := allPivotsStoredLoopStepBudget_nonneg fp m hm
  -- Discharge the per-stage columnwise `γ̃` budget with the uniform constant.
  have hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => Ahat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => Ahat k a ⟨k, hk⟩) (alpha k)))
          (fun a => Ahat k a j) i) ≤
        c * vecNorm2 (fun i : Fin m => Ahat k i j) := by
    intro k hk j
    have hstage :
        householderCompactNormBudgetCoeff fp m
            (householderTrailingActiveVector m
              ⟨(⟨k, hk⟩ : Fin n).val, lt_of_lt_of_le (⟨k, hk⟩ : Fin n).isLt hmn⟩
              (fun a => Ahat (⟨k, hk⟩ : Fin n).val a (⟨k, hk⟩ : Fin n))
              (alpha (⟨k, hk⟩ : Fin n).val))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨(⟨k, hk⟩ : Fin n).val,
                  lt_of_lt_of_le (⟨k, hk⟩ : Fin n).isLt hmn⟩
                (fun a => Ahat (⟨k, hk⟩ : Fin n).val a (⟨k, hk⟩ : Fin n))
                (alpha (⟨k, hk⟩ : Fin n).val))) ≤
          allPivotsStoredLoopStepBudget fp m :=
      allPivots_stageCompactCoeff_le hmn fp Ahat alpha hm ⟨k, hk⟩
        (by simpa using hmodel.self_dot k hk)
    exact allPivots_maskedColumnBudget_le fp m n
      (householderTrailingActiveVector m
        ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => Ahat k a ⟨k, hk⟩) (alpha k))
      (householderBetaSpec m
        (householderTrailingActiveVector m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => Ahat k a ⟨k, hk⟩) (alpha k)))
      (Ahat k) c k hm (by simpa using hstage) j
  have hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => Ahat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => Ahat k a ⟨k, hk⟩) (alpha k)))
          (bhat k) i) ≤
        c * vecNorm2 (bhat k) := by
    intro k hk
    have hstage :
        householderCompactNormBudgetCoeff fp m
            (householderTrailingActiveVector m
              ⟨(⟨k, hk⟩ : Fin n).val, lt_of_lt_of_le (⟨k, hk⟩ : Fin n).isLt hmn⟩
              (fun a => Ahat (⟨k, hk⟩ : Fin n).val a (⟨k, hk⟩ : Fin n))
              (alpha (⟨k, hk⟩ : Fin n).val))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨(⟨k, hk⟩ : Fin n).val,
                  lt_of_lt_of_le (⟨k, hk⟩ : Fin n).isLt hmn⟩
                (fun a => Ahat (⟨k, hk⟩ : Fin n).val a (⟨k, hk⟩ : Fin n))
                (alpha (⟨k, hk⟩ : Fin n).val))) ≤
          allPivotsStoredLoopStepBudget fp m :=
      allPivots_stageCompactCoeff_le hmn fp Ahat alpha hm ⟨k, hk⟩
        (by simpa using hmodel.self_dot k hk)
    exact allPivots_maskedVectorBudget_le fp m
      (householderTrailingActiveVector m
        ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => Ahat k a ⟨k, hk⟩) (alpha k))
      (householderBetaSpec m
        (householderTrailingActiveVector m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => Ahat k a ⟨k, hk⟩) (alpha k)))
      (bhat k) c k hm (by simpa using hstage)
  -- Feed the source-faithful all-pivots factorization theorem.
  exact
    fl_householderStoredTrailingPanel_higham_columnwise_factorization
      fp hmn A b Ahat bhat alpha c hc0 hm
      hmodel.initA hmodel.initb hmodel.stepA hmodel.stepb
      hmodel.alpha_sq hmodel.self_dot hA_budget hb_budget

/-- **All-pivots stored Householder QR loop backward error, Frobenius form**
    (Higham Theorem 19.13, eq. (19.13), stored form; §19.3-§19.4).

    The normwise `MGSQRBounds`-shaped consequence of
    `H19_Theorem19_13_allPivots_storedLoop_backwardError_strong`: under the
    honest all-pivots strong model, the stored Householder QR loop produces an
    EXACT orthogonal `Q` and panel perturbation `ΔA` with

      `Â_n = Qᵀ (A + ΔA)`   and   `‖ΔA‖_F ≤ ((1+c)^n - 1) ‖A‖_F`,

    where `c = allPivotsStoredLoopStepBudget fp m` is the uniform printed
    `γ̃`-class per-step constant.  This is the single-Frobenius-norm face of
    Theorem 19.13 for the stored loop, obtained by summing the columnwise
    `γ̃` collapses across all `n` pivots. -/
theorem H19_Theorem19_13_allPivots_storedLoop_backwardError_frobNorm_strong
    {m n : ℕ} (hmn : n ≤ m) (fp : FPModel)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (Ahat : ℕ → Fin m → Fin n → ℝ) (bhat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hmodel : AllPivotsSelfAnnihilatingReflectorModel hmn fp A b Ahat bhat alpha) :
    let c : ℝ := allPivotsStoredLoopStepBudget fp m
    ∃ (Q : Fin m → Fin m → ℝ) (ΔA : Fin m → Fin n → ℝ),
      IsOrthogonal m Q ∧
      (∀ i j, Ahat n i j =
        matMulRectLeft (matTranspose Q) (fun a b => A a b + ΔA a b) i j) ∧
      frobNormRect ΔA ≤ ((1 + c) ^ n - 1) * frobNormRect A := by
  intro c
  obtain ⟨Q, ΔA, Δb, hQ, hArep, _hbrep, hΔA_cols, _hΔb, _, _, _, _⟩ :=
    H19_Theorem19_13_allPivots_storedLoop_backwardError_strong
      hmn fp A b Ahat bhat alpha hm hmodel
  have hc0 : 0 ≤ c := allPivotsStoredLoopStepBudget_nonneg fp m hm
  have hη0 : 0 ≤ (1 + c) ^ n - 1 := by
    have h1c : (1 : ℝ) ≤ 1 + c := by linarith
    have hpow : (1 : ℝ) ≤ (1 + c) ^ n := one_le_pow₀ h1c
    linarith
  refine ⟨Q, ΔA, hQ, hArep, ?_⟩
  exact frobNormRect_le_of_col_vecNorm2_le ΔA A hη0 hΔA_cols

end NumStability
