import NumStability.Algorithms.LeastSquares.Higham20Theorem20_7ActualGrowth

namespace NumStability

open scoped BigOperators

namespace Theorem20_7

/-!
# Paired RHS for the actually rounded Cox--Higham trace

The matrix trace in `Higham20Theorem20_7ActualTrace` exchanges the active
pivot row with the constructor's first coordinate, masks the completed
prefix, and uses the guarded rounded Householder constructor/application.
This file applies precisely that same guarded reflector to the paired
right-hand side.  In particular, a zero active constructor input executes no
floating-point operations and leaves the RHS unchanged.
-/

/-- The current RHS in the work-array row coordinates used by the actual
matrix constructor.  Completed coordinates are masked exactly as in the
matrix active panel. -/
noncomputable def sourceConstructedPivotedStoredQRRhsWork
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (c : Fin m → ℝ) : Fin m → ℝ :=
  let S := sourceConstructedPivotedStoredQRRowSwap fp hn hmn A k
  fun q => if (S q).val < k then 0 else c (S q)

/-- One paired-RHS step driven by the same guarded computed normalized
reflector as the actual matrix step. -/
noncomputable def fl_sourceConstructedPivotedStoredQRRhsStep
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (c : Fin m → ℝ) : Fin m → ℝ :=
  if _hk : k < n then
    let hm : 0 < m := lt_of_lt_of_le hn hmn
    let S := sourceConstructedPivotedStoredQRRowSwap fp hn hmn A k
    let x := sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k
    if _hx : x = 0 then
      c
    else
      let work := sourceConstructedPivotedStoredQRRhsWork fp hn hmn A k c
      let raw := fl_householderApply fp m
        (fl_householderNormalizedVector fp hm x) 1 work
      fun i => if i.val < k then c i else raw (S i)
  else
    c

/-- Literal paired RHS recursion. -/
noncomputable def fl_sourceConstructedPivotedStoredQRRhsSeq
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) : ℕ → Fin m → ℝ
  | 0 => b
  | k + 1 => fl_sourceConstructedPivotedStoredQRRhsStep fp hn hmn A k
      (fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b k)

@[simp] theorem fl_sourceConstructedPivotedStoredQRRhsSeq_zero
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b 0 = b := rfl

theorem fl_sourceConstructedPivotedStoredQRRhsSeq_succ
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (k : ℕ) :
    fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b (k + 1) =
      fl_sourceConstructedPivotedStoredQRRhsStep fp hn hmn A k
        (fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b k) := rfl

/-- The exact-shadow local RHS residual. -/
noncomputable def sourceConstructedPivotedStoredQRRhsEseq
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (k : ℕ) : Fin m → ℝ :=
  fun i =>
    fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b (k + 1) i -
      matMulVec m (sourceConstructedPivotedStoredQRPseq fp hn hmn A k)
        (fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b k) i

theorem sourceConstructedPivotedStoredQRRhs_step_with_residual
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (k : ℕ) (i : Fin m) :
    fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b (k + 1) i =
      matMulVec m (sourceConstructedPivotedStoredQRPseq fp hn hmn A k)
          (fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b k) i +
        sourceConstructedPivotedStoredQRRhsEseq fp hn hmn A b k i := by
  simp [sourceConstructedPivotedStoredQRRhsEseq]

/-- Row-conjugation identity for an arbitrary paired RHS. -/
theorem sourceConstructedPivotedStoredQRPseq_matMulVec_eq_rhsWork
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (c : Fin m → ℝ)
    (k : ℕ) (hk : k < n) (i : Fin m) (hi : k ≤ i.val) :
    matMulVec m (sourceConstructedPivotedStoredQRPseq fp hn hmn A k) c i =
      matMulVec m
        (householder m
          (sourceConstructedPivotedStoredQRExactRawVectorPerm fp hn hmn A k)
          (sourceConstructedPivotedStoredQRExactBeta fp hn hmn A k))
        (sourceConstructedPivotedStoredQRRhsWork fp hn hmn A k c)
        (sourceConstructedPivotedStoredQRRowSwap fp hn hmn A k i) := by
  let S := sourceConstructedPivotedStoredQRRowSwap fp hn hmn A k
  let v0 := sourceConstructedPivotedStoredQRExactRawVectorPerm fp hn hmn A k
  let beta := sourceConstructedPivotedStoredQRExactBeta fp hn hmn A k
  let cp := vecPermute S c
  let work := sourceConstructedPivotedStoredQRRhsWork fp hn hmn A k c
  have hSinv : ∀ q, S (S q) = q := by
    intro q
    simp [S, sourceConstructedPivotedStoredQRRowSwap,
      sourceConstructedRowSwap, hk]
  have hconj :
      matMulVec m (householder m (vecPermute S v0) beta) c i =
        matMulVec m (householder m v0 beta) cp (S i) :=
    matMulVec_householder_vecPermute_involution S v0 c beta hSinv i
  have hcoord : cp (S i) = work (S i) := by
    change c (S (S i)) =
      (if (S (S i)).val < k then 0 else c (S (S i)))
    rw [hSinv i, if_neg (Nat.not_lt.mpr hi)]
  have hweighted : ∀ q, v0 q * cp q = v0 q * work q := by
    intro q
    by_cases hq : (S q).val < k
    · have hv0 : v0 q = 0 :=
        sourceConstructedPivotedStoredQRExactRawVectorPerm_zero_of_masked
          fp hn hmn A k hk q (by simpa [S] using hq)
      simp [hv0]
    · change v0 q * c (S q) =
        v0 q * (if (S q).val < k then 0 else c (S q))
      rw [if_neg hq]
  have hmask := matMulVec_householder_eq_of_coordinate_weighted_eq
    v0 cp work beta (S i) hcoord hweighted
  rw [show sourceConstructedPivotedStoredQRPseq fp hn hmn A k =
      householder m (vecPermute S v0) beta by
        simp [sourceConstructedPivotedStoredQRPseq,
          sourceConstructedPivotedStoredQRExactRawVector_eq_vecPermute,
          S, v0, beta]]
  exact hconj.trans hmask

/-- The exact-shadow reflector fixes every completed RHS coordinate. -/
theorem sourceConstructedPivotedStoredQRPseq_matMulVec_prefix_eq
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (c : Fin m → ℝ)
    (k : ℕ) (hk : k < n) (i : Fin m) (hi : i.val < k) :
    matMulVec m (sourceConstructedPivotedStoredQRPseq fp hn hmn A k) c i =
      c i := by
  let v := sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A k
  let beta := sourceConstructedPivotedStoredQRExactBeta fp hn hmn A k
  have hv : v i = 0 :=
    sourceConstructedPivotedStoredQRExactRawVector_zero_prefix
      fp hn hmn A k hk i hi
  rw [show sourceConstructedPivotedStoredQRPseq fp hn hmn A k =
      householder m v beta by rfl, householder_matMulVec_eq]
  simp [hv]

theorem fl_sourceConstructedPivotedStoredQRRhsSeq_succ_prefix_eq
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (k : ℕ) (hk : k < n) (i : Fin m) (hi : i.val < k) :
    fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b (k + 1) i =
      fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b k i := by
  rw [fl_sourceConstructedPivotedStoredQRRhsSeq_succ]
  by_cases hx : sourceConstructedPivotedStoredQRActiveInput
      fp hn hmn A k = 0
  · simp [fl_sourceConstructedPivotedStoredQRRhsStep, hk, hx]
  · simp [fl_sourceConstructedPivotedStoredQRRhsStep, hk, hx, hi]

/-- Every completed RHS coordinate has exactly zero local residual. -/
theorem sourceConstructedPivotedStoredQRRhsEseq_prefix_zero
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (k : ℕ) (hk : k < n) (i : Fin m) (hi : i.val < k) :
    sourceConstructedPivotedStoredQRRhsEseq fp hn hmn A b k i = 0 := by
  rw [sourceConstructedPivotedStoredQRRhsEseq,
    fl_sourceConstructedPivotedStoredQRRhsSeq_succ_prefix_eq
      fp hn hmn A b k hk i hi,
    sourceConstructedPivotedStoredQRPseq_matMulVec_prefix_eq
      fp hn hmn A _ k hk i hi]
  simp

/-- A zero active matrix input takes the guarded identity branch on the paired
RHS and has zero exact-shadow residual. -/
theorem sourceConstructedPivotedStoredQRRhsEseq_eq_zero_of_input_eq_zero
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (k : ℕ) (hk : k < n)
    (hx : sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k = 0) :
    sourceConstructedPivotedStoredQRRhsEseq fp hn hmn A b k = 0 := by
  funext i
  rw [sourceConstructedPivotedStoredQRRhsEseq,
    fl_sourceConstructedPivotedStoredQRRhsSeq_succ]
  simp only [fl_sourceConstructedPivotedStoredQRRhsStep, dif_pos hk]
  rw [dif_pos hx,
    sourceConstructedPivotedStoredQRPseq_eq_id_of_input_eq_zero
      fp hn hmn A k hx,
    congrFun (matMulVec_id m
      (fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b k)) i]
  simp

/-- Unconditional local scaled entrywise bound for the actual paired RHS.
The only scale premise describes the current active RHS norm; it is not a
residual or output contract. -/
theorem sourceConstructedPivotedStoredQRRhsEseq_active_abs_le_scaled
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (k : ℕ) (hk : k < n)
    (hx : sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k ≠ 0)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (hb : vecNorm2
        (sourceConstructedPivotedStoredQRRhsWork fp hn hmn A k
          (fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b k)) ≤
      rho * vecNorm2
        (sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k))
    (i : Fin m) (hi : k ≤ i.val) :
    |sourceConstructedPivotedStoredQRRhsEseq fp hn hmn A b k i| ≤
      fp.u *
          |fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b k i| +
        gamma fp (11 * m + 23) * Real.sqrt 2 * rho *
          |sourceConstructedPivotedStoredQRExactRawVector
            fp hn hmn A k i| := by
  let hm : 0 < m := lt_of_lt_of_le hn hmn
  let S := sourceConstructedPivotedStoredQRRowSwap fp hn hmn A k
  let x := sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k
  let c := fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b k
  let work := sourceConstructedPivotedStoredQRRhsWork fp hn hmn A k c
  let v0 := sourceConstructedPivotedStoredQRExactRawVectorPerm fp hn hmn A k
  let beta := sourceConstructedPivotedStoredQRExactBeta fp hn hmn A k
  have hraw := fl_householderConstructApply_raw_entrywise_error_scaled
    fp hm x work (by simpa [x] using hx) rho hrho (by simpa [work, c, x] using hb)
      hvalid (S i)
  have hwork := sourceConstructedPivotedStoredQRPseq_matMulVec_eq_rhsWork
    fp hn hmn A c k hk i hi
  have hSinv : S (S i) = i := by
    simp [S, sourceConstructedPivotedStoredQRRowSwap,
      sourceConstructedRowSwap, hk]
  have hworkEntry : work (S i) = c i := by
    change (if (S (S i)).val < k then 0 else c (S (S i))) = c i
    rw [hSinv, if_neg (Nat.not_lt.mpr hi)]
  have hv : householderVector hm x (S i) =
      sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A k i := by
    rfl
  rw [sourceConstructedPivotedStoredQRRhsEseq,
    fl_sourceConstructedPivotedStoredQRRhsSeq_succ]
  simp only [fl_sourceConstructedPivotedStoredQRRhsStep, dif_pos hk]
  rw [dif_neg hx, if_neg (Nat.not_lt.mpr hi), hwork]
  simpa [hm, S, x, c, work, v0, beta, hworkEntry, hv] using hraw

/-! ## Printed `phi` and RHS row scale for the literal trace -/

noncomputable def sourceConstructedPivotedStoredQRRhsActiveNorm
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (k : ℕ) : ℝ :=
  vecNorm2 (sourceConstructedPivotedStoredQRRhsWork fp hn hmn A k
    (fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b k))

/-- The executor's work-coordinate RHS norm is exactly Higham's printed
active-tail norm in stored row coordinates.  Thus the work-array row exchange
does not change the `phi` numerator. -/
theorem sourceConstructedPivotedStoredQRRhsActiveNorm_eq_trailingPart
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (k : ℕ) (hk : k < n) :
    sourceConstructedPivotedStoredQRRhsActiveNorm fp hn hmn A b k =
      vecNorm2
        (householderTrailingPart m (pivotedQRActiveRow hmn k hk)
          (fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b k)) := by
  let S := sourceConstructedPivotedStoredQRRowSwap fp hn hmn A k
  let c := fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b k
  let tail := householderTrailingPart m (pivotedQRActiveRow hmn k hk) c
  have hwork :
      sourceConstructedPivotedStoredQRRhsWork fp hn hmn A k c =
        vecPermute S tail := by
    funext q
    change (if (S q).val < k then 0 else c (S q)) =
      (if (S q).val < (pivotedQRActiveRow hmn k hk).val then 0
        else c (S q))
    simp [pivotedQRActiveRow]
  rw [sourceConstructedPivotedStoredQRRhsActiveNorm, show
    fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b k = c by rfl,
    hwork]
  unfold vecNorm2
  rw [vecNorm2Sq_permute]

/-- Literal common-reflector tail ratio, expressed in the work-array row
coordinates used by the executor. -/
noncomputable def sourceConstructedPivotedStoredQRPrintedPhi
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) : ℝ :=
  ⨆ k : Fin n,
    sourceConstructedPivotedStoredQRRhsActiveNorm fp hn hmn A b k.val /
      sourceConstructedPivotedStoredQRSigma fp hn hmn A k.val

/-- Source-coordinate presentation of the literal printed `phi`. -/
theorem sourceConstructedPivotedStoredQRPrintedPhi_eq_trailingPart
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    sourceConstructedPivotedStoredQRPrintedPhi fp hn hmn A b =
      ⨆ k : Fin n,
        vecNorm2
            (householderTrailingPart m
              (pivotedQRActiveRow hmn k.val k.isLt)
              (fl_sourceConstructedPivotedStoredQRRhsSeq
                fp hn hmn A b k.val)) /
          sourceConstructedPivotedStoredQRSigma fp hn hmn A k.val := by
  unfold sourceConstructedPivotedStoredQRPrintedPhi
  refine iSup_congr ?_
  intro k
  rw [sourceConstructedPivotedStoredQRRhsActiveNorm_eq_trailingPart
    fp hn hmn A b k.val k.isLt]

theorem sourceConstructedPivotedStoredQRPrintedPhi_nonneg
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    0 ≤ sourceConstructedPivotedStoredQRPrintedPhi fp hn hmn A b := by
  let k0 : Fin n := ⟨0, hn⟩
  have h0 : 0 ≤
      sourceConstructedPivotedStoredQRRhsActiveNorm fp hn hmn A b k0.val /
        sourceConstructedPivotedStoredQRSigma fp hn hmn A k0.val :=
    div_nonneg (vecNorm2_nonneg _) (vecNorm2_nonneg _)
  exact h0.trans (le_ciSup
    (Finite.bddAbove_range (fun k : Fin n =>
      sourceConstructedPivotedStoredQRRhsActiveNorm fp hn hmn A b k.val /
        sourceConstructedPivotedStoredQRSigma fp hn hmn A k.val)) k0)

theorem sourceConstructedPivotedStoredQRRhsActiveNorm_div_sigma_le_phi
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (k : ℕ) (hk : k < n) :
    sourceConstructedPivotedStoredQRRhsActiveNorm fp hn hmn A b k /
        sourceConstructedPivotedStoredQRSigma fp hn hmn A k ≤
      sourceConstructedPivotedStoredQRPrintedPhi fp hn hmn A b := by
  exact le_ciSup
    (Finite.bddAbove_range (fun q : Fin n =>
      sourceConstructedPivotedStoredQRRhsActiveNorm fp hn hmn A b q.val /
        sourceConstructedPivotedStoredQRSigma fp hn hmn A q.val))
    ⟨k, hk⟩

theorem sourceConstructedPivotedStoredQRRhsActiveNorm_le_phi_mul_sigma
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (k : ℕ) (hk : k < n)
    (hsigma : 0 < sourceConstructedPivotedStoredQRSigma fp hn hmn A k) :
    sourceConstructedPivotedStoredQRRhsActiveNorm fp hn hmn A b k ≤
      sourceConstructedPivotedStoredQRPrintedPhi fp hn hmn A b *
        sourceConstructedPivotedStoredQRSigma fp hn hmn A k := by
  exact (div_le_iff₀ hsigma).mp
    (sourceConstructedPivotedStoredQRRhsActiveNorm_div_sigma_le_phi
      fp hn hmn A b k hk)

noncomputable def sourceConstructedPivotedStoredQRRhsRowGrowthScale
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (i : Fin m) : ℝ :=
  ⨆ t : Fin (n + 1),
    |fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b t.val i|

noncomputable def sourceConstructedPivotedStoredQRPrintedBetaScale
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (i : Fin m) : ℝ :=
  max
    (sourceConstructedPivotedStoredQRPrintedPhi fp hn hmn A b *
      sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A i)
    (sourceConstructedPivotedStoredQRRhsRowGrowthScale fp hn hmn A b i)

theorem sourceConstructedPivotedStoredQRRhsRowGrowthScale_nonneg
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (i : Fin m) :
    0 ≤ sourceConstructedPivotedStoredQRRhsRowGrowthScale fp hn hmn A b i := by
  have h0 : 0 ≤
      |fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b 0 i| :=
    abs_nonneg _
  exact h0.trans (le_ciSup
    (Finite.bddAbove_range (fun t : Fin (n + 1) =>
      |fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b t.val i|))
    (0 : Fin (n + 1)))

theorem sourceConstructedPivotedStoredQRPrintedBetaScale_nonneg
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (i : Fin m) :
    0 ≤ sourceConstructedPivotedStoredQRPrintedBetaScale fp hn hmn A b i := by
  apply le_max_of_le_right
  exact sourceConstructedPivotedStoredQRRhsRowGrowthScale_nonneg
    fp hn hmn A b i

theorem fl_sourceConstructedPivotedStoredQRRhsSeq_abs_le_printedBetaScale
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (k : ℕ) (hk : k < n) (i : Fin m) :
    |fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b k i| ≤
      sourceConstructedPivotedStoredQRPrintedBetaScale fp hn hmn A b i := by
  have hhist :
      |fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b k i| ≤
        sourceConstructedPivotedStoredQRRhsRowGrowthScale fp hn hmn A b i := by
    exact le_ciSup
      (Finite.bddAbove_range (fun t : Fin (n + 1) =>
        |fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b t.val i|))
      ⟨k, Nat.lt_succ_of_le (Nat.le_of_lt hk)⟩
  exact hhist.trans (le_max_right _ _)

/-- Source-shaped local RHS budget for the literal executor.  The zero-pivot
branch is exact; otherwise `phi` supplies the current active-tail ratio and
the printed beta scale absorbs both the current RHS row and the matrix row
scale. -/
theorem sourceConstructedPivotedStoredQRRhsEseq_abs_le_printedBetaScale
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (hgammaHalf : gamma fp (m + 1) ≤ (1 : ℝ) / 2)
    (k : ℕ) (hk : k < n) (i : Fin m) :
    |sourceConstructedPivotedStoredQRRhsEseq fp hn hmn A b k i| ≤
      (fp.u + 3 * Real.sqrt 2 * gamma fp (11 * m + 23)) *
        sourceConstructedPivotedStoredQRPrintedBetaScale fp hn hmn A b i := by
  let x := sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k
  let phi := sourceConstructedPivotedStoredQRPrintedPhi fp hn hmn A b
  let alpha := sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A
  let betaScale := sourceConstructedPivotedStoredQRPrintedBetaScale
    fp hn hmn A b
  have hphi0 : 0 ≤ phi := by
    exact sourceConstructedPivotedStoredQRPrintedPhi_nonneg fp hn hmn A b
  have halpha0 : ∀ r, 0 ≤ alpha r := by
    intro r
    exact sourceConstructedPivotedStoredQRPrintedAlphaScale_nonneg
      fp hn hmn A r
  have hbeta0 : ∀ r, 0 ≤ betaScale r := by
    intro r
    exact sourceConstructedPivotedStoredQRPrintedBetaScale_nonneg
      fp hn hmn A b r
  have hgamma0 : 0 ≤ gamma fp (11 * m + 23) := gamma_nonneg fp hvalid
  have hcoeff0 : 0 ≤ fp.u + 3 * Real.sqrt 2 * gamma fp (11 * m + 23) :=
    add_nonneg fp.u_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hgamma0)
  by_cases hx : x = 0
  · have hzero := sourceConstructedPivotedStoredQRRhsEseq_eq_zero_of_input_eq_zero
      fp hn hmn A b k hk (by simpa [x] using hx)
    rw [congrFun hzero i]
    simpa using mul_nonneg hcoeff0 (hbeta0 i)
  by_cases hi : i.val < k
  · rw [sourceConstructedPivotedStoredQRRhsEseq_prefix_zero
      fp hn hmn A b k hk i hi, abs_zero]
    exact mul_nonneg hcoeff0 (hbeta0 i)
  · have hsigma : 0 < sourceConstructedPivotedStoredQRSigma
        fp hn hmn A k := by
      change 0 < vecNorm2 x
      have hxnorm : vecNorm2 x ≠ 0 := by
        intro hnorm
        apply hx
        funext q
        exact (vecNorm2_eq_zero_iff x).mp hnorm q
      exact lt_of_le_of_ne (vecNorm2_nonneg x) (Ne.symm hxnorm)
    have htail := sourceConstructedPivotedStoredQRRhsActiveNorm_le_phi_mul_sigma
      fp hn hmn A b k hk hsigma
    have hlocal := sourceConstructedPivotedStoredQRRhsEseq_active_abs_le_scaled
      fp hn hmn A b hvalid k hk (by simpa [x] using hx) phi hphi0
      (by simpa [sourceConstructedPivotedStoredQRRhsActiveNorm,
          sourceConstructedPivotedStoredQRSigma, x, phi] using htail)
      i (Nat.le_of_not_gt hi)
    have hbrow := fl_sourceConstructedPivotedStoredQRRhsSeq_abs_le_printedBetaScale
      fp hn hmn A b k hk i
    have hv :=
      sourceConstructedPivotedStoredQRExactRawVector_abs_le_three_printedAlphaScale
        fp hn hmn A k hk
          (gammaValid_mono fp (by omega) hvalid) hgammaHalf i
    have hphiAlpha : phi * alpha i ≤ betaScale i := by
      exact le_max_left _ _
    have hfirst : fp.u *
          |fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b k i| ≤
        fp.u * betaScale i :=
      mul_le_mul_of_nonneg_left hbrow fp.u_nonneg
    have hsecond :
        gamma fp (11 * m + 23) * Real.sqrt 2 * phi *
            |sourceConstructedPivotedStoredQRExactRawVector
              fp hn hmn A k i| ≤
          (3 * Real.sqrt 2 * gamma fp (11 * m + 23)) * betaScale i := by
      calc
        gamma fp (11 * m + 23) * Real.sqrt 2 * phi *
            |sourceConstructedPivotedStoredQRExactRawVector
              fp hn hmn A k i| ≤
            gamma fp (11 * m + 23) * Real.sqrt 2 * phi * (3 * alpha i) :=
          mul_le_mul_of_nonneg_left hv
            (mul_nonneg (mul_nonneg hgamma0 (Real.sqrt_nonneg _)) hphi0)
        _ = (3 * Real.sqrt 2 * gamma fp (11 * m + 23)) *
            (phi * alpha i) := by ring
        _ ≤ (3 * Real.sqrt 2 * gamma fp (11 * m + 23)) * betaScale i :=
          mul_le_mul_of_nonneg_left hphiAlpha
            (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hgamma0)
    calc
      |sourceConstructedPivotedStoredQRRhsEseq fp hn hmn A b k i| ≤
          fp.u *
              |fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b k i| +
            gamma fp (11 * m + 23) * Real.sqrt 2 * phi *
              |sourceConstructedPivotedStoredQRExactRawVector
                fp hn hmn A k i| := hlocal
      _ ≤ fp.u * betaScale i +
          (3 * Real.sqrt 2 * gamma fp (11 * m + 23)) * betaScale i :=
        add_le_add hfirst hsecond
      _ = (fp.u + 3 * Real.sqrt 2 * gamma fp (11 * m + 23)) *
          betaScale i := by ring

end Theorem20_7

end NumStability
