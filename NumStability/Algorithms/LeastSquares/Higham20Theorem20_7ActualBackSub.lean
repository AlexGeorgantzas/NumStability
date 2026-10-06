import NumStability.Algorithms.LeastSquares.Higham20Theorem20_7ActualAssembly

namespace NumStability

open scoped BigOperators

namespace Theorem20_7

/-!
# Rounded back substitution for the actually executed source trace

This file supplies the final Cox--Higham bridge for the literal rounded
column-pivoted QR trace.  In particular, the triangular perturbation produced
by `fl_backSub` is pulled through the *actual* accumulated Householder factor;
it is not postulated by a readiness or target-bearing policy premise.
-/

/-- Every entry in the newly completed pivot row is controlled by the active
pivot scale.  This is the coordinate form of active maximality plus the local
rounded application residual. -/
theorem fl_sourceConstructedPivotedStoredQRMatrixSeq_succ_pivotRow_abs_le
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (k : ℕ) (hk : k < n) (j : Fin n) (hj : k ≤ j.val) :
    |fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A (k + 1)
        (pivotedQRActiveRow hmn k hk) j| ≤
      (1 + sourceConstructedPivotedStoredQRResidualNormCoeff fp m) *
        sourceConstructedPivotedStoredQRSigma fp hn hmn A k := by
  let row := pivotedQRActiveRow hmn k hk
  let v := sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A k
  let beta := sourceConstructedPivotedStoredQRExactBeta fp hn hmn A k
  let P := sourceConstructedPivotedStoredQRPseq fp hn hmn A k
  let As := sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k
  let E := sourceConstructedPivotedStoredQREseq fp hn hmn A k
  let sigma := sourceConstructedPivotedStoredQRSigma fp hn hmn A k
  let D := sourceConstructedPivotedStoredQRResidualNormCoeff fp m
  have hP : IsOrthogonal m P := by
    simpa [P] using
      sourceConstructedPivotedStoredQRPseq_orthogonal_unconditional
        fp hn hmn A k
  have hvprefix : ∀ i : Fin m, i.val < row.val → v i = 0 := by
    intro i hi
    simpa [v, row, pivotedQRActiveRow] using
      sourceConstructedPivotedStoredQRExactRawVector_zero_prefix
        fp hn hmn A k hk i (by simpa [row, pivotedQRActiveRow] using hi)
  have hexact :
      |matMulVec m P (fun r => As r j) row| ≤
        vecNorm2 (householderTrailingPart m row (fun r => As r j)) := by
    simpa [P, v, beta] using
      abs_matMulVec_householder_pivot_le_trailing_vecNorm2_of_zero_prefix_orthogonal
        m row v beta (fun r => As r j) hvprefix
          (by simpa [P, v, beta,
            sourceConstructedPivotedStoredQRPseq] using hP)
  have htailEq :
      vecNorm2 (householderTrailingPart m row (fun r => As r j)) =
        vecNorm2 (fun q =>
          sourceConstructedPivotedStoredQRActivePanelPerm fp hn hmn A k q j) := by
    have hcol := sourceConstructedPivotedStoredQRActivePanelPerm_col_eq
      fp hn hmn A k hk j
    rw [hcol]
    unfold vecNorm2
    rw [vecNorm2Sq_permute]
  have htail :
      vecNorm2 (householderTrailingPart m row (fun r => As r j)) ≤ sigma := by
    rw [htailEq]
    simpa [sigma] using
      sourceConstructedPivotedStoredQRActiveInput_pivot_max
        fp hn hmn A k hk j hj
  have hEcoord : |E row j| ≤ D * sigma := by
    calc
      |E row j| ≤ vecNorm2 (fun i => E i j) :=
        abs_coord_le_vecNorm2 (fun i => E i j) row
      _ ≤ D * sigma := by
        simpa [E, D, sigma] using
          sourceConstructedPivotedStoredQREseq_vecNorm2_le_sigma
            fp hn hmn A hvalid k hk j
  have hstep := sourceConstructedPivotedStoredQR_step_with_residual
    fp hn hmn A k row j
  change |fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A (k + 1)
      row j| ≤ (1 + D) * sigma
  rw [hstep]
  calc
    |matMulRect m m n P As row j + E row j| ≤
        |matMulRect m m n P As row j| + |E row j| := abs_add_le _ _
    _ ≤ sigma + D * sigma := by
      apply add_le_add _ hEcoord
      simpa [matMulRect, matMulVec] using hexact.trans htail
    _ = (1 + D) * sigma := by ring

/-- Once row `k` has been completed, later active column exchanges only
permute entries satisfying the same pivot-scale bound, and later panel steps
copy that row exactly. -/
theorem fl_sourceConstructedPivotedStoredQRMatrixSeq_completedRow_abs_le
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (k : ℕ) (hk : k < n) (r : ℕ) (hkr : k + 1 ≤ r) (hrn : r ≤ n)
    (j : Fin n) (hj : k ≤ j.val) :
    |fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A r
        (pivotedQRActiveRow hmn k hk) j| ≤
      (1 + sourceConstructedPivotedStoredQRResidualNormCoeff fp m) *
        sourceConstructedPivotedStoredQRSigma fp hn hmn A k := by
  let row := pivotedQRActiveRow hmn k hk
  let B := (1 + sourceConstructedPivotedStoredQRResidualNormCoeff fp m) *
    sourceConstructedPivotedStoredQRSigma fp hn hmn A k
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkr
  revert j
  induction d with
  | zero =>
      intro j hj
      simpa [row, B] using
        fl_sourceConstructedPivotedStoredQRMatrixSeq_succ_pivotRow_abs_le
          fp hn hmn A hvalid k hk j hj
  | succ d ih =>
      intro j hj
      have hq : k + 1 + d < n := by omega
      let q := k + 1 + d
      let S := sourceConstructedPivotedStoredQRSwapSeq fp hn hmn A q
      have hrowq : row.val < q := by
        dsimp [row, q, pivotedQRActiveRow]
        omega
      have hstep := fl_sourceConstructedPivotedStoredQRMatrixSeq_succ_of_lt
        fp hn hmn A q hq
      have hcopy := fl_householderCoxHighamConstructedPanelStep_prevRow_eq
        fp (lt_of_lt_of_le hn hmn) (pivotedQRActiveRow hmn q hq)
          (pivotedQRActiveCol q hq)
          (sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A q)
          (i := row) (j := j) hrowq
      have hSj : k ≤ (S j).val := by
        by_cases hjq : j.val < q
        · have hfix := sourceConstructedPivotedStoredQRSwapSeq_fix_prefix
            fp hn hmn A q j hjq
          simpa [S, hfix] using hj
        · have hactive := sourceConstructedPivotedStoredQRSwapSeq_maps_active
            fp hn hmn A q j (Nat.le_of_not_gt hjq)
          exact le_trans (by omega : k ≤ q) (by simpa [S] using hactive)
      have hprev :
          |fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A q
              row (S j)| ≤ B := by
        exact ih (by omega) (by omega) (S j) hSj
      rw [show k + 1 + (d + 1) = q + 1 by omega, hstep, hcopy]
      simpa [sourceConstructedPivotedStoredQRSwappedPanel,
        Wave13.columnPermuteMatrix, S, B, row] using hprev

/-- Final-row form of the completed-row invariant. -/
theorem fl_sourceConstructedPivotedStoredQRMatrixSeq_finalRow_abs_le
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (k : ℕ) (hk : k < n) (j : Fin n) (hj : k ≤ j.val) :
    |fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A n
        (pivotedQRActiveRow hmn k hk) j| ≤
      (1 + sourceConstructedPivotedStoredQRResidualNormCoeff fp m) *
        sourceConstructedPivotedStoredQRSigma fp hn hmn A k := by
  exact fl_sourceConstructedPivotedStoredQRMatrixSeq_completedRow_abs_le
    fp hn hmn A hvalid k hk n (by omega) le_rfl j hj

/-- Square leading block of the final actual upper-trapezoidal factor. -/
noncomputable def sourceConstructedPivotedStoredQRTopR
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A n
    ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j

/-- Leading block of the paired, actually transformed right-hand side. -/
noncomputable def sourceConstructedPivotedStoredQRTopRhs
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) : Fin n → ℝ :=
  fun i => fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b n
    ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩

/-- Uniform raw-prefix row coefficient used by the actual `QΔR` transport. -/
noncomputable def sourceConstructedPivotedStoredQRQdRPrefixCoeff
    (fp : FPModel) (m : ℕ) : ℝ :=
  3 + 12 * (m : ℝ) * sourceConstructedPivotedStoredQRGrowthFactor fp m ^ m

/-- Dimension-only active-tail coefficient for a componentwise admissible
back-substitution perturbation.  The leading `1` also makes this coefficient
large enough for the direct rowwise correction. -/
noncomputable def sourceConstructedPivotedStoredQRBackSubEta
    (fp : FPModel) (m : ℕ) : ℝ :=
  gamma fp m *
    (1 + Real.sqrt (m : ℝ) *
      (1 + sourceConstructedPivotedStoredQRResidualNormCoeff fp m) *
        sourceConstructedPivotedStoredQRGrowthFactor fp m ^ m)

theorem sourceConstructedPivotedStoredQRQdRPrefixCoeff_nonneg
    (fp : FPModel) (m : ℕ)
    (hvalid : gammaValid fp (11 * m + 23)) :
    0 ≤ sourceConstructedPivotedStoredQRQdRPrefixCoeff fp m := by
  have hg0 : 0 ≤ sourceConstructedPivotedStoredQRGrowthFactor fp m :=
    le_trans (by norm_num)
      (one_le_sourceConstructedPivotedStoredQRGrowthFactor fp m hvalid)
  unfold sourceConstructedPivotedStoredQRQdRPrefixCoeff
  positivity

theorem sourceConstructedPivotedStoredQRBackSubEta_nonneg
    (fp : FPModel) (m : ℕ)
    (hvalid : gammaValid fp (11 * m + 23)) :
    0 ≤ sourceConstructedPivotedStoredQRBackSubEta fp m := by
  have hgm : 0 ≤ gamma fp m :=
    gamma_nonneg fp (gammaValid_mono fp (by omega) hvalid)
  have hD : 0 ≤ sourceConstructedPivotedStoredQRResidualNormCoeff fp m :=
    sourceConstructedPivotedStoredQRResidualNormCoeff_nonneg fp m hvalid
  have hg0 : 0 ≤ sourceConstructedPivotedStoredQRGrowthFactor fp m :=
    le_trans (by norm_num)
      (one_le_sourceConstructedPivotedStoredQRGrowthFactor fp m hvalid)
  unfold sourceConstructedPivotedStoredQRBackSubEta
  positivity

theorem sourceConstructedPivotedStoredQRTopR_abs_le_printedAlphaScale
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (i j : Fin n) :
    |sourceConstructedPivotedStoredQRTopR fp hn hmn A i j| ≤
      sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A
        ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ := by
  simpa [sourceConstructedPivotedStoredQRTopR,
    sourceConstructedPivotedStoredQRPrintedAlphaScale] using
      (Wave18D.abs_entry_le_rowInftyGrowthFactor
        (fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A) n
        ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ n le_rfl j)

theorem gamma_le_sourceConstructedPivotedStoredQRBackSubEta
    (fp : FPModel) {m n : ℕ} (hmn : n ≤ m)
    (hvalid : gammaValid fp (11 * m + 23)) :
    gamma fp n ≤ sourceConstructedPivotedStoredQRBackSubEta fp m := by
  let D := sourceConstructedPivotedStoredQRResidualNormCoeff fp m
  let g := sourceConstructedPivotedStoredQRGrowthFactor fp m
  let T := Real.sqrt (m : ℝ) * (1 + D) * g ^ m
  have hgmvalid : gammaValid fp m := gammaValid_mono fp (by omega) hvalid
  have hgm0 : 0 ≤ gamma fp m := gamma_nonneg fp hgmvalid
  have hD0 : 0 ≤ D := by
    simpa [D] using
      sourceConstructedPivotedStoredQRResidualNormCoeff_nonneg fp m hvalid
  have hg0 : 0 ≤ g := by
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1)
      (by simpa [g] using
        one_le_sourceConstructedPivotedStoredQRGrowthFactor fp m hvalid)
  have hT0 : 0 ≤ T := by simp [T]; positivity
  calc
    gamma fp n ≤ gamma fp m := gamma_mono fp hmn hgmvalid
    _ ≤ gamma fp m * (1 + T) := by
      nlinarith [mul_nonneg hgm0 hT0]
    _ = sourceConstructedPivotedStoredQRBackSubEta fp m := by
      simp [sourceConstructedPivotedStoredQRBackSubEta, T, D, g]

/-- The componentwise back-substitution error has the required printed row
bound, now with a produced dimension-only coefficient. -/
theorem sourceConstructedPivotedStoredQRBackSub_rectTopBlock_abs_le
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (dR : Fin n → Fin n → ℝ)
    (hdR : ∀ i j,
      |dR i j| ≤ gamma fp n *
        |sourceConstructedPivotedStoredQRTopR fp hn hmn A i j|)
    (i : Fin m) (j : Fin n) :
    |rectTopBlock (m := m) dR i j| ≤
      sourceConstructedPivotedStoredQRBackSubEta fp m *
        sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A i := by
  by_cases hi : i.val < n
  · let ii : Fin n := ⟨i.val, hi⟩
    have hd := hdR ii j
    have hR := sourceConstructedPivotedStoredQRTopR_abs_le_printedAlphaScale
      fp hn hmn A ii j
    have hgamma := gamma_le_sourceConstructedPivotedStoredQRBackSubEta
      fp hmn hvalid
    have halpha := sourceConstructedPivotedStoredQRPrintedAlphaScale_nonneg
      fp hn hmn A i
    have hscale :
        gamma fp n *
            sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A i ≤
          sourceConstructedPivotedStoredQRBackSubEta fp m *
            sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A i :=
      mul_le_mul_of_nonneg_right hgamma halpha
    rw [rectTopBlock_top dR i j hi]
    calc
      |dR ii j| ≤ gamma fp n *
          |sourceConstructedPivotedStoredQRTopR fp hn hmn A ii j| := hd
      _ ≤ gamma fp n *
          sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A i := by
        apply mul_le_mul_of_nonneg_left _
          (gamma_nonneg fp (gammaValid_mono fp (by omega) hvalid))
        simpa [ii] using hR
      _ ≤ _ := hscale
  · rw [rectTopBlock_bottom dR i j (Nat.le_of_not_gt hi), abs_zero]
    exact mul_nonneg
      (sourceConstructedPivotedStoredQRBackSubEta_nonneg fp m hvalid)
      (sourceConstructedPivotedStoredQRPrintedAlphaScale_nonneg
        fp hn hmn A i)

/-- Coordinate bound for the active tail of an admissible triangular
perturbation, relative to the pivot scale at the start of that tail. -/
theorem sourceConstructedPivotedStoredQRBackSub_tail_entry_abs_le
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (dR : Fin n → Fin n → ℝ)
    (hdR : ∀ i j,
      |dR i j| ≤ gamma fp n *
        |sourceConstructedPivotedStoredQRTopR fp hn hmn A i j|)
    (k : ℕ) (hk : k < n) (j : Fin n) (i : Fin m) :
    |householderTrailingPart m (pivotedQRActiveRow hmn k hk)
        (fun r => rectTopBlock (m := m) dR r j) i| ≤
      gamma fp m *
        (1 + sourceConstructedPivotedStoredQRResidualNormCoeff fp m) *
          sourceConstructedPivotedStoredQRGrowthFactor fp m ^ m *
            sourceConstructedPivotedStoredQRSigma fp hn hmn A k := by
  let row := pivotedQRActiveRow hmn k hk
  let D := sourceConstructedPivotedStoredQRResidualNormCoeff fp m
  let g := sourceConstructedPivotedStoredQRGrowthFactor fp m
  let sigma := sourceConstructedPivotedStoredQRSigma fp hn hmn A
  have hgmvalid : gammaValid fp m := gammaValid_mono fp (by omega) hvalid
  have hgm0 : 0 ≤ gamma fp m := gamma_nonneg fp hgmvalid
  have hD0 : 0 ≤ D := by
    simpa [D] using
      sourceConstructedPivotedStoredQRResidualNormCoeff_nonneg fp m hvalid
  have hg1 : 1 ≤ g := by
    simpa [g] using one_le_sourceConstructedPivotedStoredQRGrowthFactor
      fp m hvalid
  have hg0 : 0 ≤ g := le_trans (by norm_num) hg1
  have htarget0 : 0 ≤
      gamma fp m * (1 + D) * g ^ m * sigma k := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hgm0 (by linarith)) (pow_nonneg hg0 m))
      (vecNorm2_nonneg _)
  by_cases hik : i.val < k
  · simp [householderTrailingPart, row, pivotedQRActiveRow, hik]
    exact htarget0
  · by_cases hin : i.val < n
    · let ii : Fin n := ⟨i.val, hin⟩
      have hki : k ≤ ii.val := by simp [ii]; omega
      by_cases hji : j.val < ii.val
      · have hupper :=
          fl_sourceConstructedPivotedStoredQRMatrixSeq_upperTrapezoidal
            fp hn hmn A ⟨ii.val, lt_of_lt_of_le ii.isLt hmn⟩ j hji
        have hRzero : sourceConstructedPivotedStoredQRTopR fp hn hmn A ii j = 0 := by
          simpa [sourceConstructedPivotedStoredQRTopR, ii] using hupper
        have hd := hdR ii j
        rw [hRzero, abs_zero, mul_zero] at hd
        have hd0 : dR ii j = 0 := abs_eq_zero.mp (le_antisymm hd (abs_nonneg _))
        simp [householderTrailingPart, row, pivotedQRActiveRow, hik,
          rectTopBlock, hin, ii, hd0]
        exact htarget0
      · have hR :=
          fl_sourceConstructedPivotedStoredQRMatrixSeq_finalRow_abs_le
            fp hn hmn A hvalid ii.val ii.isLt j (Nat.le_of_not_gt hji)
        have hsig := sourceConstructedPivotedStoredQRSigma_le_pow_mul_of_le
          fp hn hmn A hvalid k ii.val hki ii.isLt
        have hpow : g ^ (ii.val - k) ≤ g ^ m :=
          pow_le_pow_right₀ hg1 (by omega)
        have hsig0 : 0 ≤ sigma k := vecNorm2_nonneg _
        have hsigBound : sigma ii.val ≤ g ^ m * sigma k := by
          calc
            sigma ii.val ≤ g ^ (ii.val - k) * sigma k := by
              simpa [sigma, g] using hsig
            _ ≤ g ^ m * sigma k :=
              mul_le_mul_of_nonneg_right hpow hsig0
        have hRbound :
            |sourceConstructedPivotedStoredQRTopR fp hn hmn A ii j| ≤
              (1 + D) * g ^ m * sigma k := by
          calc
            |sourceConstructedPivotedStoredQRTopR fp hn hmn A ii j| ≤
                (1 + D) * sigma ii.val := by
              simpa [sourceConstructedPivotedStoredQRTopR, ii, D, sigma,
                pivotedQRActiveRow] using hR
            _ ≤ (1 + D) * (g ^ m * sigma k) :=
              mul_le_mul_of_nonneg_left hsigBound (by linarith)
            _ = (1 + D) * g ^ m * sigma k := by ring
        have hgn : gamma fp n ≤ gamma fp m := gamma_mono fp hmn hgmvalid
        have hd := hdR ii j
        have htarget :
            |dR ii j| ≤ gamma fp m * (1 + D) * g ^ m * sigma k := by
          calc
            |dR ii j| ≤ gamma fp n *
                |sourceConstructedPivotedStoredQRTopR fp hn hmn A ii j| := hd
            _ ≤ gamma fp m *
                |sourceConstructedPivotedStoredQRTopR fp hn hmn A ii j| :=
              mul_le_mul_of_nonneg_right hgn (abs_nonneg _)
            _ ≤ gamma fp m * ((1 + D) * g ^ m * sigma k) :=
              mul_le_mul_of_nonneg_left hRbound hgm0
            _ = gamma fp m * (1 + D) * g ^ m * sigma k := by ring
        simpa [householderTrailingPart, row, pivotedQRActiveRow, hik,
          rectTopBlock, hin, ii, D, g, sigma] using htarget
    · simp [householderTrailingPart, row, pivotedQRActiveRow, hik,
        rectTopBlock, hin]
      exact htarget0

/-- Produced active-tail norm bound used by the direct Householder multiplier
estimate in the `QΔR` expansion. -/
theorem sourceConstructedPivotedStoredQRBackSub_tail_vecNorm2_le
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (dR : Fin n → Fin n → ℝ)
    (hdR : ∀ i j,
      |dR i j| ≤ gamma fp n *
        |sourceConstructedPivotedStoredQRTopR fp hn hmn A i j|)
    (k : ℕ) (hk : k < n) (j : Fin n) :
    vecNorm2
        (householderTrailingPart m (pivotedQRActiveRow hmn k hk)
          (fun r => rectTopBlock (m := m) dR r j)) ≤
      sourceConstructedPivotedStoredQRBackSubEta fp m *
        sourceConstructedPivotedStoredQRSigma fp hn hmn A k := by
  let D := sourceConstructedPivotedStoredQRResidualNormCoeff fp m
  let g := sourceConstructedPivotedStoredQRGrowthFactor fp m
  let sigma := sourceConstructedPivotedStoredQRSigma fp hn hmn A k
  let B := gamma fp m * (1 + D) * g ^ m * sigma
  have hgm0 : 0 ≤ gamma fp m :=
    gamma_nonneg fp (gammaValid_mono fp (by omega) hvalid)
  have hD0 : 0 ≤ D := by
    simpa [D] using
      sourceConstructedPivotedStoredQRResidualNormCoeff_nonneg fp m hvalid
  have hg0 : 0 ≤ g := by
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1)
      (by simpa [g] using
        one_le_sourceConstructedPivotedStoredQRGrowthFactor fp m hvalid)
  have hsigma0 : 0 ≤ sigma := vecNorm2_nonneg _
  have hB0 : 0 ≤ B := by simp [B]; positivity
  have hnorm := vecNorm2_le_sqrt_card_mul_of_abs_le
    (householderTrailingPart m (pivotedQRActiveRow hmn k hk)
      (fun r => rectTopBlock (m := m) dR r j)) hB0
      (fun i => by
        simpa [B, D, g, sigma] using
          sourceConstructedPivotedStoredQRBackSub_tail_entry_abs_le
            fp hn hmn A hvalid dR hdR k hk j i)
  calc
    vecNorm2
        (householderTrailingPart m (pivotedQRActiveRow hmn k hk)
          (fun r => rectTopBlock (m := m) dR r j)) ≤
        Real.sqrt (m : ℝ) * B := hnorm
    _ ≤ sourceConstructedPivotedStoredQRBackSubEta fp m * sigma := by
      unfold sourceConstructedPivotedStoredQRBackSubEta
      simp only [B, D, g, sigma]
      have hcore : 0 ≤ Real.sqrt (m : ℝ) *
          (1 + sourceConstructedPivotedStoredQRResidualNormCoeff fp m) *
            sourceConstructedPivotedStoredQRGrowthFactor fp m ^ m := by
        positivity
      nlinarith [mul_nonneg hgm0 hsigma0,
        mul_nonneg (mul_nonneg hgm0 hcore) hsigma0]

/-- Rounded-growth replacement for the false exact cross-stage raw-vector
ratio. -/
theorem sourceConstructedPivotedStoredQRExactRawVector_norm_ratio_le
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (k : ℕ) (hk : k < n)
    (hsigma : 0 < sourceConstructedPivotedStoredQRSigma fp hn hmn A k)
    (q : ℕ) (hq : q < k) :
    vecNorm2 (sourceConstructedPivotedStoredQRExactRawVector
        fp hn hmn A k) /
      vecNorm2 (sourceConstructedPivotedStoredQRExactRawVector
        fp hn hmn A q) ≤
      2 * sourceConstructedPivotedStoredQRGrowthFactor fp m ^ m := by
  let sigma := sourceConstructedPivotedStoredQRSigma fp hn hmn A
  let raw := sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A
  let g := sourceConstructedPivotedStoredQRGrowthFactor fp m
  have hg1 : 1 ≤ g := by
    simpa [g] using one_le_sourceConstructedPivotedStoredQRGrowthFactor
      fp m hvalid
  have hg0 : 0 ≤ g := le_trans (by norm_num) hg1
  have hsigq : 0 < sigma q := by
    simpa [sigma] using
      sourceConstructedPivotedStoredQRSigma_pos_of_le_of_pos
        fp hn hmn A hvalid k hk (by simpa [sigma] using hsigma) q
          (Nat.le_of_lt hq)
  have hrawqLower : sigma q ≤ vecNorm2 (raw q) := by
    simpa [sigma, raw] using
      sourceConstructedPivotedStoredQRSigma_le_rawVector_vecNorm2
        fp hn hmn A q
  have hrawqPos : 0 < vecNorm2 (raw q) := lt_of_lt_of_le hsigq hrawqLower
  have hrawk := sourceConstructedPivotedStoredQRExactRawVector_vecNorm2_le_two_sigma
    fp hn hmn A k
  have hsigk := sourceConstructedPivotedStoredQRSigma_le_pow_mul_of_le
    fp hn hmn A hvalid q k (Nat.le_of_lt hq) hk
  have hpow : g ^ (k - q) ≤ g ^ m := pow_le_pow_right₀ hg1 (by omega)
  have hsigq0 : 0 ≤ sigma q := vecNorm2_nonneg _
  have hrawBound : vecNorm2 (raw k) ≤ 2 * g ^ m * vecNorm2 (raw q) := by
    calc
      vecNorm2 (raw k) ≤ 2 * sigma k := by simpa [raw, sigma] using hrawk
      _ ≤ 2 * (g ^ (k - q) * sigma q) :=
        mul_le_mul_of_nonneg_left (by simpa [sigma, g] using hsigk) (by norm_num)
      _ ≤ 2 * (g ^ m * sigma q) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_right hpow hsigq0
      _ ≤ 2 * g ^ m * vecNorm2 (raw q) := by
        calc
          2 * (g ^ m * sigma q) = (2 * g ^ m) * sigma q := by ring
          _ ≤ (2 * g ^ m) * vecNorm2 (raw q) :=
            mul_le_mul_of_nonneg_left hrawqLower
              (mul_nonneg (by norm_num) (pow_nonneg hg0 m))
  apply (div_le_iff₀ hrawqPos).2
  simpa [raw, g, mul_assoc] using hrawBound

/-- Actual-prefix image bound for a raw reflector vector.  It is derived from
the rounded pivot-growth envelope and therefore has no rounded-ordering policy
premise. -/
theorem sourceConstructedPivotedStoredQR_rawVector_prefix_entrywise_le
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (hgammaHalf : gamma fp (m + 1) ≤ (1 : ℝ) / 2)
    (k : ℕ) (hk : k < n)
    (hsigma : 0 < sourceConstructedPivotedStoredQRSigma fp hn hmn A k)
    (i : Fin m) :
    |Wave19.applyProd
        (fun q => householder m
          (sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A q)
          (sourceConstructedPivotedStoredQRExactBeta fp hn hmn A q)) 0 k
        (sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A k) i| ≤
      sourceConstructedPivotedStoredQRQdRPrefixCoeff fp m *
        sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A i := by
  let v := sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A
  let beta := sourceConstructedPivotedStoredQRExactBeta fp hn hmn A
  let alpha := sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A
  let g := sourceConstructedPivotedStoredQRGrowthFactor fp m
  have hbound := applyProd_rawHouseholder_entrywise_le_general
    v beta (v k) alpha 3 (2 * g ^ m) 3 k i
    (by norm_num)
    (sourceConstructedPivotedStoredQRPrintedAlphaScale_nonneg fp hn hmn A)
    (fun q => by
      simpa [v, beta, sourceConstructedPivotedStoredQRPseq] using
        sourceConstructedPivotedStoredQRPseq_orthogonal_unconditional
          fp hn hmn A q)
    (by
      intro q hq
      have hsigq := sourceConstructedPivotedStoredQRSigma_pos_of_le_of_pos
        fp hn hmn A hvalid k hk hsigma q (Nat.le_of_lt hq)
      exact lt_of_lt_of_le hsigq
        (sourceConstructedPivotedStoredQRSigma_le_rawVector_vecNorm2
          fp hn hmn A q))
    (by
      intro q hq
      have hsigq := sourceConstructedPivotedStoredQRSigma_pos_of_le_of_pos
        fp hn hmn A hvalid k hk hsigma q (Nat.le_of_lt hq)
      simpa [v, beta] using
        sourceConstructedPivotedStoredQRExactBeta_mul_vecNorm2_sq
          fp hn hmn A q hsigq)
    (by
      intro q hq r
      have hqn : q < n := lt_trans hq hk
      simpa [v, alpha] using
        sourceConstructedPivotedStoredQRExactRawVector_abs_le_three_printedAlphaScale
          fp hn hmn A q hqn (gammaValid_mono fp (by omega) hvalid)
            hgammaHalf r)
    (by
      intro q hq
      simpa [v, g] using
        sourceConstructedPivotedStoredQRExactRawVector_norm_ratio_le
          fp hn hmn A hvalid k hk hsigma q hq)
    (by
      simpa [v, alpha] using
        sourceConstructedPivotedStoredQRExactRawVector_abs_le_three_printedAlphaScale
          fp hn hmn A k hk (gammaValid_mono fp (by omega) hvalid)
            hgammaHalf i)
  have hg0 : 0 ≤ g := by
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1)
      (by simpa [g] using
        one_le_sourceConstructedPivotedStoredQRGrowthFactor fp m hvalid)
  have hkm : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast (le_trans (Nat.le_of_lt hk) hmn)
  have halpha := sourceConstructedPivotedStoredQRPrintedAlphaScale_nonneg
    fp hn hmn A i
  calc
    |Wave19.applyProd
        (fun q => householder m
          (sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A q)
          (sourceConstructedPivotedStoredQRExactBeta fp hn hmn A q)) 0 k
        (sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A k) i| ≤
      (3 + 2 * 3 * (k : ℝ) * (2 * g ^ m)) * alpha i := by
        simpa [v, beta, alpha] using hbound
    _ ≤ (3 + 12 * (m : ℝ) * g ^ m) * alpha i := by
      apply mul_le_mul_of_nonneg_right _ halpha
      have hpow0 : 0 ≤ g ^ m := pow_nonneg hg0 m
      nlinarith
    _ = sourceConstructedPivotedStoredQRQdRPrefixCoeff fp m *
        sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A i := by
      simp [sourceConstructedPivotedStoredQRQdRPrefixCoeff, alpha, g]

theorem sourceConstructedPivotedStoredQR_sqrt_two_sigma_le_rawVector_vecNorm2
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) :
    Real.sqrt 2 * sourceConstructedPivotedStoredQRSigma fp hn hmn A k ≤
      vecNorm2 (sourceConstructedPivotedStoredQRExactRawVector
        fp hn hmn A k) := by
  let hm : 0 < m := lt_of_lt_of_le hn hmn
  let x := sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k
  have hperm : vecNorm2
      (sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A k) =
        vecNorm2 (householderVector hm x) := by
    rw [sourceConstructedPivotedStoredQRExactRawVector_eq_vecPermute]
    unfold vecNorm2
    rw [vecNorm2Sq_permute]
    rfl
  rw [hperm]
  simpa [x, sourceConstructedPivotedStoredQRSigma] using
    householderVector_sign_norm_bound hm x

/-- Direct scalar-multiplier estimate for one actual reflector in the pulled
back triangular correction. -/
theorem sourceConstructedPivotedStoredQR_QdR_direct_multiplier_le
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < n)
    (hsigma : 0 < sourceConstructedPivotedStoredQRSigma fp hn hmn A k)
    {eta : ℝ} (heta : 0 ≤ eta) (dR : Fin n → Fin n → ℝ)
    (htail : ∀ j : Fin n,
      vecNorm2
          (householderTrailingPart m (pivotedQRActiveRow hmn k hk)
            (fun i => rectTopBlock (m := m) dR i j)) ≤
        eta * sourceConstructedPivotedStoredQRSigma fp hn hmn A k)
    (j : Fin n) :
    |sourceConstructedPivotedStoredQRExactBeta fp hn hmn A k *
        (∑ s : Fin m,
          sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A k s *
            rectTopBlock (m := m) dR s j)| ≤
      Real.sqrt 2 * eta := by
  let v := sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A k
  let f : Fin m → ℝ := fun s => rectTopBlock (m := m) dR s j
  let row := pivotedQRActiveRow hmn k hk
  let w := householderTrailingPart m row f
  let sigma := sourceConstructedPivotedStoredQRSigma fp hn hmn A k
  have hinner : (∑ s : Fin m, v s * f s) = ∑ s : Fin m, v s * w s := by
    apply Finset.sum_congr rfl
    intro s _hs
    by_cases hsk : s.val < k
    · have hvzero : v s = 0 := by
        simpa [v] using
          sourceConstructedPivotedStoredQRExactRawVector_zero_prefix
            fp hn hmn A k hk s hsk
      simp [hvzero]
    · have hsr : ¬ s.val < row.val := by
        simpa [row, pivotedQRActiveRow] using hsk
      simp [w, householderTrailingPart, hsr]
  have hvnorm : Real.sqrt 2 * |sigma| ≤ vecNorm2 v := by
    rw [abs_of_pos (by simpa [sigma] using hsigma)]
    simpa [v, sigma] using
      sourceConstructedPivotedStoredQR_sqrt_two_sigma_le_rawVector_vecNorm2
        fp hn hmn A k
  have hbeta : sourceConstructedPivotedStoredQRExactBeta fp hn hmn A k *
      vecNorm2 v ^ 2 = 2 := by
    simpa [v] using sourceConstructedPivotedStoredQRExactBeta_mul_vecNorm2_sq
      fp hn hmn A k (by simpa [sigma] using hsigma)
  have hw : vecNorm2 w ≤ eta * |sigma| := by
    rw [abs_of_pos (by simpa [sigma] using hsigma)]
    simpa [w, row, f, sigma] using htail j
  have h := householder_multiplier_le_sqrt_two_mul
    v w sigma (sourceConstructedPivotedStoredQRExactBeta fp hn hmn A k) eta
      (abs_pos.mpr (ne_of_gt (by simpa [sigma] using hsigma)))
      heta hvnorm hw hbeta
  simpa [v, f, hinner] using h

/-- Cox--Higham `(3.7)--(3.11)` for the actual rounded trace and the concrete
triangular perturbation returned by `fl_backSub`. -/
theorem sourceConstructedPivotedStoredQR_QdR_entrywise_le
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (hgammaHalf : gamma fp (m + 1) ≤ (1 : ℝ) / 2)
    (hsigma : ∀ k, k < n →
      0 < sourceConstructedPivotedStoredQRSigma fp hn hmn A k)
    (dR : Fin n → Fin n → ℝ)
    (hdR : ∀ i j,
      |dR i j| ≤ gamma fp n *
        |sourceConstructedPivotedStoredQRTopR fp hn hmn A i j|)
    (i : Fin m) (j : Fin n) :
    |matMulRect m m n (sourceConstructedPivotedStoredQRQ fp hn hmn A)
        (rectTopBlock (m := m) dR) i j| ≤
      (1 + 2 * (n : ℝ) *
          sourceConstructedPivotedStoredQRQdRPrefixCoeff fp m) *
        sourceConstructedPivotedStoredQRBackSubEta fp m *
          sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A i := by
  let v := sourceConstructedPivotedStoredQRExactRawVector fp hn hmn A
  let beta := sourceConstructedPivotedStoredQRExactBeta fp hn hmn A
  let P : ℕ → Fin m → Fin m → ℝ :=
    fun k => householder m (v k) (beta k)
  let f : Fin m → ℝ := fun s => rectTopBlock (m := m) dR s j
  let alpha := sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A
  let eta := sourceConstructedPivotedStoredQRBackSubEta fp m
  let K := sourceConstructedPivotedStoredQRQdRPrefixCoeff fp m
  have hQ :
      matMulRect m m n (sourceConstructedPivotedStoredQRQ fp hn hmn A)
          (rectTopBlock (m := m) dR) i j =
        Wave19.applyProd P 0 n f i := by
    rw [sourceConstructedPivotedStoredQRQ,
      sourceConstructedPivotedStoredQRQaccTotal_eq_actual
        fp hn hmn A n le_rfl]
    simpa [P, v, beta, f] using
      qacc_matMulRect_eq_applyProd
        (sourceConstructedPivotedStoredQRPseq fp hn hmn A)
        (fun k => householder_symmetric m (v k) (beta k)) n
        (rectTopBlock (m := m) dR) i j
  rw [hQ, applyProd_rawHouseholder_direct_expansion]
  have heta0 : 0 ≤ eta := by
    simpa [eta] using sourceConstructedPivotedStoredQRBackSubEta_nonneg
      fp m hvalid
  have hK0 : 0 ≤ K := by
    simpa [K] using sourceConstructedPivotedStoredQRQdRPrefixCoeff_nonneg
      fp m hvalid
  have halpha0 : 0 ≤ alpha i := by
    simpa [alpha] using
      sourceConstructedPivotedStoredQRPrintedAlphaScale_nonneg
        fp hn hmn A i
  have hsqrt : Real.sqrt 2 ≤ (2 : ℝ) := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have htail : ∀ k (hk : k < n) (col : Fin n),
      vecNorm2
          (householderTrailingPart m (pivotedQRActiveRow hmn k hk)
            (fun r => rectTopBlock (m := m) dR r col)) ≤
        eta * sourceConstructedPivotedStoredQRSigma fp hn hmn A k := by
    intro k hk col
    simpa [eta] using
      sourceConstructedPivotedStoredQRBackSub_tail_vecNorm2_le
        fp hn hmn A hvalid dR hdR k hk col
  have hterm : ∀ k ∈ Finset.range n,
      |Wave19.applyProd P 0 k (rawHouseholderDirectTerm v beta f k) i| ≤
        2 * K * eta * alpha i := by
    intro k hkset
    have hk : k < n := Finset.mem_range.mp hkset
    have hmult :
        |beta k * (∑ s : Fin m, v k s * f s)| ≤ Real.sqrt 2 * eta := by
      simpa [v, beta, f] using
        sourceConstructedPivotedStoredQR_QdR_direct_multiplier_le
          fp hn hmn A k hk (hsigma k hk) heta0 dR (htail k hk) j
    have hprefix : |Wave19.applyProd P 0 k (v k) i| ≤ K * alpha i := by
      simpa [P, v, beta, K, alpha] using
        sourceConstructedPivotedStoredQR_rawVector_prefix_entrywise_le
          fp hn hmn A hvalid hgammaHalf k hk (hsigma k hk) i
    rw [applyProd_rawHouseholderDirectTerm, abs_mul]
    calc
      |beta k * (∑ s : Fin m, v k s * f s)| *
          |Wave19.applyProd P 0 k (v k) i| ≤
        (Real.sqrt 2 * eta) * (K * alpha i) :=
          mul_le_mul hmult hprefix (abs_nonneg _)
            (mul_nonneg (Real.sqrt_nonneg _) heta0)
      _ = Real.sqrt 2 * (K * eta * alpha i) := by ring
      _ ≤ 2 * (K * eta * alpha i) :=
        mul_le_mul_of_nonneg_right hsqrt
          (mul_nonneg (mul_nonneg hK0 heta0) halpha0)
      _ = 2 * K * eta * alpha i := by ring
  have hsum :
      |∑ k ∈ Finset.range n,
          Wave19.applyProd P 0 k (rawHouseholderDirectTerm v beta f k) i| ≤
        (n : ℝ) * (2 * K * eta * alpha i) := by
    calc
      |∑ k ∈ Finset.range n,
          Wave19.applyProd P 0 k (rawHouseholderDirectTerm v beta f k) i| ≤
        ∑ k ∈ Finset.range n,
          |Wave19.applyProd P 0 k (rawHouseholderDirectTerm v beta f k) i| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range n, (2 * K * eta * alpha i) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hterm k hk
      _ = (n : ℝ) * (2 * K * eta * alpha i) := by simp
  have hf : |f i| ≤ eta * alpha i := by
    simpa [f, eta, alpha] using
      sourceConstructedPivotedStoredQRBackSub_rectTopBlock_abs_le
        fp hn hmn A hvalid dR hdR i j
  have hsub := abs_sub_le (f i) 0
    (∑ k ∈ Finset.range n,
      Wave19.applyProd P 0 k (rawHouseholderDirectTerm v beta f k) i)
  calc
    |f i - ∑ k ∈ Finset.range n,
        Wave19.applyProd P 0 k (rawHouseholderDirectTerm v beta f k) i| ≤
      |f i| + |∑ k ∈ Finset.range n,
        Wave19.applyProd P 0 k (rawHouseholderDirectTerm v beta f k) i| := by
          simpa using hsub
    _ ≤ eta * alpha i + (n : ℝ) * (2 * K * eta * alpha i) :=
      add_le_add hf hsum
    _ = (1 + 2 * (n : ℝ) * K) * eta * alpha i := by ring

/-- Pivot-coordinate total matrix perturbation after pulling the triangular
solve correction back through the actual orthogonal factor. -/
noncomputable def sourceConstructedPivotedStoredQRBackSubPivotDelta
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (dR : Fin n → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j => sourceConstructedPivotedStoredQRdA fp hn hmn A i j +
    matMulRect m m n (sourceConstructedPivotedStoredQRQ fp hn hmn A)
      (rectTopBlock (m := m) dR) i j

/-- Source-column ordering of the total matrix perturbation. -/
noncomputable def sourceConstructedPivotedStoredQRBackSubSourceDelta
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (dR : Fin n → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  let pi := sourceConstructedPivotedStoredQRPi fp hn hmn A
  fun i j => sourceConstructedPivotedStoredQRBackSubPivotDelta
    fp hn hmn A dR i (pi.symm j)

/-- Pivot-coordinate vector returned by floating-point back substitution on
the actual leading triangular block. -/
noncomputable def sourceConstructedPivotedStoredQRReturnedPivotX
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) : Fin n → ℝ :=
  fl_backSub fp n (sourceConstructedPivotedStoredQRTopR fp hn hmn A)
    (sourceConstructedPivotedStoredQRTopRhs fp hn hmn A b)

/-- Returned vector in source-column coordinates. -/
noncomputable def sourceConstructedPivotedStoredQRReturnedX
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) : Fin n → ℝ :=
  vecPermute (sourceConstructedPivotedStoredQRPi fp hn hmn A).symm
    (sourceConstructedPivotedStoredQRReturnedPivotX fp hn hmn A b)

/-- Exact minimizer assembly for the actual QR/RHS trace and the concrete
rounded triangular solve.  Its only algorithm-domain premise is nonbreakdown
of the computed leading triangular block. -/
theorem fl_sourceConstructedPivotedStoredQR_returnedX_exactMinimizer
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (hdiag : ∀ i : Fin n,
      sourceConstructedPivotedStoredQRTopR fp hn hmn A i i ≠ 0) :
    ∃ dR : Fin n → Fin n → ℝ,
      (∀ i j, |dR i j| ≤ gamma fp n *
        |sourceConstructedPivotedStoredQRTopR fp hn hmn A i j|) ∧
      IsLeastSquaresMinimizer
        (fun i j => A i j +
          sourceConstructedPivotedStoredQRBackSubSourceDelta
            fp hn hmn A dR i j)
        (fun i => b i +
          sourceConstructedPivotedStoredQRRhsDelta fp hn hmn A b i)
        (sourceConstructedPivotedStoredQRReturnedX fp hn hmn A b) := by
  let Pseq := sourceConstructedPivotedStoredQRPseqTotal fp hn hmn A
  let Q := sourceConstructedPivotedStoredQRQ fp hn hmn A
  let Rfull := fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A n
  let Rtop := sourceConstructedPivotedStoredQRTopR fp hn hmn A
  let cfull := fl_sourceConstructedPivotedStoredQRRhsSeq fp hn hmn A b n
  let ctop := sourceConstructedPivotedStoredQRTopRhs fp hn hmn A b
  let pi := sourceConstructedPivotedStoredQRPi fp hn hmn A
  let dA := sourceConstructedPivotedStoredQRdA fp hn hmn A
  let db := sourceConstructedPivotedStoredQRRhsDelta fp hn hmn A b
  let xPivot := sourceConstructedPivotedStoredQRReturnedPivotX fp hn hmn A b
  have hfac := fl_sourceConstructedPivotedStoredQR_actual_factorization
    fp hn hmn A
  dsimp only at hfac
  have hQ : IsOrthogonal m Q := by simpa [Q] using hfac.1
  have hRupper : IsUpperTrapezoidal m n Rfull := by
    simpa [Rfull] using hfac.2.1
  have hRtopUpper : ∀ i j : Fin n, j.val < i.val → Rtop i j = 0 := by
    intro i j hji
    simpa [Rtop, sourceConstructedPivotedStoredQRTopR, Rfull] using
      hRupper ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j hji
  rcases backSub_backward_error fp n Rtop ctop
      (by simpa [Rtop] using hdiag) hRtopUpper
      (gammaValid_mono fp (by omega) hvalid) with
    ⟨dR, hdR, hsolve⟩
  refine ⟨dR, ?_, ?_⟩
  · simpa [Rtop] using hdR
  · let topdR := rectTopBlock (m := m) dR
    let APivot : Fin m → Fin n → ℝ := fun i j =>
      Wave13.columnPermuteMatrix A pi i j + dA i j
    let APivotTotal : Fin m → Fin n → ℝ := fun i j =>
      APivot i j + matMulRect m m n Q topdR i j
    let Atrans : Fin m → Fin n → ℝ := fun i j => Rfull i j + topdR i j
    let bPert : Fin m → ℝ := fun i => b i + db i
    have hAhat : Rfull = matMulRect m m n (matTranspose Q) APivot := by
      funext i j
      simpa [Q, Rfull, pi, dA, APivot] using hfac.2.2.1 i j
    have hbhat : cfull = matMulVec m (matTranspose Q) bPert := by
      funext i
      simpa [Q, cfull, db, bPert] using
        sourceConstructedPivotedStoredQRRhs_telescope fp hn hmn A b i
    have hQTQ : matMul m (matTranspose Q) Q = idMatrix m :=
      funext fun i => funext fun j => hQ.left_inv i j
    have hpull :
        matMulRect m m n (matTranspose Q)
            (matMulRect m m n Q topdR) = topdR := by
      rw [← matMulRect_assoc_square_left, hQTQ, matMulRect_id_left]
    have hAtrans : Atrans =
        matMulRect m m n (matTranspose Q) APivotTotal := by
      rw [show APivotTotal = fun i j =>
          APivot i j + matMulRect m m n Q topdR i j by rfl,
        matMulRect_add_right, ← hAhat, hpull]
    have hA_top : ∀ (i : Fin m) (j : Fin n) (hi : i.val < n),
        Atrans i j = (fun r s => Rtop r s + dR r s) ⟨i.val, hi⟩ j := by
      intro i j hi
      have hRi : Rfull i j = Rtop ⟨i.val, hi⟩ j := by
        simp [Rfull, Rtop, sourceConstructedPivotedStoredQRTopR]
      have hdi : topdR i j = dR ⟨i.val, hi⟩ j := by
        simpa [topdR] using rectTopBlock_top dR i j hi
      simpa [Atrans] using congrArg₂ (· + ·) hRi hdi
    have hA_bottom : ∀ (i : Fin m) (j : Fin n), n ≤ i.val →
        Atrans i j = 0 := by
      intro i j hi
      have htopzero : topdR i j = 0 := by
        simpa [topdR] using rectTopBlock_bottom dR i j hi
      rw [show Atrans i j = Rfull i j + topdR i j by rfl,
        hRupper i j (lt_of_lt_of_le j.isLt hi), htopzero]
      ring
    have hb_top : ∀ (i : Fin m) (hi : i.val < n),
        cfull i = ctop ⟨i.val, hi⟩ := by
      intro i hi
      rfl
    have hsolve' : ∀ r : Fin n,
        matMulVec n (fun i j => Rtop i j + dR i j) xPivot r = ctop r := by
      intro r
      simpa [matMulVec, xPivot,
        sourceConstructedPivotedStoredQRReturnedPivotX, Rtop, ctop] using
          hsolve r
    have hNEtrans : RectLSNormalEquations Atrans cfull xPivot :=
      RectLSNormalEquations.of_top_solve_zero_bottom
        Atrans cfull (fun i j => Rtop i j + dR i j) ctop xPivot
          hA_top hA_bottom hb_top hsolve'
    have hNEPivot : RectLSNormalEquations APivotTotal bPert xPivot :=
      RectLSNormalEquations.of_orthogonal_left
        (matTranspose Q) APivotTotal Atrans bPert cfull xPivot hQ.transpose
          hAtrans hbhat hNEtrans
    have hMinPivot : IsLeastSquaresMinimizer APivotTotal bPert xPivot :=
      hNEPivot.isLeastSquaresMinimizer
    have hPermData : rectPermuteCols pi
        (fun i j => A i j +
          sourceConstructedPivotedStoredQRBackSubSourceDelta
            fp hn hmn A dR i j) = APivotTotal := by
      funext i j
      simp [rectPermuteCols,
        sourceConstructedPivotedStoredQRBackSubSourceDelta,
        sourceConstructedPivotedStoredQRBackSubPivotDelta,
        sourceConstructedPivotedStoredQRPi,
        sourceConstructedPivotedStoredQRdA, pi, Q, dA,
        APivotTotal, APivot, topdR, Wave13.columnPermuteMatrix]
      ring
    have hMinPerm : IsLeastSquaresMinimizer
        (rectPermuteCols pi
          (fun i j => A i j +
            sourceConstructedPivotedStoredQRBackSubSourceDelta
              fp hn hmn A dR i j)) bPert xPivot := by
      rw [hPermData]
      exact hMinPivot
    have hMinSource := IsLeastSquaresMinimizer.of_permuteCols pi
      (fun i j => A i j +
        sourceConstructedPivotedStoredQRBackSubSourceDelta
          fp hn hmn A dR i j) bPert xPivot hMinPerm
    simpa [bPert, db, xPivot,
      sourceConstructedPivotedStoredQRReturnedX, pi] using hMinSource

/-- A nonzero computed diagonal forces every executed pivot scale to be
positive.  This is derived from the completed-row bound, not assumed as a
separate reflector policy. -/
theorem sourceConstructedPivotedStoredQRSigma_pos_of_topR_diag_ne
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (hdiag : ∀ i : Fin n,
      sourceConstructedPivotedStoredQRTopR fp hn hmn A i i ≠ 0)
    (k : ℕ) (hk : k < n) :
    0 < sourceConstructedPivotedStoredQRSigma fp hn hmn A k := by
  let kk : Fin n := ⟨k, hk⟩
  have hs0 : 0 ≤ sourceConstructedPivotedStoredQRSigma fp hn hmn A k :=
    vecNorm2_nonneg _
  by_contra hnot
  have hsz : sourceConstructedPivotedStoredQRSigma fp hn hmn A k = 0 :=
    le_antisymm (le_of_not_gt hnot) hs0
  have hR := fl_sourceConstructedPivotedStoredQRMatrixSeq_finalRow_abs_le
    fp hn hmn A hvalid k hk kk (by simp [kk])
  have hR' : |sourceConstructedPivotedStoredQRTopR fp hn hmn A kk kk| ≤ 0 := by
    simpa [sourceConstructedPivotedStoredQRTopR, kk,
      pivotedQRActiveRow, hsz] using hR
  have hzero : sourceConstructedPivotedStoredQRTopR fp hn hmn A kk kk = 0 :=
    abs_eq_zero.mp (le_antisymm hR' (abs_nonneg _))
  exact (hdiag kk) hzero

/-- Dimension-only coefficient contributed by the pulled-back triangular
correction. -/
noncomputable def sourceConstructedPivotedStoredQRQdRCoeff
    (fp : FPModel) (m : ℕ) : ℝ :=
  (1 + 2 * (m : ℝ) * sourceConstructedPivotedStoredQRQdRPrefixCoeff fp m) *
    sourceConstructedPivotedStoredQRBackSubEta fp m

/-- One common dimension-only coefficient for both perturbations in the final
Theorem 20.7 statement. -/
noncomputable def sourceConstructedPivotedStoredQRFinalGammaTilde
    (fp : FPModel) (m : ℕ) : ℝ :=
  sourceConstructedPivotedStoredQRGammaTilde fp m +
    sourceConstructedPivotedStoredQRRhsGammaTilde fp m +
      sourceConstructedPivotedStoredQRQdRCoeff fp m

theorem sourceConstructedPivotedStoredQRQdRCoeff_nonneg
    (fp : FPModel) (m : ℕ)
    (hvalid : gammaValid fp (11 * m + 23)) :
    0 ≤ sourceConstructedPivotedStoredQRQdRCoeff fp m := by
  have hK := sourceConstructedPivotedStoredQRQdRPrefixCoeff_nonneg
    fp m hvalid
  have heta := sourceConstructedPivotedStoredQRBackSubEta_nonneg
    fp m hvalid
  unfold sourceConstructedPivotedStoredQRQdRCoeff
  positivity

theorem sourceConstructedPivotedStoredQRFinalGammaTilde_nonneg
    (fp : FPModel) (m : ℕ)
    (hvalid : gammaValid fp (11 * m + 23)) :
    0 ≤ sourceConstructedPivotedStoredQRFinalGammaTilde fp m := by
  unfold sourceConstructedPivotedStoredQRFinalGammaTilde
  exact add_nonneg
    (add_nonneg
      (sourceConstructedPivotedStoredQRGammaTilde_nonneg fp m hvalid)
      (sourceConstructedPivotedStoredQRRhsGammaTilde_nonneg fp m hvalid))
    (sourceConstructedPivotedStoredQRQdRCoeff_nonneg fp m hvalid)

/-- Uniform, source-column `QΔR` bound produced from the actual trace. -/
theorem sourceConstructedPivotedStoredQR_QdR_source_le
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (hgammaHalf : gamma fp (m + 1) ≤ (1 : ℝ) / 2)
    (hdiag : ∀ i : Fin n,
      sourceConstructedPivotedStoredQRTopR fp hn hmn A i i ≠ 0)
    (dR : Fin n → Fin n → ℝ)
    (hdR : ∀ i j,
      |dR i j| ≤ gamma fp n *
        |sourceConstructedPivotedStoredQRTopR fp hn hmn A i j|)
    (i : Fin m) (j : Fin n) :
    |matMulRect m m n (sourceConstructedPivotedStoredQRQ fp hn hmn A)
        (rectTopBlock (m := m) dR) i
        ((sourceConstructedPivotedStoredQRPi fp hn hmn A).symm j)| ≤
      sourceConstructedPivotedStoredQRQdRCoeff fp m *
        sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A i := by
  let K := sourceConstructedPivotedStoredQRQdRPrefixCoeff fp m
  let eta := sourceConstructedPivotedStoredQRBackSubEta fp m
  let alpha := sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A
  have h := sourceConstructedPivotedStoredQR_QdR_entrywise_le
    fp hn hmn A hvalid hgammaHalf
      (sourceConstructedPivotedStoredQRSigma_pos_of_topR_diag_ne
        fp hn hmn A hvalid hdiag)
      dR hdR i ((sourceConstructedPivotedStoredQRPi fp hn hmn A).symm j)
  have hK0 : 0 ≤ K := by simpa [K] using
    sourceConstructedPivotedStoredQRQdRPrefixCoeff_nonneg fp m hvalid
  have heta0 : 0 ≤ eta := by simpa [eta] using
    sourceConstructedPivotedStoredQRBackSubEta_nonneg fp m hvalid
  have halpha0 : 0 ≤ alpha i := by simpa [alpha] using
    sourceConstructedPivotedStoredQRPrintedAlphaScale_nonneg fp hn hmn A i
  have hnm : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmn
  calc
    |matMulRect m m n (sourceConstructedPivotedStoredQRQ fp hn hmn A)
        (rectTopBlock (m := m) dR) i
        ((sourceConstructedPivotedStoredQRPi fp hn hmn A).symm j)| ≤
      (1 + 2 * (n : ℝ) * K) * eta * alpha i := by
        simpa [K, eta, alpha] using h
    _ ≤ (1 + 2 * (m : ℝ) * K) * eta * alpha i := by
      have hc : 1 + 2 * (n : ℝ) * K ≤ 1 + 2 * (m : ℝ) * K := by
        nlinarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc heta0) halpha0
    _ = sourceConstructedPivotedStoredQRQdRCoeff fp m *
        sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A i := by
      simp [sourceConstructedPivotedStoredQRQdRCoeff, K, eta, alpha]

theorem sourceConstructedPivotedStoredQRdA_source_n_sq_le
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (hgammaHalf : gamma fp (m + 1) ≤ (1 : ℝ) / 2)
    (i : Fin m) (j : Fin n) :
    |sourceConstructedPivotedStoredQRdA fp hn hmn A i
        ((sourceConstructedPivotedStoredQRPi fp hn hmn A).symm j)| ≤
      (n : ℝ) ^ 2 *
        (5 * sourceConstructedPivotedStoredQRGammaTilde fp m) *
          sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A i := by
  let pi := sourceConstructedPivotedStoredQRPi fp hn hmn A
  let G := sourceConstructedPivotedStoredQRGammaTilde fp m
  let alpha := sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A
  have h := sourceConstructedPivotedStoredQRdA_abs_le_coxHigham
    fp hn hmn A hvalid hgammaHalf i (pi.symm j)
  have hfactor := pivotPositionFactor_le_sourceDimensionFactor pi j
  have hscale : 0 ≤ (5 * G) * alpha i :=
    mul_nonneg
      (mul_nonneg (by norm_num)
        (by simpa [G] using
          (sourceConstructedPivotedStoredQRGammaTilde_nonneg fp m hvalid)))
      (by simpa [alpha] using
        (sourceConstructedPivotedStoredQRPrintedAlphaScale_nonneg
          fp hn hmn A i))
  change |sourceConstructedPivotedStoredQRdA fp hn hmn A i (pi.symm j)| ≤
    (n : ℝ) ^ 2 * (5 * G) * alpha i
  calc
    |sourceConstructedPivotedStoredQRdA fp hn hmn A i (pi.symm j)| ≤
      (((pi.symm j).val : ℝ) + 1) ^ 2 * (5 * G) * alpha i := by
        simpa [pi, G, alpha] using h
    _ = (((pi.symm j).val : ℝ) + 1) ^ 2 * ((5 * G) * alpha i) := by ring
    _ ≤ (n : ℝ) ^ 2 * ((5 * G) * alpha i) :=
      mul_le_mul_of_nonneg_right hfactor hscale
    _ = (n : ℝ) ^ 2 * (5 * G) * alpha i := by ring

/-- Literal source-row matrix perturbation bound after including the produced
triangular correction. -/
theorem sourceConstructedPivotedStoredQRBackSubSourceDelta_abs_le
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (hgammaHalf : gamma fp (m + 1) ≤ (1 : ℝ) / 2)
    (hdiag : ∀ i : Fin n,
      sourceConstructedPivotedStoredQRTopR fp hn hmn A i i ≠ 0)
    (dR : Fin n → Fin n → ℝ)
    (hdR : ∀ i j,
      |dR i j| ≤ gamma fp n *
        |sourceConstructedPivotedStoredQRTopR fp hn hmn A i j|)
    (i : Fin m) (j : Fin n) :
    |sourceConstructedPivotedStoredQRBackSubSourceDelta
        fp hn hmn A dR i j| ≤
      (n : ℝ) ^ 2 *
        (5 * sourceConstructedPivotedStoredQRFinalGammaTilde fp m) *
          sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A i := by
  let N := (n : ℝ) ^ 2
  let M := sourceConstructedPivotedStoredQRGammaTilde fp m
  let H := sourceConstructedPivotedStoredQRRhsGammaTilde fp m
  let C := sourceConstructedPivotedStoredQRQdRCoeff fp m
  let alpha := sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A
  let pi := sourceConstructedPivotedStoredQRPi fp hn hmn A
  have hb := sourceConstructedPivotedStoredQRdA_source_n_sq_le
    fp hn hmn A hvalid hgammaHalf i j
  have hq := sourceConstructedPivotedStoredQR_QdR_source_le
    fp hn hmn A hvalid hgammaHalf hdiag dR hdR i j
  have hM0 : 0 ≤ M := by simpa [M] using
    sourceConstructedPivotedStoredQRGammaTilde_nonneg fp m hvalid
  have hH0 : 0 ≤ H := by simpa [H] using
    sourceConstructedPivotedStoredQRRhsGammaTilde_nonneg fp m hvalid
  have hC0 : 0 ≤ C := by simpa [C] using
    sourceConstructedPivotedStoredQRQdRCoeff_nonneg fp m hvalid
  have ha0 : 0 ≤ alpha i := by simpa [alpha] using
    sourceConstructedPivotedStoredQRPrintedAlphaScale_nonneg fp hn hmn A i
  have hN0 : 0 ≤ N := sq_nonneg _
  have hN1 : 1 ≤ N := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hCpack : C ≤ N * 5 * C := by
    calc
      C = 1 * C := by ring
      _ ≤ N * C := mul_le_mul_of_nonneg_right hN1 hC0
      _ ≤ (N * 5) * C :=
        mul_le_mul_of_nonneg_right (by nlinarith [hN0]) hC0
      _ = N * 5 * C := by ring
  change |sourceConstructedPivotedStoredQRdA fp hn hmn A i (pi.symm j) +
      matMulRect m m n (sourceConstructedPivotedStoredQRQ fp hn hmn A)
        (rectTopBlock (m := m) dR) i (pi.symm j)| ≤ _
  calc
    |sourceConstructedPivotedStoredQRdA fp hn hmn A i (pi.symm j) +
        matMulRect m m n (sourceConstructedPivotedStoredQRQ fp hn hmn A)
          (rectTopBlock (m := m) dR) i (pi.symm j)| ≤
      |sourceConstructedPivotedStoredQRdA fp hn hmn A i (pi.symm j)| +
        |matMulRect m m n (sourceConstructedPivotedStoredQRQ fp hn hmn A)
          (rectTopBlock (m := m) dR) i (pi.symm j)| := abs_add_le _ _
    _ ≤ N * (5 * M) * alpha i + C * alpha i := by
      exact add_le_add (by simpa [N, M, alpha, pi] using hb)
        (by simpa [C, alpha, pi] using hq)
    _ = (N * 5 * M + C) * alpha i := by ring
    _ ≤ (N * 5 * M + N * 5 * C) * alpha i := by
      apply mul_le_mul_of_nonneg_right _ ha0
      linarith
    _ = (N * 5 * (M + C)) * alpha i := by ring
    _ ≤ (N * 5 * (M + H + C)) * alpha i := by
      apply mul_le_mul_of_nonneg_right _ ha0
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg hN0 (by norm_num))
      linarith
    _ = (n : ℝ) ^ 2 *
        (5 * sourceConstructedPivotedStoredQRFinalGammaTilde fp m) *
          sourceConstructedPivotedStoredQRPrintedAlphaScale fp hn hmn A i := by
      dsimp [N, M, H, C, alpha,
        sourceConstructedPivotedStoredQRFinalGammaTilde]
      ring

theorem sourceConstructedPivotedStoredQRRhsDelta_abs_le_finalGamma
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (hgammaHalf : gamma fp (m + 1) ≤ (1 : ℝ) / 2)
    (i : Fin m) :
    |sourceConstructedPivotedStoredQRRhsDelta fp hn hmn A b i| ≤
      (n : ℝ) ^ 2 *
        (5 * sourceConstructedPivotedStoredQRFinalGammaTilde fp m) *
          sourceConstructedPivotedStoredQRPrintedBetaScale
            fp hn hmn A b i := by
  have h := sourceConstructedPivotedStoredQRRhsDelta_abs_le_coxHigham
    fp hn hmn A b hvalid hgammaHalf i
  have hR : sourceConstructedPivotedStoredQRRhsGammaTilde fp m ≤
      sourceConstructedPivotedStoredQRFinalGammaTilde fp m := by
    unfold sourceConstructedPivotedStoredQRFinalGammaTilde
    have hM := sourceConstructedPivotedStoredQRGammaTilde_nonneg fp m hvalid
    have hC := sourceConstructedPivotedStoredQRQdRCoeff_nonneg fp m hvalid
    linarith
  have hN : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have hrho := sourceConstructedPivotedStoredQRPrintedBetaScale_nonneg
    fp hn hmn A b i
  calc
    |sourceConstructedPivotedStoredQRRhsDelta fp hn hmn A b i| ≤
      (n : ℝ) ^ 2 *
        (5 * sourceConstructedPivotedStoredQRRhsGammaTilde fp m) *
          sourceConstructedPivotedStoredQRPrintedBetaScale
            fp hn hmn A b i := h
    _ ≤ (n : ℝ) ^ 2 *
        (5 * sourceConstructedPivotedStoredQRFinalGammaTilde fp m) *
          sourceConstructedPivotedStoredQRPrintedBetaScale
            fp hn hmn A b i := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hR (by norm_num)) hN) hrho

/-- Fully closed, source-facing Higham Theorem 20.7 endpoint for the literal
rounded column-pivoted Householder QR, paired RHS transformation, and rounded
back substitution.  No readiness, row-policy, tail-policy, residual, or target
bound is assumed. -/
theorem higham20_7_sourceConstructed_actual_closed
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (hgammaHalf : gamma fp (m + 1) ≤ (1 : ℝ) / 2)
    (hdiag : ∀ i : Fin n,
      sourceConstructedPivotedStoredQRTopR fp hn hmn A i i ≠ 0) :
    ∃ dR : Fin n → Fin n → ℝ,
      (∀ i j, |dR i j| ≤ gamma fp n *
        |sourceConstructedPivotedStoredQRTopR fp hn hmn A i j|) ∧
      IsLeastSquaresMinimizer
        (fun i j => A i j +
          sourceConstructedPivotedStoredQRBackSubSourceDelta
            fp hn hmn A dR i j)
        (fun i => b i +
          sourceConstructedPivotedStoredQRRhsDelta fp hn hmn A b i)
        (sourceConstructedPivotedStoredQRReturnedX fp hn hmn A b) ∧
      (∀ i j,
        |sourceConstructedPivotedStoredQRBackSubSourceDelta
            fp hn hmn A dR i j| ≤
          (n : ℝ) ^ 2 *
            (5 * sourceConstructedPivotedStoredQRFinalGammaTilde fp m) *
              sourceConstructedPivotedStoredQRPrintedAlphaScale
                fp hn hmn A i) ∧
      ∀ i,
        |sourceConstructedPivotedStoredQRRhsDelta fp hn hmn A b i| ≤
          (n : ℝ) ^ 2 *
            (5 * sourceConstructedPivotedStoredQRFinalGammaTilde fp m) *
              sourceConstructedPivotedStoredQRPrintedBetaScale
                fp hn hmn A b i := by
  rcases fl_sourceConstructedPivotedStoredQR_returnedX_exactMinimizer
      fp hn hmn A b hvalid hdiag with ⟨dR, hdR, hmin⟩
  refine ⟨dR, hdR, hmin, ?_, ?_⟩
  · intro i j
    exact sourceConstructedPivotedStoredQRBackSubSourceDelta_abs_le
      fp hn hmn A hvalid hgammaHalf hdiag dR hdR i j
  · intro i
    exact sourceConstructedPivotedStoredQRRhsDelta_abs_le_finalGamma
      fp hn hmn A b hvalid hgammaHalf i

end Theorem20_7

end NumStability
