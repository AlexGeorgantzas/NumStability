-- Algorithms/QR/HouseholderApplySupport.lean
-- Compact and stored Householder application support layer.
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.QR.HouseholderApply

import NumStability.Algorithms.QR.HouseholderSpecSupport

namespace NumStability

open scoped BigOperators

/-- Apply an explicitly formed Householder/orthogonal matrix to a vector using
    the repository's floating-point matrix-vector product. -/
noncomputable def fl_householderApplyExplicit (fp : FPModel) (n : ℕ)
    (P : Fin n → Fin n → ℝ) (b : Fin n → ℝ) : Fin n → ℝ :=
  fl_matVec fp n n P b

/-- Apply an explicitly formed Householder/orthogonal matrix columnwise to a
    rectangular panel using the repository's floating-point matrix-vector
    product for each column. -/
noncomputable def fl_householderApplyExplicitPanel (fp : FPModel) (m n : ℕ)
    (P : Fin m → Fin m → ℝ) (A : Fin m → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j => fl_householderApplyExplicit fp m P (fun a => A a j) i

/-- Exact dot product used by the compact Householder application formula. -/
noncomputable def householderDot (n : ℕ)
    (v b : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, v j * b j

/-- Absolute dot-product budget `∑ |v_j| |b_j|`. -/
noncomputable def householderAbsDotBudget (n : ℕ)
    (v b : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, |v j| * |b j|

/-- Compact rounded Householder application `b - β v (vᵀ b)`.

    This is the source-level primitive missing from the explicit-matrix route:
    it first computes the dot product, then scales by `β`, then performs the
    componentwise multiply-subtract update. -/
noncomputable def fl_householderApplyCompact (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) (b : Fin n → ℝ) : Fin n → ℝ :=
  let sigmaHat := fl_dotProduct fp n v b
  let tauHat := fp.fl_mul β sigmaHat
  fun i => fp.fl_sub (b i) (fp.fl_mul tauHat (v i))

/-- Columnwise compact rounded Householder application to a rectangular panel. -/
noncomputable def fl_householderApplyCompactPanel (fp : FPModel) (m n : ℕ)
    (v : Fin m → ℝ) (β : ℝ) (A : Fin m → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j => fl_householderApplyCompact fp m v β (fun a => A a j) i

/-- One stored rectangular Householder QR panel step.

    The raw compact update is used for the active/trailing panel, but completed
    columns are stored in QR form: earlier columns are preserved, and the new
    pivot column is explicitly zeroed below the pivot.  This models the
    algorithmic storage convention needed by the least-squares QR handoff; the
    compact floating-point error analysis remains in
    `fl_householderApplyCompactPanel`. -/
noncomputable def fl_householderStoredPanelStep (fp : FPModel) (m n k : ℕ)
    (v : Fin m → ℝ) (β : ℝ) (A : Fin m → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  let raw := fl_householderApplyCompactPanel fp m n v β A
  fun i j =>
    if j.val < k then
      A i j
    else if j.val = k then
      if k < i.val then 0 else raw i j
    else
      raw i j

/-- Stored Householder panel steps copy every column before the active pivot. -/
theorem fl_householderStoredPanelStep_prevColumn_eq (fp : FPModel)
    {m n k : ℕ} (v : Fin m → ℝ) (beta : ℝ)
    (A : Fin m → Fin n → ℝ) {i : Fin m} {j : Fin n}
    (hj : j.val < k) :
    fl_householderStoredPanelStep fp m n k v beta A i j = A i j := by
  simp [fl_householderStoredPanelStep, hj]

/-- One stored rectangular Householder QR right-hand-side step.

    Rows above the active pivot are preserved, while the active tail is updated
    by the compact dot-scale-subtract primitive. -/
noncomputable def fl_householderStoredRhsStep (fp : FPModel) (m k : ℕ)
    (v : Fin m → ℝ) (β : ℝ) (b : Fin m → ℝ) : Fin m → ℝ :=
  let raw := fl_householderApplyCompact fp m v β b
  fun i => if i.val < k then b i else raw i

/-- Componentwise deterministic error budget for compact Householder
    application.

    With `S = ∑ |v_j||b_j|`, the dot product contributes `γ_m S`; the two
    following multiplications and the final subtraction contribute the remaining
    `u`-terms.  This is intentionally explicit and data-dependent, so no
    concentration or unproved stability event is hidden inside the statement. -/
noncomputable def householderCompactComponentBudget (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) (b : Fin n → ℝ) (i : Fin n) : ℝ :=
  let S := householderAbsDotBudget n v b
  let D := gamma fp n * S
  let sigmaBudget := S + D
  let tauBudget := |β| * sigmaBudget * (1 + fp.u)
  let zBudget := tauBudget * |v i| * (1 + fp.u)
  let zError :=
    fp.u * tauBudget * |v i| +
    fp.u * |β| * sigmaBudget * |v i| +
    |β| * |v i| * D
  zError + fp.u * (|b i| + zBudget)

/-- Exact compact formula for multiplying a Householder matrix by a vector. -/
theorem matMulVec_householder_eq_compact (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) (b : Fin n → ℝ) :
    matMulVec n (householder n v β) b =
      fun i => b i - β * v i * householderDot n v b := by
  ext i
  have hmat :
      householder n v β =
        fun a j : Fin n => idMatrix n a j + (-β * v a * v j) := by
    ext a j
    simp [householder]
    ring
  rw [hmat]
  have hadd := congrFun
    (matMulVec_add_left n (idMatrix n) (fun a j : Fin n => -β * v a * v j) b) i
  rw [hadd]
  have hid := congrFun (matMulVec_id n b) i
  rw [hid]
  unfold matMulVec householderDot
  have hrank :
      (∑ j : Fin n, (-β * v i * v j) * b j) =
        -β * v i * ∑ j : Fin n, v j * b j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hrank]
  ring

/-- Exact row formula for the signed, column-pivoted Householder update.

For a non-pivot active row, the abstract matrix-vector expression
`P * A(:,j)` is exactly the Cox--Higham scalar update
`A(row,j) - phi * A(row,k)`, with `phi = beta * v^T A(:,j)`.
This is the algebraic bridge between the source row-growth theorem and the
stored-panel exact same-reflector hypothesis. -/
theorem matMulVec_householder_signed_pivot_update_entry_eq
    {m n : ℕ} (p row : Fin m) (k j : Fin n) (A : Fin m → Fin n → ℝ)
    (hrow : p.val < row.val) :
    matMulVec m
        (householder m
          (householderTrailingActiveVector m p (fun r => A r k)
            (signedHouseholderAlpha
              (Real.sqrt (householderTrailingColumnNorm2Sq (m := m) (n := n) p A k))
              (A p k)))
          (householderBetaSpec m
            (householderTrailingActiveVector m p (fun r => A r k)
              (signedHouseholderAlpha
                (Real.sqrt (householderTrailingColumnNorm2Sq (m := m) (n := n) p A k))
                (A p k)))))
        (fun a => A a j) row =
      A row j -
        (householderBetaSpec m
            (householderTrailingActiveVector m p (fun r => A r k)
              (signedHouseholderAlpha
                (Real.sqrt (householderTrailingColumnNorm2Sq (m := m) (n := n) p A k))
                (A p k))) *
          (∑ i : Fin m,
            householderTrailingActiveVector m p (fun r => A r k)
                (signedHouseholderAlpha
                  (Real.sqrt (householderTrailingColumnNorm2Sq (m := m) (n := n) p A k))
                  (A p k)) i *
              householderTrailingPart m p (fun r => A r j) i)) *
          A row k := by
  let alpha : ℝ :=
    signedHouseholderAlpha
      (Real.sqrt (householderTrailingColumnNorm2Sq (m := m) (n := n) p A k))
      (A p k)
  let v : Fin m → ℝ :=
    householderTrailingActiveVector m p (fun r => A r k) alpha
  let β : ℝ := householderBetaSpec m v
  have hrow_not_prefix : ¬ row.val < p.val :=
    not_lt.mpr (Nat.le_of_lt hrow)
  have hrow_ne : row ≠ p := by
    intro h
    subst row
    exact (Nat.lt_irrefl p.val) hrow
  have hvrow : v row = A row k := by
    simp [v, alpha, householderTrailingActiveVector, householderActiveVector,
      householderTrailingPart, hrow_not_prefix, hrow_ne]
  have hdot :
      householderDot m v (fun a => A a j) =
        ∑ i : Fin m, v i * householderTrailingPart m p (fun r => A r j) i := by
    unfold householderDot
    refine Finset.sum_congr rfl ?_
    intro i _
    by_cases hi : i.val < p.val
    · have hne : i ≠ p := by
        intro h
        subst i
        exact (Nat.lt_irrefl p.val) hi
      have hvi : v i = 0 := by
        simp [v, alpha, householderTrailingActiveVector, householderActiveVector,
          householderTrailingPart, hi, hne]
      simp [hvi, householderTrailingPart, hi]
    · simp [householderTrailingPart, hi]
  have hcompact :=
    congrFun (matMulVec_householder_eq_compact m v β (fun a => A a j)) row
  change
    matMulVec m (householder m v β) (fun a => A a j) row =
      A row j - (β * (∑ i : Fin m,
        v i * householderTrailingPart m p (fun r => A r j) i)) * A row k
  rw [hcompact, hdot, hvrow]
  ring

/-- One-step exact Cox--Higham same-reflector row-growth bound.

This restates the signed column-pivoted scalar row-growth theorem as a bound on
the exact Householder matrix-vector update. It is the one-step exact field
needed by the direct stored-panel floating-point recurrence for non-pivot active
rows. -/
theorem coxHigham_exact_same_reflector_row_growth_of_signed_pivot_row_bound
    {m n : ℕ} (p row : Fin m) (k j : Fin n) (A : Fin m → Fin n → ℝ)
    (B : ℝ)
    (hrow : p.val < row.val)
    (hpivot :
      ∀ l : Fin n, k.val ≤ l.val →
        householderTrailingColumnNorm2Sq (m := m) (n := n) p A l ≤
          householderTrailingColumnNorm2Sq (m := m) (n := n) p A k)
    (hj : k.val ≤ j.val)
    (hrowBound : ∀ l : Fin n, k.val ≤ l.val → |A row l| ≤ B) :
    |matMulVec m
        (householder m
          (householderTrailingActiveVector m p (fun r => A r k)
            (signedHouseholderAlpha
              (Real.sqrt (householderTrailingColumnNorm2Sq (m := m) (n := n) p A k))
              (A p k)))
          (householderBetaSpec m
            (householderTrailingActiveVector m p (fun r => A r k)
              (signedHouseholderAlpha
                (Real.sqrt (householderTrailingColumnNorm2Sq (m := m) (n := n) p A k))
                (A p k)))))
        (fun a => A a j) row| ≤
      (1 + Real.sqrt 2) * B := by
  rw [matMulVec_householder_signed_pivot_update_entry_eq p row k j A hrow]
  exact
      abs_householder_signed_pivot_update_entry_le_one_add_sqrt_two_mul_row_bound
      p row k j A B hpivot hj hrowBound

/-- Unified one-step exact active-row bound for the signed pivoted
Householder update.

Rows below the pivot use the Cox--Higham scalar row-growth estimate; the pivot
row uses the active-tail norm estimate.  The unified factor is the maximum of
the two local constants, keeping the theorem honest about the ambient
`sqrt m` pivot-row bound. -/
theorem coxHigham_exact_signed_pivot_active_row_entry_bound_of_stage_bounds
    {m n : ℕ} (p row : Fin m) (pivotCol j : Fin n)
    (A : Fin m → Fin n → ℝ) (B : ℝ)
    (hactive : p.val ≤ row.val)
    (hB : 0 ≤ B)
    (hnorm :
      0 < householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol)
    (hpivotMax :
      ∀ l : Fin n, pivotCol.val ≤ l.val →
        householderTrailingColumnNorm2Sq (m := m) (n := n) p A l ≤
          householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol)
    (hj : pivotCol.val ≤ j.val)
    (hrowBound : ∀ l : Fin n, pivotCol.val ≤ l.val → |A row l| ≤ B)
    (hcolBound : ∀ i : Fin m, p.val ≤ i.val → |A i j| ≤ B) :
    |matMulVec m
        (householder m
          (householderTrailingActiveVector m p (fun r => A r pivotCol)
            (signedHouseholderAlpha
              (Real.sqrt
                (householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol))
              (A p pivotCol)))
          (householderBetaSpec m
            (householderTrailingActiveVector m p (fun r => A r pivotCol)
              (signedHouseholderAlpha
                (Real.sqrt
                  (householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol))
                (A p pivotCol)))))
        (fun r => A r j) row| ≤
      max (1 + Real.sqrt 2) (Real.sqrt (m : ℝ)) * B := by
  by_cases hrow_eq : row = p
  · subst row
    have htail :
        ∀ i : Fin m,
          |householderTrailingPart m p (fun r => A r j) i| ≤ B := by
      intro i
      by_cases hi : i.val < p.val
      · simpa [householderTrailingPart, hi] using hB
      · have hpi : p.val ≤ i.val := le_of_not_gt hi
        simpa [householderTrailingPart, hi] using hcolBound i hpi
    have hnorm_bound :
        vecNorm2 (householderTrailingPart m p (fun r => A r j)) ≤
          Real.sqrt (m : ℝ) * B :=
      vecNorm2_le_sqrt_card_mul_of_abs_le
        (householderTrailingPart m p (fun r => A r j)) hB htail
    have hpiv :
        |matMulVec m
            (householder m
              (householderTrailingActiveVector m p (fun r => A r pivotCol)
                (signedHouseholderAlpha
                  (Real.sqrt
                    (householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol))
                  (A p pivotCol)))
              (householderBetaSpec m
                (householderTrailingActiveVector m p (fun r => A r pivotCol)
                  (signedHouseholderAlpha
                    (Real.sqrt
                      (householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol))
                    (A p pivotCol)))))
            (fun r => A r j) p| ≤
          Real.sqrt (m : ℝ) * B :=
      (coxHigham_signed_pivot_row_update_abs_le_trailing_vecNorm2
        p pivotCol j A hnorm).trans hnorm_bound
    have hscale :
        Real.sqrt (m : ℝ) * B ≤
          max (1 + Real.sqrt 2) (Real.sqrt (m : ℝ)) * B :=
      mul_le_mul_of_nonneg_right
        (le_max_right (1 + Real.sqrt 2) (Real.sqrt (m : ℝ))) hB
    exact hpiv.trans hscale
  · have hlt : p.val < row.val := by
      exact lt_of_le_of_ne hactive
        (fun hval => hrow_eq (Fin.ext hval).symm)
    have hnon :
        |matMulVec m
            (householder m
              (householderTrailingActiveVector m p (fun r => A r pivotCol)
                (signedHouseholderAlpha
                  (Real.sqrt
                    (householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol))
                  (A p pivotCol)))
              (householderBetaSpec m
                (householderTrailingActiveVector m p (fun r => A r pivotCol)
                  (signedHouseholderAlpha
                    (Real.sqrt
                      (householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol))
                    (A p pivotCol)))))
            (fun r => A r j) row| ≤
          (1 + Real.sqrt 2) * B :=
      coxHigham_exact_same_reflector_row_growth_of_signed_pivot_row_bound
        p row pivotCol j A B hlt hpivotMax hj hrowBound
    have hscale :
        (1 + Real.sqrt 2) * B ≤
          max (1 + Real.sqrt 2) (Real.sqrt (m : ℝ)) * B :=
      mul_le_mul_of_nonneg_right
        (le_max_left (1 + Real.sqrt 2) (Real.sqrt (m : ℝ))) hB
    exact hnon.trans hscale

/-- Exact signed-pivot Householder panel step used in the Cox--Higham route.

This is the exact same-reflector update for all rows and columns before any
floating-point storage convention is applied. It gives the concrete sequence
object needed to connect the one-step source estimates to a multi-stage
pivoted/sorted loop. -/
noncomputable def exactSignedPivotHouseholderPanelStep
    (m n : ℕ) (p : Fin m) (pivotCol : Fin n)
    (A : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  let v : Fin m → ℝ :=
    householderTrailingActiveVector m p (fun r => A r pivotCol)
      (signedHouseholderAlpha
        (Real.sqrt
          (householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol))
        (A p pivotCol))
  let β : ℝ := householderBetaSpec m v
  fun row j => matMulVec m (householder m v β) (fun r => A r j) row

/-- Signed-pivot Householder vector used by the Cox--Higham route. -/
noncomputable def signedPivotHouseholderVector
    (m n : ℕ) (p : Fin m) (pivotCol : Fin n)
    (A : Fin m → Fin n → ℝ) : Fin m → ℝ :=
  householderTrailingActiveVector m p (fun r => A r pivotCol)
    (signedHouseholderAlpha
      (Real.sqrt
        (householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol))
      (A p pivotCol))

/-- Signed-pivot Householder beta used by the Cox--Higham route. -/
noncomputable def signedPivotHouseholderBeta
    (m n : ℕ) (p : Fin m) (pivotCol : Fin n)
    (A : Fin m → Fin n → ℝ) : ℝ :=
  householderBetaSpec m (signedPivotHouseholderVector m n p pivotCol A)

/-- One exact signed-pivot panel step satisfies the unified active-row
Cox--Higham bound.

This is just the named panel-step form of
`coxHigham_exact_signed_pivot_active_row_entry_bound_of_stage_bounds`. -/
theorem coxHigham_exactSignedPivotPanelStep_active_entry_bound_of_stage_bounds
    {m n : ℕ} (p row : Fin m) (pivotCol j : Fin n)
    (A : Fin m → Fin n → ℝ) (B : ℝ)
    (hactive : p.val ≤ row.val)
    (hB : 0 ≤ B)
    (hnorm :
      0 < householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol)
    (hpivotMax :
      ∀ l : Fin n, pivotCol.val ≤ l.val →
        householderTrailingColumnNorm2Sq (m := m) (n := n) p A l ≤
          householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol)
    (hj : pivotCol.val ≤ j.val)
    (hrowBound : ∀ l : Fin n, pivotCol.val ≤ l.val → |A row l| ≤ B)
    (hcolBound : ∀ i : Fin m, p.val ≤ i.val → |A i j| ≤ B) :
    |exactSignedPivotHouseholderPanelStep m n p pivotCol A row j| ≤
      coxHighamActiveRowGrowthFactor m * B := by
  simpa [exactSignedPivotHouseholderPanelStep, coxHighamActiveRowGrowthFactor]
    using
      coxHigham_exact_signed_pivot_active_row_entry_bound_of_stage_bounds
        p row pivotCol j A B hactive hB hnorm hpivotMax hj hrowBound hcolBound

/-- One active-block stage budget supplies the Cox--Higham signed-pivot
stage fields.

The exact one-step theorem asks separately for an active-row budget
`|A row l| <= B` over active columns and an active-column budget
`|A i j| <= B` over active rows.  A concrete sorting/pivoting loop usually
maintains a single active-block invariant.  This adapter records the exact
one-step consequence of such an invariant, leaving only the pivot-max and
positive active-norm fields visible. -/
theorem coxHigham_exactSignedPivotPanelStep_active_block_bound_of_stage_bound
    {m n : ℕ} (p row : Fin m) (pivotCol j : Fin n)
    (A : Fin m → Fin n → ℝ) (B : ℝ)
    (hactive : p.val ≤ row.val)
    (hB : 0 ≤ B)
    (hnorm :
      0 < householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol)
    (hpivotMax :
      ∀ l : Fin n, pivotCol.val ≤ l.val →
        householderTrailingColumnNorm2Sq (m := m) (n := n) p A l ≤
          householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol)
    (hj : pivotCol.val ≤ j.val)
    (hblock :
      ∀ i : Fin m, p.val ≤ i.val →
        ∀ l : Fin n, pivotCol.val ≤ l.val → |A i l| ≤ B) :
    |exactSignedPivotHouseholderPanelStep m n p pivotCol A row j| ≤
      coxHighamActiveRowGrowthFactor m * B := by
  exact
    coxHigham_exactSignedPivotPanelStep_active_entry_bound_of_stage_bounds
      p row pivotCol j A B hactive hB hnorm hpivotMax hj
      (fun l hl => hblock row hactive l hl)
      (fun i hi => hblock i hi j hj)

/-- Multi-stage exact signed-pivot panel bound under visible Cox--Higham stage
budgets.

The loop object is concrete: every stage is the exact signed-pivot Householder
panel step above. The remaining source-specific sorting/pivoting information
is exposed as stage-budget fields: active-row bounds, active-column bounds,
positive active pivot norms, and column-pivot maximality. -/
theorem coxHigham_exactSignedPivotPanel_sequence_active_entry_bound_of_stage_budgets
    {m n : ℕ} (steps : ℕ)
    (Astage : ℕ → Fin m → Fin n → ℝ)
    (p : ℕ → Fin m) (pivotCol : ℕ → Fin n)
    (B : ℕ → ℝ) (row : Fin m) (j : Fin n)
    (hinit : |Astage 0 row j| ≤ B 0)
    (hB : ∀ t : ℕ, t ≤ steps → 0 ≤ B t)
    (hbudget : ∀ t : ℕ, t < steps →
      coxHighamActiveRowGrowthFactor m * B t ≤ B (t + 1))
    (hstep : ∀ t : ℕ, t < steps →
      Astage (t + 1) =
        exactSignedPivotHouseholderPanelStep m n (p t) (pivotCol t) (Astage t))
    (hactive : ∀ t : ℕ, t < steps → (p t).val ≤ row.val)
    (hnorm : ∀ t : ℕ, t < steps →
      0 <
        householderTrailingColumnNorm2Sq
          (m := m) (n := n) (p t) (Astage t) (pivotCol t))
    (hpivotMax : ∀ t : ℕ, t < steps →
      ∀ l : Fin n, (pivotCol t).val ≤ l.val →
        householderTrailingColumnNorm2Sq
            (m := m) (n := n) (p t) (Astage t) l ≤
          householderTrailingColumnNorm2Sq
            (m := m) (n := n) (p t) (Astage t) (pivotCol t))
    (hj : ∀ t : ℕ, t < steps → (pivotCol t).val ≤ j.val)
    (hrowBound : ∀ t : ℕ, t < steps →
      ∀ l : Fin n, (pivotCol t).val ≤ l.val → |Astage t row l| ≤ B t)
    (hcolBound : ∀ t : ℕ, t < steps →
      ∀ i : Fin m, (p t).val ≤ i.val → |Astage t i j| ≤ B t) :
    |Astage steps row j| ≤ B steps := by
  cases steps with
  | zero =>
      simpa using hinit
  | succ steps =>
      have ht : steps < steps + 1 := Nat.lt_succ_self steps
      have hpoint :
          Astage (steps + 1) row j =
            exactSignedPivotHouseholderPanelStep m n
              (p steps) (pivotCol steps) (Astage steps) row j := by
        simpa using congrFun (congrFun (hstep steps ht) row) j
      rw [hpoint]
      have hlast :
          |exactSignedPivotHouseholderPanelStep m n
              (p steps) (pivotCol steps) (Astage steps) row j| ≤
            coxHighamActiveRowGrowthFactor m * B steps :=
        coxHigham_exactSignedPivotPanelStep_active_entry_bound_of_stage_bounds
          (p steps) row (pivotCol steps) j (Astage steps) (B steps)
          (hactive steps ht) (hB steps (Nat.le_succ steps))
          (hnorm steps ht) (hpivotMax steps ht) (hj steps ht)
          (hrowBound steps ht) (hcolBound steps ht)
      exact hlast.trans (hbudget steps ht)

/-- Multi-stage exact signed-pivot panel bound from one visible active-block
budget per stage.

This is the source-shaped companion to
`coxHigham_exactSignedPivotPanel_sequence_active_entry_bound_of_stage_budgets`:
instead of carrying separate row and column bounds, it assumes a single bound
over the active rows and remaining columns at each stage. It still leaves the
positive active norm, pivot-maximality, and active-block budget propagation
fields visible. -/
theorem coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_stage_budgets
    {m n : ℕ} (steps : ℕ)
    (Astage : ℕ → Fin m → Fin n → ℝ)
    (p : ℕ → Fin m) (pivotCol : ℕ → Fin n)
    (B : ℕ → ℝ) (row : Fin m) (j : Fin n)
    (hinit : |Astage 0 row j| ≤ B 0)
    (hB : ∀ t : ℕ, t ≤ steps → 0 ≤ B t)
    (hbudget : ∀ t : ℕ, t < steps →
      coxHighamActiveRowGrowthFactor m * B t ≤ B (t + 1))
    (hstep : ∀ t : ℕ, t < steps →
      Astage (t + 1) =
        exactSignedPivotHouseholderPanelStep m n (p t) (pivotCol t) (Astage t))
    (hactive : ∀ t : ℕ, t < steps → (p t).val ≤ row.val)
    (hnorm : ∀ t : ℕ, t < steps →
      0 <
        householderTrailingColumnNorm2Sq
          (m := m) (n := n) (p t) (Astage t) (pivotCol t))
    (hpivotMax : ∀ t : ℕ, t < steps →
      ∀ l : Fin n, (pivotCol t).val ≤ l.val →
        householderTrailingColumnNorm2Sq
            (m := m) (n := n) (p t) (Astage t) l ≤
          householderTrailingColumnNorm2Sq
            (m := m) (n := n) (p t) (Astage t) (pivotCol t))
    (hj : ∀ t : ℕ, t < steps → (pivotCol t).val ≤ j.val)
    (hblockBound : ∀ t : ℕ, t < steps →
      ∀ i : Fin m, (p t).val ≤ i.val →
        ∀ l : Fin n, (pivotCol t).val ≤ l.val → |Astage t i l| ≤ B t) :
    |Astage steps row j| ≤ B steps := by
  exact
    coxHigham_exactSignedPivotPanel_sequence_active_entry_bound_of_stage_budgets
      steps Astage p pivotCol B row j hinit hB hbudget hstep hactive hnorm
      hpivotMax hj
      (fun t ht l hl => hblockBound t ht row (hactive t ht) l hl)
      (fun t ht i hi => hblockBound t ht i hi j (hj t ht))

/-- Geometric-budget version of the exact signed-pivot panel sequence bound.

If the source sorting/pivoting invariant supplies the stage budget `c^t B0`,
where `c = coxHighamActiveRowGrowthFactor m`, then the exact signed-pivot panel
sequence has final entry bound `c^steps B0`. -/
theorem coxHigham_exactSignedPivotPanel_sequence_active_entry_bound_of_geometric_stage_budgets
    {m n : ℕ} (steps : ℕ)
    (Astage : ℕ → Fin m → Fin n → ℝ)
    (p : ℕ → Fin m) (pivotCol : ℕ → Fin n)
    (B0 : ℝ) (row : Fin m) (j : Fin n)
    (hinit : |Astage 0 row j| ≤ B0)
    (hB0 : 0 ≤ B0)
    (hstep : ∀ t : ℕ, t < steps →
      Astage (t + 1) =
        exactSignedPivotHouseholderPanelStep m n (p t) (pivotCol t) (Astage t))
    (hactive : ∀ t : ℕ, t < steps → (p t).val ≤ row.val)
    (hnorm : ∀ t : ℕ, t < steps →
      0 <
        householderTrailingColumnNorm2Sq
          (m := m) (n := n) (p t) (Astage t) (pivotCol t))
    (hpivotMax : ∀ t : ℕ, t < steps →
      ∀ l : Fin n, (pivotCol t).val ≤ l.val →
        householderTrailingColumnNorm2Sq
            (m := m) (n := n) (p t) (Astage t) l ≤
          householderTrailingColumnNorm2Sq
            (m := m) (n := n) (p t) (Astage t) (pivotCol t))
    (hj : ∀ t : ℕ, t < steps → (pivotCol t).val ≤ j.val)
    (hrowBound : ∀ t : ℕ, t < steps →
      ∀ l : Fin n, (pivotCol t).val ≤ l.val →
        |Astage t row l| ≤ coxHighamActiveRowGrowthFactor m ^ t * B0)
    (hcolBound : ∀ t : ℕ, t < steps →
      ∀ i : Fin m, (p t).val ≤ i.val →
        |Astage t i j| ≤ coxHighamActiveRowGrowthFactor m ^ t * B0) :
    |Astage steps row j| ≤ coxHighamActiveRowGrowthFactor m ^ steps * B0 := by
  refine
    coxHigham_exactSignedPivotPanel_sequence_active_entry_bound_of_stage_budgets
      steps Astage p pivotCol
        (fun t => coxHighamActiveRowGrowthFactor m ^ t * B0)
        row j ?_ ?_ ?_ hstep hactive hnorm hpivotMax hj hrowBound hcolBound
  · simpa using hinit
  · intro t _ht
    exact
      mul_nonneg
        (pow_nonneg (coxHighamActiveRowGrowthFactor_nonneg m) t) hB0
  · intro t _ht
    have hpow :
        coxHighamActiveRowGrowthFactor m *
            (coxHighamActiveRowGrowthFactor m ^ t * B0) =
          coxHighamActiveRowGrowthFactor m ^ (t + 1) * B0 := by
      rw [pow_succ]
      ring
    exact le_of_eq hpow

/-- Geometric-budget version of the active-block exact signed-pivot sequence
bound.

This is still a visible-budget theorem: the source sorting or pivoting policy
must supply the active-block bound
`|A_t i l| <= c^t * B0` on each active trailing block. -/
theorem coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_geometric_stage_budgets
    {m n : ℕ} (steps : ℕ)
    (Astage : ℕ → Fin m → Fin n → ℝ)
    (p : ℕ → Fin m) (pivotCol : ℕ → Fin n)
    (B0 : ℝ) (row : Fin m) (j : Fin n)
    (hinit : |Astage 0 row j| ≤ B0)
    (hB0 : 0 ≤ B0)
    (hstep : ∀ t : ℕ, t < steps →
      Astage (t + 1) =
        exactSignedPivotHouseholderPanelStep m n (p t) (pivotCol t) (Astage t))
    (hactive : ∀ t : ℕ, t < steps → (p t).val ≤ row.val)
    (hnorm : ∀ t : ℕ, t < steps →
      0 <
        householderTrailingColumnNorm2Sq
          (m := m) (n := n) (p t) (Astage t) (pivotCol t))
    (hpivotMax : ∀ t : ℕ, t < steps →
      ∀ l : Fin n, (pivotCol t).val ≤ l.val →
        householderTrailingColumnNorm2Sq
            (m := m) (n := n) (p t) (Astage t) l ≤
          householderTrailingColumnNorm2Sq
            (m := m) (n := n) (p t) (Astage t) (pivotCol t))
    (hj : ∀ t : ℕ, t < steps → (pivotCol t).val ≤ j.val)
    (hblockBound : ∀ t : ℕ, t < steps →
      ∀ i : Fin m, (p t).val ≤ i.val →
        ∀ l : Fin n, (pivotCol t).val ≤ l.val →
          |Astage t i l| ≤ coxHighamActiveRowGrowthFactor m ^ t * B0) :
    |Astage steps row j| ≤ coxHighamActiveRowGrowthFactor m ^ steps * B0 := by
  exact
    coxHigham_exactSignedPivotPanel_sequence_active_entry_bound_of_geometric_stage_budgets
      steps Astage p pivotCol B0 row j hinit hB0 hstep hactive hnorm hpivotMax
      hj
      (fun t ht l hl => hblockBound t ht row (hactive t ht) l hl)
      (fun t ht i hi => hblockBound t ht i hi j (hj t ht))

/-- Active-block budget propagation for an exact signed-pivot Cox--Higham
panel sequence.

This theorem removes the circular-looking active-block stage-budget hypothesis
from the pointwise sequence wrappers.  If the initial matrix has a uniform
entrywise bound `B0`, the active row window and remaining-column window move
monotonically, and each exact signed-pivot stage satisfies the visible
positive-norm and column-pivot maximality conditions, then every active
trailing block at stage `t <= steps` satisfies the geometric Cox--Higham bound
`c_m^t B0`. -/
theorem coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound
    {m n : ℕ} (steps : ℕ)
    (Astage : ℕ → Fin m → Fin n → ℝ)
    (p : ℕ → Fin m) (pivotCol : ℕ → Fin n)
    (B0 : ℝ)
    (hinitBlock : ∀ i : Fin m, ∀ l : Fin n, |Astage 0 i l| ≤ B0)
    (hB0 : 0 ≤ B0)
    (hstep : ∀ t : ℕ, t < steps →
      Astage (t + 1) =
        exactSignedPivotHouseholderPanelStep m n (p t) (pivotCol t) (Astage t))
    (hpMono : ∀ u t : ℕ, u ≤ t → t ≤ steps → (p u).val ≤ (p t).val)
    (hkMono : ∀ u t : ℕ, u ≤ t → t ≤ steps →
      (pivotCol u).val ≤ (pivotCol t).val)
    (hnorm : ∀ t : ℕ, t < steps →
      0 <
        householderTrailingColumnNorm2Sq
          (m := m) (n := n) (p t) (Astage t) (pivotCol t))
    (hpivotMax : ∀ t : ℕ, t < steps →
      ∀ l : Fin n, (pivotCol t).val ≤ l.val →
        householderTrailingColumnNorm2Sq
            (m := m) (n := n) (p t) (Astage t) l ≤
          householderTrailingColumnNorm2Sq
            (m := m) (n := n) (p t) (Astage t) (pivotCol t)) :
    ∀ t : ℕ, t ≤ steps →
      ∀ i : Fin m, (p t).val ≤ i.val →
        ∀ l : Fin n, (pivotCol t).val ≤ l.val →
          |Astage t i l| ≤ coxHighamActiveRowGrowthFactor m ^ t * B0 := by
  intro t ht
  induction t with
  | zero =>
      intro i _hi l _hl
      simpa using hinitBlock i l
  | succ t ih =>
      intro i hi l hl
      have ht_lt : t < steps := Nat.lt_of_succ_le ht
      have ht_le : t ≤ steps := Nat.le_of_succ_le ht
      have hrow_prev : (p t).val ≤ i.val :=
        le_trans (hpMono t (t + 1) (Nat.le_succ t) ht) hi
      have hcol_prev : (pivotCol t).val ≤ l.val :=
        le_trans (hkMono t (t + 1) (Nat.le_succ t) ht) hl
      have hpoint :
          Astage (t + 1) i l =
            exactSignedPivotHouseholderPanelStep m n
              (p t) (pivotCol t) (Astage t) i l := by
        simpa using congrFun (congrFun (hstep t ht_lt) i) l
      rw [hpoint]
      have hBstage :
          0 ≤ coxHighamActiveRowGrowthFactor m ^ t * B0 :=
        mul_nonneg
          (pow_nonneg (coxHighamActiveRowGrowthFactor_nonneg m) t) hB0
      have hblockPrev :
          ∀ a : Fin m, (p t).val ≤ a.val →
            ∀ b : Fin n, (pivotCol t).val ≤ b.val →
              |Astage t a b| ≤
                coxHighamActiveRowGrowthFactor m ^ t * B0 :=
        ih ht_le
      have hstepBound :
          |exactSignedPivotHouseholderPanelStep m n
              (p t) (pivotCol t) (Astage t) i l| ≤
            coxHighamActiveRowGrowthFactor m *
              (coxHighamActiveRowGrowthFactor m ^ t * B0) :=
        coxHigham_exactSignedPivotPanelStep_active_block_bound_of_stage_bound
          (p t) i (pivotCol t) l (Astage t)
          (coxHighamActiveRowGrowthFactor m ^ t * B0)
          hrow_prev hBstage (hnorm t ht_lt) (hpivotMax t ht_lt)
          hcol_prev hblockPrev
      have hpow :
          coxHighamActiveRowGrowthFactor m *
              (coxHighamActiveRowGrowthFactor m ^ t * B0) =
            coxHighamActiveRowGrowthFactor m ^ (t + 1) * B0 := by
        rw [pow_succ]
        ring
      simpa [hpow] using hstepBound

/-- Active-block budget propagation with the positive-norm field discharged by
active nonzero mass plus column-pivot maximality.

Compared with
`coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound`,
this wrapper no longer assumes the pivot column has positive active trailing
norm directly.  Instead, at each stage it asks for a nonzero entry somewhere in
the remaining active block; the existing pivot-max condition then forces the
chosen pivot column's active norm to be positive. -/
theorem coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_active_block_nonzero
    {m n : ℕ} (steps : ℕ)
    (Astage : ℕ → Fin m → Fin n → ℝ)
    (p : ℕ → Fin m) (pivotCol : ℕ → Fin n)
    (B0 : ℝ)
    (hinitBlock : ∀ i : Fin m, ∀ l : Fin n, |Astage 0 i l| ≤ B0)
    (hB0 : 0 ≤ B0)
    (hstep : ∀ t : ℕ, t < steps →
      Astage (t + 1) =
        exactSignedPivotHouseholderPanelStep m n (p t) (pivotCol t) (Astage t))
    (hpMono : ∀ u t : ℕ, u ≤ t → t ≤ steps → (p u).val ≤ (p t).val)
    (hkMono : ∀ u t : ℕ, u ≤ t → t ≤ steps →
      (pivotCol u).val ≤ (pivotCol t).val)
    (hactiveNonzero : ∀ t : ℕ, t < steps →
      ∃ l : Fin n, (pivotCol t).val ≤ l.val ∧
        ∃ i : Fin m, (p t).val ≤ i.val ∧ Astage t i l ≠ 0)
    (hpivotMax : ∀ t : ℕ, t < steps →
      ∀ l : Fin n, (pivotCol t).val ≤ l.val →
        householderTrailingColumnNorm2Sq
            (m := m) (n := n) (p t) (Astage t) l ≤
          householderTrailingColumnNorm2Sq
            (m := m) (n := n) (p t) (Astage t) (pivotCol t)) :
    ∀ t : ℕ, t ≤ steps →
      ∀ i : Fin m, (p t).val ≤ i.val →
        ∀ l : Fin n, (pivotCol t).val ≤ l.val →
          |Astage t i l| ≤ coxHighamActiveRowGrowthFactor m ^ t * B0 := by
  refine
    coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound
      steps Astage p pivotCol B0 hinitBlock hB0 hstep hpMono hkMono ?_ hpivotMax
  intro t ht
  exact
    householderTrailingColumnNorm2Sq_pos_of_pivot_max_exists_active_entry_ne
      (p t) (pivotCol t) (pivotCol t) (Astage t) (hpivotMax t ht)
      (hactiveNonzero t ht)

/-- Active-block budget propagation with the pivot-max field supplied by the
finite active-column max selector.

This is the source-shaped exact loop theorem for the column-pivoting part of
the Cox--Higham route in the current formalization: the raw pivot-max
inequality is replaced by the algorithmic policy that the current pivot column
is the finite maximizer of the active trailing column norm among remaining
columns. -/
theorem coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_active_max_pivot
    {m n : ℕ} (steps : ℕ)
    (Astage : ℕ → Fin m → Fin n → ℝ)
    (p : ℕ → Fin m) (pivotCol : ℕ → Fin n)
    (B0 : ℝ)
    (hinitBlock : ∀ i : Fin m, ∀ l : Fin n, |Astage 0 i l| ≤ B0)
    (hB0 : 0 ≤ B0)
    (hstep : ∀ t : ℕ, t < steps →
      Astage (t + 1) =
        exactSignedPivotHouseholderPanelStep m n (p t) (pivotCol t) (Astage t))
    (hpMono : ∀ u t : ℕ, u ≤ t → t ≤ steps → (p u).val ≤ (p t).val)
    (hkMono : ∀ u t : ℕ, u ≤ t → t ≤ steps →
      (pivotCol u).val ≤ (pivotCol t).val)
    (hactiveNonzero : ∀ t : ℕ, t < steps →
      ∃ l : Fin n, (pivotCol t).val ≤ l.val ∧
        ∃ i : Fin m, (p t).val ≤ i.val ∧ Astage t i l ≠ 0)
    (hpivotChoice : ∀ t : ℕ, t < steps →
      pivotCol t =
        householderActiveMaxPivotColumn (p t) (pivotCol t) (Astage t)) :
    ∀ t : ℕ, t ≤ steps →
      ∀ i : Fin m, (p t).val ≤ i.val →
        ∀ l : Fin n, (pivotCol t).val ≤ l.val →
          |Astage t i l| ≤ coxHighamActiveRowGrowthFactor m ^ t * B0 := by
  refine
    coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_active_block_nonzero
      steps Astage p pivotCol B0 hinitBlock hB0 hstep hpMono hkMono
      hactiveNonzero ?_
  intro t ht l hl
  have hmax :=
    householderActiveMaxPivotColumn_pivot_max
      (p t) (pivotCol t) (Astage t) l hl
  have hnormEq :
      householderTrailingColumnNorm2Sq
          (m := m) (n := n) (p t) (Astage t)
          (householderActiveMaxPivotColumn (p t) (pivotCol t) (Astage t)) =
        householderTrailingColumnNorm2Sq
          (m := m) (n := n) (p t) (Astage t) (pivotCol t) := by
    rw [← hpivotChoice t ht]
  exact hmax.trans_eq hnormEq

/-- Active-block budget propagation with nonbreakdown stated as positive
active-block mass and pivoting stated by the finite active max-pivot policy.

This replaces the existential nonzero-active-block field by the scalar
condition that the active trailing block has positive squared mass at each
stage.  It is still a source-shaped exact-sequence dependency: a concrete
pivoted/sorted loop must supply the positive-mass and pivot-policy fields. -/
theorem coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_active_block_norm_pos
    {m n : ℕ} (steps : ℕ)
    (Astage : ℕ → Fin m → Fin n → ℝ)
    (p : ℕ → Fin m) (pivotCol : ℕ → Fin n)
    (B0 : ℝ)
    (hinitBlock : ∀ i : Fin m, ∀ l : Fin n, |Astage 0 i l| ≤ B0)
    (hB0 : 0 ≤ B0)
    (hstep : ∀ t : ℕ, t < steps →
      Astage (t + 1) =
        exactSignedPivotHouseholderPanelStep m n (p t) (pivotCol t) (Astage t))
    (hpMono : ∀ u t : ℕ, u ≤ t → t ≤ steps → (p u).val ≤ (p t).val)
    (hkMono : ∀ u t : ℕ, u ≤ t → t ≤ steps →
      (pivotCol u).val ≤ (pivotCol t).val)
    (hactiveBlockPos : ∀ t : ℕ, t < steps →
      0 < householderActiveBlockNorm2Sq (p t) (pivotCol t) (Astage t))
    (hpivotChoice : ∀ t : ℕ, t < steps →
      pivotCol t =
        householderActiveMaxPivotColumn (p t) (pivotCol t) (Astage t)) :
    ∀ t : ℕ, t ≤ steps →
      ∀ i : Fin m, (p t).val ≤ i.val →
        ∀ l : Fin n, (pivotCol t).val ≤ l.val →
          |Astage t i l| ≤ coxHighamActiveRowGrowthFactor m ^ t * B0 := by
  refine
    coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_active_max_pivot
      steps Astage p pivotCol B0 hinitBlock hB0 hstep hpMono hkMono ?_
      hpivotChoice
  intro t ht
  exact
    exists_active_entry_ne_of_householderActiveBlockNorm2Sq_pos
      (p t) (pivotCol t) (Astage t) (hactiveBlockPos t ht)

/-- Active-block budget propagation for a stagewise sorted active-max column
policy.

At each stage, the displayed matrix `Astage t` is assumed to be obtained from a
raw stage matrix by swapping the finite active max-pivot column into the
displayed active column `pivotCol t`.  The swap theorem supplies the raw
pivot-max field consumed by the exact signed-pivot sequence, while positive
active-block mass supplies the nonbreakdown witness.

This is still a source-shaped exact-sequence dependency: it proves the
one-step sorting-policy field for the displayed stages, but it does not yet
derive positive active-block mass from rank/nonbreakdown, nor does it connect
the exact sequence to the rounded stored-panel solver theorem. -/
theorem coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_swapped_active_max_pivot
    {m n : ℕ} (steps : ℕ)
    (Araw Astage : ℕ → Fin m → Fin n → ℝ)
    (p : ℕ → Fin m) (pivotCol : ℕ → Fin n)
    (B0 : ℝ)
    (hinitBlock : ∀ i : Fin m, ∀ l : Fin n, |Astage 0 i l| ≤ B0)
    (hB0 : 0 ≤ B0)
    (hstep : ∀ t : ℕ, t < steps →
      Astage (t + 1) =
        exactSignedPivotHouseholderPanelStep m n (p t) (pivotCol t) (Astage t))
    (hpMono : ∀ u t : ℕ, u ≤ t → t ≤ steps → (p u).val ≤ (p t).val)
    (hkMono : ∀ u t : ℕ, u ≤ t → t ≤ steps →
      (pivotCol u).val ≤ (pivotCol t).val)
    (hsorted : ∀ t : ℕ, t < steps →
      Astage t =
        householderSwapColumns (Araw t) (pivotCol t)
          (householderActiveMaxPivotColumn (p t) (pivotCol t) (Araw t)))
    (hactiveBlockPos : ∀ t : ℕ, t < steps →
      0 < householderActiveBlockNorm2Sq (p t) (pivotCol t) (Astage t)) :
    ∀ t : ℕ, t ≤ steps →
      ∀ i : Fin m, (p t).val ≤ i.val →
        ∀ l : Fin n, (pivotCol t).val ≤ l.val →
          |Astage t i l| ≤ coxHighamActiveRowGrowthFactor m ^ t * B0 := by
  refine
    coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_active_block_nonzero
      steps Astage p pivotCol B0 hinitBlock hB0 hstep hpMono hkMono ?_ ?_
  · intro t ht
    exact
      exists_active_entry_ne_of_householderActiveBlockNorm2Sq_pos
        (p t) (pivotCol t) (Astage t) (hactiveBlockPos t ht)
  · intro t ht l hl
    rw [hsorted t ht]
    exact
      householderSwapColumns_activeMaxPivotColumn_pivot_max
        (p t) (pivotCol t) (Araw t) l hl

/-- Swapped active max-pivot sequence with raw-stage active-block
nonbreakdown.

This wrapper removes the need to state positive active-block mass after the
column swap.  If the raw stage has positive active-block mass and the displayed
stage is obtained by swapping the finite active max column into the active
position, then the displayed stage also has positive active-block mass.  The
remaining source obligation is therefore raw-stage nonbreakdown, not a separate
post-swap artifact. -/
theorem coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_swapped_active_max_pivot_of_raw_active_block_norm_pos
    {m n : ℕ} (steps : ℕ)
    (Araw Astage : ℕ → Fin m → Fin n → ℝ)
    (p : ℕ → Fin m) (pivotCol : ℕ → Fin n)
    (B0 : ℝ)
    (hinitBlock : ∀ i : Fin m, ∀ l : Fin n, |Astage 0 i l| ≤ B0)
    (hB0 : 0 ≤ B0)
    (hstep : ∀ t : ℕ, t < steps →
      Astage (t + 1) =
        exactSignedPivotHouseholderPanelStep m n (p t) (pivotCol t) (Astage t))
    (hpMono : ∀ u t : ℕ, u ≤ t → t ≤ steps → (p u).val ≤ (p t).val)
    (hkMono : ∀ u t : ℕ, u ≤ t → t ≤ steps →
      (pivotCol u).val ≤ (pivotCol t).val)
    (hsorted : ∀ t : ℕ, t < steps →
      Astage t =
        householderSwapColumns (Araw t) (pivotCol t)
          (householderActiveMaxPivotColumn (p t) (pivotCol t) (Araw t)))
    (hrawActiveBlockPos : ∀ t : ℕ, t < steps →
      0 < householderActiveBlockNorm2Sq (p t) (pivotCol t) (Araw t)) :
    ∀ t : ℕ, t ≤ steps →
      ∀ i : Fin m, (p t).val ≤ i.val →
        ∀ l : Fin n, (pivotCol t).val ≤ l.val →
          |Astage t i l| ≤ coxHighamActiveRowGrowthFactor m ^ t * B0 := by
  refine
    coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_swapped_active_max_pivot
      steps Araw Astage p pivotCol B0 hinitBlock hB0 hstep hpMono hkMono
      hsorted ?_
  intro t ht
  rw [hsorted t ht]
  exact
    householderActiveBlockNorm2Sq_swapColumns_pos_of_pos
      (p t) (pivotCol t)
      (householderActiveMaxPivotColumn (p t) (pivotCol t) (Araw t))
      (Araw t)
      (householderActiveMaxPivotColumn_ge (p t) (pivotCol t) (Araw t))
      (hrawActiveBlockPos t ht)

private lemma abs_one_add_le_one_add_of_abs_le {u δ : ℝ}
    (_hu : 0 ≤ u) (hδ : |δ| ≤ u) :
    |1 + δ| ≤ 1 + u := by
  calc
    |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le 1 δ
    _ ≤ 1 + u := by
      simp
      exact hδ

private lemma abs_sub_le_abs_add_abs (x y : ℝ) :
    |x - y| ≤ |x| + |y| := by
  calc
    |x - y| = |x + -y| := by ring_nf
    _ ≤ |x| + |-y| := abs_add_le x (-y)
    _ = |x| + |y| := by rw [abs_neg]

private lemma abs_add_three_le_householderSupport (a b c : ℝ) :
    |a + b + c| ≤ |a| + |b| + |c| := by
  calc
    |a + b + c| = |(a + b) + c| := by ring_nf
    _ ≤ |a + b| + |c| := abs_add_le (a + b) c
    _ ≤ (|a| + |b|) + |c| := add_le_add (abs_add_le a b) le_rfl
    _ = |a| + |b| + |c| := by ring

private lemma fl_mul_error_le (fp : FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * |x * y| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul x y
  rw [hfl]
  have hdiff : (x * y) * (1 + δ) - x * y = (x * y) * δ := by ring
  rw [hdiff, abs_mul]
  calc
    |x * y| * |δ| ≤ |x * y| * fp.u :=
      mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    _ = fp.u * |x * y| := by ring

private lemma fl_sub_error_le_abs_add_abs (fp : FPModel) (x y : ℝ) :
    |fp.fl_sub x y - (x - y)| ≤ fp.u * (|x| + |y|) := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_sub x y
  rw [hfl]
  have hdiff : (x - y) * (1 + δ) - (x - y) = (x - y) * δ := by ring
  rw [hdiff, abs_mul]
  have hsub := abs_sub_le_abs_add_abs x y
  calc
    |x - y| * |δ| ≤ (|x| + |y|) * fp.u :=
      mul_le_mul hsub hδ (abs_nonneg _) (by positivity)
    _ = fp.u * (|x| + |y|) := by ring

private lemma fl_mul_abs_le (fp : FPModel) (x y Bx By : ℝ)
    (hx : |x| ≤ Bx) (hy : |y| ≤ By)
    (hBx : 0 ≤ Bx) (hBy : 0 ≤ By) :
    |fp.fl_mul x y| ≤ Bx * By * (1 + fp.u) := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul x y
  rw [hfl, abs_mul]
  have hxy : |x * y| ≤ Bx * By := by
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) hBx
  have hδ1 : |1 + δ| ≤ 1 + fp.u :=
    abs_one_add_le_one_add_of_abs_le fp.u_nonneg hδ
  exact mul_le_mul hxy hδ1 (abs_nonneg _) (mul_nonneg hBx hBy)

private lemma householderAbsDotBudget_nonneg (n : ℕ)
    (v b : Fin n → ℝ) :
    0 ≤ householderAbsDotBudget n v b := by
  unfold householderAbsDotBudget
  exact Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)

private lemma householderDot_abs_le_budget (n : ℕ)
    (v b : Fin n → ℝ) :
    |householderDot n v b| ≤ householderAbsDotBudget n v b := by
  unfold householderDot householderAbsDotBudget
  calc
    |∑ j : Fin n, v j * b j| ≤ ∑ j : Fin n, |v j * b j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n, |v j| * |b j| := Finset.sum_abs_mul v b

private lemma fl_dotProduct_abs_le_householder_budget
    (fp : FPModel) (n : ℕ)
    (v b : Fin n → ℝ) (hn : gammaValid fp n) :
    |fl_dotProduct fp n v b| ≤
      householderAbsDotBudget n v b +
        gamma fp n * householderAbsDotBudget n v b := by
  let sigma := householderDot n v b
  let S := householderAbsDotBudget n v b
  have hdot :
      |fl_dotProduct fp n v b - sigma| ≤ gamma fp n * S := by
    simpa [sigma, S, householderDot, householderAbsDotBudget]
      using dotProduct_error_bound fp n v b hn
  have hsigma : |sigma| ≤ S := by
    simpa [sigma, S] using householderDot_abs_le_budget n v b
  have hdecomp :
      fl_dotProduct fp n v b =
        (fl_dotProduct fp n v b - sigma) + sigma := by ring
  rw [hdecomp]
  calc
    |(fl_dotProduct fp n v b - sigma) + sigma|
        ≤ |fl_dotProduct fp n v b - sigma| + |sigma| := abs_add_le _ _
    _ ≤ gamma fp n * S + S := add_le_add hdot hsigma
    _ = S + gamma fp n * S := by ring

private lemma fl_householderApplyCompact_tau_abs_le
    (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) (b : Fin n → ℝ)
    (hn : gammaValid fp n) :
    |fp.fl_mul β (fl_dotProduct fp n v b)| ≤
      |β| *
        (householderAbsDotBudget n v b +
          gamma fp n * householderAbsDotBudget n v b) *
        (1 + fp.u) := by
  let sigmaBudget :=
    householderAbsDotBudget n v b +
      gamma fp n * householderAbsDotBudget n v b
  have hsigma :
      |fl_dotProduct fp n v b| ≤ sigmaBudget := by
    simpa [sigmaBudget] using
      fl_dotProduct_abs_le_householder_budget fp n v b hn
  have hS : 0 ≤ householderAbsDotBudget n v b :=
    householderAbsDotBudget_nonneg n v b
  have hgammaS :
      0 ≤ gamma fp n * householderAbsDotBudget n v b :=
    mul_nonneg (gamma_nonneg fp hn) hS
  have hsigma_nonneg : 0 ≤ sigmaBudget := by
    dsimp [sigmaBudget]
    exact add_nonneg hS hgammaS
  simpa [sigmaBudget] using
    fl_mul_abs_le fp β (fl_dotProduct fp n v b) |β| sigmaBudget
      (le_rfl) hsigma (abs_nonneg β) hsigma_nonneg

private lemma fl_householderApplyCompact_z_abs_le
    (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) (b : Fin n → ℝ)
    (hn : gammaValid fp n) (i : Fin n) :
    |fp.fl_mul (fp.fl_mul β (fl_dotProduct fp n v b)) (v i)| ≤
      (|β| *
        (householderAbsDotBudget n v b +
          gamma fp n * householderAbsDotBudget n v b) *
        (1 + fp.u)) * |v i| * (1 + fp.u) := by
  let tauBudget :=
    |β| *
      (householderAbsDotBudget n v b +
        gamma fp n * householderAbsDotBudget n v b) *
      (1 + fp.u)
  have htau :
      |fp.fl_mul β (fl_dotProduct fp n v b)| ≤ tauBudget := by
    simpa [tauBudget] using
      fl_householderApplyCompact_tau_abs_le fp n v β b hn
  have hsigmaBudget_nonneg :
      0 ≤ householderAbsDotBudget n v b +
        gamma fp n * householderAbsDotBudget n v b := by
    exact add_nonneg (householderAbsDotBudget_nonneg n v b)
      (mul_nonneg (gamma_nonneg fp hn) (householderAbsDotBudget_nonneg n v b))
  have htau_nonneg : 0 ≤ tauBudget := by
    dsimp [tauBudget]
    have h1u : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
    exact mul_nonneg (mul_nonneg (abs_nonneg β) hsigmaBudget_nonneg) h1u
  simpa [tauBudget] using
    fl_mul_abs_le fp (fp.fl_mul β (fl_dotProduct fp n v b)) (v i)
      tauBudget |v i| htau le_rfl htau_nonneg (abs_nonneg (v i))

private lemma fl_householderApplyCompact_z_error_bound
    (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) (b : Fin n → ℝ)
    (hn : gammaValid fp n) (i : Fin n) :
    |fp.fl_mul (fp.fl_mul β (fl_dotProduct fp n v b)) (v i) -
        β * v i * householderDot n v b| ≤
      fp.u *
          (|β| *
            (householderAbsDotBudget n v b +
              gamma fp n * householderAbsDotBudget n v b) *
            (1 + fp.u)) *
          |v i| +
        fp.u * |β| *
          (householderAbsDotBudget n v b +
            gamma fp n * householderAbsDotBudget n v b) *
          |v i| +
        |β| * |v i| *
          (gamma fp n * householderAbsDotBudget n v b) := by
  let sigmaHat := fl_dotProduct fp n v b
  let sigma := householderDot n v b
  let S := householderAbsDotBudget n v b
  let D := gamma fp n * S
  let sigmaBudget := S + D
  let tauHat := fp.fl_mul β sigmaHat
  let tauBudget := |β| * sigmaBudget * (1 + fp.u)
  let zHat := fp.fl_mul tauHat (v i)
  have hdot : |sigmaHat - sigma| ≤ D := by
    simpa [sigmaHat, sigma, S, D, householderDot, householderAbsDotBudget]
      using dotProduct_error_bound fp n v b hn
  have hS_nonneg : 0 ≤ S := by
    simpa [S] using householderAbsDotBudget_nonneg n v b
  have hD_nonneg : 0 ≤ D := by
    exact mul_nonneg (gamma_nonneg fp hn) hS_nonneg
  have hsigmaBudget_nonneg : 0 ≤ sigmaBudget := by
    dsimp [sigmaBudget]
    exact add_nonneg hS_nonneg hD_nonneg
  have hsigmaHat :
      |sigmaHat| ≤ sigmaBudget := by
    simpa [sigmaHat, S, D, sigmaBudget]
      using fl_dotProduct_abs_le_householder_budget fp n v b hn
  have htau :
      |tauHat| ≤ tauBudget := by
    simpa [sigmaHat, S, D, sigmaBudget, tauHat, tauBudget]
      using fl_householderApplyCompact_tau_abs_le fp n v β b hn
  have htauBudget_nonneg : 0 ≤ tauBudget := by
    dsimp [tauBudget]
    have h1u : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
    exact mul_nonneg (mul_nonneg (abs_nonneg β) hsigmaBudget_nonneg) h1u
  have hzRoundRaw :
      |zHat - tauHat * v i| ≤ fp.u * |tauHat * v i| := by
    simpa [zHat, tauHat] using fl_mul_error_le fp tauHat (v i)
  have htauv_abs : |tauHat * v i| ≤ tauBudget * |v i| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right htau (abs_nonneg (v i))
  have hzRound :
      |zHat - tauHat * v i| ≤ fp.u * tauBudget * |v i| := by
    calc
      |zHat - tauHat * v i| ≤ fp.u * |tauHat * v i| := hzRoundRaw
      _ ≤ fp.u * (tauBudget * |v i|) :=
        mul_le_mul_of_nonneg_left htauv_abs fp.u_nonneg
      _ = fp.u * tauBudget * |v i| := by ring
  have htauRoundRaw :
      |tauHat - β * sigmaHat| ≤ fp.u * |β * sigmaHat| := by
    simpa [tauHat, sigmaHat] using fl_mul_error_le fp β sigmaHat
  have hβsigma_abs : |β * sigmaHat| ≤ |β| * sigmaBudget := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hsigmaHat (abs_nonneg β)
  have htauRound :
      |(tauHat - β * sigmaHat) * v i| ≤
        fp.u * |β| * sigmaBudget * |v i| := by
    calc
      |(tauHat - β * sigmaHat) * v i|
          = |tauHat - β * sigmaHat| * |v i| := abs_mul _ _
      _ ≤ (fp.u * |β * sigmaHat|) * |v i| :=
        mul_le_mul_of_nonneg_right htauRoundRaw (abs_nonneg (v i))
      _ ≤ (fp.u * (|β| * sigmaBudget)) * |v i| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hβsigma_abs fp.u_nonneg)
          (abs_nonneg (v i))
      _ = fp.u * |β| * sigmaBudget * |v i| := by ring
  have hdotScaled :
      |β * (sigmaHat - sigma) * v i| ≤ |β| * |v i| * D := by
    calc
      |β * (sigmaHat - sigma) * v i|
          = |β| * |sigmaHat - sigma| * |v i| := by simp [abs_mul]
      _ ≤ |β| * D * |v i| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdot (abs_nonneg β))
          (abs_nonneg (v i))
      _ = |β| * |v i| * D := by ring
  have hdecomp :
      zHat - β * v i * sigma =
        (zHat - tauHat * v i) +
          (tauHat - β * sigmaHat) * v i +
          β * (sigmaHat - sigma) * v i := by ring
  rw [hdecomp]
  calc
    |(zHat - tauHat * v i) + (tauHat - β * sigmaHat) * v i +
        β * (sigmaHat - sigma) * v i|
        ≤ |zHat - tauHat * v i| +
          |(tauHat - β * sigmaHat) * v i| +
          |β * (sigmaHat - sigma) * v i| :=
      abs_add_three_le_householderSupport _ _ _
    _ ≤ fp.u * tauBudget * |v i| +
          fp.u * |β| * sigmaBudget * |v i| +
          |β| * |v i| * D := by
      exact add_le_add (add_le_add hzRound htauRound) hdotScaled

/-- Componentwise deterministic forward-error bound for compact Householder
    application `fl(b - β v (vᵀb))`.

    This theorem is the compact dot-scale-subtract counterpart of the
    explicit-matrix route above.  It is conservative but fully explicit: the
    right-hand side is built from the dot-product γ-bound and the three rounded
    scalar operations used after the dot product. -/
theorem fl_householderApplyCompact_componentwise_error_bound
    (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) (b : Fin n → ℝ)
    (hn : gammaValid fp n) :
    ∀ i : Fin n,
      |fl_householderApplyCompact fp n v β b i -
          matMulVec n (householder n v β) b i| ≤
        householderCompactComponentBudget fp n v β b i := by
  intro i
  let sigma := householderDot n v b
  let sigmaHat := fl_dotProduct fp n v b
  let S := householderAbsDotBudget n v b
  let D := gamma fp n * S
  let sigmaBudget := S + D
  let tauHat := fp.fl_mul β sigmaHat
  let tauBudget := |β| * sigmaBudget * (1 + fp.u)
  let zHat := fp.fl_mul tauHat (v i)
  let zBudget := tauBudget * |v i| * (1 + fp.u)
  let zError :=
    fp.u * tauBudget * |v i| +
      fp.u * |β| * sigmaBudget * |v i| +
      |β| * |v i| * D
  have hz :
      |zHat - β * v i * sigma| ≤ zError := by
    simpa [sigma, sigmaHat, S, D, sigmaBudget, tauHat, tauBudget, zHat, zError]
      using fl_householderApplyCompact_z_error_bound fp n v β b hn i
  have hzAbs :
      |zHat| ≤ zBudget := by
    simpa [sigmaHat, S, D, sigmaBudget, tauHat, tauBudget, zHat, zBudget]
      using fl_householderApplyCompact_z_abs_le fp n v β b hn i
  have hsubRaw :
      |fp.fl_sub (b i) zHat - (b i - zHat)| ≤
        fp.u * (|b i| + |zHat|) :=
    fl_sub_error_le_abs_add_abs fp (b i) zHat
  have hsub :
      |fp.fl_sub (b i) zHat - (b i - zHat)| ≤
        fp.u * (|b i| + zBudget) := by
    calc
      |fp.fl_sub (b i) zHat - (b i - zHat)|
          ≤ fp.u * (|b i| + |zHat|) := hsubRaw
      _ ≤ fp.u * (|b i| + zBudget) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hzAbs) fp.u_nonneg
  have hdecomp :
      fp.fl_sub (b i) zHat - (b i - β * v i * sigma) =
        (fp.fl_sub (b i) zHat - (b i - zHat)) +
          (β * v i * sigma - zHat) := by ring
  have hz' :
      |β * v i * sigma - zHat| ≤ zError := by
    simpa [abs_sub_comm] using hz
  have hmain :
      |fp.fl_sub (b i) zHat - (b i - β * v i * sigma)| ≤
        zError + fp.u * (|b i| + zBudget) := by
    rw [hdecomp]
    calc
      |(fp.fl_sub (b i) zHat - (b i - zHat)) +
          (β * v i * sigma - zHat)|
          ≤ |fp.fl_sub (b i) zHat - (b i - zHat)| +
            |β * v i * sigma - zHat| := abs_add_le _ _
      _ ≤ fp.u * (|b i| + zBudget) + zError := add_le_add hsub hz'
      _ = zError + fp.u * (|b i| + zBudget) := by ring
  have htarget :
      matMulVec n (householder n v β) b i =
        b i - β * v i * sigma := by
    simpa [sigma] using congrFun (matMulVec_householder_eq_compact n v β b) i
  rw [htarget]
  simpa [fl_householderApplyCompact, householderCompactComponentBudget,
    sigma, sigmaHat, S, D, sigmaBudget, tauHat, tauBudget, zHat, zBudget, zError]
    using hmain

/-- The explicit compact Householder component budget is nonnegative whenever
    the dot-product gamma constant is valid. -/
theorem householderCompactComponentBudget_nonneg
    (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) (b : Fin n → ℝ)
    (hn : gammaValid fp n) (i : Fin n) :
    0 ≤ householderCompactComponentBudget fp n v β b i := by
  let S := householderAbsDotBudget n v b
  let D := gamma fp n * S
  let sigmaBudget := S + D
  let tauBudget := |β| * sigmaBudget * (1 + fp.u)
  let zBudget := tauBudget * |v i| * (1 + fp.u)
  let zError :=
    fp.u * tauBudget * |v i| +
      fp.u * |β| * sigmaBudget * |v i| +
      |β| * |v i| * D
  have hS : 0 ≤ S := by
    simpa [S] using householderAbsDotBudget_nonneg n v b
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (gamma_nonneg fp hn) hS
  have hsigma : 0 ≤ sigmaBudget := by
    dsimp [sigmaBudget]
    exact add_nonneg hS hD
  have h1u : 0 ≤ 1 + fp.u := by
    linarith [fp.u_nonneg]
  have htau : 0 ≤ tauBudget := by
    dsimp [tauBudget]
    exact mul_nonneg (mul_nonneg (abs_nonneg β) hsigma) h1u
  have hzBudget : 0 ≤ zBudget := by
    dsimp [zBudget]
    exact mul_nonneg (mul_nonneg htau (abs_nonneg (v i))) h1u
  have hzError : 0 ≤ zError := by
    dsimp [zError]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg (mul_nonneg fp.u_nonneg htau) (abs_nonneg (v i)))
        (mul_nonneg
          (mul_nonneg (mul_nonneg fp.u_nonneg (abs_nonneg β)) hsigma)
          (abs_nonneg (v i))))
      (mul_nonneg (mul_nonneg (abs_nonneg β) (abs_nonneg (v i))) hD)
  have hsub : 0 ≤ fp.u * (|b i| + zBudget) :=
    mul_nonneg fp.u_nonneg (add_nonneg (abs_nonneg _) hzBudget)
  simpa [householderCompactComponentBudget, S, D, sigmaBudget, tauBudget,
    zBudget, zError] using add_nonneg hzError hsub

/-- The absolute dot-product budget is bounded by the product of Euclidean
    norms. -/
theorem householderAbsDotBudget_le_vecNorm2_mul (n : ℕ)
    (v b : Fin n → ℝ) :
    householderAbsDotBudget n v b ≤ vecNorm2 v * vecNorm2 b := by
  unfold householderAbsDotBudget
  have hinner :=
    abs_vecInnerProduct_le_vecNorm2_mul
      (fun i : Fin n => |v i|) (fun i : Fin n => |b i|)
  have hsum_nonneg :
      0 ≤ ∑ i : Fin n, |v i| * |b i| := by
    exact Finset.sum_nonneg
      (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hsum :
      ∑ i : Fin n, |v i| * |b i| ≤
        vecNorm2 (fun i : Fin n => |v i|) *
          vecNorm2 (fun i : Fin n => |b i|) := by
    simpa [abs_of_nonneg hsum_nonneg] using hinner
  simpa [vecNorm2_abs] using hsum

/-- Reflector-dependent coefficient controlling the update part of the compact
    Householder component budget at norm scale.

    If `B = ‖b‖₂`, then the component budget is bounded by
    `updateCoeff * B * |vᵢ| + u * |bᵢ|`.  The coefficient is independent of the
    vector being updated; only the reflector and machine model appear. -/
noncomputable def householderCompactUpdateCoeff (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) : ℝ :=
  let V := vecNorm2 v
  let sigmaCoeff := (1 + gamma fp n) * V
  let tauCoeff := |β| * sigmaCoeff * (1 + fp.u)
  let zBudgetCoeff := tauCoeff * (1 + fp.u)
  let zErrorCoeff :=
    fp.u * tauCoeff + fp.u * |β| * sigmaCoeff + |β| * gamma fp n * V
  zErrorCoeff + fp.u * zBudgetCoeff

/-- Reflector-dependent normwise compact Householder budget coefficient.

    This is the coefficient `c(v,β,n,u)` such that
    `householderCompactNormBudget fp n v β b <= c(v,β,n,u) * ‖b‖₂`. -/
noncomputable def householderCompactNormBudgetCoeff (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) : ℝ :=
  fp.u + householderCompactUpdateCoeff fp n v β * vecNorm2 v

/-- The scalar multiplier in the compact Householder norm-budget coefficient.

    The full coefficient is
    `u + (|β| * ‖v‖₂^2) * householderCompactNormBudgetCoeffFactor`.
    Separating this scalar exposes the per-reflector quantity
    `|β| * ‖v‖₂^2`, which is the pivot-local estimate needed by the compact
    QR product-budget route. -/
noncomputable def householderCompactNormBudgetCoeffFactor
    (fp : FPModel) (n : ℕ) : ℝ :=
  fp.u * (1 + gamma fp n) * (1 + fp.u) +
    fp.u * (1 + gamma fp n) +
    gamma fp n +
    fp.u * (1 + gamma fp n) * (1 + fp.u) ^ 2

/-- Exact algebraic expansion of the compact Householder norm-budget
    coefficient.

    The data dependence enters only through `|β| * ‖v‖₂^2`; all remaining
    factors depend on the machine model and the dot-product dimension. -/
theorem householderCompactNormBudgetCoeff_eq_u_add_abs_beta_norm_sq_mul_factor
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) (β : ℝ) :
    householderCompactNormBudgetCoeff fp n v β =
      fp.u + (|β| * vecNorm2 v ^ 2) *
        householderCompactNormBudgetCoeffFactor fp n := by
  unfold householderCompactNormBudgetCoeff
  unfold householderCompactUpdateCoeff
  unfold householderCompactNormBudgetCoeffFactor
  ring

/-- Nonnegativity of the compact Householder norm-budget scalar factor. -/
theorem householderCompactNormBudgetCoeffFactor_nonneg
    (fp : FPModel) (n : ℕ) (hn : gammaValid fp n) :
    0 ≤ householderCompactNormBudgetCoeffFactor fp n := by
  unfold householderCompactNormBudgetCoeffFactor
  have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have h1γ : 0 ≤ 1 + gamma fp n := by linarith
  have h1u : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
  exact add_nonneg
    (add_nonneg
      (add_nonneg
        (mul_nonneg
          (mul_nonneg fp.u_nonneg h1γ) h1u)
        (mul_nonneg fp.u_nonneg h1γ))
      hγ)
    (mul_nonneg
      (mul_nonneg fp.u_nonneg h1γ)
      (sq_nonneg (1 + fp.u)))

/-- Monotone cap for the compact Householder norm-budget scalar factor.

    If the unit roundoff and dot-product gamma are bounded by displayed caps
    `Ucap` and `Gcap`, then the coefficient factor is bounded by the same
    nonnegative polynomial with those caps.  This is the local cap estimate
    consumed by the source-denominator scalar-smallness route; it does not
    prove a numerical value for `Ucap` or `Gcap`. -/
theorem householderCompactNormBudgetCoeffFactor_le_of_u_gamma_le
    (fp : FPModel) (n : ℕ) (hn : gammaValid fp n)
    (Ucap Gcap : ℝ)
    (hUcap_nonneg : 0 ≤ Ucap)
    (hGcap_nonneg : 0 ≤ Gcap)
    (hu : fp.u ≤ Ucap)
    (hγ : gamma fp n ≤ Gcap) :
    householderCompactNormBudgetCoeffFactor fp n ≤
      Ucap * (1 + Gcap) * (1 + Ucap) +
        Ucap * (1 + Gcap) +
        Gcap +
        Ucap * (1 + Gcap) * (1 + Ucap) ^ 2 := by
  let u : ℝ := fp.u
  let g : ℝ := gamma fp n
  have hu_nonneg : 0 ≤ u := by
    simpa [u] using fp.u_nonneg
  have hg_nonneg : 0 ≤ g := by
    simpa [g] using gamma_nonneg fp hn
  have hu_bound : u ≤ Ucap := by
    simpa [u] using hu
  have hg_bound : g ≤ Gcap := by
    simpa [g] using hγ
  have h1u_nonneg : 0 ≤ 1 + u := by nlinarith [hu_nonneg]
  have h1U_nonneg : 0 ≤ 1 + Ucap := by nlinarith [hUcap_nonneg]
  have h1g_nonneg : 0 ≤ 1 + g := by nlinarith [hg_nonneg]
  have h1G_nonneg : 0 ≤ 1 + Gcap := by nlinarith [hGcap_nonneg]
  have h1u_bound : 1 + u ≤ 1 + Ucap := by linarith
  have h1g_bound : 1 + g ≤ 1 + Gcap := by linarith
  have hu1g_bound : u * (1 + g) ≤ Ucap * (1 + Gcap) :=
    mul_le_mul hu_bound h1g_bound h1g_nonneg hUcap_nonneg
  have hu1g_nonneg : 0 ≤ u * (1 + g) :=
    mul_nonneg hu_nonneg h1g_nonneg
  have hU1G_nonneg : 0 ≤ Ucap * (1 + Gcap) :=
    mul_nonneg hUcap_nonneg h1G_nonneg
  have hterm1 :
      u * (1 + g) * (1 + u) ≤
        Ucap * (1 + Gcap) * (1 + Ucap) :=
    mul_le_mul hu1g_bound h1u_bound h1u_nonneg hU1G_nonneg
  have hterm2 : u * (1 + g) ≤ Ucap * (1 + Gcap) := hu1g_bound
  have hsq_bound : (1 + u) ^ 2 ≤ (1 + Ucap) ^ 2 := by
    nlinarith [h1u_bound, h1u_nonneg, h1U_nonneg]
  have hterm4 :
      u * (1 + g) * (1 + u) ^ 2 ≤
        Ucap * (1 + Gcap) * (1 + Ucap) ^ 2 :=
    mul_le_mul hu1g_bound hsq_bound (sq_nonneg _) hU1G_nonneg
  unfold householderCompactNormBudgetCoeffFactor
  change
    u * (1 + g) * (1 + u) + u * (1 + g) + g +
        u * (1 + g) * (1 + u) ^ 2 ≤
      Ucap * (1 + Gcap) * (1 + Ucap) +
      Ucap * (1 + Gcap) +
        Gcap +
        Ucap * (1 + Gcap) * (1 + Ucap) ^ 2
  linarith

/-- Concrete gamma-index cap for the compact Householder norm-budget scalar
    factor.

    Under the standard validity guard for `2*n` operations and `0 < n`, the
    explicit scalar factor in the compact dot-scale-subtract Householder
    budget is at most `15 * gamma fp n`.  The constant is deliberately
    conservative; it packages the polynomial in `u` and `gamma_n` into a single
    reusable operation-count comparison. -/
theorem householderCompactNormBudgetCoeffFactor_le_fifteen_gamma
    (fp : FPModel) (n : ℕ)
    (hn_pos : 0 < n)
    (hvalid2n : gammaValid fp (2 * n)) :
    householderCompactNormBudgetCoeffFactor fp n ≤ 15 * gamma fp n := by
  let g : ℝ := gamma fp n
  have hn : gammaValid fp n := gammaValid_mono fp (by omega) hvalid2n
  have hg_nonneg : 0 ≤ g := by
    simpa [g] using gamma_nonneg fp hn
  have hg_le_one : g ≤ 1 := by
    simpa [g] using le_of_lt (gamma_lt_one fp n hvalid2n)
  have hu_le_g : fp.u ≤ g := by
    simpa [g] using u_le_gamma fp hn_pos hn
  have hFcap :
      householderCompactNormBudgetCoeffFactor fp n ≤
        g * (1 + g) * (1 + g) +
          g * (1 + g) +
          g +
          g * (1 + g) * (1 + g) ^ 2 := by
    simpa [g] using
      householderCompactNormBudgetCoeffFactor_le_of_u_gamma_le
        fp n hn (gamma fp n) (gamma fp n)
        (by simpa [g] using hg_nonneg)
        (by simpa [g] using hg_nonneg)
        (by simpa [g] using hu_le_g) (le_rfl)
  have hpoly :
      g * (1 + g) * (1 + g) +
          g * (1 + g) +
          g +
          g * (1 + g) * (1 + g) ^ 2 ≤
        15 * g := by
    have hg2 : g ^ 2 ≤ g := by
      nlinarith [mul_nonneg hg_nonneg (sub_nonneg.mpr hg_le_one)]
    have hg3 : g ^ 3 ≤ g := by
      have h : g ^ 2 * g ≤ g * g :=
        mul_le_mul_of_nonneg_right hg2 hg_nonneg
      have h' : g ^ 3 ≤ g ^ 2 := by nlinarith [h]
      exact le_trans h' hg2
    have hg4 : g ^ 4 ≤ g := by
      have h : g ^ 3 * g ≤ g * g :=
        mul_le_mul_of_nonneg_right hg3 hg_nonneg
      have h' : g ^ 4 ≤ g ^ 2 := by nlinarith [h]
      exact le_trans h' hg2
    ring_nf
    nlinarith [hg2, hg3, hg4]
  exact le_trans hFcap hpoly

/-- Unit-roundoff-cap form of
    `householderCompactNormBudgetCoeffFactor_le_of_u_gamma_le`.

    The gamma cap is no longer an independent hypothesis: it is derived from
    `fp.u ≤ Ucap`, `(n : ℝ) * Ucap < 1`, and a displayed domination of the
    resulting rational expression by `Gcap`. -/
theorem householderCompactNormBudgetCoeffFactor_le_of_u_cap_gamma_cap
    (fp : FPModel) (n : ℕ)
    (Ucap Gcap : ℝ)
    (hUcap_nonneg : 0 ≤ Ucap)
    (hu : fp.u ≤ Ucap)
    (hcap : (n : ℝ) * Ucap < 1)
    (hGcap : ((n : ℝ) * Ucap) / (1 - (n : ℝ) * Ucap) ≤ Gcap) :
    householderCompactNormBudgetCoeffFactor fp n ≤
      Ucap * (1 + Gcap) * (1 + Ucap) +
        Ucap * (1 + Gcap) +
        Gcap +
        Ucap * (1 + Gcap) * (1 + Ucap) ^ 2 := by
  have hn_nonneg : (0 : ℝ) ≤ n := by
    exact_mod_cast n.zero_le
  have hn : gammaValid fp n := by
    unfold gammaValid
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hu hn_nonneg) hcap
  have hden : 0 < 1 - (n : ℝ) * Ucap := by
    linarith
  have hGcap_nonneg : 0 ≤ Gcap := by
    exact le_trans
      (div_nonneg
        (mul_nonneg hn_nonneg hUcap_nonneg)
        (le_of_lt hden))
      hGcap
  exact
    householderCompactNormBudgetCoeffFactor_le_of_u_gamma_le
      fp n hn Ucap Gcap hUcap_nonneg hGcap_nonneg hu
      (gamma_le_Gcap_of_u_le_cap fp n Ucap Gcap hu hcap hGcap)

/-- A per-reflector bound on `|β| * ‖v‖₂^2` bounds the compact Householder
    norm-budget coefficient.

    This is the algebraic handoff used by the stored-QR product-budget route:
    it reduces bounding the FP compact-update coefficient to a pivot-local
    Householder estimate. -/
theorem householderCompactNormBudgetCoeff_le_of_abs_beta_norm_sq_le
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) (β B : ℝ)
    (hn : gammaValid fp n)
    (hB : |β| * vecNorm2 v ^ 2 ≤ B) :
    householderCompactNormBudgetCoeff fp n v β ≤
      fp.u + B * householderCompactNormBudgetCoeffFactor fp n := by
  rw [householderCompactNormBudgetCoeff_eq_u_add_abs_beta_norm_sq_mul_factor]
  have hmul :
      |β| * vecNorm2 v ^ 2 *
          householderCompactNormBudgetCoeffFactor fp n ≤
        B * householderCompactNormBudgetCoeffFactor fp n :=
    mul_le_mul_of_nonneg_right hB
      (householderCompactNormBudgetCoeffFactor_nonneg fp n hn)
  linarith

/-- Nonnegativity of the reflector-dependent update coefficient. -/
theorem householderCompactUpdateCoeff_nonneg
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) (β : ℝ)
    (hn : gammaValid fp n) :
    0 ≤ householderCompactUpdateCoeff fp n v β := by
  let V := vecNorm2 v
  let sigmaCoeff := (1 + gamma fp n) * V
  let tauCoeff := |β| * sigmaCoeff * (1 + fp.u)
  let zBudgetCoeff := tauCoeff * (1 + fp.u)
  let zErrorCoeff :=
    fp.u * tauCoeff + fp.u * |β| * sigmaCoeff + |β| * gamma fp n * V
  have hV : 0 ≤ V := by simpa [V] using vecNorm2_nonneg v
  have hgamma : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have h1gamma : 0 ≤ 1 + gamma fp n := by linarith
  have h1u : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
  have hsigma : 0 ≤ sigmaCoeff := by
    dsimp [sigmaCoeff]
    exact mul_nonneg h1gamma hV
  have htau : 0 ≤ tauCoeff := by
    dsimp [tauCoeff]
    exact mul_nonneg (mul_nonneg (abs_nonneg β) hsigma) h1u
  have hzBudget : 0 ≤ zBudgetCoeff := by
    dsimp [zBudgetCoeff]
    exact mul_nonneg htau h1u
  have hzError : 0 ≤ zErrorCoeff := by
    dsimp [zErrorCoeff]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg fp.u_nonneg htau)
        (mul_nonneg (mul_nonneg fp.u_nonneg (abs_nonneg β)) hsigma))
      (mul_nonneg (mul_nonneg (abs_nonneg β) hgamma) hV)
  simpa [householderCompactUpdateCoeff, V, sigmaCoeff, tauCoeff,
    zBudgetCoeff, zErrorCoeff] using
      add_nonneg hzError (mul_nonneg fp.u_nonneg hzBudget)

/-- Nonnegativity of the reflector-dependent normwise compact budget
    coefficient. -/
theorem householderCompactNormBudgetCoeff_nonneg
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) (β : ℝ)
    (hn : gammaValid fp n) :
    0 ≤ householderCompactNormBudgetCoeff fp n v β := by
  unfold householderCompactNormBudgetCoeff
  exact add_nonneg fp.u_nonneg
    (mul_nonneg
      (householderCompactUpdateCoeff_nonneg fp n v β hn)
      (vecNorm2_nonneg v))

/-- Componentwise compact-budget bound at norm scale.

    This theorem avoids the false-looking requirement
    `budget_i <= c * |b_i|`.  The dot/scale/update part is instead controlled
    by `‖b‖₂ |v_i|`, while the final subtraction contributes the local
    `u * |b_i|` term. -/
theorem householderCompactComponentBudget_le_updateCoeff_mul_norm
    (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) (b : Fin n → ℝ)
    (hn : gammaValid fp n) (i : Fin n) :
    householderCompactComponentBudget fp n v β b i ≤
      householderCompactUpdateCoeff fp n v β * vecNorm2 b * |v i| +
        fp.u * |b i| := by
  let S := householderAbsDotBudget n v b
  let B := vecNorm2 b
  let V := vecNorm2 v
  let D := gamma fp n * S
  let sigmaBudget := S + D
  let tauBudget := |β| * sigmaBudget * (1 + fp.u)
  let zBudget := tauBudget * |v i| * (1 + fp.u)
  let zError :=
    fp.u * tauBudget * |v i| +
      fp.u * |β| * sigmaBudget * |v i| +
      |β| * |v i| * D
  let sigmaCoeff := (1 + gamma fp n) * V
  let tauCoeff := |β| * sigmaCoeff * (1 + fp.u)
  let zBudgetCoeff := tauCoeff * (1 + fp.u)
  let zErrorCoeff :=
    fp.u * tauCoeff + fp.u * |β| * sigmaCoeff + |β| * gamma fp n * V
  have hB : 0 ≤ B := by simpa [B] using vecNorm2_nonneg b
  have hV : 0 ≤ V := by simpa [V] using vecNorm2_nonneg v
  have hS : 0 ≤ S := by
    simpa [S] using householderAbsDotBudget_nonneg n v b
  have hgamma : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have h1gamma : 0 ≤ 1 + gamma fp n := by linarith
  have h1u : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
  have hS_le : S ≤ V * B := by
    simpa [S, V, B, mul_comm] using
      householderAbsDotBudget_le_vecNorm2_mul n v b
  have hD_le : D ≤ gamma fp n * V * B := by
    dsimp [D]
    calc
      gamma fp n * S ≤ gamma fp n * (V * B) :=
        mul_le_mul_of_nonneg_left hS_le hgamma
      _ = gamma fp n * V * B := by ring
  have hsigma_nonneg : 0 ≤ sigmaBudget := by
    dsimp [sigmaBudget, D]
    exact add_nonneg hS (mul_nonneg hgamma hS)
  have hsigmaCoeff_nonneg : 0 ≤ sigmaCoeff := by
    dsimp [sigmaCoeff]
    exact mul_nonneg h1gamma hV
  have htauCoeff_nonneg : 0 ≤ tauCoeff := by
    dsimp [tauCoeff]
    exact mul_nonneg
      (mul_nonneg (abs_nonneg β) hsigmaCoeff_nonneg) h1u
  have hzBudgetCoeff_nonneg : 0 ≤ zBudgetCoeff := by
    dsimp [zBudgetCoeff]
    exact mul_nonneg htauCoeff_nonneg h1u
  have hzErrorCoeff_nonneg : 0 ≤ zErrorCoeff := by
    dsimp [zErrorCoeff]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg fp.u_nonneg htauCoeff_nonneg)
        (mul_nonneg
          (mul_nonneg fp.u_nonneg (abs_nonneg β)) hsigmaCoeff_nonneg))
      (mul_nonneg (mul_nonneg (abs_nonneg β) hgamma) hV)
  have hsigma_le : sigmaBudget ≤ sigmaCoeff * B := by
    dsimp [sigmaBudget, sigmaCoeff, D]
    calc
      S + gamma fp n * S ≤ V * B + gamma fp n * V * B :=
        add_le_add hS_le hD_le
      _ = ((1 + gamma fp n) * V) * B := by ring
  have htau_le : tauBudget ≤ tauCoeff * B := by
    dsimp [tauBudget, tauCoeff]
    calc
      |β| * sigmaBudget * (1 + fp.u) ≤
          |β| * (sigmaCoeff * B) * (1 + fp.u) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsigma_le (abs_nonneg β)) h1u
      _ = (|β| * sigmaCoeff * (1 + fp.u)) * B := by ring
  have hzBudget_le :
      zBudget ≤ zBudgetCoeff * B * |v i| := by
    dsimp [zBudget, zBudgetCoeff]
    calc
      tauBudget * |v i| * (1 + fp.u) ≤
          (tauCoeff * B) * |v i| * (1 + fp.u) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right htau_le (abs_nonneg (v i))) h1u
      _ = (tauCoeff * (1 + fp.u)) * B * |v i| := by ring
  have hzError_le :
      zError ≤ zErrorCoeff * B * |v i| := by
    dsimp [zError, zErrorCoeff]
    calc
      fp.u * tauBudget * |v i| +
          fp.u * |β| * sigmaBudget * |v i| +
          |β| * |v i| * D
        ≤ fp.u * (tauCoeff * B) * |v i| +
            fp.u * |β| * (sigmaCoeff * B) * |v i| +
            |β| * |v i| * (gamma fp n * V * B) := by
          exact add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left htau_le fp.u_nonneg)
                (abs_nonneg (v i)))
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hsigma_le
                  (mul_nonneg fp.u_nonneg (abs_nonneg β)))
                (abs_nonneg (v i))))
            (mul_le_mul_of_nonneg_left hD_le
              (mul_nonneg (abs_nonneg β) (abs_nonneg (v i))))
      _ = zErrorCoeff * B * |v i| := by ring
  calc
    householderCompactComponentBudget fp n v β b i
        = zError + fp.u * (|b i| + zBudget) := by
          simp [householderCompactComponentBudget, S, D, sigmaBudget,
            tauBudget, zBudget, zError]
    _ ≤ zErrorCoeff * B * |v i| +
          fp.u * (|b i| + zBudgetCoeff * B * |v i|) := by
        exact add_le_add hzError_le
          (mul_le_mul_of_nonneg_left
            (add_le_add le_rfl hzBudget_le) fp.u_nonneg)
    _ = (zErrorCoeff + fp.u * zBudgetCoeff) * B * |v i| +
          fp.u * |b i| := by ring
    _ = householderCompactUpdateCoeff fp n v β * vecNorm2 b * |v i| +
          fp.u * |b i| := by
        simp [householderCompactUpdateCoeff, B, V, sigmaCoeff, tauCoeff,
          zBudgetCoeff, zErrorCoeff]

/-- Norm of the explicit componentwise compact Householder budget. -/
noncomputable def householderCompactNormBudget (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) (b : Fin n → ℝ) : ℝ :=
  vecNorm2 (fun i : Fin n =>
    householderCompactComponentBudget fp n v β b i)

/-- Normwise compact-budget domination from the explicit reflector-dependent
    coefficient.

    Unlike the componentwise-relative bridge, this result is valid for zero or
    tiny input entries: the nonlocal Householder update is charged against
    `‖b‖₂‖v‖₂`, while only the final subtraction is charged against `|bᵢ|`. -/
theorem householderCompactNormBudget_le_normBudgetCoeff_mul
    (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) (b : Fin n → ℝ)
    (hn : gammaValid fp n) :
    householderCompactNormBudget fp n v β b ≤
      householderCompactNormBudgetCoeff fp n v β * vecNorm2 b := by
  let a := householderCompactUpdateCoeff fp n v β
  let B := vecNorm2 b
  have ha : 0 ≤ a := by
    simpa [a] using householderCompactUpdateCoeff_nonneg fp n v β hn
  have hB : 0 ≤ B := by simpa [B] using vecNorm2_nonneg b
  have hcomp :
      ∀ i : Fin n,
        |householderCompactComponentBudget fp n v β b i| ≤
          a * B * |v i| + fp.u * |b i| := by
    intro i
    have hnonneg :
        0 ≤ householderCompactComponentBudget fp n v β b i :=
      householderCompactComponentBudget_nonneg fp n v β b hn i
    rw [abs_of_nonneg hnonneg]
    simpa [a, B] using
      householderCompactComponentBudget_le_updateCoeff_mul_norm
        fp n v β b hn i
  unfold householderCompactNormBudget
  have hnorm :
      vecNorm2
          (fun i : Fin n =>
            householderCompactComponentBudget fp n v β b i) ≤
        vecNorm2 (fun i : Fin n => a * B * |v i| + fp.u * |b i|) :=
    vecNorm2_le_of_abs_le
      (fun i : Fin n => householderCompactComponentBudget fp n v β b i)
      (fun i : Fin n => a * B * |v i| + fp.u * |b i|)
      hcomp
  have htri :
      vecNorm2 (fun i : Fin n => a * B * |v i| + fp.u * |b i|) ≤
        vecNorm2 (fun i : Fin n => a * B * |v i|) +
          vecNorm2 (fun i : Fin n => fp.u * |b i|) :=
    vecNorm2_add_le
      (fun i : Fin n => a * B * |v i|)
      (fun i : Fin n => fp.u * |b i|)
  have hleft :
      vecNorm2 (fun i : Fin n => a * B * |v i|) =
        a * B * vecNorm2 v := by
    rw [show (fun i : Fin n => a * B * |v i|) =
        fun i : Fin n => (a * B) * |v i| by ext i; ring]
    rw [vecNorm2_smul, abs_of_nonneg (mul_nonneg ha hB), vecNorm2_abs]
  have hright :
      vecNorm2 (fun i : Fin n => fp.u * |b i|) =
        fp.u * vecNorm2 b := by
    rw [vecNorm2_smul, abs_of_nonneg fp.u_nonneg, vecNorm2_abs]
  calc
    vecNorm2
        (fun i : Fin n =>
          householderCompactComponentBudget fp n v β b i)
      ≤ vecNorm2 (fun i : Fin n => a * B * |v i| + fp.u * |b i|) :=
        hnorm
    _ ≤ vecNorm2 (fun i : Fin n => a * B * |v i|) +
          vecNorm2 (fun i : Fin n => fp.u * |b i|) :=
        htri
    _ = a * B * vecNorm2 v + fp.u * vecNorm2 b := by
        rw [hleft, hright]
    _ = householderCompactNormBudgetCoeff fp n v β * vecNorm2 b := by
        simp [householderCompactNormBudgetCoeff, a, B]
        ring

/-- Componentwise relative compact-budget domination gives the normwise
    compact-budget domination.

    This is the first reduction below the primitive norm-budget hypotheses:
    if every explicit component budget is bounded by `c * |bᵢ|`, then the
    component-budget vector has norm at most `c * ‖b‖₂`. -/
theorem householderCompactNormBudget_le_mul_of_componentBudget_le_mul_abs
    (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) (b : Fin n → ℝ)
    (c : ℝ) (hn : gammaValid fp n) (hc : 0 ≤ c)
    (hcomp : ∀ i : Fin n,
      householderCompactComponentBudget fp n v β b i ≤ c * |b i|) :
    householderCompactNormBudget fp n v β b ≤ c * vecNorm2 b := by
  unfold householderCompactNormBudget
  have hnorm :
      vecNorm2
          (fun i : Fin n =>
            householderCompactComponentBudget fp n v β b i) ≤
        vecNorm2 (fun i : Fin n => c * |b i|) := by
    exact
      vecNorm2_le_of_abs_le
        (fun i : Fin n =>
          householderCompactComponentBudget fp n v β b i)
        (fun i : Fin n => c * |b i|)
        (fun i => by
          have hnonneg :
              0 ≤ householderCompactComponentBudget fp n v β b i :=
            householderCompactComponentBudget_nonneg fp n v β b hn i
          simpa [abs_of_nonneg hnonneg] using hcomp i)
  have hscale :
      vecNorm2 (fun i : Fin n => c * |b i|) = c * vecNorm2 b := by
    rw [vecNorm2_smul]
    rw [abs_of_nonneg hc, vecNorm2_abs]
  exact hnorm.trans_eq hscale

/-- The explicit compact Householder component budget vanishes on the zero
    input vector. -/
theorem householderCompactComponentBudget_eq_zero_of_vecNorm2_eq_zero
    (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) (b : Fin n → ℝ)
    (hzero : vecNorm2 b = 0) (i : Fin n) :
    householderCompactComponentBudget fp n v β b i = 0 := by
  have hb : ∀ j : Fin n, b j = 0 := (vecNorm2_eq_zero_iff b).mp hzero
  have hS : householderAbsDotBudget n v b = 0 := by
    unfold householderAbsDotBudget
    simp [hb]
  simp [householderCompactComponentBudget, hS, hb]

/-- The norm of the compact Householder budget vanishes on the zero vector. -/
theorem householderCompactNormBudget_eq_zero_of_vecNorm2_eq_zero
    (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) (b : Fin n → ℝ)
    (hzero : vecNorm2 b = 0) :
    householderCompactNormBudget fp n v β b = 0 := by
  unfold householderCompactNormBudget
  exact (vecNorm2_eq_zero_iff _).mpr
    (fun i => householderCompactComponentBudget_eq_zero_of_vecNorm2_eq_zero
      fp n v β b hzero i)

/-- Relative compact Householder budget for one vector.  It is exactly the
    component-budget norm divided by the input norm when the input is nonzero,
    and zero on the zero vector. -/
noncomputable def householderCompactRelativeBudget (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) (b : Fin n → ℝ) : ℝ :=
  if vecNorm2 b = 0 then 0
  else householderCompactNormBudget fp n v β b / vecNorm2 b

/-- The relative compact Householder budget is nonnegative. -/
theorem householderCompactRelativeBudget_nonneg
    (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) (b : Fin n → ℝ)
    (_hn : gammaValid fp n) :
    0 ≤ householderCompactRelativeBudget fp n v β b := by
  unfold householderCompactRelativeBudget
  by_cases hzero : vecNorm2 b = 0
  · simp [hzero]
  · simp [hzero]
    exact div_nonneg (vecNorm2_nonneg _)
      (vecNorm2_nonneg b)

/-- The relative compact Householder budget dominates the component-budget norm
    by construction. -/
theorem householderCompactRelativeBudget_bound
    (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) (b : Fin n → ℝ) :
    householderCompactNormBudget fp n v β b ≤
      householderCompactRelativeBudget fp n v β b * vecNorm2 b := by
  unfold householderCompactRelativeBudget
  by_cases hzero : vecNorm2 b = 0
  · have hbudget :
        householderCompactNormBudget fp n v β b = 0 :=
      householderCompactNormBudget_eq_zero_of_vecNorm2_eq_zero
        fp n v β b hzero
    simp [hzero, hbudget]
  · simp [hzero]

/-- A normwise compact Householder budget domination gives the corresponding
    relative-budget cap.

    This is the reverse bookkeeping direction of
    `householderCompactRelativeBudget_bound`: it turns a primitive norm-budget
    estimate into the relative cap consumed by panel and stored-QR product
    estimates. -/
theorem householderCompactRelativeBudget_le_of_normBudget_le_mul
    (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) (b : Fin n → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hbudget :
      householderCompactNormBudget fp n v β b ≤ c * vecNorm2 b) :
    householderCompactRelativeBudget fp n v β b ≤ c := by
  unfold householderCompactRelativeBudget
  by_cases hzero : vecNorm2 b = 0
  · simp [hzero, hc]
  · have hpos : 0 < vecNorm2 b :=
      lt_of_le_of_ne (vecNorm2_nonneg b) (Ne.symm hzero)
    simp [hzero]
    exact (div_le_iff₀ hpos).mpr (by
      simpa [mul_comm] using hbudget)

/-- Relative-budget cap supplied by the explicit reflector-dependent normwise
    compact budget coefficient. -/
theorem householderCompactRelativeBudget_le_normBudgetCoeff
    (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) (b : Fin n → ℝ)
    (hn : gammaValid fp n) :
    householderCompactRelativeBudget fp n v β b ≤
      householderCompactNormBudgetCoeff fp n v β := by
  exact
    householderCompactRelativeBudget_le_of_normBudget_le_mul
      fp n v β b (householderCompactNormBudgetCoeff fp n v β)
      (householderCompactNormBudgetCoeff_nonneg fp n v β hn)
      (householderCompactNormBudget_le_normBudgetCoeff_mul
        fp n v β b hn)

/-- Componentwise compact-budget domination gives the corresponding
    relative-budget cap. -/
theorem householderCompactRelativeBudget_le_of_componentBudget_le_mul_abs
    (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) (b : Fin n → ℝ)
    (c : ℝ) (hn : gammaValid fp n) (hc : 0 ≤ c)
    (hcomp : ∀ i : Fin n,
      householderCompactComponentBudget fp n v β b i ≤ c * |b i|) :
    householderCompactRelativeBudget fp n v β b ≤ c := by
  exact
    householderCompactRelativeBudget_le_of_normBudget_le_mul
      fp n v β b c hc
      (householderCompactNormBudget_le_mul_of_componentBudget_le_mul_abs
        fp n v β b c hn hc hcomp)

/-- A single deterministic relative budget for a compact Householder panel
    step, obtained by summing the per-column and RHS relative budgets. -/
noncomputable def householderCompactPanelRelativeBudget (fp : FPModel)
    (m n : ℕ) (v : Fin m → ℝ) (β : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) : ℝ :=
  (∑ j : Fin n,
    householderCompactRelativeBudget fp m v β (fun i : Fin m => A i j)) +
    householderCompactRelativeBudget fp m v β b

/-- Nonnegativity of the single compact-panel relative budget. -/
theorem householderCompactPanelRelativeBudget_nonneg
    (fp : FPModel) (m n : ℕ)
    (v : Fin m → ℝ) (β : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hm : gammaValid fp m) :
    0 ≤ householderCompactPanelRelativeBudget fp m n v β A b := by
  unfold householderCompactPanelRelativeBudget
  exact add_nonneg
    (Finset.sum_nonneg
      (fun j _ => householderCompactRelativeBudget_nonneg
        fp m v β (fun i : Fin m => A i j) hm))
    (householderCompactRelativeBudget_nonneg fp m v β b hm)

/-- A compact-panel relative budget is bounded by uniform column and RHS
    relative-budget caps.

    This is the finite-sum bookkeeping step that turns vector-level compact
    Householder error estimates into a single panel-level cap. -/
theorem householderCompactPanelRelativeBudget_le_mul_add_of_column_rhs_le
    (fp : FPModel) (m n : ℕ)
    (v : Fin m → ℝ) (β : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (cCol cRhs : ℝ)
    (hCol : ∀ j : Fin n,
      householderCompactRelativeBudget fp m v β
        (fun i : Fin m => A i j) ≤ cCol)
    (hRhs : householderCompactRelativeBudget fp m v β b ≤ cRhs) :
    householderCompactPanelRelativeBudget fp m n v β A b ≤
      (n : ℝ) * cCol + cRhs := by
  calc
    householderCompactPanelRelativeBudget fp m n v β A b
        = (∑ j : Fin n,
            householderCompactRelativeBudget fp m v β
              (fun i : Fin m => A i j)) +
            householderCompactRelativeBudget fp m v β b := rfl
    _ ≤ (∑ _j : Fin n, cCol) + cRhs := by
      exact add_le_add
        (Finset.sum_le_sum (fun j _ => hCol j)) hRhs
    _ = (n : ℝ) * cCol + cRhs := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- A compact-panel relative budget is bounded by the explicit
    reflector-dependent normwise compact coefficient.

    The same coefficient works for every panel column and the RHS because it
    depends only on the reflector `(v, β)` and the machine model, not on the
    vector being updated. -/
theorem householderCompactPanelRelativeBudget_le_mul_add_normBudgetCoeff
    (fp : FPModel) (m n : ℕ)
    (v : Fin m → ℝ) (β : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hm : gammaValid fp m) :
    householderCompactPanelRelativeBudget fp m n v β A b ≤
      (n : ℝ) * householderCompactNormBudgetCoeff fp m v β +
        householderCompactNormBudgetCoeff fp m v β := by
  exact
    householderCompactPanelRelativeBudget_le_mul_add_of_column_rhs_le
      fp m n v β A b
      (householderCompactNormBudgetCoeff fp m v β)
      (householderCompactNormBudgetCoeff fp m v β)
      (fun j =>
        householderCompactRelativeBudget_le_normBudgetCoeff
          fp m v β (fun i : Fin m => A i j) hm)
      (householderCompactRelativeBudget_le_normBudgetCoeff
        fp m v β b hm)

/-- Panel relative-budget cap from primitive column/RHS norm-budget
    domination hypotheses.

    This is the panel-facing adapter used by stored QR: each vector-level
    norm-budget estimate is first converted to a relative-budget cap, then the
    finite panel sum gives `n * cCol + cRhs`. -/
theorem householderCompactPanelRelativeBudget_le_mul_add_of_normBudget_le_mul
    (fp : FPModel) (m n : ℕ)
    (v : Fin m → ℝ) (β : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (cCol cRhs : ℝ)
    (hcCol : 0 ≤ cCol) (hcRhs : 0 ≤ cRhs)
    (hCol : ∀ j : Fin n,
      householderCompactNormBudget fp m v β
        (fun i : Fin m => A i j) ≤
          cCol * vecNorm2 (fun i : Fin m => A i j))
    (hRhs :
      householderCompactNormBudget fp m v β b ≤ cRhs * vecNorm2 b) :
    householderCompactPanelRelativeBudget fp m n v β A b ≤
      (n : ℝ) * cCol + cRhs := by
  exact
    householderCompactPanelRelativeBudget_le_mul_add_of_column_rhs_le
      fp m n v β A b cCol cRhs
      (fun j =>
        householderCompactRelativeBudget_le_of_normBudget_le_mul
          fp m v β (fun i : Fin m => A i j) cCol hcCol (hCol j))
      (householderCompactRelativeBudget_le_of_normBudget_le_mul
        fp m v β b cRhs hcRhs hRhs)

/-- Panel relative-budget cap from componentwise column/RHS compact-budget
    domination hypotheses. -/
theorem householderCompactPanelRelativeBudget_le_mul_add_of_componentBudget_le_mul_abs
    (fp : FPModel) (m n : ℕ)
    (v : Fin m → ℝ) (β : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (cCol cRhs : ℝ)
    (hm : gammaValid fp m)
    (hcCol : 0 ≤ cCol) (hcRhs : 0 ≤ cRhs)
    (hCol : ∀ j : Fin n, ∀ i : Fin m,
      householderCompactComponentBudget fp m v β
        (fun a : Fin m => A a j) i ≤ cCol * |A i j|)
    (hRhs : ∀ i : Fin m,
      householderCompactComponentBudget fp m v β b i ≤ cRhs * |b i|) :
    householderCompactPanelRelativeBudget fp m n v β A b ≤
      (n : ℝ) * cCol + cRhs := by
  exact
    householderCompactPanelRelativeBudget_le_mul_add_of_normBudget_le_mul
      fp m n v β A b cCol cRhs
      hcCol hcRhs
      (fun j =>
        householderCompactNormBudget_le_mul_of_componentBudget_le_mul_abs
          fp m v β (fun i : Fin m => A i j) cCol hm hcCol
          (fun i => by simpa using hCol j i))
      (householderCompactNormBudget_le_mul_of_componentBudget_le_mul_abs
        fp m v β b cRhs hm hcRhs hRhs)

/-- The compact-panel relative budget dominates every panel-column budget. -/
theorem householderCompactPanelRelativeBudget_column_bound
    (fp : FPModel) (m n : ℕ)
    (v : Fin m → ℝ) (β : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hm : gammaValid fp m) (j : Fin n) :
    vecNorm2 (fun i : Fin m =>
        householderCompactComponentBudget fp m v β
          (fun a : Fin m => A a j) i) ≤
      householderCompactPanelRelativeBudget fp m n v β A b *
        vecNorm2 (fun i : Fin m => A i j) := by
  have hrel :
      householderCompactRelativeBudget fp m v β
          (fun i : Fin m => A i j) ≤
        householderCompactPanelRelativeBudget fp m n v β A b := by
    have hsingle :
        householderCompactRelativeBudget fp m v β
            (fun i : Fin m => A i j) ≤
          ∑ k : Fin n,
            householderCompactRelativeBudget fp m v β
              (fun i : Fin m => A i k) :=
      Finset.single_le_sum
        (fun k _ => householderCompactRelativeBudget_nonneg
          fp m v β (fun i : Fin m => A i k) hm)
        (Finset.mem_univ j)
    have hrhs :
        0 ≤ householderCompactRelativeBudget fp m v β b :=
      householderCompactRelativeBudget_nonneg fp m v β b hm
    unfold householderCompactPanelRelativeBudget
    linarith
  calc
    vecNorm2 (fun i : Fin m =>
        householderCompactComponentBudget fp m v β
          (fun a : Fin m => A a j) i)
        = householderCompactNormBudget fp m v β
            (fun a : Fin m => A a j) := rfl
    _ ≤ householderCompactRelativeBudget fp m v β
          (fun a : Fin m => A a j) *
        vecNorm2 (fun i : Fin m => A i j) :=
      householderCompactRelativeBudget_bound fp m v β
        (fun i : Fin m => A i j)
    _ ≤ householderCompactPanelRelativeBudget fp m n v β A b *
        vecNorm2 (fun i : Fin m => A i j) :=
      mul_le_mul_of_nonneg_right hrel
        (vecNorm2_nonneg (fun i : Fin m => A i j))

/-- The compact-panel relative budget dominates the RHS budget. -/
theorem householderCompactPanelRelativeBudget_rhs_bound
    (fp : FPModel) (m n : ℕ)
    (v : Fin m → ℝ) (β : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hm : gammaValid fp m) :
    vecNorm2 (fun i : Fin m =>
        householderCompactComponentBudget fp m v β b i) ≤
      householderCompactPanelRelativeBudget fp m n v β A b *
        vecNorm2 b := by
  have hrel :
      householderCompactRelativeBudget fp m v β b ≤
        householderCompactPanelRelativeBudget fp m n v β A b := by
    have hsum :
        0 ≤ ∑ k : Fin n,
          householderCompactRelativeBudget fp m v β
            (fun i : Fin m => A i k) :=
      Finset.sum_nonneg
        (fun k _ => householderCompactRelativeBudget_nonneg
          fp m v β (fun i : Fin m => A i k) hm)
    unfold householderCompactPanelRelativeBudget
    linarith
  calc
    vecNorm2 (fun i : Fin m =>
        householderCompactComponentBudget fp m v β b i)
        = householderCompactNormBudget fp m v β b := rfl
    _ ≤ householderCompactRelativeBudget fp m v β b *
        vecNorm2 b :=
      householderCompactRelativeBudget_bound fp m v β b
    _ ≤ householderCompactPanelRelativeBudget fp m n v β A b *
        vecNorm2 b :=
      mul_le_mul_of_nonneg_right hrel (vecNorm2_nonneg b)

/-- The compact-panel relative budget also dominates the stored-step masked
    panel-column budget. -/
theorem householderCompactPanelRelativeBudget_stored_column_bound
    (fp : FPModel) (m n k : ℕ)
    (v : Fin m → ℝ) (β : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hm : gammaValid fp m) (j : Fin n) :
    vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m v β
          (fun a : Fin m => A a j) i) ≤
      householderCompactPanelRelativeBudget fp m n v β A b *
        vecNorm2 (fun i : Fin m => A i j) := by
  have hmask :
      vecNorm2 (fun i : Fin m =>
          if j.val < k then 0
          else householderCompactComponentBudget fp m v β
            (fun a : Fin m => A a j) i) ≤
        vecNorm2 (fun i : Fin m =>
          householderCompactComponentBudget fp m v β
            (fun a : Fin m => A a j) i) := by
    apply vecNorm2_le_of_abs_le
    intro i
    by_cases hj : j.val < k
    · simp [hj, householderCompactComponentBudget_nonneg
        fp m v β (fun a : Fin m => A a j) hm i]
    · have hnonneg :
          0 ≤ householderCompactComponentBudget fp m v β
            (fun a : Fin m => A a j) i :=
        householderCompactComponentBudget_nonneg
          fp m v β (fun a : Fin m => A a j) hm i
      simp [hj, abs_of_nonneg hnonneg]
  exact le_trans hmask
    (householderCompactPanelRelativeBudget_column_bound
      fp m n v β A b hm j)

/-- The compact-panel relative budget also dominates the stored-step masked RHS
    budget. -/
theorem householderCompactPanelRelativeBudget_stored_rhs_bound
    (fp : FPModel) (m n k : ℕ)
    (v : Fin m → ℝ) (β : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hm : gammaValid fp m) :
    vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m v β b i) ≤
      householderCompactPanelRelativeBudget fp m n v β A b *
        vecNorm2 b := by
  have hmask :
      vecNorm2 (fun i : Fin m =>
          if i.val < k then 0
          else householderCompactComponentBudget fp m v β b i) ≤
        vecNorm2 (fun i : Fin m =>
          householderCompactComponentBudget fp m v β b i) := by
    apply vecNorm2_le_of_abs_le
    intro i
    by_cases hi : i.val < k
    · simp [hi, householderCompactComponentBudget_nonneg fp m v β b hm i]
    · have hnonneg :
          0 ≤ householderCompactComponentBudget fp m v β b i :=
        householderCompactComponentBudget_nonneg fp m v β b hm i
      simp [hi, abs_of_nonneg hnonneg]
  exact le_trans hmask
    (householderCompactPanelRelativeBudget_rhs_bound
      fp m n v β A b hm)

/-- Componentwise forward-error bound for the stored RHS step.

    Rows above the pivot are preserved exactly, so their error is zero under
    the explicit `hprefix` preservation hypothesis.  Active-tail rows use the
    compact Householder budget. -/
theorem fl_householderStoredRhsStep_componentwise_error_bound
    (fp : FPModel) (m k : ℕ)
    (v : Fin m → ℝ) (β : ℝ) (b : Fin m → ℝ)
    (hm : gammaValid fp m)
    (hprefix : ∀ i : Fin m, i.val < k →
      matMulVec m (householder m v β) b i = b i) :
    ∀ i : Fin m,
      |fl_householderStoredRhsStep fp m k v β b i -
          matMulVec m (householder m v β) b i| ≤
        if i.val < k then 0
        else householderCompactComponentBudget fp m v β b i := by
  intro i
  by_cases hi : i.val < k
  · simp [fl_householderStoredRhsStep, hi, hprefix i hi]
  · simpa [fl_householderStoredRhsStep, hi] using
      fl_householderApplyCompact_componentwise_error_bound fp m v β b hm i

/-- Normwise forward-error bound for the stored RHS step. -/
theorem fl_householderStoredRhsStep_forward_error_bound
    (fp : FPModel) (m k : ℕ)
    (v : Fin m → ℝ) (β : ℝ) (b : Fin m → ℝ)
    (hm : gammaValid fp m)
    (hprefix : ∀ i : Fin m, i.val < k →
      matMulVec m (householder m v β) b i = b i) :
    vecNorm2 (fun i : Fin m =>
        fl_householderStoredRhsStep fp m k v β b i -
          matMulVec m (householder m v β) b i) ≤
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m v β b i) := by
  exact vecNorm2_le_of_abs_le
    (fun i : Fin m =>
      fl_householderStoredRhsStep fp m k v β b i -
        matMulVec m (householder m v β) b i)
    (fun i : Fin m =>
      if i.val < k then 0
      else householderCompactComponentBudget fp m v β b i)
    (fl_householderStoredRhsStep_componentwise_error_bound
      fp m k v β b hm hprefix)

/-- Componentwise forward-error bound for one stored panel column.

    Completed columns are preserved exactly under `hcompleted`; the current
    pivot column is stored with exact zeros below the pivot under `hpivot`;
    all other active/trailing entries use the compact Householder budget. -/
theorem fl_householderStoredPanelStep_column_componentwise_error_bound
    (fp : FPModel) (m n k : ℕ)
    (v : Fin m → ℝ) (β : ℝ) (A : Fin m → Fin n → ℝ)
    (hm : gammaValid fp m) (j : Fin n)
    (hcompleted : j.val < k →
      ∀ i : Fin m, matMulVec m (householder m v β)
        (fun a => A a j) i = A i j)
    (hpivot : j.val = k →
      ∀ i : Fin m, k < i.val →
        matMulVec m (householder m v β) (fun a => A a j) i = 0) :
    ∀ i : Fin m,
      |fl_householderStoredPanelStep fp m n k v β A i j -
          matMulVec m (householder m v β) (fun a => A a j) i| ≤
        if j.val < k then 0
        else householderCompactComponentBudget fp m v β (fun a => A a j) i := by
  intro i
  by_cases hprev : j.val < k
  · simp [fl_householderStoredPanelStep, hprev, hcompleted hprev i]
  · by_cases hpiv : j.val = k
    · by_cases hbelow : k < i.val
      · have hzero := hpivot hpiv i hbelow
        have hbudget_nonneg :
            0 ≤ householderCompactComponentBudget fp m v β (fun a => A a j) i :=
          householderCompactComponentBudget_nonneg fp m v β (fun a => A a j) hm i
        simpa [fl_householderStoredPanelStep, hprev, hpiv, hbelow, hzero]
          using hbudget_nonneg
      · simpa [fl_householderStoredPanelStep, hprev, hpiv, hbelow] using
          fl_householderApplyCompact_componentwise_error_bound
            fp m v β (fun a => A a j) hm i
    · simpa [fl_householderStoredPanelStep, hprev, hpiv] using
        fl_householderApplyCompact_componentwise_error_bound
          fp m v β (fun a => A a j) hm i

/-- Active-column entry form of
    `fl_householderStoredPanelStep_column_componentwise_error_bound`.

    This is the per-entry budget needed by the Cox--Higham row-wise route:
    once column `j` is active at stage `k`, the concrete stored rounded panel
    step differs from the exact same-reflector update by the local compact
    component budget for that row and column. -/
theorem fl_householderStoredPanelStep_active_entry_componentwise_error_bound
    (fp : FPModel) (m n k : ℕ)
    (v : Fin m → ℝ) (β : ℝ) (A : Fin m → Fin n → ℝ)
    (hm : gammaValid fp m) (i : Fin m) (j : Fin n)
    (hactive : k ≤ j.val)
    (hcompleted : j.val < k →
      ∀ i : Fin m, matMulVec m (householder m v β)
        (fun a => A a j) i = A i j)
    (hpivot : j.val = k →
      ∀ i : Fin m, k < i.val →
        matMulVec m (householder m v β) (fun a => A a j) i = 0) :
    |fl_householderStoredPanelStep fp m n k v β A i j -
        matMulVec m (householder m v β) (fun a => A a j) i| ≤
      householderCompactComponentBudget fp m v β (fun a => A a j) i := by
  have hbase :=
    fl_householderStoredPanelStep_column_componentwise_error_bound
      fp m n k v β A hm j hcompleted hpivot i
  have hnot : ¬ j.val < k := not_lt_of_ge hactive
  simpa [hnot] using hbase

/-- One concrete stored rounded panel step supplies the additive term in the
    Cox--Higham row-wise error recurrence.

    The hypothesis `hexact` is the exact same-reflector Lipschitz/growth field
    that comes from the Cox--Higham pivoting/sorting analysis.  This lemma
    discharges only the floating-point part: the concrete stored rounded step
    contributes exactly the compact Householder component budget as the
    additive per-step error. -/
theorem coxHigham_storedPanelStep_row_error_recurrence_of_exact_lipschitz
    (fp : FPModel) (m n k : ℕ)
    (v : Fin m → ℝ) (β : ℝ)
    (AhatPrev AexactPrev : Fin m → Fin n → ℝ)
    (AexactNext : Fin m → Fin n → ℝ)
    (hm : gammaValid fp m) (r : Fin m) (j : Fin n)
    (hactive : k ≤ j.val)
    (hcompleted : j.val < k →
      ∀ i : Fin m, matMulVec m (householder m v β)
        (fun a => AhatPrev a j) i = AhatPrev i j)
    (hpivot : j.val = k →
      ∀ i : Fin m, k < i.val →
        matMulVec m (householder m v β) (fun a => AhatPrev a j) i = 0)
    (hexact :
      |matMulVec m (householder m v β) (fun a => AhatPrev a j) r -
          AexactNext r j| ≤
        (1 + Real.sqrt 2) * |AhatPrev r j - AexactPrev r j|) :
    |fl_householderStoredPanelStep fp m n k v β AhatPrev r j -
        AexactNext r j| ≤
      (1 + Real.sqrt 2) * |AhatPrev r j - AexactPrev r j| +
        householderCompactComponentBudget fp m v β (fun a => AhatPrev a j) r := by
  let exactUpdate : ℝ :=
    matMulVec m (householder m v β) (fun a => AhatPrev a j) r
  have hround :
      |fl_householderStoredPanelStep fp m n k v β AhatPrev r j -
          exactUpdate| ≤
        householderCompactComponentBudget fp m v β
          (fun a => AhatPrev a j) r := by
    simpa [exactUpdate] using
      fl_householderStoredPanelStep_active_entry_componentwise_error_bound
        fp m n k v β AhatPrev hm r j hactive hcompleted hpivot
  calc
    |fl_householderStoredPanelStep fp m n k v β AhatPrev r j -
        AexactNext r j|
        ≤ |fl_householderStoredPanelStep fp m n k v β AhatPrev r j -
            exactUpdate| + |exactUpdate - AexactNext r j| := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            abs_sub_le
              (fl_householderStoredPanelStep fp m n k v β AhatPrev r j)
              exactUpdate (AexactNext r j)
    _ ≤ householderCompactComponentBudget fp m v β
          (fun a => AhatPrev a j) r +
        (1 + Real.sqrt 2) * |AhatPrev r j - AexactPrev r j| :=
          add_le_add hround hexact
    _ = (1 + Real.sqrt 2) * |AhatPrev r j - AexactPrev r j| +
        householderCompactComponentBudget fp m v β
          (fun a => AhatPrev a j) r := by ring

/-- Concrete stored rounded panel sequence version of the Cox--Higham row-wise
    accumulated perturbation bound.

    This theorem instantiates the abstract additive recurrence with the
    repository's concrete compact Householder component budget at each stored
    rounded panel step.  The exact Cox--Higham growth hypothesis is still
    visible as `hexact`: the lemma closes the floating-point per-step-budget
    part of the pivoted/sorted route, not the final QR/preconditioner theorem. -/
theorem coxHigham_storedPanel_sequence_rowwise_error_accumulation_bound_of_exact_lipschitz
    {m n : ℕ} (fp : FPModel) (steps : Fin m)
    (Ahat Aexact : ℕ → Fin m → Fin n → ℝ)
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ)
    (hm : gammaValid fp m) (r : Fin m) (j : Fin n)
    (hstep : ∀ t : ℕ, t < steps.val →
      Ahat (t + 1) = fl_householderStoredPanelStep fp m n t (v t) (β t) (Ahat t))
    (hactive : ∀ t : ℕ, t < steps.val → t ≤ j.val)
    (hcompleted : ∀ t : ℕ, t < steps.val → j.val < t →
      ∀ i : Fin m, matMulVec m (householder m (v t) (β t))
        (fun a => Ahat t a j) i = Ahat t i j)
    (hpivot : ∀ t : ℕ, t < steps.val → j.val = t →
      ∀ i : Fin m, t < i.val →
        matMulVec m (householder m (v t) (β t)) (fun a => Ahat t a j) i = 0)
    (hexact : ∀ t : ℕ, t < steps.val →
      |matMulVec m (householder m (v t) (β t)) (fun a => Ahat t a j) r -
          Aexact (t + 1) r j| ≤
        (1 + Real.sqrt 2) * |Ahat t r j - Aexact t r j|) :
    |Ahat steps.val r j - Aexact steps.val r j| ≤
      (1 + Real.sqrt 2) ^ steps.val * |Ahat 0 r j - Aexact 0 r j| +
        scalarAffineGrowthBudget (1 + Real.sqrt 2)
          (fun t => householderCompactComponentBudget fp m (v t) (β t)
            (fun a => Ahat t a j) r)
          steps.val := by
  refine
    coxHigham_rowwise_error_accumulation_bound
      steps r j Ahat Aexact
        (fun t => householderCompactComponentBudget fp m (v t) (β t)
          (fun a => Ahat t a j) r) ?_
  intro t ht
  rw [hstep t ht]
  exact
    coxHigham_storedPanelStep_row_error_recurrence_of_exact_lipschitz
      fp m n t (v t) (β t) (Ahat t) (Aexact t) (Aexact (t + 1))
      hm r j (hactive t ht) (hcompleted t ht) (hpivot t ht) (hexact t ht)

/-- Direct one-step rounded row-magnitude recurrence for the Cox--Higham route.

    This is the source-shaped alternative to the older exact-sequence adapter:
    if the exact same-reflector update of the current stored panel entry has
    the Cox--Higham row-growth bound, then the concrete rounded stored panel
    entry has the same bound plus the local compact Householder component
    budget. -/
theorem coxHigham_storedPanelStep_active_entry_bound_of_exact_growth
    (fp : FPModel) (m n k : ℕ)
    (v : Fin m → ℝ) (β : ℝ) (AhatPrev : Fin m → Fin n → ℝ)
    (hm : gammaValid fp m) (r : Fin m) (j : Fin n)
    (hactive : k ≤ j.val)
    (hcompleted : j.val < k →
      ∀ i : Fin m, matMulVec m (householder m v β)
        (fun a => AhatPrev a j) i = AhatPrev i j)
    (hpivot : j.val = k →
      ∀ i : Fin m, k < i.val →
        matMulVec m (householder m v β) (fun a => AhatPrev a j) i = 0)
    (hexact :
      |matMulVec m (householder m v β) (fun a => AhatPrev a j) r| ≤
        (1 + Real.sqrt 2) * |AhatPrev r j|) :
    |fl_householderStoredPanelStep fp m n k v β AhatPrev r j| ≤
      (1 + Real.sqrt 2) * |AhatPrev r j| +
        householderCompactComponentBudget fp m v β (fun a => AhatPrev a j) r := by
  let exactUpdate : ℝ :=
    matMulVec m (householder m v β) (fun a => AhatPrev a j) r
  have hround :
      |fl_householderStoredPanelStep fp m n k v β AhatPrev r j -
          exactUpdate| ≤
        householderCompactComponentBudget fp m v β
          (fun a => AhatPrev a j) r := by
    simpa [exactUpdate] using
      fl_householderStoredPanelStep_active_entry_componentwise_error_bound
        fp m n k v β AhatPrev hm r j hactive hcompleted hpivot
  have htri :
      |fl_householderStoredPanelStep fp m n k v β AhatPrev r j| ≤
        |fl_householderStoredPanelStep fp m n k v β AhatPrev r j -
            exactUpdate| + |exactUpdate| := by
    have hsum :
        fl_householderStoredPanelStep fp m n k v β AhatPrev r j =
          (fl_householderStoredPanelStep fp m n k v β AhatPrev r j -
              exactUpdate) + exactUpdate := by
      ring
    calc
      |fl_householderStoredPanelStep fp m n k v β AhatPrev r j|
          = |(fl_householderStoredPanelStep fp m n k v β AhatPrev r j -
              exactUpdate) + exactUpdate| := by
              exact congrArg (fun z : ℝ => |z|) hsum
      _ ≤ |fl_householderStoredPanelStep fp m n k v β AhatPrev r j -
            exactUpdate| + |exactUpdate| := by
          exact abs_add_le
            (fl_householderStoredPanelStep fp m n k v β AhatPrev r j -
              exactUpdate) exactUpdate
  calc
    |fl_householderStoredPanelStep fp m n k v β AhatPrev r j|
        ≤ |fl_householderStoredPanelStep fp m n k v β AhatPrev r j -
            exactUpdate| + |exactUpdate| := htri
    _ ≤ householderCompactComponentBudget fp m v β
          (fun a => AhatPrev a j) r +
        (1 + Real.sqrt 2) * |AhatPrev r j| :=
          add_le_add hround (by simpa [exactUpdate] using hexact)
    _ = (1 + Real.sqrt 2) * |AhatPrev r j| +
        householderCompactComponentBudget fp m v β
          (fun a => AhatPrev a j) r := by ring

/-- Direct one-step rounded row-magnitude recurrence with an arbitrary exact
    growth factor.

    This is the factor-parametric version needed to hand off the exact
    Cox--Higham active-row bridge, whose honest one-step factor is
    `coxHighamActiveRowGrowthFactor m = max (1 + sqrt 2) (sqrt m)`. -/
theorem coxHigham_storedPanelStep_active_entry_bound_of_exact_growth_factor
    (fp : FPModel) (m n k : ℕ)
    (v : Fin m → ℝ) (β c : ℝ) (AhatPrev : Fin m → Fin n → ℝ)
    (hm : gammaValid fp m) (r : Fin m) (j : Fin n)
    (hactive : k ≤ j.val)
    (hcompleted : j.val < k →
      ∀ i : Fin m, matMulVec m (householder m v β)
        (fun a => AhatPrev a j) i = AhatPrev i j)
    (hpivot : j.val = k →
      ∀ i : Fin m, k < i.val →
        matMulVec m (householder m v β) (fun a => AhatPrev a j) i = 0)
    (hexact :
      |matMulVec m (householder m v β) (fun a => AhatPrev a j) r| ≤
        c * |AhatPrev r j|) :
    |fl_householderStoredPanelStep fp m n k v β AhatPrev r j| ≤
      c * |AhatPrev r j| +
        householderCompactComponentBudget fp m v β (fun a => AhatPrev a j) r := by
  let exactUpdate : ℝ :=
    matMulVec m (householder m v β) (fun a => AhatPrev a j) r
  have hround :
      |fl_householderStoredPanelStep fp m n k v β AhatPrev r j -
          exactUpdate| ≤
        householderCompactComponentBudget fp m v β
          (fun a => AhatPrev a j) r := by
    simpa [exactUpdate] using
      fl_householderStoredPanelStep_active_entry_componentwise_error_bound
        fp m n k v β AhatPrev hm r j hactive hcompleted hpivot
  have htri :
      |fl_householderStoredPanelStep fp m n k v β AhatPrev r j| ≤
        |fl_householderStoredPanelStep fp m n k v β AhatPrev r j -
            exactUpdate| + |exactUpdate| := by
    have hsum :
        fl_householderStoredPanelStep fp m n k v β AhatPrev r j =
          (fl_householderStoredPanelStep fp m n k v β AhatPrev r j -
              exactUpdate) + exactUpdate := by
      ring
    calc
      |fl_householderStoredPanelStep fp m n k v β AhatPrev r j|
          = |(fl_householderStoredPanelStep fp m n k v β AhatPrev r j -
              exactUpdate) + exactUpdate| := by
              exact congrArg (fun z : ℝ => |z|) hsum
      _ ≤ |fl_householderStoredPanelStep fp m n k v β AhatPrev r j -
            exactUpdate| + |exactUpdate| := by
          exact abs_add_le
            (fl_householderStoredPanelStep fp m n k v β AhatPrev r j -
              exactUpdate) exactUpdate
  calc
    |fl_householderStoredPanelStep fp m n k v β AhatPrev r j|
        ≤ |fl_householderStoredPanelStep fp m n k v β AhatPrev r j -
            exactUpdate| + |exactUpdate| := htri
    _ ≤ householderCompactComponentBudget fp m v β
          (fun a => AhatPrev a j) r +
        c * |AhatPrev r j| :=
          add_le_add hround (by simpa [exactUpdate] using hexact)
    _ = c * |AhatPrev r j| +
        householderCompactComponentBudget fp m v β
          (fun a => AhatPrev a j) r := by ring

/-- Direct stored-panel sequence row-magnitude recurrence for Cox--Higham.

    The hypothesis `hexact` is now the source-visible exact same-reflector
    row-growth field for the current stored panel, rather than an error bound
    against a separate exact sequence.  The theorem accumulates only the
    concrete floating-point compact Householder component budgets. -/
theorem coxHigham_storedPanel_sequence_active_entry_bound_of_exact_growth
    {m n : ℕ} (fp : FPModel) (steps : Fin m)
    (Ahat : ℕ → Fin m → Fin n → ℝ)
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ)
    (hm : gammaValid fp m) (r : Fin m) (j : Fin n)
    (hstep : ∀ t : ℕ, t < steps.val →
      Ahat (t + 1) = fl_householderStoredPanelStep fp m n t (v t) (β t) (Ahat t))
    (hactive : ∀ t : ℕ, t < steps.val → t ≤ j.val)
    (hcompleted : ∀ t : ℕ, t < steps.val → j.val < t →
      ∀ i : Fin m, matMulVec m (householder m (v t) (β t))
        (fun a => Ahat t a j) i = Ahat t i j)
    (hpivot : ∀ t : ℕ, t < steps.val → j.val = t →
      ∀ i : Fin m, t < i.val →
        matMulVec m (householder m (v t) (β t)) (fun a => Ahat t a j) i = 0)
    (hexact : ∀ t : ℕ, t < steps.val →
      |matMulVec m (householder m (v t) (β t)) (fun a => Ahat t a j) r| ≤
        (1 + Real.sqrt 2) * |Ahat t r j|) :
    |Ahat steps.val r j| ≤
      (1 + Real.sqrt 2) ^ steps.val * |Ahat 0 r j| +
        scalarAffineGrowthBudget (1 + Real.sqrt 2)
          (fun t => householderCompactComponentBudget fp m (v t) (β t)
            (fun a => Ahat t a j) r)
          steps.val := by
  let c : ℝ := 1 + Real.sqrt 2
  let M : ℕ → ℝ := fun t => |Ahat t r j|
  have hrec :
      ∀ t : ℕ, t < steps.val →
        M (t + 1) ≤ c * M t +
          householderCompactComponentBudget fp m (v t) (β t)
            (fun a => Ahat t a j) r := by
    intro t ht
    change
      |Ahat (t + 1) r j| ≤ c * |Ahat t r j| +
        householderCompactComponentBudget fp m (v t) (β t)
          (fun a => Ahat t a j) r
    rw [hstep t ht]
    simpa [c] using
      coxHigham_storedPanelStep_active_entry_bound_of_exact_growth
        fp m n t (v t) (β t) (Ahat t) hm r j
        (hactive t ht) (hcompleted t ht) (hpivot t ht) (hexact t ht)
  simpa [M, c] using
    scalar_affine_growth_iterate_bound c M
      (fun t => householderCompactComponentBudget fp m (v t) (β t)
        (fun a => Ahat t a j) r)
      steps.val coxHighamGrowthFactor_nonneg hrec

/-- Direct stored-panel sequence recurrence with an arbitrary exact growth
    factor.

    The exact Cox--Higham active-row loop uses the factor
    `coxHighamActiveRowGrowthFactor m`, while older non-pivot-only dependencies
    use `1 + sqrt 2`.  This theorem is the common floating-point handoff: once
    the exact same-reflector row-growth field is supplied with any nonnegative
    factor `c`, the concrete compact Householder component budgets accumulate
    through `scalarAffineGrowthBudget c`. -/
theorem coxHigham_storedPanel_sequence_active_entry_bound_of_exact_growth_factor
    {m n : ℕ} (fp : FPModel) (steps : Fin m)
    (Ahat : ℕ → Fin m → Fin n → ℝ)
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ) (c : ℝ)
    (hm : gammaValid fp m) (r : Fin m) (j : Fin n)
    (hc : 0 ≤ c)
    (hstep : ∀ t : ℕ, t < steps.val →
      Ahat (t + 1) = fl_householderStoredPanelStep fp m n t (v t) (β t) (Ahat t))
    (hactive : ∀ t : ℕ, t < steps.val → t ≤ j.val)
    (hcompleted : ∀ t : ℕ, t < steps.val → j.val < t →
      ∀ i : Fin m, matMulVec m (householder m (v t) (β t))
        (fun a => Ahat t a j) i = Ahat t i j)
    (hpivot : ∀ t : ℕ, t < steps.val → j.val = t →
      ∀ i : Fin m, t < i.val →
        matMulVec m (householder m (v t) (β t)) (fun a => Ahat t a j) i = 0)
    (hexact : ∀ t : ℕ, t < steps.val →
      |matMulVec m (householder m (v t) (β t)) (fun a => Ahat t a j) r| ≤
        c * |Ahat t r j|) :
    |Ahat steps.val r j| ≤
      c ^ steps.val * |Ahat 0 r j| +
        scalarAffineGrowthBudget c
          (fun t => householderCompactComponentBudget fp m (v t) (β t)
            (fun a => Ahat t a j) r)
          steps.val := by
  let M : ℕ → ℝ := fun t => |Ahat t r j|
  have hrec :
      ∀ t : ℕ, t < steps.val →
        M (t + 1) ≤ c * M t +
          householderCompactComponentBudget fp m (v t) (β t)
            (fun a => Ahat t a j) r := by
    intro t ht
    change
      |Ahat (t + 1) r j| ≤ c * |Ahat t r j| +
        householderCompactComponentBudget fp m (v t) (β t)
          (fun a => Ahat t a j) r
    rw [hstep t ht]
    simpa using
      coxHigham_storedPanelStep_active_entry_bound_of_exact_growth_factor
        fp m n t (v t) (β t) c (Ahat t) hm r j
        (hactive t ht) (hcompleted t ht) (hpivot t ht) (hexact t ht)
  simpa [M] using
    scalar_affine_growth_iterate_bound c M
      (fun t => householderCompactComponentBudget fp m (v t) (β t)
        (fun a => Ahat t a j) r)
      steps.val hc hrec

/-- Direct stored-panel sequence recurrence using the honest active-row
    Cox--Higham factor `max (1 + sqrt 2) (sqrt m)`.

    This is the floating-point handoff for the exact signed-pivot panel
    sequence theorem.  It keeps the exact same-reflector growth field visible:
    a later concrete pivoted/sorted loop theorem must still supply `hexact`
    from the sorting-policy stage budgets. -/
theorem coxHigham_storedPanel_sequence_active_entry_bound_of_exact_active_growth
    {m n : ℕ} (fp : FPModel) (steps : Fin m)
    (Ahat : ℕ → Fin m → Fin n → ℝ)
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ)
    (hm : gammaValid fp m) (r : Fin m) (j : Fin n)
    (hstep : ∀ t : ℕ, t < steps.val →
      Ahat (t + 1) = fl_householderStoredPanelStep fp m n t (v t) (β t) (Ahat t))
    (hactive : ∀ t : ℕ, t < steps.val → t ≤ j.val)
    (hcompleted : ∀ t : ℕ, t < steps.val → j.val < t →
      ∀ i : Fin m, matMulVec m (householder m (v t) (β t))
        (fun a => Ahat t a j) i = Ahat t i j)
    (hpivot : ∀ t : ℕ, t < steps.val → j.val = t →
      ∀ i : Fin m, t < i.val →
        matMulVec m (householder m (v t) (β t)) (fun a => Ahat t a j) i = 0)
    (hexact : ∀ t : ℕ, t < steps.val →
      |matMulVec m (householder m (v t) (β t)) (fun a => Ahat t a j) r| ≤
        coxHighamActiveRowGrowthFactor m * |Ahat t r j|) :
    |Ahat steps.val r j| ≤
      coxHighamActiveRowGrowthFactor m ^ steps.val * |Ahat 0 r j| +
        scalarAffineGrowthBudget (coxHighamActiveRowGrowthFactor m)
          (fun t => householderCompactComponentBudget fp m (v t) (β t)
            (fun a => Ahat t a j) r)
          steps.val := by
  exact
    coxHigham_storedPanel_sequence_active_entry_bound_of_exact_growth_factor
      fp steps Ahat v β (coxHighamActiveRowGrowthFactor m) hm r j
      (coxHighamActiveRowGrowthFactor_nonneg m)
      hstep hactive hcompleted hpivot hexact

/-- One-step stored-panel row-magnitude handoff from an exact stage budget.

    This is the budget-shaped sibling of
    `coxHigham_storedPanelStep_active_entry_bound_of_exact_growth_factor`.
    Instead of asking the exact same-reflector row-growth theorem to be
    proportional to the current stored entry, it accepts the source-visible
    stage budget `B`.  This matches the Cox--Higham signed-pivot stage-budget
    route: exact row growth supplies `c * B`, while floating-point storage adds
    the local compact Householder component budget. -/
theorem coxHigham_storedPanelStep_active_entry_bound_of_exact_stage_budget_factor
    (fp : FPModel) (m n k : ℕ)
    (v : Fin m → ℝ) (β c B : ℝ) (AhatPrev : Fin m → Fin n → ℝ)
    (hm : gammaValid fp m) (r : Fin m) (j : Fin n)
    (hactive : k ≤ j.val)
    (hcompleted : j.val < k →
      ∀ i : Fin m, matMulVec m (householder m v β)
        (fun a => AhatPrev a j) i = AhatPrev i j)
    (hpivot : j.val = k →
      ∀ i : Fin m, k < i.val →
        matMulVec m (householder m v β) (fun a => AhatPrev a j) i = 0)
    (hexact :
      |matMulVec m (householder m v β) (fun a => AhatPrev a j) r| ≤
        c * B) :
    |fl_householderStoredPanelStep fp m n k v β AhatPrev r j| ≤
      c * B +
        householderCompactComponentBudget fp m v β (fun a => AhatPrev a j) r := by
  let exactUpdate : ℝ :=
    matMulVec m (householder m v β) (fun a => AhatPrev a j) r
  have hround :
      |fl_householderStoredPanelStep fp m n k v β AhatPrev r j -
          exactUpdate| ≤
        householderCompactComponentBudget fp m v β
          (fun a => AhatPrev a j) r := by
    simpa [exactUpdate] using
      fl_householderStoredPanelStep_active_entry_componentwise_error_bound
        fp m n k v β AhatPrev hm r j hactive hcompleted hpivot
  have htri :
      |fl_householderStoredPanelStep fp m n k v β AhatPrev r j| ≤
        |fl_householderStoredPanelStep fp m n k v β AhatPrev r j -
            exactUpdate| + |exactUpdate| := by
    have hsum :
        fl_householderStoredPanelStep fp m n k v β AhatPrev r j =
          (fl_householderStoredPanelStep fp m n k v β AhatPrev r j -
              exactUpdate) + exactUpdate := by
      ring
    calc
      |fl_householderStoredPanelStep fp m n k v β AhatPrev r j|
          = |(fl_householderStoredPanelStep fp m n k v β AhatPrev r j -
              exactUpdate) + exactUpdate| := by
              exact congrArg (fun z : ℝ => |z|) hsum
      _ ≤ |fl_householderStoredPanelStep fp m n k v β AhatPrev r j -
            exactUpdate| + |exactUpdate| := by
          exact abs_add_le
            (fl_householderStoredPanelStep fp m n k v β AhatPrev r j -
              exactUpdate) exactUpdate
  calc
    |fl_householderStoredPanelStep fp m n k v β AhatPrev r j|
        ≤ |fl_householderStoredPanelStep fp m n k v β AhatPrev r j -
            exactUpdate| + |exactUpdate| := htri
    _ ≤ householderCompactComponentBudget fp m v β
          (fun a => AhatPrev a j) r + c * B :=
          add_le_add hround (by simpa [exactUpdate] using hexact)
    _ = c * B +
        householderCompactComponentBudget fp m v β
          (fun a => AhatPrev a j) r := by ring

/-- Stored-panel sequence handoff from exact stage budgets.

    If each exact same-reflector stage is bounded by `c * B t`, and the next
    visible stage budget dominates this exact contribution plus the concrete
    compact Householder floating-point component budget, then the rounded stored
    panel entry is bounded by `B steps`. -/
theorem coxHigham_storedPanel_sequence_active_entry_bound_of_exact_stage_budgets_factor
    {m n : ℕ} (fp : FPModel) (steps : ℕ)
    (Ahat : ℕ → Fin m → Fin n → ℝ)
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ) (c : ℝ) (B : ℕ → ℝ)
    (hm : gammaValid fp m) (r : Fin m) (j : Fin n)
    (hinit : |Ahat 0 r j| ≤ B 0)
    (hstep : ∀ t : ℕ, t < steps →
      Ahat (t + 1) = fl_householderStoredPanelStep fp m n t (v t) (β t) (Ahat t))
    (hactive : ∀ t : ℕ, t < steps → t ≤ j.val)
    (hcompleted : ∀ t : ℕ, t < steps → j.val < t →
      ∀ i : Fin m, matMulVec m (householder m (v t) (β t))
        (fun a => Ahat t a j) i = Ahat t i j)
    (hpivot : ∀ t : ℕ, t < steps → j.val = t →
      ∀ i : Fin m, t < i.val →
        matMulVec m (householder m (v t) (β t)) (fun a => Ahat t a j) i = 0)
    (hbudget : ∀ t : ℕ, t < steps →
      c * B t +
          householderCompactComponentBudget fp m (v t) (β t)
            (fun a => Ahat t a j) r ≤
        B (t + 1))
    (hexact : ∀ t : ℕ, t < steps →
      |matMulVec m (householder m (v t) (β t)) (fun a => Ahat t a j) r| ≤
        c * B t) :
    |Ahat steps r j| ≤ B steps := by
  cases steps with
  | zero =>
      simpa using hinit
  | succ steps =>
      have ht : steps < steps + 1 := Nat.lt_succ_self steps
      rw [hstep steps ht]
      exact
        (coxHigham_storedPanelStep_active_entry_bound_of_exact_stage_budget_factor
          fp m n steps (v steps) (β steps) c (B steps) (Ahat steps)
          hm r j (hactive steps ht) (hcompleted steps ht) (hpivot steps ht)
          (hexact steps ht)).trans
          (hbudget steps ht)

/-- Stored-panel sequence handoff using the honest active-row Cox--Higham
    factor and explicit stage budgets. -/
theorem coxHigham_storedPanel_sequence_active_entry_bound_of_exact_active_stage_budgets
    {m n : ℕ} (fp : FPModel) (steps : ℕ)
    (Ahat : ℕ → Fin m → Fin n → ℝ)
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ) (B : ℕ → ℝ)
    (hm : gammaValid fp m) (r : Fin m) (j : Fin n)
    (hinit : |Ahat 0 r j| ≤ B 0)
    (hstep : ∀ t : ℕ, t < steps →
      Ahat (t + 1) = fl_householderStoredPanelStep fp m n t (v t) (β t) (Ahat t))
    (hactive : ∀ t : ℕ, t < steps → t ≤ j.val)
    (hcompleted : ∀ t : ℕ, t < steps → j.val < t →
      ∀ i : Fin m, matMulVec m (householder m (v t) (β t))
        (fun a => Ahat t a j) i = Ahat t i j)
    (hpivot : ∀ t : ℕ, t < steps → j.val = t →
      ∀ i : Fin m, t < i.val →
        matMulVec m (householder m (v t) (β t)) (fun a => Ahat t a j) i = 0)
    (hbudget : ∀ t : ℕ, t < steps →
      coxHighamActiveRowGrowthFactor m * B t +
          householderCompactComponentBudget fp m (v t) (β t)
            (fun a => Ahat t a j) r ≤
        B (t + 1))
    (hexact : ∀ t : ℕ, t < steps →
      |matMulVec m (householder m (v t) (β t)) (fun a => Ahat t a j) r| ≤
        coxHighamActiveRowGrowthFactor m * B t) :
    |Ahat steps r j| ≤ B steps := by
  exact
    coxHigham_storedPanel_sequence_active_entry_bound_of_exact_stage_budgets_factor
      fp steps Ahat v β (coxHighamActiveRowGrowthFactor m) B
      hm r j hinit hstep hactive hcompleted hpivot hbudget hexact

/-- One stored-panel step with the signed-pivot exact Cox--Higham stage fields.

    This composes the concrete floating-point stored-panel component budget
    with the exact signed-pivot active-row estimate.  The sorting/pivoting
    facts remain visible: positive active norm, column-pivot maximality,
    active row and column bounds, and the stored-panel completed/pivot-column
    convention. -/
theorem coxHigham_storedPanelStep_active_entry_bound_of_signed_pivot_stage_bounds
    (fp : FPModel) {m n : ℕ} (p row : Fin m) (pivotCol j : Fin n)
    (A : Fin m → Fin n → ℝ) (B : ℝ) (hm : gammaValid fp m)
    (hactiveRow : p.val ≤ row.val)
    (hB : 0 ≤ B)
    (hnorm :
      0 < householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol)
    (hpivotMax :
      ∀ l : Fin n, pivotCol.val ≤ l.val →
        householderTrailingColumnNorm2Sq (m := m) (n := n) p A l ≤
          householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol)
    (hj : pivotCol.val ≤ j.val)
    (hrowBound : ∀ l : Fin n, pivotCol.val ≤ l.val → |A row l| ≤ B)
    (hcolBound : ∀ i : Fin m, p.val ≤ i.val → |A i j| ≤ B)
    (hcompleted : j.val < pivotCol.val →
      ∀ i : Fin m, matMulVec m
        (householder m
          (householderTrailingActiveVector m p (fun r => A r pivotCol)
            (signedHouseholderAlpha
              (Real.sqrt
                (householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol))
              (A p pivotCol)))
          (householderBetaSpec m
            (householderTrailingActiveVector m p (fun r => A r pivotCol)
              (signedHouseholderAlpha
                (Real.sqrt
                  (householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol))
                (A p pivotCol)))))
        (fun a => A a j) i = A i j)
    (hpivot : j.val = pivotCol.val →
      ∀ i : Fin m, pivotCol.val < i.val →
        matMulVec m
          (householder m
            (householderTrailingActiveVector m p (fun r => A r pivotCol)
              (signedHouseholderAlpha
                (Real.sqrt
                  (householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol))
                (A p pivotCol)))
            (householderBetaSpec m
              (householderTrailingActiveVector m p (fun r => A r pivotCol)
                (signedHouseholderAlpha
                  (Real.sqrt
                    (householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol))
                  (A p pivotCol)))))
          (fun a => A a j) i = 0) :
    |fl_householderStoredPanelStep fp m n pivotCol.val
        (householderTrailingActiveVector m p (fun r => A r pivotCol)
          (signedHouseholderAlpha
            (Real.sqrt
              (householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol))
            (A p pivotCol)))
        (householderBetaSpec m
          (householderTrailingActiveVector m p (fun r => A r pivotCol)
            (signedHouseholderAlpha
              (Real.sqrt
                (householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol))
              (A p pivotCol))))
        A row j| ≤
      coxHighamActiveRowGrowthFactor m * B +
        householderCompactComponentBudget fp m
          (householderTrailingActiveVector m p (fun r => A r pivotCol)
            (signedHouseholderAlpha
              (Real.sqrt
                (householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol))
              (A p pivotCol)))
          (householderBetaSpec m
            (householderTrailingActiveVector m p (fun r => A r pivotCol)
              (signedHouseholderAlpha
                (Real.sqrt
                  (householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol))
                (A p pivotCol))))
          (fun a => A a j) row := by
  let v : Fin m → ℝ :=
    householderTrailingActiveVector m p (fun r => A r pivotCol)
      (signedHouseholderAlpha
        (Real.sqrt
          (householderTrailingColumnNorm2Sq (m := m) (n := n) p A pivotCol))
        (A p pivotCol))
  let β : ℝ := householderBetaSpec m v
  have hexact :
      |matMulVec m (householder m v β) (fun a => A a j) row| ≤
        coxHighamActiveRowGrowthFactor m * B := by
    simpa [v, β, exactSignedPivotHouseholderPanelStep] using
      coxHigham_exactSignedPivotPanelStep_active_entry_bound_of_stage_bounds
        p row pivotCol j A B hactiveRow hB hnorm hpivotMax hj hrowBound hcolBound
  simpa [v, β] using
    coxHigham_storedPanelStep_active_entry_bound_of_exact_stage_budget_factor
      fp m n pivotCol.val v β (coxHighamActiveRowGrowthFactor m) B A
      hm row j hj hcompleted hpivot hexact

/-- Rounded stored-panel active-block propagation under signed-pivot
Cox--Higham stage fields.

This is the stage-by-stage floating-point counterpart of the exact active-block
sequence theorem.  At each stage, the exact same-reflector signed-pivot update
is bounded by the Cox--Higham active-block estimate, and the next rounded
budget absorbs the concrete compact Householder component budget.  The
nonbreakdown and pivoting fields remain visible: a concrete sorted/pivoted loop
must still supply positive active pivot norm, pivot maximality, and the
completed/pivot-column storage equations. -/
theorem coxHigham_storedPanel_sequence_active_block_bound_of_signed_pivot_stage_bounds
    {m n : ℕ} (fp : FPModel) (steps : ℕ)
    (Ahat : ℕ → Fin m → Fin n → ℝ)
    (p : ℕ → Fin m) (pivotCol : ℕ → Fin n)
    (B : ℕ → ℝ) (hm : gammaValid fp m)
    (hinitBlock : ∀ i : Fin m, ∀ l : Fin n, |Ahat 0 i l| ≤ B 0)
    (hB : ∀ t : ℕ, t < steps → 0 ≤ B t)
    (hstep : ∀ t : ℕ, t < steps →
      Ahat (t + 1) =
        fl_householderStoredPanelStep fp m n (pivotCol t).val
          (signedPivotHouseholderVector m n (p t) (pivotCol t) (Ahat t))
          (signedPivotHouseholderBeta m n (p t) (pivotCol t) (Ahat t))
          (Ahat t))
    (hpMono : ∀ u t : ℕ, u ≤ t → t ≤ steps → (p u).val ≤ (p t).val)
    (hkMono : ∀ u t : ℕ, u ≤ t → t ≤ steps →
      (pivotCol u).val ≤ (pivotCol t).val)
    (hnorm : ∀ t : ℕ, t < steps →
      0 <
        householderTrailingColumnNorm2Sq
          (m := m) (n := n) (p t) (Ahat t) (pivotCol t))
    (hpivotMax : ∀ t : ℕ, t < steps →
      ∀ l : Fin n, (pivotCol t).val ≤ l.val →
        householderTrailingColumnNorm2Sq
            (m := m) (n := n) (p t) (Ahat t) l ≤
          householderTrailingColumnNorm2Sq
            (m := m) (n := n) (p t) (Ahat t) (pivotCol t))
    (hcompleted : ∀ t : ℕ, t < steps → ∀ j : Fin n,
      j.val < (pivotCol t).val →
        ∀ i : Fin m, matMulVec m
          (householder m
            (signedPivotHouseholderVector m n (p t) (pivotCol t) (Ahat t))
            (signedPivotHouseholderBeta m n (p t) (pivotCol t) (Ahat t)))
          (fun a => Ahat t a j) i = Ahat t i j)
    (hpivot : ∀ t : ℕ, t < steps → ∀ j : Fin n,
      j.val = (pivotCol t).val →
        ∀ i : Fin m, (pivotCol t).val < i.val →
          matMulVec m
            (householder m
              (signedPivotHouseholderVector m n (p t) (pivotCol t) (Ahat t))
              (signedPivotHouseholderBeta m n (p t) (pivotCol t) (Ahat t)))
            (fun a => Ahat t a j) i = 0)
    (hbudget : ∀ t : ℕ, t < steps → ∀ row : Fin m, ∀ l : Fin n,
      (p (t + 1)).val ≤ row.val →
        (pivotCol (t + 1)).val ≤ l.val →
          coxHighamActiveRowGrowthFactor m * B t +
              householderCompactComponentBudget fp m
                (signedPivotHouseholderVector m n (p t) (pivotCol t) (Ahat t))
                (signedPivotHouseholderBeta m n (p t) (pivotCol t) (Ahat t))
                (fun a => Ahat t a l) row ≤
            B (t + 1)) :
    ∀ t : ℕ, t ≤ steps →
      ∀ row : Fin m, (p t).val ≤ row.val →
        ∀ l : Fin n, (pivotCol t).val ≤ l.val →
          |Ahat t row l| ≤ B t := by
  intro t ht
  induction t with
  | zero =>
      intro row _hrow l _hl
      simpa using hinitBlock row l
  | succ t ih =>
      intro row hrow l hl
      have ht_lt : t < steps := Nat.lt_of_succ_le ht
      have ht_le : t ≤ steps := Nat.le_of_succ_le ht
      have hrow_prev : (p t).val ≤ row.val :=
        le_trans (hpMono t (t + 1) (Nat.le_succ t) ht) hrow
      have hcol_prev : (pivotCol t).val ≤ l.val :=
        le_trans (hkMono t (t + 1) (Nat.le_succ t) ht) hl
      have hblockPrev :
          ∀ a : Fin m, (p t).val ≤ a.val →
            ∀ b : Fin n, (pivotCol t).val ≤ b.val → |Ahat t a b| ≤ B t :=
        ih ht_le
      rw [hstep t ht_lt]
      have hstepBound :
          |fl_householderStoredPanelStep fp m n (pivotCol t).val
              (signedPivotHouseholderVector m n (p t) (pivotCol t) (Ahat t))
              (signedPivotHouseholderBeta m n (p t) (pivotCol t) (Ahat t))
              (Ahat t) row l| ≤
            coxHighamActiveRowGrowthFactor m * B t +
              householderCompactComponentBudget fp m
                (signedPivotHouseholderVector m n (p t) (pivotCol t) (Ahat t))
                (signedPivotHouseholderBeta m n (p t) (pivotCol t) (Ahat t))
                (fun a => Ahat t a l) row := by
        simpa [signedPivotHouseholderVector, signedPivotHouseholderBeta] using
          coxHigham_storedPanelStep_active_entry_bound_of_signed_pivot_stage_bounds
            fp (p t) row (pivotCol t) l (Ahat t) (B t) hm
            hrow_prev (hB t ht_lt) (hnorm t ht_lt) (hpivotMax t ht_lt)
            hcol_prev
            (fun l' hl' => hblockPrev row hrow_prev l' hl')
            (fun row' hrow' => hblockPrev row' hrow' l hcol_prev)
            (hcompleted t ht_lt l)
            (hpivot t ht_lt l)
      exact hstepBound.trans (hbudget t ht_lt row l hrow hl)

/-- Normwise forward-error bound for one stored panel column. -/
theorem fl_householderStoredPanelStep_column_forward_error_bound
    (fp : FPModel) (m n k : ℕ)
    (v : Fin m → ℝ) (β : ℝ) (A : Fin m → Fin n → ℝ)
    (hm : gammaValid fp m) (j : Fin n)
    (hcompleted : j.val < k →
      ∀ i : Fin m, matMulVec m (householder m v β)
        (fun a => A a j) i = A i j)
    (hpivot : j.val = k →
      ∀ i : Fin m, k < i.val →
        matMulVec m (householder m v β) (fun a => A a j) i = 0) :
    vecNorm2 (fun i : Fin m =>
        fl_householderStoredPanelStep fp m n k v β A i j -
          matMulVec m (householder m v β) (fun a => A a j) i) ≤
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m v β (fun a => A a j) i) := by
  exact vecNorm2_le_of_abs_le
    (fun i : Fin m =>
      fl_householderStoredPanelStep fp m n k v β A i j -
        matMulVec m (householder m v β) (fun a => A a j) i)
    (fun i : Fin m =>
      if j.val < k then 0
      else householderCompactComponentBudget fp m v β (fun a => A a j) i)
    (fl_householderStoredPanelStep_column_componentwise_error_bound
      fp m n k v β A hm j hcompleted hpivot)

/-- A stored rounded Householder panel/RHS step satisfies the source-faithful
    columnwise panel contract when the explicit stored-step budgets are
    dominated by `c`.

    The preservation and pivot-zeroing facts are explicit hypotheses; later QR
    loop theorems can discharge them from the trailing-reflector shape lemmas.
    No concentration or hidden stability event is assumed. -/
theorem fl_householderStoredPanelStep_HouseholderColumnwisePanelAppError_of_budget
    (fp : FPModel) (m n k : ℕ)
    (v : Fin m → ℝ) (β : ℝ) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) {c : ℝ}
    (horth : IsOrthogonal m (householder m v β))
    (hm : gammaValid fp m) (hc : 0 ≤ c)
    (hcompleted : ∀ j : Fin n, j.val < k →
      ∀ i : Fin m, matMulVec m (householder m v β)
        (fun a => A a j) i = A i j)
    (hpivot : ∀ j : Fin n, j.val = k →
      ∀ i : Fin m, k < i.val →
        matMulVec m (householder m v β) (fun a => A a j) i = 0)
    (hrhs_prefix : ∀ i : Fin m, i.val < k →
      matMulVec m (householder m v β) b i = b i)
    (hA_budget : ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m v β (fun a => A a j) i) ≤
        c * vecNorm2 (fun i : Fin m => A i j))
    (hb_budget :
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m v β b i) ≤
        c * vecNorm2 b) :
    HouseholderColumnwisePanelAppError m n (householder m v β) A
      (fl_householderStoredPanelStep fp m n k v β A)
      b (fl_householderStoredRhsStep fp m k v β b) c := by
  apply HouseholderColumnwisePanelAppError.of_forward_errors
  · exact horth
  · exact hc
  · intro j
    exact le_trans
      (fl_householderStoredPanelStep_column_forward_error_bound
        fp m n k v β A hm j (hcompleted j) (hpivot j))
      (hA_budget j)
  · exact le_trans
      (fl_householderStoredRhsStep_forward_error_bound
        fp m k v β b hm hrhs_prefix)
      hb_budget

/-- Normwise deterministic forward-error bound for compact Householder
    application, obtained directly from the componentwise budget. -/
theorem fl_householderApplyCompact_forward_error_bound
    (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) (b : Fin n → ℝ)
    (hn : gammaValid fp n) :
    vecNorm2 (fun i : Fin n =>
        fl_householderApplyCompact fp n v β b i -
          matMulVec n (householder n v β) b i) ≤
      vecNorm2 (fun i : Fin n =>
        householderCompactComponentBudget fp n v β b i) := by
  exact vecNorm2_le_of_abs_le
    (fun i : Fin n =>
      fl_householderApplyCompact fp n v β b i -
        matMulVec n (householder n v β) b i)
    (fun i : Fin n =>
      householderCompactComponentBudget fp n v β b i)
    (fl_householderApplyCompact_componentwise_error_bound fp n v β b hn)

/-- Compact rounded Householder application satisfies the existing
    `HouseholderAppError` contract whenever the explicit deterministic budget
    is dominated by `c ‖b‖₂`.

    The side condition is not a hidden concentration or stability hypothesis:
    it is the visible deterministic conversion from the componentwise arithmetic
    budget above to the repository's relative backward-error constant. -/
theorem fl_householderApplyCompact_HouseholderAppError_of_budget
    (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (β : ℝ) (b : Fin n → ℝ)
    {c : ℝ} (horth : IsOrthogonal n (householder n v β))
    (hn : gammaValid fp n) (hc : 0 ≤ c)
    (hbudget :
      vecNorm2 (fun i : Fin n =>
        householderCompactComponentBudget fp n v β b i) ≤ c * vecNorm2 b) :
    HouseholderAppError n (householder n v β) b
      (fl_householderApplyCompact fp n v β b) c := by
  exact HouseholderAppError.of_forward_error n (householder n v β) b
    (fl_householderApplyCompact fp n v β b) horth hc
    (le_trans
      (fl_householderApplyCompact_forward_error_bound fp n v β b hn)
      hbudget)

/-- Columnwise panel version of compact rounded Householder application.
    Each panel column and the right-hand side may use the same visible
    deterministic budget domination constant `c`. -/
theorem fl_householderApplyCompactPanel_HouseholderColumnwisePanelAppError_of_budget
    (fp : FPModel) (m n : ℕ)
    (v : Fin m → ℝ) (β : ℝ) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) {c : ℝ}
    (horth : IsOrthogonal m (householder m v β))
    (hm : gammaValid fp m) (hc : 0 ≤ c)
    (hA_budget : ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        householderCompactComponentBudget fp m v β (fun a => A a j) i) ≤
        c * vecNorm2 (fun i : Fin m => A i j))
    (hb_budget :
      vecNorm2 (fun i : Fin m =>
        householderCompactComponentBudget fp m v β b i) ≤ c * vecNorm2 b) :
    HouseholderColumnwisePanelAppError m n (householder m v β) A
      (fl_householderApplyCompactPanel fp m n v β A)
      b (fl_householderApplyCompact fp m v β b) c := by
  apply HouseholderColumnwisePanelAppError.of_vector_applications
  · intro j
    exact fl_householderApplyCompact_HouseholderAppError_of_budget fp m v β
      (fun i : Fin m => A i j) horth hm hc (hA_budget j)
  · exact fl_householderApplyCompact_HouseholderAppError_of_budget fp m v β
      b horth hm hc hb_budget

/-- Forward-error bound for explicit-matrix Householder application.

    This is the normwise version of the existing componentwise `fl_matVec`
    error bound:
    `‖fl(P b) - P b‖₂ ≤ γ_m ‖ |P| |b| ‖₂ ≤ γ_m ‖ |P| ‖_F ‖b‖₂`.
    It is a concrete rounded application theorem, but it is not yet the compact
    Householder dot-scale-subtract implementation. -/
theorem fl_householderApplyExplicit_forward_error_bound
    (fp : FPModel) (n : ℕ)
    (P : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hn : gammaValid fp n) :
    vecNorm2 (fun i : Fin n =>
        fl_householderApplyExplicit fp n P b i - matMulVec n P b i) ≤
      gamma fp n * frobNorm (fun i j : Fin n => |P i j|) * vecNorm2 b := by
  let err : Fin n → ℝ :=
    fun i => fl_householderApplyExplicit fp n P b i - matMulVec n P b i
  let rowAbs : Fin n → ℝ :=
    matMulVec n (fun i j : Fin n => |P i j|) (fun j => |b j|)
  have hcomp : ∀ i : Fin n, |err i| ≤ gamma fp n * rowAbs i := by
    intro i
    have h := matVec_error_bound fp n n P b hn i
    simpa [err, rowAbs, fl_householderApplyExplicit, matMulVec] using h
  have hvec :
      vecNorm2 err ≤ vecNorm2 (fun i : Fin n => gamma fp n * rowAbs i) :=
    vecNorm2_le_of_abs_le err (fun i : Fin n => gamma fp n * rowAbs i) hcomp
  have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hscale :
      vecNorm2 (fun i : Fin n => gamma fp n * rowAbs i) =
        gamma fp n * vecNorm2 rowAbs := by
    rw [vecNorm2_smul, abs_of_nonneg hγ]
  have hrow :
      vecNorm2 rowAbs ≤
        frobNorm (fun i j : Fin n => |P i j|) *
          vecNorm2 (fun j : Fin n => |b j|) := by
    simpa [rowAbs] using
      (vecNorm2_matMulVec_le_frobNorm_mul
        (n := n) (fun i j : Fin n => |P i j|) (fun j : Fin n => |b j|))
  calc
    vecNorm2 (fun i : Fin n =>
        fl_householderApplyExplicit fp n P b i - matMulVec n P b i)
        = vecNorm2 err := rfl
    _ ≤ vecNorm2 (fun i : Fin n => gamma fp n * rowAbs i) := hvec
    _ = gamma fp n * vecNorm2 rowAbs := hscale
    _ ≤ gamma fp n *
          (frobNorm (fun i j : Fin n => |P i j|) *
            vecNorm2 (fun j : Fin n => |b j|)) :=
        mul_le_mul_of_nonneg_left hrow hγ
    _ = gamma fp n * frobNorm (fun i j : Fin n => |P i j|) *
          vecNorm2 b := by
        rw [vecNorm2_abs]
        ring

/-- Explicit-matrix floating-point Householder application satisfies the
    `HouseholderAppError` backward-error contract. -/
theorem fl_householderApplyExplicit_HouseholderAppError
    (fp : FPModel) (n : ℕ)
    (P : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (horth : IsOrthogonal n P) (hn : gammaValid fp n) :
    HouseholderAppError n P b (fl_householderApplyExplicit fp n P b)
      (gamma fp n * frobNorm (fun i j : Fin n => |P i j|)) := by
  have hc :
      0 ≤ gamma fp n * frobNorm (fun i j : Fin n => |P i j|) :=
    mul_nonneg (gamma_nonneg fp hn) (frobNorm_nonneg _)
  exact HouseholderAppError.of_forward_error n P b
    (fl_householderApplyExplicit fp n P b) horth hc
    (by
      simpa [mul_assoc] using
        fl_householderApplyExplicit_forward_error_bound fp n P b hn)

/-- Columnwise panel version of explicit-matrix floating-point Householder
    application.  Each column gets its own admissible perturbation, matching the
    source-faithful columnwise contract used by the rectangular QR route. -/
theorem fl_householderApplyExplicitPanel_HouseholderColumnwisePanelAppError
    (fp : FPModel) (m n : ℕ)
    (P : Fin m → Fin m → ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (horth : IsOrthogonal m P) (hm : gammaValid fp m) :
    HouseholderColumnwisePanelAppError m n P A
      (fl_householderApplyExplicitPanel fp m n P A)
      b (fl_householderApplyExplicit fp m P b)
      (gamma fp m * frobNorm (fun i j : Fin m => |P i j|)) := by
  apply HouseholderColumnwisePanelAppError.of_vector_applications
  · intro j
    exact fl_householderApplyExplicit_HouseholderAppError fp m P
      (fun i : Fin m => A i j) horth hm
  · exact fl_householderApplyExplicit_HouseholderAppError fp m P b horth hm

end NumStability
