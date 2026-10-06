-- Algorithms/QR/GivensMatrixStep.lean
--
-- Matrix-column bridge for concrete Givens rotation application.

import NumStability.Algorithms.QR.GivensSpec

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-- Apply one computed Givens rotation to every column of a square matrix.

    The coefficients are computed once from the supplied two-vector
    `(xi,xj)` by `fl_givensC`/`fl_givensS`, and each output column is then
    computed by the rounded vector kernel `fl_givensApply`. -/
noncomputable def fl_givensApplyMatrix (fp : FPModel) (n : ℕ)
    (p q : Fin n) (xi xj : ℝ) (A : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    fl_givensApply fp n p q
      (fl_givensC fp xi xj) (fl_givensS fp xi xj) (fun k => A k j) i

/-- Apply one computed Givens rotation to every column of an `m × cols`
    rectangular panel. -/
noncomputable def fl_givensApplyMatrixRect (fp : FPModel) (m cols : ℕ)
    (p q : Fin m) (xi xj : ℝ) (A : Fin m → Fin cols → ℝ) :
    Fin m → Fin cols → ℝ :=
  fun i j =>
    fl_givensApply fp m p q
      (fl_givensC fp xi xj) (fl_givensS fp xi xj) (fun k => A k j) i

/-- Concrete square Givens column step.

    The two-vector used to construct the rotation is taken from the current
    matrix column: `(A p col, A q col)`.  This is the local operation used by
    a future full Givens QR annihilation schedule. -/
noncomputable def fl_givensColumnStepMatrix (fp : FPModel) (n : ℕ)
    (p q col : Fin n) (A : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fl_givensApplyMatrix fp n p q (A p col) (A q col) A

/-- Concrete rectangular-panel Givens column step. -/
noncomputable def fl_givensColumnStepMatrixRect (fp : FPModel) (m cols : ℕ)
    (p q : Fin m) (col : Fin cols) (A : Fin m → Fin cols → ℝ) :
    Fin m → Fin cols → ℝ :=
  fl_givensApplyMatrixRect fp m cols p q (A p col) (A q col) A

/-- Columnwise matrix-step form for one Givens rotation.

    Each output column is represented as `(G + ΔG_j) A[:,j]`; the perturbation
    is column-dependent because each vector application performs separate
    rounded operations. -/
structure ColumnwiseGivensStepError (n : ℕ)
    (G : Fin n → Fin n → ℝ) (A A_hat : Fin n → Fin n → ℝ)
    (c : ℝ) : Prop where
  /-- The exact Givens rotation is orthogonal. -/
  orth : IsOrthogonal n G
  /-- Every computed output column has a column-dependent perturbation. -/
  pert : ∀ j : Fin n, ∃ ΔGj : Fin n → Fin n → ℝ,
    frobNorm ΔGj ≤ c ∧
    ∀ i : Fin n, A_hat i j =
      matMulVec n (fun a b => G a b + ΔGj a b) (fun k => A k j) i

/-- Rectangular panel form of `ColumnwiseGivensStepError`. -/
structure ColumnwiseGivensStepErrorRect (m cols : ℕ)
    (G : Fin m → Fin m → ℝ) (A A_hat : Fin m → Fin cols → ℝ)
    (c : ℝ) : Prop where
  /-- The exact Givens rotation is orthogonal. -/
  orth : IsOrthogonal m G
  /-- Every computed output column has a column-dependent perturbation. -/
  pert : ∀ j : Fin cols, ∃ ΔGj : Fin m → Fin m → ℝ,
    frobNorm ΔGj ≤ c ∧
    ∀ i : Fin m, A_hat i j =
      matMulVec m (fun a b => G a b + ΔGj a b) (fun k => A k j) i

/-- Rectangular panel form of `ColumnwiseGivensStepError` with the local
    pair-support information retained for every column perturbation. -/
structure SparseColumnwiseGivensStepErrorRect (m cols : ℕ)
    (p q : Fin m) (G : Fin m → Fin m → ℝ)
    (A A_hat : Fin m → Fin cols → ℝ) (c : ℝ) : Prop where
  /-- The exact Givens rotation is orthogonal. -/
  orth : IsOrthogonal m G
  /-- Every computed output column has a column-dependent pair-supported
      perturbation. -/
  pert : ∀ j : Fin cols, ∃ ΔGj : Fin m → Fin m → ℝ,
    frobNorm ΔGj ≤ c ∧
    PairBlockSupported p q ΔGj ∧
    ∀ i : Fin m, A_hat i j =
      matMulVec m (fun a b => G a b + ΔGj a b) (fun k => A k j) i

/-- Forget the support information from a sparse rectangular Givens panel
    step. -/
theorem SparseColumnwiseGivensStepErrorRect.to_columnwise {m cols : ℕ}
    {p q : Fin m} {G : Fin m → Fin m → ℝ}
    {A A_hat : Fin m → Fin cols → ℝ} {c : ℝ}
    (hstep : SparseColumnwiseGivensStepErrorRect m cols p q G A A_hat c) :
    ColumnwiseGivensStepErrorRect m cols G A A_hat c := by
  refine ⟨hstep.orth, ?_⟩
  intro j
  obtain ⟨ΔGj, hΔGj, _hsupp, hcol⟩ := hstep.pert j
  exact ⟨ΔGj, hΔGj, hcol⟩

/-- If the two affected entries in a panel column are zero, an exact Givens
    row rotation leaves that column unchanged. -/
theorem givensRotation_matMulRect_pair_zero_col (m cols : ℕ)
    (p q : Fin m) (c s : ℝ) (B : Fin m → Fin cols → ℝ)
    (j : Fin cols) (hpq : p ≠ q)
    (hbp : B p j = 0) (hbq : B q j = 0) :
    ∀ i : Fin m,
      matMulRect m m cols (givensRotation m p q c s) B i j = B i j := by
  intro i
  simpa [matMulRect, matMulVec] using
    givensRotation_matMulVec_pair_zero m p q c s (fun k => B k j)
      hpq hbp hbq i

/-- The exact Givens rotation constructed from a panel column zeros the target
    row in that column. -/
theorem givensRotation_constructed_matMulRect_target_zero (m cols : ℕ)
    (p q : Fin m) (col : Fin cols) (B : Fin m → Fin cols → ℝ)
    (hpq : p ≠ q) :
    matMulRect m m cols
      (givensRotation m p q (givensC (B p col) (B q col))
        (givensS (B p col) (B q col))) B q col = 0 := by
  simpa [matMulRect, matMulVec] using
    givensRotation_constructed_matMulVec_q_zero m p q
      (B p col) (B q col) (fun k => B k col) hpq rfl rfl

/-- Package per-column `GivensAppError` facts as a square matrix-step error. -/
theorem columnwiseGivensStepError_of_appError (n : ℕ)
    (G : Fin n → Fin n → ℝ) (A A_hat : Fin n → Fin n → ℝ) (c : ℝ)
    (hG : IsOrthogonal n G)
    (hcols : ∀ j : Fin n,
      GivensAppError n G (fun i => A i j) (fun i => A_hat i j) c) :
    ColumnwiseGivensStepError n G A A_hat c := by
  refine ⟨hG, ?_⟩
  intro j
  exact (hcols j).pert

/-- Package per-column `GivensAppError` facts as a rectangular panel-step
    error. -/
theorem columnwiseGivensStepErrorRect_of_appError (m cols : ℕ)
    (G : Fin m → Fin m → ℝ) (A A_hat : Fin m → Fin cols → ℝ) (c : ℝ)
    (hG : IsOrthogonal m G)
    (hcols : ∀ j : Fin cols,
      GivensAppError m G (fun i => A i j) (fun i => A_hat i j) c) :
    ColumnwiseGivensStepErrorRect m cols G A A_hat c := by
  refine ⟨hG, ?_⟩
  intro j
  exact (hcols j).pert

/-- Package per-column sparse `GivensAppError` facts as a rectangular panel
    step. -/
theorem sparseColumnwiseGivensStepErrorRect_of_appError (m cols : ℕ)
    (p q : Fin m) (G : Fin m → Fin m → ℝ)
    (A A_hat : Fin m → Fin cols → ℝ) (c : ℝ)
    (hG : IsOrthogonal m G)
    (hcols : ∀ j : Fin cols,
      SparseGivensAppError m p q G (fun i => A i j)
        (fun i => A_hat i j) c) :
    SparseColumnwiseGivensStepErrorRect m cols p q G A A_hat c := by
  refine ⟨hG, ?_⟩
  intro j
  exact (hcols j).pert

/-- Concrete computed-coefficient Givens application satisfies the square
    columnwise matrix-step contract. -/
theorem fl_givensApply_computed_matrix_step_error (fp : FPModel) (n : ℕ)
    (p q : Fin n) (xi xj : ℝ) (A : Fin n → Fin n → ℝ)
    (hpq : p ≠ q) (h : xi ^ 2 + xj ^ 2 ≠ 0)
    (hvalid : gammaValid fp 8) :
    ColumnwiseGivensStepError n
      (givensRotation n p q (givensC xi xj) (givensS xi xj))
      A
      (fl_givensApplyMatrix fp n p q xi xj A)
      (gamma fp 8 *
        frobNorm (givensRotation n p q (givensC xi xj) (givensS xi xj))) := by
  let G := givensRotation n p q (givensC xi xj) (givensS xi xj)
  have hG : IsOrthogonal n G := by
    simpa [G] using givensRotation_constructed_orthogonal n p q xi xj hpq h
  apply columnwiseGivensStepError_of_appError n G
  · exact hG
  · intro j
    simpa [G, fl_givensApplyMatrix] using
      fl_givensApply_computed_app_error_conservative fp n p q xi xj
        (fun k => A k j) hpq h hvalid

/-- Concrete computed-coefficient Givens application satisfies the rectangular
    columnwise matrix-step contract. -/
theorem fl_givensApply_computed_matrix_step_error_rect (fp : FPModel)
    (m cols : ℕ)
    (p q : Fin m) (xi xj : ℝ) (A : Fin m → Fin cols → ℝ)
    (hpq : p ≠ q) (h : xi ^ 2 + xj ^ 2 ≠ 0)
    (hvalid : gammaValid fp 8) :
    ColumnwiseGivensStepErrorRect m cols
      (givensRotation m p q (givensC xi xj) (givensS xi xj))
      A
      (fl_givensApplyMatrixRect fp m cols p q xi xj A)
      (gamma fp 8 *
        frobNorm (givensRotation m p q (givensC xi xj) (givensS xi xj))) := by
  let G := givensRotation m p q (givensC xi xj) (givensS xi xj)
  have hG : IsOrthogonal m G := by
    simpa [G] using givensRotation_constructed_orthogonal m p q xi xj hpq h
  apply columnwiseGivensStepErrorRect_of_appError m cols G
  · exact hG
  · intro j
    simpa [G, fl_givensApplyMatrixRect] using
      fl_givensApply_computed_app_error_conservative fp m p q xi xj
        (fun k => A k j) hpq h hvalid

/-- Concrete computed-coefficient Givens application satisfies the rectangular
    sparse columnwise matrix-step contract. -/
theorem fl_givensApply_computed_matrix_sparse_step_error_rect (fp : FPModel)
    (m cols : ℕ)
    (p q : Fin m) (xi xj : ℝ) (A : Fin m → Fin cols → ℝ)
    (hpq : p ≠ q) (h : xi ^ 2 + xj ^ 2 ≠ 0)
    (hvalid : gammaValid fp 8) :
    SparseColumnwiseGivensStepErrorRect m cols p q
      (givensRotation m p q (givensC xi xj) (givensS xi xj))
      A
      (fl_givensApplyMatrixRect fp m cols p q xi xj A)
      (gamma fp 8 *
        frobNorm (givensRotation m p q (givensC xi xj) (givensS xi xj))) := by
  let G := givensRotation m p q (givensC xi xj) (givensS xi xj)
  have hG : IsOrthogonal m G := by
    simpa [G] using givensRotation_constructed_orthogonal m p q xi xj hpq h
  apply sparseColumnwiseGivensStepErrorRect_of_appError m cols p q G
  · exact hG
  · intro j
    simpa [G, fl_givensApplyMatrixRect] using
      fl_givensApply_computed_sparse_app_error_conservative fp m p q xi xj
        (fun k => A k j) hpq h hvalid

/-- Concrete square Givens column step satisfies the columnwise matrix-step
    contract, with coefficients computed from the current matrix column. -/
theorem fl_givensColumnStep_matrix_step_error (fp : FPModel) (n : ℕ)
    (p q col : Fin n) (A : Fin n → Fin n → ℝ)
    (hpq : p ≠ q) (h : A p col ^ 2 + A q col ^ 2 ≠ 0)
    (hvalid : gammaValid fp 8) :
    ColumnwiseGivensStepError n
      (givensRotation n p q (givensC (A p col) (A q col))
        (givensS (A p col) (A q col)))
      A
      (fl_givensColumnStepMatrix fp n p q col A)
      (gamma fp 8 *
        frobNorm (givensRotation n p q
          (givensC (A p col) (A q col))
          (givensS (A p col) (A q col)))) := by
  simpa [fl_givensColumnStepMatrix] using
    fl_givensApply_computed_matrix_step_error fp n p q
      (A p col) (A q col) A hpq h hvalid

/-- Concrete rectangular-panel Givens column step satisfies the columnwise
    matrix-step contract, with coefficients computed from the current panel
    column. -/
theorem fl_givensColumnStep_matrix_step_error_rect (fp : FPModel)
    (m cols : ℕ)
    (p q : Fin m) (col : Fin cols) (A : Fin m → Fin cols → ℝ)
    (hpq : p ≠ q) (h : A p col ^ 2 + A q col ^ 2 ≠ 0)
    (hvalid : gammaValid fp 8) :
    ColumnwiseGivensStepErrorRect m cols
      (givensRotation m p q (givensC (A p col) (A q col))
        (givensS (A p col) (A q col)))
      A
      (fl_givensColumnStepMatrixRect fp m cols p q col A)
      (gamma fp 8 *
        frobNorm (givensRotation m p q
          (givensC (A p col) (A q col))
          (givensS (A p col) (A q col)))) := by
  simpa [fl_givensColumnStepMatrixRect] using
    fl_givensApply_computed_matrix_step_error_rect fp m cols p q
      (A p col) (A q col) A hpq h hvalid

/-- Residual form of a square columnwise Givens matrix step. -/
theorem ColumnwiseGivensStepError.column_residual {n : ℕ}
    {G A A_hat : Fin n → Fin n → ℝ} {c : ℝ}
    (hstep : ColumnwiseGivensStepError n G A A_hat c) :
    ∀ j : Fin n, ∃ ΔGj : Fin n → Fin n → ℝ,
      frobNorm ΔGj ≤ c ∧
      ∀ i : Fin n, A_hat i j =
        matMul n G A i j +
          matMulVec n ΔGj (fun k => A k j) i := by
  intro j
  obtain ⟨ΔGj, hΔGj, hcol⟩ := hstep.pert j
  refine ⟨ΔGj, hΔGj, ?_⟩
  intro i
  rw [hcol i]
  unfold matMulVec matMul
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Matrix residual form of a square columnwise Givens step. -/
theorem ColumnwiseGivensStepError.exists_residual_matrix {n : ℕ}
    {G A A_hat : Fin n → Fin n → ℝ} {c : ℝ}
    (hstep : ColumnwiseGivensStepError n G A A_hat c) :
    ∃ E : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, A_hat i j = matMul n G A i j + E i j) ∧
      ∀ j : Fin n, ∃ ΔGj : Fin n → Fin n → ℝ,
        frobNorm ΔGj ≤ c ∧
        ∀ i : Fin n, E i j =
          matMulVec n ΔGj (fun k => A k j) i := by
  classical
  let hres := hstep.column_residual
  let ΔG : Fin n → Fin n → Fin n → ℝ := fun j => Classical.choose (hres j)
  let E : Fin n → Fin n → ℝ :=
    fun i j => matMulVec n (ΔG j) (fun k => A k j) i
  refine ⟨E, ?_, ?_⟩
  · intro i j
    have hspec := Classical.choose_spec (hres j)
    exact hspec.2 i
  · intro j
    have hspec := Classical.choose_spec (hres j)
    refine ⟨ΔG j, hspec.1, ?_⟩
    intro i
    rfl

/-- Normwise residual consequence of a square columnwise Givens step. -/
theorem ColumnwiseGivensStepError.exists_residual_matrix_bound {n : ℕ}
    {G A A_hat : Fin n → Fin n → ℝ} {c : ℝ}
    (hstep : ColumnwiseGivensStepError n G A A_hat c)
    (hc : 0 ≤ c) :
    ∃ E : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, A_hat i j = matMul n G A i j + E i j) ∧
      frobNorm E ≤ c * frobNorm A := by
  obtain ⟨E, hEA, hcol⟩ := hstep.exists_residual_matrix
  exact ⟨E, hEA, frobNorm_columnwise_matMulVec_le E A hc hcol⟩

/-- Residual form of a rectangular columnwise Givens panel step. -/
theorem ColumnwiseGivensStepErrorRect.column_residual {m cols : ℕ}
    {G : Fin m → Fin m → ℝ} {A A_hat : Fin m → Fin cols → ℝ} {c : ℝ}
    (hstep : ColumnwiseGivensStepErrorRect m cols G A A_hat c) :
    ∀ j : Fin cols, ∃ ΔGj : Fin m → Fin m → ℝ,
      frobNorm ΔGj ≤ c ∧
      ∀ i : Fin m, A_hat i j =
        matMulRect m m cols G A i j +
          matMulVec m ΔGj (fun k => A k j) i := by
  intro j
  obtain ⟨ΔGj, hΔGj, hcol⟩ := hstep.pert j
  refine ⟨ΔGj, hΔGj, ?_⟩
  intro i
  rw [hcol i]
  unfold matMulVec matMulRect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Residual form of a sparse rectangular columnwise Givens panel step. -/
theorem SparseColumnwiseGivensStepErrorRect.column_residual {m cols : ℕ}
    {p q : Fin m} {G : Fin m → Fin m → ℝ}
    {A A_hat : Fin m → Fin cols → ℝ} {c : ℝ}
    (hstep : SparseColumnwiseGivensStepErrorRect m cols p q G A A_hat c) :
    ∀ j : Fin cols, ∃ ΔGj : Fin m → Fin m → ℝ,
      frobNorm ΔGj ≤ c ∧
      PairBlockSupported p q ΔGj ∧
      ∀ i : Fin m, A_hat i j =
        matMulRect m m cols G A i j +
          matMulVec m ΔGj (fun k => A k j) i := by
  intro j
  obtain ⟨ΔGj, hΔGj, hsupp, hcol⟩ := hstep.pert j
  refine ⟨ΔGj, hΔGj, hsupp, ?_⟩
  intro i
  rw [hcol i]
  unfold matMulVec matMulRect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Matrix residual form of a rectangular columnwise Givens panel step. -/
theorem ColumnwiseGivensStepErrorRect.exists_residual_matrix {m cols : ℕ}
    {G : Fin m → Fin m → ℝ} {A A_hat : Fin m → Fin cols → ℝ} {c : ℝ}
    (hstep : ColumnwiseGivensStepErrorRect m cols G A A_hat c) :
    ∃ E : Fin m → Fin cols → ℝ,
      (∀ (i : Fin m) (j : Fin cols),
        A_hat i j = matMulRect m m cols G A i j + E i j) ∧
      ∀ j : Fin cols, ∃ ΔGj : Fin m → Fin m → ℝ,
        frobNorm ΔGj ≤ c ∧
        ∀ i : Fin m, E i j =
          matMulVec m ΔGj (fun k => A k j) i := by
  classical
  let hres := hstep.column_residual
  let ΔG : Fin cols → Fin m → Fin m → ℝ := fun j => Classical.choose (hres j)
  let E : Fin m → Fin cols → ℝ :=
    fun i j => matMulVec m (ΔG j) (fun k => A k j) i
  refine ⟨E, ?_, ?_⟩
  · intro i j
    have hspec := Classical.choose_spec (hres j)
    exact hspec.2 i
  · intro j
    have hspec := Classical.choose_spec (hres j)
    refine ⟨ΔG j, hspec.1, ?_⟩
    intro i
    rfl

/-- Normwise residual consequence of a rectangular columnwise Givens step. -/
theorem ColumnwiseGivensStepErrorRect.exists_residual_matrix_bound
    {m cols : ℕ}
    {G : Fin m → Fin m → ℝ} {A A_hat : Fin m → Fin cols → ℝ} {c : ℝ}
    (hstep : ColumnwiseGivensStepErrorRect m cols G A A_hat c)
    (hc : 0 ≤ c) :
    ∃ E : Fin m → Fin cols → ℝ,
      (∀ (i : Fin m) (j : Fin cols),
        A_hat i j = matMulRect m m cols G A i j + E i j) ∧
      frobNorm E ≤ c * frobNorm A := by
  obtain ⟨E, hEA, hcol⟩ := hstep.exists_residual_matrix
  exact ⟨E, hEA, frobNorm_columnwise_matMulVec_le_rect E A hc hcol⟩

/-- Matrix residual form of a sparse rectangular columnwise Givens panel
    step, retaining the per-column support witnesses. -/
theorem SparseColumnwiseGivensStepErrorRect.exists_residual_matrix
    {m cols : ℕ}
    {p q : Fin m} {G : Fin m → Fin m → ℝ}
    {A A_hat : Fin m → Fin cols → ℝ} {c : ℝ}
    (hstep : SparseColumnwiseGivensStepErrorRect m cols p q G A A_hat c) :
    ∃ E : Fin m → Fin cols → ℝ,
      (∀ (i : Fin m) (j : Fin cols),
        A_hat i j = matMulRect m m cols G A i j + E i j) ∧
      ∀ j : Fin cols, ∃ ΔGj : Fin m → Fin m → ℝ,
        frobNorm ΔGj ≤ c ∧
        PairBlockSupported p q ΔGj ∧
        ∀ i : Fin m, E i j =
          matMulVec m ΔGj (fun k => A k j) i := by
  classical
  let hres := hstep.column_residual
  let ΔG : Fin cols → Fin m → Fin m → ℝ := fun j => Classical.choose (hres j)
  let E : Fin m → Fin cols → ℝ :=
    fun i j => matMulVec m (ΔG j) (fun k => A k j) i
  refine ⟨E, ?_, ?_⟩
  · intro i j
    have hspec := Classical.choose_spec (hres j)
    exact hspec.2.2 i
  · intro j
    have hspec := Classical.choose_spec (hres j)
    refine ⟨ΔG j, hspec.1, hspec.2.1, ?_⟩
    intro i
    rfl

/-- Normwise residual consequence of a sparse rectangular columnwise Givens
    panel step, retaining the per-column support witnesses. -/
theorem SparseColumnwiseGivensStepErrorRect.exists_residual_matrix_bound
    {m cols : ℕ}
    {p q : Fin m} {G : Fin m → Fin m → ℝ}
    {A A_hat : Fin m → Fin cols → ℝ} {c : ℝ}
    (hstep : SparseColumnwiseGivensStepErrorRect m cols p q G A A_hat c)
    (hc : 0 ≤ c) :
    ∃ E : Fin m → Fin cols → ℝ,
      (∀ (i : Fin m) (j : Fin cols),
        A_hat i j = matMulRect m m cols G A i j + E i j) ∧
      frobNorm E ≤ c * frobNorm A ∧
      ∀ j : Fin cols, ∃ ΔGj : Fin m → Fin m → ℝ,
        frobNorm ΔGj ≤ c ∧
        PairBlockSupported p q ΔGj ∧
        ∀ i : Fin m, E i j =
          matMulVec m ΔGj (fun k => A k j) i := by
  obtain ⟨E, hEA, hcol⟩ := hstep.exists_residual_matrix
  have hcol_plain :
      ∀ j : Fin cols, ∃ ΔGj : Fin m → Fin m → ℝ,
        frobNorm ΔGj ≤ c ∧
        ∀ i : Fin m, E i j =
          matMulVec m ΔGj (fun k => A k j) i := by
    intro j
    obtain ⟨ΔGj, hΔGj, _hsupp, hΔcol⟩ := hcol j
    exact ⟨ΔGj, hΔGj, hΔcol⟩
  exact ⟨E, hEA, frobNorm_columnwise_matMulVec_le_rect E A hc hcol_plain, hcol⟩

/-- Normwise residual consequence of a sparse rectangular columnwise Givens
    panel step, as a matrix residual whose nonzero rows are contained in the
    active row pair. -/
theorem SparseColumnwiseGivensStepErrorRect.exists_residual_matrix_bound_row_support
    {m cols : ℕ}
    {p q : Fin m} {G : Fin m → Fin m → ℝ}
    {A A_hat : Fin m → Fin cols → ℝ} {c : ℝ}
    (hstep : SparseColumnwiseGivensStepErrorRect m cols p q G A A_hat c)
    (hc : 0 ≤ c) :
    ∃ E : Fin m → Fin cols → ℝ,
      (∀ (i : Fin m) (j : Fin cols),
        A_hat i j = matMulRect m m cols G A i j + E i j) ∧
      frobNorm E ≤ c * frobNorm A ∧
      ∀ (i : Fin m) (j : Fin cols), i ≠ p → i ≠ q → E i j = 0 := by
  obtain ⟨E, hEA, hEbound, hcol⟩ :=
    hstep.exists_residual_matrix_bound hc
  refine ⟨E, hEA, hEbound, ?_⟩
  intro i j hip hiq
  obtain ⟨ΔGj, _hΔGj, hsupp, hΔcol⟩ := hcol j
  rw [hΔcol i]
  have hrow : ∀ k : Fin m, ΔGj i k = 0 :=
    hsupp.row_zero hip hiq
  unfold matMulVec
  simp [hrow]

end NumStability
