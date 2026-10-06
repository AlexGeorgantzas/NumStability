-- Algorithms/QR/HouseholderMatrixStep.lean
--
-- Matrix-column bridge for concrete Householder reflector application.
--
-- Higham Lemma 18.2 gives a backward-error statement for applying one
-- Householder reflector to one vector.  A matrix step applies that same
-- reflector to every column.  The resulting perturbation matrix in the
-- per-vector statement may depend on the column; this file records that
-- columnwise interface explicitly instead of forcing it into the stronger
-- single-ΔP whole-matrix contract used by the existing QR wrapper.

import NumStability.Algorithms.QR.HouseholderOneStep

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-- Apply one rounded Householder reflector to every column of a matrix.

    This is still a concrete `fl_*` implementation: each output column is
    computed by the rounded vector kernel `fl_householderApply`, so the
    dot-product and axpy rounding order is inherited from that kernel. -/
noncomputable def fl_householderApplyMatrix (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (beta : ℝ) (A : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => fl_householderApply fp n v beta (fun k => A k j) i

/-- Apply one rounded Householder reflector to every column of a rectangular
    `m × p` panel.  This is the panel-update shape needed by QR trailing
    subproblems. -/
noncomputable def fl_householderApplyMatrixRect (fp : FPModel) (m p : ℕ)
    (v : Fin m → ℝ) (beta : ℝ) (A : Fin m → Fin p → ℝ) :
    Fin m → Fin p → ℝ :=
  fun i j => fl_householderApply fp m v beta (fun k => A k j) i

/-- Columnwise matrix-step form of Higham Lemma 18.2.

    For each matrix column `j`, the rounded application satisfies
    `A_hat[:,j] = (P + ΔP_j) A[:,j]` with `‖ΔP_j‖_F ≤ c`.  The perturbation
    is deliberately indexed by `j`: the dot-product/update roundoff used while
    applying the reflector to one column need not be the same as for another
    column.  This is the honest bridge needed before proving the repeated
    reflector sequence theorem. -/
structure ColumnwiseHouseholderStepError (n : ℕ)
    (P : Fin n → Fin n → ℝ) (A A_hat : Fin n → Fin n → ℝ)
    (c : ℝ) : Prop where
  /-- The exact reflector is orthogonal. -/
  orth : IsOrthogonal n P
  /-- Every computed output column is a backward-stable Householder application,
      with a column-dependent perturbation matrix. -/
  pert : ∀ j : Fin n, ∃ ΔPj : Fin n → Fin n → ℝ,
    frobNorm ΔPj ≤ c ∧
    ∀ i : Fin n, A_hat i j =
      matMulVec n (fun a b => P a b + ΔPj a b) (fun k => A k j) i

/-- Rectangular panel form of `ColumnwiseHouseholderStepError`.

    The reflector is `m × m`, while the panel being updated is `m × p`.  As in
    the square version, each panel column gets its own perturbation matrix. -/
structure ColumnwiseHouseholderStepErrorRect (m p : ℕ)
    (P : Fin m → Fin m → ℝ) (A A_hat : Fin m → Fin p → ℝ)
    (c : ℝ) : Prop where
  /-- The exact reflector is orthogonal. -/
  orth : IsOrthogonal m P
  /-- Every computed output column is a backward-stable Householder application,
      with a column-dependent perturbation matrix. -/
  pert : ∀ j : Fin p, ∃ ΔPj : Fin m → Fin m → ℝ,
    frobNorm ΔPj ≤ c ∧
    ∀ i : Fin m, A_hat i j =
      matMulVec m (fun a b => P a b + ΔPj a b) (fun k => A k j) i

/-- Package per-column `HouseholderAppError` facts as a columnwise matrix-step
    error statement. -/
theorem columnwiseHouseholderStepError_of_appError (n : ℕ)
    (P : Fin n → Fin n → ℝ) (A A_hat : Fin n → Fin n → ℝ) (c : ℝ)
    (hP : IsOrthogonal n P)
    (hcols : ∀ j : Fin n,
      HouseholderAppError n P (fun i => A i j) (fun i => A_hat i j) c) :
    ColumnwiseHouseholderStepError n P A A_hat c := by
  refine ⟨hP, ?_⟩
  intro j
  exact (hcols j).pert

/-- Package per-column `HouseholderAppError` facts as a rectangular panel-step
    error statement. -/
theorem columnwiseHouseholderStepErrorRect_of_appError (m p : ℕ)
    (P : Fin m → Fin m → ℝ) (A A_hat : Fin m → Fin p → ℝ) (c : ℝ)
    (hP : IsOrthogonal m P)
    (hcols : ∀ j : Fin p,
      HouseholderAppError m P (fun i => A i j) (fun i => A_hat i j) c) :
    ColumnwiseHouseholderStepErrorRect m p P A A_hat c := by
  refine ⟨hP, ?_⟩
  intro j
  exact (hcols j).pert

/-- Concrete Householder construction plus concrete columnwise application
    satisfies the matrix-step form of the Householder application contract.

    This is the matrix version of `fl_householderConstructApply_appError`.
    It proves the implementation-backed result that every column of
    `fl_householderApplyMatrix` has a Higham Lemma 18.2 style backward error.
    The repeated-reflector QR sequence theorem is proved in
    `HouseholderQR.lean`; this file supplies the one-step matrix contract. -/
theorem fl_householderConstructApply_matrix_step_error (fp : FPModel) {n : ℕ}
    (hn0 : 0 < n) (x : Fin n → ℝ) (A : Fin n → Fin n → ℝ)
    (hx : x ≠ 0)
    (hvalid : gammaValid fp (11 * n + 23)) :
    ColumnwiseHouseholderStepError n
      (householder n
        (householderNormalizedVector n
          (householderVector hn0 x) (householderBetaFromScale hn0 x)) 1)
      A
      (fl_householderApplyMatrix fp n
        (fl_householderNormalizedVector fp hn0 x) 1 A)
      (Real.sqrt ((n : ℝ) * fp.u ^ 2) +
        2 * gamma fp (11 * n + 23)) := by
  let P : Fin n → Fin n → ℝ :=
    householder n
      (householderNormalizedVector n
        (householderVector hn0 x) (householderBetaFromScale hn0 x)) 1
  have hP : IsOrthogonal n P := by
    have happ :=
      fl_householderConstructApply_appError fp hn0 x (fun _ : Fin n => 0)
        hx hvalid
    simpa [P] using happ.orth
  apply columnwiseHouseholderStepError_of_appError n P
  · exact hP
  · intro j
    have happ :=
      fl_householderConstructApply_appError fp hn0 x (fun k => A k j)
        hx hvalid
    simpa [P, fl_householderApplyMatrix] using happ

/-- Concrete Householder construction plus concrete rectangular panel
    application satisfies the rectangular matrix-step contract. -/
theorem fl_householderConstructApply_matrix_step_error_rect (fp : FPModel)
    {m p : ℕ}
    (hm0 : 0 < m) (x : Fin m → ℝ) (A : Fin m → Fin p → ℝ)
    (hx : x ≠ 0)
    (hvalid : gammaValid fp (11 * m + 23)) :
    ColumnwiseHouseholderStepErrorRect m p
      (householder m
        (householderNormalizedVector m
          (householderVector hm0 x) (householderBetaFromScale hm0 x)) 1)
      A
      (fl_householderApplyMatrixRect fp m p
        (fl_householderNormalizedVector fp hm0 x) 1 A)
      (Real.sqrt ((m : ℝ) * fp.u ^ 2) +
        2 * gamma fp (11 * m + 23)) := by
  let P : Fin m → Fin m → ℝ :=
    householder m
      (householderNormalizedVector m
        (householderVector hm0 x) (householderBetaFromScale hm0 x)) 1
  have hP : IsOrthogonal m P := by
    have happ :=
      fl_householderConstructApply_appError fp hm0 x (fun _ : Fin m => 0)
        hx hvalid
    simpa [P] using happ.orth
  apply columnwiseHouseholderStepErrorRect_of_appError m p P
  · exact hP
  · intro j
    have happ :=
      fl_householderConstructApply_appError fp hm0 x (fun k => A k j)
        hx hvalid
    simpa [P, fl_householderApplyMatrixRect] using happ

/-- Residual form of a columnwise Householder matrix step.

    Each computed column is the exact reflector application plus the residual
    produced by that column's perturbation matrix:
    `A_hat[:,j] = P*A[:,j] + ΔP_j*A[:,j]`. -/
theorem ColumnwiseHouseholderStepError.column_residual {n : ℕ}
    {P A A_hat : Fin n → Fin n → ℝ} {c : ℝ}
    (hstep : ColumnwiseHouseholderStepError n P A A_hat c) :
    ∀ j : Fin n, ∃ ΔPj : Fin n → Fin n → ℝ,
      frobNorm ΔPj ≤ c ∧
      ∀ i : Fin n, A_hat i j =
        matMul n P A i j +
          matMulVec n ΔPj (fun k => A k j) i := by
  intro j
  obtain ⟨ΔPj, hΔPj, hcol⟩ := hstep.pert j
  refine ⟨ΔPj, hΔPj, ?_⟩
  intro i
  rw [hcol i]
  unfold matMulVec matMul
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Matrix residual form of a columnwise Householder matrix step.

    There is a residual matrix `E` such that `A_hat = P*A + E`, and every
    column of `E` is still represented as `ΔP_j*A[:,j]` with
    `‖ΔP_j‖_F ≤ c`.  This is the exact algebraic handle needed for the
    Higham Lemma 18.3 aggregation step. -/
theorem ColumnwiseHouseholderStepError.exists_residual_matrix {n : ℕ}
    {P A A_hat : Fin n → Fin n → ℝ} {c : ℝ}
    (hstep : ColumnwiseHouseholderStepError n P A A_hat c) :
    ∃ E : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, A_hat i j = matMul n P A i j + E i j) ∧
      ∀ j : Fin n, ∃ ΔPj : Fin n → Fin n → ℝ,
        frobNorm ΔPj ≤ c ∧
        ∀ i : Fin n, E i j =
          matMulVec n ΔPj (fun k => A k j) i := by
  classical
  let hres := hstep.column_residual
  let ΔP : Fin n → Fin n → Fin n → ℝ := fun j => Classical.choose (hres j)
  let E : Fin n → Fin n → ℝ :=
    fun i j => matMulVec n (ΔP j) (fun k => A k j) i
  refine ⟨E, ?_, ?_⟩
  · intro i j
    have hspec := Classical.choose_spec (hres j)
    exact hspec.2 i
  · intro j
    have hspec := Classical.choose_spec (hres j)
    refine ⟨ΔP j, hspec.1, ?_⟩
    intro i
    rfl

/-- Normwise residual consequence of a columnwise Householder matrix step.

    The column-dependent perturbations aggregate to a single residual matrix
    `E` satisfying `A_hat = P*A + E` and `‖E‖_F ≤ c‖A‖_F`.  This is the
    first exact aggregation step needed for Higham Lemma 18.3. -/
theorem ColumnwiseHouseholderStepError.exists_residual_matrix_bound {n : ℕ}
    {P A A_hat : Fin n → Fin n → ℝ} {c : ℝ}
    (hstep : ColumnwiseHouseholderStepError n P A A_hat c)
    (hc : 0 ≤ c) :
    ∃ E : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, A_hat i j = matMul n P A i j + E i j) ∧
      frobNorm E ≤ c * frobNorm A := by
  obtain ⟨E, hEA, hcol⟩ := hstep.exists_residual_matrix
  exact ⟨E, hEA, frobNorm_columnwise_matMulVec_le E A hc hcol⟩

/-- Residual form of a rectangular columnwise Householder panel step. -/
theorem ColumnwiseHouseholderStepErrorRect.column_residual {m p : ℕ}
    {P : Fin m → Fin m → ℝ} {A A_hat : Fin m → Fin p → ℝ} {c : ℝ}
    (hstep : ColumnwiseHouseholderStepErrorRect m p P A A_hat c) :
    ∀ j : Fin p, ∃ ΔPj : Fin m → Fin m → ℝ,
      frobNorm ΔPj ≤ c ∧
      ∀ i : Fin m, A_hat i j =
        matMulRect m m p P A i j +
          matMulVec m ΔPj (fun k => A k j) i := by
  intro j
  obtain ⟨ΔPj, hΔPj, hcol⟩ := hstep.pert j
  refine ⟨ΔPj, hΔPj, ?_⟩
  intro i
  rw [hcol i]
  unfold matMulVec matMulRect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Rectangular matrix residual form of a columnwise Householder panel step. -/
theorem ColumnwiseHouseholderStepErrorRect.exists_residual_matrix {m p : ℕ}
    {P : Fin m → Fin m → ℝ} {A A_hat : Fin m → Fin p → ℝ} {c : ℝ}
    (hstep : ColumnwiseHouseholderStepErrorRect m p P A A_hat c) :
    ∃ E : Fin m → Fin p → ℝ,
      (∀ (i : Fin m) (j : Fin p),
        A_hat i j = matMulRect m m p P A i j + E i j) ∧
      ∀ j : Fin p, ∃ ΔPj : Fin m → Fin m → ℝ,
        frobNorm ΔPj ≤ c ∧
        ∀ i : Fin m, E i j =
          matMulVec m ΔPj (fun k => A k j) i := by
  classical
  let hres := hstep.column_residual
  let ΔP : Fin p → Fin m → Fin m → ℝ := fun j => Classical.choose (hres j)
  let E : Fin m → Fin p → ℝ :=
    fun i j => matMulVec m (ΔP j) (fun k => A k j) i
  refine ⟨E, ?_, ?_⟩
  · intro i j
    have hspec := Classical.choose_spec (hres j)
    exact hspec.2 i
  · intro j
    have hspec := Classical.choose_spec (hres j)
    refine ⟨ΔP j, hspec.1, ?_⟩
    intro i
    rfl

/-- Normwise residual consequence of a rectangular columnwise Householder panel
    step. -/
theorem ColumnwiseHouseholderStepErrorRect.exists_residual_matrix_bound
    {m p : ℕ}
    {P : Fin m → Fin m → ℝ} {A A_hat : Fin m → Fin p → ℝ} {c : ℝ}
    (hstep : ColumnwiseHouseholderStepErrorRect m p P A A_hat c)
    (hc : 0 ≤ c) :
    ∃ E : Fin m → Fin p → ℝ,
      (∀ (i : Fin m) (j : Fin p),
        A_hat i j = matMulRect m m p P A i j + E i j) ∧
      frobNorm E ≤ c * frobNorm A := by
  obtain ⟨E, hEA, hcol⟩ := hstep.exists_residual_matrix
  exact ⟨E, hEA, frobNorm_columnwise_matMulVec_le_rect E A hc hcol⟩

end NumStability
