import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.LU.BlockLU.DiagonalDominance
import NumStability.Algorithms.LinearSystems.LU.BlockLU.Factorization
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter13.Section01.NormConventions
import NumStability.Source.Higham.Chapter13.Theorem02.Factorization

/-!
# Source.Higham.Chapter13.Theorem07.PivotExistence

This module formalizes the source-facing Chapter 13 statements for
`Theorem07.PivotExistence`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    if one block column has zero off-diagonal blocks and the diagonal block has
    a nonzero right-kernel vector, then the flattened block matrix is singular.

    This formalizes the vector-kernel part of the source sentence following
    (13.18): after BDD forces the off-diagonal column norms to vanish, a
    singular active diagonal block makes the whole Schur complement singular. -/
theorem higham13_blockMatrixFlat_det_eq_zero_of_offdiag_col_zero_of_diag_kernel
    {m r : ℕ}
    (A : Fin m → Fin m → Fin r → Fin r → ℝ)
    (j : Fin m) (x : Fin r → ℝ) (s0 : Fin r) (hx : x s0 ≠ 0)
    (hdiag : ∀ s : Fin r, ∑ t : Fin r, A j j s t * x t = 0)
    (hoff : ∀ i : Fin m, i ≠ j → ∀ s t : Fin r, A i j s t = 0) :
    Matrix.det (blockMatrixFlat A) = 0 := by
  classical
  let v : Fin m × Fin r → ℝ := fun q => if q.1 = j then x q.2 else 0
  have hmul : (blockMatrixFlat A).mulVec v = 0 := by
    ext p
    rcases p with ⟨i, s⟩
    have hsum_eq :
        (∑ q : Fin m × Fin r, A i q.1 s q.2 * v q) =
          ∑ t : Fin r, A i j s t * x t := by
      rw [Fintype.sum_prod_type]
      simp [v]
    rw [Matrix.mulVec, dotProduct]
    change (∑ q : Fin m × Fin r, A i q.1 s q.2 * v q) = 0
    rw [hsum_eq]
    by_cases hij : i = j
    · subst i
      exact hdiag s
    · simp [hoff i hij]
  have hvne : v ≠ 0 := by
    intro hv
    have hvcoord := congr_fun hv (j, s0)
    simp [v] at hvcoord
    exact hx hvcoord
  exact (Matrix.exists_mulVec_eq_zero_iff).mp ⟨v, hvne, hmul⟩

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    the zero-off-column/right-kernel situation contradicts the chapter's
    explicit block-nonsingularity predicate. -/
theorem higham13_not_blockMatrixNonsingular_of_offdiag_col_zero_of_diag_kernel
    {m r : ℕ}
    (A : Fin m → Fin m → Fin r → Fin r → ℝ)
    (j : Fin m) (x : Fin r → ℝ) (s0 : Fin r) (hx : x s0 ≠ 0)
    (hdiag : ∀ s : Fin r, ∑ t : Fin r, A j j s t * x t = 0)
    (hoff : ∀ i : Fin m, i ≠ j → ∀ s t : Fin r, A i j s t = 0) :
    ¬ BlockMatrixNonsingular A := by
  intro hA
  exact
    (blockMatrixFlat_det_ne_zero_of_blockMatrixNonsingular A hA)
      (higham13_blockMatrixFlat_det_eq_zero_of_offdiag_col_zero_of_diag_kernel
        A j x s0 hx hdiag hoff)

/-- A nonzero finite vector has a nonzero coordinate.  This small adapter keeps
    the Theorem 13.7 diagonal-kernel extraction explicit. -/
theorem higham13_exists_nonzero_coord_of_vec_ne_zero {r : ℕ} {x : Fin r → ℝ}
    (hx : x ≠ 0) :
    ∃ s0 : Fin r, x s0 ≠ 0 := by
  classical
  by_contra h
  apply hx
  funext s
  by_contra hs
  exact h ⟨s, hs⟩

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof dependency:
    a singular diagonal block has a nonzero right-kernel vector with an
    explicitly nonzero coordinate. -/
theorem higham13_exists_diag_kernel_coord_of_det_eq_zero {r : ℕ}
    (B : Fin r → Fin r → ℝ)
    (hdet : Matrix.det B = 0) :
    ∃ (x : Fin r → ℝ) (s0 : Fin r),
      x s0 ≠ 0 ∧ ∀ s : Fin r, ∑ t : Fin r, B s t * x t = 0 := by
  classical
  obtain ⟨x, hxne, hmul⟩ :=
    (Matrix.exists_mulVec_eq_zero_iff (M := B)).mpr hdet
  obtain ⟨s0, hs0⟩ := higham13_exists_nonzero_coord_of_vec_ne_zero hxne
  refine ⟨x, s0, hs0, ?_⟩
  intro s
  have hs := congr_fun hmul s
  simpa [Matrix.mulVec, dotProduct] using hs

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    if one block column has zero off-diagonal blocks and the diagonal block is
    singular, then the flattened block matrix is singular. -/
theorem higham13_blockMatrixFlat_det_eq_zero_of_offdiag_col_zero_of_diag_det_eq_zero
    {m r : ℕ}
    (A : Fin m → Fin m → Fin r → Fin r → ℝ)
    (j : Fin m)
    (hdiagdet : Matrix.det (A j j) = 0)
    (hoff : ∀ i : Fin m, i ≠ j → ∀ s t : Fin r, A i j s t = 0) :
    Matrix.det (blockMatrixFlat A) = 0 := by
  obtain ⟨x, s0, hx, hdiag⟩ :=
    higham13_exists_diag_kernel_coord_of_det_eq_zero (A j j) hdiagdet
  exact
    higham13_blockMatrixFlat_det_eq_zero_of_offdiag_col_zero_of_diag_kernel
      A j x s0 hx hdiag hoff

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    the zero-off-column/singular-diagonal-block situation contradicts the
    chapter's explicit block-nonsingularity predicate. -/
theorem higham13_not_blockMatrixNonsingular_of_offdiag_col_zero_of_diag_det_eq_zero
    {m r : ℕ}
    (A : Fin m → Fin m → Fin r → Fin r → ℝ)
    (j : Fin m)
    (hdiagdet : Matrix.det (A j j) = 0)
    (hoff : ∀ i : Fin m, i ≠ j → ∀ s t : Fin r, A i j s t = 0) :
    ¬ BlockMatrixNonsingular A := by
  intro hA
  exact
    (blockMatrixFlat_det_ne_zero_of_blockMatrixNonsingular A hA)
      (higham13_blockMatrixFlat_det_eq_zero_of_offdiag_col_zero_of_diag_det_eq_zero
        A j hdiagdet hoff)

/-- Matrix-`∞` block diagonal dominance implies the finite-function block-norm
    form used by the all-leading-prefix BDD inverse bridge.

    The finite-function block norm is the chapter max-entry block norm, and it
    is bounded by the matrix `∞` operator norm for positive block size. -/
theorem higham13_blockDiagDomCol_piNorm_of_infNorm {m r : ℕ} (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound) :
    IsBlockDiagDomCol m
      (fun i j => ‖(fun a b => A i j a b : Fin r → Fin r → ℝ)‖)
      invDiagBound := by
  intro j
  calc
    ∑ i : Fin m,
        (if i = j then 0 else
          ‖(fun a b => A i j a b : Fin r → Fin r → ℝ)‖)
        ≤ ∑ i : Fin m, (if i = j then 0 else infNorm (A i j)) := by
          apply Finset.sum_le_sum
          intro i _hi
          by_cases hij : i = j
          · simp [hij]
          · simp [hij]
            rw [higham13_block_norm_eq_maxEntryNorm hr]
            exact maxEntryNorm_le_infNorm hr (A i j)
    _ ≤ invDiagBound j := hDom j

/-- Matrix-`∞` block diagonal dominance implies the source max-entry
    block-norm form used by the mixed column-mass proof of Theorem 13.8. -/
theorem higham13_blockDiagDomCol_maxEntry_of_infNorm {m r : ℕ} (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j : Fin m => infNorm (A i j)) invDiagBound) :
    IsBlockDiagDomCol m (fun i j : Fin m => maxEntryNorm hr (A i j)) invDiagBound := by
  intro j
  calc
    ∑ i : Fin m, (if i = j then 0 else maxEntryNorm hr (A i j))
        ≤ ∑ i : Fin m, (if i = j then 0 else infNorm (A i j)) := by
          apply Finset.sum_le_sum
          intro i _hi
          by_cases hij : i = j
          · simp [hij]
          · simp [hij]
            exact maxEntryNorm_le_infNorm hr (A i j)
    _ ≤ invDiagBound j := hDom j

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    in a column block diagonally dominant table, if the diagonal lower bound
    for a column is nonpositive, then every off-diagonal block norm in that
    column is zero.

    This is the scalar part of the source sentence following (13.18): when an
    active Schur diagonal block is singular, its lower norm is zero, so column
    dominance forces the whole off-diagonal column of the Schur complement to
    vanish. -/
theorem higham13_blockDiagDomCol_offdiag_zero_of_diagBound_nonpos {m : ℕ}
    (blockNorm : Fin m → Fin m → ℝ) (invDiagBound : Fin m → ℝ)
    (hNorm : ∀ i j : Fin m, 0 ≤ blockNorm i j)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (j : Fin m) (hj : invDiagBound j ≤ 0) :
    ∀ i : Fin m, i ≠ j → blockNorm i j = 0 := by
  classical
  intro i hij
  let f : Fin m → ℝ := fun a => if a = j then 0 else blockNorm a j
  have hf_nonneg : ∀ a : Fin m, 0 ≤ f a := by
    intro a
    by_cases haj : a = j
    · simp [f, haj]
    · simpa [f, haj] using hNorm a j
  have hterm_le_sum : f i ≤ ∑ a : Fin m, f a :=
    Finset.single_le_sum (fun a _ha => hf_nonneg a) (Finset.mem_univ i)
  have hsum_nonpos : (∑ a : Fin m, f a) ≤ 0 := by
    simpa [f] using le_trans (hDom j) hj
  have hterm_nonpos : f i ≤ 0 := le_trans hterm_le_sum hsum_nonpos
  have hterm_zero : f i = 0 := le_antisymm hterm_nonpos (hf_nonneg i)
  simpa [f, hij] using hterm_zero

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    row analogue of
    `higham13_blockDiagDomCol_offdiag_zero_of_diagBound_nonpos`. -/
theorem higham13_blockDiagDomRow_offdiag_zero_of_diagBound_nonpos {m : ℕ}
    (blockNorm : Fin m → Fin m → ℝ) (invDiagBound : Fin m → ℝ)
    (hNorm : ∀ i j : Fin m, 0 ≤ blockNorm i j)
    (hDom : IsBlockDiagDomRow m blockNorm invDiagBound)
    (i : Fin m) (hi : invDiagBound i ≤ 0) :
    ∀ j : Fin m, i ≠ j → blockNorm i j = 0 := by
  classical
  intro j hij
  let f : Fin m → ℝ := fun b => if i = b then 0 else blockNorm i b
  have hf_nonneg : ∀ b : Fin m, 0 ≤ f b := by
    intro b
    by_cases hib : i = b
    · simp [f, hib]
    · simpa [f, hib] using hNorm i b
  have hterm_le_sum : f j ≤ ∑ b : Fin m, f b :=
    Finset.single_le_sum (fun b _hb => hf_nonneg b) (Finset.mem_univ j)
  have hsum_nonpos : (∑ b : Fin m, f b) ≤ 0 := by
    simpa [f] using le_trans (hDom i) hi
  have hterm_nonpos : f j ≤ 0 := le_trans hterm_le_sum hsum_nonpos
  have hterm_zero : f j = 0 := le_antisymm hterm_nonpos (hf_nonneg j)
  simpa [f, hij] using hterm_zero

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    column BDD on the actual block Pi-norm table turns a nonpositive active
    diagonal lower bound into zero scalar entries in every off-diagonal block
    of that column. -/
theorem higham13_blockDiagDomCol_offdiag_entries_zero_of_norm_table_nonpos
    {m r : ℕ}
    (A : Fin m → Fin m → Fin r → Fin r → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => ‖A i j‖) invDiagBound)
    (j : Fin m) (hj : invDiagBound j ≤ 0) :
    ∀ i : Fin m, i ≠ j → ∀ s t : Fin r, A i j s t = 0 := by
  classical
  have hNorm : ∀ i j : Fin m, 0 ≤ ‖A i j‖ := by
    intro i j
    exact norm_nonneg (A i j)
  intro i hij
  have hzero :
      ‖A i j‖ = 0 :=
    higham13_blockDiagDomCol_offdiag_zero_of_diagBound_nonpos
      (fun i j => ‖A i j‖) invDiagBound hNorm hDom j hj i hij
  exact higham13_block_entries_zero_of_norm_eq_zero hzero

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    under column BDD, a nonpositive active diagonal lower bound and a singular
    active diagonal block contradict block nonsingularity. -/
theorem higham13_not_blockMatrixNonsingular_of_blockDiagDomCol_diagBound_nonpos_diag_det_eq_zero
    {m r : ℕ}
    (A : Fin m → Fin m → Fin r → Fin r → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => ‖A i j‖) invDiagBound)
    (j : Fin m) (hj : invDiagBound j ≤ 0)
    (hdiagdet : Matrix.det (A j j) = 0) :
    ¬ BlockMatrixNonsingular A :=
  higham13_not_blockMatrixNonsingular_of_offdiag_col_zero_of_diag_det_eq_zero
    A j hdiagdet
    (higham13_blockDiagDomCol_offdiag_entries_zero_of_norm_table_nonpos
      A invDiagBound hDom j hj)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    contrapositive form of the preceding contradiction.  In a nonsingular
    column-BDD block matrix, a nonpositive active diagonal lower bound rules
    out a singular active diagonal block. -/
theorem higham13_diag_det_ne_zero_of_blockMatrixNonsingular_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ}
    (A : Fin m → Fin m → Fin r → Fin r → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hA : BlockMatrixNonsingular A)
    (hDom : IsBlockDiagDomCol m (fun i j => ‖A i j‖) invDiagBound)
    (j : Fin m) (hj : invDiagBound j ≤ 0) :
    Matrix.det (A j j) ≠ 0 := by
  intro hdiagdet
  exact
    (higham13_not_blockMatrixNonsingular_of_blockDiagDomCol_diagBound_nonpos_diag_det_eq_zero
      A invDiagBound hDom j hj hdiagdet) hA

/-- Embed the leading `(p+1)` block prefix into the full block index set. -/
noncomputable def leadingBlockPrefixIndex13_7 {m : ℕ} (p : ℕ) (hp : p < m) :
    Fin (p + 1) → Fin m :=
  fun i => ⟨i.val, by
    have hi : i.val < p + 1 := i.isLt
    omega⟩

/-- Restrict a block-norm table to the leading `(p+1)` principal block
    prefix.  This is the norm-table analogue of `leadingBlockPrefix13_2`. -/
noncomputable def leadingBlockPrefixNorm13_7 {m : ℕ}
    (blockNorm : Fin m → Fin m → ℝ) (p : ℕ) (hp : p < m) :
    Fin (p + 1) → Fin (p + 1) → ℝ :=
  fun i j =>
    blockNorm (leadingBlockPrefixIndex13_7 p hp i)
      (leadingBlockPrefixIndex13_7 p hp j)

/-- Restrict the diagonal inverse-norm lower-bound table to the leading
    `(p+1)` block prefix. -/
noncomputable def leadingBlockPrefixInvDiagBound13_7 {m : ℕ}
    (invDiagBound : Fin m → ℝ) (p : ℕ) (hp : p < m) :
    Fin (p + 1) → ℝ :=
  fun j => invDiagBound (leadingBlockPrefixIndex13_7 p hp j)

/-- The leading block prefix of a column block diagonally dominant matrix is
    column block diagonally dominant.

    This is a Theorem 13.7 nonsingularity-route dependency: to use Theorem 13.2,
    every leading principal block prefix must inherit the same dominance
    condition from the full matrix. -/
theorem isBlockDiagDomCol_leadingBlockPrefix13_7 {m : ℕ}
    (blockNorm : Fin m → Fin m → ℝ) (invDiagBound : Fin m → ℝ)
    (hNormNonneg : ∀ i j : Fin m, 0 ≤ blockNorm i j)
    (hDom : IsBlockDiagDomCol m blockNorm invDiagBound)
    (p : ℕ) (hp : p < m) :
    IsBlockDiagDomCol (p + 1)
      (leadingBlockPrefixNorm13_7 blockNorm p hp)
      (leadingBlockPrefixInvDiagBound13_7 invDiagBound p hp) := by
  classical
  intro j
  let emb : Fin (p + 1) → Fin m := leadingBlockPrefixIndex13_7 p hp
  have hemb : Function.Injective emb := by
    intro a b h
    exact Fin.ext (by
      simpa [emb, leadingBlockPrefixIndex13_7] using congrArg Fin.val h)
  calc
    ∑ i : Fin (p + 1),
        (if i = j then 0 else leadingBlockPrefixNorm13_7 blockNorm p hp i j)
        = ∑ i : Fin (p + 1),
            (if emb i = emb j then 0 else blockNorm (emb i) (emb j)) := by
            apply Finset.sum_congr rfl
            intro i _hi
            by_cases hij : i = j
            · simp [hij]
            · have hne : emb i ≠ emb j := fun h => hij (hemb h)
              simp [hij, hne, leadingBlockPrefixNorm13_7, emb]
    _ = ∑ i ∈ Finset.univ.image emb,
          (if i = emb j then 0 else blockNorm i (emb j)) := by
            rw [Finset.sum_image]
            intro a _ha b _hb hab
            exact hemb hab
    _ ≤ ∑ i : Fin m, (if i = emb j then 0 else blockNorm i (emb j)) := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (by intro x hx; simp)
              (by
                intro x _hxuniv _hxnot
                by_cases hxj : x = emb j
                · simp [hxj]
                · simp [hxj, hNormNonneg x (emb j)])
    _ ≤ invDiagBound (emb j) := hDom (emb j)
    _ = leadingBlockPrefixInvDiagBound13_7 invDiagBound p hp j := rfl

/-- The leading block prefix of a row block diagonally dominant matrix is row
    block diagonally dominant. -/
theorem isBlockDiagDomRow_leadingBlockPrefix13_7 {m : ℕ}
    (blockNorm : Fin m → Fin m → ℝ) (invDiagBound : Fin m → ℝ)
    (hNormNonneg : ∀ i j : Fin m, 0 ≤ blockNorm i j)
    (hDom : IsBlockDiagDomRow m blockNorm invDiagBound)
    (p : ℕ) (hp : p < m) :
    IsBlockDiagDomRow (p + 1)
      (leadingBlockPrefixNorm13_7 blockNorm p hp)
      (leadingBlockPrefixInvDiagBound13_7 invDiagBound p hp) := by
  classical
  intro i
  let emb : Fin (p + 1) → Fin m := leadingBlockPrefixIndex13_7 p hp
  have hemb : Function.Injective emb := by
    intro a b h
    exact Fin.ext (by
      simpa [emb, leadingBlockPrefixIndex13_7] using congrArg Fin.val h)
  calc
    ∑ j : Fin (p + 1),
        (if i = j then 0 else leadingBlockPrefixNorm13_7 blockNorm p hp i j)
        = ∑ j : Fin (p + 1),
            (if emb i = emb j then 0 else blockNorm (emb i) (emb j)) := by
            apply Finset.sum_congr rfl
            intro j _hj
            by_cases hij : i = j
            · simp [hij]
            · have hne : emb i ≠ emb j := fun h => hij (hemb h)
              simp [hij, hne, leadingBlockPrefixNorm13_7, emb]
    _ = ∑ j ∈ Finset.univ.image emb,
          (if emb i = j then 0 else blockNorm (emb i) j) := by
            rw [Finset.sum_image]
            intro a _ha b _hb hab
            exact hemb hab
    _ ≤ ∑ j : Fin m, (if emb i = j then 0 else blockNorm (emb i) j) := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (by intro x hx; simp)
              (by
                intro x _hxuniv _hxnot
                by_cases hix : emb i = x
                · simp [hix]
                · simp [hix, hNormNonneg (emb i) x])
    _ ≤ invDiagBound (emb i) := hDom (emb i)
    _ = leadingBlockPrefixInvDiagBound13_7 invDiagBound p hp i := rfl

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    a nonsingular leading prefix that inherits column BDD cannot have a
    singular active diagonal block when the active diagonal lower bound is
    nonpositive. -/
theorem higham13_leadingBlockPrefix_diag_det_ne_zero_of_blockMatrixNonsingular_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ}
    (A : Fin m → Fin m → Fin r → Fin r → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => ‖A i j‖) invDiagBound)
    (p : ℕ) (hp : p < m)
    (hPrefix : BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (j : Fin (p + 1))
    (hj : invDiagBound (leadingBlockPrefixIndex13_7 p hp j) ≤ 0) :
    Matrix.det
      (A (leadingBlockPrefixIndex13_7 p hp j)
        (leadingBlockPrefixIndex13_7 p hp j)) ≠ 0 := by
  classical
  have hNormNonneg : ∀ i j : Fin m, 0 ≤ ‖A i j‖ := by
    intro i j
    exact norm_nonneg (A i j)
  have hDomPrefixRaw :=
    isBlockDiagDomCol_leadingBlockPrefix13_7
      (fun i j => ‖A i j‖) invDiagBound hNormNonneg hDom p hp
  have hDomPrefix :
      IsBlockDiagDomCol (p + 1)
        (fun i j => ‖leadingBlockPrefix13_2 A p hp i j‖)
        (leadingBlockPrefixInvDiagBound13_7 invDiagBound p hp) := by
    simpa [leadingBlockPrefixNorm13_7, leadingBlockPrefix13_2,
      leadingBlockPrefixIndex13_7] using hDomPrefixRaw
  have hjPrefix :
      leadingBlockPrefixInvDiagBound13_7 invDiagBound p hp j ≤ 0 := by
    simpa [leadingBlockPrefixInvDiagBound13_7, leadingBlockPrefixIndex13_7]
      using hj
  have hdetPrefix :=
    higham13_diag_det_ne_zero_of_blockMatrixNonsingular_blockDiagDomCol_diagBound_nonpos
      (leadingBlockPrefix13_2 A p hp)
      (leadingBlockPrefixInvDiagBound13_7 invDiagBound p hp)
      hPrefix hDomPrefix j hjPrefix
  simpa [leadingBlockPrefix13_2, leadingBlockPrefixIndex13_7] using hdetPrefix

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    leading-principal-block nonsingularity supplies the prefix nonsingularity
    premise used by
    `higham13_leadingBlockPrefix_diag_det_ne_zero_of_blockMatrixNonsingular_blockDiagDomCol_diagBound_nonpos`. -/
theorem higham13_leadingBlockPrefix_diag_det_ne_zero_of_leadingPrincipalBlockNonsingular13_2_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ}
    (A : Fin m → Fin m → Fin r → Fin r → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hLead : LeadingPrincipalBlockNonsingular13_2 A)
    (hDom : IsBlockDiagDomCol m (fun i j => ‖A i j‖) invDiagBound)
    (p : ℕ) (hpLead : p + 1 < m)
    (j : Fin (p + 1))
    (hj : invDiagBound
        (leadingBlockPrefixIndex13_7 p
          (Nat.lt_trans (Nat.lt_succ_self p) hpLead) j) ≤ 0) :
    Matrix.det
      (A
        (leadingBlockPrefixIndex13_7 p
          (Nat.lt_trans (Nat.lt_succ_self p) hpLead) j)
        (leadingBlockPrefixIndex13_7 p
          (Nat.lt_trans (Nat.lt_succ_self p) hpLead) j)) ≠ 0 :=
  higham13_leadingBlockPrefix_diag_det_ne_zero_of_blockMatrixNonsingular_blockDiagDomCol_diagBound_nonpos
    A invDiagBound hDom p (Nat.lt_trans (Nat.lt_succ_self p) hpLead)
    (hLead p hpLead) j hj

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    the BDD leading-prefix contradiction supplies the canonical two-sided
    inverse for a diagonal block of a nonsingular leading prefix. -/
theorem higham13_leadingBlockPrefix_diag_nonsingInv_isInverse_of_blockMatrixNonsingular_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ}
    (A : Fin m → Fin m → Fin r → Fin r → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hDom : IsBlockDiagDomCol m (fun i j => ‖A i j‖) invDiagBound)
    (p : ℕ) (hp : p < m)
    (hPrefix : BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (j : Fin (p + 1))
    (hj : invDiagBound (leadingBlockPrefixIndex13_7 p hp j) ≤ 0) :
    IsInverse r
      (A (leadingBlockPrefixIndex13_7 p hp j)
        (leadingBlockPrefixIndex13_7 p hp j))
      (nonsingInv r
        (A (leadingBlockPrefixIndex13_7 p hp j)
          (leadingBlockPrefixIndex13_7 p hp j))) := by
  exact
    isInverse_nonsingInv_of_det_ne_zero r
      (A (leadingBlockPrefixIndex13_7 p hp j)
        (leadingBlockPrefixIndex13_7 p hp j))
      (higham13_leadingBlockPrefix_diag_det_ne_zero_of_blockMatrixNonsingular_blockDiagDomCol_diagBound_nonpos
        A invDiagBound hDom p hp hPrefix j hj)

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    leading-principal-block nonsingularity plus column BDD supplies the
    canonical two-sided inverse for every prefix diagonal block whose BDD
    lower bound is nonpositive. -/
theorem higham13_leadingBlockPrefix_diag_nonsingInv_isInverse_of_leadingPrincipalBlockNonsingular13_2_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ}
    (A : Fin m → Fin m → Fin r → Fin r → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hLead : LeadingPrincipalBlockNonsingular13_2 A)
    (hDom : IsBlockDiagDomCol m (fun i j => ‖A i j‖) invDiagBound)
    (p : ℕ) (hpLead : p + 1 < m)
    (j : Fin (p + 1))
    (hj : invDiagBound
        (leadingBlockPrefixIndex13_7 p
          (Nat.lt_trans (Nat.lt_succ_self p) hpLead) j) ≤ 0) :
    IsInverse r
      (A
        (leadingBlockPrefixIndex13_7 p
          (Nat.lt_trans (Nat.lt_succ_self p) hpLead) j)
        (leadingBlockPrefixIndex13_7 p
          (Nat.lt_trans (Nat.lt_succ_self p) hpLead) j))
      (nonsingInv r
        (A
          (leadingBlockPrefixIndex13_7 p
            (Nat.lt_trans (Nat.lt_succ_self p) hpLead) j)
          (leadingBlockPrefixIndex13_7 p
            (Nat.lt_trans (Nat.lt_succ_self p) hpLead) j))) :=
  higham13_leadingBlockPrefix_diag_nonsingInv_isInverse_of_blockMatrixNonsingular_blockDiagDomCol_diagBound_nonpos
    A invDiagBound hDom p (Nat.lt_trans (Nat.lt_succ_self p) hpLead)
    (hLead p hpLead) j hj

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    if every leading prefix is nonsingular, column BDD supplies the canonical
    two-sided inverse table for all original diagonal blocks whose BDD lower
    bounds are nonpositive. -/
theorem higham13_diag_nonsingInv_isInverse_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ}
    (A : Fin m → Fin m → Fin r → Fin r → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (hDom : IsBlockDiagDomCol m (fun i j => ‖A i j‖) invDiagBound)
    (hBound : ∀ j : Fin m, invDiagBound j ≤ 0)
    (j : Fin m) :
    IsInverse r (A j j) (nonsingInv r (A j j)) := by
  let jPrefix : Fin (j.val + 1) := ⟨j.val, by omega⟩
  have hidx : leadingBlockPrefixIndex13_7 j.val j.isLt jPrefix = j := by
    ext
    simp [leadingBlockPrefixIndex13_7, jPrefix]
  have hmain :=
    higham13_leadingBlockPrefix_diag_nonsingInv_isInverse_of_blockMatrixNonsingular_blockDiagDomCol_diagBound_nonpos
      A invDiagBound hDom j.val j.isLt (hPrefix j.val j.isLt) jPrefix
      (by simpa [hidx] using hBound j)
  simpa [hidx] using hmain

/-- Higham, 2nd ed., Chapter 13, Theorem 13.7 proof step:
    right-inverse projection of
    `higham13_diag_nonsingInv_isInverse_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos`,
    ready for downstream Algorithm 13.3 pivot-certificate APIs. -/
theorem higham13_diag_nonsingInv_isRightInverse_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
    {m r : ℕ}
    (A : Fin m → Fin m → Fin r → Fin r → ℝ)
    (invDiagBound : Fin m → ℝ)
    (hPrefix : ∀ p : ℕ, ∀ hp : p < m,
      BlockMatrixNonsingular (leadingBlockPrefix13_2 A p hp))
    (hDom : IsBlockDiagDomCol m (fun i j => ‖A i j‖) invDiagBound)
    (hBound : ∀ j : Fin m, invDiagBound j ≤ 0)
    (j : Fin m) :
    IsRightInverse r (A j j) (nonsingInv r (A j j)) :=
  (higham13_diag_nonsingInv_isInverse_of_all_leadingBlockPrefixes_blockDiagDomCol_diagBound_nonpos
    A invDiagBound hPrefix hDom hBound j).2

end NumStability
