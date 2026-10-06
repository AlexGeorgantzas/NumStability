import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.LU.BlockLU.BlockMatrices
import NumStability.Algorithms.LinearSystems.LU.BlockLU.ResidualLifting
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum

/-!
# Block LU factorization foundations

Reusable block-LU factorization specifications, uniform block-matrix
flattenings, first-split reindexing bridges, nonsingularity criteria, and
entrywise norm comparisons. Numbered Chapter 13 results live under
`NumStability.Source.Higham`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix

/-- **Block LU factorization specification** (Higham, 2nd ed., §13.1).
    A = LU where L is block unit lower triangular (identity diagonal blocks)
    and U is block upper triangular, with m blocks of uniform size r. -/
structure BlockLUFactSpec (m r : ℕ)
    (A L U : Fin m → Fin m → (Fin r → Fin r → ℝ)) : Prop where
  /-- L has identity blocks on the diagonal: L_{ii} = I_r. -/
  L_diag : ∀ i : Fin m, L i i = idBlock r
  /-- L is block lower triangular: L_{ij} = 0 for i < j. -/
  L_upper_zero : ∀ i j : Fin m, i.val < j.val → L i j = zeroBlock r
  /-- U is block upper triangular: U_{ij} = 0 for j < i. -/
  U_lower_zero : ∀ i j : Fin m, j.val < i.val → U i j = zeroBlock r
  /-- Block product L·U equals A entrywise. -/
  product_eq : ∀ (i j : Fin m) (s t : Fin r),
    ∑ k : Fin m, ∑ l : Fin r, L i k s l * U k j l t = A i j s t

/-- Identity block matrix at the uniform-block level.  This is the target
    matrix for the source phrase "nonsingular leading principal block
    submatrix" in Theorem 13.2. -/
noncomputable def blockMatrixIdentity (m r : ℕ) :
    Fin m → Fin m → (Fin r → Fin r → ℝ) :=
  fun i j => if i = j then idBlock r else zeroBlock r

/-- A two-sided inverse for a uniform block matrix under block multiplication. -/
def BlockMatrixTwoSidedInverse {m r : ℕ}
    (A Ainv : Fin m → Fin m → (Fin r → Fin r → ℝ)) : Prop :=
  (∀ i j : Fin m, ∀ s t : Fin r,
    ∑ k : Fin m, ∑ l : Fin r, Ainv i k s l * A k j l t =
      blockMatrixIdentity m r i j s t) ∧
  (∀ i j : Fin m, ∀ s t : Fin r,
    ∑ k : Fin m, ∑ l : Fin r, A i k s l * Ainv k j l t =
      blockMatrixIdentity m r i j s t)

/-- Uniform block-matrix nonsingularity, represented by an explicit two-sided
    block inverse. -/
def BlockMatrixNonsingular {m r : ℕ}
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ)) : Prop :=
  ∃ Ainv : Fin m → Fin m → (Fin r → Fin r → ℝ), BlockMatrixTwoSidedInverse A Ainv

/-- Flatten a uniform block matrix to an ordinary matrix indexed by
    block-within-block pairs.  This is the bridge between Mathlib determinant
    and positive-definite facts and the Chapter 13 block predicates. -/
noncomputable def blockMatrixFlat {m r : ℕ}
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ)) :
    Matrix (Fin m × Fin r) (Fin m × Fin r) ℝ :=
  fun is jt => A is.1 jt.1 is.2 jt.2

/-- Flatten a uniform block matrix to the standard `Fin (m*r)` square index.

    This is the same scalar matrix as `blockMatrixFlat`, reindexed through
    Mathlib's `finProdFinEquiv`.  It is useful when a later max-entry growth
    theorem is stated with the repository's `Fin n` matrix convention. -/
noncomputable def blockMatrixFlatFin {m r : ℕ}
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ)) :
    Matrix (Fin (m * r)) (Fin (m * r)) ℝ :=
  fun p q =>
    A (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm q).1
      (finProdFinEquiv.symm p).2 (finProdFinEquiv.symm q).2

@[simp] theorem blockMatrixFlatFin_apply {m r : ℕ}
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (i j : Fin m) (s t : Fin r) :
    blockMatrixFlatFin A (finProdFinEquiv (i, s)) (finProdFinEquiv (j, t)) =
      A i j s t := by
  simp [blockMatrixFlatFin]

/-- Flatten a uniformly blocked matrix of right-hand sides by stacking its
    block rows.  Unlike `blockMatrixFlatFin`, the column type is left generic;
    this is the representation used to turn the DHS per-block-row solve
    equations into one ordinary matrix equation. -/
noncomputable def blockMatrixRowsFlatFin {m r : ℕ} {p : Type*}
    (X : Fin m → Matrix (Fin r) p ℝ) : Matrix (Fin (m * r)) p ℝ :=
  fun is k =>
    X (finProdFinEquiv.symm is).1 (finProdFinEquiv.symm is).2 k

@[simp] theorem blockMatrixRowsFlatFin_apply {m r : ℕ} {p : Type*}
    (X : Fin m → Matrix (Fin r) p ℝ)
    (i : Fin m) (s : Fin r) (k : p) :
    blockMatrixRowsFlatFin X (finProdFinEquiv (i, s)) k = X i s k := by
  simp [blockMatrixRowsFlatFin]

/-- A diagonal block's max-entry norm is bounded by that of the full flattened
    block matrix. -/
theorem maxEntryNorm_diagonalBlock_le_blockMatrixFlatFin
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (i : Fin m) :
    maxEntryNorm hr (U i i) ≤
      maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin U) := by
  apply maxEntryNorm_le_of_entry_le_bound
  intro s t
  simpa using entry_le_maxEntryNorm (Nat.mul_pos hm hr)
    (blockMatrixFlatFin U) (finProdFinEquiv (i, s))
      (finProdFinEquiv (i, t))

/-- The masked strict-upper block row is an entrywise submatrix of the full
    flattened upper factor, so it needs no independent norm majorant. -/
theorem maxEntryNorm_upperTailRowFlat_le_blockMatrixFlatFin
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (U : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (i : Fin m) :
    maxEntryNormRect hr (Nat.mul_pos hm hr)
        (dhsBlockBackUpperTailRowFlat i (U i)) ≤
      maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin U) := by
  apply maxEntryNormRect_le_of_entry_abs_le
  intro s jt
  let q := finProdFinEquiv.symm jt
  have hjt : finProdFinEquiv q = jt := finProdFinEquiv.apply_symm_apply jt
  rw [← hjt, dhsBlockBackUpperTailRowFlat_apply]
  by_cases hiq : i.val < q.1.val
  · have hiq' : i.val < jt.val / r := by simpa [q] using hiq
    simpa [blockMatrixFlatFin, hiq'] using
      entry_le_maxEntryNorm (Nat.mul_pos hm hr)
        (blockMatrixFlatFin U) (finProdFinEquiv (i, s)) jt
  · have hiq' : ¬i.val < jt.val / r := by simpa [q] using hiq
    simp [hiq', maxEntryNorm_nonneg]

/-- A product of a flattened uniform block row with stacked right-hand sides
    is the scalar entry of the corresponding sum of block products.

    The two coefficient families are kept separate because the DHS row
    equation uses `Uhat + DeltaU`. -/
theorem blockMatrixFlatFin_add_mul_blockMatrixRowsFlatFin_apply
    {m r : ℕ} {p : Type*}
    (A B : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X : Fin m → Matrix (Fin r) p ℝ)
    (i : Fin m) (s : Fin r) (k : p) :
    (∑ jt : Fin (m * r),
      (blockMatrixFlatFin A (finProdFinEquiv (i, s)) jt +
          blockMatrixFlatFin B (finProdFinEquiv (i, s)) jt) *
        blockMatrixRowsFlatFin X jt k) =
      ∑ j : Fin m, ((A i j + B i j) * X j) s k := by
  calc
    (∑ jt : Fin (m * r),
      (blockMatrixFlatFin A (finProdFinEquiv (i, s)) jt +
          blockMatrixFlatFin B (finProdFinEquiv (i, s)) jt) *
        blockMatrixRowsFlatFin X jt k) =
        ∑ jt : Fin m × Fin r,
          (A i jt.1 s jt.2 + B i jt.1 s jt.2) * X jt.1 jt.2 k := by
      rw [Fintype.sum_equiv finProdFinEquiv]
      intro jt
      rw [blockMatrixFlatFin_apply, blockMatrixFlatFin_apply,
        blockMatrixRowsFlatFin_apply]
    _ = ∑ j : Fin m, ∑ t : Fin r,
          (A i j s t + B i j s t) * X j t k := by
      rw [Fintype.sum_prod_type]
    _ = ∑ j : Fin m, ((A i j + B i j) * X j) s k := by
      simp [Matrix.mul_apply]

/-- The product-index and `Fin (m*r)` flattenings have the same determinant,
    because they are simultaneous row/column reindexings of the same scalar
    block matrix. -/
theorem det_blockMatrixFlat_eq_blockMatrixFlatFin {m r : ℕ}
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ)) :
    Matrix.det (blockMatrixFlat A :
      Matrix (Fin m × Fin r) (Fin m × Fin r) ℝ) =
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin (m * r)) (Fin (m * r)) ℝ) := by
  have hflat :
      blockMatrixFlat A =
        (blockMatrixFlatFin A).submatrix finProdFinEquiv finProdFinEquiv := by
    ext is jt
    rcases is with ⟨i, s⟩
    rcases jt with ⟨j, t⟩
    simp [blockMatrixFlat, blockMatrixFlatFin]
  rw [hflat]
  simpa [Matrix.submatrix] using
    (Matrix.det_submatrix_equiv_self
      (finProdFinEquiv : Fin m × Fin r ≃ Fin (m * r))
      (blockMatrixFlatFin A :
        Matrix (Fin (m * r)) (Fin (m * r)) ℝ))

lemma maxEntryNorm_blockMatrixFlatFin_le_blockMaxNorm {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ)) :
    maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A) ≤
      blockMaxNorm hm hr A := by
  have hrect :
      maxEntryNormRect (Nat.mul_pos hm hr) (Nat.mul_pos hm hr)
          (blockMatrixFlatFin A) ≤
        blockMaxNorm hm hr A := by
    apply maxEntryNormRect_le_of_entry_abs_le
    intro p q
    simpa [blockMatrixFlatFin] using
      block_entry_abs_le_blockMaxNorm hm hr A
        (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm q).1
        (finProdFinEquiv.symm p).2 (finProdFinEquiv.symm q).2
  simpa [maxEntryNormRect_eq_maxEntryNorm (Nat.mul_pos hm hr)] using hrect

lemma blockMaxNorm_le_maxEntryNorm_blockMatrixFlatFin {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ)) :
    blockMaxNorm hm hr A ≤
      maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A) := by
  apply blockMaxNorm_le_of_entry_abs_le
  intro i j s t
  have hentry :=
    entry_le_maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A)
      (finProdFinEquiv (i, s)) (finProdFinEquiv (j, t))
  simpa [blockMatrixFlatFin] using hentry

/-- Reindexing a block matrix from block/product indices to `Fin (m*r)`
    preserves Higham Chapter 13's entrywise max norm. -/
theorem maxEntryNorm_blockMatrixFlatFin_eq_blockMaxNorm {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ)) :
    maxEntryNorm (Nat.mul_pos hm hr) (blockMatrixFlatFin A) =
      blockMaxNorm hm hr A := by
  exact le_antisymm
    (maxEntryNorm_blockMatrixFlatFin_le_blockMaxNorm hm hr A)
    (blockMaxNorm_le_maxEntryNorm_blockMatrixFlatFin hm hr A)

/-- Flatten a `(m+1) × (m+1)` uniform block matrix along the first block
    split, producing the scalar matrix indexed by `Fin (r + m*r)`.

    The left summand is the first block row/column and the right summand is
    the remaining `m` block rows/columns, flattened through
    `finProdFinEquiv`.  This is the shape used by the local two-by-two Schur
    split in Problem 13.4. -/
noncomputable def blockMatrixFirstSplitFlat {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ)) :
    Matrix (Fin (r + m * r)) (Fin (r + m * r)) ℝ :=
  fun p q =>
    match finSumFinEquiv.symm p, finSumFinEquiv.symm q with
    | Sum.inl s, Sum.inl t => A 0 0 s t
    | Sum.inl s, Sum.inr qt =>
        let jt := finProdFinEquiv.symm qt
        A 0 (Fin.succ jt.1) s jt.2
    | Sum.inr ip, Sum.inl t =>
        let is := finProdFinEquiv.symm ip
        A (Fin.succ is.1) 0 is.2 t
    | Sum.inr ip, Sum.inr qt =>
        let is := finProdFinEquiv.symm ip
        let jt := finProdFinEquiv.symm qt
        A (Fin.succ is.1) (Fin.succ jt.1) is.2 jt.2

@[simp] theorem blockMatrixFirstSplitFlat_11 {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ))
    (s t : Fin r) :
    blockMatrixFirstSplitFlat A
        (finSumFinEquiv (Sum.inl s : Fin r ⊕ Fin (m * r)))
        (finSumFinEquiv (Sum.inl t : Fin r ⊕ Fin (m * r))) =
      A 0 0 s t := by
  simp [blockMatrixFirstSplitFlat]

@[simp] theorem blockMatrixFirstSplitFlat_12 {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ))
    (s : Fin r) (j : Fin m) (t : Fin r) :
    blockMatrixFirstSplitFlat A
        (finSumFinEquiv (Sum.inl s : Fin r ⊕ Fin (m * r)))
        (finSumFinEquiv (Sum.inr (finProdFinEquiv (j, t)) : Fin r ⊕ Fin (m * r))) =
      A 0 (Fin.succ j) s t := by
  simp [blockMatrixFirstSplitFlat]

@[simp] theorem blockMatrixFirstSplitFlat_21 {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ))
    (i : Fin m) (s : Fin r) (t : Fin r) :
    blockMatrixFirstSplitFlat A
        (finSumFinEquiv (Sum.inr (finProdFinEquiv (i, s)) : Fin r ⊕ Fin (m * r)))
        (finSumFinEquiv (Sum.inl t : Fin r ⊕ Fin (m * r))) =
      A (Fin.succ i) 0 s t := by
  simp [blockMatrixFirstSplitFlat]

@[simp] theorem blockMatrixFirstSplitFlat_22 {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ))
    (i j : Fin m) (s t : Fin r) :
    blockMatrixFirstSplitFlat A
        (finSumFinEquiv (Sum.inr (finProdFinEquiv (i, s)) : Fin r ⊕ Fin (m * r)))
        (finSumFinEquiv (Sum.inr (finProdFinEquiv (j, t)) : Fin r ⊕ Fin (m * r))) =
      A (Fin.succ i) (Fin.succ j) s t := by
  simp [blockMatrixFirstSplitFlat]

/-- The leading `r × r` scalar block in the first-split flattening. -/
noncomputable def blockMatrixFirstSplitA11 {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ)) :
    Matrix (Fin r) (Fin r) ℝ :=
  A 0 0

/-- The top-right scalar block row in the first-split flattening. -/
noncomputable def blockMatrixFirstSplitA12 {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ)) :
    Matrix (Fin r) (Fin (m * r)) ℝ :=
  fun i q =>
    let jq := finProdFinEquiv.symm q
    A 0 (Fin.succ jq.1) i jq.2

/-- The bottom-left scalar block column in the first-split flattening. -/
noncomputable def blockMatrixFirstSplitA21 {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ)) :
    Matrix (Fin (m * r)) (Fin r) ℝ :=
  fun p j =>
    let ip := finProdFinEquiv.symm p
    A (Fin.succ ip.1) 0 ip.2 j

/-- The trailing scalar block matrix in the first-split flattening. -/
noncomputable def blockMatrixFirstSplitA22 {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ)) :
    Matrix (Fin (m * r)) (Fin (m * r)) ℝ :=
  blockMatrixFlatFin (fun i j => A (Fin.succ i) (Fin.succ j))

lemma maxEntryNorm_blockMatrixFirstSplitFlat_le_blockMaxNorm {m r : ℕ}
    (_hm : 0 < m) (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ)) :
    maxEntryNorm (Nat.add_pos_left hr (m * r)) (blockMatrixFirstSplitFlat A) ≤
      blockMaxNorm (Nat.succ_pos m) hr A := by
  have hrect :
      maxEntryNormRect (Nat.add_pos_left hr (m * r)) (Nat.add_pos_left hr (m * r))
          (blockMatrixFirstSplitFlat A) ≤
        blockMaxNorm (Nat.succ_pos m) hr A := by
    apply maxEntryNormRect_le_of_entry_abs_le
    intro p q
    cases hp : finSumFinEquiv.symm p with
    | inl s =>
        cases hq : finSumFinEquiv.symm q with
        | inl t =>
            simpa [blockMatrixFirstSplitFlat, hp, hq] using
              block_entry_abs_le_blockMaxNorm (Nat.succ_pos m) hr A 0 0 s t
        | inr qt =>
            let jt := finProdFinEquiv.symm qt
            simpa [blockMatrixFirstSplitFlat, hp, hq, jt] using
              block_entry_abs_le_blockMaxNorm (Nat.succ_pos m) hr A
                0 (Fin.succ jt.1) s jt.2
    | inr ip =>
        let is := finProdFinEquiv.symm ip
        cases hq : finSumFinEquiv.symm q with
        | inl t =>
            simpa [blockMatrixFirstSplitFlat, hp, hq, is] using
              block_entry_abs_le_blockMaxNorm (Nat.succ_pos m) hr A
                (Fin.succ is.1) 0 is.2 t
        | inr qt =>
            let jt := finProdFinEquiv.symm qt
            simpa [blockMatrixFirstSplitFlat, hp, hq, is, jt] using
              block_entry_abs_le_blockMaxNorm (Nat.succ_pos m) hr A
                (Fin.succ is.1) (Fin.succ jt.1) is.2 jt.2
  simpa [maxEntryNormRect_eq_maxEntryNorm (Nat.add_pos_left hr (m * r))]
    using hrect

lemma maxEntryNorm_blockMatrixFirstSplitFlat_le_blockMaxNorm_of_hN {m r : ℕ}
    (hN : 0 < r + m * r) (_hm : 0 < m) (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ)) :
    maxEntryNorm hN (blockMatrixFirstSplitFlat A) ≤
        blockMaxNorm (Nat.succ_pos m) hr A := by
  have hrect :
      maxEntryNormRect hN hN (blockMatrixFirstSplitFlat A) ≤
        blockMaxNorm (Nat.succ_pos m) hr A := by
    apply maxEntryNormRect_le_of_entry_abs_le
    intro p q
    cases hp : finSumFinEquiv.symm p with
    | inl s =>
        cases hq : finSumFinEquiv.symm q with
        | inl t =>
            simpa [blockMatrixFirstSplitFlat, hp, hq] using
              block_entry_abs_le_blockMaxNorm (Nat.succ_pos m) hr A 0 0 s t
        | inr qt =>
            let jt := finProdFinEquiv.symm qt
            simpa [blockMatrixFirstSplitFlat, hp, hq, jt] using
              block_entry_abs_le_blockMaxNorm (Nat.succ_pos m) hr A
                0 (Fin.succ jt.1) s jt.2
    | inr ip =>
        let is := finProdFinEquiv.symm ip
        cases hq : finSumFinEquiv.symm q with
        | inl t =>
            simpa [blockMatrixFirstSplitFlat, hp, hq, is] using
              block_entry_abs_le_blockMaxNorm (Nat.succ_pos m) hr A
                (Fin.succ is.1) 0 is.2 t
        | inr qt =>
            let jt := finProdFinEquiv.symm qt
            simpa [blockMatrixFirstSplitFlat, hp, hq, is, jt] using
              block_entry_abs_le_blockMaxNorm (Nat.succ_pos m) hr A
                (Fin.succ is.1) (Fin.succ jt.1) is.2 jt.2
  simpa [maxEntryNormRect_eq_maxEntryNorm hN] using hrect

/-- The first-split scalar flattening contains every block entry of `A`. -/
lemma blockMaxNorm_le_maxEntryNorm_blockMatrixFirstSplitFlat {m r : ℕ}
    (_hm : 0 < m) (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ)) :
    blockMaxNorm (Nat.succ_pos m) hr A ≤
      maxEntryNorm (Nat.add_pos_left hr (m * r)) (blockMatrixFirstSplitFlat A) := by
  apply blockMaxNorm_le_of_entry_abs_le
  intro i j s t
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      have hentry :=
        entry_le_maxEntryNorm (Nat.add_pos_left hr (m * r))
          (blockMatrixFirstSplitFlat A)
          (finSumFinEquiv (Sum.inl s : Fin r ⊕ Fin (m * r)))
          (finSumFinEquiv (Sum.inl t : Fin r ⊕ Fin (m * r)))
      rw [blockMatrixFirstSplitFlat_11 A s t] at hentry
      exact hentry
    · have hentry :=
        entry_le_maxEntryNorm (Nat.add_pos_left hr (m * r))
          (blockMatrixFirstSplitFlat A)
          (finSumFinEquiv (Sum.inl s : Fin r ⊕ Fin (m * r)))
          (finSumFinEquiv
            (Sum.inr (finProdFinEquiv (j.pred hj, t)) : Fin r ⊕ Fin (m * r)))
      rw [blockMatrixFirstSplitFlat_12 A s (j.pred hj) t] at hentry
      simpa [Fin.succ_pred j hj] using hentry
  · by_cases hj : j = 0
    · subst j
      have hentry :=
        entry_le_maxEntryNorm (Nat.add_pos_left hr (m * r))
          (blockMatrixFirstSplitFlat A)
          (finSumFinEquiv
            (Sum.inr (finProdFinEquiv (i.pred hi, s)) : Fin r ⊕ Fin (m * r)))
          (finSumFinEquiv (Sum.inl t : Fin r ⊕ Fin (m * r)))
      rw [blockMatrixFirstSplitFlat_21 A (i.pred hi) s t] at hentry
      simpa [Fin.succ_pred i hi] using hentry
    · have hentry :=
        entry_le_maxEntryNorm (Nat.add_pos_left hr (m * r))
          (blockMatrixFirstSplitFlat A)
          (finSumFinEquiv
            (Sum.inr (finProdFinEquiv (i.pred hi, s)) : Fin r ⊕ Fin (m * r)))
          (finSumFinEquiv
            (Sum.inr (finProdFinEquiv (j.pred hj, t)) : Fin r ⊕ Fin (m * r)))
      rw [blockMatrixFirstSplitFlat_22 A (i.pred hi) (j.pred hj) s t] at hentry
      simpa [Fin.succ_pred i hi, Fin.succ_pred j hj] using hentry

/-- The first-split scalar flattening has exactly the block max norm. -/
theorem maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMaxNorm {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ)) :
    maxEntryNorm (Nat.add_pos_left hr (m * r)) (blockMatrixFirstSplitFlat A) =
      blockMaxNorm (Nat.succ_pos m) hr A := by
  exact le_antisymm
    (maxEntryNorm_blockMatrixFirstSplitFlat_le_blockMaxNorm hm hr A)
    (blockMaxNorm_le_maxEntryNorm_blockMatrixFirstSplitFlat hm hr A)

/-- The first-split flattening and the uniform flat block matrix have the same
    Chapter 13 max-entry norm. -/
theorem maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → (Fin r → Fin r → ℝ)) :
    maxEntryNorm (Nat.add_pos_left hr (m * r)) (blockMatrixFirstSplitFlat A) =
      maxEntryNorm (Nat.mul_pos (Nat.succ_pos m) hr) (blockMatrixFlatFin A) := by
  rw [maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMaxNorm hm hr A]
  rw [maxEntryNorm_blockMatrixFlatFin_eq_blockMaxNorm (Nat.succ_pos m) hr A]

/-- Reindex the first-split scalar ordering `Fin (r + m*r)` to the uniform
    block/product ordering `Fin (m+1) × Fin r`. -/
noncomputable def blockMatrixFirstSplitToFlatProductEquiv {m r : ℕ} :
    Fin (r + m * r) ≃ Fin (m + 1) × Fin r where
  toFun p :=
    match finSumFinEquiv.symm p with
    | Sum.inl s => (0, s)
    | Sum.inr q =>
        let jq := finProdFinEquiv.symm q
        (Fin.succ jq.1, jq.2)
  invFun is :=
    if hi : is.1 = 0 then
      finSumFinEquiv (Sum.inl is.2 : Fin r ⊕ Fin (m * r))
    else
      finSumFinEquiv
        (Sum.inr (finProdFinEquiv (is.1.pred hi, is.2)) :
          Fin r ⊕ Fin (m * r))
  left_inv := by
    intro p
    cases hp : finSumFinEquiv.symm p with
    | inl s =>
        dsimp
        rw [hp]
        simp
        have hp' :
            finSumFinEquiv (Sum.inl s : Fin r ⊕ Fin (m * r)) = p := by
          rw [← hp]
          exact finSumFinEquiv.apply_symm_apply p
        simpa using hp'
    | inr q =>
        dsimp
        rw [hp]
        simp
        have hq : finProdFinEquiv (q.divNat, q.modNat) = q := by
          exact finProdFinEquiv.apply_symm_apply q
        have hp' :
            finSumFinEquiv (Sum.inr q : Fin r ⊕ Fin (m * r)) = p := by
          rw [← hp]
          exact finSumFinEquiv.apply_symm_apply p
        simpa [hq] using hp'
  right_inv := by
    intro is
    rcases is with ⟨i, s⟩
    by_cases hi : i = 0
    · subst i
      dsimp
      simp
    · have hsucc : Fin.succ (i.pred hi) = i := Fin.succ_pred i hi
      dsimp
      simp [hi]
      constructor
      · have hpair :
            finProdFinEquiv.symm (finProdFinEquiv (i.pred hi, s)) =
              (i.pred hi, s) :=
          finProdFinEquiv.symm_apply_apply (i.pred hi, s)
        have hfst := congrArg Prod.fst hpair
        change (finProdFinEquiv (i.pred hi, s)).divNat = i.pred hi at hfst
        rw [hfst, hsucc]
      · have hpair :
            finProdFinEquiv.symm (finProdFinEquiv (i.pred hi, s)) =
              (i.pred hi, s) :=
          finProdFinEquiv.symm_apply_apply (i.pred hi, s)
        have hsnd := congrArg Prod.snd hpair
        change (finProdFinEquiv (i.pred hi, s)).modNat = s at hsnd
        exact hsnd

/-- Reindex the first-split scalar ordering `Fin (r + m*r)` to the uniform
    flat ordering `Fin ((m+1)*r)`. -/
noncomputable def blockMatrixFirstSplitToFlatFinEquiv {m r : ℕ} :
    Fin (r + m * r) ≃ Fin ((m + 1) * r) :=
  blockMatrixFirstSplitToFlatProductEquiv.trans finProdFinEquiv

@[simp] theorem blockMatrixFirstSplitToFlatFinEquiv_inl {m r : ℕ}
    (s : Fin r) :
    (blockMatrixFirstSplitToFlatFinEquiv
        (finSumFinEquiv (Sum.inl s : Fin r ⊕ Fin (m * r))) :
      Fin ((m + 1) * r)) =
      finProdFinEquiv ((0 : Fin (m + 1)), s) := by
  dsimp [blockMatrixFirstSplitToFlatFinEquiv, blockMatrixFirstSplitToFlatProductEquiv]
  simp

@[simp] theorem blockMatrixFirstSplitToFlatFinEquiv_inr {m r : ℕ}
    (j : Fin m) (t : Fin r) :
    (blockMatrixFirstSplitToFlatFinEquiv
        (finSumFinEquiv
          (Sum.inr (finProdFinEquiv (j, t)) : Fin r ⊕ Fin (m * r))) :
      Fin ((m + 1) * r)) =
      finProdFinEquiv (Fin.succ j, t) := by
  dsimp [blockMatrixFirstSplitToFlatFinEquiv, blockMatrixFirstSplitToFlatProductEquiv]
  have hpair :
      finProdFinEquiv.symm (finProdFinEquiv (j, t)) = (j, t) :=
    finProdFinEquiv.symm_apply_apply (j, t)
  have hfst := congrArg Prod.fst hpair
  have hsnd := congrArg Prod.snd hpair
  change (finProdFinEquiv (j, t)).divNat = j at hfst
  change (finProdFinEquiv (j, t)).modNat = t at hsnd
  rw [finSumFinEquiv_symm_apply_natAdd]
  change finProdFinEquiv
      ((finProdFinEquiv (j, t)).divNat.succ,
        (finProdFinEquiv (j, t)).modNat) =
    finProdFinEquiv (Fin.succ j, t)
  rw [hfst, hsnd]

/-- The first-split flattening is the uniform flat block matrix reindexed by
    `blockMatrixFirstSplitToFlatFinEquiv`. -/
theorem blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin_reindex {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ) :
    blockMatrixFirstSplitFlat A =
      fun p q : Fin (r + m * r) =>
        blockMatrixFlatFin A (blockMatrixFirstSplitToFlatFinEquiv p)
          (blockMatrixFirstSplitToFlatFinEquiv q) := by
  ext p q
  cases hp : finSumFinEquiv.symm p with
  | inl s =>
      cases hq : finSumFinEquiv.symm q with
      | inl t =>
          have hp' :
              p = finSumFinEquiv (Sum.inl s : Fin r ⊕ Fin (m * r)) := by
            rw [← hp]
            exact (finSumFinEquiv.apply_symm_apply p).symm
          have hq' :
              q = finSumFinEquiv (Sum.inl t : Fin r ⊕ Fin (m * r)) := by
            rw [← hq]
            exact (finSumFinEquiv.apply_symm_apply q).symm
          rw [hp', hq']
          rw [blockMatrixFirstSplitFlat_11]
          rw [blockMatrixFirstSplitToFlatFinEquiv_inl,
            blockMatrixFirstSplitToFlatFinEquiv_inl]
          rw [blockMatrixFlatFin_apply]
      | inr qt =>
          let jt := finProdFinEquiv.symm qt
          have hp' :
              p = finSumFinEquiv (Sum.inl s : Fin r ⊕ Fin (m * r)) := by
            rw [← hp]
            exact (finSumFinEquiv.apply_symm_apply p).symm
          have hq' :
              q = finSumFinEquiv (Sum.inr qt : Fin r ⊕ Fin (m * r)) := by
            rw [← hq]
            exact (finSumFinEquiv.apply_symm_apply q).symm
          have hqt : finProdFinEquiv (jt.1, jt.2) = qt := by
            exact finProdFinEquiv.apply_symm_apply qt
          rw [hp', hq', ← hqt]
          rw [blockMatrixFirstSplitFlat_12]
          rw [blockMatrixFirstSplitToFlatFinEquiv_inl,
            blockMatrixFirstSplitToFlatFinEquiv_inr]
          rw [blockMatrixFlatFin_apply]
  | inr ip =>
      let is := finProdFinEquiv.symm ip
      cases hq : finSumFinEquiv.symm q with
      | inl t =>
          have hip : finProdFinEquiv (is.1, is.2) = ip := by
            exact finProdFinEquiv.apply_symm_apply ip
          have hp' :
              p = finSumFinEquiv (Sum.inr ip : Fin r ⊕ Fin (m * r)) := by
            rw [← hp]
            exact (finSumFinEquiv.apply_symm_apply p).symm
          have hq' :
              q = finSumFinEquiv (Sum.inl t : Fin r ⊕ Fin (m * r)) := by
            rw [← hq]
            exact (finSumFinEquiv.apply_symm_apply q).symm
          rw [hp', hq', ← hip]
          rw [blockMatrixFirstSplitFlat_21]
          rw [blockMatrixFirstSplitToFlatFinEquiv_inr,
            blockMatrixFirstSplitToFlatFinEquiv_inl]
          rw [blockMatrixFlatFin_apply]
      | inr qt =>
          let jt := finProdFinEquiv.symm qt
          have hip : finProdFinEquiv (is.1, is.2) = ip := by
            exact finProdFinEquiv.apply_symm_apply ip
          have hqt : finProdFinEquiv (jt.1, jt.2) = qt := by
            exact finProdFinEquiv.apply_symm_apply qt
          have hp' :
              p = finSumFinEquiv (Sum.inr ip : Fin r ⊕ Fin (m * r)) := by
            rw [← hp]
            exact (finSumFinEquiv.apply_symm_apply p).symm
          have hq' :
              q = finSumFinEquiv (Sum.inr qt : Fin r ⊕ Fin (m * r)) := by
            rw [← hq]
            exact (finSumFinEquiv.apply_symm_apply q).symm
          rw [hp', hq', ← hip, ← hqt]
          rw [blockMatrixFirstSplitFlat_22]
          rw [blockMatrixFirstSplitToFlatFinEquiv_inr,
            blockMatrixFirstSplitToFlatFinEquiv_inr]
          rw [blockMatrixFlatFin_apply]

/-- First-split flattening preserves invertibility from the uniform flat
    block-matrix representation. -/
noncomputable def blockMatrixFirstSplitFlat_invertible_of_blockMatrixFlatFin
    {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    [Invertible (blockMatrixFlatFin A)] :
    Invertible (blockMatrixFirstSplitFlat A) := by
  classical
  let M : Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ :=
    blockMatrixFlatFin A
  let e : Fin (r + m * r) ≃ Fin ((m + 1) * r) :=
    blockMatrixFirstSplitToFlatFinEquiv
  letI : Invertible (M.submatrix e e) :=
    Matrix.submatrixEquivInvertible M e e
  rw [blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin_reindex A]
  exact (inferInstance : Invertible (M.submatrix e e))

/-- The `Matrix.fromBlocks` view of a first-split block matrix preserves
    invertibility from the scalar first-split flattening. -/
noncomputable def blockMatrixFirstSplit_fromBlocks_invertible_of_blockMatrixFirstSplitFlat
    {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    [Invertible (blockMatrixFirstSplitFlat A)] :
    Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 A)
      (blockMatrixFirstSplitA12 A)
      (blockMatrixFirstSplitA21 A)
      (blockMatrixFirstSplitA22 A)) := by
  classical
  let M : Matrix (Fin (r + m * r)) (Fin (r + m * r)) ℝ :=
    blockMatrixFirstSplitFlat A
  let e : Fin r ⊕ Fin (m * r) ≃ Fin (r + m * r) := finSumFinEquiv
  letI : Invertible (M.submatrix e e) :=
    Matrix.submatrixEquivInvertible M e e
  suffices
      Matrix.fromBlocks
          (blockMatrixFirstSplitA11 A)
          (blockMatrixFirstSplitA12 A)
          (blockMatrixFirstSplitA21 A)
          (blockMatrixFirstSplitA22 A) =
        M.submatrix e e by
    simpa [this] using (inferInstance : Invertible (M.submatrix e e))
  ext i j
  cases i with
  | inl s =>
      cases j with
      | inl t =>
          simpa [M, e, Fin.castAdd, blockMatrixFirstSplitA11] using
            (blockMatrixFirstSplitFlat_11 A s t).symm
      | inr q =>
          let jq := finProdFinEquiv.symm q
          have hq : finProdFinEquiv jq = q := finProdFinEquiv.apply_symm_apply q
          rw [← hq]
          simpa [M, e, Fin.castAdd, Fin.natAdd, blockMatrixFirstSplitA12] using
            (blockMatrixFirstSplitFlat_12 A s jq.1 jq.2).symm
  | inr p =>
      cases j with
      | inl t =>
          let ip := finProdFinEquiv.symm p
          have hp : finProdFinEquiv ip = p := finProdFinEquiv.apply_symm_apply p
          rw [← hp]
          simpa [M, e, Fin.castAdd, Fin.natAdd, blockMatrixFirstSplitA21] using
            (blockMatrixFirstSplitFlat_21 A ip.1 ip.2 t).symm
      | inr q =>
          let ip := finProdFinEquiv.symm p
          let jq := finProdFinEquiv.symm q
          have hp : finProdFinEquiv ip = p := finProdFinEquiv.apply_symm_apply p
          have hq : finProdFinEquiv jq = q := finProdFinEquiv.apply_symm_apply q
          rw [← hp, ← hq]
          change
            blockMatrixFirstSplitA22 A (finProdFinEquiv ip) (finProdFinEquiv jq) =
              blockMatrixFirstSplitFlat A
                (finSumFinEquiv
                  (Sum.inr (finProdFinEquiv ip) : Fin r ⊕ Fin (m * r)))
                (finSumFinEquiv
                  (Sum.inr (finProdFinEquiv jq) : Fin r ⊕ Fin (m * r)))
          rw [blockMatrixFirstSplitA22, blockMatrixFlatFin_apply]
          exact (blockMatrixFirstSplitFlat_22 A ip.1 jq.1 ip.2 jq.2).symm

/-- The `Matrix.fromBlocks` view of a first-split block matrix preserves
    invertibility from the uniform flat block-matrix representation. -/
noncomputable def blockMatrixFirstSplit_fromBlocks_invertible_of_blockMatrixFlatFin
    {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    [Invertible (blockMatrixFlatFin A)] :
    Invertible (Matrix.fromBlocks
      (blockMatrixFirstSplitA11 A)
      (blockMatrixFirstSplitA12 A)
      (blockMatrixFirstSplitA21 A)
      (blockMatrixFirstSplitA22 A)) := by
  classical
  letI : Invertible (blockMatrixFirstSplitFlat A) :=
    blockMatrixFirstSplitFlat_invertible_of_blockMatrixFlatFin A
  exact blockMatrixFirstSplit_fromBlocks_invertible_of_blockMatrixFirstSplitFlat A

/-- The first-split inverse has max-entry norm bounded by the uniform-flat
    canonical inverse of the same block matrix. -/
theorem maxEntryNormRect_nonsingInv_blockMatrixFirstSplitFlat_le_blockMatrixFlatFin
    {m r : ℕ} (hr : 0 < r)
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    [Invertible (blockMatrixFirstSplitFlat A)] :
    maxEntryNormRect (Nat.add_pos_left hr (m * r)) (Nat.add_pos_left hr (m * r))
        (nonsingInv (r + m * r) (blockMatrixFirstSplitFlat A)) ≤
      maxEntryNormRect (Nat.mul_pos (Nat.succ_pos m) hr)
        (Nat.mul_pos (Nat.succ_pos m) hr)
        (nonsingInv ((m + 1) * r) (blockMatrixFlatFin A)) := by
  apply maxEntryNormRect_le_of_entry_abs_le
  intro i j
  have hEqInv :
      nonsingInv (r + m * r) (blockMatrixFirstSplitFlat A) =
        fun i j : Fin (r + m * r) =>
          (⅟(blockMatrixFirstSplitFlat A :
            Matrix (Fin (r + m * r)) (Fin (r + m * r)) ℝ)) i j := by
    exact
      nonsingInv_eq_of_isRightInverse
        (blockMatrixFirstSplitFlat A)
        (fun i j : Fin (r + m * r) =>
          (⅟(blockMatrixFirstSplitFlat A :
            Matrix (Fin (r + m * r)) (Fin (r + m * r)) ℝ)) i j)
        (isRightInverse_of_eq_invOf
          (blockMatrixFirstSplitFlat A)
          (⅟(blockMatrixFirstSplitFlat A :
            Matrix (Fin (r + m * r)) (Fin (r + m * r)) ℝ))
          rfl)
  rw [hEqInv]
  exact
    maxEntryNormRect_invOf_reindex_equiv_nonsingInv_entry_bound
      (Nat.mul_pos (Nat.succ_pos m) hr)
      (blockMatrixFirstSplitToFlatFinEquiv : Fin (r + m * r) ≃ Fin ((m + 1) * r))
      (blockMatrixFlatFin A)
      (blockMatrixFirstSplitFlat A)
      (blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin_reindex A)
      i j

/-- Higham, 2nd ed., Chapter 13, SPD/block-LU existence dependency:
    a two-sided inverse for the flattened block matrix gives the chapter's
    explicit block-matrix nonsingularity predicate.

    This theorem is only a representation bridge; determinant or SPD facts
    still have to supply the flattened inverse or nonsingularity premise. -/
theorem blockMatrixNonsingular_of_flat_inverse {m r : ℕ}
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (AinvFlat : Matrix (Fin m × Fin r) (Fin m × Fin r) ℝ)
    (hLeft : AinvFlat * blockMatrixFlat A = 1)
    (hRight : blockMatrixFlat A * AinvFlat = 1) :
    BlockMatrixNonsingular A := by
  let Ainv : Fin m → Fin m → (Fin r → Fin r → ℝ) :=
    fun i j s t => AinvFlat (i, s) (j, t)
  refine ⟨Ainv, ?_, ?_⟩
  · intro i j s t
    have h := congr_fun (congr_fun hLeft (i, s)) (j, t)
    have hId :
        blockMatrixIdentity m r i j s t =
          if (i, s) = (j, t) then 1 else 0 := by
      by_cases hij : i = j <;> by_cases hst : s = t <;>
        simp [blockMatrixIdentity, idBlock, zeroBlock, hij, hst, Prod.ext_iff]
    simpa [Ainv, blockMatrixFlat, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.one_apply, hId] using h
  · intro i j s t
    have h := congr_fun (congr_fun hRight (i, s)) (j, t)
    have hId :
        blockMatrixIdentity m r i j s t =
          if (i, s) = (j, t) then 1 else 0 := by
      by_cases hij : i = j <;> by_cases hst : s = t <;>
        simp [blockMatrixIdentity, idBlock, zeroBlock, hij, hst, Prod.ext_iff]
    simpa [Ainv, blockMatrixFlat, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.one_apply, hId] using h

/-- Higham, 2nd ed., Chapter 13, SPD/block-LU existence dependency:
    determinant nonsingularity of the flattened block matrix gives the
    chapter's block-matrix nonsingularity predicate. -/
theorem blockMatrixNonsingular_of_isUnit_det_flat {m r : ℕ}
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (hdet : IsUnit (Matrix.det (blockMatrixFlat A))) :
    BlockMatrixNonsingular A := by
  exact blockMatrixNonsingular_of_flat_inverse A (blockMatrixFlat A)⁻¹
    (Matrix.nonsing_inv_mul (blockMatrixFlat A) hdet)
    (Matrix.mul_nonsing_inv (blockMatrixFlat A) hdet)

/-- Higham, 2nd ed., Chapter 13, SPD/block-LU existence dependency:
    nonzero determinant of the flattened block matrix gives block-matrix
    nonsingularity over `ℝ`. -/
theorem blockMatrixNonsingular_of_det_ne_zero_flat {m r : ℕ}
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (hdet : Matrix.det (blockMatrixFlat A) ≠ 0) :
    BlockMatrixNonsingular A :=
  blockMatrixNonsingular_of_isUnit_det_flat A (isUnit_iff_ne_zero.mpr hdet)

/-- A block matrix with an explicit two-sided block inverse has nonzero
    determinant after flattening.  This is the converse determinant bridge to
    `blockMatrixNonsingular_of_det_ne_zero_flat`. -/
theorem blockMatrixFlat_det_ne_zero_of_blockMatrixNonsingular {m r : ℕ}
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (hA : BlockMatrixNonsingular A) :
    Matrix.det (blockMatrixFlat A) ≠ 0 := by
  classical
  rcases hA with ⟨Ainv, _hLeft, hRight⟩
  let AinvFlat : Matrix (Fin m × Fin r) (Fin m × Fin r) ℝ :=
    fun p q => Ainv p.1 q.1 p.2 q.2
  have hRightFlat : blockMatrixFlat A * AinvFlat = 1 := by
    ext p q
    rcases p with ⟨i, s⟩
    rcases q with ⟨j, t⟩
    have h := hRight i j s t
    have hId :
        blockMatrixIdentity m r i j s t =
          if (i, s) = (j, t) then 1 else 0 := by
      by_cases hij : i = j <;> by_cases hst : s = t <;>
        simp [blockMatrixIdentity, idBlock, zeroBlock, hij, hst, Prod.ext_iff]
    simpa [AinvFlat, blockMatrixFlat, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.one_apply, hId] using h
  exact Matrix.det_ne_zero_of_right_inverse hRightFlat

/-- A block-nonsingular matrix has nonzero determinant after uniform
    `Fin (m*r)` flattening. -/
theorem det_ne_zero_blockMatrixFlatFin_of_blockMatrixNonsingular {m r : ℕ}
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (hA : BlockMatrixNonsingular A) :
    Matrix.det (blockMatrixFlatFin A :
      Matrix (Fin (m * r)) (Fin (m * r)) ℝ) ≠ 0 := by
  rw [← det_blockMatrixFlat_eq_blockMatrixFlatFin A]
  exact blockMatrixFlat_det_ne_zero_of_blockMatrixNonsingular A hA

/-- Multiplication by a homogeneous block-diagonal matrix acts block-rowwise on
    the flattened `(within-block index, block index)` representation. -/
lemma blockDiagonal_mul_apply_block
    {ι r α : Type*} [DecidableEq ι] [Fintype r] [Fintype ι]
    [NonUnitalNonAssocSemiring α]
    (D : ι → Matrix r r α) (N : Matrix (r × ι) (r × ι) α)
    (s t : r) (i j : ι) :
    (Matrix.blockDiagonal D * N) (s, i) (t, j) =
      ∑ a : r, D i s a * N (a, i) (t, j) := by
  simp [Matrix.mul_apply, Matrix.blockDiagonal_apply, Fintype.sum_prod_type]

/-- The first-split scalar matrix has the same determinant as the uniform flat
    block matrix, because it is just a simultaneous row/column reindexing.

    This is the determinant side of the first-split/uniform-flat representation
    bridge used by the Problem 13.4 exact-κ route. -/
theorem det_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin
    {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ) :
    Matrix.det (blockMatrixFirstSplitFlat A :
      Matrix (Fin (r + m * r)) (Fin (r + m * r)) ℝ) =
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) := by
  rw [blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin_reindex A]
  simpa [Matrix.submatrix] using
    (Matrix.det_submatrix_equiv_self
      (blockMatrixFirstSplitToFlatFinEquiv :
        Fin (r + m * r) ≃ Fin ((m + 1) * r))
      (blockMatrixFlatFin A :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ))

/-- Determinant nonsingularity transports from the uniform flat block matrix
    to the first-split scalar matrix. -/
theorem det_ne_zero_blockMatrixFirstSplitFlat_of_blockMatrixFlatFin
    {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ)
    (hdet :
      Matrix.det (blockMatrixFlatFin A :
        Matrix (Fin ((m + 1) * r)) (Fin ((m + 1) * r)) ℝ) ≠ 0) :
    Matrix.det (blockMatrixFirstSplitFlat A :
      Matrix (Fin (r + m * r)) (Fin (r + m * r)) ℝ) ≠ 0 := by
  rw [det_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin A]
  exact hdet

/-- A matrix right-inverse certificate identifies the supplied inverse with
    Mathlib's `⅟` inverse for an `Invertible` matrix. -/
theorem matrix_invOf_eq_of_isRightInverse {r : ℕ}
    (A P : Matrix (Fin r) (Fin r) ℝ) [Invertible A]
    (hRight : IsRightInverse r A P) :
    P = ⅟A := by
  symm
  apply invOf_eq_right_inv
  ext i j
  simpa [Matrix.mul_apply] using hRight i j

/-- The determinant of the sum-indexed first-split block matrix agrees with
    the determinant of the uniform flattening of the same block matrix. -/
theorem det_blockMatrixFirstSplit_fromBlocks_eq_blockMatrixFlatFin
    {m r : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → Matrix (Fin r) (Fin r) ℝ) :
    Matrix.det (Matrix.fromBlocks
        (blockMatrixFirstSplitA11 A)
        (blockMatrixFirstSplitA12 A)
        (blockMatrixFirstSplitA21 A)
        (blockMatrixFirstSplitA22 A)) =
      Matrix.det (blockMatrixFlatFin A) := by
  classical
  let M : Matrix (Fin (r + m * r)) (Fin (r + m * r)) ℝ :=
    blockMatrixFirstSplitFlat A
  let e : Fin r ⊕ Fin (m * r) ≃ Fin (r + m * r) := finSumFinEquiv
  have hEq :
      Matrix.fromBlocks
          (blockMatrixFirstSplitA11 A)
          (blockMatrixFirstSplitA12 A)
          (blockMatrixFirstSplitA21 A)
          (blockMatrixFirstSplitA22 A) =
        M.submatrix e e := by
    ext i j
    cases i with
    | inl s =>
        cases j with
        | inl t =>
            simpa [M, e, Fin.castAdd, blockMatrixFirstSplitA11] using
              (blockMatrixFirstSplitFlat_11 A s t).symm
        | inr q =>
            let jq := finProdFinEquiv.symm q
            have hq : finProdFinEquiv jq = q := finProdFinEquiv.apply_symm_apply q
            rw [← hq]
            simpa [M, e, Fin.castAdd, Fin.natAdd, blockMatrixFirstSplitA12] using
              (blockMatrixFirstSplitFlat_12 A s jq.1 jq.2).symm
    | inr p =>
        cases j with
        | inl t =>
            let ip := finProdFinEquiv.symm p
            have hp : finProdFinEquiv ip = p := finProdFinEquiv.apply_symm_apply p
            rw [← hp]
            simpa [M, e, Fin.castAdd, Fin.natAdd, blockMatrixFirstSplitA21] using
              (blockMatrixFirstSplitFlat_21 A ip.1 ip.2 t).symm
        | inr q =>
            let ip := finProdFinEquiv.symm p
            let jq := finProdFinEquiv.symm q
            have hp : finProdFinEquiv ip = p := finProdFinEquiv.apply_symm_apply p
            have hq : finProdFinEquiv jq = q := finProdFinEquiv.apply_symm_apply q
            rw [← hp, ← hq]
            change
              blockMatrixFirstSplitA22 A (finProdFinEquiv ip) (finProdFinEquiv jq) =
                blockMatrixFirstSplitFlat A
                  (finSumFinEquiv
                    (Sum.inr (finProdFinEquiv ip) : Fin r ⊕ Fin (m * r)))
                  (finSumFinEquiv
                    (Sum.inr (finProdFinEquiv jq) : Fin r ⊕ Fin (m * r)))
            rw [blockMatrixFirstSplitA22, blockMatrixFlatFin_apply]
            exact (blockMatrixFirstSplitFlat_22 A ip.1 jq.1 ip.2 jq.2).symm
  calc
    Matrix.det (Matrix.fromBlocks
        (blockMatrixFirstSplitA11 A)
        (blockMatrixFirstSplitA12 A)
        (blockMatrixFirstSplitA21 A)
        (blockMatrixFirstSplitA22 A)) = Matrix.det M := by
          rw [hEq, Matrix.det_submatrix_equiv_self]
    _ = Matrix.det (blockMatrixFlatFin A) := by
      simpa [M] using det_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin A

end NumStability
