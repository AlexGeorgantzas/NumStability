import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum

/-!
# Block-matrix primitives for block LU

Reusable operations and norms for uniform block matrices
`Fin m → Fin m → (Fin r → Fin r → ℝ)`. The module defines identity and zero
blocks, block multiplication, block-matrix products, `blockMaxNorm`, and
`blockInfNorm`, with entrywise bounds and comparisons to the flattened
entrywise maximum norm.

This leaf contains source-independent block algebra; numbered Chapter 13
statements and recurrence constants live under `NumStability.Source.Higham`.
-/

namespace NumStability

open scoped BigOperators

/-- r×r identity block: I(s,t) = δ_{st}. -/
noncomputable def idBlock (r : ℕ) : Fin r → Fin r → ℝ :=
  fun s t => if s = t then 1 else 0

/-- r×r zero block. -/
noncomputable def zeroBlock (r : ℕ) : Fin r → Fin r → ℝ :=
  fun _ _ => 0

/-- The entrywise max norm of the zero block is zero. -/
lemma maxEntryNorm_zeroBlock {r : ℕ} (hr : 0 < r) :
    maxEntryNorm hr (zeroBlock r) = 0 := by
  apply le_antisymm
  · unfold maxEntryNorm zeroBlock
    apply Finset.sup'_le
    intro i _hi
    apply Finset.sup'_le
    intro j _hj
    simp
  · exact maxEntryNorm_nonneg hr (zeroBlock r)

/-- If a block is definitionally the zero block, its entrywise max norm is
    bounded by zero.  This is the norm-level form used for strict lower `U`
    blocks in the Eq.13.21 bridges. -/
lemma maxEntryNorm_le_zero_of_eq_zeroBlock {r : ℕ} (hr : 0 < r)
    {B : Fin r → Fin r → ℝ} (hB : B = zeroBlock r) :
    maxEntryNorm hr B ≤ 0 := by
  rw [hB, maxEntryNorm_zeroBlock hr]

/-- r×r block multiplication: (AB)(s,t) = ∑_l A(s,l) · B(l,t). -/
noncomputable def blockMul {r : ℕ} (A B : Fin r → Fin r → ℝ) :
    Fin r → Fin r → ℝ :=
  fun s t => ∑ l : Fin r, A s l * B l t

/-- Block matrix product: (AB)_{ij}(s,t) = ∑_k ∑_l A_{ik}(s,l) · B_{kj}(l,t). -/
noncomputable def blockMatProd {m r : ℕ}
    (A B : Fin m → Fin m → (Fin r → Fin r → ℝ)) :
    Fin m → Fin m → (Fin r → Fin r → ℝ) :=
  fun i j s t => ∑ k : Fin m, ∑ l : Fin r, A i k s l * B k j l t

/-- Entrywise max norm of the full block matrix (Chapter 13's convention):
    ‖A‖ := max_{i,j} maxEntryNorm(A_{ij}) = max_{i,j,s,t} |A_{ij}(s,t)|. -/
noncomputable def blockMaxNorm {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ)) : ℝ :=
  Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩)
    (fun i => Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩)
      (fun j => maxEntryNorm hr (A i j)))

/-- Each block norm is bounded by the full block max norm. -/
lemma block_le_blockMaxNorm {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ)) (i j : Fin m) :
    maxEntryNorm hr (A i j) ≤ blockMaxNorm hm hr A := by
  unfold blockMaxNorm
  exact le_trans
    (Finset.le_sup' (fun j' => maxEntryNorm hr (A i j')) (Finset.mem_univ j))
    (Finset.le_sup' (fun i' => Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩)
      (fun j' => maxEntryNorm hr (A i' j'))) (Finset.mem_univ i))

lemma blockMaxNorm_nonneg {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ)) :
    0 ≤ blockMaxNorm hm hr A :=
  le_trans (maxEntryNorm_nonneg hr (A ⟨0, hm⟩ ⟨0, hm⟩))
    (block_le_blockMaxNorm hm hr A ⟨0, hm⟩ ⟨0, hm⟩)

/-- Blockwise matrix-`∞` norm maximum for a uniform block matrix.

    This is the source-style block norm obtained by using the matrix `∞`
    operator norm on each block and then taking the maximum over block
    indices.  It is distinct from `blockMaxNorm`, which is the chapter's
    entrywise max norm over all scalar entries. -/
noncomputable def blockInfNorm {m r : ℕ} (hm : 0 < m)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ) : ℝ :=
  Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩)
    (fun i => Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩)
      (fun j => infNorm (A i j)))

/-- Each block matrix-`∞` norm is bounded by the blockwise matrix-`∞`
    maximum. -/
lemma block_le_blockInfNorm {m r : ℕ} (hm : 0 < m)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ) (i j : Fin m) :
    infNorm (A i j) ≤ blockInfNorm hm A := by
  unfold blockInfNorm
  exact le_trans
    (Finset.le_sup' (fun j' => infNorm (A i j')) (Finset.mem_univ j))
    (Finset.le_sup' (fun i' => Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩)
      (fun j' => infNorm (A i' j'))) (Finset.mem_univ i))

lemma blockInfNorm_nonneg {m r : ℕ} (hm : 0 < m)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ) :
    0 ≤ blockInfNorm hm A :=
  le_trans (infNorm_nonneg (A ⟨0, hm⟩ ⟨0, hm⟩))
    (block_le_blockInfNorm hm A ⟨0, hm⟩ ⟨0, hm⟩)

/-- Bound a blockwise matrix-`∞` maximum from uniform bounds on all blocks. -/
lemma blockInfNorm_le_of_block_le {m r : ℕ} (hm : 0 < m)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ) {C : ℝ}
    (hC : ∀ i j : Fin m, infNorm (A i j) ≤ C) :
    blockInfNorm hm A ≤ C := by
  unfold blockInfNorm
  apply Finset.sup'_le
  intro i _hi
  apply Finset.sup'_le
  intro j _hj
  exact hC i j

/-- The matrix-`∞` norm of a zero block is zero. -/
lemma infNorm_zeroBlock (r : ℕ) :
    infNorm (zeroBlock r) = 0 := by
  apply le_antisymm
  · apply infNorm_le_of_row_sum_le
    · intro i
      simp [zeroBlock]
    · norm_num
  · exact infNorm_nonneg (zeroBlock r)

lemma infNorm_le_zero_of_eq_zeroBlock {r : ℕ}
    {B : Matrix (Fin r) (Fin r) ℝ} (hB : B = zeroBlock r) :
    infNorm B ≤ 0 := by
  rw [hB, infNorm_zeroBlock]

/-- Every scalar entry of a block matrix is bounded by the Chapter 13
    entrywise max norm. -/
lemma block_entry_abs_le_blockMaxNorm {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (i j : Fin m) (s t : Fin r) :
    |A i j s t| ≤ blockMaxNorm hm hr A := by
  exact le_trans (entry_le_maxEntryNorm hr (A i j) s t)
    (block_le_blockMaxNorm hm hr A i j)

/-- A uniform scalar entrywise bound controls the Chapter 13 block max norm. -/
lemma blockMaxNorm_le_of_entry_abs_le {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ)) (C : ℝ)
    (hEntry : ∀ i j : Fin m, ∀ s t : Fin r, |A i j s t| ≤ C) :
    blockMaxNorm hm hr A ≤ C := by
  unfold blockMaxNorm
  apply Finset.sup'_le
  intro i _hi
  apply Finset.sup'_le
  intro j _hj
  unfold maxEntryNorm
  apply Finset.sup'_le
  intro s _hs
  apply Finset.sup'_le
  intro t _ht
  exact hEntry i j s t

/-- The chapter entrywise block max norm is bounded by the blockwise
    matrix-`∞` maximum. -/
lemma blockMaxNorm_le_blockInfNorm {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : Fin m → Fin m → Matrix (Fin r) (Fin r) ℝ) :
    blockMaxNorm hm hr A ≤ blockInfNorm hm A := by
  apply blockMaxNorm_le_of_entry_abs_le
  intro i j s t
  exact le_trans
    (entry_le_maxEntryNorm hr (A i j) s t)
    (le_trans (maxEntryNorm_le_infNorm hr (A i j))
      (block_le_blockInfNorm hm A i j))

/-- A block matrix whose scalar entries occur in a square matrix is bounded by
    that square matrix's max-entry norm.  This is the block analogue of the
    rectangular submatrix containment bridge and is used to connect the
    Algorithm 13.3 block upper factor to a common GE growth object. -/
lemma blockMaxNorm_le_maxEntryNorm_of_reindex_eq
    {N m r : ℕ} (hN : 0 < N) (hm : 0 < m) (hr : 0 < r)
    (B : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (G : Fin N → Fin N → ℝ)
    (row : Fin m → Fin r → Fin N) (col : Fin m → Fin r → Fin N)
    (hB : ∀ i j s t, B i j s t = G (row i s) (col j t)) :
    blockMaxNorm hm hr B ≤ maxEntryNorm hN G := by
  apply blockMaxNorm_le_of_entry_abs_le
  intro i j s t
  rw [hB i j s t]
  exact entry_le_maxEntryNorm hN G (row i s) (col j t)

end NumStability
