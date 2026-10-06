import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Analysis.MatrixAlgebra

/-!
# Entrywise maximum matrix norms

Reusable square and rectangular entrywise-maximum norms, exposed as
`maxEntryNorm` and `maxEntryNormRect`. This module proves entry, transpose,
submatrix, addition, and subtraction bounds; comparisons with the matrix
infinity norm; matrix-product estimates and sharp dimension-dependence
counterexamples; and right-inverse and nonsingular-inverse entry bounds.

The definitions are source-independent norm infrastructure used by LU growth
analysis and block-matrix algorithms.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix

/-- **Max-entry norm** of a matrix: max_{i,j} |A_ij|.

    This is the elementwise maximum absolute value, used in
    Higham's definition of the growth factor (Definition 9.6):
      ρ_n = max_{i,j} |û_ij| / max_{i,j} |a_ij|

    Distinguished from `infNorm` (the operator ∞-norm = max row sum). -/
noncomputable def maxEntryNorm {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ) : ℝ :=
  Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
    (fun i => Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
      (fun j => |A i j|))

/-- Max-entry norm is nonneg. -/
lemma maxEntryNorm_nonneg {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ) :
    0 ≤ maxEntryNorm hn A := by
  have h0 : (⟨0, hn⟩ : Fin n) ∈ Finset.univ := Finset.mem_univ _
  have h1 : 0 ≤ |A ⟨0, hn⟩ ⟨0, hn⟩| := abs_nonneg _
  have h2 : |A ⟨0, hn⟩ ⟨0, hn⟩| ≤ Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun j => |A ⟨0, hn⟩ j|) :=
    Finset.le_sup' (fun j => |A ⟨0, hn⟩ j|) h0
  have h3 : Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
      (fun j => |A ⟨0, hn⟩ j|) ≤ maxEntryNorm hn A :=
    Finset.le_sup' (fun i => Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun j => |A i j|)) h0
  linarith

/-- Each entry is bounded by the max-entry norm. -/
lemma entry_le_maxEntryNorm {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (i j : Fin n) : |A i j| ≤ maxEntryNorm hn A := by
  apply le_trans
  · exact Finset.le_sup' (fun j => |A i j|) (Finset.mem_univ j)
  · exact Finset.le_sup' (fun i => Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun j => |A i j|))
      (Finset.mem_univ i)

/-- Each entry is bounded by the matrix infinity norm. -/
lemma entry_abs_le_infNorm {n : ℕ} (A : Fin n → Fin n → ℝ)
    (i j : Fin n) : |A i j| ≤ infNorm A := by
  have hrow : |A i j| ≤ ∑ j' : Fin n, |A i j'| :=
    Finset.single_le_sum (fun j' _ => abs_nonneg (A i j')) (Finset.mem_univ j)
  exact le_trans hrow (row_sum_le_infNorm A i)

/-- The max-entry norm is bounded by the matrix infinity norm. -/
lemma maxEntryNorm_le_infNorm {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) :
    maxEntryNorm hn A ≤ infNorm A := by
  unfold maxEntryNorm
  apply Finset.sup'_le
  intro i _
  apply Finset.sup'_le
  intro j _
  exact entry_abs_le_infNorm A i j

/-- Max-entry norm monotonicity from componentwise absolute-value bounds. -/
lemma maxEntryNorm_le_of_entry_abs_le {n : ℕ} (hn : 0 < n)
    (A B : Fin n → Fin n → ℝ)
    (hentry : ∀ i j : Fin n, |A i j| ≤ |B i j|) :
    maxEntryNorm hn A ≤ maxEntryNorm hn B := by
  unfold maxEntryNorm
  apply Finset.sup'_le
  intro i _
  apply Finset.sup'_le
  intro j _
  exact le_trans (hentry i j) (entry_le_maxEntryNorm hn B i j)

/-- Max-entry norm bound from a uniform entrywise bound. -/
lemma maxEntryNorm_le_of_entry_le_bound {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (M : ℝ)
    (hentry : ∀ i j : Fin n, |A i j| ≤ M) :
    maxEntryNorm hn A ≤ M := by
  unfold maxEntryNorm
  apply Finset.sup'_le
  intro i _
  apply Finset.sup'_le
  intro j _
  exact hentry i j

/-- Max-entry norm monotonicity when every entry is bounded by another
matrix's max-entry norm, possibly at different indices. -/
lemma maxEntryNorm_le_of_entry_le_max {n : ℕ} (hn : 0 < n)
    (A B : Fin n → Fin n → ℝ)
    (hentry : ∀ i j : Fin n, |A i j| ≤ maxEntryNorm hn B) :
    maxEntryNorm hn A ≤ maxEntryNorm hn B := by
  exact maxEntryNorm_le_of_entry_le_bound hn A (maxEntryNorm hn B) hentry

/-- The max-entry norm is invariant under matrix transposition. -/
lemma maxEntryNorm_matTranspose {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) :
    maxEntryNorm hn (matTranspose A) = maxEntryNorm hn A := by
  apply le_antisymm
  · let hne : (Finset.univ : Finset (Fin n)).Nonempty :=
      Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
    change Finset.sup' Finset.univ hne
        (fun i => Finset.sup' Finset.univ hne (fun j => |matTranspose A i j|)) ≤
      maxEntryNorm hn A
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    simpa [matTranspose] using entry_le_maxEntryNorm hn A j i
  · let hne : (Finset.univ : Finset (Fin n)).Nonempty :=
      Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
    change Finset.sup' Finset.univ hne
        (fun i => Finset.sup' Finset.univ hne (fun j => |A i j|)) ≤
      maxEntryNorm hn (matTranspose A)
    apply Finset.sup'_le
    intro i _
    apply Finset.sup'_le
    intro j _
    simpa [matTranspose] using entry_le_maxEntryNorm hn (matTranspose A) j i

/-- Any square submatrix has max-entry norm bounded by the source matrix's
max-entry norm. -/
lemma maxEntryNorm_submatrix_le {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : Fin n → Fin n → ℝ) (rows cols : Fin m → Fin n) :
    maxEntryNorm hm (fun i j : Fin m => A (rows i) (cols j)) ≤
      maxEntryNorm hn A := by
  let hne : (Finset.univ : Finset (Fin m)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩
  change Finset.sup' Finset.univ hne
      (fun i => Finset.sup' Finset.univ hne
        (fun j => |A (rows i) (cols j)|)) ≤ maxEntryNorm hn A
  apply Finset.sup'_le
  intro i _
  apply Finset.sup'_le
  intro j _
  exact entry_le_maxEntryNorm hn A (rows i) (cols j)

/-- The matrix infinity norm is at most `n` times the max-entry norm. -/
theorem infNorm_le_card_mul_maxEntryNorm {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) :
    infNorm A ≤ (n : ℝ) * maxEntryNorm hn A := by
  apply infNorm_le_of_row_sum_le
  · intro i
    calc
      ∑ j : Fin n, |A i j|
          ≤ ∑ _j : Fin n, maxEntryNorm hn A := by
            apply Finset.sum_le_sum
            intro j _
            exact entry_le_maxEntryNorm hn A i j
      _ = (n : ℝ) * maxEntryNorm hn A := by
            simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
  · exact mul_nonneg (Nat.cast_nonneg' n) (maxEntryNorm_nonneg hn A)

/-- Rectangular entrywise max norm used by Chapter 13's `max |aᵢⱼ|`
    convention for nonsquare computed kernels such as matrix multiplication. -/
noncomputable def maxEntryNormRect {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) : ℝ :=
  Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩)
    (fun i => Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
      (fun j => |A i j|))

lemma maxEntryNormRect_nonneg {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) :
    0 ≤ maxEntryNormRect hm hn A := by
  have h0m : (⟨0, hm⟩ : Fin m) ∈ Finset.univ := Finset.mem_univ _
  have h0n : (⟨0, hn⟩ : Fin n) ∈ Finset.univ := Finset.mem_univ _
  have hentry : 0 ≤ |A ⟨0, hm⟩ ⟨0, hn⟩| := abs_nonneg _
  have hcol :
      |A ⟨0, hm⟩ ⟨0, hn⟩| ≤
        Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
          (fun j => |A ⟨0, hm⟩ j|) :=
    Finset.le_sup' (fun j => |A ⟨0, hm⟩ j|) h0n
  have hrow :
      Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
          (fun j => |A ⟨0, hm⟩ j|) ≤
        maxEntryNormRect hm hn A :=
    Finset.le_sup' (fun i => Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun j => |A i j|)) h0m
  exact le_trans hentry (le_trans hcol hrow)

lemma entry_le_maxEntryNormRect {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    |A i j| ≤ maxEntryNormRect hm hn A := by
  exact le_trans
    (Finset.le_sup' (fun j' => |A i j'|) (Finset.mem_univ j))
    (Finset.le_sup' (fun i' => Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun j' => |A i' j'|))
      (Finset.mem_univ i))

/-- The rectangular max-entry norm specializes definitionally to the square
    max-entry norm used by the growth-factor API. -/
lemma maxEntryNormRect_eq_maxEntryNorm {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) :
    maxEntryNormRect hn hn A = maxEntryNorm hn A := rfl


lemma maxEntryNormRect_le_of_entry_abs_le {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) (C : ℝ)
    (hEntry : ∀ i : Fin m, ∀ j : Fin n, |A i j| ≤ C) :
    maxEntryNormRect hm hn A ≤ C := by
  unfold maxEntryNormRect
  apply Finset.sup'_le
  intro i _hi
  apply Finset.sup'_le
  intro j _hj
  exact hEntry i j

/-- The rectangular max-entry norm of a single-column matrix is exactly the
    infinity norm of the represented vector. -/
lemma maxEntryNormRect_single_col_eq_infNormVec {r : ℕ}
    (hr : 0 < r) (X : Matrix (Fin r) (Fin 1) ℝ) :
    maxEntryNormRect hr (Nat.succ_pos 0) X =
      infNormVec (fun i : Fin r => X i 0) := by
  apply le_antisymm
  · apply maxEntryNormRect_le_of_entry_abs_le
    intro i j
    fin_cases j
    exact abs_le_infNormVec (fun t : Fin r => X t 0) i
  · apply infNormVec_le_of_abs_le
    · intro i
      exact entry_le_maxEntryNormRect hr (Nat.succ_pos 0) X i 0
    · exact maxEntryNormRect_nonneg hr (Nat.succ_pos 0) X

/-- Triangle inequality for the Chapter 13 block max norm under subtraction. -/
lemma maxEntryNorm_sub_le {r : ℕ} (hr : 0 < r)
    (A B : Matrix (Fin r) (Fin r) ℝ) :
    maxEntryNorm hr (A - B) ≤ maxEntryNorm hr A + maxEntryNorm hr B := by
  have hrect :
      maxEntryNormRect hr hr (A - B) ≤ maxEntryNorm hr A + maxEntryNorm hr B := by
    apply maxEntryNormRect_le_of_entry_abs_le
    intro s t
    exact le_trans
      (by
        simpa [sub_eq_add_neg, abs_neg] using abs_sub_le (A s t) 0 (B s t))
      (add_le_add (entry_le_maxEntryNorm hr A s t)
        (entry_le_maxEntryNorm hr B s t))
  simpa [maxEntryNormRect_eq_maxEntryNorm hr] using hrect

/-- Triangle inequality for the Chapter 13 square max-entry norm. -/
lemma maxEntryNorm_add_le {r : ℕ} (hr : 0 < r)
    (A B : Matrix (Fin r) (Fin r) ℝ) :
    maxEntryNorm hr (A + B) ≤ maxEntryNorm hr A + maxEntryNorm hr B := by
  have hrect :
      maxEntryNormRect hr hr (A + B) ≤
        maxEntryNorm hr A + maxEntryNorm hr B := by
    apply maxEntryNormRect_le_of_entry_abs_le
    intro i j
    calc
      |(A + B) i j| ≤ |A i j| + |B i j| := abs_add_le _ _
      _ ≤ maxEntryNorm hr A + maxEntryNorm hr B :=
        add_le_add (entry_le_maxEntryNorm hr A i j)
          (entry_le_maxEntryNorm hr B i j)
  simpa [maxEntryNormRect_eq_maxEntryNorm hr] using hrect

/-- Four-term triangle inequality used by the concrete DHS solve perturbation
    `E + DeltaL * Uhat + Lhat * DeltaU + DeltaL * DeltaU`. -/
lemma maxEntryNorm_four_add_le {r : ℕ} (hr : 0 < r)
    (A B C D : Matrix (Fin r) (Fin r) ℝ) :
    maxEntryNorm hr (A + B + C + D) ≤
      maxEntryNorm hr A + maxEntryNorm hr B +
        maxEntryNorm hr C + maxEntryNorm hr D := by
  calc
    maxEntryNorm hr (A + B + C + D) ≤
        maxEntryNorm hr (A + B + C) + maxEntryNorm hr D :=
      maxEntryNorm_add_le hr (A + B + C) D
    _ ≤ (maxEntryNorm hr (A + B) + maxEntryNorm hr C) +
          maxEntryNorm hr D := by
      linarith [maxEntryNorm_add_le hr (A + B) C]
    _ ≤ ((maxEntryNorm hr A + maxEntryNorm hr B) + maxEntryNorm hr C) +
          maxEntryNorm hr D := by
      linarith [maxEntryNorm_add_le hr A B]

/-- An invertible square matrix has positive Chapter 13 max-entry norm. -/
lemma maxEntryNorm_pos_of_invertible {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) [Invertible A] :
    0 < maxEntryNorm hn A := by
  have hnonneg : 0 ≤ maxEntryNorm hn A :=
    maxEntryNorm_nonneg hn A
  have hne : maxEntryNorm hn A ≠ 0 := by
    intro hzero
    have hentries : ∀ i j : Fin n, A i j = 0 := by
      intro i j
      have hle := entry_le_maxEntryNorm hn A i j
      rw [hzero] at hle
      exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg (A i j)))
    let z : Fin n := ⟨0, hn⟩
    have hprod0 : (A * ⅟A) z z = 0 := by
      simp [Matrix.mul_apply, hentries]
    have hprod1 : (A * ⅟A) z z = 1 := by
      exact congr_fun (congr_fun (mul_invOf_self A) z) z
    nlinarith
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- A square matrix with nonzero determinant has positive Chapter 13
    max-entry norm. -/
lemma maxEntryNorm_pos_of_det_ne_zero {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    0 < maxEntryNorm hn A := by
  have hnonneg : 0 ≤ maxEntryNorm hn A :=
    maxEntryNorm_nonneg hn A
  have hne : maxEntryNorm hn A ≠ 0 := by
    intro hzero
    have hentries : ∀ i j : Fin n, A i j = 0 := by
      intro i j
      have hle := entry_le_maxEntryNorm hn A i j
      rw [hzero] at hle
      exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg (A i j)))
    apply hdet
    exact Matrix.det_eq_zero_of_row_eq_zero (⟨0, hn⟩ : Fin n)
      (fun j => hentries ⟨0, hn⟩ j)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- A rectangular matrix whose entries occur in a square matrix is bounded by
    that square matrix's max-entry norm.  This is the max-entry submatrix
    bookkeeping bridge used when a Schur complement is identified with an
    active GE growth-factor block. -/
lemma maxEntryNormRect_le_maxEntryNorm_of_reindex_eq
    {N m n : ℕ} (hN : 0 < N) (hm : 0 < m) (hn : 0 < n)
    (S : Fin m → Fin n → ℝ) (U : Fin N → Fin N → ℝ)
    (row : Fin m → Fin N) (col : Fin n → Fin N)
    (hS : ∀ i j, S i j = U (row i) (col j)) :
    maxEntryNormRect hm hn S ≤ maxEntryNorm hN U := by
  apply maxEntryNormRect_le_of_entry_abs_le
  intro i j
  rw [hS i j]
  exact entry_le_maxEntryNorm hN U (row i) (col j)

/-- Rectangular max-entry product bound:
    `||A B||_max <= n ||A||_max ||B||_max`.

    This is the entrywise norm submultiplicativity estimate used in the
    max-entry-norm route for Higham Chapter 13, Problem 13.4. -/
theorem maxEntryNormRect_rectMatMul_le {m n p : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hp : 0 < p)
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ) :
    maxEntryNormRect hm hp (rectMatMul A B) ≤
      (n : ℝ) * maxEntryNormRect hm hn A * maxEntryNormRect hn hp B := by
  let normA : ℝ := maxEntryNormRect hm hn A
  let normB : ℝ := maxEntryNormRect hn hp B
  have hnormA : 0 ≤ normA := maxEntryNormRect_nonneg hm hn A
  apply maxEntryNormRect_le_of_entry_abs_le
  intro i j
  have hsum :
      (∑ k : Fin n, |A i k| * |B k j|) ≤ (n : ℝ) * (normA * normB) := by
    calc
      (∑ k : Fin n, |A i k| * |B k j|)
          ≤ ∑ _k : Fin n, normA * normB := by
              apply Finset.sum_le_sum
              intro k _hk
              exact mul_le_mul
                (entry_le_maxEntryNormRect hm hn A i k)
                (entry_le_maxEntryNormRect hn hp B k j)
                (abs_nonneg (B k j)) hnormA
      _ = (n : ℝ) * (normA * normB) := by
        simp [nsmul_eq_mul]
  calc
    |rectMatMul A B i j|
        ≤ ∑ k : Fin n, |A i k * B k j| := by
          simpa [rectMatMul] using
            (Finset.abs_sum_le_sum_abs
              (s := (Finset.univ : Finset (Fin n)))
              (f := fun k => A i k * B k j))
    _ = ∑ k : Fin n, |A i k| * |B k j| := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact abs_mul (A i k) (B k j)
    _ ≤ (n : ℝ) * (normA * normB) := hsum
    _ = (n : ℝ) * maxEntryNormRect hm hn A *
          maxEntryNormRect hn hp B := by
      simp [normA, normB, mul_assoc]

/-- Mixed matrix-∞/entrywise max product bound:
    `||A B||_max <= ||A||_∞ ||B||_max`.

    This is the dimension-free product estimate needed by the column-BDD
    Chapter 13 route: the left factor is controlled by row mass while the
    right factor is controlled entrywise. -/
theorem maxEntryNorm_matrix_mul_le_infNorm_mul_maxEntryNorm {r : ℕ} (hr : 0 < r)
    (A B : Matrix (Fin r) (Fin r) ℝ) :
    maxEntryNorm hr (A * B) ≤ infNorm A * maxEntryNorm hr B := by
  change maxEntryNormRect hr hr (fun i j => (A * B) i j) ≤
    infNorm A * maxEntryNorm hr B
  apply maxEntryNormRect_le_of_entry_abs_le
  intro i j
  have hB_nonneg : 0 ≤ maxEntryNorm hr B := maxEntryNorm_nonneg hr B
  have hsum_abs :
      |∑ k : Fin r, A i k * B k j| ≤
        ∑ k : Fin r, |A i k * B k j| :=
    Finset.abs_sum_le_sum_abs
      (s := (Finset.univ : Finset (Fin r)))
      (f := fun k => A i k * B k j)
  have hterms :
      (∑ k : Fin r, |A i k * B k j|) ≤
        ∑ k : Fin r, |A i k| * maxEntryNorm hr B := by
    apply Finset.sum_le_sum
    intro k _hk
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (entry_le_maxEntryNorm hr B k j) (abs_nonneg (A i k))
  have hrow :
      (∑ k : Fin r, |A i k| * maxEntryNorm hr B) ≤
        infNorm A * maxEntryNorm hr B := by
    calc
      (∑ k : Fin r, |A i k| * maxEntryNorm hr B)
          = (∑ k : Fin r, |A i k|) * maxEntryNorm hr B := by
              rw [Finset.sum_mul]
      _ ≤ infNorm A * maxEntryNorm hr B :=
              mul_le_mul_of_nonneg_right (row_sum_le_infNorm A i) hB_nonneg
  calc
    |(A * B) i j|
        = |∑ k : Fin r, A i k * B k j| := by
            simp [Matrix.mul_apply]
    _ ≤ ∑ k : Fin r, |A i k * B k j| := hsum_abs
    _ ≤ ∑ k : Fin r, |A i k| * maxEntryNorm hr B := hterms
    _ ≤ infNorm A * maxEntryNorm hr B := hrow

/-- Square matrix-product max-entry bound with the dimension factor exposed. -/
theorem maxEntryNorm_matrix_mul_le_dim {r : ℕ} (hr : 0 < r)
    (A B : Matrix (Fin r) (Fin r) ℝ) :
    maxEntryNorm hr (A * B) ≤
      (r : ℝ) * maxEntryNorm hr A * maxEntryNorm hr B := by
  have h :=
    maxEntryNormRect_rectMatMul_le hr hr hr
      (fun i j => A i j) (fun i j => B i j)
  simpa [rectMatMul, Matrix.mul_apply, maxEntryNormRect_eq_maxEntryNorm hr]
    using h

/-- Triple square matrix-product max-entry bound with the unavoidable
    `r^2` factor for the entrywise max norm. -/
theorem maxEntryNorm_matrix_mul_mul_le_dim_sq {r : ℕ} (hr : 0 < r)
    (A B C : Matrix (Fin r) (Fin r) ℝ) :
    maxEntryNorm hr (A * B * C) ≤
      (r : ℝ) ^ 2 * maxEntryNorm hr A * maxEntryNorm hr B *
        maxEntryNorm hr C := by
  have hAB :
      maxEntryNorm hr (A * B) ≤
        (r : ℝ) * maxEntryNorm hr A * maxEntryNorm hr B :=
    maxEntryNorm_matrix_mul_le_dim hr A B
  have hABC :
      maxEntryNorm hr ((A * B) * C) ≤
        (r : ℝ) * maxEntryNorm hr (A * B) * maxEntryNorm hr C :=
    maxEntryNorm_matrix_mul_le_dim hr (A * B) C
  have hr_nonneg : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hC_nonneg : 0 ≤ maxEntryNorm hr C := maxEntryNorm_nonneg hr C
  have hstep :
      (r : ℝ) * maxEntryNorm hr (A * B) * maxEntryNorm hr C ≤
        (r : ℝ) * ((r : ℝ) * maxEntryNorm hr A * maxEntryNorm hr B) *
          maxEntryNorm hr C := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hAB hr_nonneg) hC_nonneg
  calc
    maxEntryNorm hr (A * B * C)
        ≤ (r : ℝ) * maxEntryNorm hr (A * B) * maxEntryNorm hr C := hABC
    _ ≤ (r : ℝ) * ((r : ℝ) * maxEntryNorm hr A * maxEntryNorm hr B) *
          maxEntryNorm hr C := hstep
    _ = (r : ℝ) ^ 2 * maxEntryNorm hr A * maxEntryNorm hr B *
          maxEntryNorm hr C := by ring

/-- Audit for the Chapter 13 max-entry route: ordinary square matrix
    multiplication is not dimension-free submultiplicative for the entrywise
    max norm.  The all-ones `2 × 2` matrix gives `‖J*J‖max = 2` while
    `‖J‖max * ‖J‖max = 1`. -/
theorem maxEntryNorm_matrix_mul_dimension_free_counterexample :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ,
      ¬ maxEntryNorm (by norm_num : 0 < 2) (A * B) ≤
        maxEntryNorm (by norm_num : 0 < 2) A *
          maxEntryNorm (by norm_num : 0 < 2) B := by
  let J : Matrix (Fin 2) (Fin 2) ℝ := fun _ _ => 1
  refine ⟨J, J, ?_⟩
  norm_num [maxEntryNorm, J, Matrix.mul_apply, Fin.sum_univ_two]

/-- Audit for the Chapter 13 max-entry route: the corresponding
    dimension-free triple-product estimate is also false for generic square
    matrix multiplication in the entrywise max norm. -/
theorem maxEntryNorm_matrix_mul_mul_dimension_free_counterexample :
    ∃ A B C : Matrix (Fin 2) (Fin 2) ℝ,
      ¬ maxEntryNorm (by norm_num : 0 < 2) (A * B * C) ≤
        maxEntryNorm (by norm_num : 0 < 2) A *
          maxEntryNorm (by norm_num : 0 < 2) B *
            maxEntryNorm (by norm_num : 0 < 2) C := by
  let J : Matrix (Fin 2) (Fin 2) ℝ := fun _ _ => 1
  refine ⟨J, J, J, ?_⟩
  norm_num [maxEntryNorm, J, Matrix.mul_apply, Fin.sum_univ_two]

/-- A right inverse forces the max-entry product to be large enough to cover
    the identity, up to the usual dimension factor for the entrywise max norm.

    This is the nonvacuity lemma behind the diagonal `1 <= nρ²κ(A)` side
    condition in the assembled Eq.13.22 lower-factor bound. -/
theorem one_le_dim_mul_maxEntryNormRect_mul_of_isRightInverse {n : ℕ}
    (hn : 0 < n) (A Ainv : Fin n → Fin n → ℝ)
    (hRight : IsRightInverse n A Ainv) :
    1 ≤ (n : ℝ) * maxEntryNormRect hn hn A *
      maxEntryNormRect hn hn Ainv := by
  let I : Fin n → Fin n → ℝ := fun i j => if i = j then 1 else 0
  have hI_entry :
      (1 : ℝ) ≤ maxEntryNormRect hn hn I := by
    have hentry :=
      entry_le_maxEntryNormRect hn hn I
        (⟨0, hn⟩ : Fin n) (⟨0, hn⟩ : Fin n)
    simpa [I] using hentry
  have hmul_eq_I : rectMatMul A Ainv = I := by
    ext i j
    simpa [rectMatMul, I] using hRight i j
  have hmul_norm :
      maxEntryNormRect hn hn (rectMatMul A Ainv) ≤
        (n : ℝ) * maxEntryNormRect hn hn A *
          maxEntryNormRect hn hn Ainv := by
    exact maxEntryNormRect_rectMatMul_le hn hn hn A Ainv
  calc
    (1 : ℝ) ≤ maxEntryNormRect hn hn I := hI_entry
    _ = maxEntryNormRect hn hn (rectMatMul A Ainv) := by
          rw [← hmul_eq_I]
    _ ≤ (n : ℝ) * maxEntryNormRect hn hn A *
          maxEntryNormRect hn hn Ainv := hmul_norm

/-- A certified inverse gives the dimension-free mixed-norm pivot lower
    product used by the column-BDD route:
    `1 <= ||A⁻¹||_∞ ||A||_max`.

    The proof applies the mixed `∞`/max-entry product bound to the left inverse
    equation `A⁻¹ * A = I`, which is derived from the supplied finite square
    right-inverse certificate. -/
theorem one_le_infNorm_mul_maxEntryNorm_of_isRightInverse {r : ℕ} (hr : 0 < r)
    (A Ainv : Matrix (Fin r) (Fin r) ℝ)
    (hRight : IsRightInverse r A Ainv) :
    1 ≤ infNorm Ainv * maxEntryNorm hr A := by
  let i0 : Fin r := ⟨0, hr⟩
  have hLeft : IsLeftInverse r A Ainv :=
    isLeftInverse_of_isRightInverse A Ainv hRight
  have hdiag : (Ainv * A) i0 i0 = 1 := by
    simpa [Matrix.mul_apply] using hLeft i0 i0
  have hentry :
      (1 : ℝ) ≤ maxEntryNorm hr (Ainv * A) := by
    have h :=
      entry_le_maxEntryNorm hr (Ainv * A) i0 i0
    simpa [hdiag] using h
  exact le_trans hentry
    (maxEntryNorm_matrix_mul_le_infNorm_mul_maxEntryNorm hr Ainv A)

/-- A certified right inverse turns the source reciprocal diagonal budget into
    a max-entry lower bound for the original diagonal block.  This is the
    mixed matrix-`∞`/max-entry bridge used in the column-BDD route for
    Theorem 13.8. -/
theorem inv_infNorm_le_maxEntryNorm_of_isRightInverse {r : ℕ} (hr : 0 < r)
    (A Ainv : Matrix (Fin r) (Fin r) ℝ)
    (hRight : IsRightInverse r A Ainv) :
    (infNorm Ainv)⁻¹ ≤ maxEntryNorm hr A := by
  have hprod := one_le_infNorm_mul_maxEntryNorm_of_isRightInverse hr A Ainv hRight
  have hnorm_nonneg : 0 ≤ infNorm Ainv := infNorm_nonneg Ainv
  by_cases hzero : infNorm Ainv = 0
  · have hbad : (1 : ℝ) ≤ 0 := by
      have hprod0 : (1 : ℝ) ≤ 0 * maxEntryNorm hr A := by
        simpa [hzero] using hprod
      simpa using hprod0
    linarith
  · have hpos : 0 < infNorm Ainv := lt_of_le_of_ne hnorm_nonneg (Ne.symm hzero)
    have hinv_nonneg : 0 ≤ (infNorm Ainv)⁻¹ := inv_nonneg.mpr hnorm_nonneg
    calc
      (infNorm Ainv)⁻¹ = (infNorm Ainv)⁻¹ * 1 := by ring
      _ ≤ (infNorm Ainv)⁻¹ * (infNorm Ainv * maxEntryNorm hr A) :=
        mul_le_mul_of_nonneg_left hprod hinv_nonneg
      _ = maxEntryNorm hr A := by
        field_simp [hpos.ne']

/-- Reindexing a source `Fin n` matrix by an equivalence and taking Mathlib's
    constructive inverse gives entrywise max-entry certificates bounded by the
    repository's source-facing canonical inverse `nonsingInv`.

    This is the max-entry analogue of
    `finiteOpNorm2Le_invOf_reindex_equiv_nonsingInv` for the Chapter 13
    Problem 13.4 route. -/
theorem maxEntryNormRect_invOf_reindex_equiv_nonsingInv_entry_bound
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ Fin n) (A : Fin n → Fin n → ℝ)
    (M : Matrix ι ι ℝ) [Invertible M]
    (hM : M = fun i j : ι => A (e i) (e j)) :
    ∀ i j : ι, |(⅟M) i j| ≤
      maxEntryNormRect hn hn (nonsingInv n A) := by
  classical
  intro i j
  have h1 : ⅟M = M⁻¹ :=
    Matrix.invOf_eq_nonsing_inv M
  have h2 :
      M⁻¹ =
        (((A : Matrix (Fin n) (Fin n) ℝ)⁻¹ :
          Matrix (Fin n) (Fin n) ℝ).submatrix e e) := by
    rw [hM]
    exact Matrix.inv_submatrix_equiv (A : Matrix (Fin n) (Fin n) ℝ) e e
  have hentry :
      (⅟M) i j = nonsingInv n A (e i) (e j) := by
    calc
      (⅟M) i j = M⁻¹ i j := by rw [h1]
      _ =
          (((A : Matrix (Fin n) (Fin n) ℝ)⁻¹ :
            Matrix (Fin n) (Fin n) ℝ) (e i) (e j)) := by
        rw [h2]
        rfl
      _ = nonsingInv n A (e i) (e j) := by
        unfold nonsingInv
        rfl
  rw [hentry]
  exact entry_le_maxEntryNormRect hn hn (nonsingInv n A) (e i) (e j)

end NumStability
