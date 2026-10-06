-- Algorithms/GaussJordanPivoting.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed.,
-- Chapter 14, §14.4, Algorithm 14.4 (Gauss–Jordan elimination with partial
-- pivoting), pp. 273–274.
--
-- Codex's `GaussJordan.lean` models the SECOND-STAGE structural data of GJE
-- (the `N_k = I - n_k e_kᵀ` matrices and their cumulative error recurrences)
-- via the abstract `GJEStage2Spec`, but never specifies the *full* pivoting
-- algorithm: the max-magnitude pivot search, the row-swap permutation state,
-- or the whole-column elimination update.  This file supplies that
-- source-faithful definition together with its basic STRUCTURAL correctness
-- lemmas.  (The numerical stability of the second stage, Theorem 14.5, lives
-- in Codex's file / the endpoint files; it is not re-proved here.)
--
-- Algorithm 14.4 (verbatim structure, p. 273):
--   for k = 1: n
--       Find r such that |a_rk| = max_{i≥k} |a_ik|.   -- pivot search
--       A(k, k:n) ↔ A(r, k:n),  b(k) ↔ b(r)           -- swap rows k and r
--       row_ind = [1:k-1, k+1:n]                       -- ALL other rows
--       m = A(row_ind, k)/A(k, k)                      -- multipliers
--       A(row_ind, k:n) = A(row_ind, k:n) - m * A(k, k:n)
--       b(row_ind)      = b(row_ind)      - m * b(k)
--   end
--   x_i = b_i / a_ii,  i = 1: n
--
-- The distinguishing feature versus Gaussian elimination is that GJE
-- eliminates the ENTIRE off-diagonal column k (both above and below the
-- pivot), reducing A all the way to diagonal form.
--
-- What is proved here (all unconditional, honest structural facts):
--   • `ch14ext_pivotRow` realizes the "max_{i≥k} |a_ik|" search, with the
--     two defining properties (pivot row ≥ k; it attains the column max).
--   • The row swap is `Equiv.swap`, hence the accumulated interchange state
--     is a genuine permutation (`Function.Bijective`, matching the repo's
--     `IsPermutation`).
--   • After swapping the pivot into place, the pivot entry is the column
--     maximum, so the elimination multipliers for rows i ≥ k are bounded by
--     1 in magnitude (the partial-pivoting bound).  NB: the ABOVE-diagonal
--     multipliers (i < k) are NOT bounded by 1 — this is exactly the source
--     of GJE's backward instability discussed by Higham (§14.4).
--   • The whole-column elimination zeroes every off-diagonal entry of column
--     k (the claimed reduced form) and leaves the pivot row unchanged, and it
--     is realized as left multiplication by the elementary matrix G_k.
--   • The full interleaved loop `ch14ext_reduce` reduces A to DIAGONAL form
--     (`ch14ext_reduce_diagonal`), given the standard nonsingularity side
--     condition that each pivot is nonzero.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Equiv.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Tactic.Linarith
import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.LU.GaussianElimination

namespace NumStability.Ch14Ext

open Finset BigOperators

variable {n : ℕ}

-- ══════════════════════════════════════════════════════════════════════
-- §1  Partial-pivot row selection  ("Find r such that |a_rk| = max_{i≥k}|a_ik|")
-- ══════════════════════════════════════════════════════════════════════

/-- Candidate rows for the step-`k` pivot search: all row indices `i ≥ k`
    (Algorithm 14.4, "max over `i ≥ k`"). -/
def ch14ext_pivotCandidates (n : ℕ) (k : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => k ≤ i)

@[simp] lemma ch14ext_mem_pivotCandidates {k i : Fin n} :
    i ∈ ch14ext_pivotCandidates n k ↔ k ≤ i := by
  simp [ch14ext_pivotCandidates]

lemma ch14ext_pivotCandidates_nonempty (k : Fin n) :
    (ch14ext_pivotCandidates n k).Nonempty :=
  ⟨k, by simp⟩

/-- **Partial-pivot row selection** (Algorithm 14.4: "Find `r` such that
    `|a_rk| = max_{i≥k} |a_ik|`").  Realized by choosing an argmax of the
    magnitude `|A i k|` over the candidate rows `i ≥ k`. -/
noncomputable def ch14ext_pivotRow (A : Fin n → Fin n → ℝ) (k : Fin n) : Fin n :=
  (Finset.exists_max_image (ch14ext_pivotCandidates n k) (fun i => |A i k|)
    (ch14ext_pivotCandidates_nonempty k)).choose

lemma ch14ext_pivotRow_mem (A : Fin n → Fin n → ℝ) (k : Fin n) :
    ch14ext_pivotRow A k ∈ ch14ext_pivotCandidates n k :=
  (Finset.exists_max_image (ch14ext_pivotCandidates n k) (fun i => |A i k|)
    (ch14ext_pivotCandidates_nonempty k)).choose_spec.1

/-- The selected pivot row is `≥ k` (interchange never reaches above the
    diagonal). -/
lemma ch14ext_pivotRow_ge (A : Fin n → Fin n → ℝ) (k : Fin n) :
    k ≤ ch14ext_pivotRow A k := by
  have := ch14ext_pivotRow_mem A k
  simpa using this

/-- The selected pivot attains the column maximum over rows `i ≥ k`. -/
lemma ch14ext_pivotRow_max (A : Fin n → Fin n → ℝ) (k : Fin n) :
    ∀ i : Fin n, k ≤ i → |A i k| ≤ |A (ch14ext_pivotRow A k) k| := by
  intro i hi
  have hspec := (Finset.exists_max_image (ch14ext_pivotCandidates n k)
    (fun i => |A i k|) (ch14ext_pivotCandidates_nonempty k)).choose_spec.2
  exact hspec i (by simpa using hi)

-- ══════════════════════════════════════════════════════════════════════
-- §2  Row swap and the interchange permutation state
-- ══════════════════════════════════════════════════════════════════════

/-- The step-`k` row interchange of Algorithm 14.4 ("Swap rows `k` and `r`"),
    modeled as the transposition `Equiv.swap k r`.  Because it is an `Equiv`,
    the accumulated product of such swaps is automatically a *genuine*
    permutation. -/
def ch14ext_swap (k r : Fin n) : Equiv.Perm (Fin n) := Equiv.swap k r

/-- Apply a row permutation `σ` to a matrix: `(σ · A) i j = A (σ i) j`. -/
def ch14ext_permRows (σ : Equiv.Perm (Fin n)) (A : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => A (σ i) j

/-- **The interchange state is a genuine permutation.**  Every `Equiv.Perm`
    (in particular any product of the row swaps of Algorithm 14.4) is
    bijective, i.e. satisfies the repo's `IsPermutation` predicate. -/
lemma ch14ext_perm_isPermutation (σ : Equiv.Perm (Fin n)) :
    NumStability.IsPermutation n σ := σ.bijective

/-- A swap keeps the "≥ k" range invariant: if `k ≤ r` and `k ≤ i`, then the
    swapped index `swap k r i` is still `≥ k`. -/
lemma ch14ext_swap_ge {k r i : Fin n} (hkr : k ≤ r) (hi : k ≤ i) :
    k ≤ Equiv.swap k r i := by
  rcases eq_or_ne i k with rfl | hik
  · simpa [Equiv.swap_apply_left] using hkr
  rcases eq_or_ne i r with rfl | hir
  · simp [Equiv.swap_apply_right]
  · simpa [Equiv.swap_apply_of_ne_of_ne hik hir] using hi

/-- Swapping the pivot row `r = pivotRow A k` into position `k` makes the
    `(k,k)` entry the maximum-magnitude entry of column `k` over all rows
    `i ≥ k`.  This is the property that underlies the partial-pivoting
    multiplier bound. -/
lemma ch14ext_pivoted_colmax (A : Fin n → Fin n → ℝ) (k : Fin n) :
    ∀ i : Fin n, k ≤ i →
      |ch14ext_permRows (ch14ext_swap k (ch14ext_pivotRow A k)) A i k| ≤
      |ch14ext_permRows (ch14ext_swap k (ch14ext_pivotRow A k)) A k k| := by
  intro i hi
  set r := ch14ext_pivotRow A k with hr
  have hkr : k ≤ r := ch14ext_pivotRow_ge A k
  -- (σ · A) k k = A r k
  have hkk : ch14ext_permRows (ch14ext_swap k r) A k k = A r k := by
    simp [ch14ext_permRows, ch14ext_swap, Equiv.swap_apply_left]
  -- (σ · A) i k = A (swap k r i) k, and swap k r i ≥ k
  have hik : ch14ext_permRows (ch14ext_swap k r) A i k = A (Equiv.swap k r i) k := rfl
  have hge : k ≤ Equiv.swap k r i := ch14ext_swap_ge hkr hi
  rw [hik, hkk]
  exact ch14ext_pivotRow_max A k (Equiv.swap k r i) hge

-- ══════════════════════════════════════════════════════════════════════
-- §3  Multipliers  ("m = A(row_ind, k) / A(k, k)")  and the bound ≤ 1
-- ══════════════════════════════════════════════════════════════════════

/-- Step-`k` elimination multiplier for row `i` (Algorithm 14.4:
    `m = A(row_ind, k) / A(k, k)`). -/
noncomputable def ch14ext_multiplier (A : Fin n → Fin n → ℝ) (k i : Fin n) : ℝ :=
  A i k / A k k

/-- **Partial-pivoting multiplier bound.**  If the `(k,k)` entry is the
    column maximum over rows `i ≥ k` (as produced by the pivot swap) and is
    nonzero, then the elimination multiplier `m_i = A i k / A k k` has
    magnitude `≤ 1` for every row `i ≥ k`.  This is the sub-diagonal
    partial-pivoting bound `|m_ik| ≤ 1`. -/
lemma ch14ext_multiplier_abs_le_one
    (A : Fin n → Fin n → ℝ) (k i : Fin n)
    (hmax : |A i k| ≤ |A k k|) (hpiv : A k k ≠ 0) :
    |ch14ext_multiplier A k i| ≤ 1 := by
  unfold ch14ext_multiplier
  rw [abs_div]
  have hpos : 0 < |A k k| := abs_pos.mpr hpiv
  rw [div_le_one hpos]
  exact hmax

/-- The partial-pivoting multiplier bound, specialized to the matrix as it
    stands *after* the pivot swap of Algorithm 14.4: for every row `i ≥ k`,
    the multiplier has magnitude `≤ 1`, provided the pivot is nonzero
    (guaranteed here by nonsingularity of `A`). -/
lemma ch14ext_pivoted_multiplier_abs_le_one
    (A : Fin n → Fin n → ℝ) (k i : Fin n) (hi : k ≤ i)
    (hpiv : ch14ext_permRows (ch14ext_swap k (ch14ext_pivotRow A k)) A k k ≠ 0) :
    |ch14ext_multiplier
        (ch14ext_permRows (ch14ext_swap k (ch14ext_pivotRow A k)) A) k i| ≤ 1 :=
  ch14ext_multiplier_abs_le_one _ k i (ch14ext_pivoted_colmax A k i hi) hpiv

-- ══════════════════════════════════════════════════════════════════════
-- §4  Whole-column elimination  and the reduced form
-- ══════════════════════════════════════════════════════════════════════

/-- **Step-`k` GJE elimination update** (Algorithm 14.4:
    `A(row_ind, k:n) = A(row_ind, k:n) - m * A(k, k:n)`), applied to the WHOLE
    off-diagonal column (rows both above and below the pivot).  The pivot row
    `k` is left unchanged. -/
noncomputable def ch14ext_eliminate (A : Fin n → Fin n → ℝ) (k : Fin n) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if i = k then A i j
    else A i j - ch14ext_multiplier A k i * A k j

/-- **Step-`k` GJE elementary matrix** `G_k`: the identity except that column
    `k` carries the negated multipliers `-m_i` in the off-diagonal rows.
    Left multiplication by `G_k` performs the elimination update. -/
noncomputable def ch14ext_elimMatrix (A : Fin n → Fin n → ℝ) (k : Fin n) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if i = j then 1
    else if j = k then -ch14ext_multiplier A k i
    else 0

/-- The elimination update is exactly left multiplication by the elementary
    matrix `G_k`:  `eliminate A k = G_k · A`. -/
lemma ch14ext_eliminate_eq_matMul (A : Fin n → Fin n → ℝ) (k : Fin n) :
    ch14ext_eliminate A k = NumStability.matMul n (ch14ext_elimMatrix A k) A := by
  ext i j
  unfold ch14ext_eliminate NumStability.matMul
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl]
    -- row i of G_i is the unit vector e_i
    have hcongr : ∀ x ∈ (Finset.univ : Finset (Fin n)),
        ch14ext_elimMatrix A i i x * A x j = (if i = x then A x j else 0) := by
      intro x _
      unfold ch14ext_elimMatrix
      by_cases hx : i = x
      · subst hx; simp
      · rw [if_neg hx, if_neg (by simpa [eq_comm] using hx), zero_mul, if_neg hx]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq]
    simp
  · rw [if_neg hik]
    -- row i of G_i has 1 at column i and -m_i at column k
    have hcongr : ∀ x ∈ (Finset.univ : Finset (Fin n)),
        ch14ext_elimMatrix A k i x * A x j =
          (if i = x then A x j else 0) +
            (if x = k then -ch14ext_multiplier A k i * A x j else 0) := by
      intro x _
      unfold ch14ext_elimMatrix
      by_cases hx : i = x
      · subst hx
        rw [if_pos rfl, if_pos rfl, if_neg hik, one_mul, add_zero]
      · rw [if_neg hx]
        by_cases hxk : x = k
        · subst hxk
          rw [if_pos rfl, if_pos rfl, if_neg hx, zero_add]
        · rw [if_neg hxk, if_neg hx, if_neg hxk, zero_mul, add_zero]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_add_distrib,
      Finset.sum_ite_eq, Finset.sum_ite_eq']
    simp
    ring

/-- **Reduced form (column zeroing).**  After the step-`k` elimination, every
    off-diagonal entry of column `k` is zero — the defining action of
    Gauss–Jordan elimination.  Requires the pivot `A k k ≠ 0`. -/
lemma ch14ext_eliminate_column_zero
    (A : Fin n → Fin n → ℝ) (k : Fin n) (hpiv : A k k ≠ 0) :
    ∀ i : Fin n, i ≠ k → ch14ext_eliminate A k i k = 0 := by
  intro i hik
  unfold ch14ext_eliminate ch14ext_multiplier
  rw [if_neg hik, div_mul_cancel₀ _ hpiv, sub_self]

/-- The step-`k` elimination leaves the pivot row `k` unchanged. -/
lemma ch14ext_eliminate_pivot_row (A : Fin n → Fin n → ℝ) (k : Fin n) :
    ∀ j : Fin n, ch14ext_eliminate A k k j = A k j := by
  intro j; unfold ch14ext_eliminate; rw [if_pos rfl]

/-- The step-`k` elimination does not touch any column `j` in which the pivot
    row already vanishes; in particular it preserves any earlier-zeroed
    off-diagonal column. -/
lemma ch14ext_eliminate_preserves_zero_column
    (A : Fin n → Fin n → ℝ) (k j : Fin n) (hj : A k j = 0) :
    ∀ i : Fin n, ch14ext_eliminate A k i j = A i j := by
  intro i
  unfold ch14ext_eliminate
  by_cases hik : i = k
  · rw [if_pos hik]
  · rw [if_neg hik, hj, mul_zero, sub_zero]

-- ══════════════════════════════════════════════════════════════════════
-- §5  The full interleaved loop and reduction to diagonal form
-- ══════════════════════════════════════════════════════════════════════

/-- One full pass of the Algorithm 14.4 loop body at column `k`: search the
    pivot, swap it into row `k`, then eliminate the whole off-diagonal
    column. -/
noncomputable def ch14ext_stepMat (A : Fin n → Fin n → ℝ) (k : Fin n) :
    Fin n → Fin n → ℝ :=
  ch14ext_eliminate (ch14ext_permRows (ch14ext_swap k (ch14ext_pivotRow A k)) A) k

/-- The Algorithm 14.4 elimination loop, run for the first `t` columns
    `0, 1, …, t-1` (interleaving pivot search, row swap and elimination at
    each column, exactly as in the book). -/
noncomputable def ch14ext_reduce (A : Fin n → Fin n → ℝ) : ℕ → (Fin n → Fin n → ℝ)
  | 0 => A
  | (t + 1) =>
      if h : t < n then ch14ext_stepMat (ch14ext_reduce A t) ⟨t, h⟩
      else ch14ext_reduce A t

/-- `ch14ext_ReducedUpTo t M`: the first `t` columns of `M` are already in
    reduced (diagonal) form — every off-diagonal entry of column `j` with
    `j < t` is zero. -/
def ch14ext_ReducedUpTo (t : ℕ) (M : Fin n → Fin n → ℝ) : Prop :=
  ∀ j : Fin n, j.val < t → ∀ i : Fin n, i ≠ j → M i j = 0

/-- A swap of `k, r` fixes any index `j ∉ {k, r}`, hence maps every `a ≠ j`
    away from `j` (bijectivity). -/
lemma ch14ext_swap_apply_ne {k r j a : Fin n}
    (hjk : j ≠ k) (hjr : j ≠ r) (ha : a ≠ j) :
    Equiv.swap k r a ≠ j := by
  intro h
  have hfix : Equiv.swap k r j = j := Equiv.swap_apply_of_ne_of_ne hjk hjr
  rw [← hfix] at h
  exact ha ((Equiv.swap k r).injective h)

/-- **Reduced-form invariant of the loop.**  Under the standard
    nonsingularity side condition that every pivot encountered is nonzero,
    after processing the first `t` columns the matrix `ch14ext_reduce A t`
    has its first `t` columns in diagonal form.  The pivot search + swap +
    whole-column elimination at each column zeroes the current column while
    preserving all previously reduced columns. -/
theorem ch14ext_reduce_ReducedUpTo (A : Fin n → Fin n → ℝ)
    (hpiv : ∀ s : ℕ, ∀ hs : s < n,
      ch14ext_permRows
          (ch14ext_swap ⟨s, hs⟩ (ch14ext_pivotRow (ch14ext_reduce A s) ⟨s, hs⟩))
          (ch14ext_reduce A s) ⟨s, hs⟩ ⟨s, hs⟩ ≠ 0) :
    ∀ t : ℕ, ch14ext_ReducedUpTo t (ch14ext_reduce A t) := by
  intro t
  induction t with
  | zero => intro j hj; exact absurd hj (by omega)
  | succ t ih =>
      intro j hj i hij
      by_cases h : t < n
      · -- process column k = ⟨t, h⟩ on R = reduce A t
        set R := ch14ext_reduce A t with hR
        set k : Fin n := ⟨t, h⟩ with hk
        set r := ch14ext_pivotRow R k with hrdef
        set P := ch14ext_permRows (ch14ext_swap k r) R with hP
        have hstep : ch14ext_reduce A (t + 1) = ch14ext_eliminate P k := by
          show (if h' : t < n then ch14ext_stepMat R ⟨t, h'⟩ else R) = _
          rw [dif_pos h]; rfl
        rw [hstep]
        have hkr : k ≤ r := ch14ext_pivotRow_ge R k
        -- P k k ≠ 0 is exactly the pivot hypothesis at step t
        have hpivk : P k k ≠ 0 := hpiv t h
        by_cases hjt : j.val = t
        · -- j is the current pivot column: whole-column elimination zeroes it
          have hjk : j = k := Fin.ext (by rw [hk]; exact hjt)
          rw [hjk] at hij ⊢
          exact ch14ext_eliminate_column_zero P k hpivk i hij
        · -- j is an earlier column (j.val < t): preserved as zero
          have hjlt : j.val < t := by omega
          have hkval : (k : Fin n).val = t := rfl
          have hrge : (k : Fin n).val ≤ r.val := hkr
          have hjnek : j ≠ k := by
            apply Fin.ne_of_val_ne; omega
          have hjner : j ≠ r := by
            apply Fin.ne_of_val_ne; omega
          -- pivot row of P vanishes in column j
          have hPkj : P k j = 0 := by
            have : P k j = R r j := by
              simp [hP, ch14ext_permRows, ch14ext_swap, Equiv.swap_apply_left]
            rw [this]
            exact ih j hjlt r (Ne.symm hjner)
          -- elimination preserves column j; and P already has zeros there
          rw [ch14ext_eliminate_preserves_zero_column P k j hPkj i]
          -- P i j = R (swap k r i) j = 0 since swap k r i ≠ j
          have hPij : P i j = R (Equiv.swap k r i) j := rfl
          rw [hPij]
          exact ih j hjlt (Equiv.swap k r i)
            (ch14ext_swap_apply_ne hjnek hjner hij)
      · -- t ≥ n: no more columns; the state is unchanged
        have hstep : ch14ext_reduce A (t + 1) = ch14ext_reduce A t := by
          show (if h' : t < n then ch14ext_stepMat (ch14ext_reduce A t) ⟨t, h'⟩
                else ch14ext_reduce A t) = _
          rw [dif_neg h]
        rw [hstep]
        have hjt : j.val < t := by
          have := j.isLt; omega
        exact ih j hjt i hij

/-- **The full Gauss–Jordan loop reduces `A` to diagonal form.**  After all
    `n` columns are processed, every off-diagonal entry of
    `ch14ext_reduce A n` is zero (given the nonsingularity side condition that
    each pivot is nonzero).  This is the "reduced form" produced by
    Algorithm 14.4 before the final `x_i = b_i / a_ii` back-scaling. -/
theorem ch14ext_reduce_diagonal (A : Fin n → Fin n → ℝ)
    (hpiv : ∀ s : ℕ, ∀ hs : s < n,
      ch14ext_permRows
          (ch14ext_swap ⟨s, hs⟩ (ch14ext_pivotRow (ch14ext_reduce A s) ⟨s, hs⟩))
          (ch14ext_reduce A s) ⟨s, hs⟩ ⟨s, hs⟩ ≠ 0) :
    ∀ i j : Fin n, i ≠ j → ch14ext_reduce A n i j = 0 := by
  intro i j hij
  exact ch14ext_reduce_ReducedUpTo A hpiv n j j.isLt i hij

-- ═════════════════════════════════════════════════════════════════════════════
-- §6  Literal Algorithm 14.4 state: A-tail swap, RHS update, and final scaling
-- ═════════════════════════════════════════════════════════════════════════════

/-- The mutable data of Algorithm 14.4: the matrix and right-hand side are
    advanced together. -/
structure Ch14GJEState (n : ℕ) where
  matrix : Fin n → Fin n → ℝ
  rhs : Fin n → ℝ

/-- Swap rows `k` and `r` only in columns `j ≥ k`, exactly matching the
    source instruction `A(k,k:n) ↔ A(r,k:n)`.  Earlier columns are left
    definitionally unchanged. -/
def ch14ext_tailSwapRows (A : Fin n → Fin n → ℝ) (k r : Fin n) :
    Fin n → Fin n → ℝ :=
  fun i j => if k ≤ j then A (Equiv.swap k r i) j else A i j

/-- The simultaneous RHS interchange `b(k) ↔ b(r)` in Algorithm 14.4. -/
def ch14ext_swapRhs (b : Fin n → ℝ) (k r : Fin n) : Fin n → ℝ :=
  fun i => b (Equiv.swap k r i)

/-- Matrix after the source's partial-pivot search and tail-row interchange. -/
noncomputable def ch14ext_tailPivotMatrix (s : Ch14GJEState n) (k : Fin n) :
    Fin n → Fin n → ℝ :=
  ch14ext_tailSwapRows s.matrix k (ch14ext_pivotRow s.matrix k)

/-- RHS after the same pivot-row interchange. -/
noncomputable def ch14ext_tailPivotRhs (s : Ch14GJEState n) (k : Fin n) :
    Fin n → ℝ :=
  ch14ext_swapRhs s.rhs k (ch14ext_pivotRow s.matrix k)

/-- The exact multiplier vector formed from the pivoted state. -/
noncomputable def ch14ext_fullMultiplier (s : Ch14GJEState n) (k i : Fin n) : ℝ :=
  ch14ext_tailPivotMatrix s k i k / ch14ext_tailPivotMatrix s k k k

/-- One literal loop body of Algorithm 14.4.  It performs the max-magnitude
    pivot search, swaps only the matrix tail `k:n`, swaps the RHS entries,
    updates every nonpivot row in columns `k:n`, and updates the same RHS rows
    with the same multiplier. -/
noncomputable def ch14ext_fullStep (s : Ch14GJEState n) (k : Fin n) :
    Ch14GJEState n where
  matrix := fun i j =>
    if i = k then ch14ext_tailPivotMatrix s k i j
    else if k ≤ j then
      ch14ext_tailPivotMatrix s k i j -
        ch14ext_fullMultiplier s k i * ch14ext_tailPivotMatrix s k k j
    else ch14ext_tailPivotMatrix s k i j
  rhs := fun i =>
    if i = k then ch14ext_tailPivotRhs s k i
    else ch14ext_tailPivotRhs s k i -
      ch14ext_fullMultiplier s k i * ch14ext_tailPivotRhs s k k

@[simp] theorem ch14ext_tailPivotMatrix_before
    (s : Ch14GJEState n) (k i j : Fin n) (hj : j < k) :
    ch14ext_tailPivotMatrix s k i j = s.matrix i j := by
  simp [ch14ext_tailPivotMatrix, ch14ext_tailSwapRows, not_le.mpr hj]

/-- The tail swap puts the selected maximum-magnitude entry in position
    `(k,k)`; restricting the swap to `k:n` does not alter pivot semantics. -/
theorem ch14ext_tailPivotMatrix_colmax (s : Ch14GJEState n) (k : Fin n) :
    ∀ i : Fin n, k ≤ i →
      |ch14ext_tailPivotMatrix s k i k| ≤
        |ch14ext_tailPivotMatrix s k k k| := by
  intro i hi
  simpa [ch14ext_tailPivotMatrix, ch14ext_tailSwapRows,
    ch14ext_permRows, ch14ext_swap] using
      ch14ext_pivoted_colmax s.matrix k i hi

/-- A literal Algorithm-14.4 step leaves every earlier matrix column
    definitionally unchanged. -/
theorem ch14ext_fullStep_matrix_before
    (s : Ch14GJEState n) (k i j : Fin n) (hj : j < k) :
    (ch14ext_fullStep s k).matrix i j = s.matrix i j := by
  by_cases hik : i = k
  · subst i
    simp [ch14ext_fullStep, ch14ext_tailPivotMatrix_before s k k j hj]
  · simp [ch14ext_fullStep, hik, not_le.mpr hj,
      ch14ext_tailPivotMatrix_before s k i j hj]

/-- With a nonzero selected pivot, the full source step zeros every
    off-diagonal entry in the current column. -/
theorem ch14ext_fullStep_current_column_zero
    (s : Ch14GJEState n) (k i : Fin n)
    (hpiv : ch14ext_tailPivotMatrix s k k k ≠ 0) (hik : i ≠ k) :
    (ch14ext_fullStep s k).matrix i k = 0 := by
  simp only [ch14ext_fullStep, hik, if_false, le_refl, if_true]
  unfold ch14ext_fullMultiplier
  rw [div_mul_cancel₀ _ hpiv, sub_self]

/-- The RHS update uses exactly the same multiplier as the matrix row update. -/
theorem ch14ext_fullStep_rhs_offpivot
    (s : Ch14GJEState n) (k i : Fin n) (hik : i ≠ k) :
    (ch14ext_fullStep s k).rhs i =
      ch14ext_tailPivotRhs s k i -
        ch14ext_fullMultiplier s k i * ch14ext_tailPivotRhs s k k := by
  simp [ch14ext_fullStep, hik]

/-- Run the literal stateful Algorithm-14.4 loop for the first `t` columns. -/
noncomputable def ch14ext_fullReduce (s : Ch14GJEState n) : ℕ → Ch14GJEState n
  | 0 => s
  | (t + 1) =>
      if h : t < n then ch14ext_fullStep (ch14ext_fullReduce s t) ⟨t, h⟩
      else ch14ext_fullReduce s t

/-- The matrix component of a state is reduced in its first `t` columns. -/
def ch14ext_FullReducedUpTo (t : ℕ) (s : Ch14GJEState n) : Prop :=
  ∀ j : Fin n, j.val < t → ∀ i : Fin n, i ≠ j → s.matrix i j = 0

/-- The literal stateful loop reaches reduced form, assuming each selected
    pivot is nonzero.  This hypothesis is the operational meaning of the
    source phrase "GJE successfully computes"; it is not inferred here from a
    target-equivalent conclusion. -/
theorem ch14ext_fullReduce_ReducedUpTo (s : Ch14GJEState n)
    (hpiv : ∀ t : ℕ, ∀ ht : t < n,
      ch14ext_tailPivotMatrix (ch14ext_fullReduce s t) ⟨t, ht⟩ ⟨t, ht⟩ ⟨t, ht⟩ ≠ 0) :
    ∀ t : ℕ, ch14ext_FullReducedUpTo t (ch14ext_fullReduce s t) := by
  intro t
  induction t with
  | zero =>
      intro j hj
      exact absurd hj (by omega)
  | succ t ih =>
      intro j hj i hij
      by_cases ht : t < n
      · let k : Fin n := ⟨t, ht⟩
        have hstep : ch14ext_fullReduce s (t + 1) =
            ch14ext_fullStep (ch14ext_fullReduce s t) k := by
          simp [ch14ext_fullReduce, ht, k]
        rw [hstep]
        by_cases hjt : j.val = t
        · have hjk : j = k := Fin.ext hjt
          subst j
          exact ch14ext_fullStep_current_column_zero
            (ch14ext_fullReduce s t) k i (hpiv t ht) hij
        · have hjlt : j.val < t := by omega
          have hjk : j < k := hjlt
          rw [ch14ext_fullStep_matrix_before (ch14ext_fullReduce s t) k i j hjk]
          exact ih j hjlt i hij
      · have hstep : ch14ext_fullReduce s (t + 1) = ch14ext_fullReduce s t := by
          simp [ch14ext_fullReduce, ht]
        rw [hstep]
        have hjlt : j.val < t := by
          have := j.isLt
          omega
        exact ih j hjlt i hij

/-- After all `n` loop iterations, the literal Algorithm-14.4 matrix state is
    diagonal. -/
theorem ch14ext_fullReduce_diagonal (s : Ch14GJEState n)
    (hpiv : ∀ t : ℕ, ∀ ht : t < n,
      ch14ext_tailPivotMatrix (ch14ext_fullReduce s t) ⟨t, ht⟩ ⟨t, ht⟩ ⟨t, ht⟩ ≠ 0) :
    ∀ i j : Fin n, i ≠ j → (ch14ext_fullReduce s n).matrix i j = 0 := by
  intro i j hij
  exact ch14ext_fullReduce_ReducedUpTo s hpiv n j j.isLt i hij

/-- The final source instruction `xᵢ = bᵢ/aᵢᵢ`. -/
noncomputable def ch14ext_fullSolution (s : Ch14GJEState n) : Fin n → ℝ :=
  fun i =>
    (ch14ext_fullReduce s n).rhs i / (ch14ext_fullReduce s n).matrix i i

/-- Successful final scaling solves every diagonal equation exactly. -/
theorem ch14ext_fullSolution_diag_equation (s : Ch14GJEState n) (i : Fin n)
    (hdiag : (ch14ext_fullReduce s n).matrix i i ≠ 0) :
    ch14ext_fullSolution s i * (ch14ext_fullReduce s n).matrix i i =
      (ch14ext_fullReduce s n).rhs i := by
  unfold ch14ext_fullSolution
  exact div_mul_cancel₀ _ hdiag

end NumStability.Ch14Ext
